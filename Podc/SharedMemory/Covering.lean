import Cslib.Computability.Distributed.SharedMemory.Covering
import Cslib.Computability.Distributed.SharedMemory.Progress

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Covering.lean

/-!
# Covering, poised processes and block writes

Additions to CSLib's `Covering.lean`, generic in the implemented object `A`.

## Agreement of configurations

`Impl.AgreeOn Q C D` (CSLib: same memory, same local states and pending operations on `Q`) is an
equivalence relation (`AgreeOn.refl`, `AgreeOn.symm`, `AgreeOn.trans`), and agreement on all
processes is equality (`AgreeOn.univ_eq`).

## Poised and covering processes

* `Impl.PoisedAt I C p i o` — `p` is pending in `C` and its next step applies `o` to the base
  object `i`; `Covers` is `PoisedAt` with a blind overwrite (`covers_iff_poisedAt`).
* `PoisedAt.congr`, `Covers.congr`: both only depend on the local state and pending operation of
  the process; `PoisedAt.unique`, `Covers.unique`: a (deterministic) process is poised at, and
  covers, at most one base object.

## Block writes

* `opsOf_blockWrite`, `respsOf_blockWrite`, `blockWrite_append`, `runFrom_blockWrite_other`;
* `applyAccesses M as` — the memory `M` after the accesses `as` (base object and operation),
  applied in order (`applyAccesses_map_mk`: accesses to a single object);
* `Impl.runFrom_poised_block` — distinct poised processes take one step each: the memory becomes
  `applyAccesses`, pending operations and the other processes are unchanged;
* `Impl.blockWrite_swap` — two block writes by covering processes to the same set of objects
  commute, up to the memory inside that set.

## Locality and commutation of steps

* `Impl.mem_of_step` — a step changes at most the base object accessed by an internal step;
* `Impl.step_exact` — exact version of CSLib's `step_local`: a step of `a` can be replayed in a
  configuration that agrees with the original one on `a` and on the accessed object; the results
  agree on `a`, on the memory outside the accessed object, and on that object as well;
* `Impl.step_comm` — steps of distinct processes commute unless both access the same base object
  and one of them changes it.
-/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

/-! ### Agreement of configurations -/

/-- Agreement is reflexive. -/
@[refl] lemma AgreeOn.refl (Q : Set P) (C : Config A B P L) : AgreeOn Q C C :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Agreement is transitive. -/
lemma AgreeOn.trans {Q : Set P} {C D E : Config A B P L} (h₁ : AgreeOn Q C D)
    (h₂ : AgreeOn Q D E) : AgreeOn Q C E :=
  ⟨h₁.mem.trans h₂.mem, fun q hq => (h₁.loc q hq).trans (h₂.loc q hq),
    fun q hq => (h₁.pend q hq).trans (h₂.pend q hq)⟩

/-- Configurations that agree on all processes are equal. -/
lemma AgreeOn.univ_eq {C D : Config A B P L} (h : AgreeOn Set.univ C D) : C = D := by
  cases C; cases D
  simp only [Config.mk.injEq]
  exact ⟨funext fun q => h.loc q trivial, funext fun q => h.pend q trivial, h.mem⟩

/-- Agreement on all processes is equality. -/
lemma agreeOn_univ_iff {C D : Config A B P L} : AgreeOn Set.univ C D ↔ C = D :=
  ⟨AgreeOn.univ_eq, fun h => h ▸ AgreeOn.refl _ _⟩

/-! ### Poised and covering processes -/

variable (I : Impl A B P L)

/-- In `C`, process `p` is *poised* to apply `o` to base object `i`: it is pending and its next
step is this access. -/
def PoisedAt (C : Config A B P L) (p : P) (i : ι) (o : (B i).Op) : Prop :=
  C.pend p ≠ none ∧ ∃ k, I.act p (C.loc p) = .access i o k

variable {I}

/-- Covering is being poised to apply a blind overwrite. -/
lemma covers_iff_poisedAt {C : Config A B P L} {p : P} {i : ι} :
    I.Covers C p i ↔ ∃ o, I.PoisedAt C p i o ∧ (B i).Overwrites o :=
  ⟨fun ⟨hp, o, k, hk, ho⟩ => ⟨o, ⟨hp, k, hk⟩, ho⟩, fun ⟨o, ⟨hp, k, hk⟩, ho⟩ => ⟨hp, o, k, hk, ho⟩⟩

/-- Being poised only depends on the local state and the pending operation. -/
lemma PoisedAt.congr {C D : Config A B P L} {p : P} {i : ι} {o : (B i).Op}
    (h : I.PoisedAt C p i o) (hl : C.loc p = D.loc p) (hp : C.pend p = D.pend p) :
    I.PoisedAt D p i o :=
  ⟨hp ▸ h.1, hl ▸ h.2⟩

/-- Covering only depends on the local state and the pending operation. -/
lemma Covers.congr {C D : Config A B P L} {p : P} {i : ι} (h : I.Covers C p i)
    (hl : C.loc p = D.loc p) (hp : C.pend p = D.pend p) : I.Covers D p i := by
  obtain ⟨h1, o, k, h2, h3⟩ := h
  exact ⟨hp ▸ h1, o, k, hl ▸ h2, h3⟩

/-- A process is poised at most at one base object. -/
lemma PoisedAt.unique {C : Config A B P L} {p : P} {i j : ι} {o : (B i).Op} {o' : (B j).Op}
    (hi : I.PoisedAt C p i o) (hj : I.PoisedAt C p j o') : i = j := by
  obtain ⟨-, k, h1⟩ := hi
  obtain ⟨-, k', h2⟩ := hj
  rw [h1] at h2
  cases h2; rfl

/-- A process covers at most one base object. -/
lemma Covers.unique {C : Config A B P L} {p : P} {i j : ι} (hi : I.Covers C p i)
    (hj : I.Covers C p j) : i = j := by
  obtain ⟨o, hi, -⟩ := covers_iff_poisedAt.1 hi
  obtain ⟨o', hj, -⟩ := covers_iff_poisedAt.1 hj
  exact hi.unique hj

/-! ### Block writes -/

variable [DecidableEq P]

/-- A block write invokes nothing. -/
@[simp] lemma opsOf_blockWrite (ps : List P) (q : P) :
    opsOf (blockWrite (A := A) ps) q = [] := by
  simp [opsOf, blockWrite, List.filterMap_map, Function.comp_def]

/-- A block write returns nothing. -/
@[simp] lemma respsOf_blockWrite (ps : List P) (q : P) :
    respsOf (blockWrite (A := A) ps) q = [] := by
  simp [respsOf, blockWrite, List.filterMap_map, Function.comp_def]

omit [DecidableEq P] in
/-- Block writes of concatenated lists of processes. -/
@[simp] lemma blockWrite_append (ps qs : List P) :
    blockWrite (A := A) (ps ++ qs) = blockWrite ps ++ blockWrite qs := by
  simp [blockWrite]

/-- A block write does not change the processes outside it. -/
lemma runFrom_blockWrite_other [DecidableEq ι] {C C' : Config A B P L} {ps : List P}
    (h : I.runFrom C (blockWrite ps) = some C') {q : P} (hq : q ∉ ps) :
    C'.loc q = C.loc q ∧ C'.pend q = C.pend q :=
  I.runFrom_other h fun _ hℓ he => hq (he ▸ mem_blockWrite hℓ)

end Impl

/-- The memory `M` after applying the accesses `as` (a base object and an operation on it), in
order. -/
def applyAccesses [DecidableEq ι] (M : ∀ i, (B i).State) :
    List (Σ i, (B i).Op) → ∀ i, (B i).State
  | [] => M
  | a :: as => applyAccesses (Function.update M a.1 ((B a.1).δ (M a.1) a.2).1) as

section applyAccesses

variable [DecidableEq ι]

/-- No accesses: the memory is unchanged. -/
@[simp] lemma applyAccesses_nil (M : ∀ i, (B i).State) : applyAccesses M [] = M := rfl

/-- The first access is applied first. -/
@[simp] lemma applyAccesses_cons (M : ∀ i, (B i).State) (a : Σ i, (B i).Op)
    (as : List (Σ i, (B i).Op)) :
    applyAccesses M (a :: as) =
      applyAccesses (Function.update M a.1 ((B a.1).δ (M a.1) a.2).1) as := rfl

/-- Accesses of concatenated lists are applied one list after the other. -/
lemma applyAccesses_append (M : ∀ i, (B i).State) (as bs : List (Σ i, (B i).Op)) :
    applyAccesses M (as ++ bs) = applyAccesses (applyAccesses M as) bs := by
  induction as generalizing M with
  | nil => rfl
  | cons a as ih => exact ih _

/-- Accesses to a single base object `i` apply their operations to its state, in order. -/
lemma applyAccesses_map_mk (M : ∀ i, (B i).State) (i : ι) (os : List (B i).Op) :
    applyAccesses M (os.map (Sigma.mk i)) = Function.update M i ((B i).runOps (M i) os) := by
  induction os generalizing M with
  | nil => simp
  | cons o os ih => simp [ih, ObjSpec.runOps_cons]

/-- Base objects that are not accessed keep their state. -/
lemma applyAccesses_of_forall_ne (M : ∀ i, (B i).State) {as : List (Σ i, (B i).Op)} {j : ι}
    (h : ∀ a ∈ as, a.1 ≠ j) : applyAccesses M as j = M j := by
  induction as generalizing M with
  | nil => rfl
  | cons a as ih =>
    rw [applyAccesses_cons, ih _ fun b hb => h b (List.mem_cons_of_mem _ hb),
      Function.update_of_ne (h a List.mem_cons_self).symm]

end applyAccesses

namespace Impl

variable [DecidableEq P] [DecidableEq ι] {I : Impl A B P L}

/-- **A block of poised processes.** If the distinct processes `e.1` are poised to perform the
accesses `e.2` in `C`, then they can take one step each, in order: the memory becomes
`applyAccesses C.mem`, pending operations do not change, the other processes do not move, and
each process of the block continues with the response of its access. -/
theorem runFrom_poised_block {es : List (P × Σ i, (B i).Op)} (hnd : (es.map Prod.fst).Nodup)
    {C : Config A B P L} (h : ∀ e ∈ es, I.PoisedAt C e.1 e.2.1 e.2.2) :
    ∃ C', I.runFrom C (blockWrite (es.map Prod.fst)) = some C' ∧
      C'.mem = applyAccesses C.mem (es.map Prod.snd) ∧ C'.pend = C.pend ∧
      (∀ q ∉ es.map Prod.fst, C'.loc q = C.loc q) ∧
      (∀ e ∈ es, ∃ k s, I.act e.1 (C.loc e.1) = .access e.2.1 e.2.2 k ∧
        C'.loc e.1 = k ((B e.2.1).δ s e.2.2).2) := by
  induction es generalizing C with
  | nil => exact ⟨C, rfl, rfl, rfl, fun _ _ => rfl, by simp⟩
  | cons e es ih =>
    obtain ⟨p, i, o⟩ := e
    obtain ⟨hp, k, hk⟩ := h (p, ⟨i, o⟩) List.mem_cons_self
    obtain ⟨hpes, hnd'⟩ := List.nodup_cons.1 hnd
    set C₁ : Config A B P L := { C with
      mem := Function.update C.mem i ((B i).δ (C.mem i) o).1,
      loc := Function.update C.loc p (k ((B i).δ (C.mem i) o).2) } with hC₁
    have hs : I.step C (.tau p) = some C₁ := by simp [step, hp, hk, hC₁]
    have hne : ∀ e ∈ es, e.1 ≠ p := fun e he h => hpes (List.mem_map.2 ⟨e, he, h⟩)
    obtain ⟨C', h1, h2, h3, h4, h5⟩ := ih hnd' (C := C₁) fun e he => by
      refine (h e (List.mem_cons_of_mem _ he)).congr ?_ rfl
      simp [hC₁, Function.update_of_ne (hne e he)]
    refine ⟨C', by simp [hs, h1], by simp [h2, hC₁], h3, fun q hq => ?_, fun e he => ?_⟩
    · have hqp : q ≠ p := fun e => hq (by simp [e])
      rw [h4 q fun h => hq (List.mem_cons_of_mem _ h)]
      simp [hC₁, hqp]
    · rcases List.mem_cons.1 he with rfl | he
      · refine ⟨k, C.mem i, hk, ?_⟩
        rw [h4 _ hpes]
        simp [hC₁]
      · obtain ⟨k', s, hk', hl⟩ := h5 e he
        refine ⟨k', s, ?_, hl⟩
        simpa [hC₁, Function.update_of_ne (hne e he)] using hk'

/-- **Commuting block writes.** Two block writes by distinct processes covering the same set of
base objects can be performed in either order: the results agree on all processes and on the
memory outside the covered objects. -/
lemma blockWrite_swap {C : Config A B P L} {b b' : List (P × ι)}
    (hnd : (b.map Prod.fst ++ b'.map Prod.fst).Nodup)
    (hcov : ∀ c ∈ b ++ b', I.Covers C c.1 c.2)
    (hsnd : ∀ j, j ∈ b.map Prod.snd ↔ j ∈ b'.map Prod.snd) :
    ∃ X X', I.runFrom C (blockWrite (b.map Prod.fst) ++ blockWrite (b'.map Prod.fst)) = some X ∧
      I.runFrom C (blockWrite (b'.map Prod.fst) ++ blockWrite (b.map Prod.fst)) = some X' ∧
      (∀ q, X.loc q = X'.loc q ∧ X.pend q = X'.pend q) ∧
      (∀ j, j ∉ b.map Prod.snd → X.mem j = X'.mem j) := by
  obtain ⟨hnd₁, hnd₂, hdis⟩ := List.nodup_append.1 hnd
  have hcb : ∀ c ∈ b, I.Covers C c.1 c.2 := fun c hc => hcov c (List.mem_append_left _ hc)
  have hcb' : ∀ c ∈ b', I.Covers C c.1 c.2 := fun c hc => hcov c (List.mem_append_right _ hc)
  have hn₁ : ∀ c ∈ b, c.1 ∉ b'.map Prod.fst := fun c hc h =>
    hdis _ (List.mem_map_of_mem hc) _ h rfl
  have hn₂ : ∀ c ∈ b', c.1 ∉ b.map Prod.fst := fun c hc h =>
    hdis _ h _ (List.mem_map_of_mem hc) rfl
  obtain ⟨Y, hY, hYo, hYm⟩ := blockWrite_run (I := I) hnd₁ hcb
  obtain ⟨Y', hY', hY'o, hY'm⟩ := blockWrite_run (I := I) hnd₂ hcb'
  obtain ⟨Z, X', hZ, hX', hag⟩ := blockWrite_agreeOn (I := I)
    (Q := {q | q ∉ b'.map Prod.fst}) (cs := b) hnd₁ hn₁ (C := C) (D := Y') hcb
    (fun q hq => (hY'o q hq).1.symm) (fun q hq => (hY'o q hq).2.symm)
    (fun j hj => (hY'm j (fun h => hj ((hsnd j).2 h))).symm)
  rw [hY] at hZ; cases hZ
  obtain ⟨Z', X, hZ', hX, hag'⟩ := blockWrite_agreeOn (I := I)
    (Q := {q | q ∉ b.map Prod.fst}) (cs := b') hnd₂ hn₂ (C := C) (D := Y) hcb'
    (fun q hq => (hYo q hq).1.symm) (fun q hq => (hYo q hq).2.symm)
    (fun j hj => (hYm j (fun h => hj ((hsnd j).1 h))).symm)
  rw [hY'] at hZ'; cases hZ'
  refine ⟨X, X', by rw [runFrom_append_of_eq I hY, hX], by rw [runFrom_append_of_eq I hY', hX'],
    fun q => ?_, fun j hj => ?_⟩
  · by_cases hq : q ∈ b.map Prod.fst
    · have hq' : q ∉ b'.map Prod.fst := fun h => hdis _ hq _ h rfl
      have h1 := runFrom_blockWrite_other hX hq'
      rw [h1.1, h1.2]; exact ⟨hag.loc q hq', hag.pend q hq'⟩
    · have h1 := runFrom_blockWrite_other hX' hq
      rw [h1.1, h1.2]; exact ⟨(hag'.loc q hq).symm, (hag'.pend q hq).symm⟩
  · rw [← hag'.mem, ← hag.mem, hY'm j (fun h => hj ((hsnd j).2 h)), hYm j hj]

/-! ### Locality and commutation of steps -/

/-- The memory after a step: unchanged, except for the base object accessed by an internal step
of a pending process. -/
lemma mem_of_step {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C') (j : ι) :
    C'.mem j = C.mem j ∨ (ℓ = .tau ℓ.proc ∧ C.pend ℓ.proc ≠ none ∧
      ∃ o k, I.act ℓ.proc (C.loc ℓ.proc) = .access j o k ∧
        C'.mem j = ((B j).δ (C.mem j) o).1) := by
  cases ℓ with
  | inv q o => left; rw [(step_inv h).2.2.2.2]
  | ret q r => left; rw [(step_ret h).2.2.1]
  | tau q =>
    obtain ⟨h0, -, i, o, k, hact, hm, -⟩ := step_tau h
    by_cases hj : j = i
    · subst hj; right; exact ⟨rfl, h0, o, k, hact, by simp [hm]⟩
    · left; simp [hm, Function.update_of_ne hj]

/-- **Exact locality of steps.** A step of `a` only depends on the local state and pending
operation of `a` and on the state of the object it accesses: it can be replayed in `D`, the
other processes of `D` do not move, and on every base object either both steps leave the memory
unchanged or the results agree (and the step is an access of `a` to that object). -/
lemma step_exact {a : P} {C D C' : Config A B P L} {ℓ : Label P A} (hℓ : ℓ.proc = a)
    (hloc : C.loc a = D.loc a) (hpend : C.pend a = D.pend a)
    (hobj : ∀ i o k, ℓ = .tau a → I.act a (C.loc a) = .access i o k → C.mem i = D.mem i)
    (h : I.step C ℓ = some C') :
    ∃ D', I.step D ℓ = some D' ∧ D'.loc a = C'.loc a ∧ D'.pend a = C'.pend a ∧
      (∀ q, q ≠ a → D'.loc q = D.loc q ∧ D'.pend q = D.pend q) ∧
      ∀ j, (D'.mem j = D.mem j ∧ C'.mem j = C.mem j) ∨
        (D'.mem j = C'.mem j ∧ ℓ = .tau a ∧ ∃ o k, I.act a (C.loc a) = .access j o k) := by
  obtain ⟨D', hD', hl, hp, hm⟩ :=
    step_local hloc hpend hℓ (fun hτ i o k hact _ => hobj i o k hτ hact) h
  refine ⟨D', hD', hl.symm, hp.symm, fun q hq => step_other hD' (by rw [hℓ]; exact Ne.symm hq),
    fun j => ?_⟩
  rcases hm j with ⟨h1, h2⟩ | h1
  · exact Or.inl ⟨h2, h1⟩
  · rcases mem_of_step h j with e | ⟨hτ, -, o, k, hact, -⟩
    · rcases mem_of_step hD' j with e' | ⟨hτ, -, o, k, hact, -⟩
      · exact Or.inl ⟨e', e⟩
      · rw [hℓ, ← hloc] at hact
        rw [hℓ] at hτ
        exact Or.inr ⟨h1.symm, hτ, o, k, hact⟩
    · rw [hℓ] at hτ hact
      exact Or.inr ⟨h1.symm, hτ, o, k, hact⟩

/-- **Commuting steps.** Steps of distinct processes commute unless both access the same object
and one of them changes it. -/
lemma step_comm {a b : P} (hab : a ≠ b) {C Ca Cab : Config A B P L} {ℓa ℓb : Label P A}
    (ha : ℓa.proc = a) (hb : ℓb.proc = b) (h1 : I.step C ℓa = some Ca)
    (h2 : I.step Ca ℓb = some Cab)
    (hnc : ∀ i o k j o' k', ℓa = .tau a → I.act a (C.loc a) = .access i o k → ℓb = .tau b →
      I.act b (C.loc b) = .access j o' k' →
        i ≠ j ∨ (((B i).δ (C.mem i) o).1 = C.mem i ∧ ((B j).δ (C.mem j) o').1 = C.mem j)) :
    ∃ Cb, I.step C ℓb = some Cb ∧ I.step Cb ℓa = some Cab := by
  have hbC : Ca.loc b = C.loc b ∧ Ca.pend b = C.pend b :=
    step_other h1 (by rw [ha]; exact hab)
  -- the object accessed by `b` is unchanged by `a`'s step
  have hobjb : ∀ j o' k', ℓb = .tau b → I.act b (Ca.loc b) = .access j o' k' →
      Ca.mem j = C.mem j := by
    intro j o' k' hℓb hact
    rw [hbC.1] at hact
    rcases mem_of_step h1 j with h | ⟨hℓa, -, o, k, hact', hv⟩
    · exact h
    · rw [ha] at hℓa hact'
      rcases hnc j o k j o' k' hℓa hact' hℓb hact with h | ⟨h, -⟩
      · exact absurd rfl h
      · rw [hv, h]
  obtain ⟨Cb, hCb, hl1, hp1, ho1, hm1⟩ := step_exact (I := I) hb hbC.1 hbC.2 hobjb h2
  have haCb : Cb.loc a = C.loc a ∧ Cb.pend a = C.pend a := ho1 a hab
  have hobja : ∀ i o k, ℓa = .tau a → I.act a (C.loc a) = .access i o k →
      C.mem i = Cb.mem i := by
    intro i o k hℓa hact
    rcases mem_of_step hCb i with h | ⟨hℓb, -, o', k', hact', hv⟩
    · exact h.symm
    · rw [hb] at hℓb hact'
      rcases hnc i o k i o' k' hℓa hact hℓb hact' with h | ⟨-, h⟩
      · exact absurd rfl h
      · rw [hv, h]
  obtain ⟨Cba, hCba, hl2, hp2, ho2, hm2⟩ := step_exact (I := I) ha haCb.1.symm haCb.2.symm
    hobja h1
  refine ⟨Cb, hCb, ?_⟩
  rw [hCba]
  congr 1
  have haCab : Cab.loc a = Ca.loc a ∧ Cab.pend a = Ca.pend a :=
    step_other h2 (by rw [hb]; exact Ne.symm hab)
  apply AgreeOn.univ_eq
  refine ⟨funext fun j => ?_, fun x _ => ?_, fun x _ => ?_⟩
  · rcases hm1 j with ⟨e1, e2⟩ | ⟨e1, hℓb, o', k', hact'⟩ <;>
      rcases hm2 j with ⟨e3, e4⟩ | ⟨e3, hℓa, o, k, hact⟩
    · rw [e3, e1, e2, ← e4]
    · rw [e3, e2]
    · rw [e3, e1]
    · -- both access `j`: both leave it unchanged
      rw [hbC.1] at hact'
      rcases hnc j o k j o' k' hℓa hact hℓb hact' with h | ⟨h, h'⟩
      · exact absurd rfl h
      · rw [e3, ← e1]
        rcases mem_of_step h1 j with f1 | ⟨-, -, o₁, k₁, hact₁, f1⟩ <;>
          rcases mem_of_step hCb j with f2 | ⟨-, -, o₂, k₂, hact₂, f2⟩
        · rw [f1, f2]
        · rw [hb] at hact₂; rw [hact'] at hact₂
          simp only [Action.access.injEq] at hact₂
          obtain ⟨-, ho, -⟩ := hact₂; rw [f1, f2, ← eq_of_heq ho, h']
        · rw [ha] at hact₁; rw [hact] at hact₁
          simp only [Action.access.injEq] at hact₁
          obtain ⟨-, ho, -⟩ := hact₁; rw [f1, f2, ← eq_of_heq ho, h]
        · rw [ha] at hact₁; rw [hact] at hact₁
          rw [hb] at hact₂; rw [hact'] at hact₂
          simp only [Action.access.injEq] at hact₁ hact₂
          obtain ⟨-, ho₁, -⟩ := hact₁; obtain ⟨-, ho₂, -⟩ := hact₂
          rw [f1, f2, ← eq_of_heq ho₁, ← eq_of_heq ho₂, h, h']
  · by_cases hxa : x = a
    · subst hxa; rw [hl2, ← haCab.1]
    · by_cases hxb : x = b
      · subst hxb; rw [(ho2 x hxa).1, hl1]
      · rw [(ho2 x hxa).1, (ho1 x hxb).1, (step_other h2 (by rw [hb]; exact Ne.symm hxb)).1,
          (step_other h1 (by rw [ha]; exact Ne.symm hxa)).1]
  · by_cases hxa : x = a
    · subst hxa; rw [hp2, ← haCab.2]
    · by_cases hxb : x = b
      · subst hxb; rw [(ho2 x hxa).2, hp1]
      · rw [(ho2 x hxa).2, (ho1 x hxb).2, (step_other h2 (by rw [hb]; exact Ne.symm hxb)).2,
          (step_other h1 (by rw [ha]; exact Ne.symm hxa)).2]

end Impl

end Cslib.SharedMemory
