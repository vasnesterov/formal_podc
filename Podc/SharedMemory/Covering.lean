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
  applied in order;
* `Impl.runFrom_poised_block` — distinct poised processes take one step each: the memory becomes
  `applyAccesses`, pending operations and the other processes are unchanged;
* `Impl.blockWrite_swap` — two block writes by covering processes to the same set of objects
  commute, up to the memory inside that set.
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

end Impl

end Cslib.SharedMemory
