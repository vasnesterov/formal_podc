import Papers.PODC2026.ConsistentRefereeing.LongLivedValency
import Podc.SharedMemory.Objects
import Podc.SharedMemory.ObjClasses

/-!
# Long-lived contest: indistinguishability of schedules (Section 5 of [ACE26])

Step-level facts used in the case analyses of Lemmas 20, 23, 27, 28 and Theorems 25, 30 of
[ACE26], stated for the schedules of `LLCtx`:

* `step_exact` — a step only depends on the stepping process and the object it accesses
  (exact version of CSLib's `step_local`); `step_comm` — two steps of distinct processes that
  do not conflict (different objects, or both leave the common object unchanged) commute;
* `X.Writes C c i` (`c` is poised to apply a non-read-only primitive to `i`), `X.Quiet C c`
  (`c`'s next step does not change the memory: an invocation, a response or a read-only
  primitive), `X.Accesses C c i`;
* `X.Sim Q α α'` — `α`, `α'` are good, their final configurations agree on `Q`, and the
  referee has invoked in both or in none; preserved by schedules of processes of `Q`;
* `Good.sim_quiet` — a quiet step is invisible to everybody else; `Good.sim_swap`,
  `Good.sim_pass` — commuting steps; `window_run`, `Good.window`, `Good.sim_window` — a block of
  `w` writes to a `w`-window register erases the previous contents; `Good.sim_tas` — two
  operations on a test&set-like object leave the same memory; `Good.tas_mem` — a set
  test&set-like object stays set;
* test&set-like and read/write-like object classes (`ObjSpec.TASLike`, `tasObj_tasLike`,
  `ObjSpec.windowLike_one_of_rw`) come from `Podc.SharedMemory.ObjClasses`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Impl

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  {I : Impl A B P L}

-- CSLib candidate
lemma config_eq_of_agreeOn_univ {C D : Config A B P L} (h : AgreeOn Set.univ C D) : C = D := by
  cases C; cases D
  simp only [Config.mk.injEq]
  exact ⟨funext fun q => h.loc q trivial, funext fun q => h.pend q trivial, h.mem⟩

-- CSLib candidate
lemma AgreeOn.trans {Q : Set P} {C D E : Config A B P L} (h₁ : AgreeOn Q C D)
    (h₂ : AgreeOn Q D E) : AgreeOn Q C E :=
  ⟨h₁.mem.trans h₂.mem, fun q hq => (h₁.loc q hq).trans (h₂.loc q hq),
    fun q hq => (h₁.pend q hq).trans (h₂.pend q hq)⟩

lemma agreeOn_refl (Q : Set P) (C : Config A B P L) : AgreeOn Q C C :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Exact locality of steps** (CSLib candidate). A step of `a` only depends on the local
state and pending operation of `a` and on the state of the object it accesses. -/
lemma step_exact {a : P} {C D C' : Config A B P L} {ℓ : Label P A} (hℓ : ℓ.proc = a)
    (hloc : C.loc a = D.loc a) (hpend : C.pend a = D.pend a)
    (hobj : ∀ i o k, ℓ = .tau a → I.act a (C.loc a) = .access i o k → C.mem i = D.mem i)
    (h : I.step C ℓ = some C') :
    ∃ D', I.step D ℓ = some D' ∧ D'.loc a = C'.loc a ∧ D'.pend a = C'.pend a ∧
      (∀ q, q ≠ a → D'.loc q = D.loc q ∧ D'.pend q = D.pend q) ∧
      ∀ j, (D'.mem j = D.mem j ∧ C'.mem j = C.mem j) ∨
        (D'.mem j = C'.mem j ∧ ℓ = .tau a ∧ ∃ o k, I.act a (C.loc a) = .access j o k) := by
  classical
  cases ℓ with
  | inv q o =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨h0, h1, h2, h3, h4⟩ := step_inv h
    refine ⟨{ D with pend := Function.update D.pend q (some o),
                     loc := Function.update D.loc q (I.invoke q (D.loc q) o) },
      by simp [step, ← hpend, h0, h1], by simp [h3, hloc], by simp [h2],
      fun x hx => by simp [Function.update_of_ne hx], fun j => Or.inl ⟨rfl, by rw [h4]⟩⟩
  | tau q =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨h0, h1, i, o, k, hact, hm, hl⟩ := step_tau h
    have hact' : I.act q (D.loc q) = .access i o k := by rw [← hloc, hact]
    have hi : C.mem i = D.mem i := hobj i o k rfl hact
    refine ⟨{ D with mem := Function.update D.mem i ((B i).δ (D.mem i) o).1,
                     loc := Function.update D.loc q (k ((B i).δ (D.mem i) o).2) },
      by simp [step, ← hpend, h0, hact'], by simp [hl, hi], by simp [h1, hpend],
      fun x hx => by simp [Function.update_of_ne hx], fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; right; exact ⟨by simp [hm, hi], rfl, o, k, hact⟩
    · left; simp [hm, Function.update_of_ne hj]
  | ret q r =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨h0, h1, h2, l, hact, hl⟩ := step_ret h
    have hact' : I.act q (D.loc q) = .ret r l := by rw [← hloc, hact]
    refine ⟨{ D with pend := Function.update D.pend q none, loc := Function.update D.loc q l },
      by simp [step, ← hpend, h0, hact'], by simp [hl], by simp [h1],
      fun x hx => by simp [Function.update_of_ne hx], fun j => Or.inl ⟨rfl, by rw [h2]⟩⟩

/-- The memory after a step. -/
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

/-- **Commuting steps** (CSLib candidate). Steps of distinct processes commute unless both
access the same object and one of them changes it. -/
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
  apply config_eq_of_agreeOn_univ
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

namespace Referee

open Impl

namespace LLCtx

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι] (X : LLCtx P ι L B)

/-! ### Kinds of next steps -/

/-- `c` is poised to apply a non-read-only primitive to base object `i`. -/
def Writes (C : Config (llObj P) B P L) (c : P) (i : ι) : Prop :=
  C.pend c ≠ none ∧ ∃ o k, X.I.act c (C.loc c) = .access i o k ∧ ¬ (B i).ReadOnly o

/-- `c` is poised to apply a primitive to base object `i`. -/
def Accesses (C : Config (llObj P) B P L) (c : P) (i : ι) : Prop :=
  C.pend c ≠ none ∧ ∃ o k, X.I.act c (C.loc c) = .access i o k

/-- `c`'s next step does not change the memory (an invocation, a response, or a read-only
primitive). -/
def Quiet (C : Config (llObj P) B P L) (c : P) : Prop := ∀ i, ¬ X.Writes C c i

/-- The next steps of `a` and `b` do not conflict: they access different objects, or both leave
the common object unchanged. -/
def NonConflict (C : Config (llObj P) B P L) (a b : P) : Prop :=
  ∀ i o k j o' k', C.pend a ≠ none → X.I.act a (C.loc a) = .access i o k → C.pend b ≠ none →
    X.I.act b (C.loc b) = .access j o' k' →
      i ≠ j ∨ (((B i).δ (C.mem i) o).1 = C.mem i ∧ ((B j).δ (C.mem j) o').1 = C.mem j)

variable {X}

lemma Writes.accesses {C : Config (llObj P) B P L} {c : P} {i : ι} (h : X.Writes C c i) :
    X.Accesses C c i :=
  let ⟨h1, o, k, h2, _⟩ := h; ⟨h1, o, k, h2⟩

lemma Accesses.unique {C : Config (llObj P) B P L} {c : P} {i j : ι} (h1 : X.Accesses C c i)
    (h2 : X.Accesses C c j) : i = j := by
  obtain ⟨-, o, k, h⟩ := h1
  obtain ⟨-, o', k', h'⟩ := h2
  rw [h] at h'
  simp only [Action.access.injEq] at h'
  exact h'.1

lemma Writes.congr {C D : Config (llObj P) B P L} {c : P} {i : ι} (h : X.Writes C c i)
    (hl : C.loc c = D.loc c) (hp : C.pend c = D.pend c) : X.Writes D c i := by
  obtain ⟨h1, o, k, h2, h3⟩ := h
  exact ⟨hp ▸ h1, o, k, hl ▸ h2, h3⟩

lemma Accesses.congr {C D : Config (llObj P) B P L} {c : P} {i : ι} (h : X.Accesses C c i)
    (hl : C.loc c = D.loc c) (hp : C.pend c = D.pend c) : X.Accesses D c i := by
  obtain ⟨h1, o, k, h2⟩ := h
  exact ⟨hp ▸ h1, o, k, hl ▸ h2⟩

lemma Quiet.congr {C D : Config (llObj P) B P L} {c : P} (h : X.Quiet C c)
    (hl : C.loc c = D.loc c) (hp : C.pend c = D.pend c) : X.Quiet D c :=
  fun i hw => h i (hw.congr hl.symm hp.symm)

lemma quiet_or_writes (C : Config (llObj P) B P L) (c : P) :
    X.Quiet C c ∨ ∃ i, X.Writes C c i := by
  by_cases h : ∃ i, X.Writes C c i
  · exact Or.inr h
  · push Not at h; exact Or.inl h

lemma nonConflict_of_ne {C : Config (llObj P) B P L} {a b : P} {i j : ι}
    (ha : X.Accesses C a i) (hb : X.Accesses C b j) (hij : i ≠ j) : X.NonConflict C a b := by
  intro i' o k j' o' k' _ hact _ hact'
  left
  rw [ha.unique ⟨‹_›, o, k, hact⟩, hb.unique ⟨‹_›, o', k', hact'⟩] at hij
  exact hij

lemma nonConflict_of_not_pend {C : Config (llObj P) B P L} {a b : P}
    (ha : C.pend a = none) : X.NonConflict C a b :=
  fun _ _ _ _ _ _ h => absurd ha h

/-! ### Next labels after other processes' steps -/

lemma nl_of_access {α : List (LLabel P)} {c : P} {i : ι} (h : X.Accesses (X.cfg α) c i) :
    X.nl α c = some (.tau c) := by
  obtain ⟨h1, o, k, h2⟩ := h
  rw [nl_of_pend h1]; simp [nextLabel, h2]

lemma nl_eq_of_state {α α' : List (LLabel P)} {p : P} (hl : (X.cfg α).loc p = (X.cfg α').loc p)
    (hp : (X.cfg α).pend p = (X.cfg α').pend p)
    (hst : p = X.ref → (opsOf α X.ref = [] ↔ opsOf α' X.ref = [])) : X.nl α p = X.nl α' p := by
  have hnl : X.I.nextLabel (X.cfg α) p = X.I.nextLabel (X.cfg α') p := by
    unfold nextLabel; rw [hl]
  unfold nl
  rw [hp, hnl]
  by_cases hpr : p = X.ref
  · subst hpr
    have := hst rfl
    by_cases h1 : opsOf α X.ref = []
    · simp [h1, this.1 h1]
    · have h2 : opsOf α' X.ref ≠ [] := fun h => h1 (this.2 h)
      simp [h1, h2]
  · simp [hpr]

/-- The next label of `p` does not change when other processes move. -/
lemma Good.nl_ext_of_not_mem {α : List (LLabel P)} (hα : X.Good α) {p : P} {σ : List P}
    (hp : p ∉ σ) : X.nl (X.ext α σ) p = X.nl α p := by
  obtain ⟨h1, h2⟩ := hα.ext_other hp
  exact nl_eq_of_state h1 h2 (fun hpr => by subst hpr; rw [opsOf_ext_of_not_mem hp])

lemma Good.opsOf_ext_ref_eq_nil {α : List (LLabel P)} (hα : X.Good α) (σ : List P) :
    opsOf (X.ext α σ) X.ref = [] ↔ opsOf α X.ref = [] ∧ X.ref ∉ σ := by
  induction σ generalizing α with
  | nil => simp
  | cons p σ ih =>
    rw [ext_cons, ih (hα.ext1 p)]
    by_cases hp : p = X.ref
    · subst hp
      simp only [List.mem_cons, true_or, not_true_eq_false, and_false, iff_false, not_and]
      intro h; exact absurd h hα.opsOf_ext1_ref_ne_nil
    · rw [opsOf_ext1_of_ne (Ne.symm hp)]
      simp only [List.mem_cons, not_or]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, Ne.symm hp, h2⟩
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩

/-! ### Memory after one step -/

lemma Good.mem_ext1 {α : List (LLabel P)} (hα : X.Good α) {c : P} {j : ι}
    (h : ¬ X.Accesses (X.cfg α) c j) : (X.cfg (X.ext1 α c)).mem j = (X.cfg α).mem j := by
  cases hn : X.nl α c with
  | none => rw [ext1_of_none hn]
  | some ℓ =>
    rw [ext1_of_some hn]
    rcases mem_of_step (hα.nl_step hn).1 j with e | ⟨-, hp, o, k, hact, -⟩
    · exact e
    · rw [nl_proc hn] at hp hact; exact absurd ⟨hp, o, k, hact⟩ h

lemma Good.mem_ext1_access {α : List (LLabel P)} (hα : X.Good α) {c : P} {R : ι}
    {o : (B R).Op} {k : (B R).Resp → L} (hp : (X.cfg α).pend c ≠ none)
    (hact : X.I.act c ((X.cfg α).loc c) = .access R o k) :
    (X.cfg (X.ext1 α c)).mem R = ((B R).δ ((X.cfg α).mem R) o).1 ∧
      (X.cfg (X.ext1 α c)).loc c = k ((B R).δ ((X.cfg α).mem R) o).2 ∧
      (X.cfg (X.ext1 α c)).pend c = (X.cfg α).pend c := by
  have hn := nl_of_access (X := X) ⟨hp, o, k, hact⟩
  rw [ext1_of_some hn]
  obtain ⟨-, h1, i, o', k', hact', hm, hl⟩ := step_tau (hα.nl_step hn).1
  rw [hact] at hact'
  simp only [Action.access.injEq] at hact'
  obtain ⟨rfl, ho, hk⟩ := hact'
  have ho' := eq_of_heq ho; subst ho'
  have hk' := eq_of_heq hk; subst hk'
  refine ⟨by simp [hm], by simp [hl], by rw [h1]⟩

/-! ### Indistinguishability of executions -/

variable (X) in
/-- `α` and `α'` are good, their final configurations agree on `Q`, and the referee has invoked
`decide` in both or in none. -/
structure Sim (Q : Set P) (α α' : List (LLabel P)) : Prop where
  good : X.Good α
  good' : X.Good α'
  agree : AgreeOn Q (X.cfg α) (X.cfg α')
  status : opsOf α X.ref = [] ↔ opsOf α' X.ref = []

lemma Sim.symm {Q : Set P} {α α' : List (LLabel P)} (h : X.Sim Q α α') : X.Sim Q α' α :=
  ⟨h.good', h.good, h.agree.symm, h.status.symm⟩

lemma Sim.trans {Q : Set P} {α α' α'' : List (LLabel P)} (h : X.Sim Q α α')
    (h' : X.Sim Q α' α'') : X.Sim Q α α'' :=
  ⟨h.good, h'.good', h.agree.trans h'.agree, h.status.trans h'.status⟩

lemma Sim.mono {Q Q' : Set P} {α α' : List (LLabel P)} (h : X.Sim Q α α') (hQ : Q' ⊆ Q) :
    X.Sim Q' α α' :=
  ⟨h.good, h.good', h.agree.mono hQ, h.status⟩

lemma Sim.refl {α : List (LLabel P)} (hα : X.Good α) (Q : Set P) : X.Sim Q α α :=
  ⟨hα, hα, agreeOn_refl _ _, Iff.rfl⟩

lemma Sim.of_eq {α α' : List (LLabel P)} (hα : X.Good α) (hα' : X.Good α')
    (h : X.cfg α = X.cfg α') (hs : opsOf α X.ref = [] ↔ opsOf α' X.ref = []) (Q : Set P) :
    X.Sim Q α α' :=
  ⟨hα, hα', by rw [h]; exact agreeOn_refl _ _, hs⟩

lemma Sim.cfg_eq {α α' : List (LLabel P)} (h : X.Sim Set.univ α α') : X.cfg α = X.cfg α' :=
  config_eq_of_agreeOn_univ h.agree

/-- Schedules of processes of `Q` preserve `Sim Q`. -/
lemma Sim.ext {Q : Set P} {α α' : List (LLabel P)} (h : X.Sim Q α α') {σ : List P}
    (hσ : ∀ p ∈ σ, p ∈ Q) : X.Sim Q (X.ext α σ) (X.ext α' σ) := by
  refine ⟨h.good.ext σ, h.good'.ext σ,
    (transfer h.good h.good' h.agree (fun _ => h.status) hσ).2.1, ?_⟩
  rw [h.good.opsOf_ext_ref_eq_nil, h.good'.opsOf_ext_ref_eq_nil, h.status]

/-- **A quiet step is invisible** to all other processes. -/
lemma Good.sim_quiet {α : List (LLabel P)} (hα : X.Good α) {c : P} (hc : c ≠ X.ref)
    (hq : X.Quiet (X.cfg α) c) : X.Sim {x | x ≠ c} (X.ext α [c]) α := by
  rw [ext_singleton]
  refine ⟨hα.ext1 c, hα, ⟨funext fun j => ?_, fun x hx => (hα.ext1_other hx).1,
    fun x hx => (hα.ext1_other hx).2⟩, by rw [opsOf_ext1_of_ne (Ne.symm hc)]⟩
  obtain ⟨ℓ, hn⟩ := Option.isSome_iff_exists.1 (nl_isSome_of_ne (X := X) (α := α) hc)
  rw [ext1_of_some hn]
  rcases mem_of_step (hα.nl_step hn).1 j with e | ⟨-, hp, o, k, hact, e⟩
  · exact e
  · rw [nl_proc hn] at hp hact
    have hro : (B j).ReadOnly o := by
      by_contra hro; exact hq j ⟨hp, o, k, hact, hro⟩
    rw [e, hro]

/-- **Swapping two non-conflicting steps.** -/
lemma Good.sim_swap {α : List (LLabel P)} (hα : X.Good α) {a b : P} (hab : a ≠ b)
    (hnc : X.NonConflict (X.cfg α) a b) : X.Sim Set.univ (X.ext α [a, b]) (X.ext α [b, a]) := by
  have e1 : X.ext α [a, b] = X.ext1 (X.ext1 α a) b := by
    rw [ext_cons, ext_singleton]
  have e2 : X.ext α [b, a] = X.ext1 (X.ext1 α b) a := by
    rw [ext_cons, ext_singleton]
  have hb' : X.nl (X.ext1 α a) b = X.nl α b := by
    rw [← ext_singleton]; exact hα.nl_ext_of_not_mem (by simpa using Ne.symm hab)
  have ha' : X.nl (X.ext1 α b) a = X.nl α a := by
    rw [← ext_singleton]; exact hα.nl_ext_of_not_mem (by simpa using hab)
  have hlists : ∀ la lb : Option (LLabel P), X.nl α a = la → X.nl α b = lb →
      X.ext α [a, b] = α ++ la.toList ++ lb.toList ∧
        X.ext α [b, a] = α ++ lb.toList ++ la.toList := by
    intro la lb h1 h2
    rw [e1, e2]
    show X.ext1 α a ++ (X.nl (X.ext1 α a) b).toList = _ ∧
      X.ext1 α b ++ (X.nl (X.ext1 α b) a).toList = _
    rw [hb', ha']
    simp only [LLCtx.ext1, h1, h2, and_self]
  have hst : ∀ l₁ l₂ : List (LLabel P), (opsOf (α ++ l₁ ++ l₂) X.ref = [] ↔
      opsOf (α ++ l₂ ++ l₁) X.ref = []) := by
    intro l₁ l₂; simp only [opsOf_append, List.append_eq_nil_iff]; tauto
  cases hna : X.nl α a with
  | none =>
    obtain ⟨h1, h2⟩ := hlists none (X.nl α b) hna rfl
    have : X.ext α [a, b] = X.ext α [b, a] := by rw [h1, h2]; simp
    rw [this]; exact Sim.refl (hα.ext _) _
  | some ℓa =>
    cases hnb : X.nl α b with
    | none =>
      obtain ⟨h1, h2⟩ := hlists (some ℓa) none hna hnb
      have : X.ext α [a, b] = X.ext α [b, a] := by rw [h1, h2]; simp
      rw [this]; exact Sim.refl (hα.ext _) _
    | some ℓb =>
      obtain ⟨h1, h2⟩ := hlists (some ℓa) (some ℓb) hna hnb
      simp only [Option.toList_some] at h1 h2
      have g1 : X.Good (α ++ [ℓa] ++ [ℓb]) := by rw [← h1]; exact hα.ext _
      have g2 : X.Good (α ++ [ℓb] ++ [ℓa]) := by rw [← h2]; exact hα.ext _
      obtain ⟨sa, ga⟩ := hα.nl_step hna
      obtain ⟨sb, gb⟩ := hα.nl_step hnb
      have sab := (ga.nl_step (show X.nl (α ++ [ℓa]) b = some ℓb by
        rw [← ext1_of_some hna, hb', hnb])).1
      have sba := (gb.nl_step (show X.nl (α ++ [ℓb]) a = some ℓa by
        rw [← ext1_of_some hnb, ha', hna])).1
      obtain ⟨Cb, hCb, hCba⟩ := step_comm hab (nl_proc hna) (nl_proc hnb) sa sab (by
        intro i o k j o' k' hta hacta htb hactb
        have hpa := (step_tau (hta ▸ sa)).1
        have hpb := (step_tau (htb ▸ sb)).1
        exact hnc i o k j o' k' hpa hacta hpb hactb)
      rw [sb] at hCb; cases hCb
      rw [sba] at hCba
      rw [h1, h2]
      exact Sim.of_eq g1 g2 (Option.some.inj hCba).symm (hst _ _) _

/-- **Passing a step over a sequence of steps** on other objects. -/
lemma Good.sim_pass {α : List (LLabel P)} (hα : X.Good α) {c : P} {R : ι} {u : List P}
    (hcu : c ∉ u) (hnd : u.Nodup) (hc : X.Accesses (X.cfg α) c R)
    (hu : ∀ a ∈ u, ∃ i, i ≠ R ∧ X.Accesses (X.cfg α) a i) :
    X.Sim Set.univ (X.ext α (c :: u)) (X.ext α (u ++ [c])) := by
  induction u generalizing α with
  | nil => exact Sim.refl (hα.ext _) _
  | cons a u ih =>
    have hca : c ≠ a := fun h => hcu (h ▸ List.mem_cons_self)
    obtain ⟨i, hiR, hai⟩ := hu a List.mem_cons_self
    have h1 := (hα.sim_swap hca (nonConflict_of_ne hc hai (Ne.symm hiR))).ext
      (σ := u) (fun _ _ => trivial)
    have e1 : X.ext (X.ext α [c, a]) u = X.ext α (c :: a :: u) := by
      rw [← ext_append]; rfl
    have e2 : X.ext (X.ext α [a, c]) u = X.ext (X.ext α [a]) (c :: u) := by
      rw [← ext_append, ← ext_append]; rfl
    rw [e1, e2] at h1
    have hg1 := hα.ext [a]
    have hstate : ∀ x, x ≠ a → (X.cfg (X.ext α [a])).loc x = (X.cfg α).loc x ∧
        (X.cfg (X.ext α [a])).pend x = (X.cfg α).pend x := fun x hx =>
      hα.ext_other (by simpa using hx)
    have h2 := ih hg1 (fun h => hcu (List.mem_cons_of_mem _ h)) (List.nodup_cons.1 hnd).2
      (hc.congr (hstate c hca).1.symm (hstate c hca).2.symm)
      (fun a' ha' => by
        obtain ⟨i', h1', h2'⟩ := hu a' (List.mem_cons_of_mem _ ha')
        have hne : a' ≠ a := fun h => (List.nodup_cons.1 hnd).1 (h ▸ ha')
        exact ⟨i', h1', h2'.congr (hstate a' hne).1.symm (hstate a' hne).2.symm⟩)
    have e3 : X.ext (X.ext α [a]) (u ++ [c]) = X.ext α (a :: u ++ [c]) := by
      rw [← ext_append]; rfl
    rw [e3] at h2
    exact h1.trans h2

/-! ### Window registers and test&set objects -/

/-- **A block of writes to a window-like object** (configuration level): the processes of `ws`
are poised to apply non-read-only primitives to `R` in `C`, and agree with `D`. Running them
in `C` and in `D` applies the same primitives to `R`, gives the writers the same states (writes
have state-independent responses), and touches nothing else. -/
lemma window_run {C D : Config (llObj P) B P L} {R : ι}
    (hresp : ∀ o, ¬ (B R).ReadOnly o → ∀ s s', ((B R).δ s o).2 = ((B R).δ s' o).2)
    (ws : List P) (hnd : ws.Nodup) (hag : ∀ a ∈ ws, C.loc a = D.loc a ∧ C.pend a = D.pend a)
    (hwr : ∀ a ∈ ws, X.Writes C a R) :
    ∃ (C' D' : Config (llObj P) B P L) (os : List (B R).Op),
      X.I.runFrom C (ws.map Label.tau) = some C' ∧ X.I.runFrom D (ws.map Label.tau) = some D' ∧
      os.length = ws.length ∧ (∀ o ∈ os, ¬ (B R).ReadOnly o) ∧
      C'.mem R = (B R).runOps (C.mem R) os ∧ D'.mem R = (B R).runOps (D.mem R) os ∧
      (∀ j, j ≠ R → C'.mem j = C.mem j ∧ D'.mem j = D.mem j) ∧
      (∀ a ∈ ws, C'.loc a = D'.loc a ∧ C'.pend a = D'.pend a) ∧
      (∀ x, x ∉ ws → C'.loc x = C.loc x ∧ C'.pend x = C.pend x ∧
        D'.loc x = D.loc x ∧ D'.pend x = D.pend x) := by
  induction ws generalizing C D with
  | nil =>
    exact ⟨C, D, [], rfl, rfl, rfl, by simp, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, by simp,
      fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  | cons a ws ih =>
    obtain ⟨hp, o, k, hact, hro⟩ := hwr a List.mem_cons_self
    obtain ⟨hl, hpd⟩ := hag a List.mem_cons_self
    have hactD : X.I.act a (D.loc a) = .access R o k := by rw [← hl, hact]
    have hpD : D.pend a ≠ none := by rw [← hpd]; exact hp
    set C₁ : Config (llObj P) B P L := { C with
        mem := Function.update C.mem R ((B R).δ (C.mem R) o).1,
        loc := Function.update C.loc a (k ((B R).δ (C.mem R) o).2) } with hC₁
    set D₁ : Config (llObj P) B P L := { D with
        mem := Function.update D.mem R ((B R).δ (D.mem R) o).1,
        loc := Function.update D.loc a (k ((B R).δ (D.mem R) o).2) } with hD₁
    have sC : X.I.step C (.tau a) = some C₁ := by simp [step, hp, hact, hC₁]
    have sD : X.I.step D (.tau a) = some D₁ := by simp [step, hpD, hactD, hD₁]
    have ha_notin : a ∉ ws := (List.nodup_cons.1 hnd).1
    obtain ⟨C', D', os, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := ih (C := C₁) (D := D₁)
      (List.nodup_cons.1 hnd).2
      (fun b hb => by
        have hba : b ≠ a := fun h => ha_notin (h ▸ hb)
        obtain ⟨e1, e2⟩ := hag b (List.mem_cons_of_mem _ hb)
        simp [hC₁, hD₁, Function.update_of_ne hba, e1, e2])
      (fun b hb => by
        have hba : b ≠ a := fun h => ha_notin (h ▸ hb)
        exact (hwr b (List.mem_cons_of_mem _ hb)).congr (by simp [hC₁, Function.update_of_ne hba])
          rfl)
    refine ⟨C', D', o :: os, by simp [sC, r1], by simp [sD, r2], by simp [r3],
      fun o' ho' => ?_, by rw [r5]; simp [hC₁, ObjSpec.runOps_cons],
      by rw [r6]; simp [hD₁, ObjSpec.runOps_cons], fun j hj => ?_, fun b hb => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.1 ho' with rfl | ho'
      · exact hro
      · exact r4 o' ho'
    · rw [(r7 j hj).1, (r7 j hj).2]; simp [hC₁, hD₁, Function.update_of_ne hj]
    · rcases List.mem_cons.1 hb with rfl | hb
      · rw [(r9 b ha_notin).1, (r9 b ha_notin).2.1, (r9 b ha_notin).2.2.1,
          (r9 b ha_notin).2.2.2]
        simp [hC₁, hD₁, hresp o hro (C.mem R) (D.mem R), hpd]
      · exact r8 b hb
    · have hxa : x ≠ a := fun h => hx (h ▸ List.mem_cons_self)
      have hx' : x ∉ ws := fun h => hx (List.mem_cons_of_mem _ h)
      rw [(r9 x hx').1, (r9 x hx').2.1, (r9 x hx').2.2.1, (r9 x hx').2.2.2]
      simp [hC₁, hD₁, Function.update_of_ne hxa]

lemma Good.extL_of_accesses {α : List (LLabel P)} (hα : X.Good α) {ws : List P}
    (hnd : ws.Nodup) (h : ∀ a ∈ ws, ∃ i, X.Accesses (X.cfg α) a i) :
    X.extL α ws = ws.map Label.tau := by
  induction ws generalizing α with
  | nil => rfl
  | cons a ws ih =>
    obtain ⟨i, hi⟩ := h a List.mem_cons_self
    simp only [extL, nl_of_access hi, Option.toList_some, List.map_cons, List.singleton_append,
      List.cons.injEq, true_and]
    apply ih (hα.ext1 a) (List.nodup_cons.1 hnd).2
    intro b hb
    have hba : b ≠ a := fun h' => (List.nodup_cons.1 hnd).1 (h' ▸ hb)
    obtain ⟨j, hj⟩ := h b (List.mem_cons_of_mem _ hb)
    exact ⟨j, hj.congr (hα.ext1_other hba).1.symm (hα.ext1_other hba).2.symm⟩

lemma Good.runFrom_ext {α : List (LLabel P)} (hα : X.Good α) (σ : List P) :
    X.I.runFrom (X.cfg α) (X.extL α σ) = some (X.cfg (X.ext α σ)) := by
  rw [← run_append_of_eq _ hα.run]; exact (hα.ext σ).run

/-- **A block of writes to a window-like object** (schedule level). -/
lemma Good.window {α α' : List (LLabel P)} (hα : X.Good α) (hα' : X.Good α') {R : ι}
    (hresp : ∀ o, ¬ (B R).ReadOnly o → ∀ s s', ((B R).δ s o).2 = ((B R).δ s' o).2)
    {ws : List P} (hnd : ws.Nodup)
    (hag : ∀ a ∈ ws, (X.cfg α).loc a = (X.cfg α').loc a ∧ (X.cfg α).pend a = (X.cfg α').pend a)
    (hwr : ∀ a ∈ ws, X.Writes (X.cfg α) a R) :
    ∃ os : List (B R).Op, os.length = ws.length ∧ (∀ o ∈ os, ¬ (B R).ReadOnly o) ∧
      (X.cfg (X.ext α ws)).mem R = (B R).runOps ((X.cfg α).mem R) os ∧
      (X.cfg (X.ext α' ws)).mem R = (B R).runOps ((X.cfg α').mem R) os ∧
      (∀ j, j ≠ R → (X.cfg (X.ext α ws)).mem j = (X.cfg α).mem j ∧
        (X.cfg (X.ext α' ws)).mem j = (X.cfg α').mem j) ∧
      (∀ a ∈ ws, (X.cfg (X.ext α ws)).loc a = (X.cfg (X.ext α' ws)).loc a ∧
        (X.cfg (X.ext α ws)).pend a = (X.cfg (X.ext α' ws)).pend a) := by
  obtain ⟨C', D', os, r1, r2, r3, r4, r5, r6, r7, r8, -⟩ :=
    window_run hresp ws hnd hag hwr
  have e1 : X.extL α ws = ws.map Label.tau :=
    hα.extL_of_accesses hnd (fun a ha => ⟨R, (hwr a ha).accesses⟩)
  have e2 : X.extL α' ws = ws.map Label.tau :=
    hα'.extL_of_accesses hnd (fun a ha => ⟨R,
      ((hwr a ha).congr (hag a ha).1 (hag a ha).2).accesses⟩)
  have c1 := hα.runFrom_ext ws
  have c2 := hα'.runFrom_ext ws
  rw [e1, r1] at c1; rw [e2, r2] at c2
  cases c1; cases c2
  exact ⟨os, r3, r4, r5, r6, r7, r8⟩

/-- A block of `≥ w` writes to a `w`-window register: afterwards the two executions agree on
`Q` and on the whole memory, if before they agreed on `Q` and on the memory outside `R`. -/
lemma Good.sim_window {α α' : List (LLabel P)} (hα : X.Good α) (hα' : X.Good α') {R : ι}
    {w : ℕ} (hW : (B R).WindowLike w) {ws : List P} (hnd : ws.Nodup) (hne : ws ≠ [])
    (hlen : w ≤ ws.length) {Q : Set P}
    (hagQ : ∀ x ∈ Q, (X.cfg α).loc x = (X.cfg α').loc x ∧ (X.cfg α).pend x = (X.cfg α').pend x)
    (hag : ∀ a ∈ ws, (X.cfg α).loc a = (X.cfg α').loc a ∧ (X.cfg α).pend a = (X.cfg α').pend a)
    (hmem : ∀ j, j ≠ R → (X.cfg α).mem j = (X.cfg α').mem j)
    (hwr : ∀ a ∈ ws, X.Writes (X.cfg α) a R)
    (hst : opsOf α X.ref = [] ↔ opsOf α' X.ref = []) :
    X.Sim Q (X.ext α ws) (X.ext α' ws) := by
  have hresp : ∀ o, ¬ (B R).ReadOnly o → ∀ s s', ((B R).δ s o).2 = ((B R).δ s' o).2 :=
    fun o ho => (hW.1 o).resolve_left ho
  obtain ⟨os, h1, h2, h3, h4, h5, h6⟩ := hα.window hα' hresp hnd hag hwr
  refine ⟨hα.ext ws, hα'.ext ws, ⟨funext fun j => ?_, fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
  · by_cases hj : j = R
    · subst hj; rw [h3, h4]
      exact hW.2 os (by intro h; rw [h] at h1; simp at h1
                        exact hne (List.length_eq_zero_iff.1 h1.symm)) (by omega) h2 _ _
    · rw [(h5 j hj).1, (h5 j hj).2, hmem j hj]
  · by_cases hx' : x ∈ ws
    · exact (h6 x hx').1
    · rw [(hα.ext_other hx').1, (hα'.ext_other hx').1]; exact (hagQ x hx).1
  · by_cases hx' : x ∈ ws
    · exact (h6 x hx').2
    · rw [(hα.ext_other hx').2, (hα'.ext_other hx').2]; exact (hagQ x hx).2
  · rw [hα.opsOf_ext_ref_eq_nil, hα'.opsOf_ext_ref_eq_nil, hst]

/-- Two operations on a test&set-like object leave the same memory. -/
lemma Good.sim_tas {α : List (LLabel P)} (hα : X.Good α) {a b : P} {R : ι}
    (hT : (B R).TASLike) (ha : X.Accesses (X.cfg α) a R) (hb : X.Accesses (X.cfg α) b R)
    (ha' : a ≠ X.ref) (hb' : b ≠ X.ref) :
    X.Sim {x | x ≠ a ∧ x ≠ b} (X.ext α [a]) (X.ext α [b]) := by
  obtain ⟨s₁, hs₁⟩ := hT
  obtain ⟨hpa, oa, ka, hacta⟩ := ha
  obtain ⟨hpb, ob, kb, hactb⟩ := hb
  rw [ext_singleton, ext_singleton]
  refine ⟨hα.ext1 a, hα.ext1 b, ⟨funext fun j => ?_, fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
  · by_cases hj : j = R
    · subst hj
      rw [(hα.mem_ext1_access hpa hacta).1, (hα.mem_ext1_access hpb hactb).1, hs₁, hs₁]
    · have h1 : ¬ X.Accesses (X.cfg α) a j := fun h =>
        hj ((Accesses.unique h ⟨hpa, oa, ka, hacta⟩))
      have h2 : ¬ X.Accesses (X.cfg α) b j := fun h =>
        hj ((Accesses.unique h ⟨hpb, ob, kb, hactb⟩))
      rw [hα.mem_ext1 h1, hα.mem_ext1 h2]
  · rw [(hα.ext1_other hx.1).1, (hα.ext1_other hx.2).1]
  · rw [(hα.ext1_other hx.1).2, (hα.ext1_other hx.2).2]
  · rw [opsOf_ext1_of_ne (Ne.symm ha'), opsOf_ext1_of_ne (Ne.symm hb')]

/-- Once a test&set-like object is set, it stays set. -/
lemma Good.tas_mem {α : List (LLabel P)} (hα : X.Good α) {R : ι} {s₁ : (B R).State}
    (hT : ∀ s o, ((B R).δ s o).1 = s₁) (h : (X.cfg α).mem R = s₁) (σ : List P) :
    (X.cfg (X.ext α σ)).mem R = s₁ := by
  induction σ generalizing α with
  | nil => simpa using h
  | cons p σ ih =>
    rw [ext_cons]
    apply ih (hα.ext1 p)
    by_cases hacc : X.Accesses (X.cfg α) p R
    · obtain ⟨hp, o, k, hact⟩ := hacc
      rw [(hα.mem_ext1_access hp hact).1, hT]
    · rw [hα.mem_ext1 hacc, h]

end LLCtx

end Referee

end Cslib.SharedMemory
