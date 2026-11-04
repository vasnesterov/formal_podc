import Cslib.Computability.Distributed.SharedMemory.Covering

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Contention.lean

/-!
# Base objects accessed and written by execution fragments; commuting non-contending fragments

For an execution fragment `α` (a list of labels) run from a configuration `C`:

* `Impl.accessed I C α` — the base objects to which some step of `α` applies a primitive;
* `Impl.written I C α` — the base objects to which some step of `α` applies a *non-trivial*
  primitive (one that is not `ObjSpec.ReadOnly`, i.e. that may change the state).

Two fragments *contend* on `b` if both access `b` and one of them writes it (Ellen et al.,
PODC 2012; Attiya–Hillel–Milani). Main results:

* `Impl.mem_eq_of_not_written` — a fragment does not change objects it does not write;
* `Impl.runFrom_frame` — **frame lemma**: a fragment of a single process only depends on the
  state of that process and on the objects it accesses;
* `Impl.runFrom_comm` — **commutation**: fragments of two distinct processes that do not contend
  (neither accesses an object the other writes) can be reordered, with the same final
  configuration;
* `Impl.mem_accessed_soloLabels`, `Impl.mem_written_soloLabels` — the objects accessed/written by
  a solo run, step by step;
* `Impl.AgreeExcept`, `Impl.iterate_soloStep_agreeExcept` — solo runs from configurations that
  differ only on a set `X` of objects (and on other processes) take the same steps as long as
  they do not access `X`;
* `Impl.soloLabels_add` — splitting a solo run.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-- The step `ℓ`, taken in `C`, applies a primitive to base object `i`. -/
def StepAccess (C : Config A B P L) (ℓ : Label P A) (i : ι) : Prop :=
  ∃ r o k, ℓ = .tau r ∧ C.pend r ≠ none ∧ I.act r (C.loc r) = .access i o k

/-- The step `ℓ`, taken in `C`, applies a non-trivial primitive to base object `i`. -/
def StepWrite (C : Config A B P L) (ℓ : Label P A) (i : ι) : Prop :=
  ∃ r o k, ℓ = .tau r ∧ C.pend r ≠ none ∧ I.act r (C.loc r) = .access i o k ∧
    ¬ (B i).ReadOnly o

/-- Base objects accessed by the fragment `α` run from `C` (up to its first disabled label). -/
noncomputable def accessed : Config A B P L → List (Label P A) → Set ι
  | _, [] => ∅
  | C, ℓ :: α => {i | I.StepAccess C ℓ i} ∪
      (match I.step C ℓ with
        | some C' => accessed C' α
        | none => ∅)

/-- Base objects written (non-trivially accessed) by the fragment `α` run from `C`. -/
noncomputable def written : Config A B P L → List (Label P A) → Set ι
  | _, [] => ∅
  | C, ℓ :: α => {i | I.StepWrite C ℓ i} ∪
      (match I.step C ℓ with
        | some C' => written C' α
        | none => ∅)

variable {I}

@[simp] lemma accessed_nil (C : Config A B P L) : I.accessed C [] = ∅ := rfl
@[simp] lemma written_nil (C : Config A B P L) : I.written C [] = ∅ := rfl

lemma accessed_cons_of_step {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C')
    (α : List (Label P A)) :
    I.accessed C (ℓ :: α) = {i | I.StepAccess C ℓ i} ∪ I.accessed C' α := by
  simp [accessed, h]

lemma written_cons_of_step {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C')
    (α : List (Label P A)) :
    I.written C (ℓ :: α) = {i | I.StepWrite C ℓ i} ∪ I.written C' α := by
  simp [written, h]

lemma accessed_append {C C' : Config A B P L} {α : List (Label P A)}
    (h : I.runFrom C α = some C') (β : List (Label P A)) :
    I.accessed C (α ++ β) = I.accessed C α ∪ I.accessed C' β := by
  induction α generalizing C with
  | nil => simp only [runFrom_nil, Option.some.injEq] at h; subst h; simp
  | cons ℓ α ih =>
    simp only [runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      rw [List.cons_append, accessed_cons_of_step hs, accessed_cons_of_step hs, ih h,
        Set.union_assoc]

lemma written_append {C C' : Config A B P L} {α : List (Label P A)}
    (h : I.runFrom C α = some C') (β : List (Label P A)) :
    I.written C (α ++ β) = I.written C α ∪ I.written C' β := by
  induction α generalizing C with
  | nil => simp only [runFrom_nil, Option.some.injEq] at h; subst h; simp
  | cons ℓ α ih =>
    simp only [runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      rw [List.cons_append, written_cons_of_step hs, written_cons_of_step hs, ih h,
        Set.union_assoc]

lemma written_subset_accessed (C : Config A B P L) (α : List (Label P A)) :
    I.written C α ⊆ I.accessed C α := by
  induction α generalizing C with
  | nil => simp
  | cons ℓ α ih =>
    cases hs : I.step C ℓ with
    | none =>
      simp only [written, accessed, hs]
      intro i hi
      rcases hi with ⟨r, o, k, h1, h2, h3, -⟩ | hi
      · exact Or.inl ⟨r, o, k, h1, h2, h3⟩
      · exact absurd hi (Set.notMem_empty i)
    | some C₁ =>
      rw [written_cons_of_step hs, accessed_cons_of_step hs]
      rintro i (⟨r, o, k, h1, h2, h3, -⟩ | hi)
      · exact Or.inl ⟨r, o, k, h1, h2, h3⟩
      · exact Or.inr (ih C₁ hi)

/-- A single step does not change an object it does not write. -/
lemma step_mem_of_not_write {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C')
    {i : ι} (hi : ¬ I.StepWrite C ℓ i) : C'.mem i = C.mem i := by
  rcases mem_of_step h i with e | ⟨hτ, hp, o, k, hact, e⟩
  · exact e
  · rw [e]
    by_contra hne
    exact hi ⟨ℓ.proc, o, k, hτ, hp, hact, fun hro => hne (hro _)⟩

/-- A fragment does not change the objects it does not write. -/
lemma mem_eq_of_not_written {C C' : Config A B P L} {α : List (Label P A)}
    (h : I.runFrom C α = some C') {i : ι} (hi : i ∉ I.written C α) : C'.mem i = C.mem i := by
  induction α generalizing C with
  | nil => simp only [runFrom_nil, Option.some.injEq] at h; subst h; rfl
  | cons ℓ α ih =>
    simp only [runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      rw [written_cons_of_step hs] at hi
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hi
      rw [ih h hi.2, step_mem_of_not_write hs hi.1]

lemma mem_eq_of_not_accessed {C C' : Config A B P L} {α : List (Label P A)}
    (h : I.runFrom C α = some C') {i : ι} (hi : i ∉ I.accessed C α) : C'.mem i = C.mem i :=
  mem_eq_of_not_written h (fun h' => hi (written_subset_accessed C α h'))

lemma stepAccess_congr {r : P} {C D : Config A B P L} {ℓ : Label P A} (hℓ : ℓ.proc = r)
    (hloc : C.loc r = D.loc r) (hpend : C.pend r = D.pend r) (i : ι) :
    I.StepAccess C ℓ i ↔ I.StepAccess D ℓ i := by
  constructor
  · rintro ⟨r', o, k, rfl, h2, h3⟩
    simp only [Label.proc] at hℓ; subst hℓ
    exact ⟨_, o, k, rfl, hpend ▸ h2, hloc ▸ h3⟩
  · rintro ⟨r', o, k, rfl, h2, h3⟩
    simp only [Label.proc] at hℓ; subst hℓ
    exact ⟨_, o, k, rfl, hpend ▸ h2, hloc ▸ h3⟩

lemma stepWrite_congr {r : P} {C D : Config A B P L} {ℓ : Label P A} (hℓ : ℓ.proc = r)
    (hloc : C.loc r = D.loc r) (hpend : C.pend r = D.pend r) (i : ι) :
    I.StepWrite C ℓ i ↔ I.StepWrite D ℓ i := by
  constructor
  · rintro ⟨r', o, k, rfl, h2, h3, h4⟩
    simp only [Label.proc] at hℓ; subst hℓ
    exact ⟨_, o, k, rfl, hpend ▸ h2, hloc ▸ h3, h4⟩
  · rintro ⟨r', o, k, rfl, h2, h3, h4⟩
    simp only [Label.proc] at hℓ; subst hℓ
    exact ⟨_, o, k, rfl, hpend ▸ h2, hloc ▸ h3, h4⟩

/-- **Frame lemma.** A fragment `α` of process `r` that runs from `C` also runs from any `D` that
agrees with `C` on `r` and on the objects `α` accesses; it accesses and writes the same objects,
and the result agrees with the result from `C` on `r` and on the accessed objects, and with `D`
elsewhere. -/
lemma runFrom_frame {r : P} {C C' D : Config A B P L} {α : List (Label P A)}
    (hα : ∀ ℓ ∈ α, ℓ.proc = r) (h : I.runFrom C α = some C')
    (hloc : C.loc r = D.loc r) (hpend : C.pend r = D.pend r)
    (hmem : ∀ i ∈ I.accessed C α, C.mem i = D.mem i) :
    ∃ D', I.runFrom D α = some D' ∧ I.accessed D α = I.accessed C α ∧
      I.written D α = I.written C α ∧ D'.loc r = C'.loc r ∧ D'.pend r = C'.pend r ∧
      (∀ x, x ≠ r → D'.loc x = D.loc x ∧ D'.pend x = D.pend x) ∧
      (∀ i ∈ I.accessed C α, D'.mem i = C'.mem i) ∧
      (∀ i ∉ I.accessed C α, D'.mem i = D.mem i) := by
  induction α generalizing C D with
  | nil =>
    simp only [runFrom_nil, Option.some.injEq] at h; subst h
    exact ⟨D, rfl, rfl, rfl, hloc.symm, hpend.symm, fun _ _ => ⟨rfl, rfl⟩, by simp,
      fun _ _ => rfl⟩
  | cons ℓ α ih =>
    simp only [runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have hℓ : ℓ.proc = r := hα ℓ (by simp)
      have hacc := accessed_cons_of_step hs α
      have hobj : ∀ i o k, ℓ = .tau r → I.act r (C.loc r) = .access i o k →
          C.mem i = D.mem i := by
        intro i o k hτ hact
        refine hmem i ?_
        rw [hacc]
        exact Or.inl ⟨r, o, k, hτ, (step_tau (hτ ▸ hs)).1, hact⟩
      obtain ⟨D₁, hD₁, hl1, hp1, ho1, hm1⟩ := step_exact (I := I) hℓ hloc hpend hobj hs
      have hmem₁ : ∀ i ∈ I.accessed C₁ α, C₁.mem i = D₁.mem i := by
        intro i hi
        rcases hm1 i with ⟨e1, e2⟩ | ⟨e1, -⟩
        · rw [e1, e2]; exact hmem i (by rw [hacc]; exact Or.inr hi)
        · exact e1.symm
      obtain ⟨D', hD', ha, hw, hl, hp, ho, hmi, hmo⟩ :=
        ih (fun ℓ' h' => hα ℓ' (by simp [h'])) h hl1.symm hp1.symm hmem₁
      refine ⟨D', by simp [hD₁, hD'], ?_, ?_, hl, hp, ?_, ?_, ?_⟩
      · rw [accessed_cons_of_step hD₁, hacc, ha]
        ext i; simp only [Set.mem_union, Set.mem_ofPred_eq]
        rw [stepAccess_congr hℓ hloc hpend]
      · rw [written_cons_of_step hD₁, written_cons_of_step hs, hw]
        ext i; simp only [Set.mem_union, Set.mem_ofPred_eq]
        rw [stepWrite_congr hℓ hloc hpend]
      · intro x hx
        obtain ⟨a1, a2⟩ := ho x hx
        obtain ⟨b1, b2⟩ := ho1 x hx
        exact ⟨a1.trans b1, a2.trans b2⟩
      · intro i hi
        by_cases hi₁ : i ∈ I.accessed C₁ α
        · exact hmi i hi₁
        · rw [hmo i hi₁, mem_eq_of_not_accessed h hi₁]
          rcases hm1 i with ⟨e1, e2⟩ | ⟨e1, -⟩
          · rw [e1, e2]; exact (hmem i hi).symm
          · exact e1
      · intro i hi
        rw [hacc] at hi
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hi
        rw [hmo i hi.2]
        rcases hm1 i with ⟨e1, -⟩ | ⟨-, hτ, o, k, hact⟩
        · exact e1
        · exact absurd ⟨r, o, k, hτ, (step_tau (hτ ▸ hs)).1, hact⟩ hi.1

/-- **Commuting non-contending fragments.** If fragments `α` of `r` and `β` of `s ≠ r` both run
from `C`, and neither accesses an object the other writes, then `α ++ β` and `β ++ α` lead to the
same configuration. -/
lemma runFrom_comm {r s : P} (hrs : r ≠ s) {C Cα Cβ : Config A B P L}
    {α β : List (Label P A)} (hα : ∀ ℓ ∈ α, ℓ.proc = r) (hβ : ∀ ℓ ∈ β, ℓ.proc = s)
    (h1 : I.runFrom C α = some Cα) (h2 : I.runFrom C β = some Cβ)
    (hd1 : ∀ i ∈ I.accessed C α, i ∉ I.written C β)
    (hd2 : ∀ i ∈ I.written C α, i ∉ I.accessed C β) :
    ∃ D, I.runFrom Cα β = some D ∧ I.runFrom Cβ α = some D := by
  have oα := I.runFrom_other h1 (q := s) (fun ℓ h => by rw [hα ℓ h]; exact hrs)
  have oβ := I.runFrom_other h2 (q := r) (fun ℓ h => by rw [hβ ℓ h]; exact hrs.symm)
  obtain ⟨D₁, hD₁, -, -, l1, p1, o1, mi1, mo1⟩ := runFrom_frame hβ h2 oα.1.symm oα.2.symm
    (fun i hi => (mem_eq_of_not_written h1 (fun h' => hd2 i h' hi)).symm)
  obtain ⟨D₂, hD₂, -, -, l2, p2, o2, mi2, mo2⟩ := runFrom_frame hα h1 oβ.1.symm oβ.2.symm
    (fun i hi => (mem_eq_of_not_written h2 (hd1 i hi)).symm)
  refine ⟨D₁, hD₁, ?_⟩
  rw [hD₂]
  congr 1
  have hloc : D₂.loc = D₁.loc := by
    funext x
    by_cases hxr : x = r
    · subst hxr; rw [l2, (o1 x hrs).1]
    · by_cases hxs : x = s
      · subst hxs; rw [l1, (o2 x hxr).1]
      · rw [(o2 x hxr).1, (o1 x hxs).1, (I.runFrom_other h1 (q := x)
          (fun ℓ h => by rw [hα ℓ h]; exact Ne.symm hxr)).1,
          (I.runFrom_other h2 (q := x) (fun ℓ h => by rw [hβ ℓ h]; exact Ne.symm hxs)).1]
  have hpend : D₂.pend = D₁.pend := by
    funext x
    by_cases hxr : x = r
    · subst hxr; rw [p2, (o1 x hrs).2]
    · by_cases hxs : x = s
      · subst hxs; rw [p1, (o2 x hxr).2]
      · rw [(o2 x hxr).2, (o1 x hxs).2, (I.runFrom_other h1 (q := x)
          (fun ℓ h => by rw [hα ℓ h]; exact Ne.symm hxr)).2,
          (I.runFrom_other h2 (q := x) (fun ℓ h => by rw [hβ ℓ h]; exact Ne.symm hxs)).2]
  have hmem : D₂.mem = D₁.mem := by
    funext i
    by_cases hb : i ∈ I.accessed C β
    · rw [mi1 i hb]
      by_cases ha : i ∈ I.accessed C α
      · rw [mi2 i ha, mem_eq_of_not_written h1 (fun h' => hd2 i h' hb),
          mem_eq_of_not_written h2 (hd1 i ha)]
      · rw [mo2 i ha]
    · rw [mo1 i hb]
      by_cases ha : i ∈ I.accessed C α
      · rw [mi2 i ha]
      · rw [mo2 i ha, mem_eq_of_not_accessed h1 ha, mem_eq_of_not_accessed h2 hb]
  cases D₁; cases D₂
  simp only at hloc hpend hmem
  rw [hloc, hpend, hmem]

/-! ### Solo runs -/

/-- In `C`, process `p` is pending and its next step applies a primitive to object `i`. -/
def SoloAcc (p : P) (i : ι) (C : Config A B P L) : Prop :=
  C.pend p ≠ none ∧ ∃ o k, I.act p (C.loc p) = .access i o k

/-- In `C`, process `p` is pending and its next step applies a non-trivial primitive to `i`. -/
def SoloWr (p : P) (i : ι) (C : Config A B P L) : Prop :=
  C.pend p ≠ none ∧ ∃ o k, I.act p (C.loc p) = .access i o k ∧ ¬ (B i).ReadOnly o

lemma soloStep_of_idle {p : P} {C : Config A B P L} (h : C.pend p = none) :
    I.soloStep p C = C := by
  simp [soloStep, h]

lemma iterate_soloStep_of_idle {p : P} {C : Config A B P L} (h : C.pend p = none) (k : ℕ) :
    (I.soloStep p)^[k] C = C := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, soloStep_of_idle h, ih]

lemma soloLabels_of_idle {p : P} {C : Config A B P L} (h : C.pend p = none) (k : ℕ) :
    I.soloLabels p C k = [] := by
  cases k with
  | zero => rfl
  | succ k => simp [soloLabels, h]

lemma step_nextLabel {p : P} {C : Config A B P L} (h : C.pend p ≠ none) :
    I.step C (I.nextLabel C p) = some (I.soloStep p C) := by
  obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 (I.step_nextLabel_isSome C p h)
  simp [soloStep, h, hC']

lemma stepAccess_nextLabel {p : P} {C : Config A B P L} (i : ι) :
    I.StepAccess C (I.nextLabel C p) i ↔ I.SoloAcc p i C := by
  unfold nextLabel SoloAcc
  split
  · rename_i j o k hact
    constructor
    · rintro ⟨r, o', k', h1, h2, h3⟩
      cases h1
      exact ⟨h2, o', k', h3⟩
    · rintro ⟨h2, o', k', h3⟩
      exact ⟨p, o', k', rfl, h2, h3⟩
  · rename_i r l hact
    constructor
    · rintro ⟨r', o', k', h1, -⟩; cases h1
    · rintro ⟨-, o', k', h3⟩; rw [hact] at h3; cases h3

lemma stepWrite_nextLabel {p : P} {C : Config A B P L} (i : ι) :
    I.StepWrite C (I.nextLabel C p) i ↔ I.SoloWr p i C := by
  unfold nextLabel SoloWr
  split
  · rename_i j o k hact
    constructor
    · rintro ⟨r, o', k', h1, h2, h3, h4⟩
      cases h1
      exact ⟨h2, o', k', h3, h4⟩
    · rintro ⟨h2, o', k', h3, h4⟩
      exact ⟨p, o', k', rfl, h2, h3, h4⟩
  · rename_i r l hact
    constructor
    · rintro ⟨r', o', k', h1, -⟩; cases h1
    · rintro ⟨-, o', k', h3, -⟩; rw [hact] at h3; cases h3

/-- The objects accessed by `k` solo steps of `p`. -/
lemma mem_accessed_soloLabels (p : P) (C : Config A B P L) (n : ℕ) (i : ι) :
    i ∈ I.accessed C (I.soloLabels p C n) ↔ ∃ k < n, I.SoloAcc p i ((I.soloStep p)^[k] C) := by
  induction n generalizing C with
  | zero => simp [soloLabels]
  | succ n ih =>
    by_cases hp : C.pend p = none
    · rw [soloLabels_of_idle hp]
      simp only [accessed_nil, Set.mem_empty_iff_false, false_iff, not_exists, not_and]
      intro k _ h
      rw [iterate_soloStep_of_idle hp] at h
      exact h.1 hp
    · rw [soloLabels_succ, ite_eq_right hp, accessed_cons_of_step (step_nextLabel hp)]
      simp only [Set.mem_union, Set.mem_ofPred_eq, stepAccess_nextLabel, ih]
      constructor
      · rintro (h | ⟨k, hk, h⟩)
        · exact ⟨0, by omega, h⟩
        · exact ⟨k + 1, by omega, by rwa [Function.iterate_succ_apply]⟩
      · rintro ⟨k, hk, h⟩
        cases k with
        | zero => exact Or.inl h
        | succ k => exact Or.inr ⟨k, by omega, by rwa [Function.iterate_succ_apply] at h⟩

/-- The objects written by `k` solo steps of `p`. -/
lemma mem_written_soloLabels (p : P) (C : Config A B P L) (n : ℕ) (i : ι) :
    i ∈ I.written C (I.soloLabels p C n) ↔ ∃ k < n, I.SoloWr p i ((I.soloStep p)^[k] C) := by
  induction n generalizing C with
  | zero => simp [soloLabels]
  | succ n ih =>
    by_cases hp : C.pend p = none
    · rw [soloLabels_of_idle hp]
      simp only [written_nil, Set.mem_empty_iff_false, false_iff, not_exists, not_and]
      intro k _ h
      rw [iterate_soloStep_of_idle hp] at h
      exact h.1 hp
    · rw [soloLabels_succ, ite_eq_right hp, written_cons_of_step (step_nextLabel hp)]
      simp only [Set.mem_union, Set.mem_ofPred_eq, stepWrite_nextLabel, ih]
      constructor
      · rintro (h | ⟨k, hk, h⟩)
        · exact ⟨0, by omega, h⟩
        · exact ⟨k + 1, by omega, by rwa [Function.iterate_succ_apply]⟩
      · rintro ⟨k, hk, h⟩
        cases k with
        | zero => exact Or.inl h
        | succ k => exact Or.inr ⟨k, by omega, by rwa [Function.iterate_succ_apply] at h⟩

/-- Splitting a solo run. -/
lemma soloLabels_add (p : P) (C : Config A B P L) (a b : ℕ) :
    I.soloLabels p C (a + b) = I.soloLabels p C a ++ I.soloLabels p ((I.soloStep p)^[a] C) b := by
  induction a generalizing C with
  | zero => simp [soloLabels]
  | succ a ih =>
    by_cases hp : C.pend p = none
    · rw [soloLabels_of_idle hp, soloLabels_of_idle hp, iterate_soloStep_of_idle hp,
        soloLabels_of_idle hp]
      rfl
    · rw [show a + 1 + b = (a + b) + 1 by omega, soloLabels_succ, soloLabels_succ, ite_eq_right hp,
        ite_eq_right hp, ih, Function.iterate_succ_apply]
      rfl

/-- `C` and `D` agree on process `p` and on all objects outside `X`. -/
structure AgreeExcept (p : P) (X : Set ι) (C D : Config A B P L) : Prop where
  loc : C.loc p = D.loc p
  pend : C.pend p = D.pend p
  mem : ∀ i ∉ X, C.mem i = D.mem i

lemma AgreeExcept.symm {p : P} {X : Set ι} {C D : Config A B P L} (h : AgreeExcept p X C D) :
    AgreeExcept p X D C :=
  ⟨h.loc.symm, h.pend.symm, fun i hi => (h.mem i hi).symm⟩

lemma AgreeExcept.trans {p : P} {X Y : Set ι} {C D E : Config A B P L}
    (h : AgreeExcept p X C D) (h' : AgreeExcept p Y D E) : AgreeExcept p (X ∪ Y) C E :=
  ⟨h.loc.trans h'.loc, h.pend.trans h'.pend,
    fun i hi => (h.mem i (fun h'' => hi (Or.inl h''))).trans (h'.mem i (fun h'' => hi (Or.inr h'')))⟩

lemma AgreeExcept.mono {p : P} {X Y : Set ι} {C D : Config A B P L} (h : AgreeExcept p X C D)
    (hXY : X ⊆ Y) : AgreeExcept p Y C D :=
  ⟨h.loc, h.pend, fun i hi => h.mem i (fun h' => hi (hXY h'))⟩

lemma AgreeExcept.soloAcc_iff {p : P} {X : Set ι} {C D : Config A B P L}
    (h : AgreeExcept p X C D) (i : ι) : I.SoloAcc p i C ↔ I.SoloAcc p i D := by
  simp only [SoloAcc, h.loc, h.pend]

lemma AgreeExcept.soloWr_iff {p : P} {X : Set ι} {C D : Config A B P L}
    (h : AgreeExcept p X C D) (i : ι) : I.SoloWr p i C ↔ I.SoloWr p i D := by
  simp only [SoloWr, h.loc, h.pend]

/-- One solo step that does not access `X` preserves agreement outside `X`. -/
lemma AgreeExcept.soloStep {p : P} {X : Set ι} {C D : Config A B P L} (h : AgreeExcept p X C D)
    (hX : ∀ i ∈ X, ¬ I.SoloAcc p i C) :
    AgreeExcept p X (I.soloStep p C) (I.soloStep p D) ∧ I.nextLabel C p = I.nextLabel D p := by
  have hnl : I.nextLabel C p = I.nextLabel D p := by simp only [nextLabel, h.loc]
  refine ⟨?_, hnl⟩
  by_cases hp : C.pend p = none
  · have hp' : D.pend p = none := h.pend ▸ hp
    rw [soloStep_of_idle hp, soloStep_of_idle hp']; exact h
  · have hp' : D.pend p ≠ none := h.pend ▸ hp
    have hC := step_nextLabel (I := I) hp
    obtain ⟨D', hD', hl, hpe, hm⟩ := step_local (I := I) h.loc h.pend (I.nextLabel_proc C p)
      (fun hτ i o k hact _ => h.mem i (fun hi => hX i hi ⟨hp, o, k, hact⟩)) hC
    have hD := step_nextLabel (I := I) hp'
    rw [hnl, hD] at hD'
    cases hD'
    refine ⟨hl, hpe, fun j hj => ?_⟩
    rcases hm j with ⟨e1, e2⟩ | e
    · rw [e1, e2]; exact h.mem j hj
    · exact e

/-- Solo runs from configurations that agree outside `X` take the same steps as long as they do
not access `X`. -/
lemma AgreeExcept.iterate_soloStep {p : P} {X : Set ι} {C D : Config A B P L}
    (h : AgreeExcept p X C D) (n : ℕ)
    (hX : ∀ k < n, ∀ i ∈ X, ¬ I.SoloAcc p i ((I.soloStep p)^[k] C)) :
    AgreeExcept p X ((I.soloStep p)^[n] C) ((I.soloStep p)^[n] D) ∧
      I.soloLabels p C n = I.soloLabels p D n := by
  induction n generalizing C D with
  | zero => exact ⟨h, rfl⟩
  | succ n ih =>
    obtain ⟨h1, hnl⟩ := h.soloStep (hX 0 (by omega))
    obtain ⟨h2, hl⟩ := ih h1 (fun k hk i hi => by
      have := hX (k + 1) (by omega) i hi
      rwa [Function.iterate_succ_apply] at this)
    refine ⟨by simpa only [Function.iterate_succ_apply] using h2, ?_⟩
    rw [soloLabels_succ, soloLabels_succ, hl, hnl, h.pend]

end Impl

end Cslib.SharedMemory
