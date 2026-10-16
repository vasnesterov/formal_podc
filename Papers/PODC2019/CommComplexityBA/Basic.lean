import Papers.PODC2019.CommComplexityBA.Model

/-!
# Basic lemmas on executions: coupling, forever-honest nodes, measurability
-/

set_option linter.unusedSectionVars false

open MeasureTheory

namespace CommComplexityBA

variable {P I M Ω : Type*} [DecidableEq P] {f : ℕ}

/-! ### First `some` -/

-- CSLib candidate
lemma firstSome_eq_some_iff {α : Type*} (g : ℕ → Option α) (x : α) :
    firstSome g = some x ↔ ∃ r, g r = some x ∧ ∀ r' < r, g r' = none := by
  classical
  unfold firstSome
  split_ifs with h
  · constructor
    · intro hx
      refine ⟨Nat.find h, hx, fun r' hr' => ?_⟩
      have := Nat.find_min h hr'
      simpa using this
    · rintro ⟨r, hr, hmin⟩
      have hle : Nat.find h ≤ r := Nat.find_min' h (by simp [hr])
      rcases lt_or_eq_of_le hle with hlt | heq
      · have := Nat.find_spec h
        rw [hmin _ hlt] at this
        simp at this
      · rw [heq, hr]
  · simp only [false_iff, not_exists, not_and]
    intro r hr _
    exact h ⟨r, by simp [hr]⟩

lemma firstSome_isSome_iff {α : Type*} (g : ℕ → Option α) :
    (firstSome g).isSome ↔ ∃ r, (g r).isSome := by
  classical
  unfold firstSome
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => Nat.find_spec h⟩
  · simpa using h

namespace Protocol

variable (π : Protocol P I M Ω) (inp : P → I) (ω : Ω)

@[simp] lemma runD_zero (d : List (Pattern P) → P → P → Bool) :
    π.runD inp ω d 0 = (fun _ => [], []) := rfl

lemma runD_succ (d : List (Pattern P) → P → P → Bool) (r : ℕ) :
    π.runD inp ω d (r + 1) = π.stepD inp ω d (π.runD inp ω d r) := rfl

lemma runD_pats_succ (d : List (Pattern P) → P → P → Bool) (r : ℕ) :
    (π.runD inp ω d (r + 1)).2 =
      (π.runD inp ω d r).2 ++ [fun p q => (π.msg inp ω (π.runD inp ω d r).1 p q).isSome] := rfl

lemma runD_hist_succ (d : List (Pattern P) → P → P → Bool) (r : ℕ) (q : P) :
    (π.runD inp ω d (r + 1)).1 q = (π.runD inp ω d r).1 q ++
      [fun p => if d (π.runD inp ω d (r + 1)).2 p q then none
        else π.msg inp ω (π.runD inp ω d r).1 p q] := rfl

/-- **Coupling.** Two omission rules that agree on every message actually sent in the execution of
the first one produce the same execution. -/
lemma runD_congr (d₁ d₂ : List (Pattern P) → P → P → Bool)
    (h : ∀ r p q, (π.msg inp ω (π.runD inp ω d₁ r).1 p q).isSome →
      d₁ (π.runD inp ω d₁ (r + 1)).2 p q = d₂ (π.runD inp ω d₁ (r + 1)).2 p q) :
    ∀ r, π.runD inp ω d₁ r = π.runD inp ω d₂ r := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [runD_succ, runD_succ, ← ih]
    simp only [stepD, Prod.mk.injEq, and_true]
    funext q
    congr 2
    funext p
    by_cases hs : (π.msg inp ω (π.runD inp ω d₁ r).1 p q).isSome
    · have := h r p q hs
      simp only [runD_pats_succ] at this
      rw [this]
    · simp only [Option.not_isSome_iff_eq_none] at hs
      simp [hs]

/-- Corruptions only grow along an execution. -/
lemma corrupt_run_mono (A : Adversary P f) {r r' : ℕ} (hr : r ≤ r') :
    A.corrupt (π.run inp ω A (r + 1)).2 ⊆ A.corrupt (π.run inp ω A (r' + 1)).2 := by
  induction hr with
  | refl => exact le_rfl
  | step _ ih =>
    refine ih.trans ?_
    simp only [run]
    rw [runD_pats_succ _ _ _ _ (_ + 1)]
    exact A.corrupt_mono _ _

/-- If the adversary never corrupts more than `c` nodes, then a set of more than `c` nodes contains
a forever-honest node. -/
lemma exists_honest (A : Adversary P f) {c : ℕ} (hc : ∀ l, (A.corrupt l).card ≤ c)
    (W : Finset P) (hW : c < W.card) : ∃ w ∈ W, π.Honest inp ω A w := by
  classical
  by_contra hcon
  push Not at hcon
  simp only [Honest, not_forall, not_not] at hcon
  choose! R hR using hcon
  have hsub : W ⊆ A.corrupt (π.run inp ω A (W.sup R + 1)).2 := fun w hw =>
    corrupt_run_mono π inp ω A (Finset.le_sup hw) (hR w hw)
  have := (Finset.card_le_card hsub).trans (hc _)
  omega

end Protocol

/-! ### Measurability via fibres -/

section Meas

variable [MeasurableSpace Ω]

-- CSLib candidate (general measurability via countable fibres)
/-- All fibres of `g` are measurable (for countable codomains this is measurability). -/
def FiberMeas {X : Type*} (g : Ω → X) : Prop := ∀ x, MeasurableSet {ω | g ω = x}

lemma FiberMeas.const {X : Type*} (x₀ : X) : FiberMeas (fun _ : Ω => x₀) := by
  classical
  intro x
  by_cases h : x₀ = x <;> simp [h]

lemma FiberMeas.preimage {X : Type*} [Countable X] {g : Ω → X} (hg : FiberMeas g) (S : Set X) :
    MeasurableSet {ω | g ω ∈ S} := by
  have : {ω | g ω ∈ S} = ⋃ x ∈ S, {ω | g ω = x} := by ext; simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable S) fun x _ => hg x

lemma FiberMeas.map {X Y : Type*} [Countable X] {g : Ω → X} (hg : FiberMeas g) (h : X → Y) :
    FiberMeas (fun ω => h (g ω)) := fun y => hg.preimage {x | h x = y}

lemma FiberMeas.bind {X Y : Type*} [Countable X] {g : Ω → X} (hg : FiberMeas g)
    {F : Ω → X → Y} (hF : ∀ x, FiberMeas (fun ω => F ω x)) : FiberMeas (fun ω => F ω (g ω)) := by
  intro y
  have : {ω | F ω (g ω) = y} = ⋃ x, {ω | g ω = x} ∩ {ω | F ω x = y} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.iUnion fun x => (hg x).inter (hF x y)

lemma FiberMeas.pi {ι : Type*} [Finite ι] {X : ι → Type*} {g : Ω → ∀ i, X i}
    (hg : ∀ i, FiberMeas fun ω => g ω i) : FiberMeas g := by
  intro x
  have : {ω | g ω = x} = ⋂ i, {ω | g ω i = x i} := by ext; simp [funext_iff]
  rw [this]
  exact MeasurableSet.iInter fun i => hg i (x i)

lemma FiberMeas.measurable {X : Type*} [Countable X] [MeasurableSpace X]
    {g : Ω → X} (hg : FiberMeas g) : Measurable g :=
  measurable_to_countable' fun x => hg x

variable [Fintype P] [Countable M]

namespace Protocol

variable (π : Protocol P I M Ω) (inp : P → I)

lemma fiberMeas_msg (hπ : π.IsMeasurable) (h : P → History P M) (p q : P) :
    FiberMeas (fun ω => π.msg inp ω h p q) := by
  by_cases hpq : p = q
  · simp only [msg, hpq, ite_true]; exact FiberMeas.const _
  · simp only [msg, hpq, ite_false]; exact hπ.1 _ _ _ _

lemma fiberMeas_runD (hπ : π.IsMeasurable) (d : List (Pattern P) → P → P → Bool) (r : ℕ) :
    FiberMeas (fun ω => π.runD inp ω d r) := by
  induction r with
  | zero => exact FiberMeas.const _
  | succ r ih =>
    simp only [runD_succ]
    refine ih.bind (F := fun ω s => π.stepD inp ω d s) fun s => ?_
    -- `stepD` depends on `ω` only through the finite family of messages
    have hm : FiberMeas (fun ω => fun p q => π.msg inp ω s.1 p q) :=
      FiberMeas.pi fun p => FiberMeas.pi fun q => π.fiberMeas_msg inp hπ s.1 p q
    exact hm.map (fun m => (fun q => s.1 q ++
      [fun p => if d (s.2 ++ [fun p q => (m p q).isSome]) p q then none else m p q],
      s.2 ++ [fun p q => (m p q).isSome]))

lemma measurableSet_sentAt (hπ : π.IsMeasurable) (A : Adversary P f) (r : ℕ) (p q : P) :
    MeasurableSet {ω | π.sentAt inp ω A r p q = true} := by
  have : FiberMeas (fun ω => π.sentAt inp ω A r p q) :=
    (π.fiberMeas_runD inp hπ A.drop r).bind (F := fun ω s => (π.msg inp ω s.1 p q).isSome)
      fun s => (π.fiberMeas_msg inp hπ s.1 p q).map _
  exact this true

lemma fiberMeas_silentOut (hπ : π.IsMeasurable) (p : P) (x : I) :
    FiberMeas (fun ω => π.silentOut p x ω) := by
  classical
  have hg : ∀ r o, MeasurableSet
      {ω | π.decide p x ω (List.replicate r fun _ => none) = o} := fun r o => hπ.2 _ _ _ _
  intro o
  cases o with
  | some b =>
    have : {ω | π.silentOut p x ω = some b} = ⋃ r, ({ω | π.decide p x ω
        (List.replicate r fun _ => none) = some b} ∩
          ⋂ r' ∈ Finset.range r, {ω | π.decide p x ω (List.replicate r' fun _ => none) = none}) := by
      ext ω
      simp only [silentOut, Set.mem_ofPred_eq, firstSome_eq_some_iff, Set.mem_iUnion,
        Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range]
    rw [this]
    exact MeasurableSet.iUnion fun r => (hg r _).inter
      (MeasurableSet.biInter (Set.to_countable _) fun r' _ => hg r' _)
  | none =>
    have : {ω | π.silentOut p x ω = none} =
        ⋂ r, {ω | π.decide p x ω (List.replicate r fun _ => none) = none} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, silentOut]
      rw [← Option.not_isSome_iff_eq_none, firstSome_isSome_iff]
      simp
    rw [this]
    exact MeasurableSet.iInter fun r => hg r _

end Protocol

end Meas

end CommComplexityBA
