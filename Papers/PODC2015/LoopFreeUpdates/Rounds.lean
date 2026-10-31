import Papers.PODC2015.LoopFreeUpdates.Basic

/-!
# Two and three rounds (§3.1, §3.2.1 of the paper)

* In the first round only nodes with a forward new rule (types `F·`) can be updated, in the last
  round only nodes with a forward old rule (types `·F`) (`dashedFwd_of_mem_first`,
  `solidFwd_of_mem_last`).
* §3.1: a 2-round schedule exists iff there is no `BB` node (`hasSLF_two_iff`).
* Lemma 1, corrected: `F·` nodes of round 2 can be moved to round 1 (`lemma_1`), and `·F` nodes of
  round 2 can be moved to round 3 (`lemma_1_backward`).
* Normal form for 3 rounds: a 3-round schedule exists iff some set `S` of `FF` nodes makes every state
  `FB ∪ S ∪ X`, `X ⊆ BB`, loop-free (`hasSLF_three_iff`). This is the "edge selection problem"
  to which §3.2 reduces 3-SAT.
-/

set_option linter.unusedSectionVars false

namespace Podc.LoopFreeUpdates

open Relation

variable {V : Type*} [DecidableEq V]

namespace Instance

variable (I : Instance V)

/-! ### First and last rounds -/

theorem fwd_eq_out₁_of_not_mem {A : Finset V} {v : V} (h : v ∉ A) : I.fwd A v = I.out₁ v :=
  I.fwd_of_not_mem h

/-- In a strongly loop-free schedule, nodes updated in the first round have forward new rules. -/
theorem dashedFwd_of_mem_first {rounds : List (Finset V)} (h : I.IsSLF rounds)
    (h0 : 0 < rounds.length) {v : V} (hv : v ∈ rounds[0]) (hu : v ∈ I.toUpdate) :
    I.DashedFwd v := by
  by_contra hF
  obtain ⟨w, hw, hlt⟩ := I.dashed_bwd hu hF
  have hloop := h.2 0 h0 {v} (Finset.singleton_subset_iff.2 hv)
  rw [done_zero, Finset.empty_union] at hloop
  refine hloop v (I.loop_of_dashed_bwd (Finset.mem_singleton_self v) hw hlt ?_)
  intro x _ _ hx2
  have : x ≠ v := by rintro rfl; omega
  exact I.fwd_of_not_mem (by simpa using this)

/-- Every node to be updated lies in some round of index `< rounds.length`. -/
theorem exists_round {rounds : List (Finset V)} (h : I.IsSchedule rounds) {v : V}
    (hv : v ∈ I.toUpdate) : ∃ (i : ℕ) (hi : i < rounds.length), v ∈ rounds[i] := by
  obtain ⟨r, hr, hvr⟩ := h.2 v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  exact ⟨i, hi, hvr⟩

/-- Two different rounds of a schedule are disjoint. -/
theorem disjoint_rounds {rounds : List (Finset V)} (h : I.IsSchedule rounds) {i j : ℕ}
    (hi : i < rounds.length) (hj : j < rounds.length) (hij : i ≠ j) :
    Disjoint rounds[i] rounds[j] := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact List.pairwise_iff_getElem.1 h.1 i j hi hj hlt
  · exact (List.pairwise_iff_getElem.1 h.1 j i hj hi hlt).symm

/-- In a strongly loop-free schedule, nodes updated in the last round have old rules pointing
forward on the new route. -/
theorem solidFwd_of_mem_last {rounds : List (Finset V)} (h : I.IsSLF rounds) {t : ℕ}
    (ht : t + 1 = rounds.length) {v : V} (hv : v ∈ rounds[t]) (hu : v ∈ I.toUpdate) :
    I.SolidFwd v := by
  by_contra hF
  obtain ⟨w, hw, hlt⟩ := I.solid_bwd hu hF
  have hloop := h.2 t (by omega) (rounds[t].erase v) (Finset.erase_subset _ _)
  refine hloop v (I.loop_of_solid_bwd ?_ hw hlt ?_)
  · simp only [Finset.mem_union, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, or_false]
    rw [mem_done]
    rintro ⟨i, hi, hit, hvi⟩
    exact Finset.disjoint_left.1 (I.disjoint_rounds h.1 hi (by omega) (by omega)) hvi hv
  intro x _ _ hx2
  have hxv : x ≠ v := by rintro rfl; omega
  by_cases hx : x ∈ I.toUpdate
  · obtain ⟨i, hi, hxi⟩ := I.exists_round h.1 hx
    apply I.fwd_of_mem
    rcases Nat.lt_or_ge i t with hit | hit
    · exact Finset.mem_union_left _ (mem_done.2 ⟨i, hi, hit, hxi⟩)
    · have : i = t := by omega
      subst this
      exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hxv, hxi⟩)
  · rw [I.fwd_of_not_toUpdate _ hx]; exact I.out₁_eq_out₂_of_not_mem hx

/-! ### Two rounds (§3.1) -/

/-- The nodes of a type, as a finite set. -/
def ofType (P : V → Prop) [DecidablePred P] : Finset V := I.toUpdate.filter P

theorem mem_ofType {P : V → Prop} [DecidablePred P] {v : V} :
    v ∈ I.ofType P ↔ v ∈ I.toUpdate ∧ P v := Finset.mem_filter

theorem isSchedule_two {R₁ R₂ : Finset V} (hd : Disjoint R₁ R₂)
    (hc : ∀ v ∈ I.toUpdate, v ∈ R₁ ∨ v ∈ R₂) : I.IsSchedule [R₁, R₂] := by
  refine ⟨by simp [hd], fun v hv => ?_⟩
  rcases hc v hv with h | h
  · exact ⟨R₁, by simp, h⟩
  · exact ⟨R₂, by simp, h⟩

/-- §3.1 ("2-Round is Easy"): a strongly loop-free 2-round schedule exists iff there is no `BB`
node; then the `F·` nodes go first and the `B·` nodes second. -/
theorem hasSLF_two_iff : I.HasSLF 2 ↔ ∀ v, ¬ I.IsBB v := by
  constructor
  · rintro ⟨rounds, hlen, h⟩ v ⟨hu, hF, hS⟩
    obtain ⟨i, hi, hvi⟩ := I.exists_round h.1 hu
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · exact hF (I.dashedFwd_of_mem_first h hi hvi hu)
    · exact hS (I.solidFwd_of_mem_last h (by omega) hvi hu)
  · intro hBB
    refine ⟨[I.ofType I.DashedFwd, I.ofType (fun v => ¬ I.DashedFwd v)], rfl, ?_, ?_⟩
    · refine I.isSchedule_two ?_ (fun v hv => ?_)
      · rw [Finset.disjoint_left]
        intro v h1 h2
        exact ((I.mem_ofType).1 h2).2 ((I.mem_ofType).1 h1).2
      · by_cases h : I.DashedFwd v
        · exact Or.inl ((I.mem_ofType).2 ⟨hv, h⟩)
        · exact Or.inr ((I.mem_ofType).2 ⟨hv, h⟩)
    · intro t ht X hX
      have : t = 0 ∨ t = 1 := by simp at ht; omega
      rcases this with rfl | rfl
      · rw [done_zero, Finset.empty_union]
        exact I.loopFree_of_dashedFwd fun v hv _ => ((I.mem_ofType).1 (hX hv)).2
      · refine I.loopFree_of_solidFwd fun v hv hvA => ?_
        have hnF : ¬ I.DashedFwd v := by
          intro hF
          apply hvA
          refine Finset.mem_union_left _ (mem_done.2 ⟨0, by simp, by omega, ?_⟩)
          exact (I.mem_ofType).2 ⟨hv, hF⟩
        by_contra hS
        exact hBB v ⟨hv, hnF, hS⟩

/-! ### Lemma 1 -/

/-- Lemma 1 of [LMS15], as proved in the paper: nodes with a forward new rule (types `FB`, `FF`)
that a schedule updates in round 2 can be moved to round 1. (Stated for any schedule with at least two
rounds.) -/
theorem lemma_1 {r₀ r₁ : Finset V} {rest : List (Finset V)} (h : I.IsSLF (r₀ :: r₁ :: rest))
    {V' : Finset V} (hV' : V' ⊆ r₁) (hF : ∀ v ∈ V', v ∈ I.toUpdate → I.DashedFwd v) :
    I.IsSLF ((r₀ ∪ V') :: (r₁ \ V') :: rest) := by
  have h0 : ∀ v ∈ r₀, v ∈ I.toUpdate → I.DashedFwd v := fun v hv hu =>
    I.dashedFwd_of_mem_first h (by simp) hv hu
  obtain ⟨⟨hpw, hcov⟩, hlf⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at hpw ⊢
    obtain ⟨⟨h01, h0r⟩, h1r, hr⟩ := hpw
    refine ⟨⟨?_, fun a ha => ?_⟩, fun a ha => ?_, hr⟩
    · rw [Finset.disjoint_union_left]
      exact ⟨h01.mono_right Finset.sdiff_subset, Finset.disjoint_sdiff⟩
    · rw [Finset.disjoint_union_left]
      exact ⟨h0r a ha, (h1r a ha).mono_left hV'⟩
    · exact (h1r a ha).mono_left Finset.sdiff_subset
  · intro v hv
    obtain ⟨r, hr, hvr⟩ := hcov v hv
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · exact ⟨r ∪ V', by simp, Finset.mem_union_left _ hvr⟩
    · by_cases hvV : v ∈ V'
      · exact ⟨r₀ ∪ V', by simp, Finset.mem_union_right _ hvV⟩
      · exact ⟨r \ V', by simp, Finset.mem_sdiff.2 ⟨hvr, hvV⟩⟩
    · exact ⟨r, by simp [hr], hvr⟩
  · intro t ht X hX
    match t, ht, hX with
    | 0, _, hX =>
      rw [done_zero, Finset.empty_union]
      refine I.loopFree_of_dashedFwd fun v hv hu => ?_
      rcases Finset.mem_union.1 (hX hv) with h' | h'
      · exact h0 v h' hu
      · exact hF v h' hu
    | 1, _, hX =>
      have := hlf 1 (by simp) (V' ∪ X) (Finset.union_subset hV' (hX.trans Finset.sdiff_subset))
      rw [done_cons_succ, done_zero, Finset.union_empty] at this ⊢
      rwa [Finset.union_assoc]
    | t + 2, ht, hX =>
      have := hlf (t + 2) ht X hX
      rw [done_cons_succ, done_cons_succ] at this ⊢
      convert this using 2
      ext v
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ((h1 | h1) | h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl (hV' h1))
        · exact Or.inr (Or.inl h1.1)
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | h1 | h1)
        · exact Or.inl (Or.inl h1)
        · by_cases hv : v ∈ V'
          · exact Or.inl (Or.inr hv)
          · exact Or.inr (Or.inl ⟨h1, hv⟩)
        · exact Or.inr (Or.inr h1)

/-- Lemma 1 of [LMS15], "backward perspective": nodes with a forward old rule (types `BF`, `FF`)
that a 3-round schedule updates in round 2 can be moved to round 3. -/
theorem lemma_1_backward {r₀ r₁ r₂ : Finset V} (h : I.IsSLF [r₀, r₁, r₂])
    {V' : Finset V} (hV' : V' ⊆ r₁) (hS : ∀ v ∈ V', v ∈ I.toUpdate → I.SolidFwd v) :
    I.IsSLF [r₀, r₁ \ V', r₂ ∪ V'] := by
  have h2 : ∀ v ∈ r₂, v ∈ I.toUpdate → I.SolidFwd v := fun v hv hu =>
    I.solidFwd_of_mem_last h (t := 2) (by simp) hv hu
  obtain ⟨⟨hpw, hcov⟩, hlf⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
      forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
      and_true, false_imp_iff, or_false] at hpw ⊢
    obtain ⟨⟨h01, h02⟩, h12⟩ := hpw
    refine ⟨⟨h01.mono_right Finset.sdiff_subset, ?_⟩, ?_⟩
    · rw [Finset.disjoint_union_right]; exact ⟨h02, h01.mono_right hV'⟩
    · rw [Finset.disjoint_union_right]; exact ⟨h12.mono_left Finset.sdiff_subset, Finset.sdiff_disjoint⟩
  · intro v hv
    obtain ⟨r, hr, hvr⟩ := hcov v hv
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨r, by simp, hvr⟩
    · by_cases hvV : v ∈ V'
      · exact ⟨r₂ ∪ V', by simp, Finset.mem_union_right _ hvV⟩
      · exact ⟨r \ V', by simp, Finset.mem_sdiff.2 ⟨hvr, hvV⟩⟩
    · exact ⟨r ∪ V', by simp, Finset.mem_union_left _ hvr⟩
  · intro t ht X hX
    have ht' : t < 3 := by simpa using ht
    obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    · simpa [done_zero] using hlf 0 (by simp) X (by simpa using hX)
    · exact hlf 1 (by simp) X ((show X ⊆ r₁ \ V' by simpa using hX).trans Finset.sdiff_subset)
    · have hX' : X ⊆ r₂ ∪ V' := by simpa using hX
      refine I.loopFree_of_solidFwd fun v hv hvA => ?_
      obtain ⟨r, hr, hvr⟩ := hcov v hv
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      simp only [done_cons_succ, done_zero, Finset.union_empty, Finset.mem_union,
        Finset.mem_sdiff, not_or, not_and, not_not] at hvA
      rcases hr with rfl | rfl | rfl
      · exact absurd hvr hvA.1.1
      · exact hS v (hvA.1.2 hvr) hv
      · exact h2 v hvr hv

/-! ### Normal form of 3-round schedules (§3.2.1) -/

theorem step_congr {A B : Finset V} (h : A ∩ I.toUpdate = B ∩ I.toUpdate) :
    I.Step A = I.Step B := by
  unfold Step; rw [← I.fwd_inter A, h, I.fwd_inter]

theorem loopFree_congr {A B : Finset V} (h : A ∩ I.toUpdate = B ∩ I.toUpdate) :
    I.LoopFree A ↔ I.LoopFree B := by
  unfold LoopFree; rw [I.step_congr h]

/-- The normal form of 3-round schedules (§3.2.1, consequence of Lemma 1 and its backward version):
a strongly loop-free 3-round schedule exists iff there is a set `S` of `FF` nodes such that, with
`FB ∪ S` updated in round 1, all `BB` nodes can be updated in round 2 in any order, i.e. every state
`FB ∪ S ∪ X` with `X ⊆ BB` is loop-free. (Round 3 then updates `BF` and the remaining `FF` nodes.) -/
theorem hasSLF_three_iff :
    I.HasSLF 3 ↔ ∃ S : Finset V, (∀ v ∈ S, I.IsFF v) ∧
      ∀ X : Finset V, (∀ v ∈ X, I.IsBB v) → I.LoopFree (I.ofType I.IsFB ∪ S ∪ X) := by
  constructor
  · rintro ⟨rounds, hlen, h⟩
    match rounds, hlen, h with
    | [U₀, U₁, U₂], _, h =>
    have hF : ∀ v ∈ U₀, v ∈ I.toUpdate → I.DashedFwd v := fun v hv hu =>
      I.dashedFwd_of_mem_first h (by simp) hv hu
    have hS : ∀ v ∈ U₂, v ∈ I.toUpdate → I.SolidFwd v := fun v hv hu =>
      I.solidFwd_of_mem_last h (t := 2) (by simp) hv hu
    have hcov := h.1.2
    have hpw := h.1.1
    simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
      forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
      and_true, false_imp_iff, or_false] at hpw
    obtain ⟨⟨h01, h02⟩, h12⟩ := hpw
    have hin : ∀ v ∈ I.toUpdate, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ U₂ := by
      intro v hv
      obtain ⟨r, hr, hvr⟩ := hcov v hv
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [hvr]
    refine ⟨U₀.filter I.IsFF, fun v hv => (Finset.mem_filter.1 hv).2, fun X hX => ?_⟩
    let X' := U₁.filter (fun v => I.IsFB v ∨ v ∈ X)
    have := h.2 1 (by simp) X' (Finset.filter_subset _ _)
    rw [show done [U₀, U₁, U₂] 1 = U₀ by simp [done_cons_succ, done_zero]] at this
    refine (I.loopFree_congr ?_).1 this
    ext v
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_filter, X', mem_ofType]
    constructor
    · rintro ⟨h1 | h1, hu⟩
      · refine ⟨?_, hu⟩
        rcases I.type_cases hu with h' | h' | h' | h'
        · exact Or.inl (Or.inr ⟨h1, h'⟩)
        · exact Or.inl (Or.inl ⟨hu, h'⟩)
        · exact absurd (hF v h1 hu) h'.2.1
        · exact absurd (hF v h1 hu) h'.2.1
      · rcases h1.2 with h2 | h2
        · exact ⟨Or.inl (Or.inl ⟨hu, h2⟩), hu⟩
        · exact ⟨Or.inr h2, hu⟩
    · rintro ⟨(h1 | h1) | h1, hu⟩
      · refine ⟨?_, hu⟩
        rcases hin v hu with h2 | h2 | h2
        · exact Or.inl h2
        · exact Or.inr ⟨h2, Or.inl h1.2⟩
        · exact absurd (hS v h2 hu) h1.2.2.2
      · exact ⟨Or.inl h1.1, hu⟩
      · refine ⟨?_, hu⟩
        have hB := hX v h1
        rcases hin v hu with h2 | h2 | h2
        · exact absurd (hF v h2 hu) hB.2.1
        · exact Or.inr ⟨h2, Or.inr h1⟩
        · exact absurd (hS v h2 hu) hB.2.2
  · rintro ⟨S, hSFF, hS⟩
    let R₁ := I.ofType I.IsFB ∪ S
    let R₂ := I.ofType I.IsBB
    let R₃ := I.toUpdate.filter (fun v => (I.IsBF v ∨ I.IsFF v) ∧ v ∉ S)
    refine ⟨[R₁, R₂, R₃], rfl, ⟨?_, ?_⟩, ?_⟩
    · simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
        forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
        and_true, false_imp_iff, or_false]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rw [Finset.disjoint_left] <;> intro v h1 h2 <;>
        simp only [R₁, R₂, R₃, Finset.mem_union, Finset.mem_filter, mem_ofType] at h1 h2
      · rcases h1 with h1 | h1
        · exact h2.2.2.1 h1.2.2.1
        · exact h2.2.2.1 (hSFF v h1).2.1
      · rcases h1 with h1 | h1
        · rcases h2.2.1 with h3 | h3
          · exact h1.2.2.2 h3.2.2
          · exact h1.2.2.2 h3.2.2
        · exact h2.2.2 h1
      · rcases h2.2.1 with h3 | h3
        · exact h1.2.2.2 h3.2.2
        · exact h1.2.2.2 h3.2.2
    · intro v hv
      rcases I.type_cases hv with h' | h' | h' | h'
      · by_cases hvS : v ∈ S
        · exact ⟨R₁, by simp, Finset.mem_union_right _ hvS⟩
        · exact ⟨R₃, by simp, Finset.mem_filter.2 ⟨hv, Or.inr h', hvS⟩⟩
      · exact ⟨R₁, by simp, Finset.mem_union_left _ ((I.mem_ofType).2 ⟨hv, h'⟩)⟩
      · refine ⟨R₃, by simp, Finset.mem_filter.2 ⟨hv, Or.inl h', fun hvS => ?_⟩⟩
        exact h'.2.1 (hSFF v hvS).2.1
      · exact ⟨R₂, by simp, (I.mem_ofType).2 ⟨hv, h'⟩⟩
    · intro t ht X hX
      have ht' : t < 3 := by simpa using ht
      obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
      · rw [done_zero, Finset.empty_union]
        refine I.loopFree_of_dashedFwd fun v hv _ => ?_
        have : v ∈ R₁ := by simpa using hX hv
        simp only [R₁, Finset.mem_union, mem_ofType] at this
        rcases this with h1 | h1
        · exact h1.2.2.1
        · exact (hSFF v h1).2.1
      · rw [show done [R₁, R₂, R₃] 1 = R₁ by simp [done_cons_succ, done_zero]]
        refine hS X fun v hv => ?_
        have : v ∈ R₂ := by simpa using hX hv
        exact ((I.mem_ofType).1 this).2
      · refine I.loopFree_of_solidFwd fun v hv hvA => ?_
        simp only [done_cons_succ, done_zero, Finset.union_empty, Finset.mem_union, not_or,
          R₁, R₂, mem_ofType] at hvA
        rcases I.type_cases hv with h' | h' | h' | h'
        · exact h'.2.2
        · exact absurd ⟨hv, h'⟩ hvA.1.1.1
        · exact h'.2.2
        · exact absurd ⟨hv, h'⟩ hvA.1.2

end Instance

end Podc.LoopFreeUpdates
