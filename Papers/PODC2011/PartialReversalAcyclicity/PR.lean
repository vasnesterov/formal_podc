import Papers.PODC2011.PartialReversalAcyclicity.Model

/-!
# Section 3: properties of `PR`

Invariant 3.1 (edge-direction consistency), Invariant 3.2 (the possible contents of `list[u]`),
Corollaries 3.3 and 3.4. Since `OneStepPR` is `PR` restricted to singleton sets, every
reachable state of `OneStepPR` is a reachable state of `PR` (`OneStepPR.Reachable.toPR`), and the
invariants transfer.

Invariant 3.2 claims that *exactly one* of its two parts holds. This is false for an isolated
node (both parts hold, see `Counterexamples.lean`); we prove "at least one" in general
(`PR.inv_3_2`) and "exactly one" for nodes with at least one neighbour (`PR.inv_3_2_exactlyOne`).
-/

noncomputable section
open Classical

namespace Podc.PartialReversalAcyclicity

variable {V : Type*} {N : Network V}

/-- The common shape of the two parts of Invariant 3.2: for each `w ∈ B`, `dir[u,w] = in`, and
`list[u] = {v ∈ A | dir[u,v] = in}`. Part 1 is `A = in-nbrsᵤ, B = out-nbrsᵤ`, part 2 the
other way round. -/
def ListShape (s : PRState V) (u : V) (A B : Set V) : Prop :=
  (∀ w ∈ B, s.dir u w = .inc) ∧ s.list u = {v | v ∈ A ∧ s.dir u v = .inc}

variable (N) in
/-- Part 1 of Invariant 3.2. -/
def Part1 (s : PRState V) (u : V) : Prop :=
  (∀ w ∈ N.outNbrs u, s.dir u w = .inc) ∧ s.list u = {v | v ∈ N.inNbrs u ∧ s.dir u v = .inc}

variable (N) in
/-- Part 2 of Invariant 3.2. -/
def Part2 (s : PRState V) (u : V) : Prop :=
  (∀ w ∈ N.inNbrs u, s.dir u w = .inc) ∧ s.list u = {v | v ∈ N.outNbrs u ∧ s.dir u v = .inc}

namespace PR

theorem effect_dir_of_notMem {S : Set V} {s : PRState V} {u : V} (hu : u ∉ S) (v : V) :
    (effect N S s).dir u v = if v ∈ S ∧ u ∈ revSet N s v then .inc else s.dir u v := by
  simp [effect, hu]

theorem effect_list_of_notMem {S : Set V} {s : PRState V} {u : V} (hu : u ∉ S) :
    (effect N S s).list u = s.list u ∪ {y | y ∈ S ∧ u ∈ revSet N s y} := by
  simp [effect, hu]

theorem effect_list_of_mem {S : Set V} {s : PRState V} {u : V} (hu : u ∈ S) :
    (effect N S s).list u = ∅ := by
  simp [effect, hu]

theorem effect_dir_of_mem {S : Set V} {s : PRState V} {u v : V} (hu : u ∈ S) (hv : v ∉ S) :
    (effect N S s).dir u v = if v ∈ revSet N s u then .out else s.dir u v := by
  simp [effect, hu, hv]

/-- Invariant 3.1 is preserved by every step from a consistent state. -/
theorem consistent_effect {S : Set V} {s : PRState V} (hc : DirConsistent N s.dir)
    (hS : ∀ u ∈ S, IsSink N s.dir u) : DirConsistent N (effect N S s).dir := by
  intro x y hxy
  have hyx : N.Adj y x := Network.adj_comm.mp hxy
  have hind : ¬ (x ∈ S ∧ y ∈ S) := fun ⟨hx, hy⟩ =>
    hc.not_both_sinks hxy (hS x hx) (hS y hy)
  have hcx := hc x y hxy
  simp only [effect]
  by_cases h1 : x ∈ S ∧ y ∈ revSet N s x
  · have hy : y ∉ S := fun hy => hind ⟨h1.1, hy⟩
    simp [h1, hy]
  · by_cases h2 : y ∈ S ∧ x ∈ revSet N s y
    · have hx : x ∉ S := fun hx => hind ⟨hx, h2.1⟩
      simp [h2, hx]
    · simp only [h1, h2, ite_false]
      exact hcx

theorem consistent_of_reachable {s : PRState V} (hs : Reachable N s) : DirConsistent N s.dir := by
  induction hs with
  | refl => exact initDir_consistent
  | tail _ hstep ih =>
    obtain ⟨S, -, -, hS, rfl⟩ := hstep
    exact consistent_effect ih hS

/-- One step preserves the shape of `list[u]` (the induction step of Invariant 3.2). -/
theorem listShape_effect {S : Set V} {s : PRState V} (hc : DirConsistent N s.dir)
    (hS : ∀ u ∈ S, IsSink N s.dir u) {u : V} {A B : Set V} (hAB : A ∪ B = N.nbrs u)
    (hd : Disjoint A B) (h : ListShape s u A B) :
    ListShape (effect N S s) u A B ∨ ListShape (effect N S s) u B A := by
  obtain ⟨hB, hl⟩ := h
  have hA_sub : A ⊆ N.nbrs u := hAB ▸ Set.subset_union_left
  have hB_sub : B ⊆ N.nbrs u := hAB ▸ Set.subset_union_right
  by_cases hu : u ∈ S
  · -- Case 1: `u` takes a step.
    have hsink := hS u hu
    have hnS : ∀ v ∈ N.nbrs u, v ∉ S := fun v hv hvS =>
      hc.not_both_sinks hv hsink (hS v hvS)
    have hdir : ∀ v ∈ N.nbrs u,
        (effect N S s).dir u v = if v ∈ revSet N s u then .out else .inc := by
      intro v hv
      rw [effect_dir_of_mem hu (hnS v hv), hsink v hv]
    have hlA : s.list u = A := by
      rw [hl]; ext v
      simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
      exact fun hv => hsink v (hA_sub hv)
    have hl' := effect_list_of_mem (N := N) (s := s) hu
    by_cases hfull : s.list u = N.nbrs u
    · -- `list[u] = nbrsᵤ`: all edges are reversed, the shape is kept.
      have hrev : revSet N s u = N.nbrs u := by simp [revSet, hfull]
      left
      refine ⟨fun w hw => ?_, ?_⟩
      · exfalso
        have : w ∈ A := hlA ▸ hfull ▸ hB_sub hw
        exact Set.disjoint_left.mp hd this hw
      · rw [hl']; ext v
        simp only [Set.mem_empty_iff_false, Set.mem_ofPred_eq, false_iff, not_and]
        intro hv
        rw [hdir v (hA_sub hv), hrev, ite_eq_left (hA_sub hv)]; simp
    · -- otherwise `u` reverses `nbrsᵤ \ A = B` and the shape switches.
      have hrev : revSet N s u = B := by
        rw [revSet, ite_eq_left hfull, hlA, ← hAB]; ext v
        simp only [Set.mem_sdiff, Set.mem_union]
        constructor
        · rintro ⟨h | h, h'⟩
          · exact absurd h h'
          · exact h
        · intro h; exact ⟨Or.inr h, Set.disjoint_right.mp hd h⟩
      right
      refine ⟨fun w hw => ?_, ?_⟩
      · rw [hdir w (hA_sub hw), hrev, ite_eq_right (Set.disjoint_left.mp hd hw)]
      · rw [hl']; ext v
        simp only [Set.mem_empty_iff_false, Set.mem_ofPred_eq, false_iff, not_and]
        intro hv
        rw [hdir v (hB_sub hv), hrev, ite_eq_left hv]; simp
  · -- Cases 2 and 3: `u` does not take a step; neighbours that reverse their edge to `u`
    -- join `list[u]`.
    left
    have hT : ∀ y, y ∈ S ∧ u ∈ revSet N s y → y ∈ A ∧ s.dir u y = .out := by
      rintro y ⟨hyS, hyu⟩
      have hadj : N.Adj y u := revSet_subset s y hyu
      have hadj' : N.Adj u y := Network.adj_comm.mp hadj
      have hout : s.dir u y = .out := (hc.out_iff hadj').mpr (hS y hyS u hadj)
      refine ⟨?_, hout⟩
      have hy : y ∈ A ∪ B := hAB ▸ hadj'
      rcases hy with hy | hy
      · exact hy
      · exact absurd (hB y hy) (by rw [hout]; simp)
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [effect_dir_of_notMem hu]
      split_ifs
      · rfl
      · exact hB w hw
    · rw [effect_list_of_notMem hu, hl]; ext v
      simp only [Set.mem_union, Set.mem_ofPred_eq, effect_dir_of_notMem hu]
      by_cases hv : v ∈ S ∧ u ∈ revSet N s v
      · simp only [hv, and_self, or_true, ite_true, true_iff, and_true]
        exact (hT v hv).1
      · simp only [hv, or_false, ite_false]

theorem inv_3_2_or {s : PRState V} (hs : Reachable N s) (u : V) :
    Part1 N s u ∨ Part2 N s u := by
  have hAB : N.inNbrs u ∪ N.outNbrs u = N.nbrs u := (Network.nbrs_eq_union u).symm
  have hAB' : N.outNbrs u ∪ N.inNbrs u = N.nbrs u := by rw [Set.union_comm, hAB]
  have hd : Disjoint (N.inNbrs u) (N.outNbrs u) :=
    Set.disjoint_left.mpr fun _ h => Network.not_mem_outNbrs_of_mem_inNbrs h
  induction hs with
  | refl =>
    right
    refine ⟨fun w hw => Network.initDir_eq_inc.mpr hw, ?_⟩
    ext v
    simp only [init, Set.mem_empty_iff_false, Network.mem_outNbrs, Network.initDir_eq_inc,
      Set.mem_ofPred_eq, false_iff, not_and]
    exact fun h => Network.init_asymm h
  | tail hr hstep ih =>
    obtain ⟨S, -, -, hS, rfl⟩ := hstep
    have hc := consistent_of_reachable hr
    rcases ih with h | h
    · rcases listShape_effect hc hS hAB hd h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · rcases listShape_effect hc hS hAB' hd.symm h with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'

/-- Invariant 3.1 of [Radeva–Lynch]: in every reachable state of `PR`, for each edge `{u,v}`,
`dir[u,v] = in` iff `dir[v,u] = out`. -/
theorem inv_3_1 {s : PRState V} (hs : Reachable N s) {u v : V} (huv : N.Adj u v) :
    s.dir u v = .inc ↔ s.dir v u = .out :=
  consistent_of_reachable hs u v huv

/-- The two parts of Invariant 3.2 can hold together only for an isolated node. -/
theorem part1_and_part2_iff {s : PRState V} {u : V} :
    Part1 N s u ∧ Part2 N s u ↔ N.nbrs u = ∅ ∧ s.list u = ∅ := by
  constructor
  · rintro ⟨⟨h1B, h1l⟩, ⟨h2B, h2l⟩⟩
    have hin : N.inNbrs u = ∅ := by
      ext v; simp only [Set.mem_empty_iff_false, iff_false]
      intro hv
      have : v ∈ s.list u := h1l ▸ ⟨hv, h2B v hv⟩
      rw [h2l] at this
      exact Network.not_mem_outNbrs_of_mem_inNbrs hv this.1
    have hout : N.outNbrs u = ∅ := by
      ext v; simp only [Set.mem_empty_iff_false, iff_false]
      intro hv
      have : v ∈ s.list u := h2l ▸ ⟨hv, h1B v hv⟩
      rw [h1l] at this
      exact Network.not_mem_outNbrs_of_mem_inNbrs this.1 hv
    refine ⟨by rw [Network.nbrs_eq_union, hin, hout, Set.union_empty], ?_⟩
    rw [h1l, hin]; ext v; simp
  · rintro ⟨hn, hl⟩
    have hin : N.inNbrs u = ∅ := Set.subset_empty_iff.mp (hn ▸ Network.inNbrs_subset_nbrs u)
    have hout : N.outNbrs u = ∅ :=
      Set.subset_empty_iff.mp (hn ▸ Network.outNbrs_subset_nbrs u)
    refine ⟨⟨by simp [hout], ?_⟩, ⟨by simp [hin], ?_⟩⟩
    · rw [hl, hin]; ext v; simp
    · rw [hl, hout]; ext v; simp

/-- Invariant 3.2 of [Radeva–Lynch], the part that holds for every node: in every reachable
state of `PR`, for each node `u`, part 1 or part 2 holds; and they do not both hold unless `u`
is isolated. (The paper claims "exactly one" for every node; for an isolated node both hold,
see `inv_3_2_exactlyOne_false`.) -/
theorem inv_3_2 {s : PRState V} (hs : Reachable N s) (u : V) :
    (Part1 N s u ∨ Part2 N s u) ∧ (N.nbrs u ≠ ∅ → ¬ (Part1 N s u ∧ Part2 N s u)) :=
  ⟨inv_3_2_or hs u, fun hn h => hn (part1_and_part2_iff.mp h).1⟩

/-- Invariant 3.2 of [Radeva–Lynch] as stated ("exactly one of the parts"), for every node with
at least one neighbour. -/
theorem inv_3_2_exactlyOne {s : PRState V} (hs : Reachable N s) {u : V}
    (hu : (N.nbrs u).Nonempty) : Xor (Part1 N s u) (Part2 N s u) := by
  have h := inv_3_2 hs u
  have hn : N.nbrs u ≠ ∅ := hu.ne_empty
  rcases h.1 with h1 | h2
  · exact Or.inl ⟨h1, fun h2 => h.2 hn ⟨h1, h2⟩⟩
  · exact Or.inr ⟨h2, fun h1 => h.2 hn ⟨h1, h2⟩⟩

/-- Corollary 3.3 of [Radeva–Lynch]: `list[u] ⊆ in-nbrsᵤ` or `list[u] ⊆ out-nbrsᵤ`. -/
theorem cor_3_3 {s : PRState V} (hs : Reachable N s) (u : V) :
    s.list u ⊆ N.inNbrs u ∨ s.list u ⊆ N.outNbrs u := by
  rcases inv_3_2_or hs u with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl (h ▸ fun _ hv => hv.1)
  · exact Or.inr (h ▸ fun _ hv => hv.1)

/-- Corollary 3.4 of [Radeva–Lynch]: if `u` is a sink, `list[u] = in-nbrsᵤ` or
`list[u] = out-nbrsᵤ`. -/
theorem cor_3_4 {s : PRState V} (hs : Reachable N s) {u : V} (hu : IsSink N s.dir u) :
    s.list u = N.inNbrs u ∨ s.list u = N.outNbrs u := by
  rcases inv_3_2_or hs u with ⟨-, h⟩ | ⟨-, h⟩
  · left; rw [h]; ext v
    simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
    exact fun hv => hu v (Network.inNbrs_subset_nbrs u hv)
  · right; rw [h]; ext v
    simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
    exact fun hv => hu v (Network.outNbrs_subset_nbrs u hv)

end PR

/-- Every reachable state of `OneStepPR` is a reachable state of `PR`. -/
theorem OneStepPR.Reachable.toPR {s : PRState V} (hs : OneStepPR.Reachable N s) :
    PR.Reachable N s := by
  induction hs with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨u, hu, hsink, rfl⟩ := hstep
    exact ih.tail ⟨{u}, Set.singleton_nonempty u, by simpa [eq_comm] using hu,
      by simpa using hsink, rfl⟩

end Podc.PartialReversalAcyclicity

end
