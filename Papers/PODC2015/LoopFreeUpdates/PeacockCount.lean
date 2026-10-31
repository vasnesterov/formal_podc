import Papers.PODC2015.LoopFreeUpdates.PeacockReduce

/-!
# Peacock (§4): the walk after an odd round, and Lemma 2

* `reach_iff_not_inside`: in state `C` (after the odd round) the walk from `s` visits exactly the
  nodes that are not inside the interval of a selected node. Hence the pruned nodes are exactly the
  non-updated nodes off the `s`–`d` path (as in the paper), and the kept nodes are exactly the
  non-updated nodes on it.
* `lemma2` (**Lemma 2**): if the current line has `N ≥ 2` nodes, then after the odd round, with node
  merging (every updated node is merged into the target of its new rule), the `s`–`d` path has
  `N'` nodes with `3 N' + 1 ≤ 2 N`, i.e. it shrinks by at least `(N + 1) / 3 > N / 3` nodes.

*Remark (merging is essential).* Without merging, i.e. counting the updated nodes on the walk as well,
the claim fails: for `old = [0,1,2,3]`, `new = [0,2,1,3]` the only forward candidate of maximal
distance is `0` (`0 → 2`, distance 2; then `2 → 1` is backward and `1 → 3` is blocked) and the walk
`0 → 2 → 3` still has `3` nodes, while `3 · 3 + 1 > 2 · 4`. With merging, `0` is merged into `2` and
the line has `2` nodes.
-/

set_option linter.unusedSectionVars false

namespace Podc.LoopFreeUpdates

open Relation

variable {V : Type*} [DecidableEq V]

namespace Instance

variable (I : Instance V)

/-- The number of nodes at old positions in `[a, b)`. -/
theorem card_filter_pos_Ico {a b : ℕ} (hb : b ≤ I.old.length) :
    (I.nodes.filter (fun v => a ≤ I.pos₁ v ∧ I.pos₁ v < b)).card = b - a := by
  rw [← Finset.card_image_of_injOn (f := I.pos₁)]
  · have : (I.nodes.filter (fun v => a ≤ I.pos₁ v ∧ I.pos₁ v < b)).image I.pos₁ =
        Finset.Ico a b := by
      ext i
      simp only [Finset.mem_image, Finset.mem_filter, I.mem_nodes, Finset.mem_Ico]
      constructor
      · rintro ⟨v, ⟨_, h⟩, rfl⟩; exact h
      · rintro h
        exact ⟨I.old[i]'(by omega), ⟨List.getElem_mem _, by rw [I.pos₁_getElem]; exact h⟩,
          I.pos₁_getElem _ _⟩
    rw [this, Nat.card_Ico]
  · intro v hv w hw h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, I.mem_nodes] at hv hw
    exact I.pos₁_inj hv.1 hw.1 h

/-- Discrete intermediate value theorem: the new route, which goes from old position `0` to old
position `N - 1`, has an edge jumping over every gap `(i, i + 1)` of the old route. -/
theorem exists_cross {i : ℕ} (hi : i + 1 < I.old.length) :
    ∃ u, I.pos₁ u ≤ i ∧ i < I.dpos u := by
  have key : ∀ m j (hj : j < I.new.length), I.new.length - j = m → I.pos₁ I.new[j] ≤ i →
      ∃ u, I.pos₁ u ≤ i ∧ i < I.dpos u := by
    intro m
    induction m with
    | zero => intro j hj h; omega
    | succ m ih =>
      intro j hj hm hle
      by_cases hlast : j + 1 < I.new.length
      · have hout := I.out₂_getElem j hlast
        by_cases hlt : i < I.pos₁ I.new[j + 1]
        · exact ⟨_, hle, by rw [I.dpos_of_out₂ hout]; exact hlt⟩
        · exact ih (j + 1) hlast (by omega) (by omega)
      · have : I.new[j] = I.d := by
          rw [I.d_eq_new_getLast, List.getLast_eq_getElem]; congr 1; omega
        rw [this, I.pos₁_d] at hle; omega
  have hlen := I.length_new
  have h0 : I.new[0]'(by omega) = I.s := by rw [I.s_eq_new_head, List.head_eq_getElem]
  exact key _ 0 (by omega) rfl (by rw [h0, I.pos₁_s]; omega)

variable {I} {C : Finset V}

namespace GoodSelection

variable (hC : I.GoodSelection C)
include hC

/-! ### The walk after the odd round -/

theorem not_inside_of_reach {v : V} (h : ReflTransGen (I.Step C) I.s v) : ¬ I.Inside C v := by
  induction h with
  | refl => exact hC.s_not_inside
  | tail _ hst ih =>
    rename_i u w _
    unfold Step Instance.fwd at hst
    split_ifs at hst with hu
    · exact hC.not_inside_dpos hu hst
    · exact hC.not_inside_out₁ ih hu hst

theorem reach_of_not_inside :
    ∀ (n : ℕ) (v : V), I.pos₁ v = n → v ∈ I.old → ¬ I.Inside C v →
      ReflTransGen (I.Step C) I.s v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv hvin
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [← I.pos₁_s] at hn
      rw [I.pos₁_inj hv I.s_mem hn]
    have hvlt := I.pos₁_lt hv
    set u := I.old[n - 1]'(by omega) with hu_def
    have hum : u ∈ I.old := List.getElem_mem _
    have hpu : I.pos₁ u = n - 1 := I.pos₁_getElem _ _
    have hout : I.out₁ u = some v := by
      have := I.out₁_getElem (n - 1) (by omega)
      rw [← hu_def] at this
      rw [this]
      congr 1
      have e : n - 1 + 1 = I.pos₁ v := by omega
      simp only [e]
      exact I.getElem_pos₁ hv
    -- a selected node `c` jumping exactly to `v`
    have jump : ∀ c ∈ C, I.pos₁ c < n → n ≤ I.dpos c → ReflTransGen (I.Step C) I.s v := by
      intro c hc h1 h2
      have hdc : I.dpos c = n := by
        by_contra hne
        exact hvin ⟨c, hc, by omega, by omega⟩
      obtain ⟨y, hy, hpy⟩ := I.out₂_of_fwd (hC.fwd c hc)
      have hyv : y = v := I.pos₁_inj (I.out₂_spec hy).2.1 hv (by omega)
      subst hyv
      exact (ih _ h1 c rfl (I.mem_old_of_fwd (hC.fwd c hc)) (hC.not_inside_of_mem hc)).tail
        (by unfold Step; rw [I.fwd_of_mem hc, hy])
    by_cases huC : u ∈ C
    · exact jump u huC (by omega) (by have := hC.fwd u huC; omega)
    by_cases huin : I.Inside C u
    · obtain ⟨c, hc, h1, h2⟩ := huin
      exact jump c hc (by omega) (by omega)
    · exact (ih _ (by omega) u hpu hum huin).tail (by unfold Step; rw [I.fwd_of_not_mem huC, hout])

/-- After the odd round (state `C`), the walk from `s` visits exactly the nodes not inside `C`. -/
theorem reach_iff_not_inside {v : V} (hv : v ∈ I.old) :
    ReflTransGen (I.Step C) I.s v ↔ ¬ I.Inside C v :=
  ⟨hC.not_inside_of_reach, hC.reach_of_not_inside _ v rfl hv⟩

/-- The nodes pruned in the even round are exactly the non-updated nodes that are not on the
`s`–`d` path after the odd round (Algorithm 1, line 11). -/
theorem mem_prune_iff {v : V} :
    v ∈ I.prune C ↔ v ∈ I.old ∧ v ∉ C ∧ ¬ ReflTransGen (I.Step C) I.s v := by
  rw [mem_prune]
  constructor
  · rintro ⟨hv, hc, hin⟩
    exact ⟨hv, hc, fun h => hC.not_inside_of_reach h hin⟩
  · rintro ⟨hv, hc, hr⟩
    refine ⟨hv, hc, ?_⟩
    by_contra h
    exact hr ((hC.reach_iff_not_inside hv).2 h)

/-- The kept nodes (the nodes of the merged line) are exactly the non-updated nodes on the
`s`–`d` path after the odd round. -/
theorem keep_iff {v : V} (hv : v ∈ I.old) :
    I.Keep C v ↔ v ∉ C ∧ ReflTransGen (I.Step C) I.s v := by
  rw [hC.reach_iff_not_inside hv]; rfl

/-! ### Counting -/

theorem nonkeep_eq : I.nodes.filter (fun v => ¬ I.Keep C v) =
    C.biUnion (fun c => I.nodes.filter (fun v => I.pos₁ c ≤ I.pos₁ v ∧ I.pos₁ v < I.dpos c)) := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_biUnion, I.mem_nodes]
  constructor
  · rintro ⟨hv, hk⟩
    by_cases hvC : v ∈ C
    · exact ⟨v, hvC, hv, le_rfl, hC.fwd v hvC⟩
    · have hin : I.Inside C v := by
        by_contra h; exact hk ⟨hvC, h⟩
      obtain ⟨c, hc, h1, h2⟩ := hin
      exact ⟨c, hc, hv, h1.le, h2⟩
  · rintro ⟨c, hc, hv, h1, h2⟩
    refine ⟨hv, fun hk => ?_⟩
    rcases Nat.lt_or_eq_of_le h1 with h1 | h1
    · exact hk.2 ⟨c, hc, h1, h2⟩
    · rw [I.pos₁_inj hv (I.mem_old_of_fwd (hC.fwd c hc)) h1.symm] at hk
      exact hk.1 hc

/-- The merged nodes are the disjoint union of the intervals `[pos₁ c, pos₁ (out₂ c))`. -/
theorem card_nonkeep :
    (I.nodes.filter (fun v => ¬ I.Keep C v)).card = ∑ c ∈ C, I.len c := by
  rw [hC.nonkeep_eq, Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [I.card_filter_pos_Ico (I.dpos_lt_of_fwd (hC.fwd c hc)).le]
    rfl
  · intro a ha c hc hac
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro v _ h1 h2
    have := hC.disj a ha c hc hac
    omega

/-- Every gap of the old route lies within distance `x - 1` of the interval of a selected node of
distance `x` (a non-selected crossing edge is blocked by a selected edge at least as long). -/
theorem cover :
    I.old.length - 1 ≤ ∑ c ∈ C, (3 * I.len c - 2) := by
  have hsub : Finset.range (I.old.length - 1) ⊆
      C.biUnion (fun c => Finset.Ico (I.pos₁ c + 1 - I.len c) (I.dpos c + I.len c - 1)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨u, h1, h2⟩ := I.exists_cross (i := i) (by omega)
    have hu : I.pos₁ u < I.dpos u := by omega
    rw [Finset.mem_biUnion]
    by_cases huC : u ∈ C
    · refine ⟨u, huC, ?_⟩
      rw [Finset.mem_Ico]; unfold len; omega
    · obtain ⟨v, hv, hlen, hb⟩ := hC.blocked u hu huC
      refine ⟨v, hv, ?_⟩
      have := hC.fwd v hv
      rw [Finset.mem_Ico]; unfold len at *; unfold Blocks at hb; omega
  calc I.old.length - 1 = (Finset.range (I.old.length - 1)).card := by simp
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ _ := by
      refine Finset.sum_le_sum (fun c hc => ?_)
      have := hC.fwd c hc
      rw [Nat.card_Ico]; unfold len; omega

/-- The number of nodes of the merged line. -/
theorem reduce_length_eq :
    (I.reduce hC).old.length = (I.nodes.filter (fun v => I.Keep C v)).card := by
  rw [hC.reduce_old, ← List.toFinset_card_of_nodup (I.nodup.filter _), List.toFinset_filter]
  simp [nodes]

/-- **Lemma 2** (in the recursive form used by the algorithm): a double round of Peacock on a line
with `N ≥ 2` nodes leaves, after node merging, a line with `N'` nodes where `3 N' + 1 ≤ 2 N`. -/
theorem reduce_length (hN : 2 ≤ I.old.length) :
    3 * (I.reduce hC).old.length + 1 ≤ 2 * I.old.length := by
  have hcard : I.nodes.card = I.old.length := List.toFinset_card_of_nodup I.nodup
  have hsplit := Finset.card_filter_add_card_filter_not (s := I.nodes) (fun v => I.Keep C v)
  rw [hcard, ← hC.reduce_length_eq, hC.card_nonkeep] at hsplit
  have hcov := hC.cover
  have hsum : ∑ c ∈ C, (3 * I.len c - 2) + 2 * C.card = 3 * ∑ c ∈ C, I.len c := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have := hC.fwd c hc
    unfold len; omega
  have hne : 1 ≤ C.card := by
    by_contra h
    have : C = ∅ := Finset.card_eq_zero.1 (by omega)
    subst this
    simp at hcov; omega
  omega

theorem reduce_length_lt (hN : 2 ≤ I.old.length) :
    (I.reduce hC).old.length < I.old.length := by
  have := hC.reduce_length hN; omega

open Classical in
/-- **Lemma 2** (Ludwig–Marcinkowski–Schmid, PODC 2015). Let the current network be a line with
`N ≥ 2` nodes and let `C` be the set of nodes updated in the odd (shortcut) round. After node merging
(every updated node is merged into the target of its new rule), the path from `s` to `d` consists of
the non-updated nodes on the walk from `s` in state `C`; their number `N'` satisfies `3 N' + 1 ≤ 2 N`,
i.e. the path shrinks by at least `(N + 1) / 3` nodes.

Without merging (counting also the updated nodes on the walk) the statement is false; see the module
docstring. -/
theorem lemma2 (hN : 2 ≤ I.old.length) :
    3 * {v ∈ I.nodes | v ∉ C ∧ ReflTransGen (I.Step C) I.s v}.card + 1 ≤ 2 * I.old.length := by
  have : {v ∈ I.nodes | v ∉ C ∧ ReflTransGen (I.Step C) I.s v} =
      I.nodes.filter (fun v => I.Keep C v) := by
    ext v
    simp only [Finset.mem_filter, I.mem_nodes]
    constructor
    · rintro ⟨hv, h⟩; exact ⟨hv, (hC.keep_iff hv).2 h⟩
    · rintro ⟨hv, h⟩; exact ⟨hv, (hC.keep_iff hv).1 h⟩
  rw [this, ← hC.reduce_length_eq]
  exact hC.reduce_length hN

end GoodSelection

end Instance

end Podc.LoopFreeUpdates
