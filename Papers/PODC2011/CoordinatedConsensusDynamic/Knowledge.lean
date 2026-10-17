import Papers.PODC2011.CoordinatedConsensusDynamic.Hiding

/-!
# Lemma 3.1: knowing that one has heard from everyone (unknown `n`)

`u` knows at time `t` that `past(u,t)(0) = V` iff `past(u,t)(0) = past(u,t)(1)`, in the system
`UnknownN` where nothing is known about the count. The "if" direction uses only connectivity of
round 1; the "only if" direction attaches a fresh node to some `v ∈ past(u,t)(0) \ past(u,t)(1)`.
We also formalize the remark after the lemma: if `past(u,t)(0) ≠ past(u,t)(1)`, then `u` knows no
upper bound on `|V|` and does not know the value of any input function `f` that can always be
changed by adding more inputs (minimum/maximum over unbounded domains, majority, …).
-/

namespace CoordCons

open DGraph Relation
open Cslib.DynNet (Journey)

variable {α : Type*} {G : DGraph α}

/-- The combinatorial core of Lemma 3.1: if every node heard of at time `0` was also heard of at
time `1`, then `u` has heard from everybody at time `1`. -/
theorem reach_one_of_closed (hG : G.Valid) {u t : ℕ} (hu : u ∈ G.V)
    (hc : ∀ w, G.Reach w 0 u t → G.Reach w 1 u t) : ∀ w ∈ G.V, G.Reach w 1 u t := by
  have ht : 1 ≤ t := (hc u (Journey.self (Nat.zero_le t))).le
  intro y hy
  by_contra hyp
  obtain ⟨z, x, hzx, hz, hx⟩ := Cslib.DynNet.exists_edge_cross
    (S := fun x => G.Reach x 1 u t) (hG.conn 1 le_rfl y hy u hu) hyp (Journey.self ht)
  exact hz (hc z (Journey.cons (Or.inr hzx) hx))

theorem past_eq_V_of_past_eq (hG : G.Valid) {u t : ℕ} (hu : u ∈ G.V)
    (h : G.past u t 0 = G.past u t 1) : G.past u t 0 = G.V := by
  apply Finset.Subset.antisymm (past_subset _ _ _)
  intro w hw
  have hc : ∀ w, G.Reach w 0 u t → G.Reach w 1 u t := by
    intro w hw0
    have hwV := (hw0.mem_iff hG).2 hu
    have : w ∈ G.past u t 1 := h ▸ mem_past.2 ⟨hwV, hw0⟩
    exact (mem_past.1 this).2
  exact mem_past.2 ⟨hw, (reach_one_of_closed hG hu hc w hw).mono_left (Nat.zero_le 1)⟩

/-- **Lemma 3.1.** With no a-priori knowledge of the count, `u` knows at time `t` that it has
heard from all nodes iff `past(u,t)(0) = past(u,t)(1)`. -/
theorem lemma_3_1 (hG : UnknownN G) {u t : ℕ} (hu : u ∈ G.V) :
    Knows UnknownN G u t (fun H => H.past u t 0 = H.V) ↔ G.past u t 0 = G.past u t 1 := by
  constructor
  · intro hK
    by_contra hne
    obtain ⟨v, hv0, hv1⟩ : ∃ v ∈ G.past u t 0, v ∉ G.past u t 1 := by
      by_contra hcon
      push Not at hcon
      exact hne (Finset.Subset.antisymm hcon (past_succ_subset u t 0))
    have hv1' : ¬ G.Reach v 1 u t := fun h => hv1 (mem_past.2 ⟨(mem_past.1 hv0).1, h⟩)
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset G.V
    have hH : UnknownN (G.addLeaf x v) := ⟨hG.1.addLeaf hx (mem_past.1 hv0).1, hG.2⟩
    have hind := indist_addLeaf hG.1 hu hx hv1'
    have : (G.addLeaf x v).past u t 0 = (G.addLeaf x v).V := hK _ hH hind
    rw [← hind.past_eq hG.1 hH.1] at this
    have hxV : x ∈ (G.addLeaf x v).V := Finset.mem_insert_self _ _
    rw [← this] at hxV
    exact hx (past_subset _ _ _ hxV)
  · intro h H hH hind
    have h' : H.past u t 0 = H.past u t 1 := by
      rw [← hind.past_eq hG.1 hH.1, ← hind.past_eq hG.1 hH.1]; exact h
    exact past_eq_V_of_past_eq hH.1 hind.mem_right h'

/-- Attaching new leaves (with prescribed inputs) to a node `v` not heard of since time `1`. -/
theorem exists_indist_extend (hG : UnknownN G) {u t v : ℕ} (hu : u ∈ G.V) (hv : v ∈ G.V)
    (hv1 : ¬ G.Reach v 1 u t) (s : Multiset α) :
    ∃ H, UnknownN H ∧ Indist G H u t ∧ v ∈ H.V ∧ H.V.card = G.V.card + Multiset.card s ∧
      H.V.val.map H.input = G.V.val.map G.input + s := by
  classical
  induction s using Multiset.induction_on with
  | empty => exact ⟨G, hG, Indist.refl hG.1 hu t, hv, by simp, by simp⟩
  | cons c s ih =>
    obtain ⟨H, hH, hind, hvH, hcard, hmap⟩ := ih
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset H.V
    have hv1H : ¬ H.Reach v 1 u t := fun h => hv1 (hind.reach_iff.2 h)
    have huH := hind.mem_right
    have hL : UnknownN (H.addLeaf x v) := ⟨hH.1.addLeaf hx hvH, hH.2⟩
    have hind1 := indist_addLeaf hH.1 huH hx hv1H
    have hx0 : ¬ (H.addLeaf x v).Reach x 0 u t := by
      intro hr
      have : x ∈ (H.addLeaf x v).past u t 0 := mem_past.2 ⟨Finset.mem_insert_self _ _, hr⟩
      rw [← hind1.past_eq hH.1 hL.1] at this
      exact hx (past_subset _ _ _ this)
    have hind2 := indist_setInput hL.1 hind1.mem_right c hx0
    refine ⟨(H.addLeaf x v).setInput x c, ⟨hL.1.setInput _ _, hH.2⟩,
      hind.trans (hind1.trans hind2), Finset.mem_insert_of_mem hvH, ?_, ?_⟩
    · show (insert x H.V).card = _
      rw [Finset.card_insert_of_notMem hx, hcard, Multiset.card_cons]; ring
    · show (insert x H.V).val.map (Function.update H.input x c) = _
      rw [Finset.insert_val_of_notMem hx, Multiset.map_cons, Function.update_self,
        Multiset.add_cons, ← hmap]
      congr 1
      refine Multiset.map_congr rfl (fun y hy => ?_)
      have : y ≠ x := fun h => hx (h ▸ hy)
      rw [Function.update_of_ne this]

/-- Remark after Lemma 3.1: if `past(u,t)(0) ≠ past(u,t)(1)` and the count is not known a priori,
`u` knows no upper bound on the number of nodes. -/
theorem not_knows_bound (hG : UnknownN G) {u t : ℕ} (hu : u ∈ G.V)
    (h : G.past u t 0 ≠ G.past u t 1) (m : ℕ) [Inhabited α] :
    ¬ Knows UnknownN G u t (fun H => H.V.card ≤ m) := by
  intro hK
  obtain ⟨v, hv0, hv1⟩ : ∃ v ∈ G.past u t 0, v ∉ G.past u t 1 := by
    by_contra hcon
    push Not at hcon
    exact h (Finset.Subset.antisymm hcon (past_succ_subset u t 0))
  have hv1' : ¬ G.Reach v 1 u t := fun h => hv1 (mem_past.2 ⟨(mem_past.1 hv0).1, h⟩)
  obtain ⟨H, hH, hind, -, hcard, -⟩ := exists_indist_extend hG hu (mem_past.1 hv0).1 hv1'
    (Multiset.replicate (m + 1) default)
  have := hK H hH hind
  simp at hcard
  omega

/-- Remark after Lemma 3.1: if `past(u,t)(0) ≠ past(u,t)(1)`, `u` does not know the value of any
function `f` of the multiset of inputs that can always be changed by adding further inputs
(e.g. minimum or maximum over an unbounded domain, majority). -/
theorem not_knows_value {β : Type*} (f : Multiset α → β)
    (hf : ∀ s, ∃ s', f (s + s') ≠ f s) (hG : UnknownN G) {u t : ℕ} (hu : u ∈ G.V)
    (h : G.past u t 0 ≠ G.past u t 1) (b : β) :
    ¬ Knows UnknownN G u t (fun H => f (H.V.val.map H.input) = b) := by
  intro hK
  obtain ⟨v, hv0, hv1⟩ : ∃ v ∈ G.past u t 0, v ∉ G.past u t 1 := by
    by_contra hcon
    push Not at hcon
    exact h (Finset.Subset.antisymm hcon (past_succ_subset u t 0))
  have hv1' : ¬ G.Reach v 1 u t := fun h => hv1 (mem_past.2 ⟨(mem_past.1 hv0).1, h⟩)
  have hb : f (G.V.val.map G.input) = b := hK G hG (Indist.refl hG.1 hu t)
  obtain ⟨s', hs'⟩ := hf (G.V.val.map G.input)
  obtain ⟨H, hH, hind, -, -, hmap⟩ := exists_indist_extend hG hu (mem_past.1 hv0).1 hv1' s'
  have : f (H.V.val.map H.input) = b := hK H hH hind
  rw [hmap] at this
  exact hs' (this.trans hb.symm)

end CoordCons
