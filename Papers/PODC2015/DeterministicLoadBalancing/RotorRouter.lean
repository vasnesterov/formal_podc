import Papers.PODC2015.DeterministicLoadBalancing.Model
import Podc.Foundations.Combinatorics.SimpleGraph.OddGirth

/-!
# The ROTOR-ROUTER without self-loops

Berenbrink, Klasing, Kosowski, Mallmann-Trenn, Uznański, PODC 2015 (arXiv:1404.4344v4),
Section 1.1 and Theorem 4.3 (`d⁺ = d`: no self-loops).

Every node `v` has a fixed cyclic order of its `d` edges (`ord v : Fin d ≃ N(v)`) and a rotor
`ρ : Fin d` pointing to one of them. A node holding `x` tokens sends them one by one, starting at
the edge the rotor points to and advancing the rotor after each token. Hence the edge at position
`i` receives `⌊x/d⌋ + [ (i − ρ) mod d < x mod d ]` tokens, and the rotor advances by `x mod d`.

This file defines the balancer (`rotorRouter`) and proves an abstract periodicity lemma
(`rotorRouter_periodic`): every symmetric "two-phase" flow `g` (with `g v w + g w v = 2L` along
every edge and the values `g v ·` within `1` of each other) is realised by the rotor-router for
suitable edge orders and initial rotors, alternating between the loads `Σ_w g v w` and
`Σ_w g w v`.
-/

open Finset Fin.NatCast

namespace Podc.DeterministicLoadBalancing

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

section RotorRouter

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} [NeZero d]

/-- Summing a port-indexed quantity over the neighbours, through the port numbering. -/
lemma sum_neighbor_port (S : Finset V) (ord : Fin d ≃ S) (F : Fin d → ℕ) :
    ∑ w ∈ S, (if h : w ∈ S then F (ord.symm ⟨w, h⟩) else 0) = ∑ i, F i := by
  rw [← Finset.sum_coe_sort S]
  simp only [Finset.coe_mem, dite_true]
  exact Equiv.sum_comp ord.symm F

/-- Number of tokens the rotor-router sends over the edge at position `i` when the rotor is at `ρ`
and the node holds `x` tokens. -/
def rotorShare (ρ i : Fin d) (x : ℕ) : ℕ := x / d + if (i - ρ).val < x % d then 1 else 0

lemma sum_rotorShare (ρ : Fin d) (x : ℕ) : ∑ i, rotorShare ρ i x = x := by
  unfold rotorShare
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hc := Equiv.sum_comp (Equiv.subRight ρ) (fun j : Fin d => if j.val < x % d then 1 else 0)
  simp only [Equiv.subRight_apply] at hc
  rw [hc, Finset.sum_boole, Fin.card_filter_val_lt]
  have := Nat.mod_lt x (NeZero.pos d)
  rw [min_eq_right this.le]
  push_cast
  exact Nat.div_add_mod x d

/-- **ROTOR-ROUTER** without self-loops, with edge orders `ord` and initial rotors `ρ₀`. -/
def rotorRouter (ord : ∀ v, Fin d ≃ G.neighborFinset v) (ρ₀ : V → Fin d) : Balancer G where
  σ := Fin d
  init := ρ₀
  out v ρ x w := if h : w ∈ G.neighborFinset v then rotorShare ρ ((ord v).symm ⟨w, h⟩) x else 0
  keep _ _ _ := 0
  next _ ρ x := ρ + (x : Fin d)
  conserve v ρ x := by
    rw [zero_add, sum_neighbor_port _ (ord v) (fun i => rotorShare ρ i x), sum_rotorShare]

/-- The rotor-router output for a load `d a + k` (`k ≤ d`): `a + 1` on the `k` edges following the
rotor, `a` on the others; the rotor advances by `k`. -/
lemma rotorShare_eq (ρ i : Fin d) (a k : ℕ) (hk : k ≤ d) :
    rotorShare ρ i (d * a + k) = a + if (i - ρ).val < k then 1 else 0 := by
  unfold rotorShare
  have hd := NeZero.pos d
  rcases hk.lt_or_eq with hk | hk
  · rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hk, Nat.mul_add_mod, Nat.mod_eq_of_lt hk, add_zero]
  · have : d * a + d = d * (a + 1) := by ring
    rw [hk, this, Nat.mul_div_cancel_left _ hd, Nat.mul_mod_right]
    simp [(i - ρ).isLt]

lemma natCast_mul_add (a k : ℕ) (d : ℕ) [NeZero d] : ((d * a + k : ℕ) : Fin d) = (k : Fin d) := by
  simp

/-- For `k ≤ d`: `(i − k) mod d < d − k` iff `k ≤ i`. -/
lemma sub_natCast_val_lt_iff (i : Fin d) (k : ℕ) (hk : k ≤ d) :
    (i - (k : Fin d)).val < d - k ↔ k ≤ i.val := by
  rcases hk.lt_or_eq with hk | rfl
  · have hkv : ((k : Fin d) : ℕ) = k := by rw [Fin.val_natCast, Nat.mod_eq_of_lt hk]
    by_cases hki : k ≤ i.val
    · have : (k : Fin d) ≤ i := by rw [Fin.le_def, hkv]; exact hki
      rw [Fin.coe_sub_iff_le.2 this, hkv]; omega
    · have : i < (k : Fin d) := by rw [Fin.lt_def, hkv]; omega
      rw [Fin.coe_sub_iff_lt.2 this, hkv]; omega
  · simp only [Fin.natCast_self, sub_zero, Nat.sub_self, Nat.not_lt_zero, false_iff, not_le]
    exact i.isLt

/-- Existence of an edge order listing a prescribed subset `P` of the neighbours first. -/
lemma exists_ord_prefix (S P : Finset V) (hPS : P ⊆ S) (hS : S.card = d) (v₀ : V) :
    ∃ ord : Fin d ≃ S, ∀ i, ((ord i : V) ∈ P ↔ i.val < P.card) := by
  classical
  let f : Fin d → V := fun i => if h : i.val < P.card then (P.equivFin.symm ⟨i.val, h⟩ : V) else v₀
  have hf : ∀ i (h : i.val < P.card), f i = (P.equivFin.symm ⟨i.val, h⟩ : V) := fun i h => by simp [f, h]
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq (α := Fin d) (t := S)
    (s := univ.filter fun i : Fin d => i.val < P.card) (f := f) (by simp [hS])
    (by
      intro y hy
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      rw [hf i hi]; exact hPS (Finset.coe_mem _))
    (by
      intro i hi j hj hij
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
      rw [hf i hi, hf j hj] at hij
      have := P.equivFin.symm.injective (Subtype.ext hij)
      exact Fin.ext (by simpa using this))
  refine ⟨g, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · by_contra hlt
    set j := P.equivFin ⟨g i, hi⟩ with hj
    have hjP : j.val < P.card := j.isLt
    have hdj : j.val < d := lt_of_lt_of_le hjP (hS ▸ Finset.card_le_card hPS)
    have h1 : (g ⟨j.val, hdj⟩ : V) = g i := by
      rw [hg _ (by simp [hjP]), hf _ hjP]
      simp [hj]
    have := g.injective (Subtype.ext h1)
    rw [← this] at hlt
    exact hlt hjP
  · rw [hg i (by simpa using hi), hf i hi]
    exact Finset.coe_mem _

lemma rotorRouter_out_of_mem (ord : ∀ v, Fin d ≃ G.neighborFinset v) (ρ₀ : V → Fin d) {v w : V}
    (h : w ∈ G.neighborFinset v) (ρ : Fin d) (x : ℕ) :
    (rotorRouter ord ρ₀).out v ρ x w = rotorShare ρ ((ord v).symm ⟨w, h⟩) x := by
  simp [rotorRouter, h]

/-- **Periodic rotor-router executions.** Let `g` be a flow on the darts of a `d`-regular graph
with `g v w + g w v = 2L` along every edge and, at every node, values in `{a v, a v + 1}`
(`a v + 1 ≤ 2L`). Then for suitable edge orders and initial rotors the rotor-router started from
the loads `Σ_w g v w` sends exactly `g` in even steps and the reversed flow `g w v` in odd steps, so
the loads alternate between `Σ_w g v w` and `Σ_w g w v`. -/
theorem rotorRouter_periodic (hreg : G.IsRegularOfDegree d) (g : V → V → ℕ) (L : ℕ) (a : V → ℕ)
    (hsym : ∀ v w, G.Adj v w → g v w + g w v = 2 * L)
    (hval : ∀ v w, G.Adj v w → g v w = a v ∨ g v w = a v + 1)
    (ha : ∀ v, a v + 1 ≤ 2 * L) :
    ∃ (ord : ∀ v, Fin d ≃ G.neighborFinset v) (ρ₀ : V → Fin d), ∀ t,
      (rotorRouter ord ρ₀).load (fun v => ∑ w ∈ G.neighborFinset v, g v w) (2 * t) =
          (fun v => ∑ w ∈ G.neighborFinset v, g v w) ∧
      (rotorRouter ord ρ₀).load (fun v => ∑ w ∈ G.neighborFinset v, g v w) (2 * t + 1) =
          (fun v => ∑ w ∈ G.neighborFinset v, g w v) := by
  classical
  set P : V → Finset V := fun v => (G.neighborFinset v).filter (fun w => g v w = a v + 1) with hPdef
  have hcardN : ∀ v, (G.neighborFinset v).card = d := fun v => by
    rw [G.card_neighborFinset_eq_degree, hreg v]
  have hPN : ∀ v, P v ⊆ G.neighborFinset v := fun v => Finset.filter_subset _ _
  have hPd : ∀ v, (P v).card ≤ d := fun v => hcardN v ▸ Finset.card_le_card (hPN v)
  choose ord hord using fun v => exists_ord_prefix (G.neighborFinset v) (P v) (hPN v) (hcardN v) v
  refine ⟨ord, fun _ => 0, ?_⟩
  set x0 : V → ℕ := fun v => ∑ w ∈ G.neighborFinset v, g v w with hx0def
  set x1 : V → ℕ := fun v => ∑ w ∈ G.neighborFinset v, g w v with hx1def
  set ρ1 : V → Fin d := fun v => ((P v).card : Fin d) with hρ1
  -- membership in `P` is decided by the position in the edge order
  have hpos : ∀ v w (h : w ∈ G.neighborFinset v),
      (((ord v).symm ⟨w, h⟩).val < (P v).card ↔ w ∈ P v) := by
    intro v w h
    have := hord v ((ord v).symm ⟨w, h⟩)
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm
  have hgval : ∀ v w, w ∈ G.neighborFinset v → g v w = a v + if w ∈ P v then 1 else 0 := by
    intro v w h
    have hadj := (G.mem_neighborFinset _ _).1 h
    simp only [hPdef, Finset.mem_filter, h, true_and]
    rcases hval v w hadj with h' | h' <;> simp [h']
  have hx0 : ∀ v, x0 v = d * a v + (P v).card := by
    intro v
    simp only [hx0def]
    rw [Finset.sum_congr rfl (hgval v), Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      hcardN, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hPN v),
      Nat.cast_id, mul_comm]
  have hrev : ∀ v w, w ∈ G.neighborFinset v →
      g w v = (2 * L - a v - 1) + if w ∈ P v then 0 else 1 := by
    intro v w h
    have hs := hsym v w ((G.mem_neighborFinset _ _).1 h)
    have hv := hgval v w h
    have := ha v
    split_ifs at hv ⊢ <;> omega
  have hx1 : ∀ v, x1 v = d * (2 * L - a v - 1) + (d - (P v).card) := by
    intro v
    simp only [hx1def]
    rw [Finset.sum_congr rfl (hrev v), Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      hcardN]
    have : ∑ w ∈ G.neighborFinset v, (if w ∈ P v then 0 else 1) = d - (P v).card := by
      have h1 := Finset.sum_filter_add_sum_filter_not (G.neighborFinset v) (· ∈ P v)
        (fun w => if w ∈ P v then 0 else 1)
      have h2 : ∑ w ∈ (G.neighborFinset v).filter (· ∉ P v), (if w ∈ P v then 0 else 1) =
          ((G.neighborFinset v).filter (· ∉ P v)).card := by
        rw [Finset.card_eq_sum_ones]
        exact Finset.sum_congr rfl fun w hw => by simp [(Finset.mem_filter.1 hw).2]
      have h3 : ∑ w ∈ (G.neighborFinset v).filter (· ∈ P v), (if w ∈ P v then 0 else 1) = 0 :=
        Finset.sum_eq_zero fun w hw => by simp [(Finset.mem_filter.1 hw).2]
      have h4 := Finset.card_filter_add_card_filter_not (s := G.neighborFinset v)
        (fun w => w ∈ P v)
      have h5 : (G.neighborFinset v).filter (· ∈ P v) = P v := by
        rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hPN v)]
      rw [h5] at h4
      rw [← h1, h2, h3, hcardN] at *
      omega
    rw [this, mul_comm]
  have hout0 : ∀ v w (h : w ∈ G.neighborFinset v),
      (rotorRouter ord (fun _ => (0 : Fin d))).out v (0 : Fin d) (x0 v) w = g v w := by
    intro v w h
    rw [rotorRouter_out_of_mem ord _ h, hx0, rotorShare_eq _ _ _ _ (hPd v), sub_zero, hgval v w h]
    congr 1
    have := hpos v w h
    split_ifs <;> tauto
  have hout1 : ∀ v w (h : w ∈ G.neighborFinset v),
      (rotorRouter ord (fun _ => (0 : Fin d))).out v (ρ1 v) (x1 v) w = g w v := by
    intro v w h
    rw [rotorRouter_out_of_mem ord _ h, hx1, rotorShare_eq _ _ _ _ (Nat.sub_le _ _), hrev v w h]
    congr 1
    have key : ((ord v).symm ⟨w, h⟩ - ρ1 v).val < d - (P v).card ↔ w ∉ P v := by
      rw [show ρ1 v = ((P v).card : Fin d) from rfl, sub_natCast_val_lt_iff _ _ (hPd v),
        ← hpos v w h, not_lt]
    by_cases hw : w ∈ P v <;> simp [hw, key]
  have hstep0 : (rotorRouter ord (fun _ => (0 : Fin d))).step (x0, fun _ => (0 : Fin d)) = (x1, ρ1) := by
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · simp only [Balancer.step]
      simp only [rotorRouter, zero_add]
      refine Finset.sum_congr rfl fun w hw => ?_
      have hv : v ∈ G.neighborFinset w := by
        rw [SimpleGraph.mem_neighborFinset] at hw ⊢; exact hw.symm
      exact hout0 w v hv
    · simp only [Balancer.step, rotorRouter, zero_add]
      rw [hx0, natCast_mul_add]
  have hstep1 : (rotorRouter ord (fun _ => (0 : Fin d))).step (x1, ρ1) = (x0, fun _ => (0 : Fin d)) := by
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · simp only [Balancer.step]
      simp only [rotorRouter, zero_add]
      refine Finset.sum_congr rfl fun w hw => ?_
      have hv : v ∈ G.neighborFinset w := by
        rw [SimpleGraph.mem_neighborFinset] at hw ⊢; exact hw.symm
      exact hout1 w v hv
    · simp only [Balancer.step, rotorRouter]
      rw [hx1, natCast_mul_add, hρ1]
      dsimp only
      rw [← Nat.cast_add, Nat.add_sub_cancel' (hPd v), Fin.natCast_self]
  have hconf : ∀ t, (rotorRouter ord (fun _ => (0 : Fin d))).config x0 (2 * t) = (x0, fun _ => (0 : Fin d)) ∧
      (rotorRouter ord (fun _ => (0 : Fin d))).config x0 (2 * t + 1) = (x1, ρ1) := by
    intro t
    induction t with
    | zero => exact ⟨rfl, hstep0⟩
    | succ t ih =>
      have e1 : (rotorRouter ord (fun _ => (0 : Fin d))).config x0 (2 * (t + 1)) =
          (x0, fun _ => (0 : Fin d)) := by
        rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring]
        show (rotorRouter ord (fun _ => (0 : Fin d))).step
          ((rotorRouter ord (fun _ => (0 : Fin d))).config x0 (2 * t + 1)) = _
        rw [ih.2]; exact hstep1
      refine ⟨e1, ?_⟩
      show (rotorRouter ord (fun _ => (0 : Fin d))).step
        ((rotorRouter ord (fun _ => (0 : Fin d))).config x0 (2 * (t + 1))) = _
      rw [e1]; exact hstep0
  intro t
  exact ⟨congrArg Prod.fst (hconf t).1, congrArg Prod.fst (hconf t).2⟩

end RotorRouter

end Podc.DeterministicLoadBalancing
