import Papers.PODC2024.MinWeightCycleCongest.DirectedGadget

/-!
# The undirected weighted lower-bound graph (Lemma 14 of the companion paper)

arXiv:2205.14797v2, §3.1.2, Figure 5, Lemma 14, with the light/heavy weights `1` and `w`
(the paper uses `w = 2` for the exact bound and "any `w ≥ 2`" for the `(2 - ε)` bound).

Vertices as in `DirectedGadget.lean`. Edges: `ℓ_i r_i` and `ℓ'_i r'_i` of weight `1` ("light");
`ℓ_i ℓ'_j` iff `x (i, j)` and `r_i r'_j` iff `y (i, j)`, of weight `w` ("heavy"); and — our
addition for the constant-diameter claim — `hub v` of weight `2w` for every `v ≠ hub`.

Lemma 14 (generalised): if the sets intersect there is a cycle of weight `2w + 2`; otherwise every
cycle has weight `≥ 4w` (`uGraph.weight_ge`). The paper's argument ("bipartite, the light edges form
a matching, so a cycle has at most as many light as heavy edges, hence a cycle with `≥ 6` edges
weighs `≥ 9`") only covers `w = 2`: for large `w` it gives only `3w + 3` for a `6`-cycle, which is
below `4w`. The repair uses that a light edge is the only kind of edge between Alice's side
`L ∪ L'` and Bob's side `R ∪ R'`, so every cycle has an *even* number of light edges.
-/

namespace Podc.MinWeightCycleCongest

open Finset Vtx

variable {k p : ℕ}

/-- Edge weights of the undirected lower-bound graph (as natural numbers). -/
def uval (w : ℕ) (x y : Fin k × Fin k → Bool) : Vtx k p → Vtx k p → Option ℕ
  | .l i, .r j => if i = j then some 1 else none
  | .r i, .l j => if j = i then some 1 else none
  | .l' i, .r' j => if i = j then some 1 else none
  | .r' i, .l' j => if j = i then some 1 else none
  | .l i, .l' j => if x (i, j) then some w else none
  | .l' j, .l i => if x (i, j) then some w else none
  | .r i, .r' j => if y (i, j) then some w else none
  | .r' j, .r i => if y (i, j) then some w else none
  | .hub, .hub => none
  | .hub, _ => some (2 * w)
  | _, .hub => some (2 * w)
  | _, _ => none

variable {w W : ℕ} {x y : Fin k × Fin k → Bool}

lemma uval_symm (u v : Vtx k p) : uval w x y u v = uval w x y v u := by
  cases u <;> cases v <;> rfl

lemma uval_self (v : Vtx k p) : uval w x y v v = none := by
  cases v <;> simp [uval]

lemma uval_le (hw : 1 ≤ w) {u v : Vtx k p} {n : ℕ} (h : uval w x y u v = some n) :
    n ≤ 2 * w := by
  cases u <;> cases v <;> simp only [uval] at h <;> (try split_ifs at h) <;> (try cases h) <;>
    omega

/-- The undirected weighted lower-bound graph `G_{x,y}` (weights are capped at `W`; the cap is
never active when `2w ≤ W`). -/
def uGraph (W w : ℕ) (x y : Fin k × Fin k → Bool) : WGraph (Vtx k p) W where
  wt u v := (uval w x y u v).map fun n => ⟨min n W, Nat.lt_succ_of_le (min_le_right _ _)⟩
  symm u v := by rw [uval_symm]
  loopless v := by rw [uval_self]; rfl

lemma uGraph_isSome {u v : Vtx k p} :
    ((uGraph W w x y).wt u v).isSome ↔ (uval w x y u v).isSome := by
  simp [uGraph]

lemma uGraph_w (hw : 1 ≤ w) (hW : 2 * w ≤ W) {u v : Vtx k p} {n : ℕ} (h : uval w x y u v = some n) :
    (uGraph W w x y).w u v = n := by
  have := uval_le hw h
  simp [WGraph.w, uGraph, h]
  omega

/-- Alice's side (`0`: `L ∪ L'`) or Bob's side (`1`: `R ∪ R'`). -/
def side : Vtx k p → ZMod 2
  | .l _ => 0
  | .l' _ => 0
  | .r _ => 1
  | .r' _ => 1
  | .hub => 0
  | .pad _ => 0

/-- The bipartition `L ∪ R'` / `R ∪ L'`. -/
def chi : Vtx k p → ZMod 2
  | .l _ => 0
  | .r' _ => 0
  | .r _ => 1
  | .l' _ => 1
  | .hub => 0
  | .pad _ => 0

/-- The only neighbour of a padding vertex is the hub. -/
lemma uval_pad {u : Vtx k p} {j : Fin p} (h : (uval w x y (.pad j) u).isSome) : u = .hub := by
  cases u <;> simp_all [uval]

lemma uval_hub {v : Vtx k p} (hv : v ≠ .hub) : uval w x y v .hub = some (2 * w) := by
  cases v <;> simp_all [uval]

lemma uval_hub' {v : Vtx k p} (hv : v ≠ .hub) : uval w x y .hub v = some (2 * w) := by
  rw [uval_symm]; exact uval_hub hv

/-- Gadget edges (between non-hub vertices) change the colour `chi`. -/
lemma chi_edge {u v : Vtx k p} (h : (uval w x y u v).isSome) (hu : u ≠ .hub) (hv : v ≠ .hub) :
    chi v = chi u + 1 := by
  cases u <;> cases v <;> simp_all [uval, chi] <;> decide

/-- A gadget edge is light (weight `1`) iff it changes sides, heavy (weight `w`) otherwise. -/
lemma uval_side {u v : Vtx k p} {n : ℕ} (h : uval w x y u v = some n) (hu : u ≠ .hub)
    (hv : v ≠ .hub) : n = if side u = side v then w else 1 := by
  cases u <;> cases v <;> simp only [uval] at h <;> (try split_ifs at h) <;> (try cases h) <;>
    simp_all [side]

/-- Light edges form a matching. -/
lemma light_unique {u v z : Vtx k p} (h1 : (uval w x y u v).isSome) (h2 : (uval w x y v z).isSome)
    (hu : u ≠ .hub) (hv : v ≠ .hub) (hz : z ≠ .hub) (s1 : side u ≠ side v)
    (s2 : side v ≠ side z) : u = z := by
  set_option linter.unusedSimpArgs false in
  cases u <;> cases v <;> simp_all [uval, side] <;> cases z <;> simp_all [uval, side]

/-- A light–heavy–light–heavy closed walk of gadget edges forces an element of `S_a ∩ S_b`. -/
lemma uval_four {u₀ u₁ u₂ u₃ : Vtx k p} (h01 : (uval w x y u₀ u₁).isSome)
    (h12 : (uval w x y u₁ u₂).isSome) (h23 : (uval w x y u₂ u₃).isSome)
    (h30 : (uval w x y u₃ u₀).isSome) (h0 : u₀ ≠ .hub) (h1 : u₁ ≠ .hub) (h2 : u₂ ≠ .hub)
    (h3 : u₃ ≠ .hub) (s01 : side u₀ ≠ side u₁) (s12 : side u₁ = side u₂)
    (s23 : side u₂ ≠ side u₃) : ∃ q, x q = true ∧ y q = true := by
  cases u₀ <;> cases u₁ <;> cases u₂ <;> cases u₃ <;> simp_all [uval, side] <;>
    subst_vars <;> first | exact ⟨_, _, h30, h12⟩ | exact ⟨_, _, h12, h30⟩

namespace uGraph

variable (c : (uGraph (p := p) W w x y).Cycle)

lemma adj (i : ℕ) : (uval w x y (c.vtx i) (c.vtx (i + 1))).isSome := uGraph_isSome.1 (c.adj i)

lemma vtx_add_len (i : ℕ) : c.vtx (i + c.len) = c.vtx i := c.periodic i

/-- Shift invariance of the weight. -/
lemma weight_shift (s : ℕ) :
    c.weight = ∑ t ∈ range c.len, (uGraph W w x y).w (c.vtx (s + t)) (c.vtx (s + t + 1)) := by
  unfold WGraph.Cycle.weight
  exact (sum_shift (fun t => (uGraph W w x y).w (c.vtx t) (c.vtx (t + 1)))
    (fun i => by simp only [c.periodic, Nat.add_right_comm i c.len 1]) s).symm

/-- A cycle through the hub weighs at least `4w` (two hub edges of weight `2w`). -/
lemma weight_ge_of_hub (hw : 1 ≤ w) (hW : 2 * w ≤ W) {i : ℕ} (hi : c.vtx i = .hub) :
    4 * w ≤ c.weight := by
  have hL := c.three_le_len
  set j := i + c.len - 1 with hj
  have e1 : c.vtx (j + 1) = .hub := by
    rw [show j + 1 = i + c.len by omega, c.periodic, hi]
  have h0 : c.vtx j ≠ .hub := by
    intro h; have := adj c j; rw [h, e1, uval_self] at this; simp at this
  have h2 : c.vtx (j + 2) ≠ .hub := by
    intro h; have := adj c (j + 1); rw [h, e1, uval_self] at this; simp at this
  rw [weight_shift c j]
  obtain ⟨m, hm⟩ : ∃ m, c.len = m + 2 := ⟨c.len - 2, by omega⟩
  rw [hm, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [add_zero, show j + (0 + 1) = j + 1 by omega, show j + (0 + 1) + 1 = j + 2 by omega,
    e1]
  rw [uGraph_w hw hW (uval_hub' h2), uGraph_w hw hW (uval_hub h0)]
  omega

/-- **Lemma 14** (disjoint case, for every heavy weight `w ≥ 1`): if `S_a ∩ S_b = ∅`, every cycle
has weight `≥ 4w`. -/
theorem weight_ge (hw : 1 ≤ w) (hW : 2 * w ≤ W) (hd : ∀ q, ¬ (x q = true ∧ y q = true)) :
    4 * w ≤ c.weight := by
  by_cases hh : ∃ i, c.vtx i = .hub
  · obtain ⟨i, hi⟩ := hh
    exact weight_ge_of_hub c hw hW hi
  push Not at hh
  have hL := c.three_le_len
  set a : ℕ → ℕ := fun t => if side (c.vtx t) = side (c.vtx (t + 1)) then 0 else 1 with ha
  set A := ∑ t ∈ range c.len, a t with hA
  have a_per : ∀ t, a (t + c.len) = a t := fun t => by
    simp only [ha, c.periodic, Nat.add_right_comm t c.len 1]
  have a_le : ∀ t, a t ≤ 1 := fun t => by simp only [ha]; split_ifs <;> omega
  -- the weight of each edge
  have hf : ∀ t, w ≤ (uGraph W w x y).w (c.vtx t) (c.vtx (t + 1)) + w * a t := fun t => by
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (adj c t)
    rw [uGraph_w hw hW hn, uval_side hn (hh t) (hh (t + 1))]
    simp only [ha]
    split_ifs <;> omega
  have hsum : c.len * w ≤ c.weight + w * A := by
    unfold WGraph.Cycle.weight
    rw [hA, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc c.len * w = ∑ t ∈ range c.len, w := by simp
      _ ≤ _ := Finset.sum_le_sum fun t _ => hf t
  -- the length is even (the graph is bipartite)
  have hlen : Even c.len := by
    have h := Finset.sum_range_sub (fun i => chi (c.vtx i)) c.len
    have e : ∀ i ∈ range c.len, chi (c.vtx (i + 1)) - chi (c.vtx i) = 1 := fun i _ => by
      rw [chi_edge (adj c i) (hh i) (hh (i + 1))]; ring
    rw [Finset.sum_congr rfl e, show c.vtx c.len = c.vtx 0 by simpa using c.periodic 0] at h
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one, sub_self] at h
    exact ZMod.natCast_eq_zero_iff_even.1 h
  -- the number of light edges is even (each one changes sides)
  have hAeven : Even A := by
    have h := Finset.sum_range_sub (fun i => side (c.vtx i)) c.len
    have key : ∀ u v : ZMod 2, u ≠ v → v - u = 1 := by decide
    have e : ∀ i ∈ range c.len, side (c.vtx (i + 1)) - side (c.vtx i) = (a i : ZMod 2) :=
      fun i _ => by
        simp only [ha]
        split_ifs with h1
        · rw [h1]; simp
        · rw [key _ _ h1]; simp
    rw [Finset.sum_congr rfl e, show c.vtx c.len = c.vtx 0 by simpa using c.periodic 0] at h
    rw [sub_self, ← Nat.cast_sum] at h
    exact ZMod.natCast_eq_zero_iff_even.1 h
  -- no two consecutive light edges (light edges form a matching)
  have hcons : ∀ t, a t + a (t + 1) ≤ 1 := fun t => by
    by_contra hcon
    have h1 : a t = 1 := by have := a_le t; have := a_le (t + 1); omega
    have h2 : a (t + 1) = 1 := by have := a_le t; have := a_le (t + 1); omega
    simp only [ha] at h1 h2
    split_ifs at h1 h2 with s1 s2
    exact ne_add_two c.periodic c.inj hL t
      (light_unique (adj c t) (adj c (t + 1)) (hh t) (hh _) (hh _) s1 s2).symm
  have h2A : 2 * A ≤ c.len := by
    have h1 : ∑ t ∈ range c.len, (a t + a (t + 1)) ≤ ∑ t ∈ range c.len, 1 :=
      Finset.sum_le_sum fun t _ => hcons t
    rw [Finset.sum_add_distrib] at h1
    have h2 : ∑ t ∈ range c.len, a (t + 1) = A := by
      rw [hA, ← sum_shift a a_per 1]; simp only [Nat.add_comm 1]
    simp only [h2, sum_const, card_range, smul_eq_mul, mul_one] at h1
    omega
  obtain ⟨l2, hl2⟩ := hlen
  obtain ⟨A2, hA2⟩ := hAeven
  rcases (show A + 4 ≤ c.len ∨ (c.len = 4 ∧ A = 2) by omega) with h | ⟨h4, hA4⟩
  · have h' : (A + 4) * w ≤ c.len * w := Nat.mul_le_mul_right _ h
    nlinarith
  · exfalso
    obtain ⟨t, ht⟩ : ∃ t, a t = 1 := by
      by_contra hne
      push Not at hne
      have : A = 0 := Finset.sum_eq_zero fun t _ => by have := a_le t; have := hne t; omega
      omega
    have per4 : ∀ s, c.vtx (s + 4) = c.vtx s := fun s => by rw [← h4]; exact c.periodic s
    have a4 : a (t + 4) = a t := by rw [← h4]; exact a_per t
    have hw4 : ∑ s ∈ range 4, a (t + s) = 2 := by
      rw [← h4, sum_shift a a_per t, ← hA, hA4]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero] at hw4
    have c1 := hcons t
    have c3 := hcons (t + 3)
    rw [show t + 3 + 1 = t + 4 by omega, a4] at c3
    have h1 : a (t + 1) = 0 := by omega
    have h3 : a (t + 3) = 0 := by omega
    have h2 : a (t + 2) = 1 := by
      have := a_le (t + 2); have := a_le (t + 1); have := a_le (t + 3); omega
    simp only [ha, show t + 1 + 1 = t + 2 by omega, show t + 2 + 1 = t + 3 by omega] at ht h1 h2
    split_ifs at ht h1 h2 with s1 s2 s3
    have h30 := adj c (t + 3)
    rw [show t + 3 + 1 = t + 4 by omega, per4] at h30
    have := adj c (t + 1)
    have := adj c (t + 2)
    rw [show t + 1 + 1 = t + 2 by omega] at *
    rw [show t + 2 + 1 = t + 3 by omega] at *
    obtain ⟨q, hq⟩ := uval_four (adj c t) ‹_› ‹_› h30 (hh _) (hh _) (hh _) (hh _) s1 s2 s3
    exact hd q hq

end uGraph

/-- **Lemma 14** (intersecting case): if `(i, j) ∈ S_a ∩ S_b`, then `ℓ_i r_i r'_j ℓ'_j` is a cycle
of weight `2w + 2`. -/
def uGraph.cycle4 (i j : Fin k) (hx : x (i, j) = true) (hy : y (i, j) = true) :
    (uGraph (p := p) W w x y).Cycle where
  len := 4
  three_le_len := by norm_num
  vtx := cyc4 (.l i) (.r i) (.r' j) (.l' j)
  periodic := cyc4_periodic _ _ _ _
  inj := cyc4_inj (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  adj := cyc4_cases (fun u v => ((uGraph W w x y).wt u v).isSome) (by simp [uGraph_isSome, uval])
    (by simp [uGraph_isSome, uval, hy]) (by simp [uGraph_isSome, uval])
    (by simp [uGraph_isSome, uval, hx])

lemma uGraph.cycle4_weight (hw : 1 ≤ w) (hW : 2 * w ≤ W) (i j : Fin k) (hx : x (i, j) = true)
    (hy : y (i, j) = true) : (uGraph.cycle4 (p := p) (W := W) (w := w) i j hx hy).weight = 2 * w + 2 := by
  unfold WGraph.Cycle.weight uGraph.cycle4
  simp only
  rw [sum_range_four_cyc4]
  rw [uGraph_w hw hW (u := .l i) (v := .r i) (n := 1) (by simp [uval]),
    uGraph_w hw hW (u := .r i) (v := .r' j) (n := w) (by simp [uval, hy]),
    uGraph_w hw hW (u := .r' j) (v := .l' j) (n := 1) (by simp [uval]),
    uGraph_w hw hW (u := .l' j) (v := .l i) (n := w) (by simp [uval, hx])]
  ring

/-- **Lemma 14**, as a statement about the minimum weight cycle. -/
theorem uGraph_mwc_le (hw : 1 ≤ w) (hW : 2 * w ≤ W) (h : ∃ q, x q = true ∧ y q = true) :
    (uGraph (p := p) W w x y).mwc ≤ 2 * w + 2 := by
  obtain ⟨⟨i, j⟩, hx, hy⟩ := h
  refine (iInf_le _ (uGraph.cycle4 i j hx hy)).trans ?_
  rw [uGraph.cycle4_weight hw hW]; norm_num

theorem uGraph_mwc_ge (hw : 1 ≤ w) (hW : 2 * w ≤ W) (h : ∀ q, ¬ (x q = true ∧ y q = true)) :
    4 * w ≤ (uGraph (p := p) W w x y).mwc := by
  refine le_iInf fun c => ?_
  exact_mod_cast uGraph.weight_ge c hw hW h

end Podc.MinWeightCycleCongest
