import Papers.PODC2024.MinWeightCycleCongest.Defs

/-!
# The directed lower-bound graph (Lemma 13 of the companion paper)

The PODC paper defers the proof of Theorem 1.2.A to its full version (arXiv:2308.08670), which in
turn refers to Manoharan–Ramachandran, *Near Optimal Bounds for Replacement Paths and Related
Problems in the CONGEST Model* (arXiv:2205.14797v2, §3.1.1, Figure 4, Lemma 13).

Vertices: `ℓ_i, ℓ'_i, r_i, r'_i` (`i < k`), plus — our addition, needed for the "constant
diameter" claim — a sink `hub` with an arc from every other vertex, and `p` padding vertices
`pad_j` (so that every `n ≥ 1` is realised as `n = 4k + 1 + p`).
Arcs: `ℓ_i → r_i`, `r'_i → ℓ'_i`; `ℓ'_j → ℓ_i` iff `x (i, j)` (Alice's set contains the pair
`(i, j)`, the paper's `S_a[(i-1)k + j] = 1`); `r_i → r'_j` iff `y (i, j)`; `v → hub` for `v ≠ hub`.
All arcs have weight `1`.

Lemma 13: if the sets intersect there is a directed `4`-cycle; otherwise every directed cycle has
length `≥ 8` (`dGraph_len_ge_eight`). The hub and the pads lie on no cycle.
-/

namespace Podc.MinWeightCycleCongest

open Finset

/-- Vertices of the lower-bound graphs (directed and undirected). -/
inductive Vtx (k p : ℕ) where
  | l (i : Fin k)
  | l' (i : Fin k)
  | r (i : Fin k)
  | r' (i : Fin k)
  | hub
  | pad (j : Fin p)
  deriving DecidableEq, Fintype

namespace Vtx

variable {k p : ℕ}

/-- `Vtx k p` as a sum type. -/
def equivSum : Vtx k p ≃ (Fin k ⊕ Fin k ⊕ Fin k ⊕ Fin k) ⊕ (Unit ⊕ Fin p) where
  toFun
    | .l i => .inl (.inl i)
    | .l' i => .inl (.inr (.inl i))
    | .r i => .inl (.inr (.inr (.inl i)))
    | .r' i => .inl (.inr (.inr (.inr i)))
    | .hub => .inr (.inl ())
    | .pad j => .inr (.inr j)
  invFun
    | .inl (.inl i) => .l i
    | .inl (.inr (.inl i)) => .l' i
    | .inl (.inr (.inr (.inl i))) => .r i
    | .inl (.inr (.inr (.inr i))) => .r' i
    | .inr (.inl ()) => .hub
    | .inr (.inr j) => .pad j
  left_inv v := by cases v <;> rfl
  right_inv s := by rcases s with (_ | _ | _ | _) | (⟨⟩ | _) <;> rfl

/-- The lower-bound graphs have `n = 4k + 1 + p` vertices. -/
lemma card : Fintype.card (Vtx k p) = 4 * k + 1 + p := by
  rw [Fintype.card_congr equivSum]
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  ring

end Vtx

open Vtx

variable {k p : ℕ}

/-- Arcs of the directed lower-bound graph for Alice's input `x` and Bob's input `y`. -/
def darc (x y : Fin k × Fin k → Bool) : Vtx k p → Vtx k p → Prop
  | .l i, .r j => i = j
  | .r i, .r' j => y (i, j) = true
  | .r' i, .l' j => i = j
  | .l' j, .l i => x (i, j) = true
  | .hub, _ => False
  | _, .hub => True
  | _, _ => False

instance (x y : Fin k × Fin k → Bool) : DecidableRel (darc (p := p) x y) := fun u v => by
  cases u <;> cases v <;> unfold darc <;> infer_instance

/-- The directed lower-bound graph `G_{x,y}` (all arc weights `1`). -/
def dGraph (W : ℕ) (x y : Fin k × Fin k → Bool) : WDigraph (Vtx k p) (W + 1) where
  wt u v := if darc x y u v then some 1 else none

variable {W : ℕ} {x y : Fin k × Fin k → Bool}

lemma dGraph_isSome {u v : Vtx k p} : ((dGraph W x y).wt u v).isSome ↔ darc x y u v := by
  simp only [dGraph]; split_ifs with h <;> simp [h]

lemma dGraph_w {u v : Vtx k p} (h : darc x y u v) : (dGraph W x y).w u v = 1 := by
  simp [WDigraph.w, dGraph, h]

lemma dGraph_unweighted : (dGraph (p := p) W x y).Unweighted := by
  intro u v c h
  simp only [dGraph] at h
  split_ifs at h with h'
  cases h
  simp

lemma not_darc_hub (v : Vtx k p) : ¬ darc x y .hub v := by cases v <;> simp [darc]

lemma not_darc_pad (u : Vtx k p) (j : Fin p) : ¬ darc x y u (.pad j) := by
  cases u <;> simp [darc]

lemma darc_hub {v : Vtx k p} (hv : v ≠ .hub) : darc x y v .hub := by
  cases v <;> simp_all [darc]

/-- Levels modulo `4`: every arc between non-hub vertices goes one level up. -/
def lvl : Vtx k p → ZMod 4
  | .l _ => 0
  | .r _ => 1
  | .r' _ => 2
  | .l' _ => 3
  | .hub => 0
  | .pad _ => 0

lemma lvl_arc {u v : Vtx k p} (h : darc x y u v) (hv : v ≠ .hub) : lvl v = lvl u + 1 := by
  cases u <;> cases v <;> simp_all [darc, lvl] <;> decide

/-- Four consecutive arcs closing up force an element of `S_a ∩ S_b` (the case `len = 4` of
Lemma 13). -/
lemma darc_four {u₀ u₁ u₂ u₃ : Vtx k p} (h01 : darc x y u₀ u₁) (h12 : darc x y u₁ u₂)
    (h23 : darc x y u₂ u₃) (h30 : darc x y u₃ u₀) (h1 : u₁ ≠ .hub) (h2 : u₂ ≠ .hub)
    (h3 : u₃ ≠ .hub) (h0 : u₀ ≠ .hub) : ∃ q, x q = true ∧ y q = true := by
  cases u₀ <;> cases u₁ <;> simp only [darc, ne_eq, not_true_eq_false] at h01 h0 h1 <;>
    cases u₂ <;> simp only [darc, ne_eq, not_true_eq_false] at h12 h2 <;>
    cases u₃ <;> simp only [darc, ne_eq] at h23 h30 h3 <;>
    subst_vars <;> exact ⟨_, ‹_›, ‹_›⟩

namespace dGraph

variable (c : (dGraph (p := p) W x y).Cycle)

lemma arc (i : ℕ) : darc x y (c.vtx i) (c.vtx (i + 1)) := dGraph_isSome.1 (c.arc i)

lemma ne_hub (i : ℕ) : c.vtx i ≠ .hub := fun h => not_darc_hub _ (h ▸ arc c i)

lemma ne_pad (i : ℕ) (j : Fin p) : c.vtx i ≠ .pad j := by
  intro h
  have h1 := arc c (i + c.len - 1)
  rw [show i + c.len - 1 + 1 = i + c.len by have := c.two_le_len; omega, c.periodic, h] at h1
  exact not_darc_pad _ _ h1

/-- An unweighted cycle has weight equal to its length. -/
lemma weight_eq : c.weight = c.len := by
  unfold WDigraph.Cycle.weight
  rw [Finset.sum_congr rfl fun i _ => dGraph_w (arc c i)]
  simp

/-- Every directed cycle has length divisible by `4`. -/
lemma four_dvd_len : 4 ∣ c.len := by
  have h := Finset.sum_range_sub (fun i => lvl (c.vtx i)) c.len
  have e : ∀ i ∈ range c.len, lvl (c.vtx (i + 1)) - lvl (c.vtx i) = 1 := fun i _ => by
    rw [lvl_arc (arc c i) (ne_hub c _)]; ring
  rw [Finset.sum_congr rfl e, show c.vtx c.len = c.vtx 0 by simpa using c.periodic 0] at h
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one, sub_self] at h
  exact (ZMod.natCast_eq_zero_iff _ _).1 h

/-- **Lemma 13** (disjoint case): if `S_a ∩ S_b = ∅`, every directed cycle has length `≥ 8`. -/
theorem len_ge_eight (hd : ∀ q, ¬ (x q = true ∧ y q = true)) : 8 ≤ c.len := by
  obtain ⟨m, hm⟩ := four_dvd_len c
  have h2 := c.two_le_len
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hm1 : m = 1 := by omega
    subst hm1
    have h4 : c.vtx (0 + 4) = c.vtx 0 := by rw [show 4 = c.len by omega]; exact c.periodic 0
    have := darc_four (arc c 0) (arc c 1) (arc c 2) (h4 ▸ arc c 3) (ne_hub c 1) (ne_hub c 2)
      (ne_hub c 3) (ne_hub c 0)
    obtain ⟨q, hq⟩ := this
    exact absurd hq (hd q)
  · omega

end dGraph

/-- **Lemma 13** (intersecting case): if `(i, j) ∈ S_a ∩ S_b`, then `ℓ_i → r_i → r'_j → ℓ'_j → ℓ_i`
is a directed cycle of length (= weight) `4`. -/
def dGraph.cycle4 (i j : Fin k) (hx : x (i, j) = true) (hy : y (i, j) = true) :
    (dGraph (p := p) W x y).Cycle where
  len := 4
  two_le_len := by norm_num
  vtx := cyc4 (.l i) (.r i) (.r' j) (.l' j)
  periodic := cyc4_periodic _ _ _ _
  inj := cyc4_inj (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  arc := cyc4_cases (fun u v => ((dGraph W x y).wt u v).isSome) (by simp [dGraph_isSome, darc])
    (by simp [dGraph_isSome, darc, hy]) (by simp [dGraph_isSome, darc])
    (by simp [dGraph_isSome, darc, hx])

lemma dGraph.cycle4_weight (i j : Fin k) (hx : x (i, j) = true) (hy : y (i, j) = true) :
    (dGraph.cycle4 (p := p) (W := W) i j hx hy).weight = 4 := by
  rw [dGraph.weight_eq]; rfl

/-- **Lemma 13**, as a statement about the minimum weight cycle: `MWC(G_{x,y}) ≤ 4` if the sets
intersect, and `MWC(G_{x,y}) ≥ 8` otherwise. -/
theorem dGraph_mwc_le (h : ∃ q, x q = true ∧ y q = true) : (dGraph (p := p) W x y).mwc ≤ 4 := by
  obtain ⟨⟨i, j⟩, hx, hy⟩ := h
  refine (iInf_le _ (dGraph.cycle4 i j hx hy)).trans ?_
  rw [dGraph.cycle4_weight]; norm_num

theorem dGraph_mwc_ge (h : ∀ q, ¬ (x q = true ∧ y q = true)) :
    8 ≤ (dGraph (p := p) W x y).mwc := by
  refine le_iInf fun c => ?_
  rw [dGraph.weight_eq]
  exact_mod_cast dGraph.len_ge_eight c h

end Podc.MinWeightCycleCongest
