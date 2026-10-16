import Papers.PODC2010.EdgeDominatingSets.Basic

/-!
# The gadget of the lower-bound constructions (§3–4 of the paper)

Both lower-bound graphs of Suomela (PODC 2010) are built from a `2k`-regular port-numbered graph
whose port numbering is a *2-factorisation*: for each `j < k`, ports `2j` and `2j+1` form a
2-factor, and every edge joins port `2j` of one endpoint to port `2j + 1` of the other. Such a
graph covers the one-node multigraph with loops `(·, 2j) ↔ (·, 2j+1)`.

We give the 2-factorisation in closed form. Parameters: `m`, a shift `s : ℤ/m`, and `k` with
`2k ≤ m`. Nodes: `a_x` for `x ∈ ℤ/m` and `b_y` for `y ∈ ℤ/m`, `y ≠ 0`. Writing `t^1` for `t xor 1`:

* port `t` of `a_x` leads to port `t^1` of `b_{x+s+t}` if `x + s + t ≠ 0`; otherwise to port `t^1`
  of `a_{x-1}` (`t` even) or `a_{x+1}` (`t` odd);
* port `t` of `b_y` leads to port `t^1` of `a_{y-s-t^1}`.

Factor `j` is the bipartite circulant with differences `{s + 2j, s + 2j + 1}` with the node `b_0`
removed and its two neighbours joined. For `s = 0`, `m = 2k` this is `K_{2k,2k-1}` plus a perfect
matching on the `a`-side (the graph of Theorem 1); for `s = 1`, `m = 2k+1` it is the component
`H(ℓ)` of Theorem 2 (with `c = a_0`).
-/

namespace Podc.EdgeDominatingSets

open Podc.PortNumbering Finset

namespace Gadget

/-- `fl t = t xor 1`: port `2j` is paired with port `2j + 1`. -/
def fl (t : ℕ) : ℕ := if t % 2 = 0 then t + 1 else t - 1

theorem fl_fl (t : ℕ) : fl (fl t) = t := by unfold fl; split_ifs <;> omega

theorem fl_ne (t : ℕ) : fl t ≠ t := by unfold fl; split_ifs <;> omega

theorem fl_lt {t k : ℕ} (h : t < 2 * k) : fl t < 2 * k := by unfold fl; split_ifs <;> omega

theorem fl_inj {t t' : ℕ} (h : fl t = fl t') : t = t' := by rw [← fl_fl t, h, fl_fl]

/-- Nodes of the gadget: `a_x = inl x` for `x ∈ ℤ/m`, `b_y = inr y` for `y ≠ 0`. -/
abbrev Node (m : ℕ) := ZMod m ⊕ {y : ZMod m // y ≠ 0}

variable {m : ℕ} (s : ZMod m)

/-- The port map of the gadget. -/
def gp : Node m → ℕ → Node m × ℕ
  | .inl x, t =>
    if h : x + s + t = 0 then (.inl (if t % 2 = 0 then x - 1 else x + 1), fl t)
    else (.inr ⟨x + s + t, h⟩, fl t)
  | .inr y, t => (.inl (y.1 - s - ((fl t : ℕ) : ZMod m)), fl t)

theorem gp_snd (v : Node m) (t : ℕ) : (gp s v t).2 = fl t := by
  rcases v with x | y
  · simp only [gp]; split_ifs <;> rfl
  · rfl

theorem gp_gp (v : Node m) (t : ℕ) : gp s (gp s v t).1 (gp s v t).2 = (v, t) := by
  rcases v with x | ⟨y, hy⟩
  · by_cases hz : x + s + t = 0
    · rcases Nat.mod_two_eq_zero_or_one t with h | h
      · have h1 : fl t = t + 1 := by simp [fl, h]
        have h2 : (x - 1) + s + ((t + 1 : ℕ) : ZMod m) = 0 := by
          push_cast; linear_combination hz
        push_cast at h2
        have h3 : (t + 1) % 2 ≠ 0 := by omega
        have h4 : fl (t + 1) = t := by simp [fl, h3]
        simp [gp, hz, h, h1, h2, h3, h4]
      · have h0 : 1 ≤ t := by omega
        have h1 : fl t = t - 1 := by simp [fl, h]
        have h2 : (x + 1) + s + ((t - 1 : ℕ) : ZMod m) = 0 := by
          rw [Nat.cast_sub h0]; push_cast; linear_combination hz
        have h3 : (t - 1) % 2 = 0 := by omega
        have h4 : fl (t - 1) = t := by simp [fl, h3]; omega
        simp [gp, hz, h, h1, h2, h3, h4]
    · have h2 : x + s + (t : ZMod m) - s - t = x := by ring
      simp [gp, hz, fl_fl, h2]
  · have h2 : y - s - ((fl t : ℕ) : ZMod m) + s + ((fl t : ℕ) : ZMod m) = y := by ring
    simp [gp, h2, hy, fl_fl]

theorem natCast_inj_of_lt {a b : ℕ} (ha : a < m) (hb : b < m) (h : (a : ZMod m) = b) :
    a = b := by
  have := congrArg ZMod.val h; rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at this

theorem one_ne_zero_of_two_le (h : 2 ≤ m) : (1 : ZMod m) ≠ 0 := by
  intro h1
  have := (ZMod.natCast_eq_zero_iff 1 m).1 (by simpa using h1)
  have := Nat.le_of_dvd one_pos this
  omega

theorem card_node [NeZero m] : Fintype.card (Node m) = m + (m - 1) := by
  simp [Fintype.card_subtype_compl, ZMod.card]

variable {k : ℕ}

/-- The gadget has no loops. -/
theorem gp_ne (hm : 2 * k ≤ m) {t : ℕ} (ht : t < 2 * k) (v : Node m) : (gp s v t).1 ≠ v := by
  have h1 := one_ne_zero_of_two_le (m := m) (by omega)
  rcases v with x | y
  · simp only [gp]
    split_ifs with hz h
    · intro h'
      have := Sum.inl.inj h'
      exact h1 (by linear_combination -this)
    · intro h'
      have := Sum.inl.inj h'
      exact h1 (by linear_combination this)
    · simp
  · simp [gp]

/-- The gadget has no parallel edges. -/
theorem gp_inj (hm : 2 * k ≤ m) {t t' : ℕ} (ht : t < 2 * k) (ht' : t' < 2 * k) (v : Node m)
    (h : (gp s v t).1 = (gp s v t').1) : t = t' := by
  rcases v with x | y
  · by_cases hz : x + s + t = 0 <;> by_cases hz' : x + s + t' = 0
    · exact natCast_inj_of_lt (m := m) (by omega) (by omega) (by linear_combination hz - hz')
    · simp only [gp, hz, hz', dite_true, dite_false] at h; simp at h
    · simp only [gp, hz, hz', dite_true, dite_false] at h; simp at h
    · simp only [gp, hz, hz', dite_false, Sum.inr.injEq, Subtype.mk.injEq] at h
      exact natCast_inj_of_lt (m := m) (by omega) (by omega) (by linear_combination h)
  · simp only [gp, Sum.inl.injEq] at h
    exact fl_inj (natCast_inj_of_lt (fl_lt (by omega : t < 2 * k) |>.trans_le hm)
      (fl_lt (by omega : t' < 2 * k) |>.trans_le hm) (by linear_combination -h))

/-- The edges `a_x a_{x-1}` with `x + s + t = 0`, `t` even (the matching `S` of the paper). -/
theorem gp_match {x : ZMod m} {t : ℕ} (hz : x + s + t = 0) (ht : t % 2 = 0) :
    (gp s (.inl x) t).1 = .inl (x - 1) := by
  simp [gp, hz, ht]

theorem gp_match' (j : ℕ) :
    (gp s (.inl (-s - ((2 * j : ℕ) : ZMod m))) (2 * j)).1 =
      .inl (-s - ((2 * j : ℕ) : ZMod m) - 1) :=
  gp_match s (by ring) (by omega)

/-- Every `a_x` with `(-x - s).val < 2k` is covered by the matching. -/
theorem exists_match [NeZero m] (x : ZMod m) (hx : (-x - s).val < 2 * k) :
    ∃ j < k, x = -s - ((2 * j : ℕ) : ZMod m) ∨ x = -s - ((2 * j : ℕ) : ZMod m) - 1 := by
  have ht : (((-x - s).val : ℕ) : ZMod m) = -x - s := ZMod.natCast_zmod_val _
  rcases Nat.even_or_odd' (-x - s).val with ⟨j, hj | hj⟩
  · refine ⟨j, by omega, Or.inl ?_⟩
    rw [hj] at ht
    linear_combination ht
  · refine ⟨j, by omega, Or.inr ?_⟩
    rw [hj] at ht
    push_cast at ht ⊢
    linear_combination ht

end Gadget

/-! ### A counting lemma for covering maps -/

/-- **Counting lemma for covering-map lower bounds** (variant of `card_fibre_le`). Let `f` be a
covering map from a simple graph `G` onto `H`, and `q < deg x` a port of `x` that is not a
half-loop. For any set `s` of nodes in the fibre `f⁻¹(x)`, the edges behind port `q` of the nodes of
`s` are pairwise distinct; hence any set `S` containing them has `|S| ≥ |s|`. -/
theorem card_le_of_fibre {V W : Type*} [DecidableEq V] {G : PNGraph V} (hG : G.IsSimple)
    {H : PNGraph W} {f : V → W} (hf : G.IsCovering H f) {x : W} {q : ℕ} (hq : q < H.deg x)
    (hloop : H.p x q ≠ (x, q)) (s : Finset V) (hs : ∀ v ∈ s, f v = x)
    (S : Finset (Sym2 V)) (hS : ∀ v ∈ s, G.edge v q ∈ S) : s.card ≤ S.card := by
  refine card_le_card_of_injOn (fun v => G.edge v q) (fun v hv => hS v hv) ?_
  intro v hv w hw h
  have hv' := hs v hv
  have hw' := hs w hw
  by_contra hvw
  have hqv : q < G.deg v := by rw [← hf.deg_eq, hv']; exact hq
  have hqw : q < G.deg w := by rw [← hf.deg_eq, hw']; exact hq
  obtain ⟨h1, h2⟩ := rport_eq_of_edge_eq hG hqv hqw hvw h
  apply hloop
  have := hf.p_eq v q hqv
  rw [h1, h2, hw', hv'] at this
  exact this

/-- The image of a neighbour under a covering map. -/
theorem covering_nbr {V W : Type*} {G : PNGraph V} {H : PNGraph W} {f : V → W}
    (hf : G.IsCovering H f) {v : V} {i : ℕ} (hi : i < G.deg v) :
    f (G.nbr v i) = (H.p (f v) i).1 := by
  rw [hf.p_eq v i hi]

end Podc.EdgeDominatingSets
