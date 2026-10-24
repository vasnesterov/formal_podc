import Papers.PODC2014.PlanarMDSLowerBound.Lemma1
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Main theorem: no deterministic local `(7 - ε)`-approximation of MDS on planar graphs

* `dstar W H`: the explicit dominating set `D*` of Figure 1b: the nodes `(x, y)` with
  `x + 2y ≡ 0 (mod 7)` (a perfect code of the triangular lattice: the values `x + 2y` on a closed
  neighbourhood are `x + 2y + {0, ±1, ±2, ±3}`), plus the nodes on the outer border of the grid.
  `dstar_isDominatingSet`, `card_dstar_le`: `|D*| ≤ (W/7 + 1) H + 2W + 2H`.
* `card_output_ge`: under the identifier assignment of Lemma 1 the output has at least
  `(r - ℓ)(m - 2T)²` nodes.
* `main_theorem`: for every `T` and `ε > 0` there are `W`, `H` (depending only on `T` and `ε`) such
  that every `T`-round LOCAL algorithm on the `W × H` triangulated grid with identifiers
  `{0, …, WH - 1}` that always outputs a dominating set outputs, for some identifier assignment,
  more than `7 - ε` times the size of a dominating set.
* `no_local_approx_planar`: the paper's formulation: no `T`-round LOCAL algorithm (which may know
  `n`) finds a `(7 - ε)`-approximation of a minimum dominating set in every planar graph.
-/

namespace Podc.PlanarMDSLowerBound

open Finset Cslib Cslib.SimpleGraph

/-! ### The dominating set `D*` -/

/-- `D*` (Figure 1b): the residue class `x + 2y ≡ 0 (mod 7)` plus the outer border of the grid. -/
def dstar (W H : ℕ) : Finset (GV W H) :=
  univ.filter fun p => ((p.1 : ℕ) + 2 * (p.2 : ℕ)) % 7 = 0 ∨ (p.1 : ℕ) = 0 ∨ (p.1 : ℕ) + 1 = W ∨
    (p.2 : ℕ) = 0 ∨ (p.2 : ℕ) + 1 = H

/-- `D*` dominates the grid. -/
lemma dstar_isDominatingSet (W H : ℕ) : (grid W H).IsDominatingSet (dstar W H : Set (GV W H)) := by
  intro p
  simp only [dstar, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
  simp only
  by_cases hb : x = 0 ∨ x + 1 = W ∨ y = 0 ∨ y + 1 = H
  · exact Or.inl (Or.inr hb)
  push Not at hb
  obtain ⟨h1, h2, h3, h4⟩ := hb
  -- a neighbour (or `p` itself) in the residue class
  have key : ∀ dx dy : ℤ, -1 ≤ dx → dx ≤ 1 → -1 ≤ dy → dy ≤ 1 →
      TriAdj ((x : ℤ), (y : ℤ)) ((x : ℤ) + dx, (y : ℤ) + dy) →
      (((x : ℤ) + dx) + 2 * ((y : ℤ) + dy)) % 7 = 0 →
      ∃ u : GV W H, ((u.1 : ℕ) + 2 * (u.2 : ℕ)) % 7 = 0 ∧ (grid W H).Adj (⟨x, hx⟩, ⟨y, hy⟩) u := by
    intro dx dy a1 a2 a3 a4 hadj hmod
    obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x + dx := ⟨(x + dx).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨y', hy'⟩ : ∃ y' : ℕ, (y' : ℤ) = y + dy := ⟨(y + dy).toNat, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨(⟨x', by omega⟩, ⟨y', by omega⟩), show (x' + 2 * y') % 7 = 0 by omega, ?_⟩
    rw [grid_adj]
    simp only [pt]
    rw [hx', hy']
    exact hadj
  have hr := Nat.mod_lt (x + 2 * y) (show 0 < 7 by norm_num)
  rcases (by omega : (x + 2 * y) % 7 = 0 ∨ (x + 2 * y) % 7 = 1 ∨ (x + 2 * y) % 7 = 2 ∨
      (x + 2 * y) % 7 = 3 ∨ (x + 2 * y) % 7 = 4 ∨ (x + 2 * y) % 7 = 5 ∨ (x + 2 * y) % 7 = 6) with
    h | h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  all_goals right
  · obtain ⟨u, hu, ha⟩ := key (-1) 0 (by omega) (by omega) (by omega) (by omega)
      (by simp only [TriAdj]; omega) (by omega)
    exact ⟨u, Or.inl hu, ha⟩
  · obtain ⟨u, hu, ha⟩ := key 0 (-1) (by omega) (by omega) (by omega) (by omega)
      (by simp only [TriAdj]; omega) (by omega)
    exact ⟨u, Or.inl hu, ha⟩
  · obtain ⟨u, hu, ha⟩ := key (-1) (-1) (by omega) (by omega) (by omega) (by omega)
      (by simp only [TriAdj]; omega) (by omega)
    exact ⟨u, Or.inl hu, ha⟩
  · obtain ⟨u, hu, ha⟩ := key 1 1 (by omega) (by omega) (by omega) (by omega)
      (by simp only [TriAdj]; omega) (by omega)
    exact ⟨u, Or.inl hu, ha⟩
  · obtain ⟨u, hu, ha⟩ := key 0 1 (by omega) (by omega) (by omega) (by omega)
      (by simp only [TriAdj]; omega) (by omega)
    exact ⟨u, Or.inl hu, ha⟩
  · obtain ⟨u, hu, ha⟩ := key 1 0 (by omega) (by omega) (by omega) (by omega)
      (by simp only [TriAdj]; omega) (by omega)
    exact ⟨u, Or.inl hu, ha⟩

/-- The copy of `D*` under an identifier assignment dominates the network. -/
lemma dstar_map_isDominatingSet {W H n : ℕ} (σ : GV W H ≃ Fin n) :
    (lab σ).IsDominatingSet ((dstar W H).map σ.toEmbedding : Set (Fin n)) := by
  intro u
  rcases dstar_isDominatingSet W H (σ.symm u) with h | ⟨q, hq, hadj⟩
  · left
    simp only [coe_map, Equiv.coe_toEmbedding, Set.mem_image, mem_coe]
    exact ⟨_, h, σ.apply_symm_apply u⟩
  · right
    refine ⟨σ q, ?_, ?_⟩
    · simp only [coe_map, Equiv.coe_toEmbedding, Set.mem_image, mem_coe]
      exact ⟨q, hq, rfl⟩
    · rw [lab_adj, Equiv.symm_apply_apply]; exact hadj

/-- Lines `x = c` have at most `H` nodes. -/
private lemma card_col_le {W H : ℕ} (P : ℕ → Prop) [DecidablePred P] (hP : ∀ a b, P a → P b → a = b) :
    (univ.filter fun p : GV W H => P (p.1 : ℕ)).card ≤ H := by
  calc _ ≤ (univ : Finset (Fin H)).card := by
        refine card_le_card_of_injOn (fun p => p.2) (fun _ _ => mem_univ _) ?_
        intro p hp q hq hpq
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
        exact Prod.ext (Fin.ext (hP _ _ hp hq)) hpq
    _ = H := by simp

/-- Rows `y = c` have at most `W` nodes. -/
private lemma card_row_le {W H : ℕ} (P : ℕ → Prop) [DecidablePred P] (hP : ∀ a b, P a → P b → a = b) :
    (univ.filter fun p : GV W H => P (p.2 : ℕ)).card ≤ W := by
  calc _ ≤ (univ : Finset (Fin W)).card := by
        refine card_le_card_of_injOn (fun p => p.1) (fun _ _ => mem_univ _) ?_
        intro p hp q hq hpq
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
        exact Prod.ext hpq (Fin.ext (hP _ _ hp hq))
    _ = W := by simp

/-- The residue class has at most `(W/7 + 1) H` nodes. -/
private lemma card_residue_le (W H : ℕ) :
    (univ.filter fun p : GV W H => ((p.1 : ℕ) + 2 * (p.2 : ℕ)) % 7 = 0).card ≤ (W / 7 + 1) * H := by
  calc _ ≤ (univ : Finset (Fin (W / 7 + 1) × Fin H)).card := by
        refine card_le_card_of_injOn
          (fun p => (⟨(p.1 : ℕ) / 7, Nat.lt_succ_of_le (Nat.div_le_div_right p.1.2.le)⟩, p.2))
          (fun _ _ => mem_univ _) ?_
        intro p hp q hq hpq
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
        simp only [Prod.mk.injEq, Fin.mk.injEq] at hpq
        have := Nat.div_add_mod (p.1 : ℕ) 7
        have := Nat.div_add_mod (q.1 : ℕ) 7
        have h2 : (p.2 : ℕ) = q.2 := congrArg Fin.val hpq.2
        exact Prod.ext (Fin.ext (by omega)) hpq.2
    _ = (W / 7 + 1) * H := by simp

/-- `|D*| ≤ (W/7 + 1) H + 2H + 2W`. -/
lemma card_dstar_le (W H : ℕ) : (dstar W H).card ≤ (W / 7 + 1) * H + 2 * H + 2 * W := by
  have hsub : dstar W H ⊆
      (univ.filter fun p : GV W H => ((p.1 : ℕ) + 2 * (p.2 : ℕ)) % 7 = 0) ∪
      (univ.filter fun p : GV W H => (p.1 : ℕ) = 0) ∪
      (univ.filter fun p : GV W H => (p.1 : ℕ) + 1 = W) ∪
      (univ.filter fun p : GV W H => (p.2 : ℕ) = 0) ∪
      (univ.filter fun p : GV W H => (p.2 : ℕ) + 1 = H) := by
    intro p hp
    simp only [dstar, mem_filter, mem_univ, true_and] at hp
    simp only [mem_union, mem_filter, mem_univ, true_and]
    tauto
  refine (card_le_card hsub).trans ?_
  have := card_residue_le W H
  have := card_col_le (W := W) (H := H) (fun a : ℕ => a = 0) (fun a b ha hb => ha.trans hb.symm)
  have := card_col_le (W := W) (H := H) (fun a : ℕ => a + 1 = W) (fun a b ha hb => by omega)
  have := card_row_le (W := W) (H := H) (fun a : ℕ => a = 0) (fun a b ha hb => ha.trans hb.symm)
  have := card_row_le (W := W) (H := H) (fun a : ℕ => a + 1 = H) (fun a b ha hb => by omega)
  set S1 := univ.filter fun p : GV W H => ((p.1 : ℕ) + 2 * (p.2 : ℕ)) % 7 = 0
  set S2 := univ.filter fun p : GV W H => (p.1 : ℕ) = 0
  set S3 := univ.filter fun p : GV W H => (p.1 : ℕ) + 1 = W
  set S4 := univ.filter fun p : GV W H => (p.2 : ℕ) = 0
  set S5 := univ.filter fun p : GV W H => (p.2 : ℕ) + 1 = H
  have u1 := card_union_le (S1 ∪ S2 ∪ S3 ∪ S4) S5
  have u2 := card_union_le (S1 ∪ S2 ∪ S3) S4
  have u3 := card_union_le (S1 ∪ S2) S3
  have u4 := card_union_le S1 S2
  omega

/-! ### Counting the output -/

lemma node_injective {m r : ℕ} {i a b i' a' b' : ℕ} {hi : i < r} {ha : a < m} {hb : b < m}
    {hi' : i' < r} {ha' : a' < m} {hb' : b' < m}
    (h : node (r := r) i a b hi ha hb = node i' a' b' hi' ha' hb') : i = i' ∧ a = a' ∧ b = b' := by
  have h1 := congrArg (fun p : GV (r * m) m => (p.1 : ℕ) / m) h
  have h2 := congrArg (fun p : GV (r * m) m => (p.1 : ℕ) % m) h
  have h3 := congrArg (fun p : GV (r * m) m => (p.2 : ℕ)) h
  simp only [node_div, node_mod] at h1 h2
  simp only [node] at h3
  exact ⟨h1, h2, h3⟩

/-- If all internal nodes of the blocks `i < r - ℓ` are in the output, the output has at least
`(r - ℓ)(m - 2T)²` nodes. -/
lemma card_output_ge {T m r ℓ : ℕ} (σ : GV (r * m) m ≃ Fin (r * m * m)) (O : Finset (Fin (r * m * m)))
    (hO : ∀ i (hi : i + ℓ < r) a b, T ≤ a → ∀ (ha' : a + T < m), T ≤ b → ∀ (hb' : b + T < m),
      σ (node i a b (by omega) (by omega) (by omega)) ∈ O) :
    (r - ℓ) * (m - 2 * T) * (m - 2 * T) ≤ O.card := by
  calc (r - ℓ) * (m - 2 * T) * (m - 2 * T)
      = (univ : Finset (Fin (r - ℓ) × Fin (m - 2 * T) × Fin (m - 2 * T))).card := by
        simp [Nat.mul_assoc]
    _ ≤ O.card := by
        refine card_le_card_of_injOn
          (fun t => σ (node t.1 (T + t.2.1) (T + t.2.2) (by omega) (by omega) (by omega)))
          (fun t _ => hO t.1 (by omega) _ _ (by omega) (by omega) (by omega) (by omega)) ?_
        intro t _ t' _ htt
        simp only at htt
        obtain ⟨e1, e2, e3⟩ := node_injective (σ.injective htt)
        exact Prod.ext (Fin.ext e1) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))

/-! ### The main theorem -/

/-- **Main theorem** of Hilke–Lenzen–Suomela (PODC 2014, Brief Announcement), explicit form.
For every running time `T` and every `ε > 0` there are `W`, `H` (depending only on `T` and `ε`)
such that every deterministic `T`-round LOCAL algorithm `A` that outputs a dominating set on every
copy of the `W × H` triangulated grid with unique identifiers `{0, …, WH - 1}` outputs, for some
identifier assignment `σ`, more than `7 - ε` times the size of some dominating set `D` (so more than
`(7 - ε) γ(G)`). -/
theorem main_theorem (T : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ W H : ℕ, ∀ A : SimpleGraph (Fin (W * H)) → Fin (W * H) → Bool,
      Local.IsLocal T (fun G (_ : Fin (W * H) → Unit) v => A G v) →
      (∀ σ : GV W H ≃ Fin (W * H), (lab σ).IsDominatingSet {u | A (lab σ) u = true}) →
      ∃ σ : GV W H ≃ Fin (W * H), ∃ D : Finset (Fin (W * H)), (lab σ).IsDominatingSet D ∧
        (7 - ε) * D.card < ((univ.filter fun u => A (lab σ) u = true).card : ℝ) := by
  -- parameters
  set m : ℕ := ⌈7 * (4 * T + 72) / ε⌉₊ + 2 * T + 3 with hm_def
  obtain ⟨N, hN⟩ := exists_homogeneous.{0} ((2 * T + 1) * (2 * T + 1)) (m * m)
  set ℓ := N + 1
  set r := (m + 1) * ℓ
  refine ⟨r * m, m, fun A hA hdom => ?_⟩
  obtain ⟨σ, hσ⟩ := lemma_1 (ℓ := ℓ) (N := N) (r := r) (by omega) (fun c S hS => hN c S hS)
    (by omega) A hA hdom
  refine ⟨σ, (dstar (r * m) m).map σ.toEmbedding, dstar_map_isDominatingSet σ, ?_⟩
  set O := univ.filter fun u => A (lab σ) u = true
  have hO := card_output_ge σ O (T := T) (ℓ := ℓ) (fun i hi a b ha ha' hb hb' => by
    simp only [O, mem_filter, mem_univ, true_and]
    exact hσ i hi a b ha ha' hb hb')
  have hD := card_dstar_le (r * m) m
  rw [card_map]
  -- arithmetic
  have hrl : r - ℓ = m * ℓ := by
    show (m + 1) * ℓ - ℓ = m * ℓ
    rw [Nat.add_mul, one_mul]; omega
  rw [hrl] at hO
  set s := m - 2 * T with hs
  have hms : m = s + 2 * T := by omega
  have hs3 : 3 ≤ s := by omega
  have h7D : 7 * (dstar (r * m) m).card ≤ r * m * m + 35 * r * m := by
    have h1 : 7 * (r * m / 7) ≤ r * m := Nat.mul_div_le _ _
    have h2 : m ≤ r * m := Nat.le_mul_of_pos_left _ (by positivity)
    have h3 : 7 * ((r * m / 7 + 1) * m) ≤ (r * m + 7) * m := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
    have h4 : (r * m + 7) * m = r * m * m + 7 * m := by ring
    have h5 : 7 * m ≤ 7 * (r * m) := by omega
    have h6 : 14 * m ≤ 14 * (r * m) := by omega
    nlinarith
  -- real inequalities
  have hℓpos : (0 : ℝ) < ℓ := by positivity
  have hmR : (m : ℝ) = s + 2 * T := by exact_mod_cast hms
  have hs3R : (3 : ℝ) ≤ s := by exact_mod_cast hs3
  have hOR : ((m * ℓ) * s * s : ℝ) ≤ O.card := by exact_mod_cast hO
  have hDR : 7 * ((dstar (r * m) m).card : ℝ) ≤ r * m * m + 35 * r * m := by exact_mod_cast h7D
  have hrR : (r : ℝ) = (m + 1) * ℓ := by
    show (((m + 1) * ℓ : ℕ) : ℝ) = _
    push_cast; ring
  have hDnn : (0 : ℝ) ≤ (dstar (r * m) m).card := Nat.cast_nonneg _
  have hmpos : (0 : ℝ) < m := by rw [hmR]; positivity
  have hpos : (0 : ℝ) < m * ℓ * s * s := by
    have : (0 : ℝ) < s := by linarith
    positivity
  rcases le_or_gt 7 ε with h7 | h7
  · nlinarith
  · -- `ε m ≥ 7 (4T + 72)`
    have hceil : 7 * (4 * T + 72) / ε ≤ (⌈7 * (4 * T + 72) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hmc : (m : ℝ) = ⌈7 * (4 * T + 72) / ε⌉₊ + 2 * T + 3 := by
      rw [hm_def]; push_cast; ring
    have hεm : 7 * (4 * T + 72 : ℝ) ≤ ε * m := by
      have := (div_le_iff₀ hε).1 hceil
      nlinarith
    -- reduce to `(7 - ε) (m + 1)(m + 35) < 7 s²`, after dividing by `ℓ m / 7`
    have key : (7 - ε) * ((m + 1) * (m + 35)) < 7 * (s * s) := by
      have hT : (0 : ℝ) ≤ T := by positivity
      have : (s : ℝ) * s ≥ m * m - 4 * T * m := by rw [hmR]; nlinarith
      nlinarith
    calc (7 - ε) * ((dstar (r * m) m).card : ℝ)
        = (1 - ε / 7) * (7 * (dstar (r * m) m).card) := by ring
      _ ≤ (1 - ε / 7) * (r * m * m + 35 * r * m) := by
          apply mul_le_mul_of_nonneg_left hDR; linarith
      _ = (m * ℓ / 7) * ((7 - ε) * ((m + 1) * (m + 35))) := by rw [hrR]; ring
      _ < (m * ℓ / 7) * (7 * (s * s)) := by
          apply mul_lt_mul_of_pos_left key; positivity
      _ = m * ℓ * s * s := by ring
      _ ≤ O.card := hOR

/-- **Main theorem**, in the paper's formulation: there is no deterministic local algorithm that
finds a `(7 - ε)`-approximation of a minimum dominating set on planar graphs. Here `A n` is the
algorithm run on networks with identifiers `{0, …, n - 1}` (it may depend on `n`), it runs `T`
rounds (`Cslib.Local.IsLocal T`), and planarity is witnessed by a straight-line planar drawing
(`IsStraightLinePlanar`). -/
theorem no_local_approx_planar (T : ℕ) {ε : ℝ} (hε : 0 < ε)
    (A : ∀ n, SimpleGraph (Fin n) → Fin n → Bool)
    (hA : ∀ n, Local.IsLocal T (fun G (_ : Fin n → Unit) v => A n G v)) :
    ¬ ∀ n (G : SimpleGraph (Fin n)), IsStraightLinePlanar G →
      G.IsDominatingSet {u | A n G u = true} ∧
      ∀ D : Finset (Fin n), G.IsDominatingSet D →
        ((univ.filter fun u => A n G u = true).card : ℝ) ≤ (7 - ε) * D.card := by
  intro h
  obtain ⟨W, H, hWH⟩ := main_theorem T hε
  have hplanar : ∀ σ : GV W H ≃ Fin (W * H), IsStraightLinePlanar (lab σ) := fun σ =>
    isStraightLinePlanar_comap_triangularLattice (pt_injective.comp σ.symm.injective)
  obtain ⟨σ, D, hD, hlt⟩ := hWH (A (W * H)) (hA _) (fun σ => (h _ _ (hplanar σ)).1)
  exact absurd ((h _ _ (hplanar σ)).2 D hD) (not_le.2 hlt)

/-! ### Non-vacuity -/

/-- The hypotheses of `main_theorem` and `no_local_approx_planar` are satisfiable: the `0`-round
algorithm "every node joins" is local and always outputs a dominating set. -/
example (n T : ℕ) :
    Local.IsLocal T (fun (_ : _root_.SimpleGraph (Fin n)) (_ : Fin n → Unit) (_ : Fin n) => true) ∧
      ∀ G : _root_.SimpleGraph (Fin n), G.IsDominatingSet {u | (fun _ => true) u = true} :=
  ⟨fun _ _ _ _ _ _ => rfl, fun _ _ => Or.inl rfl⟩

end Podc.PlanarMDSLowerBound
