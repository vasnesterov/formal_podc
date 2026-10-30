import Mathlib

/-!
# The asynchronous model: routes, walks chosen by the adversary, meetings

Dieudonné, Pelc, Villain, *How to meet asynchronously at polynomial cost*, PODC 2013
(arXiv:1301.7119v2), Section 1 ("The model").

* The graph is embedded so that edges are pairwise disjoint segments (the paper uses an embedding in
  `ℝ³`; any such embedding gives the same meeting relation). We use the embedding of a graph on the
  node set `V` into `V → ℝ` that sends node `v` to the basis vector `emb v` and the edge `{u, w}`
  to the segment between `emb u` and `emb w`: two such segments meet only at a common endpoint.
  `point u w c` is the point at fraction `c ∈ [0, 1]` of the way from `u` to `w`.
* A *route* is the sequence of nodes `r 0, r 1, …` visited by the agent (consecutive nodes adjacent,
  `IsRoute`). `posR r x` is the point at "progress" `x ≥ 0` along the route: `x = i + c` with
  `c ∈ [0, 1]` is the point at fraction `c` of the `i`-th edge `{r i, r (i+1)}`.
* A *walk* (chosen by the adversary) is an increasing sequence of times `τ 0 = 0 < τ 1 < …` and a
  progress function `p` such that on `[τ i, τ (i+1)]` the progress `p` is continuous, stays in
  `[i, i+1]`, and `p (τ i) = i`. This is exactly the paper's walk `f` on the route (the paper's
  `f_i : [t_i, t_{i+1}] → [v_i, v_{i+1}]` is `t ↦ point (r i) (r (i+1)) (p t - i)`): the adversary may
  stop the agent, move it back and forth inside an edge, and speed it up arbitrarily. The times may
  accumulate (we do not require `τ i → ∞`); positions are only considered at times `t ≤ τ i`.
  `τ i` is the time at which the agent completes its `i`-th edge traversal.
* Agents with routes `ra`, `rb` and walks `Wa`, `Wb` *meet* at time `t` (`Meet`) if both positions
  are defined at `t` and equal (a meeting at a node or inside an edge).
-/

namespace Podc.AsyncRendezvousPoly

open Set

/-! ### Trajectories (finite sequences of nodes) -/

-- CSLib candidate
/-- A finite trajectory: the nodes `f 0, f 1, …, f len` (values of `f` beyond `len` are
irrelevant). `len` is the number of edge traversals, the paper's `|T|`. -/
structure Traj (V : Type*) where
  /-- Number of edge traversals. -/
  len : ℕ
  /-- The `i`-th node, for `i ≤ len`. -/
  f : ℕ → V

variable {V : Type*}

/-- `T` occurs in the route `r` starting at index `α`. -/
def Occ (T : Traj V) (r : ℕ → V) (α : ℕ) : Prop := ∀ i ≤ T.len, r (α + i) = T.f i

/-- The triangle wave `0, 1, …, L, L-1, …, 1, 0, 1, …` of period `2L`: the index in `T` of the node
at position `i` of `T T̄ T T̄ …` (where `T̄` is the reverse of `T` and `|T| = L`). -/
def foldN (L i : ℕ) : ℕ := if i % (2 * L) ≤ L then i % (2 * L) else 2 * L - i % (2 * L)

theorem foldN_le (L i : ℕ) : foldN L i ≤ L := by
  unfold foldN; split_ifs with h
  · exact h
  · omega

theorem foldN_of_le {L i : ℕ} (h : i ≤ L) : foldN L i = i := by
  unfold foldN
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp at h; subst h; simp
  · rw [Nat.mod_eq_of_lt (by omega)]; simp [h]

theorem foldN_add_mul (L q i : ℕ) : foldN L (q * (2 * L) + i) = foldN L i := by
  unfold foldN; rw [Nat.mul_add_mod_self_right]

theorem foldN_mul_add {L q i : ℕ} (h : i ≤ L) : foldN L (q * (2 * L) + i) = i := by
  rw [foldN_add_mul, foldN_of_le h]

/-- Consecutive values of the triangle wave differ by one. -/
theorem foldN_succ {L : ℕ} (hL : 0 < L) (i : ℕ) :
    (i % (2 * L) < L ∧ foldN L (i + 1) = foldN L i + 1) ∨
    (L ≤ i % (2 * L) ∧ foldN L (i + 1) + 1 = foldN L i) := by
  have hm := Nat.mod_lt i (show 0 < 2 * L by omega)
  have hs : (i + 1) % (2 * L) = if i % (2 * L) + 1 < 2 * L then i % (2 * L) + 1 else 0 := by
    rw [Nat.add_mod]; split_ifs with h
    · rw [Nat.one_mod_eq_one.2 (by omega), Nat.mod_eq_of_lt h]
    · rw [Nat.one_mod_eq_one.2 (by omega), show i % (2 * L) + 1 = 2 * L by omega, Nat.mod_self]
  unfold foldN; rw [hs]
  by_cases h : i % (2 * L) < L
  · left; refine ⟨h, ?_⟩; split_ifs <;> omega
  · right; refine ⟨by omega, ?_⟩; split_ifs <;> omega

/-- Starting at index `β`, the route `r` repeats `c` times the closed trajectory `T T̄`
("keeps repeating `X(m, v)`" in the paper, for `T = R(m, v)`). -/
def RepOcc (T : Traj V) (c β : ℕ) (r : ℕ → V) : Prop :=
  ∀ i ≤ c * (2 * T.len), r (β + i) = T.f (foldN T.len i)

/-- `T` is a walk in `G`. -/
def Traj.IsWalk (G : SimpleGraph V) (T : Traj V) : Prop := ∀ i < T.len, G.Adj (T.f i) (T.f (i + 1))

/-- `T` traverses every edge of `G` (the paper's *integral* trajectory). -/
def Covers (G : SimpleGraph V) (T : Traj V) : Prop :=
  ∀ u w, G.Adj u w → ∃ i < T.len, (T.f i = u ∧ T.f (i + 1) = w) ∨ (T.f i = w ∧ T.f (i + 1) = u)

/-- A route in `G`: consecutive nodes are adjacent. -/
def IsRoute (G : SimpleGraph V) (r : ℕ → V) : Prop := ∀ i, G.Adj (r i) (r (i + 1))

/-! ### The embedding -/

variable [DecidableEq V]

/-- Node `v` is embedded as the basis vector `e_v`. -/
noncomputable def emb (v : V) : V → ℝ := Pi.single v 1

/-- The point at fraction `c` of the way from `u` to `w`. -/
noncomputable def point (u w : V) (c : ℝ) : V → ℝ := (1 - c) • emb u + c • emb w

/-- The point at progress `x ≥ 0` along the route `r`. -/
noncomputable def posR (r : ℕ → V) (x : ℝ) : V → ℝ :=
  point (r ⌊x⌋₊) (r (⌊x⌋₊ + 1)) (x - ⌊x⌋₊)

theorem point_symm (u w : V) (c : ℝ) : point u w c = point w u (1 - c) := by
  simp only [point, sub_sub_cancel]; exact add_comm _ _

theorem point_zero (u w : V) : point u w 0 = emb u := by simp [point]

theorem point_one (u w : V) : point u w 1 = emb w := by simp [point]

theorem posR_nat_add (r : ℕ → V) (i : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    posR r (i + c) = point (r i) (r (i + 1)) c := by
  rcases hc1.lt_or_eq with hc1 | rfl
  · have : ⌊(i : ℝ) + c⌋₊ = i := by
      rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
    simp [posR, this]
  · have : ⌊(i : ℝ) + 1⌋₊ = i + 1 := by exact_mod_cast Nat.floor_natCast (i + 1)
    simp only [posR, this, Nat.cast_add, Nat.cast_one, sub_self, point_zero, point_one]

theorem posR_nat (r : ℕ → V) (i : ℕ) : posR r i = emb (r i) := by
  simpa [point_zero] using posR_nat_add r i le_rfl zero_le_one

/-- Every `y ∈ [0, M]` (`M ≥ 1`) is `i + c` with `i < M` and `c ∈ [0, 1]`. -/
theorem exists_nat_add {y : ℝ} {M : ℕ} (hM : 1 ≤ M) (h0 : 0 ≤ y) (h1 : y ≤ M) :
    ∃ i < M, ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ y = i + c := by
  by_cases hy : y < M
  · refine ⟨⌊y⌋₊, ?_, y - ⌊y⌋₊, by simp [Nat.floor_le h0], ?_, by ring⟩
    · exact (Nat.floor_lt h0).2 hy
    · linarith [Nat.lt_floor_add_one y]
  · refine ⟨M - 1, by omega, 1, zero_le_one, le_rfl, ?_⟩
    have : y = M := le_antisymm h1 (not_lt.1 hy)
    rw [this, Nat.cast_sub hM]; ring

/-! ### Walks -/

-- CSLib candidate
/-- A walk of an agent on its route, chosen by the adversary (see the module docstring). -/
structure Walk where
  /-- `τ i`: the time at which the `i`-th edge traversal is completed. -/
  τ : ℕ → ℝ
  /-- The progress along the route at time `t`. -/
  p : ℝ → ℝ
  τ_zero : τ 0 = 0
  τ_mono : StrictMono τ
  p_τ : ∀ i, p (τ i) = i
  p_mem : ∀ i, ∀ t ∈ Icc (τ i) (τ (i + 1)), p t ∈ Icc (i : ℝ) (i + 1)
  cont : ∀ i, ContinuousOn p (Icc (τ i) (τ (i + 1)))

namespace Walk

variable (W : Walk)

theorem τ_nonneg (i : ℕ) : 0 ≤ W.τ i := W.τ_zero ▸ W.τ_mono.monotone (Nat.zero_le i)

theorem τ_le {i j : ℕ} (h : i ≤ j) : W.τ i ≤ W.τ j := W.τ_mono.monotone h

theorem τ_lt {i j : ℕ} (h : i < j) : W.τ i < W.τ j := W.τ_mono h

theorem le_of_τ_le {i j : ℕ} (h : W.τ i ≤ W.τ j) : i ≤ j := W.τ_mono.le_iff_le.1 h

theorem lt_of_τ_lt {i j : ℕ} (h : W.τ i < W.τ j) : i < j := W.τ_mono.lt_iff_lt.1 h

/-- A time in `[τ i, τ j]` lies in some single piece `[τ k, τ (k+1)]` with `i ≤ k < j`. -/
theorem exists_piece {i j : ℕ} (hij : i < j) {t : ℝ} (ht : t ∈ Icc (W.τ i) (W.τ j)) :
    ∃ k, i ≤ k ∧ k < j ∧ t ∈ Icc (W.τ k) (W.τ (k + 1)) := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj : i < j ∧ t ≤ W.τ j
    · obtain ⟨k, h1, h2, h3⟩ := ih hj.1 ⟨ht.1, hj.2⟩
      exact ⟨k, h1, by omega, h3⟩
    · refine ⟨j, by omega, by omega, ?_, ht.2⟩
      rcases not_and_or.1 hj with h | h
      · have : i = j := by omega
        exact this ▸ ht.1
      · exact (not_le.1 h).le

/-- The progress during `[τ i, τ j]` stays in `[i, j]`. -/
theorem p_mem_window {i j : ℕ} (hij : i ≤ j) {t : ℝ} (ht : t ∈ Icc (W.τ i) (W.τ j)) :
    W.p t ∈ Icc (i : ℝ) j := by
  rcases hij.lt_or_eq with hij | rfl
  · obtain ⟨k, h1, h2, h3⟩ := W.exists_piece hij ht
    have := W.p_mem k t h3
    refine ⟨le_trans (by exact_mod_cast h1) this.1, le_trans this.2 ?_⟩
    exact_mod_cast h2
  · have : t = W.τ i := le_antisymm ht.2 ht.1
    simp [this, W.p_τ]

theorem continuousOn_window (i j : ℕ) : ContinuousOn W.p (Icc (W.τ i) (W.τ j)) := by
  induction j with
  | zero =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [Icc_self]; exact continuousOn_singleton _ _
    · rw [Icc_eq_empty (not_le.2 (W.τ_lt hi))]; exact continuousOn_empty _
  | succ j ih =>
    by_cases hij : i ≤ j
    · have h := ih.union_of_isClosed (W.cont j) isClosed_Icc isClosed_Icc
      rwa [Icc_union_Icc_eq_Icc (W.τ_le hij) (W.τ_le (Nat.le_succ j))] at h
    · rcases (show i = j + 1 ∨ j + 1 < i by omega) with rfl | hi
      · simp only [Icc_self]; exact continuousOn_singleton _ _
      · rw [Icc_eq_empty (not_le.2 (W.τ_lt hi))]; exact continuousOn_empty _

end Walk

-- CSLib candidate
/-- Agents with routes `ra`, `rb` walking `Wa`, `Wb` meet at time `t`. -/
def Meet (ra rb : ℕ → V) (Wa Wb : Walk) (t : ℝ) : Prop :=
  0 ≤ t ∧ (∃ i, t ≤ Wa.τ i) ∧ (∃ j, t ≤ Wb.τ j) ∧ posR ra (Wa.p t) = posR rb (Wb.p t)

theorem Meet.symm {ra rb : ℕ → V} {Wa Wb : Walk} {t : ℝ} (h : Meet ra rb Wa Wb t) :
    Meet rb ra Wb Wa t := ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.symm⟩

end Podc.AsyncRendezvousPoly
