import Papers.PODC2013.AsyncRendezvousPoly.Traj

/-!
# The trajectories `X, Q, Y, Z, A, B, K, Ω` (Definitions 3.1–3.8)

Dieudonné, Pelc, Villain, *How to meet asynchronously at polynomial cost*, PODC 2013
(arXiv:1301.7119v2), §3.1.

**The exploration procedure as a hypothesis (UXS "axiom").** Instead of Reingold's procedure we
assume an abstract family `R k v` of trajectories (`Explorer G P`) in the graph `G`:
`R k v` starts at `v`, is a walk in `G` of exactly `P k ≥ 1` edges, and traverses every edge of `G`
whenever `G` has at most `k` nodes (the paper's "integral"). This is all the rendezvous analysis
uses. The family may depend on `G` arbitrarily, so the results below hold in particular for
Reingold's port-local procedure (see `Bridge.lean`).

Lengths (`lenX`, …, `lenOm`) depend only on `P`, not on the graph or the starting node: they are
the paper's `|X(k)|`, …, `|Ω(k)|`.
-/

namespace Podc.AsyncRendezvousPoly

open Traj Finset

/-- An exploration family with step counts `P` in the graph `G` (the paper's `R(k, v)`). -/
structure Explorer {V : Type*} (G : SimpleGraph V) (P : ℕ → ℕ) where
  /-- The trajectory `R(k, v)`. -/
  R : ℕ → V → Traj V
  len_eq : ∀ k v, (R k v).len = P k
  start : ∀ k v, (R k v).f 0 = v
  walk : ∀ k v, (R k v).IsWalk G
  /-- `R(k, v)` is integral in graphs of size at most `k`. -/
  covers : ∀ [Fintype V] (k : ℕ) (v : V), Fintype.card V ≤ k → Covers G (R k v)
  /-- Every `R(k, ·)` moves (harmless: pad by back-and-forth moves). -/
  P_pos : ∀ k, 1 ≤ P k

/-! ### Lengths -/

section Lengths

variable (P : ℕ → ℕ)

/-- `|X(k)|`. -/
def lenX (k : ℕ) : ℕ := 2 * P k
/-- `|Q(k)|`. -/
def lenQ (k : ℕ) : ℕ := ∑ i ∈ range k, lenX P (i + 1)
/-- `|Y'(k)|`. -/
def lenY' (k : ℕ) : ℕ := (P k + 1) * lenQ P k + P k
/-- `|Y(k)|`. -/
def lenY (k : ℕ) : ℕ := 2 * lenY' P k
/-- `|Z(k)|`. -/
def lenZ (k : ℕ) : ℕ := ∑ i ∈ range k, lenY P (i + 1)
/-- `|A'(k)|`. -/
def lenA' (k : ℕ) : ℕ := (P k + 1) * lenZ P k + P k
/-- `|A(k)|`. -/
def lenA (k : ℕ) : ℕ := 2 * lenA' P k
/-- `|B(k)|`. -/
def lenB (k : ℕ) : ℕ := 2 * lenA P (4 * k) * lenY P k
/-- `|K(k)|`. -/
def lenK (k : ℕ) : ℕ := 2 * (lenB P (4 * k) + lenA P (8 * k)) * lenX P k
/-- `|Ω(k)|`. -/
def lenOm (k : ℕ) : ℕ := (2 * k - 1) * lenK P k * lenX P k

/-- An upper bound on the number of edge traversals in the first `N` iterations of Algorithm
RV-asynch-poly (each piece `T(k)` has at most `(2k-1)|K(k)|` edges). This is the paper's
`Π(n, m)` for `N = 2(n + l) + 1`, with correct estimates (see `differencies.md`). -/
def piBound (N : ℕ) : ℕ := ∑ t ∈ range N, ((2 * (t + 1) - 1) * lenK P (t + 1) + lenOm P (t + 1))

end Lengths

namespace Explorer

variable {V : Type*} {G : SimpleGraph V} {P : ℕ → ℕ} (E : Explorer G P)

/-- Definition 3.1: `X(k, v) = R(k, v) R̄(k, v)`. -/
def X (k : ℕ) (v : V) : Traj V := (E.R k v).dbl
/-- Definition 3.2: `Q(k, v) = X(1, v) X(2, v) … X(k, v)`. -/
def Q (k : ℕ) (v : V) : Traj V := concatFn v (fun i => E.X (i + 1) v) k
/-- Definition 3.3: `Y'(k, v₁) = Q(k, v₁)(v₁, v₂)Q(k, v₂) … (v_{s-1}, v_s)Q(k, v_s)`. -/
def Y' (k : ℕ) (v : V) : Traj V := weave (E.R k v) (E.Q k)
/-- Definition 3.3: `Y(k, v) = Y'(k, v) Ȳ'(k, v)`. -/
def Y (k : ℕ) (v : V) : Traj V := (E.Y' k v).dbl
/-- Definition 3.4: `Z(k, v) = Y(1, v) … Y(k, v)`. -/
def Z (k : ℕ) (v : V) : Traj V := concatFn v (fun i => E.Y (i + 1) v) k
/-- Definition 3.5: `A'(k, v₁) = Z(k, v₁)(v₁, v₂)Z(k, v₂) … Z(k, v_s)`. -/
def A' (k : ℕ) (v : V) : Traj V := weave (E.R k v) (E.Z k)
/-- Definition 3.5: `A(k, v) = A'(k, v) Ā'(k, v)`. -/
def A (k : ℕ) (v : V) : Traj V := (E.A' k v).dbl
/-- Definition 3.6: `B(k, v) = Y(k, v)^{2|A(4k)|}`. -/
def B (k : ℕ) (v : V) : Traj V := pow (E.Y k v) (2 * lenA P (4 * k))
/-- Definition 3.7: `K(k, v) = X(k, v)^{2(|B(4k)| + |A(8k)|)}`. -/
def K (k : ℕ) (v : V) : Traj V := pow (E.X k v) (2 * (lenB P (4 * k) + lenA P (8 * k)))
/-- Definition 3.8: `Ω(k, v) = X(k, v)^{(2k-1)|K(k)|}`. -/
def Om (k : ℕ) (v : V) : Traj V := pow (E.X k v) ((2 * k - 1) * lenK P k)

/-! ### Closedness and lengths -/

theorem X_closed (k : ℕ) (v : V) : (E.X k v).ClosedAt v := by
  have := dbl_closed (E.R k v); rwa [E.start] at this

theorem Q_closed (k : ℕ) (v : V) : (E.Q k v).ClosedAt v :=
  concatFn_closed _ (fun i => E.X_closed (i + 1) v) k

theorem Y'_f_zero (k : ℕ) (v : V) : (E.Y' k v).f 0 = v := by
  simp [Y', weave_f_zero, E.start]

theorem Y_closed (k : ℕ) (v : V) : (E.Y k v).ClosedAt v := by
  have := dbl_closed (E.Y' k v); rwa [E.Y'_f_zero] at this

theorem Z_closed (k : ℕ) (v : V) : (E.Z k v).ClosedAt v :=
  concatFn_closed _ (fun i => E.Y_closed (i + 1) v) k

theorem A'_f_zero (k : ℕ) (v : V) : (E.A' k v).f 0 = v := by
  simp [A', weave_f_zero, E.start]

theorem A_closed (k : ℕ) (v : V) : (E.A k v).ClosedAt v := by
  have := dbl_closed (E.A' k v); rwa [E.A'_f_zero] at this

theorem B_closed (k : ℕ) (v : V) : (E.B k v).ClosedAt v := pow_closed (E.Y_closed k v) _

theorem K_closed (k : ℕ) (v : V) : (E.K k v).ClosedAt v := pow_closed (E.X_closed k v) _

theorem Om_closed (k : ℕ) (v : V) : (E.Om k v).ClosedAt v := pow_closed (E.X_closed k v) _

theorem X_len (k : ℕ) (v : V) : (E.X k v).len = lenX P k := by simp [X, lenX, E.len_eq]

theorem Q_len (k : ℕ) (v : V) : (E.Q k v).len = lenQ P k := by
  simp [Q, lenQ, concatFn_len, X_len]

theorem Y'_len (k : ℕ) (v : V) : (E.Y' k v).len = lenY' P k := by
  rw [Y', weave_len _ _ (lenQ P k) (fun w => E.Q_len k w), E.len_eq]; rfl

theorem Y_len (k : ℕ) (v : V) : (E.Y k v).len = lenY P k := by simp [Y, lenY, Y'_len]

theorem Z_len (k : ℕ) (v : V) : (E.Z k v).len = lenZ P k := by
  simp [Z, lenZ, concatFn_len, Y_len]

theorem A'_len (k : ℕ) (v : V) : (E.A' k v).len = lenA' P k := by
  rw [A', weave_len _ _ (lenZ P k) (fun w => E.Z_len k w), E.len_eq]; rfl

theorem A_len (k : ℕ) (v : V) : (E.A k v).len = lenA P k := by simp [A, lenA, A'_len]

theorem B_len (k : ℕ) (v : V) : (E.B k v).len = lenB P k := by
  simp [B, lenB, pow_len, Y_len]

theorem K_len (k : ℕ) (v : V) : (E.K k v).len = lenK P k := by
  simp [K, lenK, pow_len, X_len]

theorem Om_len (k : ℕ) (v : V) : (E.Om k v).len = lenOm P k := by
  simp [Om, lenOm, pow_len, X_len]

/-! ### Walks -/

theorem X_walk (k : ℕ) (v : V) : (E.X k v).IsWalk G := (E.walk k v).dbl

theorem Q_walk (k : ℕ) (v : V) : (E.Q k v).IsWalk G :=
  IsWalk.concatFn (fun _ => v) _ (fun i => (E.X_closed (i + 1) v).1)
    (fun i => (E.X_closed (i + 1) v).2) k (fun _ _ => E.X_walk _ _)

theorem Y_walk (k : ℕ) (v : V) : (E.Y k v).IsWalk G :=
  ((E.walk k v).weave _ (E.Q_closed k) (E.Q_walk k)).dbl

theorem Z_walk (k : ℕ) (v : V) : (E.Z k v).IsWalk G :=
  IsWalk.concatFn (fun _ => v) _ (fun i => (E.Y_closed (i + 1) v).1)
    (fun i => (E.Y_closed (i + 1) v).2) k (fun _ _ => E.Y_walk _ _)

theorem A_walk (k : ℕ) (v : V) : (E.A k v).IsWalk G :=
  ((E.walk k v).weave _ (E.Z_closed k) (E.Z_walk k)).dbl

theorem B_walk (k : ℕ) (v : V) : (E.B k v).IsWalk G := IsWalk.pow (E.Y_closed k v) (E.Y_walk k v) _

theorem K_walk (k : ℕ) (v : V) : (E.K k v).IsWalk G := IsWalk.pow (E.X_closed k v) (E.X_walk k v) _

theorem Om_walk (k : ℕ) (v : V) : (E.Om k v).IsWalk G :=
  IsWalk.pow (E.X_closed k v) (E.X_walk k v) _

/-! ### Repetitions -/

theorem B_rep {k β : ℕ} {v : V} {r : ℕ → V} (h : Occ (E.B k v) r β) :
    RepOcc (E.Y' k v) (2 * lenA P (4 * k)) β r := RepOcc.of_occ h

theorem K_rep {k β : ℕ} {v : V} {r : ℕ → V} (h : Occ (E.K k v) r β) :
    RepOcc (E.R k v) (2 * (lenB P (4 * k) + lenA P (8 * k))) β r := RepOcc.of_occ h

theorem Om_rep {k β : ℕ} {v : V} {r : ℕ → V} (h : Occ (E.Om k v) r β) :
    RepOcc (E.R k v) ((2 * k - 1) * lenK P k) β r := RepOcc.of_occ h

/-! ### Integrality and visiting all nodes -/

variable [Fintype V]

theorem covers_R {k : ℕ} (hk : Fintype.card V ≤ k) (v : V) : Covers G (E.R k v) :=
  E.covers k v hk

theorem covers_Y' {k : ℕ} (hk : Fintype.card V ≤ k) (v : V) : Covers G (E.Y' k v) :=
  (E.covers k v hk).weave _ (E.Q_closed k)

/-- In a graph of size at most `k`, `R(k, v)` visits every node. -/
theorem visits (hG : G.Connected) {k : ℕ} (hk : Fintype.card V ≤ k) (v u : V) :
    ∃ i ≤ P k, (E.R k v).f i = u := by
  have hadj := E.walk 0 v 0 (by rw [E.len_eq]; exact E.P_pos 0)
  have : Nontrivial V := nontrivial_of_ne _ _ hadj.ne
  obtain ⟨w, hw⟩ := hG.preconnected.exists_adj_of_nontrivial u
  obtain ⟨i, hi, h⟩ := E.covers k v hk u w hw
  rw [E.len_eq] at hi
  rcases h with h | h
  · exact ⟨i, hi.le, h.1⟩
  · exact ⟨i + 1, hi, h.2⟩

/-! ### Contents of the atoms -/

variable (hG : G.Connected)
include hG

/-- `A(K, v)` contains `R(m, u)` for every node `u` and `1 ≤ m ≤ K`, if `K ≥ n`. -/
theorem R_in_A {K m : ℕ} (hK : Fintype.card V ≤ K) (hm1 : 1 ≤ m) (hmK : m ≤ K) (v u : V) :
    ∃ δ, OccIn (E.R m u) (E.A K v) δ := by
  obtain ⟨i, hi, rfl⟩ := E.visits hG hK v u
  set w := (E.R K v).f i
  obtain ⟨δ1, h1⟩ := occIn_weave_F (E.R K v) (E.Z K) (E.Z_closed K) (i := i) (by rw [E.len_eq]; exact hi)
  obtain ⟨δ2, h2⟩ : ∃ δ, OccIn (E.Y m w) (E.Z K w) δ := by
    have := occIn_concatFn_closed (v := w) (fun i => E.Y (i + 1) w)
      (fun i => E.Y_closed (i + 1) w) (show m - 1 < K by omega)
    rw [show m - 1 + 1 = m by omega] at this; exact ⟨_, this⟩
  obtain ⟨δ3, h3⟩ : ∃ δ, OccIn (E.Q m w) (E.Y' m w) δ := by
    have := occIn_weave_F (E.R m w) (E.Q m) (E.Q_closed m) (i := 0) (by simp)
    rwa [E.start] at this
  obtain ⟨δ4, h4⟩ : ∃ δ, OccIn (E.X m w) (E.Q m w) δ := by
    have := occIn_concatFn_closed (v := w) (fun i => E.X (i + 1) w)
      (fun i => E.X_closed (i + 1) w) (show m - 1 < m by omega)
    rw [show m - 1 + 1 = m by omega] at this; exact ⟨_, this⟩
  exact ⟨_, (occIn_append_left _ _ : OccIn (E.R m w) (E.X m w) 0).trans h4 |>.trans h3
    |>.trans (occIn_append_left _ _ : OccIn (E.Y' m w) (E.Y m w) 0) |>.trans h2 |>.trans h1
    |>.trans (occIn_append_left _ _ : OccIn (E.A' K v) (E.A K v) 0)⟩

/-- `A(K, v)` contains `Y'(m, u)` for every node `u` and `1 ≤ m ≤ K`, if `K ≥ n`. -/
theorem Y'_in_A {K m : ℕ} (hK : Fintype.card V ≤ K) (hm1 : 1 ≤ m) (hmK : m ≤ K) (v u : V) :
    ∃ δ, OccIn (E.Y' m u) (E.A K v) δ := by
  obtain ⟨i, hi, rfl⟩ := E.visits hG hK v u
  set w := (E.R K v).f i
  obtain ⟨δ1, h1⟩ := occIn_weave_F (E.R K v) (E.Z K) (E.Z_closed K) (i := i) (by rw [E.len_eq]; exact hi)
  obtain ⟨δ2, h2⟩ : ∃ δ, OccIn (E.Y m w) (E.Z K w) δ := by
    have := occIn_concatFn_closed (v := w) (fun i => E.Y (i + 1) w)
      (fun i => E.Y_closed (i + 1) w) (show m - 1 < K by omega)
    rw [show m - 1 + 1 = m by omega] at this; exact ⟨_, this⟩
  exact ⟨_, (occIn_append_left _ _ : OccIn (E.Y' m w) (E.Y m w) 0) |>.trans h2 |>.trans h1
    |>.trans (occIn_append_left _ _ : OccIn (E.A' K v) (E.A K v) 0)⟩

/-- `B(K, v)` contains `R(m, u)` for every node `u` and `1 ≤ m ≤ K`, if `K ≥ n`. -/
theorem R_in_B {K m : ℕ} (hK : Fintype.card V ≤ K) (hm1 : 1 ≤ m) (hmK : m ≤ K) (v u : V) :
    ∃ δ, OccIn (E.R m u) (E.B K v) δ := by
  obtain ⟨i, hi, rfl⟩ := E.visits hG hK v u
  set w := (E.R K v).f i
  obtain ⟨δ1, h1⟩ := occIn_weave_F (E.R K v) (E.Q K) (E.Q_closed K) (i := i) (by rw [E.len_eq]; exact hi)
  obtain ⟨δ4, h4⟩ : ∃ δ, OccIn (E.X m w) (E.Q K w) δ := by
    have := occIn_concatFn_closed (v := w) (fun i => E.X (i + 1) w)
      (fun i => E.X_closed (i + 1) w) (show m - 1 < K by omega)
    rw [show m - 1 + 1 = m by omega] at this; exact ⟨_, this⟩
  have hc : 1 ≤ 2 * lenA P (4 * K) := by
    have := E.P_pos (4 * K); simp only [lenA, lenA']; nlinarith
  exact ⟨_, (occIn_append_left _ _ : OccIn (E.R m w) (E.X m w) 0).trans h4 |>.trans h1
    |>.trans (occIn_append_left _ _ : OccIn (E.Y' K v) (E.Y K v) 0)
    |>.trans (occIn_pow (E.Y_closed K v) hc)⟩

end Explorer

end Podc.AsyncRendezvousPoly
