import Mathlib

/-!
# Uniform deployment of mobile agents in asynchronous rings — basic definitions

Definitions shared by the formalization of
[M. Shibata, T. Mega, F. Ooshita, H. Kakugawa, T. Masuzawa, *Uniform deployment of mobile agents
in asynchronous rings*, PODC 2016; JPDC 119 (2018)].

* `IsUniform n k occ` : the agents (node `v` holds `occ v` of them, `k` in total) are uniformly
  deployed in the ring `ZMod n`: all at distinct nodes, and the distance from every agent to the
  next agent (in the forward direction) is `⌊n/k⌋` or `⌈n/k⌉` (Section 2.2).
* `gap H h`, `next H h`, `distSeq H h` : for a set `H` of home nodes, the distance from `h` to the
  next home node, that next home node, and the distance sequence `D(h)` observed by the agent
  whose home is `h` (Section 2.1).
* `rank D`, `period D`, `offset`, `moves1 D` : the local computation of Algorithm 1 (with the
  extension of Section 3.1.1 to `n ≠ ck`).
* `FourRep w m`, `est w` : the estimation rule of Algorithm 4 (the agent stops when the observed
  distance sequence is a fourth power `S⁴` with `|S| = m`).
-/

namespace Podc.UniformDeploymentRings

/-! ### Uniform deployment -/

/-- Uniform deployment (Section 2.2): node `v` holds `occ v` agents, `k` agents in total; all
agents are at distinct nodes and the distance from every agent to the next one is `⌊n/k⌋` or
`⌈n/k⌉`. -/
def IsUniform (n k : ℕ) (occ : ZMod n → ℕ) : Prop :=
  (∀ v, occ v ≤ 1) ∧
    ∀ v, occ v ≠ 0 → ∃ d : ℕ, (d = n / k ∨ d = (n + k - 1) / k) ∧ 0 < d ∧
      occ (v + d) ≠ 0 ∧ ∀ e : ℕ, 0 < e → e < d → occ (v + e) = 0

/-- Uniform deployment of a set `P` of occupied nodes. -/
def IsUniformSet (n k : ℕ) (P : Finset (ZMod n)) : Prop :=
  IsUniform n k fun v => if v ∈ P then 1 else 0

/-! ### Home nodes and distance sequences -/

variable {n : ℕ}

/-- The distance from `h` to the next node of `H` (in the forward direction); it is `n` if `h` is
the only node of `H`. -/
def gap (H : Finset (ZMod n)) (h : ZMod n) : ℕ :=
  Nat.find (⟨max n 1, by omega, Or.inr (le_max_left _ _)⟩ :
    ∃ d : ℕ, 0 < d ∧ (h + (d : ZMod n) ∈ H ∨ n ≤ d))

/-- The next node of `H` after `h`. -/
def next (H : Finset (ZMod n)) (h : ZMod n) : ZMod n := h + (gap H h : ZMod n)

/-- The distance sequence `D(h) = (d₀, …, d_{k-1})` observed by the agent with home `h`: `dⱼ` is
the distance from the `j`-th to the `(j+1)`-th home node after `h` (`h` itself being the `0`-th). -/
def distSeq (H : Finset (ZMod n)) (h : ZMod n) : List ℕ :=
  (List.range H.card).map fun j => gap H ((next H)^[j] h)

/-! ### Local computation of Algorithm 1 -/

/-- `x` is a rotation index of `D` giving the lexicographically minimum rotation `D_min`. -/
def IsMinRot (D : List ℕ) (x : ℕ) : Prop := ∀ y < D.length, D.rotate x ≤ D.rotate y

instance (D : List ℕ) (x : ℕ) : Decidable (IsMinRot D x) := by
  unfold IsMinRot; infer_instance

theorem exists_isMinRot (D : List ℕ) : ∃ x, IsMinRot D x := by
  rcases eq_or_ne D [] with rfl | hD
  · exact ⟨0, fun y hy => by simp at hy⟩
  · obtain ⟨y₀, hy₀, hmin⟩ := (Finset.range D.length).exists_min_image (fun y => D.rotate y)
      (by simpa using hD)
    exact ⟨y₀, fun y hy => hmin y (by simpa using hy)⟩

/-- `rank = min{x ≥ 0 | shift(D, x) = D_min}` (Algorithm 1, line 14). -/
def rank (D : List ℕ) : ℕ := Nat.find (exists_isMinRot D)

/-- The minimal period of `D` up to rotation: the least `p > 0` with `shift(D, p) = D`. -/
def period (D : List ℕ) : ℕ :=
  Nat.find (⟨max D.length 1, by omega, by
    rcases Nat.eq_zero_or_pos D.length with h | h
    · simp [List.length_eq_zero_iff.mp h]
    · rw [max_eq_left h]; exact List.rotate_length D⟩ : ∃ p, 0 < p ∧ D.rotate p = D)

/-- Position of the `x`-th target node after a base node, when a segment of length `N` between
two consecutive base nodes contains `p` target nodes: the first `N % p` intervals have length
`⌈N/p⌉` and the others `⌊N/p⌋` (Section 3.1.1). For `p ∣ N` this is `x * (N / p)`. -/
def offset (x N p : ℕ) : ℕ := x * (N / p) + min x (N % p)

/-- The number of moves of an agent of Algorithm 1 in its deployment phase, computed from its
distance sequence `D`: `disBase` (to reach its base node) plus the offset of its target. -/
def moves1 (D : List ℕ) : ℕ :=
  (D.take (rank D)).sum + offset (rank D) ((D.take (period D)).sum) (period D)

/-! ### Estimation of Algorithm 4 -/

/-- The prefix of length `4m` of the infinite sequence `w` is `(w₀, …, w_{m-1})⁴`. -/
def FourRep (w : ℕ → ℕ) (m : ℕ) : Prop := ∀ x < 3 * m, w (x + m) = w x

instance (w : ℕ → ℕ) (m : ℕ) : Decidable (FourRep w m) := by
  unfold FourRep; infer_instance

/-- The estimated number of tokens `k'` of Algorithm 4: the least `m > 0` such that the observed
distance sequence starts with a fourth power of length `4m` (`0` if there is none). -/
noncomputable def est (w : ℕ → ℕ) : ℕ :=
  open Classical in if h : ∃ m, 0 < m ∧ FourRep w m then Nat.find h else 0

end Podc.UniformDeploymentRings
