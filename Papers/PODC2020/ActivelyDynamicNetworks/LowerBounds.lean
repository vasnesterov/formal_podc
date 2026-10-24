import Podc.Computability.Distributed.DynamicNetworks.ActivelyDynamic
import Cslib.Foundations.Combinatorics.SimpleGraph.Ball
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Centralized lower bounds (Section 6 / Appendix D.1)

Michail–Skretas–Spirakis, *Distributed Computation and Reconfiguration in Actively Dynamic
Networks*, PODC 2020.

The Depth-`d` Tree problem asks to reconfigure the initial network into a rooted tree of depth `d`
(`IsDepthTree`). The lower bounds below hold for **every** execution of the actively dynamic model
(`Cslib.DynNet.Active.IsExec`), i.e. for any centralized strategy, started on a spanning line
`pathGraph n`. They only use that the final snapshot has all nodes within distance `d` of some
node `r` (so they hold for any target of radius `d`, tree or not).

* `lemma_6_1` (Lemma 6.1 / D.2): `n - 1 ≤ 2^(T+1) · d`, since one round at most halves distances
  and the endpoints of the line start at distance `n - 1`. Corollaries: `lemma_6_1_log`
  (`⌊log(n-1)⌋ ≤ T + 1 + ⌈log d⌉`) and `lemma_6_1_asymp` (for `d ≤ ⌊log n⌋ + 1`:
  `⌊log n⌋ ≤ 2T + 7`, i.e. `T = Ω(log n)`).
* `lemma_6_2_total` (Lemma 6.2 / D.3): `n - 1 ≤ (total activations) + 2d`, since each activated
  edge shortens a distance by at most one. No time bound is needed. With `d = O(log n)` this is
  `Ω(n)`.
* `lemma_6_2_perRound` (Lemma 6.2 / D.4): if at most `m` edges are activated per round, then
  `n - 1 ≤ T · m + 2d`; for `T = O(log n)` and `d = O(log n)`, `m = Ω(n / log n)`.
-/

namespace Podc.ActivelyDynamicNetworks

open SimpleGraph Cslib.DynNet.Active

variable {V : Type*}

/-- The target of the Depth-`d` Tree problem: `G` is a tree in which every node is within
distance `d` of the root `r` (a rooted tree of depth at most `d`). -/
def IsDepthTree (G : SimpleGraph V) (r : V) (d : ℕ) : Prop :=
  G.IsTree ∧ ∀ v, G.edist r v ≤ d

/-- In the path graph the endpoints are at distance (at least) `n - 1`. -/
theorem pathGraph_edist_ge {n : ℕ} (u v : Fin n) :
    ((v : ℕ) : ℕ∞) ≤ u + (pathGraph n).edist u v := by
  refine le_add_edist_of_lipschitz (f := fun x : Fin n => (x : ℕ)) ?_ u v
  intro x y h
  rw [pathGraph_adj] at h
  omega

/-- If all nodes are within distance `d` of `r`, any two are within distance `2d`. -/
theorem edist_le_two_mul_of_radius {G : SimpleGraph V} {r : V} {d : ℕ}
    (h : ∀ v, G.edist r v ≤ d) (u v : V) : G.edist u v ≤ 2 * d := by
  calc G.edist u v ≤ G.edist u r + G.edist r v := G.edist_triangle
    _ ≤ d + d := by rw [SimpleGraph.edist_comm]; gcongr <;> exact h _
    _ = 2 * d := by ring

/-- The distance between the endpoints of the initial line. -/
theorem edist_endpoints {n : ℕ} {E : ℕ → SimpleGraph (Fin (n + 1))} (h0 : E 0 = pathGraph (n + 1)) :
    (n : ℕ∞) ≤ (E 0).edist 0 (Fin.last n) := by
  have := pathGraph_edist_ge (n := n + 1) 0 (Fin.last n)
  rw [h0]; simpa using this

/-- **Lemma 6.1 / D.2.** Starting from a spanning line on `n` nodes, any strategy that reaches,
after `T` rounds, a network in which all nodes are within distance `d` of some node (e.g. a
rooted tree of depth `d`) satisfies `n - 1 ≤ 2^(T+1) · d`. -/
theorem lemma_6_1 {n : ℕ} {E : ℕ → SimpleGraph (Fin n)} (hE : IsExec E)
    (h0 : E 0 = pathGraph n) {T d : ℕ} {r : Fin n} (hT : ∀ v, (E T).edist r v ≤ d) :
    n - 1 ≤ 2 ^ (T + 1) * d := by
  rcases n with _ | n
  · simp
  have h1 := edist_endpoints h0
  have h2 := hE.edist_le_pow 0 (Fin.last n) T
  have h3 := edist_le_two_mul_of_radius hT 0 (Fin.last n)
  have : (n : ℕ∞) ≤ ((2 ^ (T + 1) * d : ℕ) : ℕ∞) := by
    calc (n : ℕ∞) ≤ 2 ^ T * (E T).edist 0 (Fin.last n) := h1.trans h2
      _ ≤ 2 ^ T * (2 * d) := by gcongr
      _ = ((2 ^ (T + 1) * d : ℕ) : ℕ∞) := by push_cast; ring
  simp only [add_tsub_cancel_right]
  exact_mod_cast this

/-- Lemma 6.1 in logarithmic form: `⌊log₂ (n-1)⌋ ≤ T + 1 + ⌈log₂ d⌉`. -/
theorem lemma_6_1_log {n : ℕ} {E : ℕ → SimpleGraph (Fin n)} (hE : IsExec E)
    (h0 : E 0 = pathGraph n) {T d : ℕ} {r : Fin n} (hT : ∀ v, (E T).edist r v ≤ d) :
    Nat.log 2 (n - 1) ≤ T + 1 + Nat.clog 2 d := by
  have h := lemma_6_1 hE h0 hT
  have hd : d ≤ 2 ^ Nat.clog 2 d := Nat.le_pow_clog (by norm_num) d
  have : n - 1 ≤ 2 ^ (T + 1 + Nat.clog 2 d) := by
    rw [pow_add]; exact h.trans (Nat.mul_le_mul_left _ hd)
  calc Nat.log 2 (n - 1) ≤ Nat.log 2 (2 ^ (T + 1 + Nat.clog 2 d)) := Nat.log_mono_right this
    _ = T + 1 + Nat.clog 2 d := Nat.log_pow (by norm_num) _

/-- `L + 1 ≤ 2^(L/2 + 1)`. -/
theorem succ_le_two_pow_half (L : ℕ) : L + 1 ≤ 2 ^ (L / 2 + 1) := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    rcases L with _ | _ | L
    · norm_num
    · norm_num
    · have := ih L (by omega)
      have e : (L + 2) / 2 + 1 = (L / 2 + 1) + 1 := by omega
      rw [e, pow_succ]
      have : 1 ≤ 2 ^ (L / 2 + 1) := Nat.one_le_two_pow
      omega

/-- **Lemma 6.1 / D.2, asymptotic form.** A strategy solving Depth-`log n` Tree from a spanning
line (any depth `d ≤ ⌊log₂ n⌋ + 1`) needs `T` rounds with `⌊log₂ n⌋ ≤ 2T + 7`, i.e.
`T = Ω(log n)`. -/
theorem lemma_6_1_asymp {n : ℕ} {E : ℕ → SimpleGraph (Fin n)} (hE : IsExec E)
    (h0 : E 0 = pathGraph n) {T d : ℕ} {r : Fin n} (hT : ∀ v, (E T).edist r v ≤ d)
    (hd : d ≤ Nat.log 2 n + 1) : Nat.log 2 n ≤ 2 * T + 7 := by
  have h := lemma_6_1 hE h0 hT
  set L := Nat.log 2 n with hL
  rcases Nat.eq_zero_or_pos L with hL0 | hL0
  · omega
  have hn : n ≠ 0 := by intro h; simp [h, L] at hL0
  have h2L : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn
  have h1 : 2 ^ (L - 1) ≤ n - 1 := by
    have : 2 ^ L = 2 * 2 ^ (L - 1) := by rw [← pow_succ']; congr 1; omega
    have : 1 ≤ 2 ^ (L - 1) := Nat.one_le_two_pow
    omega
  have h3 : n - 1 ≤ 2 ^ (T + 1 + (L / 2 + 1)) := by
    rw [pow_add]
    exact h.trans (Nat.mul_le_mul_left _ (hd.trans (succ_le_two_pow_half L)))
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (h1.trans h3)
  omega

/-- **Lemma 6.2 / D.3 (total activations).** Starting from a spanning line on `n` nodes, any
strategy reaching a network of radius `d` after `T` rounds activates at least `n - 1 - 2d` edges in
total: `n - 1 ≤ Σ_{i<T} |E_ac(i)| + 2d`. -/
theorem lemma_6_2_total {n : ℕ} {E : ℕ → SimpleGraph (Fin n)} (hE : IsExec E)
    (h0 : E 0 = pathGraph n) {T d : ℕ} {r : Fin n} (hT : ∀ v, (E T).edist r v ≤ d) :
    n - 1 ≤ totalActivations E T + 2 * d := by
  rcases n with _ | n
  · simp
  have h1 := edist_endpoints h0
  have h2 := hE.edist_le_add_total 0 (Fin.last n) T
  have h3 := edist_le_two_mul_of_radius hT 0 (Fin.last n)
  have : (n : ℕ∞) ≤ ((totalActivations E T + 2 * d : ℕ) : ℕ∞) := by
    calc (n : ℕ∞) ≤ (E T).edist 0 (Fin.last n) + totalActivations E T := h1.trans h2
      _ ≤ 2 * d + totalActivations E T := by gcongr
      _ = _ := by push_cast; ring
  simp only [add_tsub_cancel_right]
  exact_mod_cast this

/-- **Lemma 6.2 / D.4 (activations per round).** If every one of the first `T` rounds activates at
most `m` edges, then `n - 1 ≤ T · m + 2d`. -/
theorem lemma_6_2_perRound {n : ℕ} {E : ℕ → SimpleGraph (Fin n)} (hE : IsExec E)
    (h0 : E 0 = pathGraph n) {T d m : ℕ} {r : Fin n} (hT : ∀ v, (E T).edist r v ≤ d)
    (hm : ∀ i < T, numActivated E i ≤ m) : n - 1 ≤ T * m + 2 * d := by
  have h := lemma_6_2_total hE h0 hT
  have : totalActivations E T ≤ T * m := by
    unfold totalActivations
    calc ∑ i ∈ Finset.range T, numActivated E i ≤ ∑ _i ∈ Finset.range T, m :=
          Finset.sum_le_sum fun i hi => hm i (Finset.mem_range.1 hi)
      _ = T * m := by simp
  omega

end Podc.ActivelyDynamicNetworks
