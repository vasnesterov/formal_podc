import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/AQT/Basic.lean

/-!
# Adversarial queuing on a path: injection patterns, `(ρ, σ)`-boundedness, excess

Basic notions of Adversarial Queuing Theory (AQT, Borodin et al., J. ACM 2001; in the form of
Miller, Patt-Shamir, Rosenbaum, PODC 2019) on the directed path `0 → 1 → ⋯ → n-1`.

* An injection pattern is a count function `A t a b`: the number of packets injected in round `t`
  at node `a` with destination `b`. Only entries with `a < b < n` are meaningful; all counting
  functions below ignore the others.
* A packet with source `a` and destination `b` *crosses* (has in its route) the buffer of node `v`
  iff `a ≤ v < b` (it has to be forwarded over the edge `(v, v+1)`).
* `cross A n v s t`: number of packets injected in rounds `[s, t)` whose route crosses `v`.
* `IsBounded A n ρ σ`: for every buffer `v` and every interval of rounds `[s, t)`,
  `cross A n v s t ≤ ρ (t - s) + σ` (Definition 2.1 of the paper).
* `excess A n ρ v t = max_{s ≤ t} (cross A n v s t - ρ (t - s))` (Definition 2.2; the term `s = t`
  makes it nonnegative). Lemma 2.3: `excess ≤ σ` and `cross A n v t (t+1) ≤ excess (t+1) - excess t + ρ`.
* `reduce A ℓ`: the `ℓ`-reduction (Definition 2.4), where all packets injected during rounds
  `[ℓ(φ-1), ℓφ)` are delivered as one batch at time `φ`. Lemma 2.5: it is `(ℓρ, σ)`-bounded.
-/

namespace Cslib.AQT

open Finset

/-- Number of packets injected during rounds `[s, t)` whose route `[a, b)` contains the buffer `v`
(only packets with `a < b < n` are counted). -/
def cross (A : ℕ → ℕ → ℕ → ℕ) (n v s t : ℕ) : ℕ :=
  ∑ u ∈ Ico s t, ∑ a ∈ range (v + 1), ∑ b ∈ Ioo v n, A u a b

/-- Definition 2.1: `A` is `(ρ, σ)`-bounded if, for every buffer `v < n` and every interval of
rounds `[s, t)`, at most `ρ (t - s) + σ` injected packets have `v` in their route. -/
def IsBounded (A : ℕ → ℕ → ℕ → ℕ) (n : ℕ) (ρ σ : ℝ) : Prop :=
  ∀ v < n, ∀ s t, s ≤ t → (cross A n v s t : ℝ) ≤ ρ * ((t : ℝ) - s) + σ

/-- Definition 2.2: the excess of buffer `v` after the injections of rounds `[0, t)`. -/
noncomputable def excess (A : ℕ → ℕ → ℕ → ℕ) (n : ℕ) (ρ : ℝ) (v t : ℕ) : ℝ :=
  (range (t + 1)).sup' nonempty_range_add_one
    (fun s => (cross A n v s t : ℝ) - ρ * ((t : ℝ) - s))

lemma cross_self (A : ℕ → ℕ → ℕ → ℕ) (n v t : ℕ) : cross A n v t t = 0 := by
  simp [cross]

lemma cross_add {A : ℕ → ℕ → ℕ → ℕ} {n v s t u : ℕ} (hst : s ≤ t) (htu : t ≤ u) :
    cross A n v s t + cross A n v t u = cross A n v s u := by
  unfold cross
  exact sum_Ico_consecutive _ hst htu

lemma excess_nonneg (A : ℕ → ℕ → ℕ → ℕ) (n : ℕ) (ρ : ℝ) (v t : ℕ) : 0 ≤ excess A n ρ v t := by
  unfold excess
  refine le_trans ?_ (le_sup' _ (mem_range.2 (Nat.lt_succ_self t)))
  simp [cross_self]

/-- Lemma 2.3 (1): the excess of a `(ρ, σ)`-bounded adversary is at most `σ`. -/
theorem excess_le {A : ℕ → ℕ → ℕ → ℕ} {n : ℕ} {ρ σ : ℝ} (hA : IsBounded A n ρ σ) {v : ℕ}
    (hv : v < n) (t : ℕ) : excess A n ρ v t ≤ σ := by
  unfold excess
  refine sup'_le _ _ fun s hs => ?_
  have := hA v hv s t (Nat.lt_succ_iff.1 (mem_range.1 hs))
  linarith

/-- Lemma 2.3 (2): the number of packets injected in round `t` that cross `v` is at most the
increase of the excess plus `ρ`. -/
theorem cross_succ_le (A : ℕ → ℕ → ℕ → ℕ) (n : ℕ) (ρ : ℝ) (v t : ℕ) :
    (cross A n v t (t + 1) : ℝ) ≤ excess A n ρ v (t + 1) - excess A n ρ v t + ρ := by
  obtain ⟨s, hs, hmax⟩ := exists_mem_eq_sup' (nonempty_range_add_one (n := t))
    (fun s => (cross A n v s t : ℝ) - ρ * ((t : ℝ) - s))
  have hst : s ≤ t := Nat.lt_succ_iff.1 (mem_range.1 hs)
  have h1 : (cross A n v s t : ℝ) - ρ * ((t : ℝ) - s) = excess A n ρ v t := by
    unfold excess; exact hmax.symm
  have h2 : (cross A n v s (t + 1) : ℝ) - ρ * (((t + 1 : ℕ) : ℝ) - s) ≤ excess A n ρ v (t + 1) := by
    unfold excess
    exact le_sup' (fun s => (cross A n v s (t + 1) : ℝ) - ρ * (((t + 1 : ℕ) : ℝ) - s))
      (mem_range.2 (by omega))
  have h3 : (cross A n v s (t + 1) : ℝ) = cross A n v s t + cross A n v t (t + 1) := by
    rw [← Nat.cast_add, cross_add hst (Nat.le_succ t)]
  push_cast at h2
  linarith

/-- Definition 2.4: the `ℓ`-reduction of `A`. Batch `φ` consists of all packets injected during
rounds `[ℓ(φ-1), ℓφ)` (batch `0` is empty); an algorithm working in phases of `ℓ` rounds accepts
batch `φ` at the beginning of phase `φ`. -/
def reduce (A : ℕ → ℕ → ℕ → ℕ) (ℓ : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  fun φ a b => ∑ u ∈ Ico (ℓ * φ - ℓ) (ℓ * φ), A u a b

lemma cross_reduce (A : ℕ → ℕ → ℕ → ℕ) (ℓ n v : ℕ) {s t : ℕ} (hst : s ≤ t) :
    cross (reduce A ℓ) n v s t = cross A n v (ℓ * s - ℓ) (ℓ * t - ℓ) := by
  induction t, hst using Nat.le_induction with
  | base => simp [cross_self]
  | succ t hst ih =>
    rw [← cross_add (A := reduce A ℓ) hst (Nat.le_succ t), ih,
      ← cross_add (A := A) (t := ℓ * t - ℓ) (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hst) _)
        (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ (Nat.le_succ t)) _)]
    congr 1
    have e : ℓ * t.succ - ℓ = ℓ * t := by rw [Nat.succ_eq_add_one, mul_add, mul_one, Nat.add_sub_cancel]
    simp only [cross, reduce, Nat.Ico_succ_singleton, sum_singleton, e]
    symm
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]

/-- Lemma 2.5: if `A` is `(ρ, σ)`-bounded then its `ℓ`-reduction is `(ℓρ, σ)`-bounded. -/
theorem reduce_isBounded {A : ℕ → ℕ → ℕ → ℕ} {n : ℕ} {ρ σ : ℝ} (hA : IsBounded A n ρ σ)
    (hρ : 0 ≤ ρ) (ℓ : ℕ) : IsBounded (reduce A ℓ) n (ℓ * ρ) σ := by
  intro v hv s t hst
  rw [cross_reduce A ℓ n v hst]
  have hle : ℓ * s - ℓ ≤ ℓ * t - ℓ := Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hst) _
  refine (hA v hv _ _ hle).trans ?_
  have : ((ℓ * t - ℓ : ℕ) : ℝ) - ((ℓ * s - ℓ : ℕ) : ℝ) ≤ ℓ * ((t : ℝ) - s) := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · have : ((ℓ * t - ℓ : ℕ) : ℝ) ≤ ℓ * t := by
        exact_mod_cast (Nat.sub_le _ _).trans (le_of_eq rfl)
      simp only [mul_zero, Nat.zero_sub, CharP.cast_eq_zero, sub_zero]
      exact this
    · rw [Nat.cast_sub (by nlinarith), Nat.cast_sub (by nlinarith)]
      push_cast; nlinarith
  nlinarith

/-! ### Topology-free excess

The same notions for an arbitrary sequence `N : ℕ → ℕ` of per-round counts (e.g. the number of
packets injected in round `t` whose route contains a fixed buffer, in any network). -/

section Seq

/-- Total count of the rounds `[s, t)`. -/
def seqCross (N : ℕ → ℕ) (s t : ℕ) : ℕ := ∑ u ∈ Ico s t, N u

/-- Excess of a count sequence after rounds `[0, t)` (Definition 2.2, topology-free). -/
noncomputable def seqExcess (N : ℕ → ℕ) (ρ : ℝ) (t : ℕ) : ℝ :=
  (range (t + 1)).sup' nonempty_range_add_one
    (fun s => (seqCross N s t : ℝ) - ρ * ((t : ℝ) - s))

lemma seqCross_self (N : ℕ → ℕ) (t : ℕ) : seqCross N t t = 0 := by
  simp [seqCross]

lemma seqCross_add {N : ℕ → ℕ} {s t u : ℕ} (hst : s ≤ t) (htu : t ≤ u) :
    seqCross N s t + seqCross N t u = seqCross N s u :=
  sum_Ico_consecutive _ hst htu

lemma seqExcess_nonneg (N : ℕ → ℕ) (ρ : ℝ) (t : ℕ) : 0 ≤ seqExcess N ρ t := by
  unfold seqExcess
  refine le_trans ?_ (le_sup' _ (mem_range.2 (Nat.lt_succ_self t)))
  simp [seqCross_self]

/-- Lemma 2.3 (1), topology-free: if every interval `[s, t)` has count at most `ρ (t - s) + σ`,
then the excess is at most `σ`. -/
theorem seqExcess_le {N : ℕ → ℕ} {ρ σ : ℝ}
    (hN : ∀ s t, s ≤ t → (seqCross N s t : ℝ) ≤ ρ * ((t : ℝ) - s) + σ) (t : ℕ) :
    seqExcess N ρ t ≤ σ := by
  unfold seqExcess
  refine sup'_le _ _ fun s hs => ?_
  have := hN s t (Nat.lt_succ_iff.1 (mem_range.1 hs))
  linarith

/-- Lemma 2.3 (2), topology-free: `N t ≤ ξ(t+1) - ξ(t) + ρ`. -/
theorem seq_le_excess_succ (N : ℕ → ℕ) (ρ : ℝ) (t : ℕ) :
    (N t : ℝ) ≤ seqExcess N ρ (t + 1) - seqExcess N ρ t + ρ := by
  obtain ⟨s, hs, hmax⟩ := exists_mem_eq_sup' (nonempty_range_add_one (n := t))
    (fun s => (seqCross N s t : ℝ) - ρ * ((t : ℝ) - s))
  have hst : s ≤ t := Nat.lt_succ_iff.1 (mem_range.1 hs)
  have h1 : (seqCross N s t : ℝ) - ρ * ((t : ℝ) - s) = seqExcess N ρ t := by
    unfold seqExcess; exact hmax.symm
  have h2 : (seqCross N s (t + 1) : ℝ) - ρ * (((t + 1 : ℕ) : ℝ) - s) ≤
      seqExcess N ρ (t + 1) := by
    unfold seqExcess
    exact le_sup' (fun s => (seqCross N s (t + 1) : ℝ) - ρ * (((t + 1 : ℕ) : ℝ) - s))
      (mem_range.2 (by omega))
  have h3 : (seqCross N s (t + 1) : ℝ) = seqCross N s t + N t := by
    rw [← seqCross_add (N := N) hst (Nat.le_succ t)]
    simp [seqCross]
  push_cast at h2
  linarith

end Seq

end Cslib.AQT
