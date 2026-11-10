import Papers.PODC2010.KShotRadioBroadcast.UpperBoundSchedule
import Papers.PODC2010.KShotRadioBroadcast.UpperBoundProgress

/-!
# Theorem 4.3: Oblivious k-Shot broadcasts in `O(n²/k)` steps

Main results:
* `obliviousKShot_complete`: for every prime `p` with `n ≤ p²`, every `k ≥ 3` and every directed
  network in which all nodes are reachable from the source, *Oblivious k-Shot* completes
  broadcasting within `2(2n - 1)` stages, i.e. `2(2n - 1) · p (⌈p/(k-2)⌉ + 1)` steps;
* `theorem_4_3`: with `p` the smallest prime `≥ ⌈√n⌉` and `3 ≤ k ≤ √n`, this is at most
  `80 n² / k` steps;
* `theorem_4_3_large_k`: for `k > √n` (and `k ≥ 3`) it is at most `32 n ⌊√n⌋` steps
  (the paper's `O(n^{3/2})` corollary; no need to run the algorithm with `⌊√n⌋` shots);
* `obliviousKShot_correctOnUndirected`: hence the algorithm is a correct broadcasting protocol;
* `roundRobin_complete`: for `k ∈ {1, 2}` (not covered by the paper's algorithm, as
  `⌈p/(k-2)⌉` is undefined) plain Round-Robin completes within `2(2n - 1) n ≤ 4n²` steps.
-/

namespace Podc.KShotRadioBroadcast

open Finset

/-- **Theorem 4.3 (exact form).** Let `p` be a prime with `n ≤ p²` and `k ≥ 3`. On every directed
network on the nodes `Fin n` in which every node is reachable from the source `s`, the `k`-shot
oblivious algorithm *Oblivious k-Shot* completes broadcasting within `2(2n - 1)` stages of
`p (K + 1)` steps each, `K = ⌈p / (k - 2)⌉`. -/
theorem obliviousKShot_complete {n p k : ℕ} (hp : p.Prime) (hn : n ≤ p * p) (hk : 3 ≤ k)
    (E : Fin n → Fin n → Prop) (s : Fin n) (hreach : ∀ v, Relation.ReflTransGen E s v) :
    Complete (obliviousKShot n p k) k E s (2 * (2 * n - 1) * (p * (numRR p k + 1))) := by
  have hp0 := hp.pos
  have hK := one_le_numRR hp0 hk
  have hS : 0 < p * (numRR p k + 1) := Nat.mul_pos hp0 (Nat.succ_pos _)
  have hlone : ∀ (v : Fin n) (r : ℕ), ∃ t, TransmitsAt (obliviousKShot n p k) k r v t ∧
      obliviousKShot n p k t = {v} ∧
      t ≤ (r / (p * (numRR p k + 1)) + p + 1) * (p * (numRR p k + 1)) := by
    intro v r
    have hc : p ≤ min (k - 2) p * numRR p k := by
      rcases le_total (k - 2) p with h | h
      · rw [min_eq_left h]; exact le_mul_numRR hk
      · rw [min_eq_right h]; exact Nat.le_mul_of_pos_right p hK
    obtain ⟨t, h1, h2, h3⟩ := exists_lone_transmission hp0 hn hK (k := k) hc (by omega) v r
    exact ⟨t, h1, h2, h3.trans (Nat.mul_le_mul_right _ (by omega))⟩
  have := complete_of_stages (p := p) hS hlone (lineRR_appears hp0)
    (fun t t' u v ht htt hst hu hv hu' hv' => lineRR_common_le_one hp hn ht htt hst hu hv hu' hv')
    hreach
  simpa using this

/-! ## Explicit bounds -/

/-- Some prime `p` has `n ≤ p²`. -/
theorem exists_prime_sq_ge (n : ℕ) : ∃ p, p.Prime ∧ n ≤ p * p := by
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
  exact ⟨p, hp, hnp.trans (Nat.le_mul_self p)⟩

/-- The smallest prime `p ≥ ⌈√n⌉`, i.e. the smallest prime with `n ≤ p²` (the paper's choice). -/
noncomputable def smallestPrime (n : ℕ) : ℕ := Nat.find (exists_prime_sq_ge n)

theorem smallestPrime_prime (n : ℕ) : (smallestPrime n).Prime :=
  (Nat.find_spec (exists_prime_sq_ge n)).1

theorem le_smallestPrime_sq (n : ℕ) : n ≤ smallestPrime n * smallestPrime n :=
  (Nat.find_spec (exists_prime_sq_ge n)).2

theorem smallestPrime_le {n q : ℕ} (hq : q.Prime) (hnq : n ≤ q * q) : smallestPrime n ≤ q :=
  Nat.find_min' (exists_prime_sq_ge n) ⟨hq, hnq⟩

/-- Bertrand's postulate: `p ≤ 2 ⌊√n⌋` for `n ≥ 1`. -/
theorem smallestPrime_le_two_sqrt {n : ℕ} (hn : 1 ≤ n) : smallestPrime n ≤ 2 * Nat.sqrt n := by
  have hs : Nat.sqrt n ≠ 0 := by
    have := Nat.sqrt_pos.2 hn; omega
  obtain ⟨q, hq, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (Nat.sqrt n) hs
  refine (smallestPrime_le hq ?_).trans h2
  have := Nat.lt_succ_sqrt n
  have := Nat.mul_self_le_mul_self h1
  omega

theorem smallestPrime_sq_le {n : ℕ} (hn : 1 ≤ n) :
    smallestPrime n * smallestPrime n ≤ 4 * n := by
  have h := smallestPrime_le_two_sqrt hn
  have h1 := Nat.mul_self_le_mul_self h
  have h2 := Nat.sqrt_le n
  nlinarith

/-- `k (K + 1) ≤ 5 p` for `3 ≤ k ≤ p`. -/
theorem mul_numRR_succ_le {p k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p) : k * (numRR p k + 1) ≤ 5 * p := by
  have h1 : (k - 2) * numRR p k ≤ p + k - 3 := Nat.mul_div_le (p + k - 3) (k - 2)
  have h2 := numRR_le (p := p) hk
  have : k * (numRR p k + 1) = (k - 2) * numRR p k + 2 * numRR p k + k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  omega

/-- **Theorem 4.3.** For `3 ≤ k ≤ √n`, *Oblivious k-Shot* (with `p` the smallest prime
`≥ ⌈√n⌉`) completes `k`-shot broadcasting on every directed network in which all nodes are
reachable from the source within `T` steps, `k T ≤ 80 n²`, i.e. in `O(n² / k)` steps. -/
theorem theorem_4_3 {n k : ℕ} (hk : 3 ≤ k) (hkn : k * k ≤ n) (E : Fin n → Fin n → Prop)
    (s : Fin n) (hreach : ∀ v, Relation.ReflTransGen E s v) :
    ∃ T, k * T ≤ 80 * n * n ∧ Complete (obliviousKShot n (smallestPrime n) k) k E s T := by
  set p := smallestPrime n with hpdef
  have hn1 : 1 ≤ n := by have := s.isLt; omega
  refine ⟨_, ?_, obliviousKShot_complete (smallestPrime_prime n) (le_smallestPrime_sq n) hk E s
    hreach⟩
  rw [← hpdef]
  have hkp : k ≤ p := Nat.mul_self_le_mul_self_iff.1 (hkn.trans (le_smallestPrime_sq n))
  have h1 := mul_numRR_succ_le hk hkp
  have h2 := smallestPrime_sq_le hn1
  rw [← hpdef] at h2
  calc k * (2 * (2 * n - 1) * (p * (numRR p k + 1)))
      = 2 * (2 * n - 1) * p * (k * (numRR p k + 1)) := by ring
    _ ≤ 2 * (2 * n) * p * (5 * p) := by gcongr; omega
    _ = 20 * n * (p * p) := by ring
    _ ≤ 20 * n * (4 * n) := by gcongr
    _ = 80 * n * n := by ring

/-- `K ≤ 3` when `k > √n` (and `k ≥ 3`). -/
theorem numRR_le_three {n k : ℕ} (hk : 3 ≤ k) (hkn : n < k * k) :
    numRR (smallestPrime n) k ≤ 3 := by
  have hp3 : smallestPrime n ≤ 3 * (k - 2) := by
    rcases le_or_gt (Nat.sqrt n) 2 with hs | hs
    · have h1 : n ≤ 3 * 3 := by
        have : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
        have := Nat.mul_self_le_mul_self (show Nat.sqrt n + 1 ≤ 3 by omega)
        omega
      have := smallestPrime_le Nat.prime_three h1
      omega
    · have hn1 : 1 ≤ n := by
        have := Nat.sqrt_le n
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp at hs
        · exact h
      have h1 := smallestPrime_le_two_sqrt hn1
      have h2 : Nat.sqrt n < k := Nat.sqrt_lt.2 hkn
      omega
  unfold numRR
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  omega

/-- **Theorem 4.3, case `k > √n`.** For `k ≥ 3` with `k > √n`, *Oblivious k-Shot* completes
broadcasting within `32 n ⌊√n⌋ = O(n^{3/2})` steps. -/
theorem theorem_4_3_large_k {n k : ℕ} (hk : 3 ≤ k) (hkn : n < k * k) (E : Fin n → Fin n → Prop)
    (s : Fin n) (hreach : ∀ v, Relation.ReflTransGen E s v) :
    ∃ T, T ≤ 32 * n * Nat.sqrt n ∧ Complete (obliviousKShot n (smallestPrime n) k) k E s T := by
  set p := smallestPrime n with hpdef
  have hn1 : 1 ≤ n := by have := s.isLt; omega
  refine ⟨_, ?_, obliviousKShot_complete (smallestPrime_prime n) (le_smallestPrime_sq n) hk E s
    hreach⟩
  rw [← hpdef]
  have h1 := numRR_le_three hk hkn
  have h2 := smallestPrime_le_two_sqrt hn1
  rw [← hpdef] at h1 h2
  calc 2 * (2 * n - 1) * (p * (numRR p k + 1))
      ≤ 2 * (2 * n) * ((2 * Nat.sqrt n) * (3 + 1)) := by gcongr; omega
    _ = 32 * n * Nat.sqrt n := by ring

/-- *Oblivious k-Shot* (`k ≥ 3`) is a correct broadcasting protocol on undirected networks, for
every source. -/
theorem obliviousKShot_correctOnUndirected {n k : ℕ} (hk : 3 ≤ k) (s : Fin n) :
    CorrectOnUndirected (obliviousKShot n (smallestPrime n) k) k s := by
  intro G hG
  exact ⟨_, obliviousKShot_complete (smallestPrime_prime n) (le_smallestPrime_sq n) hk G.Adj s
    fun v => (SimpleGraph.reachable_iff_reflTransGen s v).1 (hG.preconnected s v)⟩

/-! ## `k ∈ {1, 2}`: Round-Robin -/

/-- Plain Round-Robin: at step `t` the node with label `t mod n` transmits. -/
def roundRobin (n : ℕ) : Schedule (Fin n) := fun t => univ.filter fun v => v.val = t % n

/-- For every `k ≥ 1` (in particular `k ∈ {1, 2}`, not covered by *Oblivious k-Shot*), Round-Robin
completes broadcasting within `2(2n - 1) n ≤ 4 n²` steps on every directed network in which all
nodes are reachable from the source. -/
theorem roundRobin_complete {n k : ℕ} (hk : 1 ≤ k) (E : Fin n → Fin n → Prop) (s : Fin n)
    (hreach : ∀ v, Relation.ReflTransGen E s v) :
    Complete (roundRobin n) k E s (2 * (2 * n - 1) * n) := by
  classical
  have hn : 0 < n := by have := s.isLt; omega
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have := complete_of_progress (S := n) (σ := roundRobin n) (k := k) hreach ?_
  · rwa [hcard] at this
  intro g
  set f := (activeSet (roundRobin n) k E s (g * n)).card with hf
  rcases Nat.eq_zero_or_pos f with h0 | hpos
  · rw [h0]; simp
  refine (progress_add_le_of_done (Nat.mul_le_mul_right _ (by omega)) ?_).trans
    (progress_mono (Nat.mul_le_mul_right _ (show g + 1 ≤ g + 2 * f by omega)))
  intro v hv
  have hvI : Informed (roundRobin n) k E s (g * n) v :=
    mem_informedSet.1 (mem_sdiff.1 hv).1
  obtain ⟨r, hr⟩ := informed_iff.1 hvI
  have hrg := recvTime_le hr
  -- the first appearance of `v` after `r`, within `n` steps
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_mod_eq hn (r + 1) v.val v.isLt
  have hex : ∃ t, r < t ∧ v ∈ roundRobin n t := ⟨m, by omega, by simp [roundRobin, hm3]⟩
  obtain ⟨hrt, hvt⟩ := Nat.find_spec hex
  have hle : Nat.find hex ≤ m := Nat.find_min' hex ⟨by omega, by simp [roundRobin, hm3]⟩
  have hcount : count (roundRobin n) v r (Nat.find hex) = 0 := by
    unfold count
    rw [card_eq_zero, filter_eq_empty_iff]
    intro t ht hvt'
    rw [mem_Ioo] at ht
    exact Nat.find_min hex ht.2 ⟨ht.1, hvt'⟩
  have htr : Transmits (roundRobin n) k E s (Nat.find hex - 1) v :=
    ⟨r, recvTime_of_le hr (by omega), by
      rw [Nat.sub_add_cancel (by omega)]; exact ⟨hrt, hvt, by omega⟩⟩
  have hσ : roundRobin n (Nat.find hex - 1 + 1) = {v} := by
    rw [Nat.sub_add_cancel (by omega)]
    ext u
    simp only [roundRobin, mem_filter, mem_univ, true_and, mem_singleton] at hvt ⊢
    exact ⟨fun h => Fin.ext (h.trans hvt.symm), fun h => h ▸ hvt⟩
  have hτ : Nat.find hex - 1 + 1 ≤ (g + 1) * n := by
    have : (g + 1) * n = g * n + n := by ring
    omega
  refine ⟨hvI.mono (Nat.mul_le_mul_right _ (by omega)), fun w hw => ?_⟩
  exact (informed_of_transmits_alone htr hσ hw).mono hτ

end Podc.KShotRadioBroadcast
