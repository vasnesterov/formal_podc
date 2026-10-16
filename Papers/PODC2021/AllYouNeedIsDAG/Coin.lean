import Mathlib

/-!
# DAG-Rider: expected number of waves until a commit (Claim 6)

Keidar, Kokoris-Kogias, Naor, Spiegelman, *All You Need is DAG*, PODC 2021 (arXiv:2102.08325v2),
Claim 6: "the expected number of waves until the commit rule is met is at most `3/2 + ε`".

## Model

* The global perfect coin (`ε = 0`) yields i.i.d. uniform leaders `c 0, c 1, … ∈ P`, `|P| = n`.
  We use finite uniform counting: a coin sequence of length `K` is a function `Fin K → P`, and all
  `n ^ K` of them are equally likely. No measure theory is needed.
* The adversary is adaptive: it sees all coins revealed so far. Before coin `i` is revealed, the
  execution (a function of the earlier coins; the adversary is deterministic w.l.o.g.) fixes a set
  `V i (c 0, …, c (i-1)) ⊆ P` of "good leaders" of wave `i`, of size at least `q`. In DAG-Rider `V i`
  is the common core of wave `i` (`DagRider.core` in `CommonCore.lean`, `q = 2f + 1`), which is
  determined as soon as `2f + 1` vertices of the third round of the wave exist, i.e. before
  any correct process reveals its coin share of the wave.
* Wave `i` is a success (`Hit`) iff `c i ∈ V i (c 0, …, c (i-1))`.

## Results

* `card_misses_le`: at most `(n - q) ^ k` of the `n ^ k` coin sequences make all of the first `k`
  waves fail.
* `card_missesWindow_le`: failing at all `k` waves `w₀, …, w₀ + k - 1` has probability at most
  `((n - q) / n) ^ k → 0`, so a success eventually occurs with probability `1`.
* `expected_waves_le`: the expected number `T` of waves up to and including the first success
  (truncated at any horizon `K`) is at most `n / q`.
* `dagRider_expected_waves`: with `n = 3f + 1`, `q = 2f + 1` this is `≤ (3f+1)/(2f+1) ≤ 3/2`.
-/

namespace DagRider.Coin

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The adversary: before coin `i` is revealed, a set `V i h ⊆ P` of good leaders is fixed as a
function of the earlier coins `h = (c 0, …, c (i-1))`. -/
abbrev Adversary (P : Type*) := (i : ℕ) → (Fin i → P) → Finset P

/-- Wave `i < m` is a success for the coin sequence `c : Fin m → P`: the coin of wave `i` lands in
the set of good leaders that was fixed from the coins of the waves before `i`. -/
def Hit (V : Adversary P) {m : ℕ} (c : Fin m → P) (i : ℕ) (h : i < m) : Prop :=
  c ⟨i, h⟩ ∈ V i (fun j => c ⟨j.1, j.2.trans h⟩)

instance (V : Adversary P) {m : ℕ} (c : Fin m → P) (i : ℕ) (h : i < m) :
    Decidable (Hit V c i h) := by
  unfold Hit; infer_instance

/-- Coin sequences of length `m` such that every wave `i` with `lo ≤ i < hi` fails. -/
def missesIn (V : Adversary P) (m lo hi : ℕ) : Finset (Fin m → P) :=
  univ.filter (fun c => ∀ i (h : i < m), lo ≤ i → i < hi → ¬ Hit V c i h)

/-- Coin sequences of length `k` such that each of the waves `0, …, k - 1` fails. -/
def misses (V : Adversary P) (k : ℕ) : Finset (Fin k → P) := missesIn V k 0 k

/-- Coin sequences of length `w₀ + k` such that each of the waves `w₀, …, w₀ + k - 1` fails. -/
def missesWindow (V : Adversary P) (w₀ k : ℕ) : Finset (Fin (w₀ + k) → P) :=
  missesIn V (w₀ + k) w₀ (w₀ + k)

/-- One more coin: the new wave `m` contributes a factor `n - q` if it must fail, `n` otherwise. -/
lemma card_missesIn_succ_le (V : Adversary P) {q : ℕ} (hV : ∀ i h, q ≤ (V i h).card)
    (m lo hi : ℕ) :
    (missesIn V (m + 1) lo hi).card ≤
      (missesIn V m lo hi).card * (if lo ≤ m ∧ m < hi then Fintype.card P - q
        else Fintype.card P) := by
  classical
  let allowed : (Fin m → P) → Finset P := fun c' =>
    if lo ≤ m ∧ m < hi then (V m c')ᶜ else univ
  have hmaps : Set.MapsTo (fun c : Fin (m + 1) → P => (⟨Fin.init c, c (Fin.last m)⟩ :
      Σ _ : Fin m → P, P)) ↑(missesIn V (m + 1) lo hi) ↑((missesIn V m lo hi).sigma allowed) := by
    intro c hc
    simp only [missesIn, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hc
    simp only [missesIn, coe_sigma, Set.mem_sigma_iff, coe_filter, mem_univ, true_and,
      Set.mem_ofPred_eq, mem_coe]
    refine ⟨fun i h h1 h2 => hc i (by omega) h1 h2, ?_⟩
    simp only [allowed]
    split_ifs with hm
    · exact mem_compl.2 (hc m (by omega) hm.1 hm.2)
    · exact mem_univ _
  have hinj : Set.InjOn (fun c : Fin (m + 1) → P => (⟨Fin.init c, c (Fin.last m)⟩ :
      Σ _ : Fin m → P, P)) ↑(missesIn V (m + 1) lo hi) := by
    intro c _ c' _ h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    rw [← Fin.snoc_init_self c, ← Fin.snoc_init_self c', h.1, h.2]
  refine (card_le_card_of_injOn _ hmaps hinj).trans ?_
  rw [card_sigma]
  refine (sum_le_sum (fun c' _ => ?_)).trans (sum_const_nat (fun _ _ => rfl)).le
  simp only [allowed]
  split_ifs
  · rw [card_compl]; have := hV m c'; omega
  · simp

/-- The number of coin sequences of length `m` failing at all waves in `[lo, hi)`, as a product
of per-wave factors. -/
lemma card_missesIn_le (V : Adversary P) {q : ℕ} (hV : ∀ i h, q ≤ (V i h).card)
    (m lo hi : ℕ) :
    (missesIn V m lo hi).card ≤
      ∏ i ∈ range m, (if lo ≤ i ∧ i < hi then Fintype.card P - q else Fintype.card P) := by
  induction m with
  | zero =>
    simp only [range_zero, prod_empty]
    exact (card_le_univ _).trans (by simp)
  | succ m ih =>
    rw [prod_range_succ]
    exact (card_missesIn_succ_le V hV m lo hi).trans (Nat.mul_le_mul_right _ ih)

/-- With an adversary whose good sets have at least `q` elements, at most `(n - q) ^ k` of the
`n ^ k` coin sequences make all of the first `k` waves fail. -/
theorem card_misses_le (V : Adversary P) {q : ℕ} (hV : ∀ i h, q ≤ (V i h).card) (k : ℕ) :
    (misses V k).card ≤ (Fintype.card P - q) ^ k := by
  refine (card_missesIn_le V hV k 0 k).trans (le_of_eq ?_)
  rw [prod_congr rfl (g := fun _ => Fintype.card P - q), prod_const, card_range]
  intro i hi
  rw [mem_range] at hi
  simp [hi]

/-- Failing at `k` consecutive waves `w₀, …, w₀ + k - 1`, whatever happened before, has
probability at most `((n - q) / n) ^ k`: among the `n ^ (w₀ + k)` coin sequences, at most
`n ^ w₀ * (n - q) ^ k` do so. Hence (for `q > 0`) some wave succeeds with probability `1`. -/
theorem card_missesWindow_le (V : Adversary P) {q : ℕ} (hV : ∀ i h, q ≤ (V i h).card)
    (w₀ k : ℕ) :
    (missesWindow V w₀ k).card ≤ Fintype.card P ^ w₀ * (Fintype.card P - q) ^ k := by
  refine (card_missesIn_le V hV (w₀ + k) w₀ (w₀ + k)).trans (le_of_eq ?_)
  rw [prod_range_add]
  congr 1
  · rw [prod_congr rfl (g := fun _ => Fintype.card P), prod_const, card_range]
    intro i hi
    rw [mem_range] at hi
    simp [show ¬ w₀ ≤ i by omega]
  · rw [prod_congr rfl (g := fun _ => Fintype.card P - q), prod_const, card_range]
    intro i hi
    rw [mem_range] at hi
    simp [hi]

/-- The probability version of `card_missesWindow_le`. -/
theorem prob_missesWindow_le (V : Adversary P) {q : ℕ} (hV : ∀ i h, q ≤ (V i h).card)
    (hn : 0 < Fintype.card P) (w₀ k : ℕ) :
    ((missesWindow V w₀ k).card : ℚ) / (Fintype.card P : ℚ) ^ (w₀ + k) ≤
      (((Fintype.card P - q : ℕ) : ℚ) / Fintype.card P) ^ k := by
  have hn' : (0 : ℚ) < Fintype.card P := by exact_mod_cast hn
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), pow_add]
  have := card_missesWindow_le V hV w₀ k
  have h' : ((missesWindow V w₀ k).card : ℚ) ≤
      (Fintype.card P : ℚ) ^ w₀ * ((Fintype.card P - q : ℕ) : ℚ) ^ k := by exact_mod_cast this
  calc ((missesWindow V w₀ k).card : ℚ) * (Fintype.card P : ℚ) ^ k
      ≤ (Fintype.card P : ℚ) ^ w₀ * ((Fintype.card P - q : ℕ) : ℚ) ^ k *
          (Fintype.card P : ℚ) ^ k := by gcongr
    _ = _ := by ring

/-- The number of waves up to and including the first successful one, truncated at the horizon
`K` (it is `K` if none of the waves `0, …, K - 1` succeeds). It is defined as the number of
`k < K` such that all waves before `k` fail; `T_eq_of_first_hit` and `T_eq_of_no_hit` show that
this is the intended quantity. -/
def T (V : Adversary P) (K : ℕ) (c : Fin K → P) : ℕ :=
  ((range K).filter (fun k => ∀ i (h : i < K), i < k → ¬ Hit V c i h)).card

omit [Fintype P] in
/-- If wave `s` is the first success, then `T = s + 1`. -/
lemma T_eq_of_first_hit (V : Adversary P) {K : ℕ} (c : Fin K → P) {s : ℕ} (hs : s < K)
    (hhit : Hit V c s hs) (hmiss : ∀ i (h : i < K), i < s → ¬ Hit V c i h) :
    T V K c = s + 1 := by
  unfold T
  convert card_range (s + 1) using 2
  ext k
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨-, hk⟩
    by_contra hks
    exact hk s hs (by omega) hhit
  · intro hk
    exact ⟨by omega, fun i h hi => hmiss i h (by omega)⟩

omit [Fintype P] in
/-- If no wave before the horizon succeeds, then `T = K`. -/
lemma T_eq_of_no_hit (V : Adversary P) {K : ℕ} (c : Fin K → P)
    (hmiss : ∀ i (h : i < K), ¬ Hit V c i h) : T V K c = K := by
  unfold T
  rw [filter_true_of_mem (fun k _ i h _ => hmiss i h), card_range]

/-- `∑_{k < K} a^k b^(K-k) * q + a^K * b = b^(K+1)` for `b = a + q` (telescoping). -/
private lemma geom_identity (a q : ℕ) (K : ℕ) :
    (∑ k ∈ range K, a ^ k * (a + q) ^ (K - k)) * q + a ^ K * (a + q) = (a + q) ^ (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, sum_congr rfl (g := fun k => (a ^ k * (a + q) ^ (K - k)) * (a + q))]
    · rw [← sum_mul, Nat.add_sub_cancel_left, pow_one, pow_succ (a + q) (K + 1), ← ih]
      ring
    · intro k hk
      rw [mem_range] at hk
      rw [show K + 1 - k = (K - k) + 1 by omega, pow_succ]
      ring

/-- **Claim 6 of the paper** (with a perfect coin, `ε = 0`): if the adversary's good set of every
wave has at least `q > 0` of the `n` possible leaders, then the expected number of waves up to and
including the first successful wave is at most `n / q`.

Here the expectation is over uniform coin sequences of length `K`, and `T` is truncated at `K`.
Since the bound holds for every horizon `K` and the truncated waiting times increase to the true
waiting time, the monotone convergence theorem gives `E[T] ≤ n / q` for the untruncated `T`. -/
theorem expected_waves_le (V : Adversary P) {q : ℕ} (hV : ∀ i h, q ≤ (V i h).card) (hq : 0 < q)
    (hqn : q ≤ Fintype.card P) (K : ℕ) :
    (∑ c : Fin K → P, (T V K c : ℚ)) / (Fintype.card P : ℚ) ^ K ≤
      (Fintype.card P : ℚ) / q := by
  set n := Fintype.card P with hn_def
  have hn : 0 < n := hq.trans_le hqn
  -- linearity: `∑_c T c = ∑_{k<K} #(sequences missing all waves < k)`
  have hsum : ∑ c : Fin K → P, T V K c = ∑ k ∈ range K, (missesIn V K 0 k).card := by
    simp only [T, card_filter, missesIn]
    rw [sum_comm]
    refine sum_congr rfl (fun k _ => ?_)
    simp
  have hbound : ∀ k ∈ range K, (missesIn V K 0 k).card ≤ (n - q) ^ k * n ^ (K - k) := by
    intro k hk
    rw [mem_range] at hk
    refine (card_missesIn_le V hV K 0 k).trans (le_of_eq ?_)
    obtain ⟨d, rfl⟩ : ∃ d, K = k + d := ⟨K - k, by omega⟩
    rw [prod_range_add, Nat.add_sub_cancel_left]
    congr 1
    · rw [prod_congr rfl (g := fun _ => n - q), prod_const, card_range]
      intro i hi; rw [mem_range] at hi; simp [hi, n]
    · rw [prod_congr rfl (g := fun _ => n), prod_const, card_range]
      intro i _; simp [n]
  have hnat : (∑ c : Fin K → P, T V K c) * q ≤ n ^ (K + 1) := by
    have hid := geom_identity (n - q) q K
    rw [Nat.sub_add_cancel hqn] at hid
    rw [hsum]
    calc (∑ k ∈ range K, (missesIn V K 0 k).card) * q
        ≤ (∑ k ∈ range K, (n - q) ^ k * n ^ (K - k)) * q :=
          Nat.mul_le_mul_right _ (sum_le_sum hbound)
      _ ≤ n ^ (K + 1) := by omega
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) hq', ← pow_succ']
  exact_mod_cast hnat

/-- **Claim 6 for DAG-Rider** (`n = 3f + 1` processes, common core of size `2f + 1`, perfect coin):
the expected number of waves until the commit rule is met is at most `(3f+1)/(2f+1) ≤ 3/2`. -/
theorem dagRider_expected_waves (f : ℕ) (hP : Fintype.card P = 3 * f + 1) (V : Adversary P)
    (hV : ∀ i h, 2 * f + 1 ≤ (V i h).card) (K : ℕ) :
    (∑ c : Fin K → P, (T V K c : ℚ)) / (Fintype.card P : ℚ) ^ K ≤
        ((3 * f + 1 : ℕ) : ℚ) / (2 * f + 1 : ℕ) ∧
      (∑ c : Fin K → P, (T V K c : ℚ)) / (Fintype.card P : ℚ) ^ K ≤ 3 / 2 := by
  have h := expected_waves_le V hV (by omega) (by omega) K
  replace h := h.trans_eq (by rw [hP])
  refine ⟨h, h.trans ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  push_cast
  linarith

end DagRider.Coin
