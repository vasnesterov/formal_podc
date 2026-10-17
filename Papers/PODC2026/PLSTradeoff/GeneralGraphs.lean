import Papers.PODC2026.PLSTradeoff.GeneralTS
import Papers.PODC2026.PLSTradeoff.StringShare

/-!
# The tradeoff theorem for general graphs (Theorem 1.2)

Lemma 5.6 (`exists_stringShare`) shares the index of a good radius assignment (Lemma 5.5) with
`O(1)` bits per node; with the `FindMyCluster` verification (`tsCertGeneral`) this certifies and
outputs a `(16K+12, 1/t)`-TS partition with constant cost, and Lemma 3.2 turns any 1-PLS of
cost `p` into a `(40K+32)`-PLS of cost `2⌈(2p+1)/t⌉ + 64`, where `K = t⌈log₂ n⌉`.

As in the paper (Section 2, "Verifier knowledge"), the graphs are assumed connected and the
verifier knows `n` (in our model the node set `V` is fixed).
-/

namespace PLSTradeoff

open Classical

variable {V : Type*} [Fintype V] [LinearOrder V] {ι : Type*}

lemma clog_sq_succ_le (n : ℕ) : Nat.clog 2 (n * n + 1) ≤ 2 * Nat.clog 2 n + 1 := by
  apply Nat.clog_le_of_le_pow
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) n
  have h1 : n * n ≤ 2 ^ Nat.clog 2 n * 2 ^ Nat.clog 2 n := Nat.mul_le_mul h h
  have h2 : 1 ≤ 2 ^ Nat.clog 2 n * 2 ^ Nat.clog 2 n :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  calc n * n + 1 ≤ 2 * (2 ^ Nat.clog 2 n * 2 ^ Nat.clog 2 n) := by omega
    _ = 2 ^ (2 * Nat.clog 2 n + 1) := by ring

lemma clog_le_pred (n : ℕ) : Nat.clog 2 n ≤ n - 1 := by
  apply Nat.clog_le_of_le_pow
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := Nat.lt_two_pow_self (n := n - 1); omega

/-- **Theorem 1.2** of [Filtser–Fischer, PODC 2026]: on any family of connected graphs, every
1-PLS for `P` with cost `p` and every `t ≥ 1` yield a `(40 t⌈log₂ n⌉ + 32)`-PLS for `P` with cost
`2⌈(2p+1)/t⌉ + 64`, i.e. an `O(t log n)`-PLS with cost `O(⌈p/t⌉)` (for `p ≥ 1`). -/
theorem tradeoff_general {𝒢 : Set (SimpleGraph V)} (h𝒢 : ∀ G ∈ 𝒢, G.Connected)
    {P : SimpleGraph V → (V → ι) → Prop} {t p : ℕ} (ht : 1 ≤ t) (S1 : PLS 𝒢 P 1)
    (hp : S1.CostLE p) :
    ∃ St : PLS 𝒢 P (40 * t * Nat.clog 2 (Fintype.card V) + 32),
      St.CostLE (2 * ⌈((2 * p + 1 : ℕ) : ℝ) / t⌉₊ + 64) := by
  set n := Fintype.card V
  set K := t * Nat.clog 2 n with hK
  set rS := Nat.clog 2 (n * n + 1)
  have hrS : n * n + 1 ≤ 2 ^ rS := Nat.le_pow_clog (by norm_num) _
  have hKc : Nat.clog 2 n ≤ K := Nat.le_mul_of_pos_left _ ht
  have hrS2 : rS ≤ 2 * Nat.clog 2 n + 1 := clog_sq_succ_le n
  obtain ⟨prov, ver, hloc, hcomp, hsound, hcost⟩ := exists_stringShare (V := V) rS
  let SS : ShareScheme V rS (2 * cdiv rS n + 8) (4 * rS + 2) :=
    { prov := prov, ver := ver, isLocal := hloc, complete := hcomp, sound := hsound,
      cost := hcost }
  have hρ : 4 * rS + 2 ≤ genR K := by unfold genR rhoMax rad; omega
  obtain ⟨S, hS⟩ := tsCertGeneral (t := t) ht hK 𝒢 h𝒢 hrS SS hρ
  have hex : ∀ G ∈ 𝒢, Nonempty (TSPartition G (2 * rhoMax K) (1 / t)) := by
    intro G hG
    obtain ⟨F, hF⟩ := exists_good_family (V := V) ht hK
    obtain ⟨i, hi⟩ := hF G (h𝒢 G hG)
    exact ⟨TSPartition.ofDegenerate (isDegenerate_of_allClustered ht hi)
      (isWeaklyBounded_of_allClustered (Mx := 3 * K + 2)
        (fun w => by have := (F i w).isLt; omega) hi)⟩
  obtain ⟨St, hSt⟩ := tradeoff_of_tsCert S hS hex S1 hp
  have hR : max (genR K) (2 * (2 * rhoMax K) + 2) = 40 * t * Nat.clog 2 n + 32 := by
    rw [max_eq_left (by unfold genR; omega)]
    simp only [genR, rhoMax, rad, hK]; ring
  have hcd : cdiv rS n ≤ 2 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [cdiv, hn]
    · apply cdiv_le_of_le_mul hn
      have := clog_le_pred n
      omega
  have hε : (1 / t : ℝ) * (2 * p + 1) = ((2 * p + 1 : ℕ) : ℝ) / t := by push_cast; ring
  refine ⟨St.mono hR.le, fun G hG I hP v => ?_⟩
  have := hSt G hG I hP v
  rw [hε] at this
  rw [PLS.mono_prov]
  omega

end PLSTradeoff
