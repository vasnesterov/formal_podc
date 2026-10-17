import Papers.PODC2026.PLSTradeoff.CertifyTS
import Papers.PODC2026.PLSTradeoff.BallCarving

/-!
# The warm-up tradeoff for general graphs (Corollary 4.7)

Combining the warm-up ball carving (an `(O(t log n), 1/t)`-TS partition in every graph,
`exists_tsPartition`), Lemma 4.5 (`exists_tsCert`) and Lemma 3.2 (`tradeoff_of_tsCert`):
every 1-PLS of cost `p` yields an `O(t log n)`-PLS of cost `O(⌈p/t⌉ + log n)`.

With `D = 4(t⌈log₂ n⌉ + 1)` the verification radius is `3D + 2 = 12 t⌈log₂ n⌉ + 14` and the cost
is `4⌈log₂ n⌉ + 2⌈(2p+1)/t⌉ + 10`.

The paper obtains Corollary 4.7 from Bartal's padded decompositions; its technical overview
(Section 1.1, "Warmup") derives the same statement from the ball carving formalized here.
-/

namespace PLSTradeoff

variable {V : Type*} [Fintype V] [LinearOrder V] {ι : Type*}

/-- **Corollary 4.7** of [Filtser–Fischer, PODC 2026] (via the warm-up construction of
Section 1.1): for any graph family, every 1-PLS for `P` with cost `p` and every `t ≥ 1` yield a
`(12 t⌈log₂ n⌉ + 14)`-PLS for `P` with cost `4⌈log₂ n⌉ + 2⌈(2p+1)/t⌉ + 10`, i.e. an
`O(t log n)`-PLS with cost `O(⌈p/t⌉ + log n)`. -/
theorem warmup_tradeoff {𝒢 : Set (SimpleGraph V)} {P : SimpleGraph V → (V → ι) → Prop}
    {t p : ℕ} (ht : 1 ≤ t) (S1 : PLS 𝒢 P 1) (hp : S1.CostLE p) :
    ∃ St : PLS 𝒢 P (12 * t * Nat.clog 2 (Fintype.card V) + 14),
      St.CostLE (4 * Nat.clog 2 (Fintype.card V) + 2 * ⌈((2 * p + 1 : ℕ) : ℝ) / t⌉₊ + 10) := by
  set D := 4 * (t * Nat.clog 2 (Fintype.card V) + 1) with hD
  obtain ⟨S, hS⟩ := exists_tsCert 𝒢 D (1 / t : ℝ)
  obtain ⟨St, hSt⟩ := tradeoff_of_tsCert S hS (fun G _ => exists_tsPartition G ht) S1 hp
  have hR : max (3 * D + 2) (2 * D + 2) = 12 * t * Nat.clog 2 (Fintype.card V) + 14 := by
    rw [max_eq_left (by omega), hD]; ring
  have hε : (1 / t : ℝ) * (2 * p + 1) = ((2 * p + 1 : ℕ) : ℝ) / t := by
    push_cast; ring
  refine ⟨St.mono hR.le, fun G hG I hP v => ?_⟩
  have := hSt G hG I hP v
  rw [PLS.mono_prov]
  rw [hε] at this
  omega

end PLSTradeoff
