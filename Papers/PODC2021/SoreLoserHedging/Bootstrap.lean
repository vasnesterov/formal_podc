import Mathlib

/-!
# Bootstrapping premiums (§6 of [Xue–Herlihy 2021])

Y. Xue, M. Herlihy, *Hedging Against Sore Loser Attacks in Cross-Chain Transactions*, PODC 2021
(arXiv:2105.06322), §6, Figure 2.

A premium of `v / P` (`P > 1`) is considered acceptable to protect an escrowed value `v`. In the
hedged swap of §5.2 with principals `A` (Alice) and `B` (Bob), the leader deposits
`B⁽¹⁾ = (A + B) / P` and the follower `A⁽¹⁾ = A / P`. A bootstrapping round is a hedged swap of
the next round's premiums (with the roles swapped), so with `A⁽⁰⁾ = A`, `B⁽⁰⁾ = B`:

  `B⁽ᵏ⁺¹⁾ = (A⁽ᵏ⁾ + B⁽ᵏ⁾) / P`,  `A⁽ᵏ⁺¹⁾ = A⁽ᵏ⁾ / P`.

The paper claims that with `r` rounds of premium exchanges the initial premiums are
`(rA + B) / P^r` and `A / P^r` (`premiums_closed_form`). Indexing: Figure 2 ("2 rounds of premium
deposits") deposits `B⁽²⁾, A⁽²⁾` and then `B⁽¹⁾, A⁽¹⁾`, i.e. the `r` rounds *include* the premium
round of the hedged swap itself; the number of genuinely additional bootstrapping rounds is
`r - 1`. The paper's numeric example ("with 1% premiums and $4 initial lock-up risk, 3
bootstrapping rounds are enough to hedge a $1,000,000 swap") matches `r = 3` in this indexing with
`A = B = 10⁶` (`example_one_million`): `B⁽³⁾ = 4`, `A⁽³⁾ = 1`. So "3 bootstrapping rounds" there
counts the hedged swap's own premium round, and a "$1,000,000 swap" means each principal is worth
`$10⁶`. With `A + B = 10⁶` (`A = B = 5·10⁵`) one gets `B⁽³⁾ = 2`, `A⁽³⁾ = 1/2`
(`example_half_million`); with `r = 4` (three rounds on top of the hedged swap's own) and
`A = B = 10⁶`, `B⁽⁴⁾ = 1/20`. The paper's estimate "approximately `log_P((A + B)/p)` rounds"
gives `log₁₀₀(2·10⁶/4) ≈ 2.85`, consistent with `r = 3` (it ignores the `rA` growth).
-/

namespace Podc.SoreLoserHedging.Bootstrap

/-- `premiums P A B k = (A⁽ᵏ⁾, B⁽ᵏ⁾)`: the premiums of bootstrapping level `k`. -/
def premiums (P A B : ℚ) : ℕ → ℚ × ℚ
  | 0 => (A, B)
  | k + 1 => ((premiums P A B k).1 / P, ((premiums P A B k).1 + (premiums P A B k).2) / P)

@[simp] lemma premiums_zero (P A B : ℚ) : premiums P A B 0 = (A, B) := rfl

@[simp] lemma premiums_succ (P A B : ℚ) (k : ℕ) :
    premiums P A B (k + 1) =
      ((premiums P A B k).1 / P, ((premiums P A B k).1 + (premiums P A B k).2) / P) := rfl

/-- The hedged swap's own premiums (§5.2, §6): `B⁽¹⁾ = (A + B) / P`, `A⁽¹⁾ = A / P`. -/
lemma premiums_one (P A B : ℚ) : premiums P A B 1 = (A / P, (A + B) / P) := rfl

/-- §6 of [Xue–Herlihy 2021]: "if they precede their swap with `r` rounds of premium exchanges,
then Alice's and Bob's initial premium is `(rA + B)/P^r` and `A/P^r`". Here `r` counts all
premium rounds including the hedged swap's own (`r = 1`: no bootstrapping); the formula also
holds for `r = 0` and for every `P` (including `P = 0`, with `x / 0 = 0`). -/
theorem premiums_closed_form (P A B : ℚ) (r : ℕ) :
    premiums P A B r = (A / P ^ r, (r * A + B) / P ^ r) := by
  induction r with
  | zero => simp
  | succ k ih =>
    rw [premiums_succ, ih, pow_succ]
    simp only [div_div, Prod.mk.injEq, true_and]
    rw [← add_div]
    push_cast
    ring_nf

/-- §6, the two-round case in the text: `B⁽²⁾ = (2A + B)/P²`, `A⁽²⁾ = A/P²`. -/
lemma premiums_two (P A B : ℚ) : premiums P A B 2 = (A / P ^ 2, (2 * A + B) / P ^ 2) := by
  rw [premiums_closed_form]; norm_num

/-- §6 example: 1% premiums (`P = 100`), principals `A = B = 10⁶`: after `r = 3` premium rounds the
initial premiums are `4` (leader) and `1` (follower) — "$4 initial lock-up risk". -/
theorem example_one_million : premiums 100 (10 ^ 6) (10 ^ 6) 3 = (1, 4) := by
  rw [premiums_closed_form]; norm_num

/-- With `A + B = 10⁶` instead, the same three rounds give initial premiums `2` and `1/2`. -/
theorem example_half_million : premiums 100 (5 * 10 ^ 5) (5 * 10 ^ 5) 3 = (1 / 2, 2) := by
  rw [premiums_closed_form]; norm_num

/-- With four premium rounds (three bootstrapping rounds on top of the hedged swap's own premium
round) and `A = B = 10⁶`, the leader's initial premium is `1/20`. -/
theorem example_four_rounds : premiums 100 (10 ^ 6) (10 ^ 6) 4 = (1 / 100, 1 / 20) := by
  rw [premiums_closed_form]; norm_num

end Podc.SoreLoserHedging.Bootstrap
