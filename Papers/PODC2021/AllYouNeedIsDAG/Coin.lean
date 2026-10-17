import Podc.Probability.CoinGame

/-!
# DAG-Rider: expected number of waves until a commit (Claim 6)

Keidar, Kokoris-Kogias, Naor, Spiegelman, *All You Need is DAG*, PODC 2021 (arXiv:2102.08325v2),
Claim 6: "the expected number of waves until the commit rule is met is at most `3/2 + ε`".

## Model

The coin game of `Podc.Probability.CoinGame` (`Cslib.Probability.CoinGame`):

* The global perfect coin (`ε = 0`) yields i.i.d. uniform leaders `c 0, c 1, … ∈ P`, `|P| = n`.
* The adversary is adaptive: it sees all coins revealed so far. Before coin `i` is revealed, the
  execution fixes a set `V i (c 0, …, c (i-1)) ⊆ P` of "good leaders" of wave `i`, of size at
  least `q`. In DAG-Rider `V i` is the common core of wave `i` (`DagRider.core` in
  `CommonCore.lean`, `q = 2f + 1`), which is determined as soon as `2f + 1` vertices of the third
  round of the wave exist, i.e. before any correct process reveals its coin share of the wave.
* Wave `i` is a success (`Hit`) iff `c i ∈ V i (c 0, …, c (i-1))`.

General results (`CoinGame.card_misses_le`, `CoinGame.prob_missesWindow_le`: a success
eventually occurs with probability `1`; `CoinGame.expected_waves_le`: `E[T] ≤ n / q`) are
specialised here to `n = 3f + 1`, `q = 2f + 1`.
-/

namespace DagRider.Coin

open Cslib.Probability.CoinGame

variable {P : Type*} [Fintype P] [DecidableEq P]

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
