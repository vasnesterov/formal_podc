# Contention Resolution with Predictions — PODC 2021

Seth Gilbert, Calvin Newport, Nitin Vaidya, Alex Weaver. *Contention Resolution with Predictions.* PODC 2021.
DOI [10.1145/3465084.3467911](https://doi.org/10.1145/3465084.3467911). Formalized version: arXiv
[2105.12706](https://arxiv.org/abs/2105.12706) v1; numbering follows it.

**Verdict: 🛠️ Hard fix.** The entropy lower bound without collision detection (Theorem 2.4) and the perfect-advice lower
bounds (Theorems 3.3–3.7) hold, but the proofs of Theorems 3.3 and 3.7 are wrong and were replaced by new arguments. The
collision-detection entropy bound (Theorem 2.8) and the upper bounds with predictions and randomization were not
checked, and the randomized lower bounds assume Newport's bound [18], as the paper does.

## Mistakes in the paper

### ✏️ Slips
- Theorems 3.3 and 3.5 (advice of "at most `b` bits"): the definitions say the advice has "no more than `b(n)` bits", and
  with strings of variable length `≤ b` both theorems are false (`theorem_3_3_false_variable_length`,
  `theorem_3_5_false_variable_length`). For `b = 1` the strings `ε, 0, 1` tell three players who transmits, although
  `1 < log₂ 3` (Theorem 3.3). With collision detection, the same three advice values select one of three groups of three
  players, and each group is resolved in two rounds (players 1, 2 of the group transmit; after silence player 3, after a
  collision player 1). So `n = 9`, `b = 1`, `t = 2 < log₂ 9 − 1` (Theorem 3.5). Both theorems are true for the
  fixed-length advice `f_A : P(A) → {0,1}^b` of Section 3.1 (`theorem_3_3`, `theorem_3_5`), which we treat as an implied
  assumption of the model section: we read "at most `b` bits" as "a `b`-bit string". The proof of 3.5 itself feeds
  variable-length histories into 3.3; padding to `b + t` bits repairs that step.
- Theorems 3.6 and 3.7 (upper halves of the `Θ` bounds): they are false for long advice, since every algorithm needs at
  least one round while the claimed bounds tend to `0` (`theorem_3_6_upper_false`, `theorem_3_7_upper_false`). For
  `b(n) = ⌊log₂ n⌋ − 1 < log n`, `log n / 2^{b(n)} → 0` (3.6). For `b(n) = ⌈log₂ log₂ n⌉ − 1 < log log n` along
  `n = 2^{2^j+1}`, `log log n − b(n) → 0` (3.7). Table 2's `Θ(log n − b)` has the same issue. It is a missing `1 +`: the
  correct forms are `Θ(1 + log n / 2^b)` and `Θ(1 + log log n − b)`, and the paper itself treats the `O(1)` regime only
  for `b ≥ log log n`. The lower halves are unaffected.
- RF-construction appends `2^j` where the range index `j` is meant.
- The tightness text after 3.4 writes `n/q` for `n/2^q`.
- The last display of 3.7 writes `O(log log n) − b(n)` for a lower bound.

## Proof gaps (statements true)

### 🛠️ Theorem 3.3 (the "strongly selective" claim)
The proof claims that the first-round transmitter sets `V(s)` form an `(n, n)`-strongly selective family,
which is false: for `n = 2`, `V(0) = {0}`, `V(1) = {0,1}` solve the problem but nothing isolates `1` in
`{0,1}` (`not_stronglySelective_example`).

**Impact.** The theorem stands with an unchanged bound, on a new argument (`theorem_3_3`, via
`Cslib.card_le_of_forall_exists_card_inter_eq_one`).

**Details.** Correctness only says that *some* participant of each `P` is isolated, not every one. So
Theorem 3.2 [5] does not apply.

**Repair.** A parity argument over `GF(2)`: a family meeting every nonempty set in exactly one point has at
least `n` members (`Cslib.card_le_of_forall_exists_card_inter_eq_one`).

### 🛠️ Theorem 3.7, lower bound (wrong direction of Jensen)
The proof bounds the cost `E[2^T]` of simulating a collision-detection algorithm without collision detection
by `2^{E[T]}`, but Jensen gives `E[2^T] ≥ 2^{E[T]}`, so the step "if `t < log t'`, we get a no-CD algorithm
faster than `t'`" does not follow.

**Impact.** The claimed `Ω(log log n − b)` stands, with half the paper's leading constant (`theorem_3_7_lower`,
`theorem_3_7_lower_bits`).

**Details.** Simulating a collision-detection algorithm that takes `T` rounds costs `2^T` rounds without
collision detection. What the paper's argument gives is `E[2^T] ≥ c log n / 2^b` (`theorem_3_7_lower_exp`).

**Repair.** Markov's inequality and independent restarts of the first `2t` rounds give
`c log₂ n ≤ 2^b · 2^{2t+1}`, i.e. `t ≥ (log₂(c log₂ n) − b − 3)/2` (`theorem_3_7_lower`,
`theorem_3_7_lower_bits`).

### 🔧 Lemma 2.5 (code not uniquely decodable)
The proof applies the Source Coding Theorem to the code `x ↦ (r, d)`, which writes `r` in `log r` bits without
a delimiter and so is not uniquely decodable.

**Impact.** The lemma's idea stands: a positive integer of mean `μ` has entropy at most `log(μ + 1) + log e`.

**Repair.** A Gibbs inequality against a geometric distribution (`sum_negMulLog_le_of_card_fiber_le`).

### 🔧 Lemma 2.7, case 1 (mean is not median)
The step "success within the first `μ_i` rounds with probability `< 1/2` contradicts expected time `μ_i`" is
false (`T = 1` w.p. 0.49, `T = 2` w.p. 0.51).

**Impact.** Repaired with a direct bound (`UniformAlg.expTime_ge`), used in Theorem 2.4.

**Repair.** If all rounds before `R` succeed with probability `< ε` and `Rε ≤ 1/2`, then `E[T] ≥ (R+1)/2`
(`UniformAlg.expTime_ge`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- *Channel:* single hop, synchronous rounds, `n` potential players `Fin n`. An adversary picks a nonempty participant
  set `P`. The problem is solved in the first round with exactly one transmitter. With collision detection everybody
  (transmitters included) learns "collision" vs "silence"; without it every unsuccessful round is silence.
- *Advice:* `f P`, the same for all participants, from an alphabet `A`; `b` bits means `A = Fin b → Bool`.
- *Deterministic algorithms:* `advice → common feedback history → id → transmit?` (`DetAlg`). This is fully general,
  since before success all participants see the same feedback.
- *Randomized algorithms:* private coins, not necessarily uniform. No-CD players draw independent transmission
  schedules `ℕ → Bool` from arbitrary laws; CD players draw strategies `List Bool → Bool`. Expected times are in
  `ℝ≥0∞`; worst case over `P`.
- *Uniform algorithms (Theorem 2.4):* a probability sequence `p_r`; the number of participants is drawn from a
  distribution on `{2, …, n}`; success events are independent with probability `k p_r (1 − p_r)^{k−1}`.
- *External result:* the randomized lower bounds assume Newport's `Ω(log n)` no-CD bound [18] as the hypothesis
  `NewportBound n c`. It is non-vacuous (`newportBound_of_le_one`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 2.4 (`t_X = Ω(2^{H(c(X))}/log log n)`, uniform, no CD) | `theorem_2_4`, `theorem_2_4_explicit` (`C = 1/(88e)`, `n ≥ 4`) | `EntropyLowerBound.lean` |
| Lemma 2.6 (contrapositive form) | `le_mul_of_good`, `mul_le_of_good` | `EntropyLowerBound.lean` |
| Theorem 3.3 (`b ≥ log n`, non-interactive) | `theorem_3_3`, `theorem_3_3_card` (`n ≤ |A|`) | `LowerBounds.lean` |
| Theorem 3.4 (`t ≥ n^{1−α}/2`, no CD) | `theorem_3_4`, `theorem_3_4_card` (`n ≤ 2^b t`) | `LowerBounds.lean` |
| Tightness of 3.4 | `upper_noCD` (`⌈n/2^b⌉` rounds, exactly optimal) | `UpperBounds.lean` |
| Theorem 3.5 (`t ≥ log n − b`, CD) | `theorem_3_5`, `theorem_3_5_card` (`n ≤ 2^b(2^t − 1)`) | `LowerBounds.lean` |
| Tightness of 3.5 | `upper_CD_clog` (`⌈log n⌉ − b + 1` rounds) | `UpperBounds.lean` |
| Theorem 3.3/3.5 with variable-length advice | `theorem_3_3_false_variable_length`, `theorem_3_5_false_variable_length` | `Counterexamples.lean` |
| Proof of 3.3 ("strongly selective") | `not_stronglySelective_example` | `Counterexamples.lean` |
| Theorem 3.6, lower bound (given [18]) | `theorem_3_6_lower`, `theorem_3_6_lower_bits` | `Randomized.lean` |
| Theorem 3.6, upper bound | `theorem_3_6_upper_false` | `ThetaClaims.lean` |
| Theorem 3.7, lower bound (given [18]) | `theorem_3_7_lower`, `theorem_3_7_lower_bits` (`t ≥ (log₂(c log₂ n) − b − 3)/2`); what the paper's argument gives: `theorem_3_7_lower_exp` | `Repair37.lean`, `Randomized.lean` |
| Theorem 3.7, upper bound | `theorem_3_7_upper_false` | `ThetaClaims.lean` |

**Not formalized.** The collision-detection entropy bound (Theorem 2.8), the upper bounds with predicted
distributions (Theorems 2.12, 2.16) and the randomized upper bounds (truncated decay, Willard's search with advice).
Theorem 3.2 (from [5]) and the range-finding Lemmas 2.5 and 2.7 as stated are bypassed, and [18] is a hypothesis.
Lemma 2.7 with its exact factor 2 is neither proved nor refuted: Lean bypasses RF-construction and our repair loses a
constant. Lemma 2.6's constants are loose (it holds as used).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
counterexamples are checked by `decide`. The selective-family lemma is staged in
`Podc/Foundations/Combinatorics/SelectiveFamily.lean` (CSLib candidate). The radio-channel models (`Model.lean`,
`Randomized.lean`) and the Gibbs/guesswork lemma in `EntropyLowerBound.lean` are paper-local CSLib candidates.
