# Differences between the formalization and the paper

Paper: Gilbert, Newport, Vaidya, Weaver. *Contention Resolution with Predictions.* PODC 2021,
arXiv 2105.12706v1. Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Statement-level issues

1. **Theorems 3.3 and 3.5 are false if the advice may have variable length** (⚠️, R4, borderline ❌).
   The definition of `b(n)`-non-interactive contention resolution says the advice "contains no more than
   `b(n)` bits", and Theorems 3.4/3.5 say `f` "returns at most `b(n)` bits". If strings of length `< b` are
   allowed there are `2^{b+1} − 1` advice values and:
   * Theorem 3.3 fails for `n = 3`, `b = 1` (advice `ε, 0, 1` names the transmitter;
     `theorem_3_3_false_variable_length`);
   * Theorem 3.5 fails for `n = 9`, `b = 1`, `t = 2` (advice names one of three groups of three players; inside a
     group two rounds with collision detection suffice; `2 < log₂ 9 − 1`; `theorem_3_5_false_variable_length`);
   * Theorem 3.4 survives (its `/2` absorbs the extra bit; our `n ≤ |A| t` gives it for `|A| < 2 n^α`).
   Section 3.1 defines the advice function as `f_A : P(A) → {0,1}^b` (fixed length), and the proof of 3.3 counts
   `2^{b(n)}` strings; under that definition all three theorems are true (`theorem_3_3`, `theorem_3_4`,
   `theorem_3_5`). We classify it as an implied assumption fixed by the paper's own model section (R4) rather than
   ❌; it is borderline because the paper's own proof of 3.5 feeds variable-length strings (`f(P)` plus an
   `(r−1)`-bit history) into Theorem 3.3. With variable-length advice the correct bounds are
   `n ≤ 2^{b+1} − 1`, `n ≤ (2^{b+1} − 1)(2^t − 1)` (`theorem_3_3_card`, `card_le_mul_of_solvesIn_CD` with any
   alphabet).
2. **Upper halves of the `Θ` claims of Theorems 3.6 and 3.7 (and Table 2) fail for long advice** (⚠️, R3).
   Every algorithm needs at least one round, but
   * Theorem 3.6 (`b(n) < log n`, claimed `t(n) = Θ(log n / 2^{b(n)})`): for `b(n) = ⌊log₂ n⌋ − 1`,
     `log n / 2^{b(n)} → 0` (`theorem_3_6_upper_false`);
   * Theorem 3.7 (`b(n) < log log n`, claimed `Θ(log log n − b(n))`): for `b(n) = ⌈log₂ log₂ n⌉ − 1` and
     `n = 2^{2^j+1}`, `log log n − b(n) = log₂(1 + 2^{−j}) → 0` (`theorem_3_7_upper_false`);
   * likewise Table 2's deterministic CD entry `Θ(log n − b)` at `b = log n`.
   The intended bounds are `Θ(1 + ·)`; the paper itself notes the `O(1)` regime `b ≥ log log n` after Theorem 3.7.
   The lower halves are unaffected.

## Proof-level issues (statements true)

3. **Proof of Theorem 3.3.** "`F = {V(s)}` is an `(n, n)`-strongly selective family" is false: correctness only
   gives, for every `P`, *one* `F ∈ F` with `|F ∩ P| = 1` (a selective family), not one for *every* `z ∈ P`.
   Counterexample `n = 2`, one bit: `V(0) = {0}`, `V(1) = {0, 1}` solves the problem but isolates `1` in `{0,1}`
   nowhere (`not_stronglySelective_example`). Theorem 3.2 [5] therefore does not apply. Repair: a family meeting every
   nonempty set in exactly one point has `≥ n` members, by a parity argument over `GF(2)`
   (`Cslib.card_le_of_forall_exists_card_inter_eq_one`). Theorem 3.2 itself (from [5]) is not formalized.
4. **Proofs of Theorems 3.4 and 3.5** go through the (fixed-length) Theorem 3.3 with advice `(f(P), r)` resp.
   `(f(P), history)`; the history has variable length `r − 1`. We count directly: no CD, the transmitter set depends
   on `(advice, round)`: `n ≤ 2^b t` (`theorem_3_4_card`, twice the paper's bound); CD, it depends on
   `(advice, history of length < t)`: `n ≤ 2^b (2^t − 1)` (`theorem_3_5_card`).
5. **Lemma 2.5** (range finding vs entropy) applies the Source Coding Theorem to the code `x ↦ (r, d)` of length
   `log r + log(α log log n) + 1`, which is not uniquely decodable (`r` is written without a delimiter). The lemma is
   still true: the entropy of a positive integer with mean `μ` is at most `log(μ+1) + log e` (geometric maximiser).
   We use a Gibbs inequality with a geometric reference distribution (`sum_negMulLog_le_of_card_fiber_le`).
   Lemma 2.5 itself is not stated in Lean; the Gibbs lemma, applied to the round index of range finding (fibres of
   size `≤ 2α log log n + 1`), gives it.
6. **Lemma 2.7, case 1** argues "if success within the first `μ_i` rounds has probability `< 1/2`, this contradicts
   `μ_i` being the expected time" — mean vs median, not a contradiction (`T = 1` w.p. `0.49`, `T = 2` w.p. `0.51`).
   We replace it by a direct bound: if all rounds before `R` succeed with probability `< ε` and `Rε ≤ 1/2`, then
   `E[T] ≥ (R+1)/2` (Weierstrass product inequality; `UniformAlg.expTime_ge`).
   Lemma 2.7 itself (RF-construction solves range finding in expected time `≤ 2 t_X`) is not formalized: the
   proof of Theorem 2.4 bypasses RF-construction, so the lemma's factor `2` is not checked (the repaired case-1
   bound loses a constant factor).
7. **Proof of Theorem 3.7 (lower bound).** "Simulating `t` rounds of a CD algorithm without CD takes `2^t` rounds,
   so `t < log t'` contradicts Theorem 3.6" uses `E[2^T] ≤ 2^{E[T]}`; Jensen gives the opposite inequality, so the
   simulation only yields `E[2^T] ≥ c log n / 2^b` (`theorem_3_7_lower_exp`). Repair (Markov + independent restarts):
   players draw independent sequences of
   strategies; block `j` simulates the first `2t` rounds of copy `j` (`2^{2t} − 1` no-CD rounds); by Markov a block
   fails with probability `≤ t/(2t+1) ≤ 1/2`, independently over blocks (`pi_infinitePi_map_swap`), so the no-CD
   expected time is `≤ 2^{2t+1}`. Combined with the interleaving: `c log₂ n ≤ |A| · 2^{2t+1}`
   (`theorem_3_7_lower`), i.e. `t ≥ (log₂(c log₂ n) − b − 3)/2` (`theorem_3_7_lower_bits`). This is the paper's bound
   up to a factor 2 and an additive constant, i.e. still `Ω(log log n − b)`.
   The last display also writes `= O(log log n) − b(n)` for what is a lower bound.
8. **Theorem 3.6 lower bound**: "try all `2^b` advice strings in parallel" is made precise by round-robin
   interleaving of independent copies (`interleave`, `expTime_parallel_le`); fine as written.

## Modelling choices

- **[18] as a hypothesis.** The randomized lower bounds (3.6, 3.7) are proved conditionally on
  `NewportBound n c` (every no-advice, no-CD randomized algorithm has a participant set with expected time
  `≥ c log₂ n`), the result of Newport (DISC 2014) that the paper cites; we do not formalize [18]. The hypothesis is
  non-vacuous (`newportBound_of_le_one`).
- **Randomized algorithms** are general (non-uniform, id-dependent, history-dependent with CD): no-CD players draw
  independent transmission schedules `ℕ → Bool` from arbitrary laws (before success every player hears only
  silence, so this is fully general); CD players draw strategies `List Bool → Bool`. Expected times are in `ℝ≥0∞`.
- **Deterministic algorithms** are `advice → common feedback history → id → transmit?`; with collision detection all
  players (transmitters included) see the same collision bit, without it every unsuccessful round is silence — as in
  Section 1.1. Rounds are counted from `0`; "solves within `t` rounds" means success in some round `< t`.
- **Theorem 2.4** (uniform algorithms): success events of different rounds are independent with probability
  `k p_r (1 − p_r)^{k−1}`; we define the survival function as the product of failure probabilities instead of
  building the product probability space. The size distribution is supported on `{2, …, n}` (paper, footnote 4);
  `Ω` is made explicit: `t_X ≥ 2^{H(c(X))} / (88 e log₂ log₂ n)` for all `n ≥ 4` (`theorem_2_4_explicit`). The paper's
  range-finding detour (RF-construction, which also appends `2^j` where `j` is meant) is bypassed by a "guess index"
  on ranges with fibres of size `O(log log n)`.
- **Theorem 3.4** is stated with real `α ∈ (0,1)` and `b ≤ α log₂ n`; it holds for every `n`, not only
  asymptotically.

## Upper bounds (tightness claims)

- No CD, `b` bits: `⌈n / 2^b⌉` rounds (`upper_noCD`), exactly matching `n ≤ 2^b t`. The paper's construction text says
  "only `n/q = n/2^{α log n}`" (typo for `n/2^q`).
- CD, `b ≤ ⌈log₂ n⌉` bits: `⌈log₂ n⌉ − b + 1` rounds by advice-prefixed binary search (`upper_CD_clog`), as in the
  paper.
- Randomized upper bounds (truncated decay, Willard's search with advice) and Theorems 2.8, 2.12, 2.16 are not
  formalized.
