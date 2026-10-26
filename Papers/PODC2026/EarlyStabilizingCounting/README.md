# Early-Stabilizing Counting — PODC 2026

Christoph Lenzen, Julian Loss. *Early-Stabilizing Counting.* PODC 2026. DOI
[10.1145/3796701.3815925](https://doi.org/10.1145/3796701.3815925). Formalized version: arXiv
[2605.18171](https://arxiv.org/abs/2605.18171) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** Theorem 5.7 and Corollary 5.8 are verified end to end, after
an off-by-one fix in Algorithm 1. The result: a deterministic self-stabilising `C`-counter
tolerating `f < n/3` Byzantine faults that stabilises in `O(f + 1 + log n)` rounds, a bound that
depends on the actual number of faults `f`. We get explicit constants, `120 f + 113⌈log₂ n⌉`,
for the recursion over Algorithm 8 (filtering) and Algorithm 10 (King Consensus). As printed,
Algorithm 1 never counts: line 3 starts King Consensus with input `C_v + R`, but the paper's own
timing conventions require `C_v + R − 1`. The proof of Lemma 2.3 uses Algorithm 8, which gives
crusader agreement over one round fewer than Definition 2.2 asks. Lemmas 5.5 and 5.6 and Corollary 5.8
have proof gaps; their statements are true. The 8-round King Consensus of Section 6.1 (Theorem 6.5) is
verified, including its message-count property. **The headline Theorem 1.1 (`O(f + 1)` stabilisation,
Section 7) is not formalized**, and neither are message sizes or the bit-complexity results of
Section 6.2.

## Mistakes in the paper

* **Algorithm 1 as written never counts (false for the literal pseudocode; one-symbol fix).**
  In Algorithm 1, line 3 starts an instance and the loop of lines 4–9 runs its round 1 in the same
  round (Section 4: round 1 is computed from the input), so an `R`-round instance whose input is
  read from `C_{v,r−1}` outputs in round `r + R − 1`. Line 7 then overwrites `C_v` with the output
  and line 15 increments it. Once the clocks agree, the next instance whose correct leader is agreed
  upon outputs the agreed input `C_{v,r−1} + R`, so `C_{v,r+R−1} = C_{v,r−1} + R + 1`: the clock
  jumps by 2 in one round. Such instances recur every `k_b` rounds. This is not a question of how
  rounds are labelled: between reading the input and writing the output there are `R` updates of
  `C_v`, while the proof of Lemma 5.4 ("outputs in round `r + R`") needs `R + 1`. The paper's own
  Lemma 5.6 (`J_ℓ` has `R` rounds) and Algorithm 7, line 19 (input `C_v + R − 1`, read after the
  increment) use the correct timing; Algorithm 7, line 2 repeats the slip (Section 7 is not
  formalized). We prove that no fault-free execution of the literal algorithm ever stabilises (any
  `n ≥ 2`, `C ≥ 2`, any early-stabilizing sub-counters; the trace-level argument does not depend on
  `k₀`, `k₁`, `X`). With input `C_v + R − 1` everything goes through. (`literal_breaks`,
  `literal_never_counts`, `literal_counterexample`; fixed: `tmpl 2`)
* **Lemma 2.3: Algorithm 8 does not meet Definition 2.2 (proof error; nothing downstream
  breaks).** Lemma 2.3 is proved by Algorithm 8. Definition 2.2 asks consistency for
  `r̂ ∈ {r', …, r' + X}`, i.e. `X + 1` rounds. Algorithm 8 resets the cooldown to `X`, which gives only `X` rounds. Counterexample: `n = 4`, one
  Byzantine node, `X = 1`, `K = 2`. The Byzantine node completes an `n − t` quorum for node 0 but
  not for node 1 in round 3. Node 0 outputs `1` at time `3 = X + 2`, and node 1 outputs `1` at time
  4, where only `⊥` or `0` are allowed. The window `X − 1` holds (`filt_crusader`). Lemma 5.6 only
  uses windows shorter than `X`, so nothing downstream breaks. Lemma 2.3 is an existence claim; we do
  not refute it for other algorithms. (`filt_crusader_window_false`)
* **Lemma 5.5: wrong constants in the proof (proof gap; the statement is true).** With
  `k₀ = ⌈(R+1)/ε⌉` and `k₁ = k₀ + R + 1`, the claim that the `⌈1/ε⌉ − 1` values after a collision
  are collision-free fails. For example `ε = 2/3`, `R = 1`, `b = 1`, `o = 0`: both `L = 0` and
  `L = 1` collide, and `2 > ε·1 + 1`. The choice `k₀ = (R+1)⌈1/ε⌉` works. It coincides with the
  paper's choice for `ε = 1/4`, the only value used. (`lemma_5_5_proof_constants_fail`,
  `lemma_5_5`)
* **Lemma 5.6: incomplete counting (proof gap; the statement is true for all `n` and the unmodified
  algorithm).**
  * "`L_max > 4`" is false for the larger `k_b`, where `L_max = 4`.
  * The choice of `i₀` needs `n` large: no clock overflow during an interval, and fresh leaders.
    Footnote 8 admits this and proposes changing the clocks to `m k_b n` for small `n`.
  * We give a different argument that works for all `n` without changing the algorithm. Group
    consecutive `b`-instances in blocks of 4. By Lemma 5.5 at most one per block collides with the
    other schedule. A faulty node occurs at most `⌊4(f+1)/n⌋ + 1` times among the first `4(f+1)`
    consecutive leaders (mod `n`), so one of the first `f + 1` blocks has an unimpeded instance.
  (`lemma_5_6`)
* **Corollary 5.8 recursion step (proof gap).** "One of `V₀`, `V₁` contains at most half of the
  faults" does not give the hypothesis `f_b < |V_b|/3` of Theorem 5.7 for that part. Example:
  `n = 7`, parts of size 3 and 4, one fault each. For the balanced partition some part satisfies
  both `3f_b < |V_b|` and `2f_b ≤ f`, and that suffices. (`exists_good_side`)
* **Notation.** In Lemmas 5.1, 5.6 and Theorem 5.7, "`f < |V_b|/3`" means the number of faults
  *inside* `V_b`. Read with `f` the total, the first statement's proof ("`f < n/3`, so
  `f < |V_b|/3` for some `b`") is false.
* **Typos:**
  * Definition 2.2: `F_{v,r̂}` should be `F_{v,r'}`.
  * Lemma 5.2: the interval `[r₀+iX, r₀+i(X+1)−1]` should be `[r₀+iX, r₀+(i+1)X−1]`.
  * Algorithm 5, line 25: `:= C` should be `:= c`.
  * Lemma 6.6: `D_{v,r}` should be `N_{v,r}`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's self-stabilising Byzantine state-broadcast model
  (`Cslib/Computability/Distributed/Byzantine/SyncCounting/Model.lean`): complete network on
  `Fin n`, synchronous lock-step rounds, deterministic algorithms, and **arbitrary initial
  states**.
* A static set `F` of Byzantine nodes with `3|F| < n` (`f ≤ t = ⌊(n−1)/3⌋`) sends arbitrary,
  receiver-dependent states. The algorithm does not know `f`.
* State spaces are not required to be finite (clock values are stored as natural numbers and read
  modulo `C`), so the paper's bounded-memory requirement is not checked; the algorithm never relies
  on large stored values.
* Each round every node sends its state. By the paper's Section 4 convention every message is a
  function of the sender's previous state, so this captures the algorithms exactly, but message
  size is not modelled.
* `IsESCounter A T`: every execution with `|F| = f`, `3f < n`, stabilises within `T f` rounds.
* The algorithm (`tmpl`) is Algorithm 1 with:
  * a balanced partition and sub-counters modulo `k_b n`;
  * Algorithm 8 filtering with `X = 48`;
  * two pipelines of Algorithm 10 King Consensus (`R = 3`, Algorithm 9 graded agreement inside);
  * constants `k₀ = 12`, `k₁ = 15`;
  * our input `C_v + 2` instead of `C_v + 3` (the fix above).
* The combinatorial core (Lemmas 5.2, 5.4, 5.6, Theorem 5.7) is proved at the level of traces
  (`TraceHyp`) for any number of King Consensus rounds `D` and any crusader window
  `W ≥ 16D − 1`. It is then instantiated with the concrete algorithm.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 2.1, 2.2 (crusader part), 2.6 | `CountsFrom`, `OCountsFrom`, `Crusader`, `KCSpec` | `Basic.lean` |
| Lemma 2.3 (Algorithm 8): validity, `S = X+2` | `filt_validity` | `Filtering.lean` |
| Lemma 2.3: crusader agreement (window `X − 1`) / window `X` false | `filt_crusader` / `filt_crusader_window_false` | `Filtering.lean` |
| Lemma 2.5 (Algorithm 9), Lemma 2.7 (Algorithm 10) | `ga_spec`, `kc_spec` | `KingConsensus.lean` |
| Lemma 5.1 | `lemma_5_1` | `Algorithm.lean` |
| Lemma 5.2 (virtual clock) | `lemma_5_2` | `Template.lean` |
| Lemma 5.4 | `lemma_5_4` | `Template.lean` |
| Lemma 5.5 / proof constants fail | `lemma_5_5`, `collides_sep` / `lemma_5_5_proof_constants_fail` | `Lemma55.lean` |
| Lemma 5.6 | `lemma_5_6` | `Template.lean` |
| Theorem 5.7 (trace level; concrete, both statements) | `theorem_5_7_trace`; `theorem_5_7`, `theorem_5_7_max` | `Template.lean`, `Algorithm.lean` |
| Corollary 5.8 (time `120 f + 113⌈log₂ n⌉`) | `corollary_5_8` | `Recursion.lean` |
| Lemma 6.2 (Algorithm 2), Lemma 6.4 (Algorithm 3), Theorem 6.5 (Algorithm 4): correctness | `WGARun.spec`, `wga_silent`, `GKCRun.spec`, `KC8Run.spec` | `KingConsensus8.lean` |
| Lemma 6.4 / Theorem 6.5: with agreed inputs and a non-faulty leader, every correct message is sent by `ℓ`, to `ℓ`, or to a faulty node; `≤ 8n(f+2)` messages | `GKCRun.sparse`, `KC8Run.sparse`, `KC8Run.card_sent_le` | `KingConsensus8.lean` |
| Algorithm 1 with input `C_v + R` never counts | `literal_never_counts`, `literal_counterexample` | `Literal.lean` |

`corollary_5_8 n C : 1 ≤ n → 1 ≤ C → ∃ X (nonempty) A : Algorithm (Fin n) X C,
IsESCounter A (fun f => 120 * f + 113 * Nat.clog 2 n)`.

Section 6.1 is checked separately, in a per-link message model where a node may send nothing and
may send different messages to different receivers. We found no error there.

**Not formalized.**
* Message sizes and bit complexity, except the message counts of Theorem 6.5.
* Section 6.2 (Algorithm 5).
* Section 7 (Theorem 1.1, `O(f + 1)` via unbalanced recursion and expanders).
* The optimality claim, which rests on cited consensus lower bounds.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The algorithm has a nonempty state space, and fault-free executions exist from every
initial state (`run`, `literal_exists_exec`), so the counting statements are not vacuous. The
model comes from CSLib (`Cslib.Byzantine.SyncCounting`). Everything else is proved here: the
subroutines (Algorithms 8–10) are verified, not assumed.

**Shared infrastructure.** `cnt` is `Finset.countEq` (`Cslib/Foundations/Data/Finset/Quorum.lean`), quorum
intersection is `Cslib.Quorum.exists_mem_inter_notMem_of_three_mul_lt` (`Cslib/Foundations/Data/Finset/Quorum.lean`).
The computable selectors of Algorithm 8 are the library ones: `majT_eq_majority?` (`Finset.majority?`),
`quorum_eq_threshold?` (`Finset.threshold?` with threshold `n - t`).
The conclusion of `ga_spec` is binary graded consensus (`ga_gradedConsensus`:
`Cslib.Byzantine.Problem.GradedConsensus`, `Cslib/Computability/Distributed/Byzantine/Specs.lean`), and the king steps of `kc_spec` and
`KC8Run.spec` are `Cslib.Byzantine.kingPhase_agreement` (`Cslib/Computability/Distributed/Byzantine/KingPhase.lean`).
