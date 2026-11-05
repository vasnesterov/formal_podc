# A Modular Approach to Shared-Memory Consensus — PODC 2010

James Aspnes. *A modular approach to shared-memory consensus, with applications to the probabilistic-write model.*
PODC 2010. DOI [10.1145/1835698.1835802](https://doi.org/10.1145/1835698.1835802). Formalized version: the
author's full version of May 14, 2011 (18 pp., with proofs; no arXiv version); numbering follows it. The author's
erratum (ratifiers are Gafni's adopt-commit objects) only fixes credit. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** Every checked result holds as stated: the composition lemmas (Lemmas 1–3,
Theorem 4), the safety of the conciliator/adopt-commit consensus construction, the multi-valued adopt-commit
object (Theorems 8 and 10), the quorum optimality via Bollobás's theorem (Theorem 9) and the new
probabilistic-write conciliator (Theorem 7: agreement probability `(1 − e^{−1/4})/4`, `2⌈lg n⌉ + 5` individual
work, `O(n)` expected total work). The probabilistic part of Section 4 (termination with probability 1, the
expected-cost bound, Theorem 5) is checked only *conditionally*: the per-stage bound "a reached conciliator fails
with probability `≤ 1 − δ`" is a hypothesis, not derived from Theorem 7 (see **Model**). The only slip is a typo in
an intermediate sentence of Section 5.2; the paper's final bound is right.

## Mistakes in the paper

No mistakes in the statements.

### Typos and slips
- §5.2: "the loop is never executed for more than `⌈lg n⌉ + 1` iterations" should be `⌈lg n⌉ + 2` (`= ⌈lg 2n⌉ + 1`):
  the write probability `2^k/(2n)` reaches 1 only at `k = ⌈lg n⌉ + 1`. For `n = 1` the loop runs twice
  (`attempts_tight`). The paper's bound `2⌈lg 2n⌉ + 3 = 2⌈lg n⌉ + 5` uses the right count and is attained.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Adopt-commit objects (Theorems 8 and 10) use CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`).
  Processes are deterministic and there may be any number of them, even infinitely many. Memory consists of atomic
  multi-writer registers, and the scheduler chooses an arbitrary interleaving. A crash is a process that stops taking
  steps. Safety (validity, coherence, convergence) is proved for every finite, possibly partial, one-shot execution
  (`Impl.Solves`). Termination is CSLib's wait-freedom, and individual work is the number of register accesses of an
  operation.
* Deciding objects and composition (Section 3) are modelled by the input/output pairs of their executions
  (`DObj`). Executions may be partial; inputs are `P → Option V` and outputs `P → Option (Decision × V)`. `(X; Y)`
  combines an execution of `X` with an execution of `Y` whose participants adopted from `X`. Composition is also
  built operationally on CSLib `Impl`s, together with a projection theorem (`SeqCompose.lean`, `ComposeBridge.lean`).
* Theorem 7 (probabilistic-write model) uses a separate model with one register `r : Option V` and `n` processes.
  The `k`-th write attempt of a process takes effect with probability `min 1 (2^k/(2n))`. The coin is flipped when
  the scheduled write step is taken. The adversary is any function of the full history, including all coins flipped
  so far, and of the current configuration. It may also idle or stop processes. This is at least as strong as the
  paper's location-oblivious adversary. Executions are Mathlib `PMF`s.
* The probabilistic termination of the consensus construction (Section 4) is formalized abstractly. The deterministic
  part is proved for executions: if a conciliator's outputs agree, every process commits in the next adopt-commit
  object. The probabilistic part is a lemma about measures. It assumes that a reached conciliator stage fails with
  probability at most `1 − δ` (`μ(E (k+1)) ≤ (1 − δ) μ(E k)`) and that the cost of an execution is bounded
  stage-wise by constants `T(A)`, `T(C)`, and derives termination with probability 1, at most `1/δ` expected
  stages, and the cost bounds. No probabilistic semantics of composed randomized objects is built, so these
  hypotheses are *not* discharged for any concrete conciliator, in particular not for Theorem 7's (whose
  agreement bound is proved for a single, stand-alone instance with fixed inputs). Theorem 5 and the Section 4.1
  termination claim are therefore verified only modulo this step, which the paper also treats informally.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (validity preserved) | `DObj.validity_seq` | `Basic.lean` |
| Lemma 2 (termination preserved; deterministic wait-freedom, additive step bounds) | `Cslib.SharedMemory.Impl.seqComp_waitFree`, `Impl.seqComp_tauSteps_le` | `Podc/…/SharedMemory/SeqCompose.lean` |
| Composition as a shared-memory implementation; its executions lie in `DObj.seq` | `Impl.seqComp`, `Impl.seqComp_project`, `seqComp_mem_seq`, `seqComp_solves_weakConsensus` | `SeqCompose.lean`, `ComposeBridge.lean` |
| Lemma 3 (coherence preserved) | `DObj.coherence_seq` | `Basic.lean` |
| Theorem 4 (weak consensus preserved) | `DObj.isWeakConsensus_seq` | `Basic.lean` |
| Associativity of composition | `DObj.seq_assoc` | `Basic.lean` |
| Remarks: converse of Lemma 1 fails; Lemma 3 needs `Y` valid | `DObj.validity_seq_converse_false`, `DObj.coherence_seq_needs_validity` | `Basic.lean` |
| §4.1 `U` is safe (validity, agreement) | `ChainExec.validity`, `ChainExec.agreement` | `Consensus.lean` |
| §4.1 agreement of `Cᵢ` ⇒ all commit in `Aᵢ` | `ChainExec.no_next_of_agreement` | `Consensus.lean` |
| §4.1 fast path `A₋₁; A₀`, §4.2 | `fastPath`, `fastPath_acImpl`, `ChainExec.no_next_of_commit` | `FastPath.lean`, `Consensus.lean` |
| §4.1 termination w.p. 1, `E[T(U)] ≤ 2T(A) + (1/δ)(T(C)+T(A))` (conditional: per-stage failure bound and per-stage cost bound are hypotheses) | `stages_prob`, `expected_cost_le` | `Consensus.lean` |
| Theorem 5 (bounded construction, `k = O(log n)`; conditional as above) | `expected_cost_bounded_le`, `exists_k_fallback_le_one` | `Consensus.lean` |
| Theorem 7 (agreement `≥ (1−e^{−1/4})/4`) | `Impatient.agreement_prob` | `ImpatientConciliator.lean` |
| Theorem 7 (individual work `2⌈lg n⌉+5`, total work `≤ 7n`, validity, coherence) | `Impatient.individual_work`, `Impatient.expected_total_work`, `Impatient.validity`, `Impatient.coherence` | `ImpatientConciliator.lean` |
| Theorem 8 (AdoptCommit: validity, coherence, convergence; termination) | `AC.theorem8_safety`, `AC.theorem8_solves`, `AC.theorem8_waitFree`, `AC.steps_le` | `AdoptCommit.lean` |
| "a process can only commit its own input" (proof of Thm 8) | `AC.commit_eq_input` | `AdoptCommit.lean` |
| §6.2 binary: 3 registers, ≤ 4 operations | `AC.binary_adoptCommit`, `AC.binary_registers`, `AC.binary_steps` | `Quorums.lean` |
| §6.2 middle-layer quorums, `k = lg m + O(log log m)` | `AC.mid_hWR`, `AC.mid_steps`, `AC.exists_k_le` | `Quorums.lean` |
| Theorem 9 (Bollobás) | `Cslib.SetPairs.sum_inv_choose_le_one` | `Podc/Foundations/Combinatorics/SetPairs.lean` |
| §6.2 optimality of the quorums (and tightness) | `AC.card_le_choose_of_quorums`, `Cslib.SetPairs.exists_card_eq_choose_half` | `Quorums.lean`, `SetPairs.lean` |
| Theorem 10 (`2⌈lg m⌉+1` registers, `2⌈lg m⌉+2` operations) | `AC.theorem10` | `Quorums.lean` |

**Proof remarks.**
* Theorem 8. The paper's timing argument is right. We prove it with an invariant on configurations, `AC.Inv`.
  Its key clause is `Inv.k2`: suppose `p` is executing line 10 with preference `v` and has read a set `S ⊆ R_v` of
  registers as 0. Then no process with input `≠ v` that read `⊥` from `proposal` has a register of `S` in its
  write quorum. Once `S = R_v`, the hypothesis `W_w ∩ R_v ≠ ∅` for `w ≠ v` shows that every writer of `proposal`
  has input `v`. Termination needs finite (in Lean: uniformly bounded) quorums, which the paper takes for granted.
* Theorem 7 is proved with a potential function (a submartingale) instead of the paper's "all-failures path"
  argument. This avoids the cases the paper skips: the index `t` with `∑_{i ≤ t} pᵢ ≥ 1/4` may not exist, because
  the adversary may stop scheduling, and the `min 1` cap in `2^k/(2n)`. The paper's two estimates appear in the
  proof as `attemptProb_le_sum` and `one_sub_sum_le_prod`.
* Section 4. The paper's "with probability 1 some `Cᵢ` produces agreement" requires each conciliator's
  `δ`-guarantee to hold conditionally on the history at the moment its first participant arrives. Its
  "for any adversary strategy" naturally covers this, but we keep it as the hypothesis of `stages_prob`.

**Not formalized.** Theorem 6 (CoinConciliator from a weak shared coin; "does not give any new results"), the
noisy/priority schedulers of §4.2, the cheap-collect variant (§6.2 item 4), the `Θ` lower bound in the
abstract's "`lg m + Θ(log log m)`" (the upper bound and the optimality among quorum systems are proved), and the
abstract's end-to-end consensus bound for the probabilistic-write model (`O(log m + log n)` individual work,
`O(n log m)` total work): it combines Theorems 7 and 10 through Section 4, whose probabilistic step is only
assumed (see **Model**).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: concrete executions of the binary AdoptCommit, one committing and one adopting (`Quorums.lean`);
the bit-vector and middle-layer quorums satisfy the hypothesis of Theorem 8 (`bit_hWR`, `mid_hWR`); the
middle-layer family attains Bollobás's bound; for Theorem 7, an adversary under which disagreement has positive
probability (`Impatient.disagreement_prob_pos`). Model: CSLib `Cslib.SharedMemory` (`Impl`, `Task`, `Potential`).
CSLib candidates: `Podc/Foundations/Combinatorics/SetPairs.lean` (Bollobás's theorem),
`Podc/Computability/Distributed/SharedMemory/SeqCompose.lean` (sequential composition of task implementations),
and the PMF helpers `one_sub_sum_le_prod`, `tsum_bind_mul`, `tsum_pure_mul` in `ImpatientConciliator.lean`.
