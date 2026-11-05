# Differences between the formalization and the paper

J. Aspnes, *A modular approach to shared-memory consensus, with applications to the probabilistic-write
model*, PODC 2010; full version of May 14, 2011 (author's copy, 18 pp.). The erratum note (ratifiers =
Gafni's adopt-commit objects) is a credit fix with no technical content.

## Model and definitions

- **Shared memory model.** Procedure AdoptCommit (Theorem 8, Section 6) is formalized in CSLib's asynchronous
  shared-memory model (`Cslib.SharedMemory.Impl`): deterministic processes, any type `P` of processes (finite or
  infinite, "unbounded number of processes"), atomic multi-writer registers, arbitrary interleavings. Crashes are
  processes that stop taking steps; every safety property is proved for every finite, possibly partial, one-shot
  execution (`Impl.Solves`), which covers crashed and still-running processes. Termination is CSLib's
  wait-freedom (`Impl.WaitFree`). Returning is a separate (non-memory) step, as in CSLib.
- **Line 10 reads with early exit.** Procedure AdoptCommit reads the registers of `R_preference` one at a time
  (in `Finset.toList` order) and stops at the first `1`. The paper only says "if `rᵢ ≠ 0` for some
  `rᵢ ∈ R_preference`". Reading the remaining registers would not change the outcome; the step bound uses the
  worst case (all of `R_preference` read).
- **Specifications as input/output relations.** Validity, coherence, convergence and agreement are predicates on
  the inputs `P → Option V` and outputs `P → Option (Decision × V)` of a (possibly partial) execution
  (`Basic.lean`). Convergence for partial executions reads "if all inputs (of the processes that invoked the
  object) equal `v`, every output given is `(commit, v)`", which is the paper's property applied to every prefix.
- **Composition (Section 3.3)** is formalized twice:
  - relationally (`DObj.seq`): an execution of `(X; Y)` is an execution of `X` plus an execution of `Y` whose
    participants are processes that adopted from `X`, with the adopted value as input. Lemmas 1 and 3 and
    Theorem 4 (validity + coherence) are proved for this relation. Associativity (`seq_assoc`) needs the middle
    object to be well-formed (only processes that invoked it get an output), which every real execution is;
  - operationally, as a CSLib `Impl` built from two `Impl`s (`Impl.seqComp`,
    `Podc/Computability/Distributed/SharedMemory/SeqCompose.lean`): every valid one-shot execution of the composite
    projects to valid one-shot executions of the components (`seqComp_project`, assuming `Y` allows every input it
    can receive), so its input/output pair lies in `DObj.seq` (`ComposeBridge.seqComp_mem_seq`) and Lemmas 1, 3 and
    Theorem 4 transfer (`seqComp_solves_weakConsensus`). Only one-shot executions are projected.
- **Termination of compositions (Lemma 2)** is deterministic wait-freedom with additive step bounds, for
  components whose termination is witnessed by a potential (strictly decreasing at each access; bounded after
  invocation for `Y`) (`seqComp_waitFree`, `seqComp_tauSteps_le`). A general `WaitFree X → WaitFree Y →
  WaitFree (X; Y)` would need projecting infinite executions and is not proved. The probabilistic "terminates
  with probability 1" of randomized components is not modelled at the level of objects (see below).
- **Wait-freedom of AdoptCommit** is proved under a uniform bound `ρ` on the read-quorum sizes (always true for
  finitely many values, and for all quorum systems of Section 6.2). With infinitely many values of unbounded
  quorum sizes each operation still finishes, but CSLib's potential method needs a uniform natural-number bound.
  The paper's "Termination is immediate from the lack of unbounded loops" implicitly assumes finite quorums.
- **Infinite consensus chain `U` (Section 4.1)** is formalized relationally (`ChainExec`): one execution per stage,
  linked by the adopt values. Safety (validity, agreement) is proved for any chain of weak consensus objects.
- **Probability in Section 4 is abstract.** The paper's argument "with probability 1, some `Cᵢ` eventually produces
  agreement" and `E[T(U)] ≤ 2T(A) + (1/δ)(T(C)+T(A))` are formalized as: (deterministic) if the outputs of a
  conciliator stage agree and the next stage is convergent, nobody reaches the following stage
  (`no_next_of_agreement`); (probabilistic, `stages_prob`, `expected_cost_le`, `expected_cost_bounded_le`) if
  `Pr[reach stage k+1] ≤ (1-δ)·Pr[reach stage k]`, then termination has probability 1, the expected number of
  stages is `≤ 1/δ`, and the expected cost bound holds. The hypothesis `Pr[reach k+1] ≤ (1-δ) Pr[reach k]` is the
  step the paper leaves informal: it needs the conciliator's agreement guarantee to hold *conditionally on the
  history at the moment its first participant arrives*, against an adversary that also controls the arrivals.
  This is the natural reading of "for any adversary strategy" but no probabilistic execution model of objects is
  built here. (No error: just not formalized at this level.) Consequences, made explicit in the README:
  - The hypothesis is **not discharged** for any concrete conciliator. Discharging it for Theorem 7's conciliator
    would need (a) a probabilistic semantics of the composed protocol and (b) Theorem 7 with *adaptively chosen*
    inputs: in `U`, a late process's input to `Cᵢ` is its adopted value from `Aᵢ₋₁`, which the adversary can steer
    after seeing coins of `Cᵢ`. `agreement_prob` fixes the inputs up front. (The potential argument does not
    depend on the inputs, so this extension is expected to go through; the paper does not discuss it.)
  - The cost hypothesis `hT` bounds the cost of each stage by *constants* `T(A)`, `T(C)` pointwise. This covers
    worst-case measures (individual work of Theorem 7's conciliator, `2⌈lg n⌉ + 5`) but not stage costs that are
    bounded only in expectation (the `O(n)` expected total work of Theorem 7), for which a Wald-type argument
    would be needed. So the "expected total work" half of Theorem 5 is covered only for conciliators with a
    worst-case total-work bound.
  - The abstract's combined consensus bound for the probabilistic-write model (`O(log m + log n)` individual,
    `O(n log m)` total work) is therefore not formalized end to end.
- **Theorem 5** is covered by `expected_cost_bounded_le` (fallback term `(1-δ)^(k+1) T(K)`, slightly better than
  the paper's `(1-δ)^k T(K)` because the stages are counted from `A₋₁`) and `exists_k_fallback_le_one`
  (`k = ⌈ln M / δ⌉` makes the fallback term `≤ 1` when `T(K) ≤ M`, so `k = O(log n)` for polynomial `T(K)`).
  The "bounded space" part is immediate (finitely many objects) and not stated separately.
- **Fast path (Sections 4.1.1, 4.2).** The indistinguishability argument "p cannot distinguish this execution from
  one in which all processes have the same input" is formalized as: the prefix ending with `p`'s response is an
  execution in which all inputs are `v`; convergence applies to it (`fastPath`, for every implementation of an
  adopt-commit object in CSLib's model).

## Theorem 7 (ImpatientFirstMoverConciliator)

- Separate model (`ImpatientConciliator.lean`): one register `Option V`, `n ≥ 1` processes `Fin n`, every step
  one register operation; the coin of a write attempt is flipped when the step is taken; executions are `PMF`s of
  `N` adversary decisions (`run`). The adversary is an arbitrary function of the history (scheduled processes and
  the outcomes of all coins already flipped) and of the configuration, and may idle (crash processes). This is at
  least as strong as the paper's location-oblivious adversary, so the agreement bound is a stronger statement.
- Agreement is stated for the processes that have returned after `N` steps, for every `N` (the paper's "all return
  values are equal").
- Proof: a potential-function (submartingale) argument instead of the paper's "all-failures path" with index
  `t`; it covers the cases the paper's text does not mention (`t` need not exist if the adversary stops; the
  `min 1` cap on `2^k/(2n)`). The paper's estimates are `attemptProb_le_sum`, `one_sub_sum_le_prod`.
- Expected total work: the explicit bound `7n` (paper: `O(n)`).

## Statement-level remarks (no verdict impact)

- **Section 5.2, iteration count.** "the loop is never executed for more than `⌈lg n⌉ + 1` iterations": the write
  probability `2^k/(2n)` reaches `1` only at `k = ⌈lg n⌉ + 1`, so there can be `⌈lg n⌉ + 2` iterations
  (`k = 0, …, ⌈lg n⌉ + 1`). The paper's final bound `2⌈lg 2n⌉ + 3 = 2⌈lg n⌉ + 5` counts `⌈lg n⌉ + 2` iterations
  and is correct. A slip in an intermediate sentence (R1/R3: not a statement; listed under "Typos and slips").
  *Borderline call (R6).* The sentence is the paper's proof of Theorem 7's work bound ("The bounds on individual
  work and total work have already been established"), so by R1 it is proof-internal, not a statement (else it
  would be ⚠️ by R3). It is not counted as a proof repair (🛠️) because nothing needs repairing: the very next
  formula `2⌈lg 2n⌉ + 3` is exactly `2·(⌈lg 2n⌉ + 1) + 1`, i.e. the proof already computes with the correct count
  `⌈lg 2n⌉ + 1`, and `⌈lg n⌉ + 1` is a typo for it (`lg n` for `lg 2n`).
- **Theorem 10 for `m = 1`.** "`O(log m)` registers and `O(log m)` individual work" is literally `O(0)` for
  `m = 1`, while every implementation needs at least one operation. Degenerate (R2); we state exact bounds
  `2⌈lg m⌉ + 1` registers and `2⌈lg m⌉ + 2` operations.
- **Abstract: "`lg m + Θ(log log m)` space and individual work".** We prove the upper bound
  `k ≤ ⌈lg m⌉ + ⌈lg(2⌈lg m⌉ + 2)⌉` for the middle-layer construction (`exists_k_le`) and its optimality among
  all quorum systems with `|W_v| + |R_v| ≤ k` (`card_le_choose_of_quorums`, from Theorem 9). The matching lower
  bound `C(k,⌊k/2⌋) ≤ 2^k/√k`-type estimate behind the `Θ` is not formalized.
- **Section 6.1 prose.** "This works as long as for every two distinct values `v` and `v'`, `R_{v'}` includes some
  register written in `W_v` that is not written in `W_{v'}`" is a different (and, without `W_v ∩ R_v = ∅`,
  insufficient) condition than the hypothesis of Theorem 8; we follow Theorem 8.
- **Theorem 9** is cited from Jukna; we prove it (`Cslib.SetPairs.sum_inv_choose_le_one`) together with the
  optimality corollary and its tightness.

## Not formalized

- Theorem 6 (CoinConciliator from a weak shared coin). The paper notes it gives no new result. Its proof is
  correct in substance, with one point a careful proof must make explicit: every "skip" decision (reading `0` from
  `r_¬v`) happens before the first process enters the shared coin (both `r₀`, `r₁` are set by then), so the skip
  value is fixed before the coin's randomness is used, which is what lets the coin's `δ`-bound apply to it.
- Section 4.2 (noisy / priority-based schedulers), Section 6.2 item 4 (cheap-collect model).
