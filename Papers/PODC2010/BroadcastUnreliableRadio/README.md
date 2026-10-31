# Broadcasting in Unreliable Radio Networks — PODC 2010

Fabian Kuhn, Nancy Lynch, Calvin Newport, Rotem Oshman, Andrea Richa. *Broadcasting in Unreliable
Radio Networks.* PODC 2010. DOI [10.1145/1835698.1835779](https://doi.org/10.1145/1835698.1835779).
Formalized version: the full version, MIT-CSAIL-TR-2010-029 (June 2010); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Proof repaired.** All four main results are true as stated:
* Theorem 2 and Theorem 4 (bounds for 2-broadcastable networks);
* Theorem 12 (the `Ω(n log n)` deterministic lower bound for undirected networks);
* Theorem 10 (strong select broadcasts in `O(n^{3/2} √log n)` rounds), with Lemmas 8 and 9;
  the existence of small strongly selective families (Theorem 7, cited from [14]) is taken as a
  hypothesis.

Two proofs need a genuine repair: the case analysis of Claim 13 (Theorem 12) misses some senders,
and the density argument of Theorem 10 breaks down at the source.

## Mistakes in the paper

* **Theorem 10: the threshold round `T` is mis-defined (proof gap, statement true).** The proof
  takes `T` to be the first round with `den(1,T) < ρ`, where `den` counts nodes that get the
  message *for the first time*. It then claims every node has the message by the end of round
  `T`. The source is not counted. If the source's identifier is not in the first set `F_1[1]`,
  nobody sends in round 1, so `den(1,1) = 0` and `T = 1`, and the claim is false.
  * The proof's final contradiction ("`u` received the message for the first time in
    `[T − 1/ρ + 1, T]`, contradicting Lemma 9") also fails when the uninformed node's neighbour
    `u` is the source.
  * Lemma 8's count `P ≤ R` misses the source when `T − 6ℓ'_s < 1`.
  * Fix: count the source as receiving the message in round 1, i.e. use `|inf t| / t` as the
    density. Then `T > 1/ρ`, and Lemmas 8, 9 and the theorem go through with the paper's
    constants and the bound `X = n/ρ`.
  * The Lean illustration uses a 3-node directed path with `s_max = f = 1`, below the paper's
    parameter range. The same failure occurs for every `n` and `s_max` in the paper's range: the
    order of the sets of `F_1` is arbitrary, and some set of an `(n, 2)`-SSF misses the source.
  * The wrong claim sits inside the proof of Theorem 10 (and in the roadmap sentence "we will
    eventually show that the algorithm terminates no later than round `T`"). Theorem 10 itself is
    true. Lemmas 8 and 9 also stay true with the paper's `T` (in Lemma 8, `P ≤ R + 1 ≤ k_s`
    suffices); we prove them for the repaired `T`, which the repaired proof uses.

  (`paper_T_claim_fails`, `Execution.lemma8`, `Execution.lemma9`, `Execution.theorem10`)
* **Theorem 12, Claim 13, Case III: some senders are overlooked (proof gap, statement true).**
  Subcase IIIa asserts that no process outside `A_k ∪ {i₁, i₁'}` sends in round `ℓ + 1`.
  Subcase IIIb asserts that the only such sender is `n₁`. Both ignore the processes removed from the
  candidate set in *earlier* steps, for instance the two `N`-processes dropped in a Case I step.
  `N_{ℓ+1}` only looks at the current candidates `C_ℓ`, and the removed processes may well send.
  * Part 2 of `P(ℓ+1)` still holds, by a uniform argument. Every process outside both candidate
    pairs is in the same state in both executions. In Case III no member of either pair sends.
    So the two executions have the *same* set of senders, disjoint from both pairs, and every
    process in both or neither pair receives the same value.
  * This replaces Subcases IIIa/IIIb.

  (`Algorithm.claim_13`, `theorem_12`)
* Small slips, none affecting the results:
  * Theorem 12 says each stage adds at least `log(n−1) − 2` rounds. Counting the isolated round
    that starts the stage, it adds at least `log(n−1) − 1`; we prove the resulting stronger bound.
  * Theorem 12's proof assigns the new pair to `L_k`; it should be `L_{k+1}`.
  * In Claim 13 Part 1, the cases are called "1, 2(a), 2(b)" instead of I/II/III, and the bound
    ends with `n/2^{ℓ+2}` instead of `(n−1)/2^{ℓ+2}`.
  * Claim 5 (Theorem 4) sums over sets of exactly `n − 2 − k` elements, while the sets `I_k` only
    have at least that many.
  * In Lemma 8's proof, `den(1,T')` should be `den(1,T'−1)`, and the display writes `den(T,T')`
    for `den(T',T)`. `2ℓ'_1 = 8f(2^{s_max} − 1)`, not `8f√(n/log n)`.
  * The proof of Theorem 10 needs SSFs of *exact* size `4^s f` (pad by repetition) for
    `ℓ'_s = 2ℓ'_{s−1}`. The round-robin family `F_{s_max}` needs `4^{s_max} f ≥ n`.
  * "The algorithm terminates by `T`": only delivery by `T` is shown.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* *Lower bounds (Sections 4, 6), `Model.lean`.*
  * Synchronous rounds with synchronous start and collision rule CR1. A process receives `⊥`,
    `⊤` (two or more messages, its own included) or the message.
  * Deterministic algorithms are arbitrary automata indexed by identifiers; any finite identifier
    set of size `n` is allowed. The broadcast message is a black box and is not part of the state.
  * The adversary places processes on nodes (`π : V ≃ I`) and, each round, chooses for every
    message a reach set between the `G`- and the `G'`-out-neighbourhood. It may depend on the
    round and the set of senders, which for deterministic algorithms is as strong as
    history-dependence.
  * A process is *informed* once it receives a message from an informed process. This
    over-approximates "the message arrives", so the lower bounds are, if anything, stronger.
  * Theorem 4: a randomized algorithm is a probability measure over random choices `ω` with a
    deterministic algorithm `A ω`. This covers private coins, and also shared randomness. The
    adversary only picks the placement and then follows the fixed rules of Theorem 2. "Success
    with probability `q`" means the success event contains a measurable event of probability `≥ q`.
* *Upper bound (Section 5), `StrongSelect.lean`.*
  * Directed dual graph, CR4, asynchronous start, global round counter.
  * An execution is any monotone sequence of informed sets starting from the source. The senders
    of each round are computed from the sequence by the strong-select schedule.
  * The only progress guarantee is that a node sending alone informs all its `G`-out-neighbours.
    Every CR4 execution is such a sequence, so the bound covers all adversaries.
  * Parameters `s_max ≥ 1`, `f ≥ 1`, families of exactly `4^s f` sets.
  * The existence of small strongly selective families (Theorem 7, [14]) is a hypothesis.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 2 (incl. 2-broadcastability) | `theorem_2`, `bridgeNet_broadcastable` | `TwoBroadcastable.lean` |
| Claim 3 | `Algorithm.claim_3` | `TwoBroadcastable.lean` |
| Theorem 4 | `theorem_4` | `TwoBroadcastable.lean` |
| Theorem 12 | `theorem_12` (explicit round count `(n−1)/4 · (log₂(n−1) − 1)` for `n = 2^m + 1`), `theorem_12_nlogn` (`k > (n−1) log₂(n−1) / 8`) | `LowerBound.lean` |
| Claim 13 | `Algorithm.claim_13`, `Algorithm.exists_pair` | `LowerBoundCore.lean` |
| Lemma 8 (for the repaired `T`) | `StrongSelect.Execution.lemma8` | `StrongSelectBound.lean` |
| Lemma 9 (for the repaired `T`) | `StrongSelect.Execution.lemma9` | `StrongSelectBound.lean` |
| Theorem 10 | `StrongSelect.Execution.theorem10` (all informed by `12 n f 2^{s_max} = n/ρ`), `StrongSelect.theorem10_asymptotic` | `StrongSelectBound.lean` |
| Gap in the proof of Theorem 10 | `StrongSelect.paper_T_claim_fails` | `StrongSelectExamples.lean` |

Theorem 12 is proved for `n − 1` a power of two (`≥ 4`), as in the paper's proof. Our version is
stronger than the paper's: *every* algorithm has an execution in which some process is still
uninformed after that many rounds.

**Not formalized.**
* Lemma 1: the reduction from explicit-interference graphs (proved in Appendix A of the full
  version); it needs a second network model and is not used by the other results.
* Theorem 11: the `Ω(n^{3/2})` bound for directed networks, adapted from [9].
* Section 7: the randomized `O(n log² n)` algorithm.
* That strong select stops sending.

**Trust.**
* No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
  `Quot.sound`.
* Non-vacuity:
  * the bridge network is shown 2-broadcastable (`bridgeNet_broadcastable`);
  * the hypotheses of Theorem 10 are satisfiable in every network, using round-robin families
    (`theorem10_hyps_rr`);
  * `trivialExecution` is an execution.
* All models are paper-local (namespace `Podc.BroadcastUnreliableRadio`).
* CSLib candidate: the dual-graph radio model with CR1 (`Model.lean`: `DualGraph`, `Algorithm`,
  `Adversary`, `Delivery`, `run`, `informed`, and the transport lemmas
  `toDelivery_fromDelivery`, `run_add`, `informed_of_invariant`).
