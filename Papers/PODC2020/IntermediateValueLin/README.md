# Intermediate Value Linearizability — PODC 2020

Arik Rinberg, Idit Keidar. *Brief Announcement: Intermediate Value Linearizability: A Quantitative
Correctness Criterion.* PODC 2020. DOI [10.1145/3382734.3405712](https://doi.org/10.1145/3382734.3405712).
Formalized version: arXiv [2006.12889](https://arxiv.org/abs/2006.12889) v1 (full version). Numbering
follows it.

**Verdict: 🛠️ Proof repaired.** All results hold: locality of IVL, Theorem 1 (IVL preserves
`(ε, δ)` error bounds), Lemma 1 (the concurrent CountMin sketch is IVL), Lemma 2 and Theorem 2 (an IVL
batched counter with `O(1)` updates), Lemmas 3 and 4, the claim that PCM is not linearizable, and
Theorem 3 (the `Ω(n)` bound for linearizable batched counters). Theorem 3 is proved **conditionally**:
the cited Israeli–Shirazi lower bound for snapshots from SWMR registers is not formalized and enters as
the hypothesis `ISLowerBound`. The locality proof (Appendix A) has a gap, and the witness execution of
Example 2 is not well formed (one process has two operations pending at once); both are easy to repair.
There are also several typos in proofs.

## Mistakes in the paper

* **Locality (Appendix A), gap in the proof; the statement is true.** To build a global linearization,
  the proof takes the union of the per-object linearization orders and the real-time order. It then
  asserts this is "a well defined partial order" because the per-object orders respect real time and
  are disjoint. That union is not transitive. The real work, as in Herlihy–Wing's locality proof, is
  showing that its transitive closure is acyclic, since cycles may alternate between objects and
  real-time edges. Our proof uses CSLib's merge of per-object linearizations by explicit linearization
  points, which proves exactly this step. Typo: "`H₂` of `H 2`" should be "of `H?`".
  (`HW.ivl_locality`)
* **Example 2, the witness that PCM is not linearizable, is not a well-formed execution; the claim is
  true.** The paper claims (abstract, introduction, and the sentence before Example 2) that PCM is not
  linearizable, and Example 2 with its proof by contradiction is the demonstration. Process `p`
  invokes `U = update(a)`, which stalls. Then "process `p`" invokes `Q₁ = query(a)` and
  `Q₂ = query(b)` while `U` is still pending. Well-formedness (Section 2.1) forbids this. With a second
  process issuing the two queries, the example works as claimed. We also reach the paper's initial
  matrix `[[1,4],[2,3]]` from the all-zero matrix of Algorithm 1 with the updates `a, b, e, e, e`. The responses force
  `U` before `Q₁` and `Q₂` before `U`, while `Q₁` precedes `Q₂` in real time. The text also says
  "P DC" where PCM is meant. (`Example2.pcm_not_linearizable`, `example2_not_lin`)
* **The proof of Lemma 2 does not define `H₁` and `H₂` precisely.** Reads are placed "after all
  preceding operations and before concurrent ones", and ties are broken arbitrarily. This is
  contradictory for two concurrent reads. The intended orders work: reads at their invocation and
  updates at their response, and the converse. The rest of the proof goes through as written.
  (`Alg2.alg2_sandwich`)
* **Lemma 1's proof is imprecise.** "`c_{σ₁}(Q)[i]` (the value when the query starts)": the count in
  `H₁` only lower-bounds the counter at the query's start, because pending updates may already have
  incremented it. The bound still holds. (`pcm_sandwich`)
* **Lemma 4's proof applies the sequential Lemma 3 to a linearization without justification.** This
  needs each process's operations to appear in program order in the linearization. It is true (each
  process's operations are ordered by real time) but not mentioned. (`alg3_linearizable`)
* Typos and slips:
  - Proof of Theorem 1 (p. 9): the first display should read
    `ret(Q, τ_{A(c)}(H₁)) ≤ ret(Q, H(A′, σ, c)) ≤ ret(Q, τ_{A(c)}(H₂))`, not `A` and `H₁`;
    "`ret(Q, τ_{A(c)}(H₂)) ≤ v_max`" should be `τ_I(H₂)`; the last line should have `≤ v_max + ε`, not
    `≥`.
  - Definition of `v_min`/`v_max`: `min{τ_I(L)}` should be `min{ret(Q, τ_I(L))}`.
  - Proof of Invariant 1, case `v = 0`: "`v′ᵢ = 1`" should be `v′ᵢ = 0`. Invariant 1 and Lemma 3 use
    `H′` before it is defined (in Lemma 4's proof). The summation index `i` clashes with the process
    index `i`.
  - Lemma 3: "the last update invocation" should be "the last `updateᵢ` invocation". The literal
    reading is also true but weaker.
  - Lemma 1's proof starts "We next prove that i is IVL".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's asynchronous shared memory with deterministic processes, atomic base objects and finite
  executions given as label lists. Correctness criteria are checked on every finite execution.
  Wait-freedom is CSLib's `Impl.WaitFree`, and step complexity counts the base-object accesses of each
  operation instance (`Impl.StepsLE`). There are no crashes; wait-freedom covers stopping processes.
* We use the amended linearization of Sela–Herlihy–Petrank: real time also constrains pending
  operations that get linearized. This matches the paper's `≺_H`, which is defined through `inv(op₂)`.
  IVL (`IsIVLFor S α`) asks for two linearizations of the skeleton `α?` such that every completed
  operation's response lies between the responses the deterministic specification `S` gives it in
  them.
* We compare all completed operations, not only queries. In every object of the paper, updates return
  a fixed dummy value.
* Randomness: a randomized object is a family of deterministic specifications `S : Ω → QSpec`, with a
  probability measure on coin vectors. A concurrent randomized algorithm is given by its executions
  under each coin vector, and a schedule is identified with the common skeleton history, which is what
  uniform step complexity gives. The adversary is oblivious: the schedule is fixed independently of
  the coins, as in the paper. Events are measured with the outer measure, so no measurability
  assumptions are needed.
* SWMR registers: base objects cannot see their caller in CSLib, so "single-writer" is a property of
  the code (`Impl.SWMR owner`). In Algorithm 2, process `i` keeps a local copy of `v[i]`, so an update
  is a single write.
* Theorem 3: the Israeli–Shirazi lower bound [21] for binary snapshots from SWMR registers is a
  hypothesis (`ISLowerBound n b`). The same bound `b` is derived for every wait-free linearizable
  batched counter from SWMR registers. The reduction inlines the counter implementation into
  Algorithm 3. It uses a variant without the line-4 shortcut (it adds `0` instead), which makes the
  simulation label-for-label exact and can only add steps. Lemma 4 itself is proved for the paper's
  Algorithm 3, with the shortcut, over an atomic counter.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 1 (IVL) | `IsIVLFor`, `IsIVL`, `Impl.IVLFor`, `Impl.IVL` | `Defs.lean` |
| Linearizable ⇒ IVL (remark) | `isIVL_of_isLinearization`, `Impl.IVL.of_linearizable` | `Defs.lean` |
| Locality of IVL (§3.2, App. A) | `HW.ivl_locality` (+ `HW.isIVLFor_iff_ivl_toHist`) | `Locality.lean` |
| Definitions 2, 3, 4 | `RandIVL`, `SeqBounded`, `ConcBounded` (`vmin`, `vmax`) | `Bounded.lean` |
| Theorem 1 | `theorem1` | `Bounded.lean` |
| Lemma 1 (PCM is IVL) | `pcm_ivl`, strong form `pcm_sandwich` | `CountMin.lean` |
| Lemma 1 + Theorem 1 (§5, before Cor. 1) | `pcm_concBounded` (sequential CM bound as hypothesis) | `Applications.lean` |
| Example 2 (PCM not linearizable) | `Example2.pcm_not_linearizable` | `CountMinExample.lean` |
| Algorithm 2 not linearizable (§6.1) | `Alg2.alg2_not_linearizable` | `Alg2NotLin.lean` |
| Lemma 2 | `Alg2.lemma2` (`Alg2.alg2_sandwich`) | `BatchedCounter.lean` |
| Theorem 2 (update 1 step, read `n` steps) | `Alg2.theorem2` | `BatchedCounter.lean` |
| Invariant 1, Lemma 3 | `alg3_invariant1`, `binSnap_scan_resp` | `Snapshot.lean` |
| Lemma 4 (+ wait-free, update/scan ≤ 1 counter access) | `alg3_linearizable`, `alg3_waitFree`, `alg3_update_steps`, `alg3_scan_steps` | `Snapshot.lean` |
| Theorem 3 (conditional on Israeli–Shirazi) | `theorem3` (hypothesis `ISLowerBound`) | `LowerBound.lean` |

**Not formalized.** The sequential error analysis of CountMin [7], and hence Corollary 1's concrete
bound `f_a^start ≤ f̂_a ≤ f_a^end + αn`; it enters only as the hypothesis of `pcm_concBounded`. The
Israeli–Shirazi lower bound itself. Infinite histories in the definition of `v_min`/`v_max`.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: Algorithm 2 instantiates Definitions 2–4 and Theorem 1 with a trivial coin
(`Alg2.alg2_randIVL`, `Alg2.bc_seqBounded`, `Alg2.alg2_concBounded`). Concrete executions are checked
with CSLib's computable `Impl.crun` and `decide` (no `native_decide`). The model comes from CSLib
`Cslib.Computability.Distributed.SharedMemory` (`Model`, `History`, `LinPoints`, `Potential`, and the
Herlihy–Wing framework `HerlihyWing/{Locality,Bridge}`).

**CSLib candidates** (marked in the files' docstrings; reusable outside this paper): skeleton histories,
`QSpec` and IVL (`Defs.lean`); the canonical linearizations `canon` (`Canonical.lean`);
`finite_isLinearization` (`Bounded.lean`); `Impl.SWMR` and `Impl.StepsLE` (`Objects.lean`).
