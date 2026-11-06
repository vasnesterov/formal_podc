# Differences between the formalization and the paper

Rinberg, Keidar. *Intermediate Value Linearizability: A Quantitative Correctness Criterion.* PODC 2020
(brief announcement); formalized version: arXiv 2006.12889v1 (full version, numbering as there).

## Model and definitions

1. **Shared-memory model.** CSLib's asynchronous shared-memory model (`Cslib.SharedMemory`):
   deterministic processes, atomic base objects, executions are label lists, only finite executions
   are considered for safety (IVL, linearizability); wait-freedom is CSLib's `Impl.WaitFree` (infinite
   executions). The paper's "standard shared memory model [17]" is the same. Returning a response is
   a separate step of the process (CSLib convention), which does not access memory.
2. **Linearization (Section 2.1).** We use CSLib's `IsLinearization` (the amended Herlihy–Wing
   definition of Sela–Herlihy–Petrank: real time is respected towards every linearized operation,
   including completed pending ones). The paper's `≺_H` is defined through `inv(op₂)` only, so it
   relates a completed operation to a pending one; this is the amended definition. Under the original
   Herlihy–Wing reading locality would fail (Sela–Herlihy–Petrank); we read the paper the amended way
   (standard convention, holds throughout the paper).
3. **Skeleton histories and `τ`.** `skel α` (paper `H?`) replaces responses by `()`; a linearization of
   `H?` is `IsLinearization (skel α) L` with `L : List (OpId P × Op)`. The paper's `τ_H(L)` is
   `tau S L` (the response that the deterministic specification gives in the unique legal history with
   skeleton `L`). Specifications are `QSpec Op Resp` (states/initial state/transition), decoupled from
   the interface object of an implementation, so that a family of implementations indexed by coin flips
   can be compared with a family of specifications.
4. **Queries only vs. all operations.** Definition 1 (and Definitions 3, 4) compare return values of
   queries only; updates "return no value". In CSLib every operation has a response, so we compare all
   completed operations; in every object of the paper updates return a fixed dummy value (`0`) both in
   the implementations and in the specifications, so for them the extra comparisons are trivial
   (`0 ≤ 0 ≤ 0`), and for Definitions 3/4 they hold with probability 1 for `ε ≥ 0`.
5. **Definition 1 for multi-object histories.** Locality needs Definition 1 for histories over several
   objects; we use the multi-object specification of Section 2.1 (`H|x ∈ H_x` for all `x`), i.e. `τ`
   acts on each object separately (`Locality.lean`, `tauHW`). The single-object definition coincides
   with the execution-level one (`isIVLFor_iff_ivl_toHist`).
6. **Randomized algorithms (Sections 2.2, 3.3, 4).** A randomized object is a family of deterministic
   objects indexed by `c : Ω` with a measure `μ` (Theorem 1 assumes `IsProbabilityMeasure μ`). A
   concurrent randomized algorithm is given by its executions under each coin vector
   (`E : Ω → List (Label P A) → Prop`). The paper's schedule `σ` is identified with the skeleton
   history (by uniform step complexity, executions of the same schedule under different coins differ
   only in response values); "`H(A, c, σ)`" is any execution under `c` with skeleton `σ` (at most one by
   determinism). Probabilities are taken with Lean's outer measure, so no measurability assumption on
   the events is needed (for measurable events it is the probability).
7. **Definition 3** quantifies over all duplicate-free sequential skeletons `L` and instances `a ∈ L`
   ("every query returning in an execution of `A` with any schedule `σ`"). `τ` depends only on the
   sequence of operations and the position of `a`, so this is the paper's quantification when every
   process may invoke every operation.
8. **`v_min`, `v_max` (Section 4).** Defined as `sInf`/`sSup` of the ideal values over all
   linearizations of the skeleton; we prove there are finitely many linearizations
   (`finite_isLinearization`), so these are attained minima/maxima, as the paper argues. The paper's
   `min{τ_I(L)}` should read `min{ret(Q, τ_I(L))}` (notation slip). Only finite executions are
   considered (the paper also discusses infinite `H`).
9. **Responses domain in Section 4.** We allow any conditionally complete linear order with an
   additive structure and truncated subtraction (`OrderedSub`), covering `ℝ` and `ℕ`; `ε` has the
   response type.
10. **Algorithm 2.** Process `i` keeps a local copy of its own register (it is the only writer), so
    `v[i] ← v[i] + v` is one write step; the literal reading (read own register, then write) would be
    two steps — both `O(1)`. Single-writer registers: CSLib base objects cannot see the caller, so
    "SWMR" is the property `Impl.SWMR owner` of the code (only `owner i` writes register `i`); for
    Algorithm 2 `owner = id`. Step complexity is `Impl.StepsLE` (accesses per operation instance); we
    prove the exact bounds 1 (update) and `n` (read) instead of `O(1)`, `O(n)`.
11. **Batched counter values.** `update(v)` with `v ≥ 0` is modelled with `v : ℕ`.

## Statements and proofs

12. **Lemma 2 (proof).** The paper's `H₁`/`H₂` ("reads after all preceding operations and before
    concurrent ones; operations with the same order are ordered arbitrarily") are not well defined
    for concurrent reads; we use the precise canonical linearizations (reads at their invocation and
    updates at their response, resp. the converse; `canon` in `Canonical.lean`), which is what the
    proof needs. The paper first completes pending updates; we instead leave pending updates out of
    `H₁` (they are not needed). Proof otherwise as in the paper (per-register sandwich, sums of
    non-negative values).
13. **Theorem 1 (✏️ proof typos, statement correct).** In the proof (p. 9): the first display should read
    `ret(Q, τ_{A(c)}(H₁)) ≤ ret(Q, H(A′, σ, c)) ≤ ret(Q, τ_{A(c)}(H₂))` (the paper writes `A` and `H₁` on
    the right); "`ret(Q, τ_{A(c)}(H₂)) ≤ v_max`" should be `ret(Q, τ_I(H₂)) ≤ v_max`; the final
    "`≥ v_max + ε`" should be `≤`. The argument is otherwise exactly ours (`theorem1`).
14. **Appendix A (🔧 locality, proof gap; statement true).** The paper takes the union of the
    per-object linearization orders and the real-time order and asserts it is a well-defined partial
    order. This union is not transitive and the acyclicity of its transitive closure is the
    non-trivial part of Herlihy–Wing locality; it is not argued. The formal proof uses CSLib's merge of
    per-object linearizations (`mergedM`, a proof of exactly this step). Typo: "linearization `H₂` of
    `H 2`" should be `H?`.
15. **Section 6.1, "not linearizable" claim** (before Lemma 2): checked with a concrete three-process
    execution (`alg2_not_linearizable`).
16. **Lemma 1 (CountMin, Section 5).** Elements of any type `E`, hash functions `h : Fin d → E → Fin w`
    fixed per coin vector; the matrix starts at 0 as in Algorithm 1. Base objects: one atomic counter
    (increment/read) per cell. The query returns `⨅ i, c[i][hᵢ(a)]`, which is `0` for `d = 0` (the paper's
    algorithm would return `∞`; degenerate case). We prove the strong form with the paper's `H₁`/`H₂`
    (`pcm_sandwich`), whose linearizations depend only on the skeleton, as Definition 2 needs.
    Proof imprecision: "`c_{σ₁}(Q)[i]` (the value when the query starts)" — the `H₁` count only
    lower-bounds the counter at the query's start (pending updates may have incremented it); the bound
    used is still correct. Our proof does not need the index `j` of the final minimum.
17. **Corollary 1** is not formalized: it needs the sequential CountMin analysis [7]. We prove the
    combination step "Lemma 1 + Theorem 1" with that analysis as a hypothesis (`pcm_concBounded`).
18. **Example 2 (🔧 proof-level).** The execution has the same process `p` invoke
    `U`, `Q₁` and `Q₂` while `U` is pending — not well formed. Evident intent: another process issues
    the queries; we use process `q` (`Example2.example2`). "P DC" should be "PCM". The paper's initial
    matrix `[[1,4],[2,3]]` is not the all-zero initial matrix of Algorithm 1; it is reached by the
    updates `a, b, e, e, e`. With these fixes the example is a valid counterexample
    (`Example2.pcm_not_linearizable`). The statement is "PCM is not a linearizable
    implementation of CM" (abstract "albeit not linearizable", introduction, and the sentence
    introducing Example 2), which is true as written; Example 2 is its demonstration and ends in a
    proof by contradiction, and it makes no separate claim about a property of `σ`.
19. **Algorithm 3 / Lemmas 3, 4.** Binary snapshot `binSnap n`: update returns the all-`false` vector as
    a dummy; process `i` may only update component `i`. In `alg3` the local `vᵢ` is set in the same
    step as the counter access (local state, equivalent). Invariant 1 is proved for concurrent
    executions along a linearization (`alg3_invariant1`), not only for sequential histories. Lemma 4 is
    for an atomic counter (the paper's "linearizable batched counter"); composition with a linearizable
    implementation is done in Theorem 3's proof. Proof issues: Invariant 1, case `v = 0`, "`v′ᵢ = 1`"
    should be `0`; Invariant 1 and Lemma 3 refer to `H′` defined only later; the summation index clashes
    with the process index; Lemma 3 "the last update invocation" should be "the last `updateᵢ`
    invocation" (literal reading also true, weaker); Lemma 4's proof applies the sequential lemma to a
    linearization, which needs program order of each process's operations in the linearization (true,
    unstated). The counter must be unbounded (`c` grows at every 1→0 flip); ours is (`ℕ`).
    `alg3_scan_steps` gives "at most 1" counter access (the paper: exactly one; not needed).
20. **Theorem 3.** The Israeli–Shirazi bound [21] (and its binary-snapshot version [20]) is the
    hypothesis `ISLowerBound n b`: no wait-free linearizable binary snapshot for `n` processes from SWMR
    registers (any index type, value type, owner map) has all updates within `b` accesses. Conclusion:
    the same `b` for every wait-free linearizable batched counter from SWMR registers in which all
    processes may invoke all operations. "Ω(n)" follows by instantiating `b` with the IS bound. The
    reduction composes Algorithm 3 **without the line-4 shortcut** (an update with `v = vᵢ` adds `0`)
    with the counter implementation; this only adds steps to snapshot updates and makes the simulation
    exact. The paper's argument "other than the access to the counter, the update takes `O(1)` steps"
    is replaced by: the composed update performs exactly the counter update's accesses.
