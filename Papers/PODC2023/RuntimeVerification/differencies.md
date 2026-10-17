# Differences between the formalization and the paper

Paper: A. Castañeda, G. V. Rodríguez, *Asynchronous Wait-Free Runtime Verification and Enforcement
of Linearizability*, PODC 2023. Formalized text: arXiv 2301.02638v3 (November 2025, journal-style
full version, 36 pages); numbering follows it.

## Errors and imprecisions in the paper

1. **Lemma 7.4 is false as stated** (false in an edge case; proof gap in Lemmas 8.1/8.2, whose
   statements are true). The lemma says that for every tight execution `E` of `A*`, `E` and
   `X(λ_E)` are equivalent with `≺_E = ≺_{X(λ_E)}`. This fails for pending operations that no view
   has seen yet, i.e. whose `N.Write` comes after the last `N.Snapshot`: `X(λ_E)` lacks their
   invocations.
   Lean counterexample: process `p₁` completes one operation, then invokes a second one and
   executes its `N.Write`; `p₂` is idle (`lemma_7_4_false`, `Lemma74.lean`).
   Corollaries 7.1 and 7.2 remain true, because `X(λ_E)` is similar to a prefix of `E`.
   The proofs of Lemmas 8.1 and 8.2 apply Lemma 7.4 to executions in which such operations
   routinely occur: the `F` of Lemma 8.1 and `T(E'|A*)` in Lemma 8.2.
   The fix is to compare with a prefix. We cut at the last relevant snapshot and use prefix
   closure (`sketch_mem_of_tight`, `tight_cut_mem_of_sketch`, `sketch_isAStarHist`).
2. **Proof of Lemma 8.1: "`≺_{F'} = ≺_{T(E'|A*)}`" is false in general** (proof imprecision; the
   statement is true). Take an operation whose tuple is missing from `τ'`. Its response is appended
   at the end of `F'`, while in `T(E'|A*)` it can precede later invocations. Only `⊆` holds, and
   only `⊆` is needed for similarity. The same proof also needs a truncation for the reason in item 1.
3. **Claim 7.2 is stated for every implementation `B`, but holds only for concrete ones**
   (imprecise statement). For an abstract implementation (an arbitrary set of histories, the
   paper's own notion), reordering concurrent invocations can leave the set. The claim is used
   only for `A*`, where it is true. We do not use Claim 7.2: the witness execution of `A*` is
   built directly (`Witness.lean`).
4. **Typos / slips.**
   * Proof of Lemma 7.3: "Note that `E` and `T(E)` are equivalent". This is false when `T(E)`
     drops pending operations that did not write; `E'` and `T(E)` are equivalent.
   * Proof of Lemma 8.2: "`H` the shortest prefix of `X(λ_{T(E'|A*)})` …" should be a prefix of
     `X(τ'')`.
   * Theorem 8.2 (3): "a history that is similar to the history of `V_{O,A}`" has the direction of
     similarity reversed. The history of `V_{O,A}` is similar to the snapshot sketch (see the proof
     of `hVy_mem_of_noReport`), not conversely.
5. **Theorem 8.2 (2) in the degenerate case `O = ∅`** (false only in a degenerate case). Before
   the first `ERROR`, the history of `V_{O,A}` is required to be in `O`; this fails if `O` has no
   histories at all. We assume `[] ∈ O` (equivalently `O ≠ ∅` for `O ∈ GenLin`).

## Strengthenings (proved results are stronger than stated)

* **Stability** (Theorem 8.1 (3)). The paper: from some point on, every new iteration reports.
  We prove that once a test reports `ERROR`, every later test reports `ERROR`
  (`Exec.sketch_mono`, `thm_8_1` (4)).
* **Predictive soundness.** Every report, not just one, comes with a witness that is a history of
  `A*` violating `O`.
* **Theorem 5.1** holds for verifiers with arbitrary atomic blocks on an arbitrary shared memory
  and synchronized clocks, and fails already for the weak requirement "report anything"
  (`thm_5_1_weak`).

## Modelling choices

* **Quantifier order for verifiers** (imprecise phrase in the paper). Section 3 says the
  black-box requirement is "modeled as conceptually `V_O` taking `A` as its input". The paper
  also says explicitly that `V_O` "cannot be designed for a specific implementation `A`, it must
  work for any possibly abstract … implementation", and §1.3 calls `A` a black box. So the paper's
  reading is `∃V ∀A`, and that is what we formalize.
  *Remark.* If `V` could depend on `A`, Definition 6.1 would be trivially solvable
  (`Impossibility.trivialVerifier_predictive`) and Theorem A.1 would fail. Theorem 5.1 holds under
  both readings (`thm_5_1_nonuniform`).
* **Determinism of the verifier blocks.** The `pre`/`post` transitions are deterministic functions.
  This loses nothing for the impossibility results: a nondeterministic verifier that is correct in
  all its executions is in particular correct for any fixed choice function, and with a fixed
  choice function it is deterministic.

* **Histories** are CSLib's single-object Herlihy–Wing histories. Linearizability is CSLib's amended
  definition (Sela–Herlihy–Petrank), which is the paper's Definition 4.2. The sequential
  specification is any prefix-closed set of sequential histories; the concrete objects are
  deterministic state machines (`detSpec`).
* **Section 3 verifiers** (`Impossibility.lean`). The blocks of Lines 03–05 and 08–12 are atomic
  transitions on an arbitrary memory type and may read the global time. A wait-free multi-step
  block run solo is a function of (start time, local state, memory), so it is subsumed. The paper's
  proof runs the blocks solo too. Abstract implementations are prefix-closed sets of well-formed
  histories; an execution must keep `A`'s history inside the set. Fairness: every process executes
  infinitely many iterations. Each process chooses each operation at most once.
* **Theorem 5.1 instances.** The paper treats the queue in detail and says the other objects are
  "nearly the same". We give explicit data for queues, stacks, priority queues, sets, counters and
  consensus (`Objects.lean`). Operations carry a tag, as in the paper's "fictitious input value".
* **Executions of `A*` and `V_O`** (`Exec.lean`) are given by the operations, `A`'s responses and
  injective step times. Shared-memory contents are derived ("a snapshot returns everything written
  before it"), which is the atomic snapshot semantics the paper assumes via linearizability.
  * Union of the `N` entries. `N[i]` holds the growing set of invocation pairs of `p_i`, so the union
    of the entries in a snapshot is the set of all pairs written so far.
  * Union of the `M` entries. The tuples `(p, op, y, λ)` form a set; its union is taken the same way.
  * Invocation records. We store `(p, k, op)`, where `k` is the index of the operation, instead of
    `(p, op)` with globally unique `op`. This is the paper's fictitious input value made explicit.
* **Witness execution of `A*`.** It may use any linear order as its time domain. We use
  lexicographic triples `TX`.
* **The sketch `X(τ)`** is built with one fixed order inside each block (by process and operation
  index). The paper allows any order; all orders give similar histories.
* **`Op` and `Y` are inhabited** (`[Inhabited Op] [Inhabited Y]`), so `X(τ)` can be defined for
  arbitrary `τ`.
* **Theorem 8.1 for infinite executions** (`thm_8_1_inf`). The paper's standing assumptions are
  stated as hypotheses:
  * no process stops between its `N.Snapshot` and its `M.Write` (no crashes; wait-free code);
  * tests happen at arbitrarily late times (lock-freedom of `A` + no crashes).
  The finite-execution versions (`thm_8_1`) need no such assumption.

## Not formalized

* Wait-freedom / lock-freedom preservation and step complexities (Lemma 7.2 progress part,
  Claim 8.1, Theorem 8.1 (1), Theorem 8.2 (1)). These are immediate from the straight-line code.
* The implementation of the snapshot objects from read/write registers. The paper cites it;
  snapshots are atomic in our model, as in the paper's analysis.
* Lemma 7.2, direction "`A*` correct ⇒ `A` correct".
* Set-/interval-linearizability as instances of `GenLin` (claimed without proof after Lemma 7.1).
  All our positive results are stated for arbitrary `O ∈ GenLin`.
* Section 9 extensions: bounded registers, the decoupled version, obstruction-free / blocking
  implementations, tasks, message passing.
