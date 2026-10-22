# Differences between the formalization and the paper

Paper: Xing Hu, Sam Toueg. *You can lie but not deny: SWMR registers with signature properties in systems with
Byzantine processes.* PODC 2025; formalized version arXiv 2504.09805v2. Scope: the optimality result of Section 10
(Definition 26, Observation 27, Lemma 28, Theorem 29, Observation 30, Theorem 31). The implementations of
Sections 5–9 (Theorems 14, 20, 25) and their ~100-page appendix proofs are **not** formalized.

## Model

1. **Execution model.** The paper's model (Section 3) is informal. We use CSLib's implementation data
   `Impl A B P L` (deterministic programs: `locInit`, `invoke`, `act`, `memInit`, `allowed`) with a new semantics
   `Impl.bstep` (`Podc/Computability/Distributed/SharedMemory/Byzantine/Model.lean`):
   * a correct process may take steps also while it has no pending operation (the paper's Section 3.3 "steps
     outside operation intervals", i.e. helping); an idle process whose next action is a response stutters;
   * a Byzantine process does not run any program; it applies arbitrary primitives to base objects, subject only
     to the access rights (`acc`) — for SWMR registers: it may write only its own registers. Byzantine reads are not
     modelled (they cannot influence anybody);
   * correct processes are invoked by the environment only when idle, and only with allowed operations.
   **Deterministic** implementations only (as everywhere in CSLib); the paper does not discuss randomized or
   nondeterministic implementations. For the impossibility this is no loss against (demonic) nondeterminism: fixing
   the choices of a nondeterministic implementation that is correct under every resolution gives a correct
   deterministic one (local states are arbitrary).
2. **Base objects.** Arbitrary atomic base objects `B i` (`i : ι`, any index type, possibly infinite) with access
   rights. The impossibility is proved for every family of *single-writer* objects (`SingleWriter acc owner`: only
   the owner changes an object, and the owner can overwrite it with any state). SWMR registers of arbitrary value
   types (`swmrAccess`, `swmr_singleWriter`) are the instance used for Theorems 29 and 31; this is a mild
   generalization of the paper (any number of registers per process, any value types).
3. **Histories, Byzantine linearizability (Definitions 1–8).** Histories are CSLib label lists; linearizations are
   CSLib's `IsLinearization` (pending operations may or may not be linearized = Definition 2's completions;
   real-time order = Definition 1). `ByzLinearizable allowed Bz h` (Definition 7) asks for a history `h'` that is
   well formed, uses only operations allowed for their process (e.g. only the setter `Set`s; only the writer
   `Write`s/`Sign`s), satisfies `h'|correct = h|correct` (as lists of invocation/response labels, i.e. the same
   real-time order among correct operations), and is linearizable. `h'` is *not* required to be one-shot.
   Well-formedness of `h'` is not explicit in the paper's informal Definition 7 but is no restriction: given any
   linearizable `h'`, putting each Byzantine operation as an immediate invocation/response pair at its linearization
   point gives a well-formed `h'` with the same restriction to the correct processes and the same linearization.
4. **Correctness (Definition 9).** `Impl.ByzCorrect acc f adm` requires, for every Byzantine set of size `≤ f`:
   Byzantine linearizability of the history of every **finite** execution, and termination (every correct process
   is idle infinitely often) in every **fair infinite** execution (every correct process takes infinitely many
   steps). The paper states Byzantine linearizability for (infinite) histories; since every finite execution
   extends to a fair one and linearizability is prefix closed, our requirement is implied by the paper's — the
   impossibility results are therefore at least as strong as the paper's.
5. **Environment restriction `adm`.** Correctness is only required for executions in which each correct process
   `p` invokes a sequence of operations satisfying `adm p`. Theorem 29 uses `oneShot` (each process invokes at most
   one operation — the paper's one-shot test-or-set); Theorem 31 uses no restriction (`fun _ _ => True`, long-lived
   registers). Internally the proof only needs the setter to invoke a prefix of its signing operations and every
   other process at most one test (`SigTest.Admits`), so the impossibility holds even for these restricted uses.

## Objects

6. **Test-or-set (Definition 26).** `testOrSet`: state `Bool`; `Set` returns `done` (the paper does not specify a
   response of `Set`), `Test` returns `bit b`. `tosAllowed s`: `Set` only by the setter `s`, `Test` by every other
   process ("by any tester").
7. **Verifiable / authenticated / sticky registers (Definitions 10, 15, 21).** `verReg`, `authReg`, `stickyReg`
   with states recording the current value and the sets of written (and signed) values; the sticky register's
   state is the first written value (`none` = `⊥`). "By any reader" is read as "by every process other than the
   writer" (`verAllowed` etc.); the writer cannot `Read`/`Verify`. This only restricts the environment (weaker
   correctness requirement ⇒ stronger impossibility) and the Byzantine operations in `h'`, where reads/verifies are
   irrelevant (they do not change the state).
8. **Signature-like objects (`SigTest`).** Instead of deriving Theorem 31 from Theorem 29, we prove the
   impossibility once for every object with a `SigTest` structure (a sign procedure `setOps` for the setter, a
   test operation, and a chain of stable state predicates), and instantiate it for test-or-set
   (`[Set]`/`Test`), verifiable registers (`[Write(v), Sign(v)]`/`Verify(v)`), authenticated registers
   (`[Write(v)]`/`Verify(v)`, `v ≠ v₀`) and sticky registers (`[Write(v)]`/`Read`, positive iff `≠ ⊥`). The paper's
   Observation 30 implementations use exactly these procedures (with `v₀ = 0`, `v = 1`).

## Statements

9. **Lemma 28** is proved for every `SigTest` object and every Byzantine linearizable history (it needs no
   termination): `SigTest.validity` (28(1); for multi-operation signing we assume the setter's operations are
   sequential and the last one precedes the test), `SigTest.unforgeability` (28(2), formulated as "the test does
   not precede the setter's first operation", i.e. the setter invoked something before the test returned),
   `SigTest.relay` (28(3)). The paper gives only a proof sketch; it is correct.
10. **Theorem 29** (`theorem29`): as stated, for `3 ≤ n = card P ≤ 3f`, any setter `s`, implementations from SWMR
    registers. The testers `pa`, `pb` and the groups `{s} ∪ Q1`, `{pa} ∪ Q2`, `{pb} ∪ Q3` are chosen inside the
    proof (`exists_groups`: a labelling of the processes into three classes of size `≤ f`).
11. **Theorem 31** (`theorem31_verifiable`, `theorem31_authenticated`, `theorem31_sticky`) is proved **directly**,
    not via "Theorem 29 and Observation 30 imply". That derivation needs a composition property (a correct
    implementation of test-or-set from a verifiable register, composed with a correct implementation of the
    verifiable register from SWMR registers, is a correct implementation of test-or-set from SWMR registers) which
    the paper neither states nor proves; it is plausible but non-trivial for Byzantine linearizability (Byzantine
    processes deviate from the composed program at both levels). We do not formalize this composition.
12. **Degenerate value domains (missing hypotheses in Theorem 31).**
    * Authenticated registers: the theorem needs a value `v ≠ v₀`. If the value domain is `{v₀}`, `Read` always
      returns `v₀` and `Verify(v₀)` always returns `true`, so the object is trivially implementable (every operation
      returns immediately) for every `n` and `f`: `authenticated_unit_byzCorrect`, `authenticated_unit_swmr` (in the
      exact setting of `theorem31_authenticated`, with no registers) in `Degenerate.lean`. The paper implicitly assumes a
      non-trivial domain: it calls the registers *multivalued*, and its Observation 30 implementation writes
      `1 ≠ v₀ = 0`. So this is an implicit convention made explicit, not an error of the paper.
    * Sticky registers: the theorem needs a nonempty domain `V` (`[Nonempty V]`); for `V = ∅` there are no writes
      and the object is trivial. (Not formalized as a separate counterexample.)
    * Verifiable registers need nothing (sign `v₀` itself, which is not initially signed).
13. **Observation 30** is formalized for every `SigTest` base object (one atomic base object of that type, Byzantine
    processes may apply any operation allowed to them), for every `f`, with the one-shot environment (see
    `Observation30.lean`: `observation30` for the generic implementation `tosImpl T`, Set = the setter's sign
    operations in order, Test = the test operation; corollaries `observation30_verifiable/_authenticated/_sticky`).
    The paper states it for `n > f`; it holds for every `f`. Correctness is proved for one-shot use (`oneShot`),
    the paper's test-or-set; the implementation is wait-free (`tos_termination`). For the sticky register our
    `Test` returns 1 iff the `Read` returns a value `≠ ⊥`; the paper's returns 1 iff the `Read` returns `1`. Both are
    correct; they differ only when a Byzantine writer writes a value other than `1`.
14. **The paper's remark for `n = 2`** ("trivial to implement") is not formalized.
15. **Typo.** Section 6 introduces the authenticated register as "a multivalued SWMR *verifiable* register"
    (copied from Section 4); Definition 15 makes clear that the authenticated register is meant.

## Proof

16. The proof follows the paper's histories `H1`, `H2`, `H3` (Figure 1) with these precise choices:
    * the indistinguishability steps are proved by a generic *replay* lemma (`Impl.replay`): processes that become
      Byzantine replay their base-object accesses as Byzantine writes (reads are dropped), and the processes of the
      other groups see exactly the same memory and local states;
    * `H2`: after replaying `H1`, the Byzantine group `{s} ∪ Q1` resets only the finitely many objects it owns whose
      state differs from the initial one (`exists_setMem`) — the paper's "reset all their SWMR registers";
    * `H3`: instead of replaying `H2` from the beginning, the Byzantine group `{pa} ∪ Q2` first writes its objects'
      contents at time `t5` (finitely many writes) and then replays its `H2` steps after `t5`; `{s} ∪ Q1` takes no
      step at all. `H3` is a finite execution, so the paper's "at time `t7` the processes in `{s} ∪ Q1` wake up" is
      not needed (Byzantine linearizability is required of finite executions);
    * termination is used through `ByzCorrect.exists_completion` (a round-robin fair continuation in which the
      Byzantine processes are silent), giving the times `t2`, `t4`, `t7`.
    No step of the paper's proof fails.
