# Differences between the formalization and the paper

Perrin, Mostéfaoui, Bonin. *Extending the Wait-free Hierarchy to Multi-Threaded Systems.* PODC 2020
(proceedings version, 10 pages; there is no arXiv version).

## Model

1. **Processes start with their inputs.** Process `p` starts in local state `init p x` (`x` = its input). A
   process *arrives* at its first step, as in the paper. Local computation is folded into the continuation of
   shared accesses: every non-trivial step is exactly one atomic operation on one object. Processes are
   deterministic. A decision is an *output state*; later steps in it are no-ops.
2. **Executions are schedules.** A finite execution is a list of process identifiers; an infinite one is a
   sequence `ℕ → ℕ`. A process that stops taking steps has crashed.
3. **Arrival models are classes of infinite schedules** (`Arrival/Basic.lean`):
   * `M₃` (`infArrival`): all schedules;
   * `M₂` (`finArrival`): schedules with finite range;
   * `Mⁿ₁` (`boundedBy n`, finite schedules `belowN n`): only `p₀, …, p_{n-1}` take steps.

   The bounded arrival model `M₁` (where `n` is known only at run time) is not a separate notion. It amounts
   to one algorithm per `n` and is not used by the formalized results.
4. **Memory.**
   * All objects are allocated and initialised at set-up. An arbitrary, possibly infinite, index type `ι` of
     objects models *infinite allocation* (`MA…`). A finite `ι` models an algorithm without any run-time
     allocation.
   * For the `MA…` models this loses nothing: run-time allocation (of infinite arrays, of window registers
     whose size and initial value are chosen at run time) can be simulated with set-up objects, by giving
     every process private pre-allocated regions indexed by (allocation count, size, initial value). So
     the impossibility for every `ι` (Proposition 5) covers the paper's `MA₃`, and the positive results use
     set-up infinite arrays exactly as the paper's algorithms do.
   * The paper's allocation mechanism for `M…` is **not modelled**. It returns finitely many fresh locations
     at a time, reachable only through references stored in memory.
   * Consequences:
     * Proposition 4 is proved only for algorithms whose objects are all allocated at set-up (finitely many).
     * Algorithm 1, which needs run-time allocation of linked-list nodes, is out of scope.
     * The positive results (Algorithms 2 and 3) use infinite arrays, as in the paper (`MA₂`, `MA₃`).
5. **Correctness of consensus** (`SolvesCons`):
   * agreement among all processes that took a step and are in an output state, over all finite schedules;
   * validity: an output is the input of a process that took a step;
   * wait-freedom: in every infinite schedule of the class, a process with infinitely many steps outputs.

   Proposition 5 is proved under the weaker *weak validity* (if all inputs are `v`, outputs are `v`), for
   *binary* consensus. Proposition 4 is proved for multi-valued consensus with validity, where process `p`
   proposes `p`, exactly as in the paper's proof.
6. **Universality is not formalized.** The paper calls a model universal if every object with a sequential
   specification can be implemented in it.
   * We formalize the consensus level only: (im)possibility of solving the consensus task.
   * "Consensus impossible ⇒ not universal" holds because a consensus object has a sequential specification
     and a wait-free linearizable implementation solves the task. This standard step is not formalized.
   * "Consensus possible ⇒ universal" is the paper's Theorem 1 (universal construction). It is not
     formalized.
7. **Composition of implementations is not formalized.** CSLib has no composition theorem. So the steps
   "replace the atomic `consₙ` / `cons⟨B⟩` objects of Algorithm 2 / 3 by their implementations from `O`" in
   Theorems 2, 3 and 5 are not formalized. We prove the algorithms correct with *atomic* objects.

## Objects

8. `cons⟨V⟩` is `consObj V`: the state is the decided value, and `propose v` returns it. `consₙ⟨V⟩` is
   `consnObj V n junk`: the first `n` invocations return the first proposed value. Later responses are
   "unspecified" in the paper. Here they are given by an arbitrary function `junk`, and the results hold
   for every `junk`. A deterministic adversary suffices, because Claim 2 shows that these responses never
   occur.
9. Window registers are CSLib's `windowObj V k`. Each object has its own value type and its own size, both
   chosen by the algorithm (the paper's "size passed to the constructor"). The initial state may be any
   list.

## Section 3 (Theorem 1, Algorithm 1)

10. Algorithm 1 is not formalized, and neither are Propositions 1–2, Lemmas 1–3, Definition 3, Theorem 1 and
    Remark 1. The paper gives no proofs for them.

## Section 4 (Lemma 4, Theorem 2)

11. **Lemma 4** (`consensus_finiteMemory`).
    * Processes are `p₀, …, p_{n-1}` directly; the paper uses identifiers bounded by `N`, obtained by
      renaming.
    * The conclusion is stronger than the paper's: the *same code*, restricted to the finite set of objects
      it ever accesses, is a wait-free binary consensus algorithm with finite memory.
    * Claim 1 (`finite_reach`) uses only wait-freedom; binary (finite) inputs are essential.
12. **Theorem 2 and Corollary 1** are not formalized as statements. Their missing parts are Theorem 1 and
    composition. The non-trivial reduction "multi-valued from binary consensus with finitely many objects
    in `Mⁿ₁`" is our Algorithm 3 run by `n` processes:
    * `alg3_solvesCons_bounded`;
    * `alg3_poised_lt`: only the `3n` objects with index `< n` are ever used.

    The paper instead cites Zhang–Chen.

## Section 5 (Theorem 3, Algorithm 2)

13. **Algorithm 2.**
    * `adopt[r] ← cons[r].propose(vᵢ)` takes two steps (propose, then write).
    * `return adopt[r]` reads the register `adopt[r]`. If it read `⊥`, the process would output its current
      value; the invariant shows this never happens.
    * Local states carry the id and the round (ghost information).
14. **Claim 2, Lemmas 5–7** are proved (`claim2`, `count_eq`, `waitFree`, `agreement`, `validity`). The paper
    states them without proofs; ours are new.
    * Agreement: an invariant over all rounds after the first round with a decision.
    * Wait-freedom: by round `N+1`, where `N` bounds the identifiers of the processes that take steps
      (`round_le_of_bound`).
15. **Theorem 3** itself ("no object has consensus number `∞¹₁`") is not formalized as a statement. It needs
    Theorem 1 and the substitution of `O`-implementations for `consₙ` (items 6–7).

## Section 6 (Proposition 3, Proposition 4, Lemmas 8–9, Proposition 5, Theorem 4)

16. **Algorithm 3 / Proposition 3** (`alg3_solvesCons`).
    * Reading `proposed[j]` returns `Option V`. The output falls back to the own input on `none`, which is
      impossible by the invariant.
    * The paper gives no proof. Our wait-freedom proof orders processes by the time they set their `isSet`
      flag. Ordering by arrival time does not work: a process may have written `proposed[j]` but not yet
      `isSet[j]` when another process reads `isSet[j] = false`. We prove that the process whose flag was set
      first can never see its `cons` decided `false`.
17. **Proposition 4** (`Prop4.not_consensus`) is proved only for finitely many objects allocated at set-up
    (item 4). Changes to the proof:
    * **Definition 4 is strengthened** (`Prop4.Inv`).
      * The paper asks that the restriction of `α` to each class be a valid execution. Its condition 3
        (equal shared memory) is stated for one process `p` only.
      * When classes are merged after a block `β`, the restriction to the *merged* class must still give
        every member its real local state. Each constituent class alone does not imply this.
      * We require it for every *union* of classes, and add two conditions: objects outside `X` are
        untouched in the real execution and in every restriction; consensus objects of `X` are either in
        their initial state or decided `dv b j`.
      * After a block, the memory of every restriction containing the block equals the real memory
        (`Inv.block_memEq`). This requires every window register of `X` to be written at least its size
        times, and every consensus object of `X` to receive a proposal.
    * **Counting.**
      * Each scheduling step consumes `l` covering processes per object, so after `j` steps the coverage is
        `uᵢ - l·j`. The paper writes `uᵢ - j`, and "`uᵢ - v = 2 l u_{i+1}`" instead of `uᵢ - l v`.
      * We pick the stepping process `p` arbitrarily, so coverage drops by `≤ l + 1` per step.
      * Our thresholds are `need l k` (a recursion on the number `k` of objects not yet covered), not the
        paper's `uᵢ = (m-i+1)!(2l)^{m-i+1}`.
      * The window bound is `l = max size + 1`.
    * **Base case.**
      * The paper assumes, w.l.o.g., that every process first writes its input to a register `first` and
        finally writes its decision to a register `last`. We do not assume this.
      * The first stage starts from `X = ∅`, with all processes fresh. The first object `x₁` is chosen by
        pigeonhole after letting fresh processes run solo until they cover something.
    * **Last step.** The paper ends with "at least `2 ≤ u_m` processes are about to write to the last
      register". We replace this with the argument of the `γ` step:
      * In the last stage `X` contains all objects, so the solo run of `p` must decide (wait-freedom).
      * A second block by other classes, then a solo run of one of their representatives, produces a
        decision on an input of a disjoint class (validity applied to the restriction).
      * This contradicts agreement (`Prop4.iteration`).
    * **The `γ` step** runs `p` until it is poised to *modify* (write / propose) an object outside `X`.
      Reads of window registers outside `X` are allowed in `γ`, because those objects are untouched
      everywhere.
    * **Dynamic allocation.** The paper's `γ` stops at "an object not in `{x₁, …, xᵢ}`", which may be a
      freshly allocated object. Then the pigeonhole over the `m - i` set-up objects fails. The repair is to
      stop only at set-up objects outside `Xᵢ` and to treat objects allocated by a class as private to it.
      This repair is not formalized.
    * **Initial state.** Consensus objects initialised as already decided at set-up are handled
      (`dv b j = mem₀.getD (b j)`).
18. **Lemma 8** is proved for any finite set `Q` of processes (`exists_crit`), assuming agreement and
    wait-freedom for finite-range schedules.
19. **Lemma 9** (`crit_write_same`).
    * The two-team / same-object / no-read arguments are the classical ones.
    * The case "`k < n`" uses the `n - 1` other processes' writes, which overwrite `p`'s write.
    * Processes that have not arrived yet are handled automatically: in our model they start with inputs
      and are poised on their first access.
20. **Proposition 5** (`window_not_consensus`) is proved for binary consensus with weak
    validity (stronger than "not universal" via `cons⟨B⟩`). The window size of each object is fixed by the
    algorithm.
21. **Theorems 4 and 5** (placement of `cons⟨B⟩` at `∞¹₃` and of `WReg` at `∞¹₂`) are not formalized as
    statements. Their components are:
    * proved: Propositions 3, 4 and 5, and Algorithm 2;
    * not formalized: Theorem 1, composition, `k`-WReg has consensus number `k`, and universality of
      `cons⟨B⟩` in `M₁`.

## Section 8 (Proposition 6, Lemma 10, Theorem 6) and Section 9

22. Not formalized. Lemma 10 and the iterator-stack argument were not targets.

## Typos and small slips noticed

* Definition 3:
  * "`node′ = listₙ`" should be "`node′ = nodeₙ`";
  * "A value `v` precedes a value `v`" should end with `v′`;
  * "if if".
* Proposition 4: executions are called "`Πᵢ`-separable" but defined as "partitioned" (Definition 4). Also
  "for some `i ∈ {0, …, m − 1}`" for a sequence indexed from 1.
* Definition 6: "it is is".
* Figure 1 caption: "multi-treaded".
