# Differences between the formalization and the paper

Paper: Peluso, Palmieri, Romano, Ravindran, Quaglia, *Disjoint-Access Parallelism: Impossibility, Possibility,
and Cost of Transactional Memory Implementations*, PODC 2015; Virginia Tech technical report (May 2015) used.

## Statement-level issues

1. **Lemma 1 is false** (❌, `Lemma1.lemma_1_false`). The abstract presents the impossibility theorems, the
   algorithm and the lower bounds, not this lemma. The paper's model has `Np` processes and Lemma 1 is used in
   histories with other transactions (Lemma 2, Theorems 1–3). The counterexample uses three processes and two transactional objects.
   - Reading of "WDAP" / "disjoint-access": the paper says it uses the definition of [4] (Attiya, Hillel,
     Milani): a path in the conflict graph, whose edges join transactions with intersecting data sets. The
     counterexample TM satisfies the strongest data-set form: concurrently contending transactions have
     *intersecting* data sets (`StrongWDAP`), so it is WDAP whether the conflict graph is taken over the whole
     history or the minimal interval containing the two transactions, with or without requiring concurrency
     for edges. The transactions `Tᵢ`, `Tⱼ` of the counterexample are disjoint-access in every one of these
     readings (no path even in the graph over all transactions of the execution).
   - The paper's sentence "not disjoint-access ... if there is a path ... in the undirected version of the DSG"
     could also be read with DSG edges (read-from / version dependencies) instead of data-set edges. Under that
     literal reading WDAP becomes much stronger (two transactions with pending operations on the same object are
     not DSG-connected until a commit), and `chainTM` is not WDAP; we did not decide Lemma 1 under that reading.
     We consider the data-set reading the intended one: it is the cited definition, and the proof of Lemma 2
     itself speaks of "the conflict graph of the minimal execution interval".
   - "Concurrent": formalized as "both live at the end of the execution", which implies overlapping intervals.
   - "Contend": a step of each transaction on the same base object, at least one non-trivial (paper's
     definition).
2. **Theorems 1 and 2 need termination** (✏️) of solo / isolated write transactions. The paper's definitions of
   obstruction-freedom ("forcefully aborted only if step contention") and weak progressiveness ("can only abort
   if it experiences a conflict") contain no termination requirement; literally, a TM whose write transactions
   never return satisfies them, and its histories preserve RTO (no committed writer, no version, no edge). The
   standard definitions (the cited [15] OFTM, [17]) include it, and the proofs use it ("T₂ and T₃ cannot
   be aborted" is meant as "commit").
3. **Proof gap in Theorems 1 and 2** (🛠️): the proofs rely on Lemma 3, i.e. on Lemmas 1–2, whose proofs only
   consider the two transactions `Tᵢ`, `Tⱼ`; in `H_WRTO`, `T₃` must also be reordered. Repaired: `theorem_1`,
   `theorem_2` via `commute_scenario`.
4. **Lemma 2** (its non-concurrent case cites Lemma 2 of [4] for "consecutive" transactions, but other
   transactions may run in between; the chain pattern of `chainTM` applies) and **Lemma 3** in general: not
   formalized. Only the instance of Lemma 3 used in the proofs of Theorems 1–2 is proved (`hWRTO_of_run`: under
   WDAP, WFRO, legal reads and WRTO, `R₄(x)` returns `T₂`'s value). The rest is not checked.
5. **Theorems 3 and 4, Section 4**: not formalized. Remarks only: Theorem 3's
   `Ω(k·Nₒ)` multiplies an informally argued `Ω(Nₒ)` by `k` with no argument that each version needs a separate
   check; its proof applies Lemma 1 to `Ti*`, `Ti+`, which are not disjoint-access (both connected to `Tro`).
   Theorem 4's "space complexity for each version" is not defined (one unbounded base object can hold a vector
   clock), so the statement is not precise enough to formalize.

## Modelling choices

- **Model**: CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`): deterministic processes,
  base objects given by sequential specifications with atomic primitives, arbitrary scheduling, environment
  choosing invocations. A primitive is *trivial* iff it never changes the state of the base object (paper:
  "may change the value"). Crashes are not modelled explicitly: all arguments use finite executions, in which a
  crashed process is one that stops taking steps.
- **TM interface**: `read x`, `write x v`, `tryC`; a response is `Option V` (`none` = abort; `some v` = success,
  the value is meaningful only for reads). No separate `begin` operation: a transaction begins with its first
  invocation (as in Guerraoui–Kapałka); the paper's `begin` could only add steps that we fold into the first
  operation. The sequential specification of the interface `ObjSpec` is a dummy (not used).
- **Transactions** are computed per process from the history (`pstate`): an abort, or a successful `tryC`, ends
  the current transaction; `(p, k)` is the `k`-th transaction of `p`.
- **Versions and the DSG**: the versions of `x` are the initial one (value `v₀ x`, treated as committed, as in
  the paper's use of `x₀`) and those of committed transactions that wrote `x`, ordered by commit time (paper:
  "the order of the write operations successfully executed on it"). The value of a version is the writer's last
  write to `x`. Read-from is determined by values (`wr` requires a committed writer, as the paper's `xᵢ` is a
  committed version). This is exact only with unique written values: otherwise a serial history in which `T₀`
  writes `x`'s initial value and a later `T₁` reads it would count as an RTO violation
  (`Figure1.serial_repeated_value_not_preservesRTO`), and every live TM would trivially fail to ensure RTO.
  So `EnsuresRTO` / `EnsuresWRTO` quantify only over histories satisfying `UniqueWrites` (each write to `x`
  writes a value different from `x`'s initial value and from the other writes to `x`), the standard convention
  behind the paper's notation `Rᵢ(xⱼ)`. Vertices of the DSG are the real transactions (the initial "transaction" is
  not a vertex; otherwise every pair of transactions would be connected through it and WDAP would be void).
  `rw` edges come from reads of any version (initial included) with a different writer. Edges are defined for
  all transactions (committed, aborted, live); in every violating history we exhibit, all transactions on the
  cycle are committed.
- **RTO / WRTO**: `Tq ≺RTO Tk` iff `Tq` committed before `Tk` began. `Tq ≺WRTO Tk` iff `Tq ≺RTO Tk` and a
  direct DSG edge (any of `wr`, `ww`, `rw`) joins them in either direction. The introduction also mentions
  same-process pairs; the formal definition of Section 2 does not, and we follow it (the proofs do not use
  same-process pairs). "`H` preserves RTO": for every `Tq ≺ Tk`, no path from `Tk` back to `Tq` in `DSG ∪ ≺`,
  i.e. no cycle through `Tq` and `Tk` once the edge `Tq → Tk` is added.
- **WDAP** (hypothesis of Theorems 1–2): at every reachable configuration in which two processes are poised to
  apply primitives to the same base object, at least one non-trivial, their current transactions are connected
  in the conflict graph of the history so far (vertices: begun transactions; edges: intersecting data sets,
  data set = objects of invoked operations, including the pending one). This is implied by the definition of
  [4] and by the paper's DSG wording (DSG edges are data-set edges; the prefix is itself an execution), so the
  theorems hold for a larger class of TMs.
- **Progress hypotheses** (each implied by the paper's notion plus solo termination, see item 2):
  - `ObstructionFreeWrites`: an operation of a transaction that has invoked a write, with no step of another
    process since the transaction began, completes solo with a non-abort response. Paper: "obstruction-free"
    TM / write transactions.
  - `IsolatedWritesCommit`: same, when moreover no transaction of another process was live when the transaction
    began. Implied by weak progressiveness (no conflict is possible without concurrent transactions).
  - `WaitFreeReadOnly`: an operation (read or `tryC`) of a transaction that has not invoked a write completes
    solo with a non-abort response. Implied by WFRO because the TM cannot know whether such a transaction will
    stay read-only; only solo completion is needed, weaker than wait-freedom.
  - `InvisibleReads`: the steps of a read of a transaction that has not invoked a write are trivial. Implied by
    IRO for the same reason.
  - `LegalReads`: a read returns the initial value or a value that some invoked write writes to that object.
    Implicit in the paper (a read always returns a version `xⱼ`); without it, a TM returning garbage would
    trivially preserve RTO.
- **Scope of Theorems 1–2**: three distinct processes and two distinct objects are assumed (the paper's
  history `H_WRTO` uses exactly these). The proofs construct the executions `E` and `E'` and show that one of
  them violates RTO (`theorem_1`, `theorem_2`); with WRTO, `E` itself is `H_WRTO` (`theorem_1_wrto`,
  `theorem_2_wrto`), which is what the paper states ("the TM cannot reject `H_WRTO`"). `T₂` and `T₃` write the
  same value `v₁` (to different objects). `theorem_1`, `theorem_2` and the `_wrto` versions assume that `v₁`
  (resp. some value) differs from the initial values of `x` and `y`, so that the violating histories satisfy
  `UniqueWrites`; this assumption on the value domain is implicit in the paper, whose histories write fresh
  versions `x₂`, `y₃`. `theorem_*_explicit` take an arbitrary `v₁`.
- **Figure 1**: concrete histories over processes `Fin 5` (process `i` runs `Tᵢ`), objects `x = 0`, `y = 1`,
  initial value `0`, values `x₂ = 2`, `y₃ = 3`. In `H_NO-RTO`, `T₁` runs between `c₂` and `R₄(x₂)` (the figure
  does not fix its position relative to `R₄(x₂)`; the claims do not depend on it). The EUS/Consistent View
  remark about `H_NO-RTO` is not formalized.
- **Non-vacuity**: `trivTM` satisfies all hypotheses of `theorem_1` and `theorem_2` (`trivTM_hyps`). The
  satisfiability of the hypotheses of `theorem_1_wrto` (WRTO together with obstruction-freedom) is not checked;
  the paper does not claim it.
