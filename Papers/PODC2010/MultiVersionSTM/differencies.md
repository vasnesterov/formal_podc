# Differences between the formalization and the paper

Paper: Perelman, Fan, Keidar, *On Maintaining Multiple Versions in STM*, PODC 2010; full version
Technion CCIT Report #765 (May 2010). Labels follow `mistakes-labeling.md`.

## Mistakes and proof gaps (see README)

1. **🛠️ Theorem 3 / Definition 4.** False under Definition 4 as stated (`theorem_3_false`): the
   eager snapshot STM satisfies MV-permissiveness, strict serializability and the literal UP GC, and
   its solo read-only transactions leave no trace. Definition 4 is self-justifying, because the
   extension may contain the STM's own answer to the reader's read. True under Section 7's
   potential-reader rule (`STM.UPGCPrec`, `theorem_3`), which is how the paper itself uses UP GC
   (Section 7, and step (1) of the proof). We did not check that this rule can be met: no STM
   satisfying it was formalized.
2. **Theorem 3 proof.** It compares `H₁` with `H₂`, but these differ in more than `T₂` (`T₅`'s commit
   point, `T₂`'s reads). We compare `H₂` with `H₂` without `T₂`. Part of item 1.
3. **✏️ Theorem 3 statement.** It is phrased for *every* solo read-only transaction, but the proof
   (and `theorem_3`) gives *some* (`¬ NoTrace`).
4. **🛠️ Theorem 1 proof.** The competing STM `X′` "behaves the same as `X` but GCs `o₃¹`" is not a
   well-defined MV-permissive STM, and "the number of versions kept" is undefined. We replace `X′`
   by verified snapshot STMs: lazy (LSA-style) for case 1, eager for case 2.
5. **✏️ Theorem 1 proof, case 2.** `X′` cannot GC `o₄¹, o₅¹` "at time `t₀`" (they are the latest
   versions then); they are GCed once `T₅` overwrites them (Figure 2(c)). Counts are at `t₁`.
6. **Typos in Theorem 1 proof, case 1.** `o₁ˣ`, `o₂³` and `o₁³` should be `o₃ˣ`, `o₃²` and `o₃¹`.
7. **✏️ Definition 2 / conflicts.** Conflicts must be between concurrent transactions. With the
   literal Section 3 definition, MV-permissiveness would allow aborting `T₄` and `T₅` in Figure 2,
   whose commits the proof of Theorem 1 needs. `MVPerm` requires a concurrent conflicting update
   transaction.
8. **🔧 Theorem 2 proof.** The auxiliary history `H₃` (with `T₂` committing after `s₂`) does not
   share the configuration before `s₃` with `H₁`. We apply weak DAP to the prefix
   `s₁ s₂ s₃` of `H₁`. The commutation also covers all steps of `T₁` (write and commit) and `T₃`,
   not only `s₁` and `s₃`.

## Modelling choices

- **Atomic transactional steps.** As in the paper (Section 3), the base steps of one transactional
  operation run atomically: one `Prog` (a finite tree of read-modify-write accesses) per
  invocation, with invocation and response in one event. The STM is deterministic. The paper's
  "steps of a transaction are not known ahead of time" is automatic: the configuration after a
  prefix depends only on the prefix.
- **No `Abort(T)` invocation.** The paper also has a voluntary `Abort(T)` invocation. We omit it:
  the proofs do not use it, and for the impossibility results a smaller interface is a weaker
  requirement on the STM.
- **Versions, not values.** Writes carry no value. A read returns the writer of the version read
  (`none` = initial). This is the paper's `oᵢʲ` notation, i.e. value semantics with distinct written
  values. Reads must return the initial version or a version whose write was invoked
  (`ReadsWrittenOnly`). This is automatic for values; with version names, an STM could otherwise
  "guess" the writer of a future write (it is used in claim (3) of Theorem 2 and in Theorems 1, 3).
- **Strict serializability** (`StrictSer`): as in the paper, the complete (committed and aborted)
  transactions get injective positions that respect the real-time order, and every successful
  read of a complete transaction is legal; only committed transactions install versions. Live
  transactions are not constrained (the paper's `complete(H)`). The snapshot STMs validate the
  read set of an update transaction at every read, so aborted transactions also see consistent
  states.
- **MV-permissiveness is checked at the time of the abort.** The conflicting concurrent update
  transaction must exist in the history up to and including the abort.
- **Well-formedness.** No step after termination; read-only transactions don't write; a thread
  starts a transaction only when its previous ones are complete. All properties of STMs are
  required only on well-formed executions.
- **Versions kept** (Definition 3 and Theorem 1; undefined in the paper). An STM comes with a
  declared set `kept C` of versions kept in configuration `C`, subject to two axioms: a read (not of
  an own write) returns a kept version (`KeepsReads`), and an existing version that is not kept is
  never kept again (`GCFinal`). "The number of versions kept" counts the kept *overwritten* versions
  (`keptOld`). This reproduces the paper's counts 6 vs 7, and the latest versions, which every STM
  must keep, cancel out anyway. Definition 3 compares two STMs on the same schedule of invocations,
  at every prefix where both histories are well-formed.
- **The class of STMs** contains every deterministic algorithm on base objects. Strategies (response
  functions of the history) are realized by a single base object holding the history
  (`ofStrategy`); the competitors of Theorem 1 are such STMs.
- **Weak DAP** (Definition 1): transactions whose execution interval (from first to last event)
  overlaps that of `{T₁, T₂}`; the object graph; "disjoint-access" = no path from an object of
  `T₁` to an object of `T₂`; contention = a base object accessed by both, changed by one of the
  accesses (old value ≠ new value), anywhere in the execution.
- **UP GC.** `UPGC` is Definition 4: extensions are executions of the STM, a live transaction has
  begun and is not complete, "`T` can read `v`" means that the history extended by `T` reading `v`
  and committing is strictly serializable, and "written after" means written by a transaction that
  committed later. `UPGCPrec` is the Section 7 rule, weakened to "some live transaction precedes
  the overwriter"; this weaker hypothesis makes `theorem_3` stronger. `Prec` is the precedence
  relation of Section 7 (real time, read-after-write, write-after-write, write-after-read,
  transitive).
- **Theorem 3's "configuration external to the transaction"** (`ExtEq`) is the shared memory and the
  private states of all other threads. "Solo" means the schedule from the transaction's first to
  its last (commit) step contains only its own steps.
- **Universe.** Each scenario fixes the transactions it needs, on distinct threads, and distinct
  objects (`Setup1`: 5 objects, `T₁, T₃` read-only; `Setup3` and `theorem_2`: 2 objects). The
  counterexample `theorem_3_false` uses a declared kept set (`keptSmall`: the latest versions and
  the snapshot versions of live read-only transactions) while its memory stores the history of
  update transactions; since versions carry no data, an implementation could drop the rest. It
  assumes that fresh read-only transactions on fresh threads always exist (`FreshRO`), so that the
  latest versions are justified under Definition 4; a concrete universe satisfies it.

## Not formalized

- Section 7: the UP-MV algorithm, Design Principles 1–6, Lemmas 1–2, Invariants 1–2 and the claims of
  Section 7.3 (MV-permissiveness, UP GC, correctness of UP-MV).
- Opacity (mentioned in Section 3) is not considered.
