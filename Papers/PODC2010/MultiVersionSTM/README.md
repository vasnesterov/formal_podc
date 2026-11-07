# Maintaining Multiple Versions in STM — PODC 2010

Dmitri Perelman, Rui Fan, Idit Keidar. *On Maintaining Multiple Versions in STM.* PODC 2010. DOI
[10.1145/1835698.1835704](https://doi.org/10.1145/1835698.1835704). Formalized version: the full
version, Technion CCIT Report #765 (May 2010, 20 pp.), which has the same numbering and adds the proof
of Invariant 1 (Appendix A). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** Theorems 1–3 hold once repaired. Theorem 1 (no MV-permissive STM is
online space optimal) needed a new construction of the competing STM, and Theorem 2 (no weak
disjoint-access parallelism) a local fix of its proof. Theorem 3 (UP GC forces read-only
transactions to leave a trace) is false for UP GC as printed in Definition 4, whose wording lets an
STM justify a version by its own future answer (`theorem_3_false`). It holds for UP GC as the paper
uses it: the potential-reader rule of Section 7 and step (1) of the proof (`theorem_3`). Section 7's
UP-MV algorithm was not checked.

## Mistakes in the paper

### 🛠️ Theorem 3 and Definition 4 (UP GC)
Definition 4 lets an STM justify keeping a version through its own future answers: there is an
MV-permissive, strictly serializable STM that satisfies UP GC as defined, and in which every solo
read-only transaction leaves the external configuration unchanged (`theorem_3_false`).

**Impact.** Theorem 3 ("MV-permissiveness and UP GC force read-only transactions to leave a trace",
so invisible reads are impossible) fails under the literal Definition 4. It holds, with a repaired
proof, for UP GC read as the paper uses it: Section 7's potential-reader rule, which step (1) of the
proof also argues with (`theorem_3`). The other results do not use Definition 4.

**Details.** Definition 4 keeps a version `oᵢʲ` only if some extension of the history has a live
transaction that can read `oᵢʲ` and cannot read any later version. The extension may contain the
STM's own answer to that transaction's read of `oᵢ`: once a read-only transaction has read `oᵢʲ`,
a second read must return `oᵢʲ` again, so no later version can be read.

The counterexample is the *eager snapshot* STM. A read-only transaction reads the versions current at
its first step, and an update transaction validates its read set at every read and at commit. It keeps the latest
versions and the snapshot versions of live read-only transactions. Every kept version is justified by
an extension in which a (live or fresh) read-only transaction reads it. The shared memory stores the
history with the events of committed read-only transactions erased, so a solo read-only transaction
leaves no trace.

In Figure 4 this STM gives `T₄` the version `o₂¹` (serialization `T₁ T₄ T₅ T₂ T₃`). The proof's step
(1), "every live transaction can read `o₂²` or a later version, so `o₂¹` is GCed", fails. It assumes
that the STM serves the latest readable version, which neither MV-permissiveness nor Definition 4
requires.

The proof of Theorem 3 also compares `H₂` with `H₁`. But these histories differ in more than
`T₂`: `T₅` commits at a different point, and `T₂` reads different objects. So "the only thread that
distinguishes `H₁` from `H₂` is `thr(T₂)`" is not justified. The repaired proof compares `H₂` with
`H₂` without `T₂`.

**Repair.** We read UP GC as Section 7's rule: an overwritten version is kept only if some live
transaction precedes, in the precedence relation of Section 7, the transaction that overwrote it
(`STM.UPGCPrec`, a weakening of "has a potential reader"). Under this rule we prove Theorem 3
(`theorem_3`): some solo read-only transaction changes the external configuration. Our proof
follows the paper with `H₂` and `H₂` without `T₂`. In the latter, `T₄` precedes only `T₅`, so `o₂¹`
is not kept and `T₄` reads `o₂²`. If `T₂` left no trace, `T₄` would read `o₂²` in `H₂` too. Then
`T₃ ≺ T₄ ≺ T₅ ≺ T₂ ≺ T₃` is a cycle. This rule is what the paper means by UP GC: Section 7
implements UP GC by it, and step (1) of the proof argues with it. We did not check that the rule can be met: Section 7 claims it for
UP-MV, but we did not check UP-MV.

### ✏️ Slips
- Theorem 3, statement: it says that *every* solo read-only transaction changes the external
  configuration, but the proof (and `theorem_3`) gives only that *some* solo read-only transaction
  must leave a trace.
- Definition 2 (MV-permissiveness), with the definition of conflict in Section 3: conflicts must be
  between *concurrent* transactions. Otherwise MV-permissiveness would allow aborting `T₄` in
  Figure 2 (it writes `o₃`, already written by the committed `T₂`), and the proof of Theorem 1 needs
  `T₄` and `T₅` to commit. We use concurrent conflicts.
- Theorem 1, proof, case 2: `X′` "GCs `o₄¹` and `o₅¹` at time `t₀`". At `t₀` these are the latest
  versions, which no MV-permissive STM can drop. As Figure 2(c) says, they are removed after `T₅`
  overwrites them, and the counts 6 and 7 are taken at `t₁`.

### Typos
- Theorem 1, proof, case 1: "`T₁` can read `o₁ˣ`", "`T₃` can return `o₂³`" and "after `X′` removes
  `o₁³`" should be `o₃ˣ`, `o₃²` and `o₃¹`.

## Proof gaps (statements true)

### 🛠️ Theorem 1 (the competing STM `X′`)
The proof builds `X′` as "`X` with `o₃¹` garbage-collected" (case 1) and checks only that the live
read-only transactions at `t₀` can still commit. `X` itself may later serve `o₃¹` to `T₃`, so `X′`
is not a well-defined MV-permissive STM.

**Impact.** Statement true; repaired with explicit competitors (`theorem_1`).

**Details.** "Behaves the same as `X` except for removing `o₃¹`" does not say what `X′` answers when
`X` would answer `o₃¹`. Answering `o₃²` instead serializes `T₃` after `T₄` and changes all of `T₃`'s
later reads. In case 2, `X′` must even answer differently from `X` (Figure 2(c)). Also, the quantity
compared, "the number of versions kept", is not defined in the model.

**Repair.** We make "kept" precise. An STM declares the versions it keeps; a read returns a kept
version, and a version, once dropped, is never kept again. We count kept *overwritten* versions,
which gives exactly the paper's 6 and 7. The competitors are two snapshot STMs, verified once for all
histories (`snapSTM_valid`). If `X` keeps `o₃¹` at `t₀`, it keeps at least 5 overwritten versions
then, while the *lazy* (LSA-style) snapshot STM keeps 4. Otherwise `X` keeps at least 7 at `t₁`
(`o₄¹, o₅¹` are forced, since `T₃` must read `o₃²`), while the *eager* snapshot STM keeps 6.

### 🔧 Theorem 2 (the history `H₃`)
To show that the steps of `T₁` and `T₃` do not contend in `H₁`, the proof uses a history `H₃` in which
`T₂` commits right after its first step, and claims that `thr(T₃)` does not distinguish `H₁` from
`H₃` after `s₃`. But in `H₃`, `T₂`'s commit happens before `s₃`, so `T₃` may see it.

**Impact.** Statement true; repaired by a local change (`theorem_2`).

**Repair.** Apply weak DAP to the prefix `s₁ s₂ s₃` of `H₁` itself: there `T₂` has accessed only
`o₁`, so `T₁` is disjoint-access from both `T₂` and `T₃`. A generic commutation lemma
(`STM.run_comm`) then moves all steps of `T₁` (its write and its commit) after those of `T₂` and
`T₃`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory. An STM is a deterministic algorithm run by threads with private
  states. Each transactional operation is one atomic step: a `Prog`, a finite decision tree of
  read-modify-write accesses to base objects. The environment chooses the invocations
  (`read T o`, `write T o`, `commit T`). There are no failures and no randomness. Whether a
  transaction is read-only, and its thread, are known a priori (`TxSys`). Histories are
  well-formed: no step after termination, read-only transactions don't write, one live transaction
  per thread.
- **Versions instead of values.** A read returns the version it reads, named by its writer. This
  is the paper's `oᵢʲ` notation (value semantics with distinct written values). Reads return
  written versions (`ReadsWrittenOnly`), as a value read in the paper is a written value.
- **Strict serializability** as in the paper: `complete(H)` (committed and aborted transactions)
  has a legal serialization that respects the real-time order (an injective position function
  plus per-read legality, `StrictSer`).
- **MV-permissiveness**: only update transactions abort, and only when a concurrent update
  transaction conflicts with them.
- **Versions kept** (not defined in the paper): an STM declares a set `kept C` per configuration,
  with `KeepsReads` and `GCFinal`. Definition 3 compares kept overwritten versions on the same
  schedule (`OnlineSpaceOptimal`).
- **Weak DAP** (Definition 1) follows the paper: transactions overlapping the interval of
  `{T₁, T₂}`, the object graph, and contention over the whole execution.
- **UP GC.** `UPGC` is Definition 4 literally: extensions are executions of the STM, and "can read"
  means the extended history with that read and a commit is strictly serializable. `UPGCPrec` is
  the potential-reader rule of Section 7.
- The scenarios fix five transactions on distinct threads and five (Theorem 1), two (Theorems 2
  and 3) distinct objects, with the paper's read-only/update kinds (`Setup1`, `Setup3`, and
  hypotheses of `theorem_2`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definitions 1–4 | `STM.WDAP`, `MVPerm`, `STM.OnlineSpaceOptimal`, `STM.UPGC` / `STM.UPGCPrec` | `Model.lean`, `STM.lean` |
| Theorem 1 | `theorem_1` | `Theorem1.lean` |
| Theorem 1, forced versions | `Setup1.t1_keeps_initial`, `Setup1.t1_keeps_T4`, `Setup1.lower_case1`, `Setup1.lower_case2` | `Theorem1Lower.lean`, `Theorem1.lean` |
| Theorem 1, competitors (Fig. 2(c)) | `snapSTM_valid`, `Setup1.lazy_kept_σH`, `Setup1.eager_kept_σH1` | `SnapshotProofs.lean`, `Theorem1.lean` |
| Theorem 2 | `theorem_2` | `Theorem2.lean` |
| Commutation of non-contending steps | `STM.run_comm` | `Commute.lean` |
| Theorem 3 is false (Definition 4 as stated) | `theorem_3_false` | `Theorem3False.lean` |
| Theorem 3 (UP GC as in Section 7) | `theorem_3` | `Theorem3.lean` |

**Not formalized.** Section 7 (the UP-MV algorithm, Lemmas 1–2, Invariants 1–2).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: the snapshot STMs satisfy every hypothesis of Theorems 1 and 2
(`snapSTM_valid`), and `theorem_3_false` comes with a concrete universe satisfying `FreshRO`. We have
no STM satisfying the hypotheses of `theorem_3` (that would be Section 7). The model is self-contained
(no CSLib model is reused: the 2010 paper's atomic transactional steps and whole-execution contention
differ from the PODC 2015 TM model in `Papers/PODC2015/DAPInvisibleReads/`).
