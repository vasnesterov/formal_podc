# From Sequential to Concurrent / Optimism for Boosting Concurrency — PODC 2012

Vincent Gramoli, Petr Kuznetsov, Srivatsan Ravi. *Brief Announcement: From Sequential to Concurrent:
Correctness and Relative Efficiency.* PODC 2012. DOI
[10.1145/2332432.2332480](https://doi.org/10.1145/2332432.2332480). Formalized version: the full version,
arXiv [1203.4751](https://arxiv.org/abs/1203.4751) v8, *Optimism for Boosting Concurrency* (2015); numbering
follows it.

**Verdict: ❌ Intent lost.** Both comparative claims that the paper is built around fail. The optimistic
list `I_RM` is not concurrency-optimal: it rejects an observable schedule (Theorem 3 is false), so the proof of
Corollary 4 ("`I_RM` supersedes `P` and `SM`") collapses. A deadlock-free pessimistic implementation accepts the
schedule σ that, according to Theorem 2(2), no implementation in `P` accepts. Compositionality of
LS-linearizability (Theorem 5) holds. The `SM` half of Theorem 2(1) holds with the definition of strict
serializability of Appendix C.1. The correctness of `I_RM` (Theorem 11) was not checked.

## Mistakes in the paper

### ❌ Theorem 3 (optimality of `I_RM`)
`I_RM` rejects an observable schedule `σ_bad` (`theorem_3_false`, `not_theorem_3`). In it, starting from
`{1, 3, 4}`, `contains(4)` reads `head` and `X₁`, then `remove(3)` runs completely, then `contains(4)` reads
`X₃` and `X₄` and returns `true`.

**Impact.** `I_RM` is not "optimal with respect to concurrency" (abstract, §6, §8). The proof of Corollary 4
collapses (next item). The experimental explanation in §8 ("`I_RM` is optimal") loses its basis.

<details><summary><b>Details.</b></summary>

`remove(3)`'s write to `X₁` marks `X₃` (line 27) before it returns. `contains(4)`'s read of `X₃` starts
later, so in every execution of `I_RM` it sees `r[X₃] = true` and returns `⊥` (line 15).

The schedule is observable, and in a much stronger sense than §6 requires. An honest history exports it: every
read returns the latest written value. After it, `contains(v)` run on the actual memory keeps the history
LS-linearizable for every `v` (`ObservableStrong`, `sigmaBad_observableStrong`). This also implies the literal
reading of the definition (`Observable`).

The proof breaks in subcase (1a). It claims that "no removed element can be read in a sequential execution of
`LL`", so the history is not locally serializable. But local serializability is per operation
(Definition 1). The witness for `contains(4)` is the sequential history without `remove(3)`, exactly as in
the paper's own Figure 1. Subcase (1b) ends with "there exist executions that export such schedules", which
proves nothing.

The rejection is proved against an over-approximation of Algorithm 1. Each shared access is atomic, the
interleaving is arbitrary, the client is arbitrary, the initial `t-var` is arbitrary, and a failed `cas` may
abort or retry with the current version (the refinement mentioned in §6). The model keeps `rbuf` across
operations; this changes nothing for `LL` clients, since every operation reads `head` and its successor before
its first write. So it applies to `I_RM` as described.
</details>

### ❌ Theorem 7 = Theorem 2, part 2 (no implementation in `P` accepts σ of Figure 2(a))
A lock-based implementation is deadlock-free, pessimistic, honest (hence obedient) and LS-linearizable, and it
accepts σ (`theorem_7_false`).

**Impact.** The claimed incomparability of `P` and `SM` loses its "TM beats every pessimistic implementation"
half. The illustration in Figure 2 and the discussion after Theorem 2 are wrong.

<details><summary><b>Details.</b></summary>

The implementation `I_LA` uses one global reader–writer lock, taken when the first read (of `head`) of an
operation responds. It is taken in shared mode if the operation does not change the abstract set of the
current memory (the implementation looks ahead with the operation's argument), and in exclusive mode
otherwise. Readers are linearized when they acquire the lock, a writer at its response. In σ both
`insert(1)` and `insert(2)` find their value present, so both run concurrently as readers.

The proof's step "if some `I ∈ P` accepts σ, it must also accept σ′" fails. It argues that "no process can
distinguish α and α′ before the read operations on `X₁` return". But the base objects after the two different
prefixes (`{1,2,3}` vs `{3}`) differ, and an implementation may inspect them.

The counterexample uses that the implementation of `read(head)` within `insert(v)` knows `v`. The paper allows
this: a process knows the operation it invoked, Algorithm 1 and `I_H` already branch on the operation type, and
lock-based implementations insert synchronization into the sequential code, where `v` is in scope. `P` is
restricted only by LS-linearizability, pessimism, deadlock-freedom and obedience, and the paper stresses that
it contains implementations "fine-tuned to the semantics of the type". `I_LA` can be built from a standard
reader–writer lock: take it in shared mode, check `v` against the list, and switch to exclusive mode if the
operation would change the set. We did not check whether Theorem 7 holds for implementations that cannot see
the arguments of operations.
</details>

### ❌ Corollary 4 (`I_RM` accepts every schedule accepted by `P` and `SM`)
The proof derives it from Theorem 3, which is false, plus the unproved remark that `SM` and `P` only accept
observable schedules. The schedule `σ_bad` rejected by `I_RM` is exported by an honest, LSL, quiescent,
safe-strict serializable history (`sigmaBad_sm`).

**Impact.** "`I_RM` strictly supersedes any pessimistic or TM-based implementation" is unsupported. TL2
(invisible reads, no validation of read-only transactions) accepts `σ_bad`, but we did not formalize a TM, so
the falsity of the statement itself is argued, not proved.

### 🔧 Theorem 6 = Theorem 2, part 1, `SM` half (no implementation in `SM` accepts σ₀ of Figure 1)
With the definition of §4, the proof fails. Acceptance looks only at `complete(H)`, while strict
serializability may use commit-pending transactions. A stalled commit-pending `remove(2)` that re-links
`X₁ := ⟨1, X₃⟩` makes an honest, LSL, safe-strict serializable history export σ₀ (`theorem_6_loophole`).

**Impact.** Local. Appendix C.1 restates strict serializability with complete operations only, and the paper's
two-case argument works for that definition (`theorem_6_appendix`).

<details><summary><b>Details.</b></summary>

The serialization is prefix, `insert(2)`, `insert(5)`, `remove(2)`, `contains(5)`. The early read of `X₁` by
`contains(5)` is legal there because `remove(2)` wrote the same value. The counterexample is a single
history; that a TM-based implementation in `SM` produces it (a value-validating TM such as NOrec, when the
process of `remove(2)` stops after its write-back) is argued, not formalized.
</details>

**Repair.** `theorem_6_appendix`: no history that is strictly serializable in the sense of Appendix C.1 (only
complete operations) and whose committed operations follow `LL` exports σ₀. With the §4 definition, the same
holds when every operation committed or aborted (`theorem_6_quiescent`).

### Typos
- Appendix D swaps the linearization points of writes: the write of `insert` is placed at "line 22", which is
  `remove`'s `cas`.
- The proof of Theorem 5 starts with its conclusion ("Let `H` … be LS-linearizable with respect to `IS`").
- §2 drops aborted reads and writes from exported histories, but `H|π` (§3) removes "the last aborted read or
  write". We keep `⊥` events.

## Proof gaps (statements true)

### 🔧 Theorem 5 (LS-linearizability is compositional)
The proof interleaves witnesses `S¹_π`, `S²_π` of both components and takes "any completion". Neither is
needed, because every operation acts on one object.

**Impact.** Statement true; proved directly (`theorem_5`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory with arbitrary base objects. Histories have two levels (high-level operations,
  reads and writes of the base objects of the sequential implementation) and `⊥` responses (`Basic.lean`).
  Linearizability is the amended Herlihy–Wing definition (CSLib).
- `LL` (Algorithm 2) is a program; `new-node` is a write to a fresh location. Σ_LL consists of the sequential
  runs from the empty list. The set type is a deterministic object (`ListSet.lean`).
- An implementation is the set of histories it exports: prefix-closed, receptive to every invocation of the
  `LL` client, and responding only to pending reads and writes. Responses may depend on the whole past.
  `ClassP` takes the strongest reading of `P`: every history LSL and honest, never `⊥`, and deadlock-free as
  "never stuck, and only boundedly many events can occur without new invocations before some operation
  returns" (`ImplModel.lean`).
- `I_RM` is an operational over-approximation of Algorithm 1, with one atomic step per shared access
  (`IRM.lean`). `SM` uses strict and safe-strict serializability with `Cseq` and commit-pending transactions
  as in §4 (`Serializability.lean`).
- Observability has a literal and a strong reading (`Observable.lean`). Schedules keep written values and
  forget read values and responses. Processes are natural numbers; the scheduler is adversarial; there is no
  randomness.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 3 (false) | `theorem_3_false`, `not_theorem_3`, `irm_rejects` | `IRMReject.lean` |
| §6 observability of `σ_bad` | `sigmaBad_observableStrong`, `sigmaBad_observable` | `Observable.lean` |
| Corollary 4 (proof broken) | `sigmaBad_sm` | `Corollary4.lean` |
| Theorem 7 / 2(2) (false) | `theorem_7_false`, `lookahead_classP`, `lookahead_accepts` | `Lookahead.lean`, `Theorem7.lean` |
| Theorem 6 / 2(1), `SM` half | `theorem_6_appendix`, `theorem_6_quiescent`, `theorem_6_loophole`, `sigma0_lsl` | `Serializability.lean` |
| Theorem 5 | `theorem_5` | `Composition.lean` |
| sequential correctness of `LL` (implicit in §2) | `soloRun_correct`, `soloRun_length_le` | `LLCorrect.lean` |

**Not formalized.** Theorem 11 / Lemmas 8–10 (`I_RM` is LSL); the pessimistic `I_H` of Theorem 6 (only "σ₀
is LSL" is proved); `I_C ∈ SM`; the experiments.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
`I_LA` is a non-vacuous member of `ClassP`. Linearizability comes from CSLib's Herlihy–Wing framework and the
linearization-point checker of `Podc/Computability/Distributed/SharedMemory/LinPointCheck.lean`. CSLib
candidates: `hwLinearizable_of_lpRun(')` (`LinCheck.lean`) and the window lemma (`KeptIdx.lean`).
