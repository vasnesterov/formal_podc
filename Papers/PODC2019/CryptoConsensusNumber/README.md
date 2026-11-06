# The Consensus Number of a Cryptocurrency — PODC 2019

Rachid Guerraoui, Petr Kuznetsov, Matteo Monti, Matej Pavlovič, Dragos-Adrian Seredinschi. *The
Consensus Number of a Cryptocurrency.* PODC 2019. DOI
[10.1145/3293611.3331589](https://doi.org/10.1145/3293611.3331589). Formalized version: arXiv
[1906.05574](https://arxiv.org/abs/1906.05574) v1 (extended version, the only arXiv version; the journal version, Distributed Computing 2022, was not checked);
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** Theorem 2 (consensus number exactly `k`, `k ≥ 1`), Corollary 1 and Lemma 2 hold, but
the wait-freedom proof of Lemma 2 is false as stated and we replaced it with a new potential argument. Theorem 1
needs a local change to Figure 1, the linearizability proof of Lemma 2 needs local repairs, and Figure 4 needs a
one-term fix, which we prove only on the counterexample. The safety of the message-passing algorithm (Theorem 3)
was not checked.

## Mistakes in the paper

### 🔧 Theorem 1 (Figure 1 is not linearizable as written)
Figure 1 keeps successful transfers in a set `ops_p`, so repeating an identical transfer is never
debited: an owner with balance 2 calls `transfer(a, b, 1)` three times solo and all three return
`true` (`Fig1.Bug.literal_not_linearizable`).

**Impact.** That is double-spending, the very thing the paper sets out to prevent, but the intent is evident:
Figure 3 tags transfers with unique sequence numbers.

**Details.** Each process adds `(a, b, x)` to the set `ops_p`. Repeating an identical transfer therefore
does not change `ops_p`, so the second withdrawal is never debited.

**Repair.** Keeping `ops_p` as a sequence is a two-line change, after which the paper's proof goes through with
its linearization points (`Fig1.fig1_linearizable`, `Fig1.fig1_waitFree`).

### 🔧 Lemma 2, proof ("the linearization of a prefix of `E` is a prefix of `L`")
The side claim that prefixes linearize to prefixes is false, because failed transfers are linearized
retroactively at the proposer's snapshot.

**Impact.** The claim is not needed for linearizability, and the paper's linearization points stay.

**Repair.** We drop the claim and insert such operations retroactively (`Fig3.fig3_linearizable`).

### ✏️ Slips
- Lemma 3 and Theorem 3, liveness (Figure 4, line 25). Figure 4 as written blocks a correct process that spends
  money it has just received: process 0 (balance 5) pays 5 to process 1 (balance 0), and process 1's transfer of
  the 5 back never returns, even with two correct processes and a perfect broadcast (`Fig4.lemma_3_false`). A
  process may spend `balance(a, hist[p] ∪ deps)`, i.e. including freshly received incoming transfers `deps`, and it
  ships them as the dependencies `h`. Validation (line 25), however, checks `balance(c, hist[q])` *without* `h`, and
  incoming transfers enter `hist[q]` only after a later transfer of `q` has been validated. So process 1's message
  is invalid at every process forever. As written this falsifies Theorem 3, since Definition 1 requires every
  operation of a correct process to return; only the safety part of Theorem 3 is unaffected. The intended check is
  `balance(c, hist[q] ∪ h) ≥ y`: line 2 spends that amount, and Lemma 3's proof assumes the receiver's check passes
  because the sender checked its balance. With it the transfer completes (`Fig4.fixed_completes`). Lean shows this
  on the counterexample only, not Theorem 3 for the fixed algorithm.
- Theorem 2 for `k = 0`. With "`k`-shared" defined as `max_a |μ(a)| = k`, an object whose accounts have no owner is
  `0`-shared, but its consensus number is 1, not 0, since one process always solves consensus (`atSolvable_one`).
  For `k ≥ 1` Theorem 2 holds (`theorem_2`).
- The transition relation `Δ` is not total, contrary to the paper's assumption: a self-transfer
  `transfer(a, a, x)` with `x > 0` has no successor state. We use "debit, then credit".
- Figure 4's `balance` omits initial balances, so taken literally no transfer of a positive amount ever succeeds.
  The prose of Section 3 includes them.
- Definition 1 (2) cannot hold for finite executions, and it also covers reads and failed transfers of other
  processes. The comment after the definition gives the intended reading.

### Typos
- Figure 3's `proposal((a, b, q, x), ·)` has the wrong arity.
- The successful-transfer case of Lemma 2's proof writes `L_k` where `L_s` is meant.

## Proof gaps (statements true)

Figure 3 implements asset transfer from a snapshot, registers and `k`-consensus objects. The algorithm is correct,
and we proved it linearizable and wait-free (`Fig3.fig3_linearizable`, `Fig3.fig3_waitFree`).

### 🛠️ Lemma 2, wait-freedom
The argument "some instance will be only accessed with `o`" is false as stated: processes with stale `collected`
sets keep proposing other transfers.

**Impact.** The paper's argument does not survive; the statement does.

**Repair.** We replace the wait-freedom argument with a potential argument. (`Fig3.fig3_waitFree`)

### 🔧 Lemma 2, incomplete transfers
The linearizability proof completes incomplete transfers "with response true" even when they were decided as
failures.

**Impact.** One-line change: complete them with the decided response, or linearize at the proposer's snapshot.
(`Fig3.fig3_linearizable`)

### 🔧 Lemma 2, non-owner transfers (lines 1–2)
The proof gives no linearization point to non-owner transfers.

**Impact.** One extra case: we linearize them at their invocation. (`Fig3.fig3_linearizable`)

### 🔧 Lemma 2, successful-transfer case
The proof leaves the key "no outgoing transfer in between" step unjustified.

**Impact.** A few lines from the round ordering the paper already mentions. (`Fig3.fig3_linearizable`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Consensus numbers (`System.lean`) use CSLib's asynchronous shared-memory model
  `Cslib.SharedMemory.Recoverable`, without crashes. There are `n` deterministic processes with
  binary inputs and wait-free consensus (`WFConsensus`; crash-stop = stop taking steps). The objects
  are any read/write objects (`ObjSpec.RWLike`: every operation is read-only or a blind write) plus any number
  of asset-transfer objects, each with its own owner map, with arbitrary initial values.
  `ATSolvable n k` means `n`-process consensus is solvable when every account has at most `k`
  owners.
* Linearizability and wait-freedom (Theorem 1, Lemma 2) use CSLib's `Impl` model: deterministic
  processes, atomic base objects, `IsLinearization` (Herlihy–Wing, amended), `WaitFree`. Figure 1's
  base object is an atomic snapshot. Its read/write implementation (Afek et al.) is cited by the
  paper and not formalized.
* CSLib object specifications do not see the caller, so `transfer` carries the invoking process as
  an argument. Algorithms must use their own identity (`allowed` / `Honest`). All own transfers and
  all reads are allowed, and Lemma 1's algorithm is proved honest.
* Figure 4 is modelled only as far as the counterexample needs: two correct processes and
  per-sender FIFO exactly-once delivery (integrity and source order). The claim covers all
  extensions.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (Fig. 1, sequence-fixed): linearizable, wait-free, single owner | `Fig1.fig1_linearizable`, `Fig1.fig1_waitFree` | `Fig1.lean` |
| Fig. 1 as written is not linearizable | `Fig1.Bug.literal_not_linearizable` | `Fig1Bug.lean` |
| Corollary 1 (consensus number 1) | `corollary_1` | `Main.lean` |
| Lemma 1 (Fig. 2: `k`-consensus from one `k`-shared object) | `Lemma1.lemma_1`, `atSolvable_self` | `Lemma1.lean`, `Main.lean` |
| Lemma 2 (Fig. 3: `k`-shared AT from snapshot + registers + `k`-consensus) | `Fig3.fig3_linearizable`, `Fig3.fig3_waitFree` | `Fig3Lin.lean`, `Fig3WF.lean` |
| Theorem 2 (consensus number exactly `k`, `k ≥ 1`) | `theorem_2` | `Main.lean` |
| "At most `k`" (direct valency proof, any `n > k`) | `no_consensus` | `Impossibility.lean` |
| `k = 0` degenerate case | `atSolvable_one` | `Main.lean` |
| Lemma 3 false for Fig. 4 as written / fixed version completes | `Fig4.lemma_3_false`, `Fig4.fixed_completes` | `Fig4.lean` |

`theorem_2` states `ATSolvable k k ∧ ∀ n > k, ¬ ATSolvable n k`. The upper bound is proved
directly rather than through Lemma 2. At a critical configuration all processes are poised on one
object. A read, a failing transfer or a blind write cannot be critical. Successful transfers from
different accounts commute. So every two processes on opposite teams withdraw from one common
account. Every process is on some team, so all `n` processes own that account, and `n ≤ k`
(`at_pair`, `no_consensus`; generic lemmas `Team.false_of_absorb`, `Team.false_of_commute`,
`Crit.not_forall_poised_of_rwLike` in `Cslib/Computability/Distributed/SharedMemory/Recoverable.lean`).
This needs neither the cited `k`-consensus hierarchy result nor composition of implementations,
and it allows any number of objects with different owner maps.

**Not formalized.** The read/write implementation of atomic snapshots, and composition of implementations (so Lemma 2 is stated from an atomic snapshot). Theorem 3 (safety of
Figure 4 under Byzantine faults with secure broadcast), also for the fixed check. Section 6 (BFT-based `k`-shared
transfers in message passing; informal).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: Lemma 1's algorithm satisfies all hypotheses of the consensus model
(`atSolvable_self`). `Fig1.Example` instantiates Theorem 1 for a concrete owner map, and
`Fig1.allowed_iff` shows the access discipline allows all reads and own transfers. The valency
machinery comes from CSLib (`Cslib/Computability/Distributed/SharedMemory/Recoverable.lean`). From the
shared library: `ObjSpec.RWLike` (`Cslib/Computability/Distributed/SharedMemory/ObjClasses.lean`), `wfConsensus_of_inv` and
`inv_run_crashFree` (`Cslib/Computability/Distributed/SharedMemory/Recoverable.lean`), the retroactive-insertion toolkit
`IsLinearization.insert`, `ObjSpec.respIn` (`Cslib/Computability/Distributed/SharedMemory/LinPoints.lean`) and
`InfExec.exists_good`, `InfExec.run_pre` (`Cslib/Computability/Distributed/SharedMemory/Potential.lean`), the
current operation instance `curOp` and `opOf_append_of_eq_some`, `linState_concat`
(`Cslib/Computability/Distributed/SharedMemory/History.lean`), and `Fintype.sum_comp_update_add`
(`Cslib/Foundations/Data/Finset/SumUpdate.lean`).
`Fig3Example.lean` instantiates Lemma 2 (2 processes, one shared account, `k = 2`). CSLib candidates:
`snapObj`, `kConsObj`, and
`not_mem_append_single` (`Fig1.lean`).
