# The Consensus Number of a Cryptocurrency — PODC 2019

Rachid Guerraoui, Petr Kuznetsov, Matteo Monti, Matej Pavlovič, Dragos-Adrian Seredinschi. *The
Consensus Number of a Cryptocurrency.* PODC 2019. DOI
[10.1145/3293611.3331589](https://doi.org/10.1145/3293611.3331589). Formalized version: arXiv
[1906.05574](https://arxiv.org/abs/1906.05574) v1 (extended version, the only arXiv version; the journal version, Distributed Computing 2022, was not checked);
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** For the message-passing algorithm of Figure 4 as written, Lemma 3 and the
liveness part of Theorem 3 are false: a correct process that spends money it has just received
blocks forever, even with two correct processes. We prove that the fix `balance(c, hist[q] ∪ h)` makes
that transfer complete. Theorem 2 (consensus number exactly `k`, `k ≥ 1`) and Corollary 1 hold, and
Theorem 1 holds once a set-vs-sequence slip in Figure 1 is fixed.

## Mistakes in the paper

* **Lemma 3 (liveness of Figure 4) is false as written.** A process may spend
  `balance(a, hist[p] ∪ deps)`, i.e. including freshly received incoming transfers `deps`, and it
  ships them as the dependencies `h`. Validation (line 25), however, checks `balance(c, hist[q])`
  *without* `h`, and incoming transfers enter `hist[q]` only after a later transfer of `q` has been
  validated. Example with two correct processes and a perfect broadcast: process 0 (balance 5) pays
  5 to process 1 (balance 0). Then process 1 pays the 5 back. That message is invalid at every
  process forever, so process 1's `transfer` never returns. The intended check
  `balance(c, hist[q] ∪ h) ≥ y` fixes it. This is a liveness bug in the pseudocode. It also falsifies
  Theorem 3 as stated, since Definition 1 requires every operation of a correct process to return;
  only the safety part of Theorem 3 survives. (`Fig4.lemma_3_false`; with the fix: `Fig4.fixed_completes`)
* **Figure 1 is not linearizable (Theorem 1 as written).** Each process keeps its successful
  transfers in a set `ops_p` and adds `(a, b, x)` to it. Repeating an identical transfer therefore
  does not change `ops_p`, so the second withdrawal is never debited. Example: an owner with
  balance 2 calls `transfer(a, b, 1)` three times solo, and all three return `true`. That is
  double-spending, the very thing the paper sets out to prevent. This is a slip with an evident intent:
  Figure 3 tags transfers with unique sequence numbers. The literal pseudocode is wrong; it is repaired by keeping `ops_p` as a sequence, after which the paper's proof goes through
  with its linearization points. (`Fig1.Bug.literal_not_linearizable`; repaired:
  `Fig1.fig1_linearizable`, `Fig1.fig1_waitFree`)
* **Lemma 2's proof has gaps; its statement is true.** The algorithm of Figure 3 (asset transfer
  from a snapshot, registers and `k`-consensus objects) is correct, and we proved it linearizable
  and wait-free. The linearizability proof has four gaps:
  * it completes incomplete transfers "with response true" even when they were decided as failures;
  * it gives no linearization point to non-owner transfers;
  * it claims prefixes linearize to prefixes, which fails because failed transfers are linearized
    retroactively at the proposer's snapshot;
  * it leaves the key "no outgoing transfer in between" step unjustified.
  The wait-freedom argument ("some instance will be only accessed with `o`") is false as stated:
  processes with stale `collected` sets keep proposing other transfers. We replace it with a
  potential argument. (`Fig3.fig3_linearizable`, `Fig3.fig3_waitFree`)
* **Degenerate case `k = 0` of Theorem 2.** With "`k`-shared" defined as `max_a |μ(a)| = k`, an
  object whose accounts have no owner is `0`-shared. Its consensus number is 1, not 0, since one
  process always solves consensus. (`atSolvable_one`)
* **Small slips.** The transition relation `Δ` is not total, contrary to the paper's assumption: a
  self-transfer `transfer(a, a, x)` with `x > 0` has no successor state. We use "debit, then
  credit". Figure 4's `balance` omits initial balances. Figure 3's `proposal((a, b, q, x), ·)` has
  the wrong arity. Definition 1 (2) cannot hold for finite executions.

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
(`at_pair`, `no_consensus`; generic lemmas `crit_overwrite`, `crit_commute` in `Valency.lean`).
This needs neither the cited `k`-consensus hierarchy result nor composition of implementations,
and it allows any number of objects with different owner maps.

**Not formalized.** The read/write implementation of atomic snapshots, and composition of implementations (so Lemma 2 is stated from an atomic snapshot). Theorem 3 (safety of
Figure 4 under Byzantine faults with secure broadcast). Section 6 (BFT-based `k`-shared transfers
in message passing; informal).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: Lemma 1's algorithm satisfies all hypotheses of the consensus model
(`atSolvable_self`). `Fig1.Example` instantiates Theorem 1 for a concrete owner map, and
`Fig1.allowed_iff` shows the access discipline allows all reads and own transfers. The valency
machinery comes from CSLib (`Cslib/Computability/Distributed/SharedMemory/Recoverable.lean`). From the
shared library: `ObjSpec.RWLike` (`Podc/SharedMemory/ObjClasses.lean`), `wfConsensus_of_inv` and
`inv_run_crashFree` (`Podc/SharedMemory/Recoverable.lean`), the retroactive-insertion toolkit
`IsLinearization.insert`, `ObjSpec.respIn` (`Podc/SharedMemory/LinResp.lean`) and
`InfExec.exists_good_of_measure`, `InfExec.run_lbls` (`Podc/SharedMemory/Progress.lean`).
`Fig3Example.lean` instantiates Lemma 2 (2 processes, one shared account, `k = 2`). CSLib candidates:
`snapObj`, `kConsObj`, `crit_overwrite`, `crit_commute`, `stepP_stepP_same`, and the generic
linearization lemmas in the `Aux` section of `Fig1.lean`.
