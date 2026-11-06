# The Impact of RDMA on Agreement — PODC 2019

Marcos K. Aguilera, Naama Ben-David, Rachid Guerraoui, Virendra Marathe, Igor Zablotchi. *The Impact of RDMA on
Agreement.* PODC 2019. DOI [10.1145/3293611.3331601](https://doi.org/10.1145/3293611.3331601). Formalized version:
arXiv [1905.12143](https://arxiv.org/abs/1905.12143) v2 (extended version, Feb 2021); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** Algorithm 7 (Protected Memory Paxos) violates agreement as printed, with a Lean run in which
two processes decide different values, but a one-line fix and one condition on the first ballot make it safe (proved).
Theorem 6.1 (no 2-deciding consensus with static permissions, for the read-first notion of "common-case execution") and
Lemma 4.1 (reliable broadcast from SWMR regular registers, `n ≥ 2f+1`) hold after local proof repairs. The Byzantine
algorithm beyond Lemma 4.1, and the termination and two-delay claims, the core of the paper's main point, were not
checked.

## Mistakes in the paper

### 🔧 Theorem D.2 (agreement of Protected Memory Paxos, Algorithm 7 line 21)
Algorithm 7 violates agreement: line 21 writes `(propNr, ⊥, ⊥)` into the leader's own slot, erasing its accepted
value, so a decided p2 that starts a new attempt lets p1 decide a different value (`theorem_D2_false`).

**Impact.** A local fix whose intent is recoverable from the paper makes the algorithm safe (`theorem_D1`,
`theorem_D2`), so the safety part of Theorem 5.1 survives.

**Details.**
- *The bug.* Line 21 writes `(propNr, ⊥, ⊥)` into the leader's own slot, which erases the value it accepted there
  earlier. The loop is `repeat forever`, so a process that has decided starts new attempts.
- *The run.* One memory, two processes, no crashes, unique ballots:
  1. p2 runs both phases and decides `true`.
  2. p2 starts a new attempt; its line-21 write erases `(2, 2, true)`.
  3. Before p2's phase-2 write, p1 takes the permission and reads: no slot holds a value, and no minProp is larger
     than its ballot.
  4. p1 writes its own input `false` and decides it. p2's next write fails.

  The run works under every reading of the ambiguous lines 24–26.
- *Where the proof fails.* The proof of D.2 assumes that a decided leader's slot still holds its value when a later
  leader reads it ("q must have seen p's value"). This is exactly what line 21 destroys.
- *Caveat.* The run needs the decided process p2 to start another attempt. The pseudocode allows this: `decide` sits
  inside `repeat forever`. But elsewhere the paper treats deciding as the end of the instance ("irrevocable
  decision", "p1 terminates, deciding", "the leader terminates one instance"). If `decide` ends the loop, this run
  is impossible, so a missing `return` after line 39 is an equally local fix (not formalized). Either way the D.2 proof
  reasons with the intended behaviour (a decided value stays in the decider's slot), not with the erasing one.

**Repair.** Keep the own accepted pair in the line-21 write, as in Disk Paxos. The prose ("write a new proposal
number in its slot") and Algorithm 10's `{propNr, -, -}` suggest this. With this fix (and the reading of lines 24–26
fixed by Algorithm 12), we prove D.1 and D.2 for any number of processes and memories, including zombie operations
of aborted attempts. (`theorem_D2_false`; repaired: `theorem_D1`, `theorem_D2`)

### 🔧 Theorem D.2 (Algorithm 7 line 13, p1's first ballot)
Protected Memory Paxos also needs p1's first ballot to be the smallest: the paper only says `propNr = a higher value
than any proposal number seen before`, and a first ballot of 100 lets two values be decided even with the line-21
fix (`first_ballot_not_minimal_false`).

**Impact.** One added condition restores agreement: only the lowest ballot may skip phase 1, the standard convention,
which we assume (`theorem_D2`).

**Details.** p1's first attempt skips phase 1 and has seen nothing, so it may pick, say, 100.
- *The run* (even with the line-21 fix; two processes, three memories):
  1. q decides `c` at ballot 5 on memories 2 and 3.
  2. p1's first attempt then writes `(100, 100, a)` on memory 1, where it still holds the initial permission, and
     aborts.
  3. q's next ballot 200 reads memories 1 and 2, adopts `a`, and decides it.
- *Where the proof fails.* Case 2 of the D.2 proof assumes that the minimal "bad" ballot performed phase 1, which this
  attempt did not.
- *Halting reading.* The Lean run again lets the decided q start a new attempt. If deciding ends the loop, a third
  process r can run ballot 200 instead of q, so the problem remains for n ≥ 3 (argued, not formalized).
- Ballot uniqueness is also only implicit. (`first_ballot_not_minimal_false`)

### 🔧 Lemma 4.1, Observation 1 (no slot written twice)
Observation 1 says no slot of a correct process is written twice, but `Value[p,k,p]` is written at line 12 and again
at line 40 (p echoes its own message), and `L2Proof[p,k,q]` at line 64 and again at line 18.

**Impact.** The overwrites are harmless: weaker invariants suffice and are proved; Lemma 4.1 holds (`lemma_4_1`).

**Details.** As a consequence line 38 must also accept the sender's own doubly signed echo.

**Repair.** All writes to a correct slot endorse one signed pair, a non-`⊥` slot stays non-`⊥`, and every `L2Proof` write
is valid. (`lemma_4_1`)

### ✏️ Slips
- **Algorithm 7, lines 24–26.** "Non-null value" and "highest propNr" do not say which slot field is meant. Read
  literally, a slot with a larger minProp and no value causes no abort, though the proof of D.2 needs one, and one
  reading adopts the leader's own fresh slot and decides `⊥`. Algorithm 12 prints the intended version, which we use
  (`theorem_D2`).
- **Theorem 6.1, one process or one value.** With one process, or a single possible value, a process decides at time 0,
  so we need `n ≥ 2` and two values (`theorem_6_1`).
- **Algorithm 2, line 27.** `try_deliver` starts at key `last[q] = 0` although keys start at 1, so taken literally
  nothing is ever delivered. With the evident fix Lemma 4.1 holds (`lemma_4_1`).
- **Algorithm 2, lines 38 and 47.** They check the reader's own signature (`sValid(p, ·)`) instead of the sender's, so
  a correct reader rejects valid values (`lemma_4_1`).

### Typos
- Algorithm 2: `state` must be per sender, line 30 uses an out-of-scope `proof`, and proof validity must require
  distinct signers, which is left unspecified.
- The proof of Observation 2 says `try_deliver` has no loops, but it has the finite `for i ∈ Π` loops.
- Lemma D.3 ("the values a leader accesses cannot change between when it reads them and when it writes them") holds
  only for a write that succeeds, which is what its proof shows.

## Proof gaps (statements true)

### 🔧 Theorem 6.1, proof (the arbitrary execution `E`)
The proof takes an *arbitrary* run E in which p decides in two delays and claims p cannot distinguish it from a run
where everybody else starts later, which is false if p's reads in E returned values written concurrently by others.

**Impact.** Statement true for the read-first notion of "common-case execution"; repaired (`theorem_6_1`,
`not_twoDeciding`). The paper never fixes how simultaneous operations are ordered, and on the other reading the theorem
fails: if "2-deciding" only requires *some* common-case run, and simultaneous operations may take effect write-first,
Theorem 6.1 fails for n = 2 (sketch in `differencies.md`, not formalized).

**Details.** In that sketch p2 writes its input while p1 reads it; p1 decides what it read, and both then run any
consensus algorithm with that value.

**Repair.** We take E to be the synchronous run in which simultaneous operations take effect reads first. There, p's
reads return the initial memory, and write responses are fixed by the static permissions. (`theorem_6_1`)

### 🔧 Theorem 6.1, proof ("p′ must eventually decide value v′")
The proof needs "p′ running alone must decide", which the model does not give when n ≥ 3 and only one crash is
tolerated, and it does not explain why p′ decides a value other than p's.

**Impact.** Statement true; repaired (`theorem_6_1`).

**Repair.** We let *all* processes except p run; to them p looks crashed. We give the others input v′ and use validity.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Theorem 6.1** (`LowerBound/Model.lean`).
  - *Memory and processes:* asynchronous shared memory, atomic registers with arbitrary *static* read/write
    permissions, a memory that never fails, crash-prone deterministic processes.
  - *Operations:* each is invoked, takes effect later, and its response is delivered later still. A process may have
    any number of pending operations.
  - *Safety:* agreement and validity are required in all executions.
  - *Termination:* required only in synchronous runs in which at most one process is crashed from the start. This
    is weaker than the paper's partial synchrony, so the impossibility is stronger.
  - *Time:* in the synchronous run an operation invoked at time `t` takes effect at `t+1` and is answered at `t+2`
    (two delays). Simultaneous operations take effect reads first.
  - *Result:* no process has decided by time 2, for any inputs (needs `n ≥ 2` and two values).
* **Protected Memory Paxos** (`PMP/Model.lean`).
  - *Model:* crash model with dynamic permissions; one region and one writer per memory; `getPermission` always
    legal.
  - *Asynchrony:* every operation is split into invoke, effect and response, with at most one outstanding
    operation per (process, memory). Threads of aborted attempts may still have operations in flight.
  - *Schedule:* Ω and the scheduler are arbitrary (safety only).
  - *Ballots:* unique, increasing per process; p1's first ballot is the smallest.
  - *Variants:* line 21 is a parameter (literal / repaired), so the counterexample and the proofs share one model.
* **Lemma 4.1** (`RB/Model.lean`).
  - *Registers:* asynchronous shared memory with SWMR *regular* registers (a read may return any value written
    concurrently).
  - *Failures:* `f` Byzantine processes, which write anything only to their own registers.
  - *Signatures:* abstract, unforgeable and transferable.
  - *Liveness:* properties (1) and (4) are proved for fair executions (every correct thread runs infinitely often,
    every write of a correct process completes).
  - *Property 2:* the paper's "r wrote before r′, so r′ later saw both" is read as "the write completed before the read
    was invoked", as regular registers require; ghost times make this formal (`RB.l1_agree`).

**Main results in Lean.** Namespace `Podc.RDMAAgreement`.

| Paper | Lean | File |
|---|---|---|
| Theorem 6.1 | `LowerBound.theorem_6_1`, `LowerBound.not_twoDeciding` | `LowerBound/Theorem61.lean` |
| Theorem 6.1, hypotheses satisfiable | `LowerBound.NonVacuity.hypotheses_satisfiable` | `LowerBound/NonVacuity.lean` |
| Theorem D.2 false for Algorithm 7 as written | `PMP.theorem_D2_false` | `PMP/Counterexample.lean` |
| p1's first ballot must be minimal | `PMP.first_ballot_not_minimal_false` | `PMP/FirstBallot.lean` |
| Theorem D.1 (validity), repaired Alg. 7 | `PMP.theorem_D1` | `PMP/Safety.lean` |
| Theorem D.2 (agreement), repaired Alg. 7 | `PMP.theorem_D2` | `PMP/Safety.lean` |
| Lemma D.4 | `PMP.lemma_D4` | `PMP/Safety.lean` |
| repaired Alg. 7 can decide | `PMP.repaired_nonvacuous` | `PMP/Safety.lean` |
| Lemma 4.1 (Definition 1, properties 1–4) | `RB.lemma_4_1` | `RB/Main.lean` |
| — property 1 / 2 / 3 / 4 | `RB.Exec.validity` / `RB.Exec.agreement` / `RB.Exec.integrity` / `RB.Exec.totality` | `RB/Validity.lean`, `RB/Safety.lean`, `RB/Totality.lean` |
| — core: L1 proofs of correct processes agree | `RB.l1_agree` | `RB/Core.lean` |
| Lemma 4.1, non-vacuity | `RB.lemma_4_1_nonvacuous` | `RB/Main.lean` |

**Not formalized.**
- Byzantine part: Robust Backup, Cheap Quorum, Preferential Paxos and the Fast & Robust composition
  (Theorems 4.2–4.9, Lemmas 4.3–4.8).
- Termination and the 2-deciding property of Protected Memory Paxos (D.6–D.8), hence those parts of Theorem 5.1, also
  for the repaired Algorithm 7.
- Aligned Paxos (§5.2).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`. The
hypotheses are shown satisfiable: Theorem 6.1 by a concrete 2-process consensus algorithm, the repaired PMP by an
execution in which a process decides, Lemma 4.1 by a fair execution delivering a broadcast. All models are
paper-local. CSLib candidates (not yet marked in code): the split-operation shared-memory model with read-first
synchronous runs (`LowerBound/Model.lean`), and the measure-based fairness lemma `RB.eventually_of_measure`.
