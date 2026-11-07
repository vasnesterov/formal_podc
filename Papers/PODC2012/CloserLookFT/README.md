# A Closer Look at Fault Tolerance — PODC 2012

Gadi Taubenfeld. *A closer look at fault tolerance.* PODC 2012. DOI
[10.1145/2332432.2332484](https://doi.org/10.1145/2332432.2332484). Formalized version: the author's full
version of 22 February 2017 (22 pp., journal version Theory Comput. Syst. 62(5), 2018); numbering follows
it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** The headline results hold: the symmetric election algorithm with
`⌈log n⌉ + 2` registers is safe and almost-wait-free (Theorems 2.1–2.5), and weak resilience is no
better than standard resilience for colorless tasks (Lemma 6.1, Theorems 6.2–6.3, with the classical
impossibility results as hypotheses). But the safety proof of the election algorithm, an informal
credit argument, had to be rebuilt with a new invariant. The test-and-set algorithm of Section 3 is
wrong as printed (two winners); a one-condition fix is proved safe. The renaming, Common2 and
message-passing results (Sections 4–5, Theorem 2.6) and the liveness of the test-and-set bit
(Theorems 3.3–3.4) were not checked beyond per-object facts.

## Mistakes in the paper

### 🔧 Theorem 3.2 (test-and-set bit, safety)
The test-and-set algorithm of Section 3.1 has well-structured runs with two winners, already for
`n = 2` (`TAS.theorem_3_2_false`, 35-step schedule; also `n = 3`).

**Impact.** Theorem 3.1 (an almost-wait-free test-and-set from `n + 1` registers) fails as printed; the
history is not even linearizable (argued below, not formalized). Adding "`or locked = 0`" to the losing test at line 10 repairs
safety for every `n ≥ 2` (`TAS.theorem_3_2_fixed`). The users of Theorem 3.1 (Theorem 4.2,
Lemma 5.1/Theorem 5.2, Corollary 6.4) need the corrected algorithm.

**Details.** A process `q` may leave the `repeat` loop because it reads `winner = 1` (some `p` has
won). While `p` resets the bit (`winner := 0` written, `turn := 0` not yet), `q` reads `turn = q` at
line 10, then `winner = 0`, and wins without holding any lock. Meanwhile `p` finishes its reset and
wins again: it gets all locks, since `q` holds none. Now `p` and `q` are both winners. `q`'s operation
overlaps `p`'s first win, `p`'s reset and `p`'s second win; no linearization point is legal for it.
The proof of Theorem 3.2 assumes that "any other process has to set all the `n − 1` locks … to become
a winner", but line 10 does not test `locked`.

**Repair.** With the extra test, at most one process is a winner in every well-structured run, for
every `n ≥ 2` (`TAS.theorem_3_2_fixed`, an invariant counting the locks a candidate has lost against
the processes with pending lock writes and the processes still able to compete). Liveness and
linearizability of the corrected algorithm (Theorems 3.3–3.4, and the claim that they imply
linearizability) are not formalized.

### ✏️ Slips
- Theorem 2.2 ("in the absence of faults, at least one leader is elected") needs at least one
  participating process; we assume it (`exists_ret_true_of_no_crash`).
- Theorem 4.1's proof derives "at most `n − i + 1` processes participate in object `i`" from the
  election specification "in the absence of faults exactly one process is elected". Read for the
  whole run, this is too weak: a crash in a later object would let object `i` elect nobody while all
  its correct participants move on. The argument needs the per-object reading (faults among the
  object's own participants), which the Section 2 algorithm satisfies (`card_outFalse_lt`).
- The definition of *winner* before Theorem 3.2 ("the last completed operation is a winning
  test-and-set") also counts a process whose reset is still pending; with that literal reading even
  the corrected algorithm has two "winners" (one finishing its reset, one that has just won). Winners
  should be processes that have not invoked reset.

### Typos
- §3: the sequential specification and the definition of winner say a winning test-and-set returns 0;
  the algorithm returns 1 to the winner (line 14).
- §3.1 says the test-and-set algorithm "makes use of exactly `n` registers"; it uses `n + 1`, as
  Theorem 3.1 says. The proof of Theorem 3.4 refers to `done`, which is `winner` in this algorithm.
- Rule 3 of the credit system (proof of Theorem 2.4): "the last process to change `V[k]`'s value back
  to 0" should be "from 0 to its id".

## Proof gaps (statements true)

### 🛠️ Theorem 2.4 (election safety, credit argument)
The credit accounting is not well defined: credits move "between processes" per *maximal set of
processes that noticed together `V[k] = 0`*, but such sets overlap and the rules decide the receiver
by future behaviour, so "no new credits are created" is not actually checked.

**Impact.** Statement true; repaired with a precise ghost-state version of the credit argument
(`EReach.elected_unique`, `election_safety`).

**Details.** The paper itself calls the proof "rather challenging" because processes can erase each
other's writes (a process that read `V[j] = p` may write `0` after another process overwrote `V[j]`).
Maximal "noticed together" sets need not be disjoint. Example at level 1: `s`, `r`, `p`
write `turn` in this order and all read `V[1] = 0`; `s` writes `V[1]`, fails at line 10 and reads
`V[1] = s`; `r` overwrites `V[1]`; `s` writes `0` (erasing `r`'s value); `u` writes `turn`, reads
`V[1] = 0` and writes it; `p` overwrites `u`. Both `{p, r, s}` and `{p, u}` are maximal sets that
noticed `V[1] = 0` together, so Rules 3–4 may apply to `p` twice, and which transfer happens depends
on which process later continues.

**Repair.** Credits are ghost state: `V[j]` holds `2^j` while it is `0`, writing over `0` moves them
to the writer, writing `0` over a non-zero value moves `2^j` from the writer back, and when a process
overwrites `V[k]` while being *younger* (it wrote `turn` later) than the current owner of `V[k]`'s
credits, the owner hands them over. Each process must hold `2^k` at level `k`, `2^L` once elected,
and otherwise what it may still have to pay back plus a reserve for pending younger overwriters.
Lemma 2.3 becomes two invariants: a younger process never passes a level whose register still holds
an older passed process's identifier, nor is about to overwrite a register owned by an older process
that has passed it. With `n` processes there are only `n + 2^L − 1` credits, fewer than the `2^(L+1)`
two leaders would need when `n ≤ 2^L` (`Inv.elected_unique`). Candidate invariants were first checked
on all reachable states with a model checker (`n ≤ 5`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory with atomic registers: CSLib's `Impl` model (deterministic processes; one
  register access per step; infinite executions `InfExec`). The election algorithm is
  `electionImpl L` (registers `turn`, `done`, `V[0..L-1]`), with a ghost-free projection to a
  transition system (`ElectionCore.lean`) on which the invariants are proved.
- Crash failures: a process crashes if it stops taking steps while an operation is pending. No
  fairness assumption is needed for the others: a non-crashed pending process eventually steps.
  `(t, f)`-, almost-, partial- and weak resilience follow §1.3 literally
  (`Podc/Computability/Distributed/SharedMemory/Resilience.lean`, staged for CSLib). A process is
  *starved* if it is pending forever without crashing.
- Participation is not required (Sections 2–3); required participation (`AllParticipate`) in Section 6.
- Symmetric algorithms: identifiers come from an arbitrary type with decidable equality and are only
  compared; `0` is `none`. The test-and-set counterexample uses identifiers `1..n`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 2.1 (election with `⌈log n⌉ + 2` registers) | `theorem_2_1` | `ElectionLiveness.lean` |
| Theorem 2.2 (a leader is elected without faults) | `exists_ret_true_of_no_crash` | `ElectionLiveness.lean` |
| Theorem 2.4 (at most one leader, any `n ≤ 2^L`) | `election_safety`, `EReach.elected_unique` | `Election.lean`, `ElectionSafety.lean` |
| Theorem 2.5 (almost-wait-freedom) | `electionImpl_almostWaitFree`, `starved_unique`, `not_starved_of_no_crash` | `ElectionLiveness.lean` |
| `n ≤ 2^L` is needed (3 processes, 1 level: two leaders) | `two_leaders_three_procs_one_level` | `NonVacuity.lean` |
| Theorem 3.2 (test-and-set safety): **false** | `TAS.theorem_3_2_false` | `TestAndSet.lean` |
| Theorem 3.2 for the corrected algorithm, all `n ≥ 2` | `TAS.theorem_3_2_fixed` | `TestAndSetFix.lean` |
| Theorem 4.1, per-object facts | `card_outFalse_lt`, `Inv.elected_unique_of_started` | `RenamingFacts.lean` |
| Lemma 6.1 (weakly-`t`-resilient ⇔ `t`-resilient, colorless tasks, `t ≤ n − 2`) | `lemma_6_1` (`resilient_withOutput`, `solves_withOutput`) | `Section6.lean`, `ColorlessLiveness.lean`, `Colorless.lean` |
| Theorem 6.2 (no weakly-1-resilient consensus, `n ≥ 3`; Loui–Abu-Amara as hypothesis) | `theorem_6_2` | `Section6.lean` |
| Theorem 6.3 (no weakly-`k`-resilient `k`-set consensus; external result as hypothesis) | `theorem_6_3` | `Section6.lean` |

**Not formalized.** Theorem 2.6 (message passing); Lemma 2.3 as stated (replaced by invariants);
Theorems 3.3–3.4, Observation 3.5 and the linearizability claim of Theorem 3.1; the composition in
Theorem 4.1 and Theorem 4.2; Lemma 5.1 and Theorem 5.2 (they rest on the Common2 constructions of
[2, 3]); the message-passing parts of Section 6.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `elected_example` (a process is elected), Theorem 2.2 itself, and the
two-leader run for `L` too small. The test-and-set counterexamples are checked by `decide`. The
Python model checkers used to find counterexamples and invariants are in the work folder, not part of
the Lean development. Shared code: `Podc/Computability/Distributed/SharedMemory/Resilience.lean`
(CSLib candidate).
