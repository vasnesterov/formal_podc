# Oh-RAM! One and a Half Round Atomic Memory — PODC 2016

Theophanis Hadjistasi, Nicolas Nicolaou, Alexander A. Schwarzmann. *Brief Announcement: Oh-RAM! One and a
Half Round Read/Write Atomic Memory.* PODC 2016. DOI
[10.1145/2933057.2933073](https://doi.org/10.1145/2933057.2933073). Formalized version: the full version
*Oh-RAM! One and a Half Round Atomic Memory*, arXiv [1610.08373](https://arxiv.org/abs/1610.08373) v2 (Nov 2020),
which has the algorithms and proofs; numbering (lines, lemmas, theorems) follows it.

**Verdict: 🔧 Easy fix.** The four algorithms OhSam, OhMam, OhSam' and OhMam' are atomic and terminate when fewer
than half of the servers crash (Theorems 5, 12, 16, 22, fully proved). The only false claim is the per-read
message complexity of Table 1: with line 53 as printed, a server re-sends a `readAck` on every stale relay. Nesting
line 53 in the `if` of line 51 restores the claimed bounds.

## Mistakes in the paper

### 🔧 Table 1 and §§3.2, 4.2, 5.1.2, 5.2.2 (read message complexity)
In the printed code the test `relays[r] = |S|/2 + 1` of line 53 lies outside the `if (operations[r] = read_op)` of
line 51, so a read can cost more than the claimed `|S|² + 2|S|` messages: with `|S| = 3`, a read gets 18 > 15
(`ohSam_read_msgs_gt`, `ohMam_read_msgs_gt`; 21 > 18 for the revised reads, `ohSam'_read_msgs_gt`,
`ohMam'_read_msgs_gt`).

**Impact.** Only the message-complexity column of Table 1 is affected. Atomicity and termination hold for the
printed code, because readers discard acknowledgments with an old `read_op`.

**Details.** A server whose counter for a *newer* read of `r` sits at `|S|/2 + 1` answers every late `readRelay`
of an *older* read of `r` with one more `readAck` for the older read (line 53 is evaluated for every relay,
line 54 sends `read_op` of the message). The run: three servers, two consecutive reads by the same reader,
each completed with the relays of `s₀, s₁`; then the relays of `s₂` for the first read arrive, and each server
sends a stale `readAck`. The first read then has 3 `readRequest`s, 9 relays and 3 + 3 `readAck`s. The run is
failure-free (the paper's worst case) and checked by kernel evaluation. The count does not depend on how the stale
`readAck`s are attributed: the two reads together send 33 > 2 · 15 messages (`ohSam_staleRun_two_reads`).

**Repair.** Nest line 53 in the `if` of line 51 (`Variant.fixAck`). Then every read has at most `|S|² + 2|S|`
messages, `|S|² + 3|S|` in OhSam' and OhMam' (`readMsgBound_fix_paper`).

### ✏️ Slips
- §3.1 defines the order through "the *maximum* ts at the completion of a read"; the code (lines 12–13, 67–68),
  the introduction and all proofs use the *minimum* of the `readAck`s, as we do.
- Algorithm 3, line 137 returns `{m.val | m ∈ rRelay}`, the values of *all* received relays (possibly with several
  tags); the text says the value of the majority set `Z` with a common tag, which we return (`fastVal`).

### Typos
- §5.1.2 says an OhSam' write exchanges `4|S|` messages; Table 1 and §3.2 say `2|S|` (correct).
- Theorem 22, proof of A1 for two writes cites Lemma 21 instead of Lemma 20; Lemma 21's proof writes `RA` for
  the relay set `RR`; line 132 has `rAck` for `|rAck|`; §4 refers to "section ??".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- CSLib's asynchronous message passing `Cslib.AsyncMP`: reliable, **non-FIFO** point-to-point channels
  (multiset of messages in transit), crash failures of any process, deterministic processes. Channel
  reliability is weak fairness (`Exec.Fair`: an enabled reception by a correct process eventually happens).
  Termination assumes at most `f` *server* crashes with `2f < |S|` (`ServerResilient`); any number of readers
  and writers may crash. No randomness; the adversary is the scheduler.
- Processes `Node W R S`: writers write, readers read, servers serve. One protocol `proto Vr next v₀`
  (`Model.lean`) covers the four algorithms: `Vr.mw` selects the single-writer write (lines 18–31, 41–44) or
  the discover/update write (lines 73–94, 118–124), `Vr.fast` the revised read (Algorithm 3). Tags: `ℕ` with
  `t + 1` for OhSam('), `WithBot (ℕ ×ₗ W)` with `⟨maxTS + 1, w⟩` for OhMam('). The paper's initial tags
  `⟨0, sᵢ⟩` become one bottom tag (all carry the initial value).
- Each block of code between two `wait`s is atomic, and each `wait until … = |S|/2 + 1` is tested right after
  the reception that may make it true. Acknowledgment sets are duplicate-free lists of `(sender, tag, value)`.
  Servers carry a ghost field `got` (senders of the counted relays).
- Atomicity = linearizability (CSLib `IsLinearization` for `register V v₀`) of every reachable history,
  including histories with pending operations; the paper's A1–A3 cover complete executions only.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 5 (OhSam atomic + terminating) | `theorem_5_full` (`theorem_5`, `theorem_5_live`) | `Main.lean` (`Safety.lean`, `Liveness.lean`) |
| Theorem 12 (OhMam) | `theorem_12_full` (`theorem_12`, `theorem_12_live`) | `Main.lean` |
| Theorem 16 (OhSam') | `theorem_16_full` (`theorem_16`, `theorem_16_live`) | `Main.lean` |
| Theorem 22 (OhMam') | `theorem_22_full` (`theorem_22`, `theorem_22_live`) | `Main.lean` |
| Atomicity, any variant / tag generator | `proto_linearizable` | `Safety.lean` |
| Termination (liveness paragraphs of §§3.1, 4.1, 5.1.1, 5.2.1) | `proto_live`, `Liveness.Ex.read_terminates`, `Liveness.Ex.write_terminates` | `Liveness.lean` |
| Lemmas 1, 6, 13, 17 (server tags monotone) | `server_tag_mono`, `sRecv_tag_mono` | `Safety.lean`, `SafetySteps.lean` |
| Lemmas 2–4, 7, 9, 10, 14, 15, 18, 19 (reads after reads/writes) | field `Inv.prec_R` (via `Inv.rRecv`, `Inv.rComplete`), `Inv.read_rt` | `SafetyInv.lean`, `SafetyRecv.lean` |
| Lemmas 8, 11, 20, 21 (writes after writes/reads) | field `Inv.prec_W` (via `Inv.wDisc`, `Inv.disc_rt`; SWMR: `Inv.wInvoke_sw`) | `SafetyInv.lean`, `SafetyRecv.lean` |
| A1–A3 from the tags | `Inv.tsLin` + `Cslib.SharedMemory.TSLin.exists_isLinearization` | `Safety.lean` |
| Table 1, read messages: false as printed | `ohSam_read_msgs_gt`, `ohMam_read_msgs_gt`, `ohSam'_read_msgs_gt`, `ohMam'_read_msgs_gt` | `Complexity.lean` |
| Table 1, read messages: no attribution saves the bound | `ohSam_staleRun_two_reads`, `ohSam'_staleRun_two_reads` | `Complexity.lean` |
| Table 1, read messages: repaired | `readMsgBound_fix_paper` | `ComplexityFix.lean` |

The proofs follow the paper (ABD-style timestamp order; "a majority of servers holds a tag ≥ the tag of every
completed operation", then quorum intersection), but they need facts that the paper leaves implicit; none of them
fails:
- the acknowledgment and relay sets have `|S|/2 + 1` *distinct* servers. With non-FIFO channels and stale messages
  this takes counting invariants: one relay per server and read, one `readAck`/`discoverAck`/`writeAck` per server
  and current operation (`CInv` in `SafetyMsg.lean`). The stale `readAck`s of line 53 carry an old `read_op`
  and never count;
- an OhMam server skips the update when `write_ops[w] ≥ write_op` (line 121), so "the writeAck carries a tag
  ≥ the write's tag" needs that no later request of the same writer exists yet (`CInv.wops`);
- the `=` tests of the waits and of line 53 fire because each counter grows by one per step and is reset only
  by a newer `read_op`, which cannot exist while the read is pending (`Liveness*.lean`);
- the single-writer `writeAck` filter `m.ts = ts` (line 30) lets the write terminate only because no tag in the
  system exceeds the writer's (`Liveness.TInv`).

**Not formalized.** The counts of communication exchanges (2 or 3 per read, 2 or 4 per write), which are read
off the code; the write message complexity; §6 (simulations); the cited MWMR impossibility.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
counterexample runs and the sanity runs are checked by `decide +kernel`. Non-vacuity: for each algorithm, a
write followed by a read completes with the written value in a run that extends to a fair execution without
crashes (`sanity_*`, `fair_exec_exists`, `Sanity.lean`). The model is CSLib's
`Cslib/Computability/Distributed/MessagePassing/Async.lean`; linearizability goes through the staged
`Podc/Computability/Distributed/SharedMemory/TimestampLin.lean`. The `Generic` section of `LivenessSteps.lean`
(reliable delivery between correct processes, `net ⊆ sent`) is a CSLib candidate.
