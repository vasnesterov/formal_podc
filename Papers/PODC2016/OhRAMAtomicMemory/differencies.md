# Differences between the formalization and the paper

Paper: T. Hadjistasi, N. Nicolaou, A. A. Schwarzmann, *Brief Announcement: Oh-RAM! One and a Half Round
Read/Write Atomic Memory*, PODC 2016. Formalized version: the full version *Oh-RAM! One and a Half Round
Atomic Memory*, arXiv:1610.08373v2 (Nov 2020), which contains the algorithms and proofs; numbering
(lines, lemmas, theorems) follows it.

## Mistakes (labeled)

1. 🔧 **Read message complexity (Table 1, §§3.2, 4.2, 5.1.2, 5.2.2).** The paper claims every read sends at
   most `|S|² + 2|S|` messages (`|S|² + 3|S|` for OhSam', OhMam'). In the printed code the test of line 53
   (`if relays[r] = |S|/2 + 1 then send readAck`) is *not* nested in the `if (operations[r] = read_op)` of
   line 51 (rendered page 6 checked). A server whose counter for a *newer* read of `r` equals `|S|/2 + 1`
   answers every stale `readRelay` of an older read with one more `readAck` carrying the old `read_op`.
   With `|S| = 3` a read gets `3 + 9 + 6 = 18 > 15` messages (`21 > 18` with the revised read):
   `ohSam_read_msgs_gt`, `ohMam_read_msgs_gt`, `ohSam'_read_msgs_gt`, `ohMam'_read_msgs_gt`
   (`Complexity.lean`). The run is failure-free (the paper's worst case), and the two reads together send
   `33 > 2 · 15` messages (`39 > 2 · 18` revised), so no attribution of the stale `readAck`s saves the bound
   (`ohSam_staleRun_two_reads`, `ohSam'_staleRun_two_reads`). Safety and
   liveness are not affected (the reader discards acks with an old `read_op`). Repair: nest line 53 in the
   `if` of line 51 (`Variant.fixAck`); then the claimed bounds hold for all four algorithms
   (`readMsgBound_fix`, `readMsgBound_fix_paper`, `ComplexityFix.lean`).
2. ✏️ **Order definition (§3.1, used for Theorems 5, 12, 16, 22).** "`ts_π` … the timestamp computed as the
   *maximum* ts at the completion of a read". The code (lines 12–13, 67–68) and every proof use the
   *minimum* timestamp of the `readAck`s (the introduction says "minimum" too). With "maximum" the order
   would violate A3. We use the returned (minimum) tag.
3. ✏️ **Fast-path return value (Algorithm 3, line 137).** `v ← {m.val | m ∈ rRelay}` collects the values of
   *all* received relays, which may carry several tags; the text (§5.1) says the reader returns "the value
   associated with the timestamp found in the readRelay messages collected from the majority". We return the
   value of the majority set `Z` (`fastVal`). Similarly lines 13/68/134 return a *set* of values; it is a
   singleton in every reachable state (one value per tag) and we return its element (`minVal`).

## Typos (claims unaffected)

- §5.1.2: "4|S| messages are exchanged during a write operation" of OhSam'; Table 1 and §3.2 say `2|S|`.
- Theorem 22, proof of A1 (writes): cites Lemma 21 instead of Lemma 20.
- Lemma 21, proof: "ρ decides on a tag that all servers attached in the set RA" — should be `RR` (the relays).
- §4: "The read protocol is identical to the one presented in section ??".
- Line 132: `if (rAck = |S|/2 + 1)` should be `|rAck|`.

## Proof imprecisions (statements true; closed in Lean)

- **Distinct servers.** Lemmas 2–4, 7–11, 14–15, 18–21 intersect "the majority of servers that sent readAck /
  writeAck / discoverAck / readRelay". The waits count elements of `rAck`, `wAck`, `mAck ⊆ S × M` and the
  counter `relays[r]` counts messages; that these are `|S|/2 + 1` *distinct* servers needs counting invariants
  over non-FIFO channels (one relay per server and read, one acknowledgment per server and current operation;
  stale `readAck`s of line 53 carry an older `read_op`): `CInv` (`SafetyMsg.lean`). For the fast path, relays
  with the same tag come from distinct servers because a tag determines its value (`Inv.val_unique`).
- **OhMam servers may skip the update (line 121, `write_ops[w] < write_op`).** Lemmas 8, 9 argue "by Lemma 6
  every server of WSet sends a writeAck with tag ≥ tg"; that needs that no later `writeRequest` of the same writer
  has reached the server while the write is pending (`CInv.wops`).
- **Termination.** The `=` tests of the waits (lines 11, 27, 66, 84, 90) and of line 53 fire because each count
  grows by one per step and is reset only by a newer `read_op`, impossible while the read is pending
  (`Liveness*.lean`). The OhSam write terminates only because no tag in the system exceeds the writer's `ts`, so
  `writeAck`s pass the filter `m.ts = ts` of line 30 (`Liveness.TInv`). The paper's liveness paragraphs do not
  mention these points.

## Modelling choices

- **Model.** CSLib `Cslib.AsyncMP` (`Cslib/Computability/Distributed/MessagePassing/Async.lean`):
  asynchronous processes, reliable non-FIFO channels (multiset `net`), crash failures of any process; a
  message whose sender crashed may be lost (`drop`, a generalization). Reliability of channels = weak
  fairness `Exec.Fair` (an enabled reception by a correct process eventually happens). Liveness assumes at
  most `f` *server* crashes with `2f < |S|` (`ServerResilient`); readers and writers may crash arbitrarily.
- **Processes.** `Node W R S` (writers, readers, servers). Writers only write, readers only read, servers
  invoke nothing (`invoke` returns `none` otherwise). OhSam(') has one writer (`W = Unit`).
- **Atomicity** = linearizability of every history of every reachable configuration (CSLib
  `Protocol.Linearizable`, `IsLinearization` for `register V v₀`); this covers incomplete operations, while
  the paper's A1–A3 are stated for executions in which all operations complete. Write responses are the
  written value (CSLib's `register` convention).
- **Atomic steps.** Each block of code between two `wait`s is atomic; every `wait until` is evaluated in
  the reception handler right after the reception that can make it true (the `=` tests of lines 11, 27, 53,
  66, 84, 90, 116 are therefore reached exactly). The MWMR write's discover-phase continuation (lines 85–89)
  runs in the same step as the reception of the `|S|/2+1`-st `discoverAck`.
- **Acknowledgment sets.** `rAck, rRelay, wAck, mAck ⊆ S × M` are lists without duplicates of triples
  `(sender, tag, value)`; the dropped fields of `m` (operation counter, sender id) are fixed by the filters
  (lines 16, 30, 71, 93, 140). Different `(sender, m)` pairs with the same triple would be identified; this
  happens only for identical messages.
- **Message fields.** Sender ids inside messages (`r` of `readRequest`, `sᵢ`, `w`) are taken from the
  channel. OhSam's `writeRequest`/`writeAck` carry a dummy `write_op = 0` (one message type for both write
  protocols; the single-writer protocol ignores it).
- **Tags.** One generic protocol `proto Vr next v₀` over any linear order `T` with bottom (the initial tag)
  and a tag generator `next`. OhSam(') use `T = ℕ`, `next _ t = t + 1` (exactly lines 6, 24, 37).
  OhMam(') use `Tag W = WithBot (ℕ ×ₗ W)` and `nextTag w t = ⟨ts(t) + 1, w⟩` (line 86; `maxTS` is the `ts`
  of the lexicographic maximum). The paper's initial server tags `⟨0, sᵢ⟩` (line 102, distinct per
  server, all with value `⊥`) and the reader's `⟨0, 0⟩` are replaced by one bottom tag `⊥`; all these tags
  carry the initial value and lie below every written tag, so nothing observable changes.
- **Ghost variable.** Servers carry `got : R → Finset S`, the senders of the relays counted in
  `relays[r]`; it does not influence the behaviour.
- **Line 53.** Modelled as printed (`fixAck = false`) for the four algorithms of the paper; `fixAck = true`
  is our repair, used only in `ComplexityFix.lean`.
- **Message complexity.** Messages of the `k`-th read of `r`: its `readRequest`s, the `readRelay`s and
  `readAck`s carrying `(r, k)` (`readMsgs`, counted in `Config.sent`).

## Not formalized

- Communication-exchange counts (2/3 exchanges per read, 2/4 per write, Table 1): immediate from the
  structure of the code; not stated in Lean.
- Write message complexity (`2|S|`, `4|S|`).
- §6 (NS3 simulations); the cited MWMR impossibility [6].
