# Differences between the formalization and the paper

Paper: J. Chalopin, Y.-J. Chang, G. A. Di Luna, H. Zhou, *Efficient Counting and Simulation in
Content-Oblivious Rings*, PODC 2026; full version arXiv 2603.28260v1 (numbering follows it).

Classification: **[false]** false statement · **[degenerate]** false only in a degenerate or unused
case · **[gap]** proof gap, statement true · **[under-spec]** under-specified definition ·
**[typo]** typo / slip · **[model]** modelling choice of the formalization.

## Model

- **[model]** Content-oblivious oriented ring on `ZMod n` for every `n ≥ 1` (`n = 1`: self-loop,
  `n = 2`: double link), from `Podc/ContentOblivious/Model.lean`. Channels are pulse counters
  (pulses are indistinguishable, so this is the paper's "FIFO w.l.o.g."). The adversary delivers
  any pulse in transit to a node that is willing to read that port; a blocking `receive` on a
  specific port = the node reads only that port, `receive on port q` (any) = both ports. Nodes are
  deterministic; all start at time 0; inputs (leader flag, bits, messages, IDs) via `Prog I`.
- **[model]** "Terminates / quiescently terminates" is stated finitely: a bound on the pulses of
  every execution (so every execution is finite, `exists_final`) and properties of every *final*
  configuration (no step possible): every node has returned and no pulse is in transit.
- **[model]** Theorem 9 / Definition 8 (composable ending property) are replaced by a semantic
  condition `Proc.Composable` (`Podc/ContentOblivious/Compose.lean`): bounded + quiescent
  termination + `clean` (a node that has not returned and is ready to read from a neighbour that
  has returned has a pulse of the current procedure in transit). Definition 8 implies `clean`.
  We prove a generalization of Theorem 9 for arbitrary sequences of stages chosen by the nodes'
  local states (`Podc.ContentOblivious.Schedule.final`, `.totalSent_le`, `.composable`), which is
  what Algorithms 5, 6 and 10 and the simulation of Theorem 14 need (loops of procedures).

## Section 4–6 (composition, ComputeOR, bit sending, message exchange, simulation)

- **[false] Lemma 16 / Theorem 17: CCWBitRelay with a relay *leader* does not have the
  composable ending property** (the paper explicitly covers this case: Lemma 16 "If the leader is
  a CCWBitRelay…", Algorithm 8 lines 2–3, 6). After forwarding the termination wave the relay leader keeps
  receiving on *any* port (Algorithm 8, line 5), i.e. it waits on the wave's port `d`, which
  Definition 8 forbids. Its clockwise neighbour returns first and may already send pulses of the
  next procedure into that port; the relay leader consumes them as pulses of the current round.
  Exhaustive check (`modelcheck/t_relaycomp.py`, `t_pairs.py`): two consecutive CCW rounds (or two
  CW rounds) with a relay leader on `n = 3` give wrong outputs; with an active leader every pair of
  procedures composes correctly, and alternating CW/CCW rounds (as in MsgExchange) also happen to
  work with a relay leader. Theorem 14 assumes an active leader and is unaffected; Theorem 22 as
  stated (and §9.2, whose relays may include the leader) covers a relay leader, and its proof relies
  on this false claim. Lean, composed outputs: `BitSending.relay_leader_composition_wrong` (n = 3,
  relay leader 0, active 1 and 2, two CCW rounds; a 16-step execution ends final and quiescent with
  process 2 holding `[0, ⊥]` instead of `[⊥, 0]`). Lean: `BitSending.not_composable_relay_leader` (`¬ proc.Composable (oriented 2) xRelay`:
  node 0 relay leader, node 1 active with `⊥`; the witness configuration `cRelay` is reached in
  three steps) and `BitSending.cw_not_composable_relay_leader`. A single round with a relay leader
  is still correct (outputs, quiescent termination, `≤ 6n` pulses: `BitSending.final_spec`,
  `returns`, `totalSent_le` hold for any leader position).
- **[gap] Theorem 22 with a relay leader.** Theorem 14 makes the leader active, Theorem 22 does
  not say so. Its proof composes the rounds via Theorem 9, which needs the (false, see above)
  composable ending of Theorem 17 for a relay leader. Random-schedule testing of Algorithms 5–6 with
  a relay leader (`n ≤ 6`, messages ≤ 3 bits) found no error — the alternation CW/CCW/ComputeOR
  happens to be safe — but this case has no proof; we prove Theorem 22 with an active leader.
- **[gap] Lemma 16** (a maximal relay segment is "equivalent to a single link") is asserted without
  proof. The formalization does not use it: outputs, quiescent termination and the `6n` bound of
  Theorem 17 are proved directly for arbitrary relay sets.
- **[under-spec]** Algorithm 7 does not say what is returned when `in ≥ 3`; this never happens
  (`in ≤ 2`).
- **[typo]** Algorithm 5, comments of lines 4, 5, 11, 12: "`⊥` if `phase > len(msg)`" should be `≥`.
- **[model]** Algorithms 5–6: we store the received values including `⊥` and decode by dropping
  `⊥` (`List.filterMap id`); the paper's `bitencode` is not specified.
- **[model]** Theorem 14: a synchronous ring algorithm is a `SyncAlg` (state → messages to the two
  neighbours; state × received messages → new state) run for a number of rounds `T` known to all
  processes; relays have no messages. The cost bound is explicit: round `k` costs at most
  `15·n·b_k + 3·n` pulses, `b_k` = longest message of round `k` (Theorem 22's `15nL + 3n`).

## Section 5 (anonymous counting)

- **[false] Distance formula (p. 9).** For processes counted in a completed phase
  (`myPhase < i`) the paper's `d = myPhase(myPhase+1)/2 − k − 1` is off by one: the correct value is
  `myPhase(myPhase+1)/2 − k`. Also the original leader has `myPhase` undefined (it is never probed),
  so the formula does not apply to it (its distance is 0). Counterexample: `n = 2`, the non-leader
  gets `d = 0` (the leader's distance) instead of 1. The model checker confirms the corrected
  formula for all `n ≤ 40`. Lean: `AnonCounting.paperResult_off_by_one` (the formula yields `d − 1`
  for every process with `myPhase < i`), `paperResult_wrong` (for every `n ≥ 2` the clockwise
  neighbour of the leader computes 0 instead of 1), `paperResult_two` (`n = 2`),
  `paperResult_leader` (undefined at the original leader). The algorithm itself is correct with the
  corrected formula `corrDist` (`anonCount_final`).
- **[model] Under-specified pseudo-code, fixed by choice:** SndCount sends the bits of `count`
  least significant first and nothing for `count = 0`; the leader terminates after SndCount (its
  "return n"); `myPhase` is `none` until written. The counting result does not depend on these.
- **[gap] Lemma 10** calls items (4)–(5) "immediate corollaries", and its premise says `p₀` has
  `counted = false` (it has `counted = true`; `p₁ … p_i` are the uncounted ones). The formalization
  proves the full per-phase structure for every reachable configuration (`reach_inv`) and reads
  off (4)–(5) at the end (`final_data`; `relayed` is one larger there because of the completion
  probe).
- **[model] Theorem 13 / 4** with explicit constants: every execution sends exactly
  `totalPulses n ≤ 6n⌊√(2n)⌋ + 8n ≤ 12n⌊√n⌋ + 14n` pulses (`totalPulses_le`, `totalPulses_le_sqrt`;
  exact values for `n = 1..9`: 6, 18, 34, 48, 70, 98, 104, 134, 170, `totalPulses_small`).
- **[typo]** Theorem 4 / §5: `d ∈ [0, n]` should be `[0, n−1]`.
- **[typo]** Lemmas 11–12 index the last phase as `⌈n^0.5⌉`; the number of phases is the `i` with
  `i(i−1)/2 + 1 ≤ n < i(i+1)/2 + 1`, i.e. about `√(2n)` (e.g. `n = 40` has 9 phases, `⌈√40⌉ = 7`).
  The asymptotic bound is unaffected (`lastPhase_spec`, `lastPhase_forty`).

## Section 9.1 (minimum finding)

- **[false → fixed] Algorithm 10, line 8:** the bit loop runs `while phase < len(bits)` with the
  process's *own* length, so processes with longer inputs would call ComputeOR more often than the
  others and the calls would no longer match. The text says inputs are "represented as a bit string
  of equal length B"; we loop `while phase < B`.
- **[under-spec]** Algorithm 10 needs at least one participant (otherwise the length search never
  stops) and non-empty encodings (`|0| = 1`). In §9.2 the first is guaranteed by the
  `ComputeOR(eligible)` guard.
- **[model]** Theorem 5 is proved with the explicit bound `6·n·|xmin|` pulses, `|x| = ⌊log₂ x⌋ + 1`
  (the paper's count `2B` calls of ComputeOR, 3n pulses each).

## Section 8 (aggregation, Theorem 1, Corollary 2)

- **[false → fixed] λ-preprocessing (proof of Theorem 1).** With the input "identifier length is
  at most i" and "stop at the first false outcome" the loop stops at `i = 1` unless some ID has one
  bit, and "the largest index with outcome true" then does not exist. We use
  `ComputeOR(size(ID) ≥ i)`, stop at the first false outcome, and set `λ = i − 1`.
- **[under-spec] Self-decomposability.** "f(X₁ ⊎ X₂) = f(X₁) ⊕ f(X₂) for disjoint multisets",
  read literally, excludes counting (`{1}` and `{1}` are not disjoint); what is meant is disjoint
  sets of *processes*. We assume `f(X₁ + X₂) = f(X₁) ⊕ f(X₂)` for all nonempty multisets (this is
  what is used); neither associativity nor commutativity of `⊕` is needed.
- **[model] Lemma 26** is proved (not assumed) for a Cole–Vishkin variant: colour reduction with
  multi-bit colour messages for `λ` rounds (message widths `w ↦ size(2w−1)`, total `≤ 5λ` bits),
  colours `< 8`, then 8 MIS rounds with the leader first (no 6→3 reduction), one round to learn
  the neighbours' membership and one aggregation round; virtual rings of 2 processes are covered.
  The cost is the same `O(λ)` per process as the paper's `λ + O(log λ) + …` CONGEST[1] rounds.
- **[under-spec] Aggregation step.** The paper does not say which MIS neighbour a leaf joins; a
  leaf joins its clockwise virtual neighbour if it is in the MIS, else its counter-clockwise one.
  Values are sent as `true :: enc w` so that empty encodings are unambiguous.
- **[model] Dissemination:** neither of the paper's two options; the leader broadcasts the bits of
  the result with two ComputeORs per bit (`3n(2L+1)` pulses, `O(nβ)` like SndCount/RcvCount).
- **[model]** The number of phases is proved `≤ ⌊log₂ n⌋` (an MIS of a cycle of `m ≥ 2` nodes
  has `≤ m/2` nodes); explicit bound for Theorem 1:
  `3n(λ + 2⌊log₂ n⌋ + 2β + 3) + ⌊log₂ n⌋·(78nλ + 15nβ + 180n)` pulses; Corollary 2 with IDs of at
  most `C(⌊log₂ n⌋+1)` bits: `(81C + 216)·n·(⌊log₂ n⌋+1)²` pulses.
- **[under-spec]** §9.2 runs the counting algorithm "on the virtual ring induced by the active
  set", which need not contain the leader, while Theorem 14 requires an active leader; the
  complexity paragraph (sum of indicator bits over the whole ring) avoids this. Theorem 6 is not
  formalized.

## Section 10 (lower bound)

- **[model] Theorem 3, "w.l.o.g. the arc is clockwise".** Not a real gap: Lemma 28 is
  direction-agnostic. The formalization avoids the mirror case anyway by choosing the sparse left
  edge among the `⌊n/2⌋` edges just clockwise after the leader and using clockwise intervals only.
  Constants: `n·⌊log₂ n⌋ ≤ 14·M + 4·n` (and `n·⌊log₂ n⌋ ≤ 28·M` for `n ≥ 2^10`).
- **[gap, minor] Lemma 28's proof.** "Replay `O` verbatim" cannot be literal: `O` contains events of
  `I₂ \ I₁` (absent from `R'`), and `I₁`'s own events must be rescheduled relative to the outside.
  Replaced by a rigorous crossing-sequence merge (`Podc.ContentOblivious.splice`).
- **[under-spec] Lemma 28, "same local history".** We prove equal final local states and pulse
  counters for all nodes of `R'` (also those of `I₁`). The hypothesis "leader ∉ I₂" is not needed
  for the lemma, only in Theorem 3.
- **[model] Theorem 3 is proved per execution:** every execution in which the leader has an
  output sends `Ω(n log n)` pulses (only safety of counting on all rings is assumed, no
  termination). The paper's form ("has an execution") follows when the leader outputs in every
  final configuration (`theorem3`).
- **[typo]** `I_t = (v, …, v+t)` has `t+1` processes; the formalization indexes by the number of
  processes.
