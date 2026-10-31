# On Using Null Messages in a Byzantine Setting — PODC 2020

Guy Goren, Yoram Moses. *Brief Announcement: On Using Null Messages in a Byzantine Setting.*
PODC 2020. DOI [10.1145/3382734.3405717](https://doi.org/10.1145/3382734.3405717). Formalized
version: the 3-page proceedings brief announcement; numbering follows it. A journal full version
exists (Goren, Moses, *Optimistically tuning synchronous Byzantine consensus: another win for null
messages*, Distributed Computing 34(5), 2021, DOI 10.1007/s00446-021-00393-8); it is not open
access and was not consulted.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** Theorem 1.2 (silent validation rounds give knowledge of a global
milestone) and Theorem 2.1 (SmallCouncil + any binary BA protocol is binary BA; failure-free runs
decide the majority value at time 3 with at most `n(t+1.5)` bits; at most `n(t+1.5) + 2n²` bits by
correct processes and 4 rounds before the base protocol in general) hold. The brief announcement
gives no proofs (Theorem 1.2 is justified "by design", Theorem 2.1 not at all), so the verdict
judges the statements only; we reconstructed the proofs. They need `2t < n` and the paper's
convention that a process receives its own broadcasts ("send to all" includes the sender).

## Mistakes in the paper

There are no false statements. One implicit convention matters and is easy to get wrong:

* **Self-delivery is essential and never stated.** Figure 1 (line 10) has a process without a
  unanimous recommendation "send `err` to all", and line 11 has a process that "did not receive any
  `err`" decide at time 3. If the sender does not count its own `err`, the protocol is wrong for
  every base protocol. Take `n = 7`, `t = 2`, Council `{0,1,2}`. Process `1` is Byzantine and
  silent, process `6` has input 0 and everyone else input 1. The correct council members recommend
  `MAJ = 1`. The null message of `1` tells `6` "recommendation 0", so `6` sees no unanimous
  recommendation, sets `est = 0` and sends `err`. Nobody else sends `err`, so `6` decides 0 at time
  3. The others got `6`'s `err` and run the base protocol with input 1. Declaring `6` Byzantine as
  well gives the same run with 2 faults, so the base protocol's validity makes them decide 1.
  Theorem 1.2 has the same issue: if `j` does not receive its own messages, silence in round `m+1`
  says nothing about `φ_j`. With the paper's wording ("sends messages to everyone", "send to all"),
  which includes the sender, both results hold. This is the paper's convention, not an extra
  assumption: Figure 1 quantifies over all of `P` including the sender (lines 01–03 for a council
  member `i`, lines 06–07 for `i = j`), and line 08 ("unanimous recommendation from `{0,…,t}`")
  only makes sense for a council member if it receives its own recommendation. We prove the
  results under this convention, or with "`φ_j` held" as an explicit hypothesis in Theorem 1.2. (`not_solves_without_selfDelivery`,
  `theorem_1_2_literal_false`; correct versions `theorem_2_1_consensus`, `theorem_1_2`)
* **Minor imprecisions.** Theorem 2.1 only needs `2t < n` for the layer itself (`k ≥ 3` matters only
  for the base protocol). "Majority value" (2.1 (3)) is ambiguous for ties when `n` is even; any
  fixed tie-break works (ours: 0). The bit bound in (2) counts the four layer rounds only, not the
  base protocol's messages.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's synchronous lock-step Byzantine model (`Cslib.Byzantine.LockStep`) on the complete network
  of `n` processes `Fin n`. Protocols are deterministic functions of input and history; messages are
  `Option`s, so `none` is a null message. A static Byzantine set of at most `t` processes
  (`atMost t`) sends arbitrary messages; links are reliable; no signatures.
* Round `r` of the model (0-indexed) is the paper's round `r+1`. The history after `r` rounds is the
  local state at time `r`.
* SmallCouncil composed with `B` (`smallCouncil t B`): messages `Bool ⊕ M₂`, one-bit layer messages
  or base-protocol messages. Processes that got a `help!` run `B` from round 4 with input `est`;
  the others are silent from then on. A process that sends `err`/`help!` counts it as received
  (flag `selfRcv := true`; `false` is the broken literal reading). `B` is an arbitrary protocol
  with `Solves ⊤ B (atMost t) BA` (termination, validity, agreement).
* Theorem 1.2 uses CSLib's interpreted systems (`Cslib.Knowledge.System`). The points are runs
  (admissible reliable scenarios) × time, `j`'s local state is (input, history), and `K` is S5
  knowledge.
* Bits: every layer message is one `Bool`, so layer bits = layer messages (`msgsAt`, messages by
  correct processes to other processes).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 1.1 (svr) | `ImplementsSVR` | `Silent.lean` |
| Theorem 1.2 | `theorem_1_2` (+ `knows_others_of_noMsgs`) | `Silent.lean` |
| Theorem 1.2 without self-delivery / `φ_j`: fails | `theorem_1_2_literal_false` | `Silent.lean` |
| Rounds 3 and 4 of SmallCouncil are svr's (§2) | `smallCouncil_svr_round3`, `smallCouncil_svr_round4` | `Silent.lean` |
| Theorem 2.1, consensus (`k ≥ 3`, `n > kt`) | `theorem_2_1_consensus` (general: `smallCouncil_solves_BA`, `2t < n`) | `Consensus.lean` |
| Theorem 2.1 (1), failure-free: decide at time 3 | `ff_status_three` | `Complexity.lean` |
| Theorem 2.1 (1), failure-free: ≤ `n(t+1.5)` bits in the whole run | `ff_bits_le`, `ff_msgsAt_eq_zero` | `Complexity.lean` |
| Theorem 2.1 (2): ≤ `n(t+1.5)+2n²` bits by correct processes in the layer; base starts at time 4 | `layer_bits_le`, `status_base`, `decides_iff_base` | `Complexity.lean`, `Compose.lean` |
| Theorem 2.1 (3): failure-free runs decide `MAJ(inputs)` | `ff_decides_maj` | `Complexity.lean` |
| Self-delivery is necessary for Figure 1 | `not_solves_without_selfDelivery` | `SelfDelivery.lean` |

**Not formalized.** Comparisons with the literature (24-fold improvement over Phase King,
the `nt/4` lower bound), the "fewer than `3n²` bits" remark, and the plurality/multi-valued remark.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: for `t = 0` the leader protocol `leaderBA` satisfies the base-protocol
hypothesis (`leaderBA_solves`, `Examples.lean`). For `t ≥ 1` the hypothesis is met by any classical
unauthenticated BA protocol for `n > 3t` (EIG, Phase King), but no such protocol is formalized in
CSLib or here, so for `t ≥ 1` the correctness part rests on that classical fact. This matches the
paper, whose Theorem 2.1 is itself a transformation of an arbitrary given base protocol. The failure-free, communication and
svr results hold for every `B`. The model and the knowledge semantics come from CSLib
(`Cslib/Computability/Distributed/Byzantine/LockStep/`, `Cslib/Computability/Distributed/Knowledge/Basic.lean`).

**CSLib candidates.** The bridge from `LockStep` runs to interpreted systems with Definition 1.1 and
Theorem 1.2 (`Runs`, `systemOf`, `ImplementsSVR`, `theorem_1_2` in `Silent.lean`), and `msgsAt`
(messages of correct processes per round, `Complexity.lean`).
