# Differences between the formalization and the paper

Paper: G. Goren, Y. Moses, *Brief Announcement: On Using Null Messages in a Byzantine Setting*,
PODC 2020 (3 pages, proceedings version; no proofs are given). A journal full version exists
(*Optimistically tuning synchronous Byzantine consensus: another win for null messages*,
Distributed Computing 34(5), 2021); it is not open access and was not consulted.

## Statement-level issues

1. **Self-delivery convention (Figure 1 lines 10–13; Definition 1.1 / Theorem 1.2).** The protocol
   is correct only if a process that sends `err` (resp. `help!`) "to all" also counts it as
   received. Under the reading "processes do not receive their own messages", agreement fails for
   every base protocol solving BA (`not_solves_without_selfDelivery`, `n = 7`, `t = 2`, Byzantine
   council member `1` silent, process `6` with the minority input decides 0 at time 3 while the
   others decide 1 through the base protocol). Theorem 1.2 likewise needs `φ_j` for the receiver `j`
   itself (`theorem_1_2_literal_false`: two processes, `φ_0` false, `φ_1` true, process `0` receives
   nothing).
   Not counted as an error: the paper's own wording ("sends messages to
   everyone", "send to all", "broadcasts an err message to alert all") includes the sender, and the
   counterexamples need our model's convention that simple graphs have no self-loops. Nothing in the
   paper suggests reading "all" as "all others". We formalize the paper's protocol with `selfRcv = true` and state
   Theorem 1.2 with the hypothesis "`φ_j` held at time `m`", which is local to `j` and holds
   automatically when `j` receives its own broadcast. Evidence that self-delivery is the paper's
   convention: Figure 1 quantifies over all of `P` / all of the Council including the process
   itself (lines 01, 06–07), and line 08 needs a council member to "receive" its own
   recommendation.
   *Slight weakening.* Under self-delivery the printed Theorem 1.2 also covers a *faulty* `j` with
   `¬φ_j` that receives nothing (then `j` can infer that it is faulty, so `φ̄_c` concerns only the
   others). `theorem_1_2` excludes that case through the hypothesis `φ_j`; `knows_others_of_noMsgs`
   covers the other correct processes without it. This is a limit of our statement, not of the paper.
1b. **Bit bound of Theorem 2.1 (2).** Printed: "When failures occur, at most `n(t+1.5)+2n²` bits
   are sent by correct processes, and 4 rounds elapse before reverting to the base protocol."
   Taken literally for the whole run this is false for any base protocol that sends many bits; the
   evident reading (the cost of the layer, before reverting; cf. §2 "SmallCouncil adds only 4
   rounds and sends fewer than `3n²` bits") is what we prove (`layer_bits_le`, rounds 1–4, every
   run). Wording, not an error (evident intent). The
   constants of (1) and (2) were checked against the rendered page: `n(t + 1.5)` and
   `n(t + 1.5) + 2n²`, decisions "after 3 rounds" (time 3).

## Modelling choices

2. **Model.** CSLib lock-step synchronous Byzantine model on the complete graph `⊤` over `Fin n`,
   static Byzantine set with `≤ t` members, reliable links, adversary chooses all Byzantine
   messages as an arbitrary function of round, sender and receiver (this covers adaptive and
   rushing behaviour for deterministic protocols). The paper fixes the classic synchronous Byzantine
   model without signatures; the two agree.
3. **Self-messages** are not delivered by the model. The protocol simulates the paper's convention
   locally: a council member uses its own input for its own vote (line 04) and its own `rec` for
   itself (line 08). A process that sent `err` counts as having received one (`GotErr`), and a
   process that got an `err` (and so sends `help!`) counts as having received a `help!`
   (`Participates`).
4. **Base protocol interface.** `B : Protocol (Fin n) Bool M₂ Bool` with
   `Solves ⊤ B (atMost t) BA` (every run started at round 0 by all processes). In the composition,
   `B` is started at round 4 by the processes that got a `help!`, with input `est`. The others
   halt (send nothing). We show that if some correct process sent `help!`, the correct processes'
   `M₂` histories from round 4 on are exactly a run of `B` (`histR_hist_base`), so `B`'s guarantee
   applies. If no correct process sent `help!`, all correct processes decided at time 3, and `B`'s
   possibly degenerate run (some correct processes halted) is irrelevant. This matches lines 13–15.
5. **Decision.** The composed protocol's decision is its *first* decision (CSLib `Decides`). A process
   that decided at time 3 still participates in `B` if it gets a `help!`, but its decision stays
   the time-3 one (line 15).
6. **Messages and bits.** Layer messages are `Bool` (one bit). Round 0: `p` sends its input to council
   member `j` iff `j mod 2 ≠ v_p` (any message is interpreted as `(j+1) mod 2`, its content is
   unused). Round 1: `j` sends `rec_j` to `i` iff `values_j[i] ≠ rec_j`. A process interprets an
   explicit round-1 message as its content, and silence as "`rec` = the value I reported", i.e. its
   own input. `err` and `help!` are one-bit messages whose content is ignored. Bits are counted as
   messages from correct processes to *other* processes (`msgsAt`). The per-process bounds we use also
   hold when self-messages are counted.
7. **`MAJ`** is strict majority of `true` with ties resolved to `false`. The paper does not fix a
   tie-break; "decides on the majority value" (2.1 (3)) is read as "decides `MAJ(inputs)`".
8. **Council** is `{j : Fin n | j ≤ t}`, i.e. `{0, …, t}` (all processes if `t ≥ n`, which the
   hypotheses exclude).

## Hypotheses

9. **Resilience.** Theorem 2.1 assumes `k ≥ 3`, `n > kt` (the base protocol's resilience). The layer
   needs only `2t < n` (`theorem_2_1_consensus` takes `k : ℕ`; a real `k ≥ 3` is covered by
   `smallCouncil_solves_BA`, since `n > kt` implies `2t < n`): `MAJ` at a correct council member equals the common correct input, and the
   Council has a correct member. `smallCouncil_solves_BA` is stated with `2t < n`;
   `theorem_2_1_consensus` is the paper's form.
10. **Non-vacuity.** The base-protocol hypothesis is discharged in Lean only for `t = 0`
    (`leaderBA_solves`); for `t ≥ 1` it is satisfied by classical protocols (EIG, Phase King) not
    formalized here. `not_solves_without_selfDelivery` assumes a BA protocol for `n = 7`, `t = 2`;
    such protocols exist classically.

## Statements: exact form

11. **Theorem 1.2** (`theorem_1_2`): for every run `r`, every `j` with no message received in round
    `m+1` and `φ_j` true at time `m`: `K_j (⋀_{correct i} φ_i at time m)` at `(r, m+1)`, in the
    interpreted system of all admissible reliable runs. Knowledge quantifies over runs where `j`
    itself may be faulty. `knows_others_of_noMsgs` drops the `φ_j` hypothesis and gives knowledge of
    `φ_i` for correct `i ≠ j`.
12. **Theorem 2.1 (1)**: `ff_status_three` (every process's status is `none` before time 3 and
    `MAJ(inputs)` at time 3), `ff_bits_le` (for every horizon `R`, `2·#bits ≤ n(2t+3)`, i.e.
    `≤ n(t+1.5)`), `ff_msgsAt_eq_zero` (nothing is sent from the paper's round 3 on, so the base
    protocol never sends a message).
13. **Theorem 2.1 (2)**: `layer_bits_le`: `2·(bits of correct processes in rounds 1–4) ≤
    n(2t+3) + 4n²`, for every run. The bound is per run and needs no hypothesis on `t`. "4 rounds
    elapse before reverting to the base protocol": `status_base`/`decides_iff_base` (the base run
    starts at round 4). Base-protocol messages are not counted, as in the paper.
14. **Theorem 2.1 (3)**: `ff_decides_maj`.
15. **Not formalized**: the comparison with Early-Stopping Phase King (8n² bits, 8 rounds), the
    "24-fold improvement" and "factor 4 above the `nt/4` lower bound" remarks, "fewer than `3n²`
    bits" (follows from (2) when `t + 1.5 < n`), the multi-valued/plurality remark, and the radio
    network / atomic commitment discussion.

## Proofs

16. The paper gives no proof of Theorem 2.1 and only "by design" for Theorem 1.2. Our reconstruction:
    a correct process attributes to a correct council member exactly its recommendation, null
    messages included (`recFrom_honest`). So unanimous recommendations of correct processes agree
    (`unanimous_agree`). Round 3 (`err`) and round 4 (`help!`) are silent validation rounds
    (`gotErr_of_err`, `participates_of_gotErr`). Case split: no correct process got an `err` (all
    decide the common estimate at time 3), or some did (all correct processes run `B`; if some
    correct process decided at time 3, all correct estimates are equal and `B`'s validity forces
    the same value).
