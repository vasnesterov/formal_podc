# Differences between the formalization and the paper

Paper: Z. Bouzid, A. Mostéfaoui, M. Raynal, *Minimal Synchrony for Byzantine Consensus*, PODC 2015
(HAL hal-01178651v1). The full version [6] (IRISA tech report no. 2025) was not available. The proofs of Lemmas 1
and 2 are therefore reconstructed.

## Errors in the paper

1. **Lemma 2 (EA-Termination) and Theorem 3 are false.** A correct process that returns at line 4 of Figure 3 never
   sets `timer[r]` (line 5). So it broadcasts `EA_RELAY[r]` only on receipt of `EA_COORD[r]` from `coord(r)`
   (lines 15–19). If the coordinator is faulty and silent, the processes that did not return at line 4 may wait
   forever at line 6. Lean: `lemma2_false` (`Counterexample.lean`). The run (`Blocking.R`):
   * Size: `n = 7`, `t = 2`; process `0` (the paper's `p₁ = coord(1)`) is faulty and sends nothing.
   * Proposals: processes `1–3` propose `true` and `4–6` propose `false`, so `m = 2 = ⌊(7−3)/2⌋`.
   * Timing: `gst = 0`, every delay is 0 or 1 tick. The run is synchronous, hence a `⟨t+1⟩bisource` run.
   * Delays chosen so that:
     * `CB[0]` returns each process its own proposal.
     * `CB[1]` returns `true` to `1–5` and `false` to `6`.
     * Processes `1, 2` receive `EA_PROP2[1]` from `1–5` first and return `true` at line 4.
     * Processes `3–6` receive the messages of `1, 2, 3, 4, 6` first and set their timers.
   * Only `3–6` ever relay (`⊥`): 4 < `n − t` relays.
   * From time 6 the run is quiescent.
2. **Theorem 4 (termination) is false**, for the same reason. Lean: `theorem4_termination_false`. In the same run,
   processes `3–6` stay at line 6 of round 1. Processes `1, 2` proceed to `AC_OBJECT[1]` and stay in its CB, which
   has 2 `AC_PROP` messages, fewer than `t + 1 = 3`. No correct process ever decides. The paper's proof applies
   EA-Termination in round 1 to conclude that "they all terminate the first round".
   * Repair (not in the paper): set the timer also when returning at line 4 (`Params.fixTimer`). The same run then
     decides (`repaired_blocking_run_decides`). Correctness of the repaired algorithm is not established (item 3).
3. **Proof of Lemma 3: line-4 returns are ignored.** "Every correct process `p_i` can either return `w` or `val_i`
   after executing the lines 7–10" overlooks processes that return at line 4 with another value. Lean:
   `lemma3_proof_fails`. The run (`GoodRound.R`):
   * Size: `n = 4`, `t = 1`, process `3` Byzantine. The EA object runs alone, in round 15.
   * Round 15 has `coord(15) = 2` correct, `F(15) = {0,1,2} = C` and `15 > 2δ` with `δ = 1`. The run is
     synchronous, so `2` is a bisource with `X⁻ = X⁺ = C`.
   * The Byzantine process RB-broadcasts `EA_PROP1(false)` consistently (`RBAdmissible`) and sends
     `EA_PROP2[15](true)`.
   * Process `0` returns `true` (line 4). Processes `1, 2` return the coordinator's `false` (line 8).
   * This refutes the proof step, not Lemma 3 itself, which quantifies over infinitely many rounds. Whether Lemma 3
     (EA-Eventual agreement) holds for Figure 3, with or without the repair, is open.
4. **Proof of Lemma 3: `p_k ∈ X⁻_ℓ ⊆ F(r)` is not justified.** The round is chosen with `X⁺_ℓ ⊆ F(r) ⊆ C` only.
   * Fix: choose `X⁻_ℓ ∪ X⁺_ℓ ⊆ F(r) ⊆ C`. This is possible since `|X⁻ ∪ X⁺| ≤ 2t + 1 ≤ n − t` when both sets have
     exactly `t + 1` elements and contain `ℓ`.
   * Not formalized: Claim C is not formalized at all.
5. Claim C says the timer is set "at line 8"; it is line 5. (Typo.)

## Modelling choices and imprecisions

### Abstract layer (`Basic`, `CB`, `AC`, `EA`, `Consensus`)

* **RB is a primitive.** It is given by its four properties on delivery traces `D i τ j : Option V`, one RB
  instance per sender (`RBSpec`). RB-Unicity is built in: a delivered message stays delivered. RB is not implemented.
  The paper also treats it as given ("can be implemented").
* **Partial participation.** Inputs are `Option V`, where `none` means the correct process never invokes the object.
  * AC-Obligation and EA-Validity are stated for "all correct processes *that invoke* propose `v`". This is stronger
    than the paper's wording ("all correct processes propose `v`").
  * Theorem 4's agreement proof needs this form, since some correct processes may never reach round `r + 1`.
  * Figures 2 and 3 satisfy it.
* **Monotone `cb_valid`.** `CBSpec` contains `mono` (`cb_valid_i` only grows). The paper says values "can still be
  added" but does not list it among the CB properties. The AC proof uses it, and Figure 1 satisfies it.
* **CB-Set Agreement** is "eventually equal" as in the paper: `∃ T, ∀ τ ≥ T, valid i τ = valid k τ`.
* **Feasibility.**
  * The CB/AC termination properties assume `Feasible`: some value is input by `t + 1` correct processes.
  * `feasible_of_mValued` derives `Feasible` from "at most `m` values" and `n − t > m t`. This is the paper's
    condition and avoids the division by `t` in `⌊(n−(t+1))/t⌋`.
* **Figure 1.**
  * `CB_broadcast()` returns at the first time `cb_valid_i ≠ ∅`.
  * The returned value is chosen adversarially (`sel`).
* **Figure 2.**
  * The process's choices of the `n − t` messages and of the most frequent value are adversarial data constrained by
    the rules (`Fig2.Follows`).
  * "Most frequent" means a value carried by at least one of the `n − t` messages, with maximal count.
  * `live` says that line 3 completes once its predicate holds (after line 1).
* **Figure 3** is abstracted to lines 1–4 (`Fig3`), which is all EA-Validity depends on. Channels for `EA_PROP2` are
  plain authenticated channels: a message from a correct process carries its `aux`.
* **Figure 4 (`Fig4`)** is an execution at the level of objects: estimates per round, EA and AC outputs per round,
  the time of the line-5 test, and the `DECIDE` RB instances.
  * Safety (`validity`, `agreement`) uses only the object specifications: CB-Set Validity of `CB[0]`, `ACSpec` for
    every round, EA-Validity for every round and RB-Validity of `DECIDE`. This matches the paper's proof.
  * `Fig4.termination` assumes, in `Fig4.Live`:
    * EA-Termination and EA-Eventual agreement (rounds ≥ 1);
    * undecided correct processes continue to the next round;
    * the line-5 test of round `r` happens at time `≥ r` ("rounds take time"; needed for "`CB[0]` is never updated
      after round `r₀`" — not stated in the paper);
    * line 9 fires once its predicate holds.

  EA-Eventual agreement is phrased as "if all correct processes start every round, then infinitely often all
  correct processes return the same value, which some correct process ea-proposed".
* "Decides and stops" (line 9): in `Fig4` a decided process may stop starting rounds. The RB layer is a primitive and
  keeps working.
* The abstract layer has no bridge to the operational machine. The two layers implement the same rules but are
  separate formalizations.

### Operational layer (`Machine`, `Counterexample`)

* **Model.** CSLib's partially synchronous model `Cslib.Byzantine.PartialSync`:
  * discrete ticks, every correct process steps every tick, authenticated links, batches with adversarial delivery
    times;
  * faulty processes send arbitrary messages;
  * processing time is 0, and a step runs at most `fuel = 8` main-thread transitions;
  * timers count ticks: `timer[r]` set to `r` expires `r` ticks later.
* **Asynchrony + bisource.** The paper's model is `Run.AsyncValid t` (reliable links, unbounded finite delays) plus
  an eventual `⟨t+1⟩bisource` (`Run.BisourceValid`). A process counts in its own sets `X⁻`/`X⁺`, and its channel to
  itself must be timely too.
  * Both counterexample runs are synchronous (`gst = 0`, delays ≤ 1), which implies every bisource condition
    (`Run.SyncValid.bisourceValid`).
  * Unbounded asynchrony therefore plays no role in the refutations.
* **RB idealized.**
  * An RB-broadcast by a correct process is an `rb k v` message sent to all.
  * A process RB-delivers the first `rb k _` of each sender.
  * Faulty processes must send RB messages consistently (`RBAdmissible`: one value per instance, sent to every
    correct process at the same time, not lost).
  * The blocking run has no faulty messages at all (`Run.Canonical`), so it is valid for any RB semantics.
  * A real RB implementation (Bracha) adds message rounds. Since its deliveries can be ordered by the adversary in the
    same way, we expect the same schedules to exist; this is not formalized.
* **Resolution of "any" choices.**
  * CB returns the value of `cb_valid` whose first `rb` message arrived first.
  * A wait statement takes the first `n − t` qualifying messages in arrival order (same tick: sender order).
  * MFA is the first value with maximal count.
  * Line 7 takes the first non-`⊥` relay from `F(r)` in arrival order. All relays received count, not only `n − t`
    of them.
  * The coordinator champions the first `EA_PROP2[r]` received from `F(r)`.
  * Coordinator messages are processed before expired timers in the same tick.
  * In both counterexample runs every such choice is forced (`facts` evaluate the runs; there is one candidate at
    every return), so the refutations do not depend on these resolutions.
* **Schedule.** `coord(r) = (r − 1) mod n` (0-based) and `F(r) = F_{index(r)}`. The `(n−t)`-subsets `F_1 … F_α` are
  enumerated in `List.sublistsLen` order, since the paper does not fix an order. The blocking run never uses `F`.
  The good-round run uses the round `r = 15` where `F(15)` is the correct set.
* `Params.eaRound = some r` runs the EA object alone (Figure 3 in round `r`), as used for Lemma 3.
* `Params.fixTimer` is our repair, not part of the paper. It is off by default.
