# Forget-IT — differences between the formalization and the paper

Paper: proceedings version, PODC 2026 (Algorithms 1–3, §3 definitions, §4.2 proof sketch). The
full version [3] was not available.

## Statement-level issues (with the deciding rule of `verdicts.md`)

1. **Theorem 3, robust good-case latency `3δ` — false (❌).** Definition (§3): `F_rgc` is the set
   of `f`-bounded adversaries "for which GST coincides with a correct leader entering its view";
   `T_rgc = sup DL`, with `DL = T − GST`. Counterexample `RobustLatency.robust_latency_counterexample`:
   `n = 4`, `f = 1`, leaders `leader(V) = V − 1 mod 4`, process 0 Byzantine (leader of view 1),
   process 1 correct (leader of view 2), `Δ = 2` ticks, GST = 21. Process 1 enters view 2 in the
   step at GST, but no correct process decides before GST + 14. The decision comes at GST + 14, in
   view 3. In paper time one message delay after GST is one tick (`δ = 1 ≤ Δ`). Cause: processes 2
   and 3 entered view 2 before GST and executed line 65 (`vc[2] ← true`), so line 37 forbids them
   to vote for the leader's proposal.
   * Every hypothesis of the paper's model holds in the run. All processes start at time 0 (by
     GST). Clocks do not drift. There are no crashes. Messages before GST are delayed (asynchrony)
     and none is lost. After GST every message is delivered in one tick. Process 0 sends only
     `echo-1/2/3(1, SAFE)` to processes 2 and 3. Process 1's entry is an active entry (line 80) and
     it broadcasts its `prepare`.
   * Why not ⚠️ (R3/R4): the fix changes the family of executions over which the metric is taken,
     i.e. the content of the claim. The paper also motivates robust latency precisely by "brief
     periods of asynchrony", which is the situation here. The proof sketch's "first view V after
     GST … each correct process enters view V (line 85)" suggests the intended reading "the whole
     view starts after GST". That version is not proved here, and it also needs `δ < Δ` (or
     tie-breaking in the protocol's favour): when `δ = Δ`, the 3Δ timer of the first process to
     enter the view (line 45) may fire exactly when the `vote-1` quorum arrives, and that process
     then never locks.
   * Why ❌ and not 🚨 (R5): the title and the abstract claim *good-case latency* 3 rounds. That is
     the non-robust notion, the one Theorem 1 states, and it is true (`good_case_latency`). The
     robust variant comes in the introduction as "in fact, our main result obtains an even
     stronger notion". It is the paper's distinguishing claim over TetraBFT (Table 1), so the call
     is borderline; we rate it as a non-headline numbered claim.
   * About `δ`: the responsiveness paragraph defines `δ(E)` as the maximum delay over *all*
     messages of the execution. Under that reading the pre-GST delays to process 1 (up to 21
     ticks) would make `3δ(E)` large. That reading contradicts the partial-synchrony paragraph
     ("`δ ≤ Δ` the actual message delay after GST", bounds relative to `max(τ, GST)`), which we
     follow. With clock drift before GST, which the paper allows, the same scenario can be made
     with small delays for every message (not formalized).
   * Reviewer note (informal, not formalized): the claim also fails under the `δ(E)` reading,
     through crash–recovery, which the paper allows before GST. Take the same setting. Processes 2
     and 3 enter view 2. They crash and recover at once, and line 53 sets `vc[2] = true`. Process 1
     enters view 2 one message delay later, and that time is GST. All message delays are at most
     some small `d`, so `δ(E) ≤ d`. Let process 0 be silent from then on. Line 37 again blocks
     every `vote-1` of 2 and 3 in view 2. The view change of view 2 needs a third `vote-2` for view
     2, and only process 1 can send it, at its 3Δ timer (line 45). So no correct process decides
     before GST + 3Δ, and `3Δ / δ(E)` is unbounded. Also, the formalized run decides at GST + 14
     ticks with `Δ = 2` ticks. That is more than `3Δ = 6`, so even the weaker bound `3Δ` fails.

## Proof-level issues (statements true)

2. **Agreement sketch.** The sketch says "at least `2f + 1` correct processes broadcast
   `⟨vote-2, V_dec, v_dec⟩`"; only `f + 1` correct ones are guaranteed. That suffices:
   `|S| + |L| = (2f + 1) + (f + 1) > n` (`base`). The sketch also argues as if all correct
   processes had entered view `V_dec + 1` before anything happens there. In asynchronous runs, the
   last locks in `V_dec` and the echoes of later views interleave arbitrarily. We prove an
   invariant parameterised by the eventual set of lockers. If at least `f + 1` correct processes
   send their `vote-2` for `V_dec` (if at all) with lock `v_dec`, then in every reachable state:
   guards of views `> V_dec` are `v_dec` or unset; echo slots of views `≥ V_dec` hold `v_dec` and
   no second (`SAFE`) echo is sent; `vote-1`s and `vote-2` guards of views `> V_dec` are `v_dec`
   (`Concl`, `concl_reach`). It also needs two facts the sketch leaves implicit: the guard of the
   current view is never `⊥`, so line 50 cannot fire spuriously, and correct `vote-2`s are unique
   per view.
3. **Non-triviality** is not argued in the sketch beyond one sentence. We derive it from
   good-case latency plus agreement (`non_triviality`).

## Modelling choices (abstract model, `Defs.lean`, `Spec.lean`)

4. Views are `ℕ`. Entering view 1 touches views `−1` and `0` (lines 32–33); both are the dummy
   view 0 here. Correct processes run the view change of this dummy view at start-up, which is
   harmless (checked by the latency proof).
5. Persistent memory: per-view unbounded arrays instead of a window of three views (line 18).
   This is equivalent: every rule reads only views in `{view−2, view−1, view}` or sets the guard
   of the view it enters, and views never decrease.
6. Timing conditions (lines 45, 65) and line 45's "non-passively entered" are dropped in the
   abstract model, so timers may fire at any time. The recovery procedure may run at any time. A
   crash is the loss of volatile state (`vol` step) followed by `recover`. All of these only add
   behaviours.
7. The network: a correct process may receive any message ever broadcast by a correct process, at
   any time and repeatedly, and any message from a Byzantine process. Abandoned broadcasts
   (line 19) and lossy links only remove behaviours. Received and accepted messages may be
   forgotten at any time.
8. "Upon … wait until …" (lines 35–36) is a single guarded rule; line 40's inner
   `if vote2 = ⊥` is part of the guard. A rule may fire again while enabled (the functions
   `send_echo_*` and the `= ⊥` tests make repetitions harmless).
9. Lines 58, 61, 63 ("existence of a set `S` of `2f + 1` accepted messages such that …") are
   stated with the largest admissible set (`lockSet`, `notPotSet`), which is equivalent. Line 58
   is split into two rule instances, `alertSet V (some ℓ)` and `alertSet V none`.
10. `divergent_guards` (line 123) is stated as "for every guard `G`, `num − #G ≥ f + 1`". This is
    equivalent to the test with the most frequent guard and independent of tie-breaking.
11. `⟨vote-2, V, lock, guard⟩` carries `Option (Value ∪ {SAFE})` as guard. The guard of a correct
    process is never `⊥` (invariant `guardV`).
12. `potential_decision` has type `Value` (the pseudocode declares `Value ∪ {SAFE}` but only ever
    assigns a lock value).
13. Decisions: every execution of line 44 is recorded as a decision event, even a repeated one.
    Agreement is proved for all events. The paper's `decided` flag is not persistent memory.
14. Static Byzantine set (the paper: adaptive, equivalent for deterministic protocols, footnote 2).

## Modelling choices (timed model, `Protocol.lean`)

15. CSLib's partially synchronous model: correct processes start at time 0, take a step every
    tick, and have drift-free clocks; there are no crashes, and delivery between correct
    processes is reliable by `max(τ, GST) + δ`. This is a subset of the paper's executions, so the
    counterexample (item 1) is valid in the paper's model. For good-case latency, `GST = 0` makes
    the paper's model coincide with this one, except for the discrete time and the step semantics
    below.
16. Local computation takes one tick. In a step a process processes the messages delivered now
    and runs `K ≥ 1` passes over candidate rule instances. The messages it broadcasts are sent at
    the next tick. Hence one message delay is `δ + 1` ticks, and the latency bound is
    `3(δ + 1)`. The proofs work for every `K ≥ 1`; rules still enabled after `K` passes fire in
    the next tick. The counterexample uses `K = 1` (with `K = 4` the run has the same timing but its kernel check needs too much memory). That view 2 decides nothing does not depend on
    `K`: after their timeouts processes 2 and 3 never vote in view 2 (line 37), so no correct
    process can lock there (line 39). The exact decision time GST + 14 does depend on the step
    semantics.
17. "for some `v` …" (lines 50, 73–88): candidates are the values occurring in received messages
    plus `SAFE`, tried in that order (`SAFE` first). A broadcast reaches every process, including
    the sender.
18. Timers: line 45 fires once `clk − entered ≥ 3Δ` and the view was entered actively; line 65
    once `clk − entered ≥ 4Δ`. `entered` is reset on every view entry.
19. The leader broadcasts `prepare` only if `value_to_propose[V] ≠ ⊥` (never `⊥` when a leader
    actively enters, by lines 27, 82–83).

## Not formalized

20. Termination in general (view synchronization after GST, line 88 passive entry, constant
    memory), view length 7Δ, `O(n²)` messages per view, `O(1)` persistent memory, optimistic
    responsiveness, the external-validity and atomic-broadcast extensions.
