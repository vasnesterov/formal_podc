# Forget-IT — PODC 2026

Ittai Abraham, Sourav Das, Yuval Efron, Jovan Komatovic. *Forget-IT: Optimal Good-Case Latency
For Information-Theoretic BFT.* PODC 2026. DOI
[10.1145/3796701.3815965](https://doi.org/10.1145/3796701.3815965). Formalized version: the
proceedings version (11 pages). The full version [3] (Cryptology ePrint) was not available, so
the proofs were rebuilt from the proof sketch of §4.2.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The robust good-case latency claim (Theorem 3, first item, also in
the introduction and Table 1) is false under the paper's own definition. A run in which GST is
the moment a correct leader enters its view can still take 14 message delays to decide. Agreement
(Theorem 2) holds even in a fully asynchronous model with crash–recovery. The headline
good-case latency of 3δ holds, and so does non-triviality.

## Mistakes in the paper

* **Robust good-case latency 3δ (Theorem 3, first item) is false as defined.** §3 defines
  `T_rgc` over the executions in which "GST coincides with a correct leader entering its view".
  Nothing stops the other correct processes from having entered that view earlier, during the
  asynchronous period, and from having timed out there. After the timeout (line 65,
  `vc[V] = true`) they never send `vote-1` in that view (line 37). So the leader's proposal
  cannot gather a quorum, and the decision waits for the leader's own timeout and a further view.
  Concrete run: `n = 4`, `f = 1`, `Δ = 2` ticks, one message delay after GST = one tick.
  Process 0 leads view 1 and is Byzantine; process 1 leads view 2 and is correct. All messages
  to process 1 are delayed until GST = 21. Processes 2 and 3 finish view 1 with the help of
  Byzantine `SAFE` echoes and enter view 2 at tick 11. They time out there, so `vc[2] = true` by
  tick 19. At GST process 1 receives `f + 1` `echo-3` for view 1 and enters view 2 (line 80). It
  proposes, but nobody votes. The processes decide only in view 3, at tick GST + 14, where the
  claim promises GST + 3. The run is a valid run of CSLib's partially synchronous model: start at
  0, no drift, no crashes, reliable delivery by `max(τ, GST) + δ`. It is therefore an execution of
  the paper's model, and the facts are checked by evaluation
  (`RobustLatency.robust_latency_counterexample`, `others_timed_out`, `decides_later`).
  The run also misses the weaker bound 3Δ = 6 ticks. The claim stays false if `δ` is read as the
  maximum delay `δ(E)` over the whole execution (§3, Responsiveness). Then a crash–recovery of
  processes 2 and 3 before GST plays the role of the timeout: line 53 sets `vc[2]`, and every
  delay can be small (informal argument, `differencies.md`).
  The termination sketch has the gap that causes this: it says every correct process "enters view
  V (line 85)" on the leader's prepare, which ignores processes already in V. The intended notion
  is probably "the whole view lies after GST". We did not prove the claim for that version. Even
  then it needs `δ < Δ` or favourable tie-breaking: with `δ = Δ` the first entrant's 3Δ timer
  (line 45) can fire just when the `vote-1` quorum arrives, and then it never locks. As written,
  though, the claim is false. This is the
  paper's distinctive claim over TetraBFT, but the title and abstract only claim (non-robust)
  good-case latency, so we rate it ❌ rather than 🚨 (see `differencies.md`).
* **Agreement proof sketch: small slips, statement true.** The sketch says a decision implies that
  "at least `2f + 1` correct processes" broadcast the deciding `vote-2`. Only `f + 1` correct ones
  are guaranteed, and that is enough: any `2f + 1` senders meet them. It also treats the views
  after the decision as if all correct processes entered `V_dec + 1` together. In an asynchronous
  run, processes may lock or echo in `V_dec` *after* others have moved on. The induction must be
  stated as an invariant that holds as soon as the `f + 1` lockers are fixed, even before they
  lock (`Hyp`/`Concl` in `Safety.lean`). With these repairs the sketch's argument goes through
  unchanged: guards, the three `echo-1` triggers, the `SAFE` wildcard, and the second-echo
  mechanism.
* **Remark (not an error).** Non-triviality is required only when GST = 0, and that restriction
  matters. Because of the `SAFE` wildcard, `cert(echo-3, f+1, V, v)` holds for *every* value once
  `f + 1` `SAFE` echoes arrive. A leader resolving line 80's "for some v" adversarially may then
  propose a value nobody proposed, so weak validity without the GST clause is not guaranteed by
  the pseudocode. Our implementation tries `SAFE` first.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* *Safety* (`Spec.lean`, `Safety.lean`): Algorithms 1–3 are written as guarded actions, one per
  pseudocode rule (`Defs.lean`). These run in an asynchronous transition system with `n = 3f + 1`
  processes and a static set of at most `f` Byzantine processes; the paper notes that adaptive
  corruption is equivalent here. Channels are authenticated, there are no signatures, and
  Byzantine processes may send anything. Correct processes receive any message ever broadcast by
  a correct process, at any time. They may lose received and accepted messages (volatile state)
  and may run the recovery procedure at any time. Timers may fire at any time. This covers every
  execution of the paper's model: partial synchrony, lossy links before GST, crash–recovery,
  constant persistent memory.
* *Timing* (`Protocol.lean`): `forgetIT prm K` is the protocol as an `Algorithm` of CSLib's
  partially synchronous model (`Cslib.Byzantine.PartialSync`). Time is discrete and every correct
  process takes one step per tick. Delivery between correct processes is reliable, by
  `max(τ, GST) + δ`. Clocks are drift-free, processes start at 0, and there are no crashes. In a
  step, a process receives, then runs `K` passes over the rule candidates, executing every enabled
  one. Timers expire after 3Δ ticks (line 45) and 4Δ ticks (line 65). One message delay is
  `δ + 1` ticks, and `Δ ≥ δ + 1` is the paper's `δ ≤ Δ`. Every run of this algorithm is an
  execution of the asynchronous system (`run_reach`), so safety transfers.
* Persistent memory is kept as unbounded per-view arrays. Every rule reads only the three-view
  window or the guard of the view being entered, and views only grow, so this is equivalent to the
  paper's window.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 2, agreement (asynchronous system, crash–recovery) | `agreement` | `Safety.lean` |
| — key steps: quorum of `vote-2` meets the lockers; induction over views | `base`, `concl_step`, `concl_reach` | `Safety.lean` |
| Theorem 2, agreement in every run of the timed protocol | `run_agreement` | `Refinement.lean` |
| Timed protocol refines the asynchronous system | `run_reach` | `Refinement.lean` |
| Theorem 1 / 3, good-case latency `3δ` (GST = 0, first leader correct) | `good_case_latency`, `good_case_decides` | `Latency.lean` |
| Theorem 2, non-triviality | `non_triviality` | `Latency.lean` |
| Theorem 3, robust good-case latency `3δ`: **false** | `RobustLatency.robust_latency_counterexample` | `Counterexample.lean` |

**Not formalized.** Termination after GST in general (view synchronization), view length 7Δ,
message complexity `O(n²)`, the `O(1)` memory bound, optimistic responsiveness, the corrected
robust-latency claim.

**CSLib candidates.** `foldl_pres`/`foldl_progress` and `quorum_of_all` (`Latency.lean`).

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`; the counterexample is checked with `decide +kernel` through CSLib's memoised
simulator (`simHist`). Non-vacuity: the good-case theorem and the counterexample run show that
decisions do happen; the agreement hypotheses are only `n = 3f + 1` and `|F| ≤ f`.
