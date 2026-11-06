# Simultaneous Tasks: From Worst-Case to All-Case Optimal — PODC 2011

Maurice P. Herlihy, Yoram Moses, Mark R. Tuttle. *Transforming worst-case optimal solutions for
simultaneous tasks into all-case optimal solutions.* PODC 2011. DOI
[10.1145/1993806.1993849](https://doi.org/10.1145/1993806.1993849). Formalized version: the ACM
proceedings version (8 pages; there is no arXiv version). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Weakened.** The transformation and its optimality are proved for `t ≤ n − 2`: Lemma 1,
Theorems 2 and 3, Lemma 4, and Theorems 6 and 8 hold, taking the cited connectivity results (Lemmas 5
and 7) and the listed properties of ConCon as hypotheses. The paper explicitly allows `t = n − 1`, and
there Lemma 5 is false and Theorem 6 contradicts the timing claimed by Theorems 2/3. Corollary 9, the
set-agreement application, is false without the hypothesis `n ≥ t + k + 1` of the bound it cites.

## Mistakes in the paper

### ⚠️ Lemma 5 (and Lemma 7), and Theorem 6 against the timing of Theorems 2/3, for `t = n − 1`
The `t + 1 − W` analysis needs `t ≤ n − 2`, but the paper allows `t = n − 1`, where Lemma 5 is false
(`lemma5_false`, `not_lemma5Hyp`), Lemma 7 fails in the same way, and for `n = 3`, `t = 2` Theorem 6 and
the timing of Theorems 2/3 cannot both hold (`thm3_thm6_incompatible`, `theorem6_fails`,
`theorem6_counterexample`).

**Impact.** The paper explicitly assumes `t ≤ n − 1` (§2.1, and again in §4), so this is not a degenerate
corner, and Lemma 5 is needed for Theorem 6. The cited sources presumably assume `n ≥ t + 2`. For
`t = n − 1` either Theorem 6 or Theorem 2's timing is false, depending on the actual ConCon; for
`t ≤ n − 2` the constructions and the optimality argument are correct.

**Details.**
- **Lemma 5.** Take `n ≥ 2`, `t = n − 1`, any complete input set, and a protocol in which everybody
  sends a message in round 1. Let `r⋆` be the run in which all processes but `p₀` crash silently in
  round 1. Then `W(r⋆) = t − 1`, so round 1 is premature in `r⋆`, as it is in the failure-free run
  (`W = 0`). At time 1 only `p₀` is alive in `r⋆`, and it received nothing. Every run that `p₀` cannot
  tell apart from `r⋆` at time 1 is of the same kind, so the failure-free run is not connected to `r⋆`.
- **Theorem 6.** Take `n = 3`, `t = 2` and binary consensus. All hypotheses of Theorem 6 hold with
  `k̂ = 2` and `A` = FloodSet: complete inputs, `2` is a worst-case lower bound, and FloodSet decides at
  time 2. In `r⋆` (two processes crash silently in round 1) `W = 1`, so Theorem 3 has `Opt(A, 2)` decide
  at `min{2, 3 − 1} = 2`. But a simultaneous consensus protocol can decide at time 1 in `r⋆`: the
  survivor sees an empty round-1 inbox, knows it is alone and decides its own input; in all other runs
  the protocol runs FloodSet. So no protocol has both the timing of Theorem 3 and the all-case
  optimality of Theorem 6. For every continuous-consensus protocol with the properties listed in §2.3
  (accuracy, consistency, (i), (ii)), `Opt(A, 2)` is not all-case optimal, and such a protocol exists
  for `n = 3`, `t = 2`.

**Repair.** `theorem6` proves the transformation and its optimality with Lemma 5 as the cited hypothesis
`Lemma5Hyp`, which excludes `t = n − 1`. `theorem6_instance` discharges every hypothesis for `t = 1`,
`n ≥ 3`.

### ⚠️ Corollary 9 (the `⌊t/k⌋ + 1` bound)
The [CHLT00] bound `⌊t/k⌋ + 1` is quoted without its hypothesis `n ≥ t + k + 1`, and for `k = 1`, `n = 3`,
`t = 2` it is not a lower bound, so `Opt(sa, ⌊t/k⌋ + 1) = Opt(sa, 3)` cannot be all-case optimal and halt
at time 3 in failure-free runs (`corollary9_false`, `not_lb_three`).

**Impact.** A false application, independent of ConCon.

**Details.** The corollary claims halting at `min{3, 3 − W}`, which is time 3 in failure-free runs, but
FloodSet decides at time 2 in every run. So no protocol has both properties.

**Repair.** Under `n ≥ t + k + 1` the corollary is `theorem6` applied to the cited bound (`WorstCaseLB` is
a hypothesis of `theorem6`). There is no separate Lean statement of the repaired corollary.

## Proof gaps (statements true)

### 🔧 Lemma 1, Theorem 3 and Lemma 4 (processes that crash later)
The three proofs assume without argument that in a simultaneous protocol, if some process decides at
time `k`, then every process *alive* at time `k` decides at time `k`, including processes that crash
later.

**Impact.** The fact is proved by truncating the failure pattern (`SolvesSim.decides_of_alive`,
`SolvesWithin.decides_of_alive`).

**Details.** Lemma 4's proof says "p has not failed", but `p` only survives round `k`. Theorem 3's proof
says the protocol "would also have caused q to decide". In Lemma 1, a faulty process of `A` could a priori
decide after `k̂` and break simultaneity.

**Repair.** Truncate the failure pattern after round `k`. The process becomes correct, its first `k`
rounds do not change, and completeness and simultaneity apply. (`SolvesSim.decides_of_alive`,
`SolvesWithin.decides_of_alive`)

### 🔧 Theorem 2 (correctness of `ConCon(A)`)
All processes simulate the same run of `A`, which makes their outputs consistent only with the
*simulated* input vector, and that differs from the real one outside the core.

**Impact.** Repaired by an indistinguishability argument (`theorem2`, `decides_simRun`).

**Details.** The paper does not even say which inputs the processes outside the core get; they must be
chosen so that the input vector is allowed.

**Repair.** For the core processes, the simulated run looks the same as the run of `A` with the real
inputs and the same silent crashes. `A`'s correctness in that run gives an output vector for the real
inputs. (`theorem2`, `decides_simRun`)

Full list of differences (including modelling choices and minor imprecisions):
[differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous message passing on a complete network with crash failures. At most `t` processes
  crash. A crashing process reaches an arbitrary subset in its crash round. This is CSLib's
  `Cslib.SyncCrash` model: a run is an input vector plus a crash pattern, so `r = A[ı, F]`.
* Protocols are deterministic, know the round number, and have perfect recall: the local state is
  the input and the history of received messages (CSLib's lock-step protocols). The adversary
  chooses the input vector from the task's set and the failure pattern. There is no randomness.
* "Decides at time `m`" is the first write to the output register, by a process alive at time `m`.
  A task is a set of input vectors with a relation to output vectors. `SolvesSim` adds
  simultaneity, and `SolvesWithin A T t k` means every nonfaulty process decides by time `k`.
* A worst-case lower bound `k̂` means that no protocol solves the task within fewer rounds.
  All-case optimality compares, in every run (inputs and failure pattern), the decision time of the
  nonfaulty processes with that of every other `sim(T)` protocol.
* ConCon [MM08] is not formalized. `ConCon C A` is built from any CC protocol `C` with the §2.3
  properties used by the paper (`IsConCon`); maximality is not assumed. Lemmas 5 and 7 (cited
  from [DM90, MR08]) are hypotheses, quantified over all protocols, as the proof of Theorem 6 needs.

**Main results in Lean.** (namespace `Podc.SimultaneousAllCaseOptimal`)

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (`Delay(A, k̂)` solves `sim(P)`, decisions exactly at `k̂`) | `lemma1` | `Constructions.lean` |
| `A else B` solves `sim(P)` (proof of Thm 3) | `else_solvesSim` | `Constructions.lean` |
| Theorem 2 (`ConCon(A)` solves `sim(P)`, decides at `t + 1 − W`) | `theorem2` | `FastProtocols.lean` |
| Theorem 3 (`Opt` solves `sim(P)` in `min{k̂, t + 1 − W}`) | `theorem3` | `FastProtocols.lean` |
| Lemma 4 | `lemma4` | `Optimality.lean` |
| Theorem 6 (given Lemma 5 and ConCon) | `theorem6` | `Optimality.lean` |
| Theorem 8 (given Lemma 7 and ConCon) | `theorem8` | `Optimality.lean` |
| "Beating the worst-case bound needs time `≥ t + 1 − W`" (abstract) | `beat_lower_bound` | `Optimality.lean` |
| Lemma 5 for `t = n − 1`: **false** | `lemma5_false`, `not_lemma5Hyp` | `Lemma5False.lean` |
| Theorem 6 vs. Theorem 3 for `n = 3`, `t = 2`: **incompatible** | `thm3_thm6_incompatible`, `theorem6_fails`, `theorem6_counterexample` | `ThreeProcesses.lean`, `LoneCC.lean` |
| Corollary 9 for `k = 1`, `n = 3`, `t = 2`: **false** | `corollary9_false`, `not_lb_three` | `ThreeProcesses.lean` |
| Lemma 5 for `t = 1`, `n ≥ 3`; consensus needs 2 rounds | `lemma5_t1`, `consensus_lb_two` | `Chain.lean` |
| Theorem 6 with all hypotheses discharged (`t = 1`, `n ≥ 3`) | `theorem6_instance` | `NonVacuity.lean` |

**Not formalized.** The ConCon protocol itself and its maximality. Lemmas 5 and 7 for
`t ≤ n − 2`. Corollaries 10 and 11 (they rest on cited bounds for d-tight conditions and strong
renaming). §6. Corollary 9 for `t ≤ n − 2` with `n < t + k + 1` was not explored.

Which claim fails at `t = n − 1` for the actual ConCon of Mizrahi–Moses depends on its behaviour there, and
this is open. Its claimed maximality (iii) and the emptiness of the core before `t + 1 − W` (ii) are
incompatible there: some CC protocol puts the lone survivor's value into its core at time 1. If ConCon
satisfies (ii), Theorem 6 fails. Otherwise ConCon(A) decides before `t + 1 − W`, and Theorem 2's "decides
at time `t + 1 − W(F)`" fails.

**CSLib candidates** (marked `-- CSLib candidate`): decision tasks and first-write decisions over
`SyncCrash`, failure-pattern truncation and `SolvesSim.decides_of_alive`, waste, and the combinators
`Delay` and `Else` (`Model.lean`, `Constructions.lean`).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: `floodCC` (`t = 1`) and `loneCC` (`n = 3`, `t = 2`) satisfy the ConCon
hypotheses. `theorem6_instance` discharges every hypothesis of Theorem 6 for `t = 1`, `n ≥ 3`. The
model is CSLib's `Cslib.Computability.Distributed.SyncCrash.Model`.
