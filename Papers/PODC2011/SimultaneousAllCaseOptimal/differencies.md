# Differences between the formalization and the paper

Paper: M. P. Herlihy, Y. Moses, M. R. Tuttle, *Transforming worst-case optimal solutions for
simultaneous tasks into all-case optimal solutions*, PODC 2011 (ACM proceedings version, 8 pages;
no arXiv version).

## Errors in the paper (statement level)

1. **Lemma 5 is false for `t = n − 1`** (❌, rule R4: the paper explicitly assumes `t ≤ n − 1` in
   §2.1 and again at the start of §4, so the missing `t ≤ n − 2` is not an implied convention).
   For every `n ≥ 2`, `t = n − 1` and every complete input set: in the run `r⋆` where all processes
   but `p₀` crash in round 1 without sending, `W(r⋆) = t − 1`, so round 1 is premature, as it is in
   the failure-free run `r₀` (`W = 0`). At time 1 only `p₀` is alive in `r⋆` and it received nothing,
   so (for a protocol in which everybody sends in round 1) every run indistinguishable from `r⋆`
   at time 1 again has `p₀` alone with an empty inbox; `r₀` is not in the component.
   (`lemma5_false`, `not_lemma5Hyp`, `Lemma5False.lean`.) Lemma 7 fails in the same way (`c = 1`,
   `k = 1 ≤ t`). Lemma 5 is cited from [DM90, MR08], which presumably assume `n ≥ t + 2`; the paper
   restates it with its own range of `t`.

2. **Theorem 6 vs. Theorems 2/3 for `t = n − 1`** (❌; borderline 🚨, see "Verdict" below).
   `n = 3`, `t = 2`, binary consensus: `2` is a worst-case lower bound (`consensus_lb_two`),
   FloodSet solves consensus in 2 rounds (`floodSet_solvesWithin`), the inputs are complete
   (`theorem6_hypotheses`). In `r⋆` (two processes crash silently in round 1) `W = 1`, so
   Theorem 3 says `Opt(A, 2)` decides at `min{2, 3 − 1} = 2`; but `loneSurvivor` (the survivor sees
   an empty round-1 inbox, knows it is alone and decides its input at time 1; otherwise FloodSet)
   solves simultaneous consensus and decides at time 1 in `r⋆` (`loneSurvivor_solvesSim`,
   `loneSurvivor_decides`). Hence no protocol has both the timing of Theorem 3 and the all-case
   optimality of Theorem 6 (`thm3_thm6_incompatible`). For every `C` with the ConCon properties
   listed in §2.3 (accuracy, consistency, (i), (ii)), `Opt(floodSet 2, 2)` is not all-case optimal
   (`theorem6_fails`), and such a `C` exists (`loneCC_isConCon`, `theorem6_counterexample`).
   Which claim fails for the *real* ConCon of [MM08] depends on how that protocol behaves for
   `t = n − 1`: §2.3 also claims ConCon's core is maximal among CC protocols (iii); a CC protocol
   may put the lone survivor's value in its core at time 1 in `r⋆`, so (ii) and (iii) cannot both
   hold for `t = n − 1` (argued on paper, not formalized). If ConCon satisfies (ii), Theorem 6 fails;
   otherwise ConCon(A) decides before `t + 1 − W`, and Theorem 2's "decides at time `t + 1 − W(F)`"
   and Theorem 3's "execution time `min{k̂, t + 1 − W}`" fail.

3. **Corollary 9 is false for `k = 1`, `n = 3`, `t = 2`** (❌, application, R5). It claims
   `Opt(sa, ⌊t/k⌋ + 1) = Opt(sa, 3)` is all-case optimal and halts at `min{3, 3 − W}`, i.e. at time 3
   in failure-free runs; `floodSet 2` decides at time 2 in every run, so no protocol has both
   properties (`corollary9_false`). This does not depend on ConCon. The cause: the paper quotes the
   [CHLT00] bound `⌊t/k⌋ + 1` without its hypothesis `n ≥ t + k + 1`; for `n = 3`, `t = 2`, `k = 1`
   it is not a lower bound (`not_lb_three`). "Halts in time `min{…}`" is read as "decides at that
   time" (`Thm3Timing`), as in Theorem 3 ("decide at the earlier of `k̂` and `t + 1 − W`"); under the
   weaker reading "by that time" the corollary still fails for every ConCon with property (ii),
   since then `Opt(sa, 3)` decides at time 3 in failure-free runs. (Also for `t ≤ n − 2` with `n < t + k + 1` the premise
   "⌊t/k⌋ + 1 is the worst-case bound" may fail; not explored.)

## Proof gaps (statements true, proofs repaired)

4. **Simultaneous protocols and processes that crash later** (used in Lemma 1, Theorem 3, Lemma 4).
   The proofs use, without argument, that if a simultaneous protocol has some process decide at
   time `k`, every process *alive* at time `k` (possibly crashing later) decides at time `k` (Lemma 4:
   "Since the nonfaulty processes decide at time k in r and p has not failed, p must decide at time k"
   — `p` only survives round `k`; Theorem 3: "Whichever simultaneous protocol caused p to decide
   at time `k_p` would also have caused q to decide at time `k_p`"; Lemma 1: a faulty process of `A`
   could a priori decide after `k̂`, breaking the simultaneity of `Delay(A, k̂)`). True: truncate
   the failure pattern after round `k` (the process becomes correct, its state up to time `k` is
   unchanged) and use completeness and simultaneity there (`SolvesSim.decides_of_alive`,
   `SolvesWithin.decides_of_alive`, `Run.trunc`).

5. **Theorem 2, correctness.** "All processes … simulate the same run of A, and hence choose output
   values consistent with the input values" gives outputs consistent with the *simulated* input
   vector, which differs from the real one on processes outside the core (and the paper does not say
   which inputs those get; for non-complete input sets they must be chosen so that the vector is
   allowed). Repair: the simulated run is indistinguishable, for the core processes, from the run of
   `A` with the real inputs and the same silent crashes; `A`'s correctness there gives an output
   vector for the real inputs (`hist_simRun`, `decides_simRun`, proof of `theorem2`).

6. **Theorem 2, the simulated run is admissible**: the non-core processes are crashed in the actual
   run (the core contains all processes alive at `t + 1 − W`), so at most `t` crash; implicit in the
   paper (`simRun_isRun`).

## Modelling choices

* **Model** — CSLib's synchronous crash model `Cslib.SyncCrash`: runs = input vector + crash round
  `c ≥ 1` + set reached in the crashing round; at most `t` crashes (`Run.Admissible`). Protocols are
  deterministic and history-based (`Cslib.Byzantine.LockStep.Protocol`): the local state of `p` at
  time `m` is its input and its received messages (perfect recall). The paper allows arbitrary local
  states; with a state that forgets, Lemma 4 would only give "decide by time `k`" (that suffices for
  Theorem 6). Protocols know the clock (history length), as in the paper (shared global clock).
  No self-messages (irrelevant: a process knows its own state).
* **Decisions** — the output register is `decide p x h`; "p decides `d` at time `m`" = the first
  time the register is nonempty (`Decides`); the process must be alive at time `m`. A process that
  crashes in round `c` is alive at times `< c`.
* **Tasks** — `Task` = set of input vectors + relation; correctness quantifies over an output
  vector `o` with `(ı, o) ∈ P` matching every decision, as in §2.2. The output sets `Oᵢ` are a single
  type `O` (no loss of generality). `sim(P)` = `SolvesSim`.
* **Worst-case execution time / lower bound** — `SolvesWithin A T t k`: every nonfaulty process
  decides by time `k`. `WorstCaseLB T t k̂`: no protocol (with any message type in `Type`) solves `T`
  within `k < k̂`. "A solves P in time k̂" (Theorem 6) is `SolvesWithin A T t k̂`.
* **All-case optimality** — `AllCaseOptimal X`: `X` solves `sim(T)`, and for every protocol `B`
  solving `sim(T)` and every run (input vector, failure pattern) in which `B`'s nonfaulty processes
  decide at time `k`, `X`'s nonfaulty processes decide at some time `≤ k`.
* **Waste** — `E(F, k)` counts processes with a missing round-`j ≤ k` edge to a process surviving
  round `j` (`Run.exposed`); `W = max_{k ≤ n} (E(F,k) − k)` (equal to the paper's max over all `k`,
  since `E ≤ n` and `E(F,0) = 0`); premature: `k + W < t + 1`.
* **Similarity graph** — vertices are the runs (≤ `t` crashes, allowed inputs); an edge needs a
  process alive at time `k` in both runs with the same local state (input and history).
* **ConCon is not formalized.** `ConCon C A T` is built from any CC protocol `C` (`CCProtocol`,
  a core `P → Option I` per local state) with the properties listed in §2.3 (`IsConCon`: accuracy,
  consistency among processes alive at time `m`, (ii) empty core before `t + 1 − W`, (i) at
  `t + 1 − W` the core holds the inputs of all processes alive then). Maximality (iii) is not needed
  and not assumed. Non-vacuity: `floodCC` (`t = 1`, any `n`) and `loneCC` (`n = 3`, `t = 2`).
* **ConCon(A)'s simulated run** — the processes outside the core crash in round 1 and send nothing;
  inputs: some allowed input vector extending the core (chosen by `Classical.choose`; the real one
  exists). Decisions in the simulated run are computed locally (unbounded local computation, as in
  the paper).
* **`A else B`** — messages are pairs of optional component messages; decisions as in [MR08].
* **Lemmas 5 and 7 are hypotheses** (`Lemma5Hyp`, `Lemma7Hyp`), quantified over all protocols (the
  proof of Theorem 6 applies Lemma 5 to the constructed protocol `Opt(B, k₀)`). They are cited from
  [DM90, MR08] and not proved here except for `t = 1`, `n ≥ 3` (`lemma5_t1`); they are false for
  `t = n − 1` (item 1). The completeness / `c`-coverability of the input set enters only through
  these hypotheses.
* **Theorem 8** — the hypothesis `k̂ ≤ t + 2 − c` is stated as `k̂ + c ≤ t + 2` (natural numbers).
* **Not formalized**: the ConCon protocol of [MM08] and its maximality; Lemma 5 / Lemma 7 for
  `t ≤ n − 2`; the applications' cited bounds (Corollaries 10, 11: d-tight conditions, strong
  renaming with `log n`); the topological discussion (§6).

## Verdict

❌ False claim (worst label). Lemma 5 (numbered lemma, cited but restated with `t ≤ n − 1`) is false
for `t = n − 1`; Corollary 9 is false for `n = 3`, `t = 2`, `k = 1`; and for `t = n − 1` either
Theorem 6 (headline) or the timing claims of Theorems 2/3 are false. Borderline 🚨: Theorem 6 is
refuted for every ConCon satisfying the properties the paper lists in §2.3 (and such protocols
exist), but not for the actual [MM08] protocol, whose behaviour for `t = n − 1` we do not formalize;
if that protocol is maximal, it is Theorem 2's timing claim (not a headline per R5: it is not in the
abstract) that fails. For `t ≤ n − 2`, all checked statements other than Corollary 9 hold given Lemma 5 / Lemma 7
(Corollary 9 also needs [CHLT00]'s `n ≥ t + k + 1`).

Reviewer's note on the borderline (R5): Theorem 6 is refuted only for ConCon protocols with property
(ii). A maximal ConCon (iii) would put the lone survivor's value into the core at time 1 in `r⋆`;
then `Opt(A, k̂)` may well be all-case optimal for `t = n − 1`, and the false claim is the timing in
Theorems 2/3 (not in the abstract). So the headline is unestablished, not refuted: ❌. Lemma 5
(numbered, restated in the paper's setting "fix … `t ≤ n − 1`" of §4, and used in the proof of
Theorem 6) and Corollary 9 are false regardless of ConCon; `t = n − 1` with `n = 3` is not
degenerate (R2), and the paper explicitly allows it twice (R4).
