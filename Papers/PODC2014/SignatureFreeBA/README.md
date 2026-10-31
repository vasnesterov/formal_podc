# Signature-Free Asynchronous Byzantine Consensus — PODC 2014

Achour Mostéfaoui, Hamouma Moumen, Michel Raynal. *Signature-Free Asynchronous Byzantine Consensus
with t < n/3 and O(n²) Messages.* PODC 2014. DOI
[10.1145/2611462.2611468](https://doi.org/10.1145/2611462.2611468). Formalized version: the full
version, IRISA technical report PI-2016 (February 2014), HAL
[hal-00944019](https://hal.science/hal-00944019) (file `RR-2016-Consensus-optimal-V5.pdf`, 13 pages;
same algorithm, lemmas and numbering as the proceedings version). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🚨 Headline claim false.** The algorithm of Figure 2 does **not** terminate with
probability 1, so Theorem 2 (it solves randomized binary consensus), Lemma 5 and Theorem 3
("expected decision time is four rounds", also in the abstract) are false. For `n = 4`, `t = 1`
and inputs `0, 0, 1`, an adversary that controls the schedule and the Byzantine process, and
learns each coin only after two correct processes have asked for it, prevents every decision
forever, whatever the coin values. The safety part holds: BV-broadcast (Theorem 1), Lemmas 1–4,
validity and agreement. So do the two deterministic steps of the termination proof.

## Mistakes in the paper

* **Lemma 5, BC-Termination of Theorem 2, and Theorem 3 are false.** The proof of Lemma 5 has a
  "Claim": with probability 1 all correct processes eventually have the same estimate. Its third
  case (some correct processes adopt the value `v` of a singleton `values` at line 09, others
  adopt the coin `s` at line 10) says that "`s` is equal to `v` with probability 1/2", because the
  coin is independent of the scheduler. But `v` is not fixed before the coin is drawn. The
  adversary can wait until the coin of the round is known and *then* decide which value the
  remaining processes see. The paper's model gives it this power: Byzantine processes control
  the message schedule, and the coin is only required not to be computable *in advance*
  (Section 4.1 and footnote 2).
  Our counterexample: `n = 4`, `t = 1`, processes `p0, p1, p2` correct with estimates `a, a, ¬a`
  (initially `0, 0, 1`), `p3` Byzantine. In every round:
  1. `p3` sends `B_VAL(¬a)` to everybody. So `¬a` gets `t + 1` copies, everybody echoes it, and
     both values enter every `bin_values`. The adversary picks the order: `p0` sees `a` first and
     broadcasts `AUX(a)`, `p1` sees `¬a` first and broadcasts `AUX(¬a)`.
  2. `p0` and `p1` receive `AUX(a)`, `AUX(¬a)`, `AUX(a)` (the last from `p3`). So `values = {0,1}`,
     both call `random()` and adopt the coin `s`.
  3. Now the adversary knows `s`. It makes `p2` see `¬s` first in `bin_values`, so `p2` broadcasts
     `AUX(¬s)`. Then `p2` receives `AUX(¬s)` from itself, from `p3` and from whichever of `p0`, `p1`
     sent `¬s`. Its `values = {¬s}` differs from the coin, so `p2` does not decide and adopts `¬s`.
  The next round starts again with two processes at one value and one at the other. Nobody ever
  decides, for **every** coin sequence. The execution is weakly fair: every message between
  correct processes is delivered and every enabled step is taken. It is also an execution of
  the deterministic code: processes react to each message at once, and every `bin_values` and
  `values` they use is the only possible one. So the probability of termination is 0, not 1,
  and the expected number of rounds is infinite, not 4.
  Theorem 2 claims Figure 2 solves randomized consensus, and the abstract claims it decides in 4
  expected rounds. The paper's own algorithm is wrong, so this is a false headline claim
  (rule R5). (`Attack.counterexample`, `Attack.prob_termination_eq_zero`, `Attack.coin_used_late`,
  `Local.eager`, `Local.forced`)
  *Scope.* The adversary needs the coin of a round only after `p0` and `p1` (and `p3`) have called
  `random()`. So the attack also works against a threshold coin that is revealed by `n − t`
  shares. It even works against an ideal coin that tells `b_r` only to the caller: the adversary
  reads `s` off `p0`'s next broadcast `B_VAL[r+1](s)`, which the Byzantine `p3` receives (this is
  exactly what `Attack.strat` looks at). The argument of the Claim would go through only if the
  adversary could not see the coin before *all* correct processes have fixed their `values`, e.g.
  with a scheduler that does not see message contents (the "oblivious scheduler" of the paper's
  footnote 2). The paper's model explicitly gives the Byzantine processes control of the
  schedule, and no common-coin implementation in an asynchronous Byzantine system can wait for
  all correct processes.
  The same liveness problem was reported by P. Tholoniat and V. Gramoli, *Formal Verification of
  Blockchain Byzantine Fault Tolerance* (arXiv:1909.07453, 2019), with another `n = 4`, `t = 1`
  scenario; according to them the authors confirmed it, and the journal version (J. ACM 2015)
  remarks that a fair scheduler and a perfect common coin are needed for this algorithm and gives a
  new algorithm. We did not check the journal version.
* **The rest of Lemma 5's proof is correct.** No correct process blocks at line 03 or 05
  (`Exec.no_blocking`). Once all correct processes start a round with the same estimate `v`,
  they all decide in the first later round whose coin is `v` (`Exec.decide_of_unanimous`). In
  particular, with unanimous inputs the algorithm terminates as soon as the coin shows the input
  (`Exec.decide_of_unanimous_inputs`).
* **Typo** in the proof of Lemma 2: "`p_x` sent `AUX[r](v)` to `p_i` and `AUX[r](w)` to `p_i`"
  should end with "to `p_j`".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* The interleaving model `Cslib.Byzantine.AsyncBroadcast` (staged in
  `Podc/Computability/Distributed/Byzantine/`). Asynchronous reliable authenticated point-to-point
  channels; each delivery is a separate event chosen by the adversary. At most `t` Byzantine
  processes; they can make anybody receive anything from them. Corruption is *adaptive* (at any
  time), which is stronger than the paper's static model.
* The algorithm (`Model.lean`, `mmr t coin`): messages `bval r v tag` = `B_VAL[r](v)` and
  `aux r v` = `AUX[r](v)`. The local tag on a process's own `B_VAL` (ignored by receivers)
  records its estimate and whether its `values` was a singleton. Guards are *liberal*: a wait may
  be passed later than possible and with any admissible set of `n − t` messages, and echoes and
  decisions are separate steps. This is a superset of the paper's behaviours, so the safety
  results cover the code.
* Common coin: a fixed sequence `coin : ℕ → Bool`, the same for all processes. Safety holds for
  every coin sequence. Liveness is proved in every weakly fair execution.
* Counterexample: the adversary is a function `strat` of the time and the current global state
  (full information about the past, including coins already used by processes, and nothing about
  other coins). The execution is generated from `strat` for each coin sequence. The schedule of
  a round is a finite, decidable script, checked by `decide`. `coin_used_late` shows that the
  script of round `r` depends on the coin of round `r` only after `p0` and `p1` have called
  `random()`. `eager`, `forced` and `quiet_final` show that the schedule uses none of the liberal
  freedoms within the round. In the other rounds no step is enabled during the round (they are
  closed, or nothing of them has been delivered yet); we argue this in prose, not in Lean.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (BV-broadcast: obligation, justification, uniformity, termination) | `theorem_1` (`Exec.bv_obligation`, `bv_justification`, `Exec.bv_uniformity`, `Exec.bv_termination`) | `BVBroadcast.lean` |
| Lemma 1 | `lemma_1` | `Safety.lean` |
| Lemma 2 | `lemma_2` | `Safety.lean` |
| Lemma 3 (BC-Validity) | `lemma_3` | `Safety.lean` |
| Lemma 4 (BC-Agreement) | `lemma_4`, `est_coin_of_single` | `Safety.lean` |
| Theorem 2, safety (validity, agreement, one-shot) | `theorem_2_safety` | `Safety.lean` |
| Lemma 5, no blocking | `Exec.no_blocking` | `Liveness.lean` |
| Lemma 5, decision after unanimity | `Exec.decide_of_unanimous`, `Exec.decide_of_unanimous_inputs` | `Liveness.lean` |
| **Lemma 5 / Theorem 2 (termination) / Theorem 3 — false** | `Attack.counterexample`, `Attack.prob_termination_eq_zero` | `Counterexample.lean` |
| The counterexample is a legal, eager, forced schedule; coin used late | `Local.valid_script`, `Local.eager`, `Local.forced`, `Local.quiet_final`, `Attack.coin_used_late` | `Local.lean`, `Counterexample.lean` |

**Not formalized.** Message, bit and step complexities (the "Cost" paragraphs, `O(n²)` messages per
round). Probability spaces: the positive termination results are deterministic statements about
fair executions. The counterexample is for `n = 4`, `t = 1` only (one instance refutes the claim
for all `n > 3t`).

**Trust.** No `sorry`; all listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The round schedule is checked by `decide` / `decide +kernel` (no `native_decide`).
Non-vacuity: the counterexample is itself a fair execution, and `exists_fair` (CSLib candidate model)
gives fair executions of `mmr` for all parameters (`Exec.exists_fair_mmr`).
