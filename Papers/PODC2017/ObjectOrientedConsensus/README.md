# Object Oriented Consensus — PODC 2017

Yehuda Afek, James Aspnes, Edo Cohen, Danny Vainstein. *Brief Announcement: Object Oriented Consensus.* PODC 2017.
DOI [10.1145/3087801.3087867](https://doi.org/10.1145/3087801.3087867). Formalized version: the full version
(16 pp., LIPIcs style, linked as "full" from Aspnes' page, file `podc2017-vac-ba-full.pdf`). It contains the
templates, Lemmas 1–7 and the proofs; numbering follows it.

**Verdict: ⚠️ Weakened.** The new framework holds: the VAC + reconciliator template (Lemma 1) is safe, and
Ben-Or's round is a VAC (Lemma 5). But the Phase-King decomposition into Aspnes' adopt-commit + conciliator
framework fails. Algorithm 2 with Algorithms 3–4 violates agreement for `n = 4`, `t = 1`, because a Byzantine
king makes the conciliator invalid. It works only with Phase-King's own decision rule (decide only after
`t + 1` kings). Also, Ben-Or composed with Algorithm 1 as printed ("decide, then halt") does not terminate.
Keeping decided processes in the protocol fixes this. Algorithm 3 (adopt-commit) can return the
non-input `2`.

## Mistakes in the paper

### ⚠️ Lemma 3 and §4.1 (Phase-King as Algorithm 2 with Algorithms 3–4)
Algorithm 4 is not a valid conciliator when the king is Byzantine. Combined with Algorithm 2's rule "on commit,
decide", this breaks agreement. With `n = 4`, `t = 1` and the Byzantine process as the king of round 1, honest
process 1 commits and decides `0` in round 1. Honest processes 2 and 3 adopt `0`, take the king's `1`, and in
round 2 commit and decide `1` (`PhaseKing.template_disagreement`).

**Impact.** Phase-King does not fit Aspnes' framework as claimed. The objects themselves are fine: Algorithm 3's
coherence and convergence (Lemma 2) and eventual agreement at an honest king (Lemma 3) hold. But the template
is correct only with a decision rule specific to Phase-King: decide on a commit only from round `t + 1` on.

**Details.** In round 1 the Byzantine process sends `0` to processes 1 and 2 and `1` to process 3 in exchange 1.
Then 1 and 2 hold `0` and 3 holds `2`. In exchange 2 it sends `0` to process 1 and `2` to the others. So process 1
sees `D(0) = 3 ≥ n − t` and commits `0`, while 2 and 3 see `D(0) = 2 < 3` and adopt `0`. As king it sends `1`
to everybody, and the adopters take `1`. In round 2 processes 2 and 3 hold `1`, the Byzantine process sends `1`,
and both commit `1`. Lemma 3's "Validity follows since the phase king's inputted value is `σm`" is false: a
Byzantine king's message need not be anybody's input. Algorithm 2's agreement needs exactly this validity
(`Exec2.agreement` takes `Exec2.ConciliatorValid` as a hypothesis). Coherence alone does not help, because
committed processes keep the committed value while adopters overwrite theirs with the king's. The original
Phase-King decides only after `t + 1` phases. The run respects the paper's remark that processes keep
participating after deciding.

**Repair.** If the kings of rounds `1, …, t + 1` are distinct and processes decide on their first commit
in a round `≥ t + 1`, agreement holds (`PhaseKing.repaired_agreement`). Every honest process commits in round
`t + 2` (`PhaseKing.repaired_termination`), and validity holds (`PhaseKing.repaired_validity`). The proof runs
through `PhaseKing.lemma3_honest_king`, `PhaseKing.persistence` and `PhaseKing.commit_after_honest_king`.

### 🔧 Lemma 1 with Lemmas 4–5 (Ben-Or decomposed by Algorithm 1)
Algorithm 1 halts a process right after it decides, but Algorithm 5 waits for `n − t` messages. So Ben-Or
composed with the template can block forever without any crash. With `n = 3`, `t = 1` and inputs `0, 0, 1`,
processes 0 and 1 commit `0` in round 1 and halt, process 2 adopts `0`, and in round 2 process 2 waits forever
for a second message (`BenOr.halting_blocks`).

**Impact.** Termination of the Ben-Or decomposition fails as printed. The local fix is the one the paper
already applies to Phase-King: decided processes keep participating. Safety is unaffected.

**Details.** Lemma 1's proof uses the round-`m + 1` VAC run by the adopters only ("by VAC's convergence all
remaining processors will decide"). But Lemma 5's termination ("the number of crash failures is less than half")
assumes `n − t` invokers, and halted processes look like crashed ones to the others.
`BenOr.wait_completes_iff`: a wait for `n − t` messages can complete iff at least `n − t` processes send.

**Repair.** The abstract Lemma 1 is proved for executions where the invokers of a round are any subset of the
previous round's returners, so it covers both halting and non-halting runs (`Exec1.lemma1_agreement`,
`Exec1.lemma1_validity`, `Exec1.lemma1_termination`). Ben-Or instantiates it (`BenOr.toExec1`,
`BenOr.agreement`). Without halting, every round has all `≥ n − t` correct processes as invokers, so every wait
completes (`BenOr.wait_completes_iff`).

### 🔧 Lemma 2, validity (Algorithm 3)
Algorithm 3 can return `(adopt, 2)`, and `2` is not an input. This happens even with no Byzantine process:
`n = 4`, `t = 1`, inputs `0, 0, 1, 1` (`PhaseKing.lemma2_validity_false`). The paper's "validity" proof in fact
proves convergence.

**Impact.** Harmless inside the Phase-King composition, since the conciliator replaces every adopted value
by `min(1, ·)` of the king's. But Algorithm 3 is not an adopt-commit object as defined.

**Repair.** A returned value is always an honest input or `2` (`PhaseKing.lemma2_validity_bot`). Returning the
own input instead of `(adopt, 2)` gives a correct adopt-commit object for `3t < n` with binary inputs
(`PhaseKing.lemma2_fixed`).

### ✏️ Slips
- Lemma 1, validity: "follows from the reconciliator's guarantees", but the reconciliator is only required to
  return an input at its agreement point (footnote 1). The proof assumes that every reconciliator output is
  valid ("all inputs to the VAC and reconciliator objects are clearly valid"). We take this as a hypothesis
  (`Exec1.RecValid`). It holds for the coin of Ben-Or (binary values) and for Raft's reconciliator, which
  returns `v`.

### Typos
- Algorithm 4 broadcasts `MIN(1, v)`. The proof of Lemma 3 needs the king's adopt-commit output `σ`, and
  `v` is not in scope.
- Algorithm 5: in `⟨1, v⟩`, `⟨2, v, ratify⟩` the `v` must be bound by the received message (Aspnes' survey),
  not be the own value. With the own value, a process holding `1` that receives ratify messages for `0` would
  vacillate, and coherence fails.
- "Algorithms 6 and 5 are the VAC's and reconciliator's implementations" has the order reversed. "Proved
  similarly to 3" should refer to Lemma 1. "Line 4/9/10" refers to unnumbered lines.

## Proof gaps (statements true)

### 🔧 Lemma 5, coherence over adopt & commit
The proof argues "at least one live processor broadcast a ratify message, thus every processor received at least
one ratify message". One correct sender does not make every process hear it within its `n − t` wait.

**Impact.** Statement true; repaired (`BenOr.Round.lemma5`).

**Details.** The correct argument: a commit means `> t` ratify senders, and any `n − t` received messages
include one of them, since `(n − t) + (t + 1) > n`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- *Objects* (`Template.lean`). VAC and AC objects are specified by one invocation round: invokers `I` with inputs,
  returners `O ⊆ I` with outputs (`IsVAC`, `IsAC`). For Byzantine models, `I = O = H` are the honest processes.
  A VAC becomes an AC by reporting `vacillate` as `adopt` (`IsVAC.toAC`).
- *Templates.* An execution of Algorithm 1 (`Exec1`) or Algorithm 2 (`Exec2`) is a sequence of such rounds.
  The invokers of round `m + 1` are a subset of the returners of round `m`, which covers crashes, halting
  after deciding, and continuing after deciding. Reconciliator and conciliator outputs are arbitrary; their
  validity, weak agreement and conciliator validity are hypotheses where needed. A process decides on its
  commits. Probability-1 termination is reduced to its deterministic step: a round with weak agreement makes
  every returner of the next round commit.
- *Phase-King* (`PhaseKing.lean`). Synchronous rounds, `n = |P|`, Byzantine set `Hᶜ` with `|Hᶜ| ≤ t` and
  `3t < n`, values `Fin 3`. The adversary (`Adv`) picks every Byzantine message of every round (exchange 1,
  exchange 2, king), with full information. Honest messages are computed by Algorithms 3 and 4. The king of
  round `m` is `king m`, an arbitrary function (the paper uses `m ↦ p_m`). All processes keep participating
  after deciding, and an honest king always broadcasts, even after committing. This reading favours the paper:
  in the literal Algorithm 2 a committing king does not call the conciliator.
- *Ben-Or* (`BenOr.lean`). Asynchronous crash model, `2t < n`. One round is given by the processes'
  views: the `n − t` senders each process waited for, in each exchange, from processes that actually sent.
  These views are otherwise arbitrary, so the scheduler, crashes and message delays are all covered. Safety is
  proved for all views. Liveness of a wait is `wait_completes_iff`. Coins are arbitrary values.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| VAC, AC (Section 2) | `IsVAC`, `IsAC`, `IsVAC.toAC` | `Template.lean` |
| Lemma 1 (Algorithm 1: agreement, validity, termination step) | `Exec1.lemma1_agreement`, `Exec1.lemma1_validity`, `Exec1.lemma1_termination`, `Exec1.weakAgreementAt_of_adopt` | `Template.lean` |
| Algorithm 2 ("proved similarly"), under conciliator validity | `Exec2.agreement`, `Exec2.validity`, `Exec2.termination` | `Template.lean` |
| Lemma 2 (coherence, convergence) | `PhaseKing.lemma2_coherence`, `PhaseKing.lemma2_convergence` | `PhaseKing.lean` |
| Lemma 2 (validity): false; corrected forms | `PhaseKing.lemma2_validity_false`, `PhaseKing.lemma2_validity_bot`, `PhaseKing.lemma2_fixed` | `PhaseKing.lean` |
| Lemma 3 (eventual agreement at an honest king), persistence | `PhaseKing.lemma3_honest_king`, `PhaseKing.persistence`, `PhaseKing.exists_honest_king` | `PhaseKing.lean` |
| §4.1 composition: disagreement; repaired rule | `PhaseKing.template_disagreement`, `PhaseKing.repaired_agreement`, `PhaseKing.repaired_termination`, `PhaseKing.repaired_validity` | `PhaseKing.lean` |
| Lemma 5 (Algorithm 5 is a VAC) | `BenOr.Round.lemma5` | `BenOr.lean` |
| Lemma 4 (deterministic part) | `BenOr.Round.lemma4_good_coins`, `BenOr.Round.adopted_value_majority` | `BenOr.lean` |
| Ben-Or via Algorithm 1: agreement; halting blocks | `BenOr.toExec1`, `BenOr.agreement`, `BenOr.halting_blocks`, `BenOr.wait_completes_iff` | `BenOr.lean` |

**Not formalized.** Raft (Section 4.3, Lemmas 6–7; informal timing assumptions). The paper itself notes after
Lemma 7's proof that Algorithm 10's convergence "does not hold as is", although Lemma 7 claims a correct VAC.
Also not formalized: Section 5 ("adopt-commit is not enough", informal; the claim "we have shown that VAC may
be implemented using two AC objects" has no counterpart in this version), and the measure-theoretic part of
probability-1 termination for Ben-Or (only the deterministic step is proved).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: the counterexample setups satisfy all hypotheses of the repaired theorems (`3t < n`, `|Hᶜ| ≤ t`,
distinct kings, binary inputs; first conjunct of `PhaseKing.template_disagreement`), and `BenOr.cxRound` is a
concrete Ben-Or round. Reuses CSLib's `Cslib.Byzantine.kingPhase_agreement` (`KingPhase.lean`) and quorum
counting (`Finset.threshold?`, `Finset.countEq`, `Foundations/Data/Finset/Quorum.lean`).
