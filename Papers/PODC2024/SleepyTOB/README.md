# Asynchrony-Resilient Sleepy TOB — PODC 2024

Francesco D'Amato, Giuliano Losa, Luca Zanolini. *Asynchrony-Resilient Sleepy Total-Order Broadcast
Protocols.* PODC 2024. DOI [10.1145/3662158.3662779](https://doi.org/10.1145/3662158.3662779).
Formalized version: arXiv [2309.05347](https://arxiv.org/abs/2309.05347) v2 (6 May 2024); numbering
follows it.

**Verdict: ⚠️ Minor statement issues.** Lemma 1 (the extended graded agreement and clique validity),
Lemmas 2–3 and the headline Theorem 2 (π-asynchrony resilience for `π < η`) hold for the protocol the
paper means, which is Malkhi–Momose–Ren's protocol [MMR] with latest unexpired votes. Algorithm 1 *as
printed* is not that protocol. Its input rule lets a Byzantine VRF winner erase the lock, and the
printed algorithm then violates safety even with no asynchrony at all. With the one-word fix taken
from [MMR] and from the paper's own proofs, all checked statements are true. Two proofs needed
repairs.

## Mistakes in the paper

* **Algorithm 1 as printed is unsafe (input rule of `GA_{v,1}`).** Lines 6–7 and the prose say that
  the input of `GA_{v,1}` is the highest-VRF proposal *not conflicting with* `L_{v-1}` (arXiv v1 says
  the same, three times). Safety needs the [MMR]-style lock rule: the proposal must *extend*
  `L_{v-1}`, and if there is none the process inputs `L_{v-1}` itself. The printed algorithm has no
  such fallback. With the printed rule, the winning proposal may be a strict prefix of the decided
  log, and then the lock is lost.
  Counterexample: 4 processes, process 3 Byzantine, everyone always awake, all messages delivered at
  once, `η = 2`. All honest processes vote `[1]` in view 1 and decide `[1]` in round 3. The
  Byzantine process then wins the VRF with the proposal `[]` (the genesis log), which does not
  conflict with `L_1 = [1]`, so every honest process votes `[]`. In view 3 an honest proposal
  `[2] = b‖C_2` wins, and `[2]` is decided in round 7. So Lemma 3 fails (round-3 voters do not
  extend the decided `[1]`), Theorem 1's safety fails (with `π = 0`), and Theorem 2 fails (`[1] ∈ D_ra`
  for `ra = 3`, `π = 1`). All of the paper's hypotheses hold in this execution: η-sleepiness
  `3 > 2/3·4` in every round, Equations 4 and 5, `π < η`. The view-1 votes `[1]` come from a
  Byzantine view-0 proposal that wins the lottery. Shifting the run by one view gives a variant in
  which the Byzantine process wins only once (not formalized). We count this, as a borderline call, as a slip with
  evident intent (R3) rather than a false algorithm. The paper presents Algorithm 1 as [MMR]'s
  protocol and defers its correctness to [MMR]'s proof. Its own proofs use the step "outputs `Λ`
  with grade 1, hence votes for an extension of `Λ`", which holds in odd rounds only under the
  "extends" rule. We formalize the [MMR] rule (`Exec.Follows`), and the printed
  rule only for the counterexample (`algorithm_1_literal_unsafe`,
  `theorem_1_false_for_literal_algorithm`, `theorem_2_false_for_literal_algorithm`).
* **The base case of Lemma 3 does not follow from graded consistency; statement true.** The proof
  says that once some process decides `Λ` (grade 1 in `GA_{v-1,2}`), "by graded consistency" every
  process of `H_r` votes for an extension of `Λ`. Graded consistency only gives `Λ` grade `≥ 0`
  elsewhere. Bounded divergence allows a second, conflicting and longer grade-0 log, which would
  become `L_{v-1}`. Example: 7 honest processes (5 vote `[1]`, 2 vote `[2,5]`) and 2 Byzantine
  processes voting `[1]` to `p` and `[2,5]` to `q`. Then `p` outputs `[1]` with grade 1, while
  `q`'s longest output is `[2,5]` (`graded_consistency_insufficient`). The repair is [MMR]'s
  argument. Integrity of `GA_{v-1,2}` makes every output extended by an honest `GA_{v-1,2}` input.
  Those inputs are grade-1 outputs of `GA_{v-1,1}` and pairwise compatible by its uniqueness. So no
  output of `GA_{v-1,2}` conflicts with `Λ`, and the longest one extends `Λ`
  (`Exec.Follows.decision_lock`). In the paper's own network model, all honest receivers of a
  synchronous round receive the same messages, so their tallies agree and the conclusion also
  follows directly. Only the cited justification is insufficient.
* **Clique validity is applied outside its stated hypotheses; easy repair.** Lemma 1 requires
  `H' ⊆ H_r ∪ H_{r+1}` and concludes only for receivers in `H'`. The proof of Lemma 2 applies it to
  `H' = H_ra \ B_r'`, which contains processes asleep at both `r'` and `r'+1`. The proof of Theorem 2
  needs the conclusion for every receiver of the synchronous round `ra+π+1` and redoes the argument
  by hand. The proof of clique validity in fact only needs `H'` disjoint from `B_r`, and works for
  any receiver whose initial votes contain the clique's votes. We prove this general form
  (`clique_validity`) and derive the paper's form from it (`lemma_1_clique_validity`).
* **Integrity in Definition 4 is misstated.** "There exists a well-behaved process that inputs the
  log" fails for every graded agreement with validity: one honest process with input `[1]` outputs
  `[]` with grade 1 (`integrity_literal_false`). The intended property, as in [MMR] and the proof of
  Lemma 1, is that some honest input *extends* the log. That is what we prove.
* **Implicit assumptions and small slips.**
  - Lemma 2's base case needs round `ra` to be η-sleepy, Lemma 3 needs η-sleepiness in rounds
    `≤ ra`, and Theorem 2 needs it in rounds `≥ ra+π+2`. The paper states Equations 1–2 as the
    synchronous-round assumptions but uses Equation 3 throughout. We show that Equations 1 and 2
    imply 3 with exactly the paper's `β̃` (`Exec.sleepy_of_churn_of_failure`, `betaTilde_identity`).
    Footnote 7's equivalences hold (`Exec.footnote_7`).
  - Algorithm 1, line 1, for `v = 1` refers to `GA_{0,2}`, which does not exist (view 0 only
    proposes). We start decisions at round 3 and leave round-1 votes unconstrained.
  - In the proof of Theorem 2, `|H_ra \ H_{ra+π+1}|` should be `|H_ra \ B_{ra+π+1}|`. In the proof
    of Lemma 2, `|S_r' ∪ P0|` should be `|O_r' ∪ P0|`, and the latest votes in `M0` are "from rounds
    no later than `ra`" only up to later honest votes, which also extend `Λ`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* `n` processes, synchronous rounds `0, 1, 2, …` with sleepiness: `O_r` is awake at round `r`, and
  `B_r ⊆ O_r` is Byzantine with a growing adversary (`B_r ⊆ B_{r+1}`; Byzantine processes never
  sleep). `H_r = O_r \ B_r`, and the receivers of round `r` are `H_{r+1}`. Signatures are modelled
  by message senders. There is no randomness: VRF proposals are abstracted adversarially. In odd
  rounds an honest vote is any extension of a longest output `L_{v-1}`, which covers every proposal
  that can win the VRF lottery, so safety holds for every outcome.
* Messages are `(sender, round, log)`. Each `q ∈ H_t` (`t ≥ 1`) sends one vote per round. Byzantine
  processes send arbitrary sets of messages with arbitrary round tags, including back-dated ones.
  `rcv p r` (messages received by the end of round `r`) only grows. In a synchronous round, every
  receiver has every message sent so far. In the single asynchronous period `[ra+1, ra+π]` delivery
  is arbitrary.
* Expiration: the GA of round `r` is tallied from the latest received votes with round tag in
  `[r-η, r]`. A sender whose latest votes equivocate is discarded. Grade 1 means more than `2m/3`
  votes for extensions, an output means more than `m/3`, and `β = 1/3` throughout.
* We prove that this tally *is* an instance of the extended GA of Figure 3, with
  `M0` = latest votes from `[r-η, r)` and `P0 = O_{r-η,r}` (`Exec.tally_eq_ga_M`). This is the
  correspondence claimed in Section 3.3, so Lemma 1 transfers verbatim (`Exec.isGA`, `Exec.clique`).
* Figure 3 is modelled as an abstract one-shot instance (`ExtGA`). Each receiver has initial votes
  `M0` from `P0`. Honest senders send only their input, absent senders send nothing, Byzantine
  senders send anything. Round-`r` votes override `M0`, and equivocations are discarded.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (GA properties, synchronous round) | `lemma_1` | `ExtendedGA.lean` |
| Lemma 1 (clique validity) | `lemma_1_clique_validity`, general form `clique_validity` | `ExtendedGA.lean` |
| §3.3: modified Alg. 1 GA = extended GA | `Exec.tally_eq_ga_M`, `Exec.isGA` | `Model.lean` |
| Lemma 2 | `Exec.lemma_2` | `Resilience.lean` |
| Lemma 3 | `Exec.lemma_3` (base case `Exec.Follows.decision_lock`) | `Resilience.lean` |
| Theorem 2 | `Exec.theorem_2`; non-vacuity `theorem_2_hypotheses_satisfiable` | `Resilience.lean`, `Counterexample.lean` |
| Theorem 1, safety part (no asynchrony) | `Exec.theorem_1_safety` | `Resilience.lean` |
| Algorithm 1 as printed is unsafe | `algorithm_1_literal_unsafe`, `theorem_1_false_for_literal_algorithm`, `theorem_2_false_for_literal_algorithm` | `Counterexample.lean` |
| Def. 4 literal integrity fails | `integrity_literal_false` | `Examples.lean` |
| Lemma 3's cited argument insufficient | `graded_consistency_insufficient` | `Examples.lean` |
| §2.3: Eq. 1 ∧ Eq. 2 ⇒ Eq. 3; footnote 7 | `Exec.sleepy_of_churn_of_failure`, `betaTilde_identity`, `Exec.footnote_7` | `Adversary.lean` |

**Not formalized.** Liveness: Theorem 1's liveness half, which is probabilistic via the VRF and
deferred to [MMR], and Theorem 3 (healing), which has a two-line informal proof. Also the necessity
of `β̃` claimed in Figure 1's caption. Safety under the original (non-expiring) MMR protocol is not
treated separately: it is the case `η = 0`.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `theorem_2_hypotheses_satisfiable` exhibits an execution of the modified
Algorithm 1 that satisfies every hypothesis of Theorem 2 and contains a decision before the
asynchronous period. The model is self-contained in this folder (Mathlib only). `Tally.lean`
(logs, faithful tallies, graded-agreement counting) is marked as a CSLib candidate.
