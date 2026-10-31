# Weakest Failure Detector for Eventual Consistency — PODC 2015

Swan Dubois, Rachid Guerraoui, Petr Kuznetsov, Franck Petit, Pierre Sens. *The Weakest Failure Detector for
Eventual Consistency.* PODC 2015. DOI [10.1145/2767386.2767404](https://doi.org/10.1145/2767386.2767404).
Formalized version: arXiv:1505.03469v1 (full version with the appendix; numbering follows it).

**Verdict: ❌ False claim.** The sufficiency half of the headline holds: `Ω` implements eventual consensus (Lemma
2), and EC and ETOB are equivalent (Theorem 1). Both proofs needed the same small repair. Lemma 3 is false: the
paper's ETOB algorithm (Algorithm 5) is not stable over non-FIFO links. Adding sequence numbers to promotions fixes
it. Theorem 3 (EC ⇔ EIC, appendix) is false if EIC-Agreement is read literally, and holds among correct
processes. The necessity half (Lemma 1, a CHT-style extraction) is not formalized.

## Mistakes in the paper

- **Lemma 3 is false (Algorithm 5 does not implement ETOB).** On receiving a promotion from its current leader,
  a process sets `d_i := promote_j`. Links are reliable but not FIFO, so an older, shorter promotion can arrive
  after a newer one, and then `d_i` shrinks. Counterexample: two processes, no crashes, `Ω` outputs process `0`
  everywhere from time 0, and the application broadcasts `0, 1, 2, …`. The adversary delivers promotion `b`
  followed by the delayed promotion `b − 1` infinitely often, with all delays bounded. ETOB-Stability then fails
  for every `τ`. The proof's step "`d_i(t₁) = promote_j(t₃)`, `d_i(t₂) = promote_j(t₄)`, hence prefix" silently
  assumes `t₃ ≤ t₄`, i.e. FIFO delivery. The same run refutes the §5 claim that Algorithm 5 gives TOB when `Ω` is
  stable from the start. The proof also uses a "longest communication delay `Δc`", which need not exist in an
  asynchronous run. Repair: the leader numbers its promotions, and a process adopts a promotion only if its number
  is larger than the last one it adopted from that leader. The repaired algorithm implements ETOB from `Ω` in
  every environment, and TOB under a leader that is stable from the start. (`Alg5.lemma_3_false`;
  `Alg5Fixed.lemma_3_fixed`, `Alg5Fixed.tob_of_const_leader`)
- **Theorem 3 / Lemma 4 fail under the literal reading of EIC-Agreement.** The paper requires that "no two
  processes return infinitely different values", and it defines a process's response as its *last* response, so
  a crashed process keeps its response forever. Under this reading, EIC cannot be implemented with `Ω` at all,
  already with 3 processes and at least one correct. Two processes run solo, respond to instance 0 with their
  own, different proposals, and crash, and nothing can change their last responses afterwards. EC, by contrast,
  is implementable with `Ω`. Algorithm 6 also violates uniform agreement concretely: a faulty process decides
  `true` and crashes while the correct one decides `false` forever, even though the EC box satisfies EC. With
  agreement among correct processes, Lemmas 4 and 5, and hence Theorem 3, hold. This is an appendix result.
  Reading it among correct processes is a plausible intent, but the paper words it exactly like the uniform
  EC-Agreement, so we count it as a false statement. (`EICImpossible.not_solvesEIC`,
  `Alg6Counterexample.not_EICAgreement`; `Alg6.lemma4`, `Alg7.lemma5`)
- **Uniform agreement proofs ignore faulty processes (Lemma 2 and Theorem 1, ETOB → EC; proof repaired).** Both
  proofs pick `k` as the first instance invoked after the stabilization time of `Ω` (resp. ETOB). However, `Ω`
  and ETOB constrain only correct processes, and EC-Agreement covers all processes. A faulty process that is
  still alive after that time can return a different value. Fix: also choose `k` after every faulty process has
  crashed, which is possible because `P` is finite. (`Alg4.agreement`, `ETOBtoEC.ecAgreement`)
- **Algorithm 2 breaks ETOB's usage assumption.** ETOB is specified only for distinct broadcast messages, but two
  processes that propose the same `v` to instance `ℓ` both broadcast `(ℓ, v)`. Local fix: broadcast `(p_i, ℓ, v)`.
  (`ETOBtoEC.tobHist_distinct`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous message passing with crash failures and failure detectors, following CHT / Jayanti–Toueg
  (`Podc/Computability/Distributed/MessagePassing/FailureDetectors/Model.lean`). The set of processes `P` is
  finite. In each step a process receives one message in transit, a time-out (`λ`), or an input; it queries the
  failure detector and broadcasts at most one message.
- Links are reliable and **not FIFO**. Failure patterns are monotone.
- An admissible run delivers every message to every correct process, and each correct process takes infinitely
  many time-out steps.
- `Ω` is the set of histories that eventually output the same correct process at all correct processes.
- All positive results hold for every failure pattern, so they hold in every environment.
- Transformations treat the black box adversarially. Its responses or outputs are input events chosen by the
  scheduler, and the box is constrained only by the hypothesis that its history meets the spec whenever it is
  used properly. This covers every implementation of the box.
- For EC, this assume-guarantee form is circular: a box that answers an instance twice makes its own usage
  improper and becomes unconstrained (`etob_of_ec_needs_integrity`). We therefore also assume EC-Integrity of
  the box in EC → ETOB, and Algorithms 6/7 use "invoke `j+1` at the *first* response to `j`".
- Applications are folded in: process `p` proposes `inp p j` to instance `j`. The algorithms are deterministic,
  so this loses nothing.
- Instances are numbered from 0.

**Main results in Lean.** All names live in the namespace `Podc.WeakestFDEventualConsistency`.

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (EC ⇔ ETOB), with non-vacuity witnesses | `theorem1`, `ECtoETOB.etob_of_ec`, `ETOBtoEC.ec_of_etob`, `*_nonvacuous` | `Theorem1.lean`, `ECtoETOB.lean`, `ETOBtoEC.lean` |
| Lemma 2 (Algorithm 4: EC from `Ω`) | `Alg4.lemma_2` | `ECFromOmega.lean` |
| Lemma 3 (Algorithm 5: ETOB from `Ω`) — false | `Alg5.lemma_3_false` | `ETOBAlgorithm.lean` |
| Lemma 3, repaired algorithm; §5 TOB claim | `Alg5Fixed.lemma_3_fixed`, `Alg5Fixed.tob_of_const_leader` | `ETOBAlgorithmFixed.lean` |
| Lemma 4 (Algorithm 6: EC → EIC), correct-process agreement | `Alg6.lemma4` | `ECtoEIC.lean` |
| Lemma 4, literal reading — false | `Alg6Counterexample.not_EICAgreement` | `ECtoEICCounterexample.lean` |
| Lemma 5 (Algorithm 7: EIC → EC) | `Alg7.lemma5` | `EICtoEC.lean` |
| Theorem 3, literal reading — false (literal EIC unsolvable with `Ω`) | `EICImpossible.not_solvesEIC` | `EICImpossible.lean` |
| (modelling) the integrity hypothesis of EC → ETOB is needed | `ECtoETOB.etob_of_ec_needs_integrity` | `ECtoETOBNeedsIntegrity.lean` |

**Not formalized.**
- Lemma 1 (`Ω` is necessary for EC; a CHT extraction with `k`-tags and Algorithm 3), and therefore the necessity
  half of Theorem 2. An informal check of Lemma 1 found no error.
- TOB-Causal-Order, the communication-step claims, and Sections 6–7.

**Trust.** No `sorry`. All theorems listed above use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity checks:
- Theorem 1: admissible runs satisfying all hypotheses of both directions (`*_nonvacuous`).
- Lemma 3 counterexample: `UpdatePromote` has an implementation (`exists_updValid`), and the counterexample holds
  for every implementation.

The model is staged in `Podc/` as a CSLib candidate (CHT model, `Ω`, admissible runs, invariant principles);
`RunTools.lean` (adaptive schedules, indistinguishability) is a candidate addition to it.
