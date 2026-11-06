# Differences between the formalization and the paper

Paper: Dubois, Guerraoui, Kuznetsov, Petit, Sens, *The Weakest Failure Detector for Eventual Consistency*,
PODC 2015, arXiv:1505.03469v1 (the version formalized; numbering follows it).

## Errors and gaps in the paper

1. **🔧 Lemma 3 is false (statement-level).** Algorithm 5 (ETOB from Ω) does not satisfy
   ETOB-Stability in the paper's model, in which links are reliable but not FIFO (a step receives *a* message in
   transit, as in the CHT model the paper adopts). A process overwrites `d_i` with every promotion of its current
   leader, so an older, shorter promotion that is delivered after a newer one makes `d_i` shrink. With infinitely
   many broadcasts this happens at arbitrarily late times, even when `Ω` outputs the same correct process at all
   processes from time 0 (`Alg5.lemma_3_false`: 2 processes, no crashes, broadcasts `0, 1, 2, …`, every odd block
   delivers promotion `b` and then the delayed promotion `b − 1`; all message delays are bounded by 16 time units).
   The proof's step "there exist `t₃ ≤ t₁`, `t₄ ≤ t₂` with `d_i(t₁) = promote_j(t₃)`, `d_i(t₂) = promote_j(t₄)`,
   hence prefix" silently needs `t₃ ≤ t₄`, i.e. FIFO delivery, a channel property the paper never fixes. The
   sufficiency half of "Ω is the weakest failure detector for EC/ETOB" rests on Lemma 2 + Theorem 1, which hold.
   The paper's model (§2) has "a reliable link" between each pair of processes and configurations holding "the set
   of messages in transit", from which a step receives "a single message" (the CHT / Jayanti–Toueg message buffer);
   FIFO order is assumed nowhere in the paper, so the counterexample is within the paper's model. It is also within
   the proof's implicit assumption that a longest delay `Δc` exists (all delays ≤ 16), and `Ω` is stable from time 0.
   The same run refutes the introduction's claim (2) that Algorithm 5 implements TOB when Ω outputs the same leader
   everywhere from the beginning.
   The proof also uses "`Δc` = the longest communication delay between two correct processes in `r`", which need
   not exist in an asynchronous run (delays are finite but unbounded).
2. **🔧 Lemma 2: proof gap, repaired.** EC-Agreement ("no two processes return different values", uniform) is proved
   for `k` = first instance invoked after `τ_Ω`. But `Ω` constrains only correct processes: a faulty process still
   alive after `τ_Ω` may trust another leader and return a different value. Repair: choose `k` after `τ_Ω` *and*
   after every faulty process has crashed (finitely many processes) (`Alg4.agreement`).
3. **🔧 Theorem 3 / Lemma 4 are false under the literal reading of EIC-Agreement.** EIC-Agreement says "no two processes return infinitely different values", and the response of a process
   at time `t` is its *last* response before `t`, so a crashed process keeps its last response forever. Under this
   (uniform) reading EIC cannot be implemented with `Ω` at all, already with 3 processes and at least one correct
   process (`EICImpossible.not_solvesEIC`): `a` (proposing `false`) and `b` (proposing `true`) run solo until they
   respond to instance `0`, which they must do with their own proposals, and crash; the correct third process
   cannot change their last responses. Since EC is implementable with `Ω` (Lemma 2), EC and literal EIC are not
   equivalent. Algorithm 6 itself also violates uniform EIC-Agreement on an admissible run whose EC black box
   satisfies EC (`Alg6Counterexample.not_EICAgreement`: a faulty process decides `true` for instance `0` and
   crashes, the correct one decides `false` forever). With EIC-Agreement among **correct** processes, Lemma 4,
   Lemma 5 and hence Theorem 3 hold (`Alg6.lemma4`, `Alg7.lemma5`). The correct-process
   reading is a plausible intent, but the paper uses the uniform wording for EC-Agreement too (where it matters
   and holds), and the "last response" convention makes the uniform reading unambiguous. Appendix result.
4. **🔧 Algorithm 2 (`T_{ETOB→EC}`) violates the ETOB usage assumption (local fix).** ETOB is only specified
   "assuming that broadcast messages are distinct", but Algorithm 2 broadcasts `(ℓ, v)`, so two processes proposing
   the same `v` to instance `ℓ` broadcast the same message and the black box is unconstrained. Fix: broadcast
   `(p_i, ℓ, v)` and let `First(ℓ)` pick the first message of the form `(_, ℓ, _)` (`ETOBtoEC.tobHist_distinct`).
5. **🔧 Theorem 1, direction ETOB → EC: proof gap, repaired.** The paper proves agreement only for two *correct*
   processes (with `k` = first instance invoked after `τ`), but EC-Agreement is uniform. A faulty process still
   alive after `τ` is not constrained by ETOB-Stability/Total-order. Repair as in Lemma 2: `k` beyond every
   instance invoked before `τ` and before the crashes of all faulty processes (`ETOBtoEC.ecAgreement`).
6. **🔧 Lemma 3, proof issue.** The proof uses "`Δc` = the longest communication delay" (see item 1). In the
   repaired algorithm (sequence numbers on promotions, below) we replace `τ_Ω + Δt + Δc` by the maximum over correct
   processes of the first adoption of a promotion of the final leader after `τ_Ω` (finite `P`).

## Repairs proved

- **Lemma 3 repaired** (`Alg5Fixed.lemma_3_fixed`): the leader tags each promotion with a counter, and a process
  adopts a promotion of `p_j` only if `Ω_i = p_j` and the counter exceeds the last one adopted from `p_j`. The
  repaired Algorithm 5 implements ETOB from `Ω` in every environment (finite `P`), for every implementation of
  `UpdatePromote`, without the distinct-broadcasts assumption. It also gives TOB when `Ω` outputs the same leader
  at all correct processes from time `0` (`Alg5Fixed.tob_of_const_leader`), the §5 claim refuted for the original.

## Modelling choices

- **Model** (`Podc/Computability/Distributed/MessagePassing/FailureDetectors/Model.lean`): CHT / Jayanti–Toueg.
  Finite set of processes `P`; one step per time unit (or none); a step receives one message, or nothing (`tick`,
  the paper's `λ` / local time-out), or one input, queries the failure detector at the current time, changes state,
  broadcasts at most one message to every process including itself, and produces outputs. Links reliable, not FIFO.
  Failure patterns are monotone; a crashed process takes no step. Admissible runs: valid receptions at most once,
  every message to a correct process is eventually received, and **every correct process takes infinitely many
  `tick` steps** (the paper requires infinitely many steps; we require infinitely many time-out opportunities, a
  restriction of the adversary that only matters for the positive results and is the intended reading of "on local
  time-out"; the Lemma 3 counterexample satisfies it).
- **Environments.** All positive results are proved for every failure pattern, hence for every environment.
- **Applications.** For algorithms providing EC (Algorithm 4, and the EC-providing transformations) the
  application's proposals are a parameter `inp : P → ℕ → V`; instance `0` is invoked at the first step and instance
  `j+1` in the step returning the response to `j` (the paper's "as soon as"). Since the algorithms are deterministic,
  a run with an adaptive application is a run for the function of the proposals actually made, so nothing is lost.
  We also check that the folded application respects the usage assumption (`Alg4.properUse`).
- **Black boxes** in transformations (the paper's `T_{P→P'}`): invocations are outputs of the transformation,
  responses are adversarial input events; the black box is constrained only by the hypothesis that its history
  satisfies the spec (plus "a response follows an invocation"). This covers every implementation `A_P` of the black
  box, so it is at least as strong as the paper's notion.
  The hypothesis has the assume-guarantee form "usage proper → spec". For EC this is circular if "proper usage" is
  `ProperUse` ("invoke `j+1` exactly at *the* response to `j`"): a black box answering an instance twice makes the
  usage improper and is then unconstrained (`ECtoETOB.etob_of_ec_needs_integrity`: it then outputs a message nobody
  broadcast). Two remedies, both harmless for real implementations (which satisfy EC-Integrity unconditionally):
  `etob_of_ec` additionally assumes `ECIntegrity` of the black box; Algorithms 6/7 use `ProperUseEIC` ("invoke `j+1`
  at the *first* response to `j`"), which the user can guarantee whatever the black box does
  (`Driver.bbHist_properUseEIC`) and which equals `ProperUse` under EC-Integrity (`properUse_iff_properUseEIC`).
- **Theorem 1** is the conjunction of the two transformation theorems (`theorem1`); non-vacuity witnesses
  (admissible runs satisfying all hypotheses) are `ECtoETOB.etob_of_ec_nonvacuous`, `ETOBtoEC.ec_of_etob_nonvacuous`.
  Neither transformation uses the failure detector, so the range `R` is arbitrary.
- **Algorithms 6/7** share a driver (`Driver.lean`) with the application folded in. Algorithm 6 invokes EC instance
  `ℓ+1` at the response to EC instance `ℓ` and ignores responses to instances other than the current one
  (equivalent when the black box satisfies EC). Lemma 5 holds with only `EICCorrect` assumed of the black box and
  gives uniform EC (faulty processes stop, so they cannot disagree forever).
- **EIC impossibility model** (`EICImpossible.lean`): algorithms `EICAlg` with the application folded in; the
  initial state of `p` contains its own future proposals (this only strengthens algorithms); adaptive schedules
  (`RunTools.policyRun`) and a local indistinguishability lemma (`RunTools.sim`).
- **Specs** (`Specs.lean`): "stably delivers `m`" is "from some time on `m ∈ d_i` forever" (the paper's version adds
  `m ∉ d_i(t−1)`; equivalent up to the choice of `t` since `d_i(0) = []`). EC-Validity: "proposed to the same
  instance at an earlier or the same time". Instances are numbered from `0` (paper: EC from `1`, EIC from `0`).
  Agreement properties ("no two processes") are read uniformly, as in the consensus abstraction the paper recalls.
  For EIC both readings are formalized (`EIC` uniform, `EICCorrect` among correct processes); see item 3.
- **Algorithm 5**: `UpdatePromote` is nondeterministic in the paper; we take an arbitrary function `upd` that returns
  an admissible sequence whenever one exists (`UpdValid`); the counterexample holds for every such `upd`, and one
  exists (`exists_updValid`). `UpdateCG(m, C)` adds the node `m` and the edges `(m', m)`; the counterexample uses
  `C(m) = ∅`.

## Not formalized

- Lemma 1 (Ω is necessary for EC: the CHT-style extraction with `k`-tags and Algorithm 3) and therefore the
  necessity half of Theorem 2. An informal check of the argument found no error (a `k`-bivalent vertex has no
  response to instance `k`; descendants of a `k`-bivalent vertex have `k`-tags ⊆ {0,1}, so the CHT gadget argument
  applies; only finitely many `k` are enabled at a given vertex, so "the first `k`-bivalent vertex" stabilizes).
- TOB-Causal-Order of Algorithm 5; the communication-step claims; Sections 6–7.
- Theorem 2 (combination of Lemma 1 and 2) as a single statement, since Lemma 1 is not formalized.
- A positive check that EIC with agreement among correct processes is implementable inside the `EICAlg` model
  (it follows informally from Lemma 2 + Lemma 4).
