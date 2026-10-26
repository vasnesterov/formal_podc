# Byzantine Agreement with Predictions — PODC 2025

Naama Ben-David, Muhammad Ayaz Dzulfikar, Faith Ellen, Seth Gilbert. *Byzantine Agreement with Predictions.*
PODC 2025. DOI [10.1145/3732772.3733518](https://doi.org/10.1145/3732772.3733518). Formalized version: arXiv
[2505.01793](https://arxiv.org/abs/2505.01793) v1; numbering follows it (Theorems 13/14 are the lower bounds).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** Every formal result holds. Both lower bounds are proved as stated:
- `Ω(n + t²)` messages even with fully correct predictions (Theorem 14);
- `min{f+2, t+1, ⌊B/(n−f)⌋+2, ⌊B/(n−t)⌋+1}` rounds (Theorem 13), for unauthenticated algorithms.

The proof of Theorem 13 cites a crash-fault bound that holds for halting times but not for decision
times. We prove the decision-time version by switching to Byzantine faults and proving the cited bound
there. The conditional algorithms (Theorems 5 and 6) and the classification lemmas are correct. The wrapper is verified against the specifications of the cited
sub-protocols. Lemma 23 and Theorem 14's choice of the faulty group have fixable proof gaps. The statement-level slips are minor:
Theorem 6's per-process message bound fails only for `n = 1`, Algorithm 4 has a typo, and the arXiv v1 abstract's
`Ω(n²)` stands for `Ω(n + t²)`.

## Mistakes in the paper

- **Theorem 13: the cited bound only covers halting times (imprecision; the statement is true).**
  - **The step.** The proof turns the predicted algorithm into an algorithm `S'` without predictions on fewer
    processes "that may fail by crashing". It then cites Dolev–Reischuk–Strong [21]: some execution with `f'`
    faults takes `min{f'+2, t'+1}` rounds.
  - **Fine for halting.** For crash faults, `min{f+2, t+1}` bounds the round in which all correct processes
    *stop* (DRS). It also bounds the decision round of *uniform* consensus. The paper says that `A`
    "terminates within `T(f)` rounds" and counts rounds "performed". Read literally as halting time, the
    proof is correct.
  - **Not enough for decisions.** We prove the stronger statement about the round in which the last honest
    process *decides*. `S'` inherits only non-uniform agreement, and non-uniform crash consensus can decide
    in `f+1` rounds. Example: `n = 3`, `t = 1`. Everyone relays all known inputs for `t+1` rounds. A process
    that heard all `n` inputs in round 1 decides their minimum at once; the others decide the minimum they
    know at round `t+1`. Failure-free runs decide at round `1 < min{f+2, t+1} = 2`. This does not contradict
    the classical `t+1` bound, which concerns runs with `f = t`.
  - **Repair.** The same simulation works with Byzantine `S'`. We prove the Byzantine early-deciding bound
    `min{f'+2, t'+1}` ourselves. The usual chain argument gives `f'+1`; the extra round comes from one more
    process that equivocates in the last round, which `f' < t'` allows.
  - **Result.** Theorem 13 holds as stated, for decision times, for at least two values and `t < n − 1`
    (`theorem13`, `earlyDecidingLB_strong`), for *unauthenticated* algorithms (see the model section).
    Reaching *exactly* `f` faults needs padding with Byzantine processes that behave honestly (`padScenario`).
- **Theorem 14: the choice of the faulty group has a gap (statement true).**
  - **The gap.** The proof picks `B ⊆ S₀`, where `S₀` are the processes that "decide 0 for some prediction
    when they receive no messages", and assumes w.l.o.g. `|S₀| ≥ ⌈(n−1)/2⌉`. A process receiving nothing need
    not decide at all, because such a run need not be admissible. So `S₀ ∪ S₁` need not cover the processes.
  - **Fix.** Split the processes by whether their isolated run ever decides `v₁`, and give the honest
    processes the other value. Both cases contradict Agreement in `E_bad` (`t_sq_om`).
  - **Also.** The paper proves Theorem 14 for broadcast and says it "implies the same bounds" for agreement.
    The reduction only transfers the `t²` term. We prove both problems directly, with
    `n + t² ≤ 8·#messages + 1` (`message_lower_bound`, `message_lower_bound_bb`).
- **The abstract and introduction of arXiv v1 claim `Ω(n²)` messages (loose shorthand).** The theorem gives
  `Ω(n + t²)`, which is `Ω(n²)` only when `t = Θ(n)` (the usual convention for Dolev–Reischuk). Read
  literally, `Ω(n²)` is false for small `t`: for `t = 0`, "everyone sends to `p₁`, `p₁` broadcasts the
  minimum" uses `2(n−1)` messages. The PODC abstract states `Ω(n + t²)`.
- **Lemma 23 (committee agreement) has a proof gap (statement true).** "If `p_i` received a chain for `x` in
  the first `k` rounds, it broadcast one" ignores that `p_i` relays only values it *adds*, at most two. The
  fix is to argue from the round in which `x` entered `X_i` (`lemma23`).
- **A remark in the introduction of Section 7 is false (never used).** It says that when `k` is too small,
  "if any honest process decides, then they all decide". Counterexample: `k = 0` and two honest processes
  whose first-ranked process is a different faulty one; one leader sends `v` everywhere, the other stays
  silent. The first process decides `v` at line 12, the second never decides. Algorithm 1 only needs
  termination, so nothing depends on this (not formalized).
- **Minor.**
  - The paper's hypotheses are stronger than needed: Lemma 5 needs only `1 ≤ ℓ ≤ r ≤ n − f`, and Lemma 6's
    hypothesis is unnecessary.
  - Lemma 6 is stated ambiguously; we prove the union version used by Lemma 24.
  - The per-process message bound of Theorem 6 fails for `n = 1`.
  - Asymptotic statements omit `+1`s: `O(min{B/n, f})` should be `O(min{B/n, f} + 1)`, and `log(·)` should be
    `log(· + 2)`.
  - Under-specified tie-breaking and defaults (Algorithm 3 line 14, empty `T_i ∩ L_i`, all-`⊥` outputs).
  - Typos:
    - the position formula for `c[i] = 0`;
    - Algorithm 4 line 4 has `y ∈ L_y` for `y ∈ T_i`;
    - Theorem 6 says "Algorithm 5" for Algorithm 7;
    - Algorithm 7 line 8 has `v_i` for `x_i`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Synchronous, deterministic, static Byzantine faults (at most `t`), complete network.** Signatures, where
  used, are CSLib's unforgeable tokens.
- **Predictions.** Inputs are pairs `(value, prediction)`. A classification prediction is a vector
  `P → Bool` (`true` = predicted honest). `B` counts the wrong bits given to honest processes (`wrongBits`).
  Algorithms must be correct for *all* predictions; validity is strong unanimity on values.
- **Theorem 14.** CSLib's synchronous Byzantine model (`PartialSync` runs with `gst = 0`, any delay bound),
  proved through omission executions. It holds for every prediction type, with or without signatures.
- **Theorem 13.** CSLib's lock-step model (`LockStep`, reliable channels, `Solves`: **unauthenticated**,
  Byzantine processes may send anything). "At least `R` rounds" means that some honest process has no output
  after `R − 1` rounds (decision time, which implies the halting-time reading). Algorithms with signatures,
  the setting of Theorem 6 when `n/3 ≤ t < n/2`, are not covered. For `n ≤ 3t` the hypothesis is unsatisfiable,
  since unauthenticated Byzantine agreement is then impossible.
- **Algorithms 2–7.** CSLib round algorithms, verified against arbitrary synchronous round executions in which
  Byzantine processes send anything (`RoundRun`, `SyncFrom 0`; `AuthValid` with signatures). These compile to
  the time-based model.
  - The conditional algorithms take the classification vectors as input. Algorithm 2 (voting) is analysed as
    a round on its own.
  - In Algorithm 5, processes do not stop early. Outputs are the paper's return values and never change.
- **Algorithm 1 (wrapper).** Verified on abstract phase traces. The outputs of graded consensus, early-stopping
  agreement and the conditional algorithm are arbitrary, subject to their specifications. The cited
  sub-protocols ([14], [37], [32]) are not implemented.

**Main results in Lean** (namespace `BAWithPredictions`).

| Paper | Lean | File |
|---|---|---|
| Theorem 14 (= Thm 1), agreement / broadcast / classification | `message_lower_bound`, `message_lower_bound_bb`, `message_lower_bound_classification` | `MessageLowerBound.lean` |
| Theorem 13 (= Thm 4) | `theorem13` | `RoundLowerBoundStrong.lean` |
| Cited [21] (Byzantine early deciding `min{f+2,t+1}`) | `earlyDecidingLB_strong`; `f+1` part: `earlyDecidingLB_weak` | `RoundLowerBoundStrong.lean`, `RoundLowerBoundChain.lean` |
| Simulation `S'` of Theorem 13; padding | `simProtocol`, `solves_simProtocol`, `roundLowerBoundWith`, `padScenario` | `RoundLowerBound.lean` (`padScenario`: `Podc/…/LockStep/Basic.lean`) |
| Algorithm 2, Observations 1–2, Lemma 1 (`k_A(⌈n/2⌉−f) ≤ B`) | `classify`, `obs12`, `card_mis_mul_le` | `Classification.lean` |
| Lemmas 2–6, Corollary 1, Lemmas 15+19 | `pos_mem_Icc`, `pos_gt_of_false`, `lemma4`, `lemma5`, `lemma6`, `corollary1`, `exists_clean_block` | `Classification.lean` |
| Algorithms 3–4, Lemmas 7–14 | `Unauth.gcB/gcOut/conc`, `Unauth.lemma7` … `Unauth.lemma14` | `UnauthPhase.lean` |
| Algorithm 5, Theorem 5 (agreement, unanimity, `5(2k+1)` rounds, `5n((2k+1)(3k+1)+k)` messages) | `Unauth.alg5`, `Unauth.theorem5_agreement`, `theorem5_strongUnanimity`, `theorem5_termination`, `theorem5_msgs` | `UnauthBA.lean` |
| Algorithm 6, Lemmas 21–23, Observation 3 | `AuthBA.lemma21`, `lemma22_honest/faulty`, `lemma23`, `observation3` | `AuthBB.lean`, `AuthMsgs.lean` |
| Algorithm 7, Lemmas 24–27, Theorem 6 (`k+3` rounds, `O(nk²)` messages) | `AuthBA.alg`, `lemma24_*`, `lemma26`, `lemma27`, `theorem6`, `theorem6_messages` | `AuthAlg.lean`, `AuthBA.lean`, `AuthMsgs.lean` |
| Lemmas 28–32 (wrapper), Lemma 33 (rounds), round part of Theorems 11/12 | `Wrapper.Trace.lemma28`, `lemma29`, `lemma30_32`, `lemma31`, `agreement`, `rounds_le`, `theorem11_rounds` | `Wrapper.lean` |

**Not formalized.**
- The cited graded-consensus and early-stopping protocols, and the formal composition of the sub-protocols
  into one round algorithm. Instead, Lemmas 28–33 are verified against the sub-protocols' specifications.
- The final asymptotic statements of Theorems 11/12, which are only assembled in prose.
- The crash-model example above (decision in `f+1` rounds); it concerns the citation, not the theorem.
- Theorem 13 for authenticated algorithms.

**Trust.**
- No `sorry`. All listed theorems use only `propext`, `Classical.choice` and `Quot.sound`.
- Non-vacuity:
  - BA with predictions is solvable for `n > 3t` without signatures and for `n > 2t` with them
    (`strongUnanimity_solvableSync`, `strongUnanimity_solvableAuthSync`), so Theorem 14's hypothesis is
    satisfiable.
  - Synchronous executions exist and the hypotheses of Theorems 5 and 6 are satisfiable
    (`Unauth.theorem5_hyps_of_correct`, `AuthBA.exists_run`, `AuthBA.hypotheses_satisfiable`).
- Models come from CSLib: `Byzantine/PartialSync` (incl. `Omission`, `Rounds`, `RoundAuth`) and
  `Byzantine/LockStep`.
- Shared library: `roundMsgs`/`procMsgs` and `syncRun` are `RoundRun.msgsUpTo`/`procMsgs` and `RoundRun.sync`
  (`Cslib/Computability/Distributed/Byzantine/PartialSync/RoundAuth.lean`); the isolated and fault-free omission executions of Theorem 14 are
  `OmExec.solo`/`OmExec.ff` (`Cslib/Computability/Distributed/Byzantine/PartialSync/Omission.lean`); the non-vacuity reduction uses the containment
  condition of `Cslib/Computability/Distributed/Byzantine/PartialSync/Containment.lean`; `cnt`/`plur`/`thr` are `Finset.countEq`/`plurality`/`threshold?`
  (`Cslib/Foundations/Data/Finset/Quorum.lean`).
- Shared code (CSLib): `padScenario`, `decides_iff_of_hist` (`Cslib/Computability/Distributed/Byzantine/LockStep/Basic.lean`),
  `Finset.pluralityMin` (smallest most frequent value, `Cslib/Foundations/Data/Finset/Quorum.lean`); `hist_eq_take` is
  CSLib's `take_hist`. CSLib candidates (marked in the files): the subtype simulation, the hybrid (equivocation) lemma.
