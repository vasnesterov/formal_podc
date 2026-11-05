# Differences between the formalization and the paper

Paper: M. Raynal, J. Stainer, *Synchrony Weakened by Message Adversaries vs Asynchrony Restricted by
Failure Detectors*, PODC 2013. Formalized from the full version: IRISA research report PI 2002
(*Round-based Synchrony Weakened by Message Adversaries vs Asynchrony Enriched with Failure Detectors*,
hal-00787978v2, February 2013), whose numbering we follow.

## Modelling choices

- **Synchronous model `SMP_n[adv : AD]`** (`Model.lean`). CSLib's heard-of model
  (`Cslib.HeardOf.conf`): a communication pattern `p : ℕ → Graph P` (`p t` = graph `G^{t+1}`, edge
  `j → i` = the message of `p_j` to `p_i` is not suppressed, self-loops implicit, as the paper assumes in
  Section 2.2); an adversary is the *set of patterns* it may produce (non-oblivious, so eventual
  properties such as SOURCE are expressible); several properties combine by intersection.
- **Full-information deterministic algorithms.** A process broadcasts its whole state and applies a
  transition function to the states it receives. This is no restriction for solvability (a process that
  receives `p_j`'s state can compute the message `p_j` would have sent it). Outputs are write-once: the
  output of a process is the first value of its output function (`Alg.output`).
- **Tasks** (`Task`): valid input vectors and `Δ`; computed outputs (with `none` = no output) are valid if
  they extend to some `O ∈ Δ(I)` (`Task.Valid`) — exactly Section 2.4.
- **Two solvability notions.**
  - `Alg.Solves` / `Solvable`: every process outputs. This is the paper's literal definition: the
    processes of `SMP_n` are "reliable" (Section 1, 2.1) and Section 2.4 allows a missing output only
    for a process that "has crashed".
  - `Alg.SolvesSC` / `SolvableSC`: only strongly correct processes must output. The paper never states
    this, but the proofs of Lemmas 2, 4 and 6 treat weakly correct processes as crashed. We use it to
    show that no single reading makes all six lemmas go through (see README).
- **Strongly correct processes** (`SC`): defined literally as in Section 2.2 (the unique strongly
  connected component of `⇝∞` without input edge, `∅` if it is not unique). `⇝≥r` is a CSLib journey
  starting at round `r` (`ReachFrom`); since journeys may wait, "starting at a round `≥ r`" is the same.
- **PAIRS.** The pair schedule is a parameter `pair : ℕ → Sym2 P` (`pair t` = pair of round `t + 1`, the
  paper's `σ(r mod C(n,2))`); the paper's schedule is an instance.
- **Asynchronous models.** `AMP_{n,n-1}[fd : D]` uses the staged CHT model
  (`Podc/Computability/Distributed/MessagePassing/FailureDetectors/Model.lean`): broadcast steps,
  reliable non-FIFO links, crash failures, at least one correct process. Point-to-point messages are
  encoded by addressing (the receiver ignores messages not meant for it).
  `ARW_{n,n-1}[fd : Ω]` (`ArwOmega.lean`, paper-local): SWMR atomic registers (unbounded number, one per
  round), steps write / read / query Ω / decide, an infinite schedule (correct = steps infinitely often),
  Ω history arbitrary until it stabilizes on a correct leader (also arbitrary for faulty processes).
  Querying Ω is a separate atomic step. Validity is required at all times, which is equivalent to
  validity of the final decisions because decisions are irrevocable. The algorithm for `Tcons`
  (`ArwOmegaCons.lean`) is Ω-led commit-adopt rounds; it also writes a register `E[r]` that only the
  proof reads.
- `(Σ, Ω)` in `AMP` is the pair of histories (`SigmaOmegaFD`); an algorithm for `Σ` is run unchanged by
  ignoring the second component (`SolvableAMP.of_map`).

## Statement-level issues (decided by `verdicts.md`)

- **Theorem 4 / Lemma 6 false** (`lemma6_false`, `theorem4_false`), and hence **Theorem 5 false**
  (`theorem5_false`): `Tseen` is solvable in `AMP_{3,2}[Σ]` (and `AMP_{3,2}[Σ, Ω]`) but not in
  `SMP_3[QUORUM]` (not even in `SMP_3[SOURCE, QUORUM]`). Headline (the abstract presents the SOURCE and
  QUORUM characterizations as the contributions) → 🚨 (R5). The counterexample uses the paper's own
  definitions: `SMP_n` processes are reliable and Section 2.4 lets only crashed processes lack an output.
  *Borderline call (R4/R6).* One might argue that the intended notion of solving in `SMP_n` is "only
  strongly correct processes must output" (the proofs of Lemmas 2, 4, 6 behave as if it were). The paper
  never says so, and under that reading Lemmas 1, 3 and 5 lose their proofs. Figure 4 makes every non-leader
  weakly correct by design; Figures 2 and 6 can make correct asynchronous processes weakly correct (e.g. Σ
  constantly `{ℓ}`). The theorems would then be unestablished (still ❌ by R5) rather than false. We keep 🚨
  because it is the literal reading and no reading makes all six lemmas go through. (R4 does not excuse an
  assumption the paper's own proofs contradict.)
  *Legitimacy of the tasks.* Section 2.4 allows any set of input vectors and any relation `Δ`, with
  partial outputs valid iff they extend to some `O ∈ Δ(I)` (exactly `Task.Valid`); it imposes no
  colorlessness or other restriction. `Tseen` and `Tcons` are such tasks (inputs: all vectors; `p₃`'s
  output unconstrained). `Tseen` is a standard wait-free read/write task (solvable in
  `SMP_3[adv : TOUR]` in one round), so the paper's equivalences cannot implicitly exclude it.
  Non-vacuity of the asynchronous side: `tseen_amp_sigma_nonvacuous` (admissible runs with a valid `Σ`
  history exist); ARW executions exist trivially (any schedule with a constant correct Ω leader).
- **Lemma 2 / Theorem 2 false** (`lemma2_false`, built from `tcons_not_solvable` and
  `tcons_solvable_arw_omega`), and therefore **Corollary 1 false** (Theorem 6 holds, so Corollary 1 is
  equivalent to Theorem 2). Same reading and same borderline remark as above. Headline → 🚨.
- **Figure 1 / Conclusion**: "SMP_n[adv: QUORUM] is stronger than SMP_n[adv: TOUR]" (explicit claim in
  the Conclusion, arrow in Figure 1), and the arrow SMP[SOURCE, QUORUM] → SMP[SOURCE, TOUR], are false
  (`not_quorum_stronger_than_tour`, `not_source_quorum_stronger_than_source_tour`). Purely synchronous;
  not a headline → ❌.
- **Theorem 3**: unestablished (⚠️). Lemma 4's proof fails under the literal reading, and Lemma 3's under
  the "strongly correct only" reading. No counterexample known; `Tseen` and `Tcons` are not solvable in
  `AMP[Ω]` (partition argument), so ours do not apply.
- **FAIR** in Theorem 3 and Lemma 6 is undefined; read as absent (R3, ⚠️; see Typos below).
- **Theorem 1**: true (`theorem1`), also under the weak reading on the synchronous side
  (`solvableSC_inf_iff_local`). The asynchronous side is modelled as `AMP_{n,n-1}[fd: ∅]` (at least one
  correct process).
- **Theorem 6**: true (`theorem6`) for `n ≥ 2`; for `n = 1` the block length `2n − 3` is meaningless (R2,
  degenerate). Stated with the strong solvability notion. The PAIRS schedule is the paper's
  `σ(r mod C(n,2))` (`paperPair`); the general statement only needs every block of `C` rounds to cover all
  pairs (`Covers`).
- **Section 2.2 claims**: `↔∞` is an equivalence (`InfReach.refl/trans`); under TOUR there is a unique set
  of strongly correct processes (`SC_nonempty_of_tour`); `SC` = the processes whose messages always
  eventually reach everybody (`SC_eq`); sources are strongly correct (`mem_SC_of_source`); the
  intersection part of QUORUM implies `SC ≠ ∅` (`SC_nonempty_of_inter`); facts (A) and (B) in the proof of
  Lemma 6 (`exists_SC_hears_of_quorum`, `eventually_no_edge_into_SC`). All true.

## Proof gaps

- Lemmas 2, 4 and 6: the step "weakly correct simulators simulate faulty processes" does not fit the
  paper's definition of solving in `SMP_n` (see above). For Lemmas 2 and 6 the statements are false; for
  Lemma 4 the statement is open.
- Lemmas 1, 3 and 5: fine under the literal reading, not formalized. Under the other reading they fail as
  explained above.
- Theorem 6, Part 2: the inequality chain `|K_i ∩ K_j| ≥ 2n−1−n ≥ n−1 ⇒ {i,j} ∩ K_i ∩ K_j ≠ ∅` omits
  that `K_i ∩ K_j ⊆ Π ∖ {i,j}` when neither knows the other's message, and "2n−1−n ≥ n−1" is an
  equality. The block simulation of Part 3 uses flooding in the Lean proof (the paper sends directly in
  the pair's round; both work).
- Theorem 1: "it is a purely local task" is argued informally. The Lean proof uses the silent pattern
  (synchronous side) and, on the asynchronous side, an explicit admissible run in which every process
  first runs alone until it decides (`amp_solvable_iff_local`).

## Typos and slips

- Theorem 3 is stated for `SMP_n[adv : SOURCE, FAIR]` and Lemma 6 for `SMP_n[adv : FAIR, QUORUM]`;
  FAIR is never defined. The section titles, Figure 1, the introduction, the conclusion, Lemmas 3–4
  and Theorem 4 all use SOURCE (resp. QUORUM) alone; we read FAIR as a leftover of an earlier version
  (rule R3). This changes nothing below: our counterexamples work for the adversaries without FAIR,
  and for the statements with FAIR they would only need FAIR to be satisfied by our patterns, which we
  cannot check for an undefined property.
- Figures 4 and 6, line 5: `r ← r_i + 1` should be `r_i ← r_i + 1`.
- Figure 7, line 9: `msgs_to_send_i ∈ ⋂ view_j` should be `⊆`.
- Figure 3, lines 14 and Lemma 2 Part 1: `seq_nq_i` for `seq_nb_i`; Lemma 2 Part 4 writes `(r, s)` and
  `(r, j)` for the pairs `(s, r)`, `(j, r)` of `missed_i`.
- Proof of Lemma 4: the paragraph "Correct and faulty (simulated) processes" ends with the unfinished
  sentence "It follows that".
- Appendix A.3, Part 2: the paragraph heading "The source of SMP_n[adv : SOURCE_pairs, PAIRS] simulates a
  source of SMP_n[adv : SOURCE, TOUR]" should read SOURCE_tp, TP.
- QUORUM (Section 5.1): the liveness conjunct `SC ≠ ∅` is implied by the intersection conjunct
  (`SC_nonempty_of_inter`, `quorum_iff`), as the proof of Lemma 5 in fact shows. Harmless redundancy.
