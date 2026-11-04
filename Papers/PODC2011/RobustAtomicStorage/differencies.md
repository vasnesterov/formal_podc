# Differences between the formalization and the paper

Paper: D. Dobre, R. Guerraoui, M. Majuntke, N. Suri, M. Vukolić. *The Complexity of Robust Atomic
Storage.* PODC 2011 (EPFL accepted version, 10 pages, proofs included).

## Model (`Model.lean`)

1. **Round model.** The paper's Definition 1 lets the client end a round after "a sufficient number of
   replies", subject to (a)/(b): a round may end without the reply of `s_i` only if `s_i` is faulty or
   some indistinguishable partial run has `s_i` faulty; together with wait-freedom this means the
   adversary can force a round to end exactly when the missing objects could *all* be faulty. We
   formalize the round model of [1] (Abraham et al.; the paper says "this is equivalent to the round
   model of [1]", right after the FIFO rule for pending invocations): a round may end as soon as
   `S − t` objects replied, and the *scheduler* decides when. This drops condition (a)/(b), so the
   Lean adversary may end rounds that the paper's adversary may not (e.g. skip correct objects while
   malicious responders forge), `Proto.Atomic` quantifies over more runs, and the Lean theorems are
   formally *weaker* than the paper's (they cover a smaller class of protocols: those that cannot
   wait for more than `S − t` replies after detecting a faulty reply). The paper's arguments that
   the terminations in its runs are legal ("`rd_j` cannot wait for additional replies", via `Δpr`)
   are therefore not checked in Lean. The reviewer checked them on the symbolic Python replay of the
   runs (outside the repository): every terminated round of
   every run of Proposition 1 (`k ≤ 5`) and Lemma 1 (`k ≤ 6` with the paper's sizes; `k ≤ 5`,
   `t_k ≤ t ≤ 3t_k + 3` with the repaired sizes of `exists_fits`) has a witness run with the same
   client view in which the skipped objects together with all objects that forged so far are at
   most `t` objects. So the constructions are legal in the paper's model, jointly (stronger than
   the per-object reading of (b)). Rule: modelling choice, not a statement issue.
2. **Fixed number of rounds.** Writes take exactly `K` rounds and reads exactly `N` rounds in every
   run (the paper: "completes in `N` rounds", i.e. at most `N`, possibly adaptively). Adaptive round
   counts are not representable in `Proto`. For writes, the statements are proved for every fixed
   `K` up to the bound. Proposition 1 is proved only for `N = 2` (not `N = 1` or reads taking one or
   two rounds depending on the run), and Lemma 1/2 and Proposition 2 only for `N = 3`. A protocol
   whose operations take *at most* `N` rounds can be padded to exactly `N` rounds with no-op rounds
   (objects ignore no-op messages; delaying responses only removes precedence constraints, so
   atomicity is preserved); this padding is not formalized. Rule: modelling choice; the formal
   statements are weaker than the paper's "at most" only by this standard reduction.
3. **Deterministic protocols**, objects described by their logs (every deterministic object
   automaton is of this form). The paper uses I/O automata and implicitly treats them as
   deterministic ("forge their state to σ").
4. **One-shot clients**: each client invokes at most one operation, and the writer writes a value
   `v ≠ ⊥`. Clients receive no messages from other clients (the paper restricts to such runs
   "without loss of generality"). Restricting the runs only *weakens* the hypothesis
   `Proto.Atomic` and so *strengthens* the impossibility results.
5. **Malicious objects** act by overwriting their state (`forge`) and otherwise behave correctly.
   This is exactly the Byzantine behaviour used in the proofs, and a special case of arbitrary
   behaviour (again a restriction of runs). A reply is received in the same step in which the
   object processes the message (no separate "in transit reply"); replies in transit at the end of
   a partial run of the paper are modelled by the client never using them (it crashes / is slow).
6. **Atomicity** is the paper's definition (properties (1)–(4) of §2.2), specialised to at most one
   write (enough in a one-shot model with one writer).
7. **Wait-freedom** is built into the round model (every round can terminate once `S − t` objects
   replied), so it is not a hypothesis.

## Proposition 1 (`ReadLB.lean`, `Main.proposition1`)

8. **More general than stated in the proof**: the paper's proof uses blocks `B₁, B₂, B₃` of size
   exactly `t ≥ 1` and `1 ≤ |B₄| ≤ t` (so `3t + 1 ≤ S ≤ 4t`) and, for `S ≤ 3t`, implicitly the
   resilience bound `S ≥ 3t + 1` of [23]. We prove the statement for all `S ≤ 4t` (four blocks of
   at most `t` objects, possibly empty) and every number `K ≥ 1` of write rounds, with no appeal to
   [23].
9. **Reconstruction of the runs.** The general step of the paper (`pr_{4i+(j mod 4)}`, states
   `σ^r_{4i+(j mod 4)−3}` and `σ_{((j mod 4)/j)(k−i−1)}`, footnote 3) is index-heavy and partly
   garbled; we index read instances by `n = 1, …, 4k − 1` (reader `(n−1) mod 4`) and give closed
   forms of all object states (`ReadLB.L`). The base runs `pr₁, …, pr₃` are uniform instances of the
   general step once labels of non-existent instances are dropped. Where the text and Fig. 1
   differ in notation we follow Fig. 1 (validated by a symbolic replay of all runs).
10. **Only the runs `pr_n` (and the final no-write run) are built**: the paper's `Δpr_n` serve to
    compare views; in our proof they are prefixes of `pr_{n+1}`, and indistinguishability is the
    canonicity of every round's transcript (`Sim.lean`).

## Lemma 1 (`WriteLB.lean`, `Main.lemma1`, `Main.write_lb_general`)

11. **Block form.** We prove the construction for every block assignment satisfying only *upper*
    bounds (`Blocks.Fits`: every set malicious in some run or skipped by some terminated round has
    at most `t` objects); the paper's sizes (`|B_l| = t_l − t_{l−2}`, …, equations (1)–(3)) are an
    instance (`Arith.exists_fits_paper`, `Arith.paper_sizes`).
12. **`k = 1`.** The paper proves `k ≥ 2` and cites [1] for `k = 1`; the same construction covers
    `k = 1` and we prove all `k ≥ 1`.
13. **Read `rd_k`.** As in the paper, its third round skips `M_{k−2} ∪ P_{k+1}` (not
    `M_{k−2} ∪ 𝒞_{k+1}` as for the other reads).
14. **Typo**: "We refer to the state of `{B_l, C_l}` at the end of `Δpr_1` as `σ^r_l`" should be
    `Δpr_l`. The proof assumes "at most `3t_k + 1` objects" but fixes the block sizes summing to
    exactly `3t_k + 1`; fewer objects are covered by our upper-bound formulation (11).
15. **Only the runs `pr_l^C` (`l = 1..k`) and `Δpr_k` are built** (see 10).

## Lemma 2 (`Main.lemma2`)

16. **Proof gap (🛠️, R1: claim inside a proof).** "By Lemma 1 … Observe that this is valid even with
    `R ≥ k` readers and `t ≥ t_k` faults": Lemma 1 is about `3t_k + 1` objects and `t_k` faults, and
    going to `S = 3t + 1` objects and `t > t_k` faults needs larger blocks; the paper's scaling
    argument (Proposition 2) only handles `t_k ∣ t`. Repaired by `Arith.exists_fits` (extra objects
    in the blocks `B_k`, `C_k`, `B_{k+1}`, which never lie in a common constrained set).
17. **Direction of "solving for k".** The proof needs `k ≤ ⌊log ⌈(3t+1)/2⌉⌋ ⇒ t ≥ t_k` but derives
    the converse from the closed form; both directions hold (`Arith.tseq_le_iff`).
18. **Degenerate cases (R2).** For `R = 0` (no reader) or `t = 0` the bound
    `min {R, ⌊log ⌈(3t+1)/2⌉⌋}` is `0` and the statement is about 0-round writes; our model has no
    0-round operations, so we state Lemma 2 for `1 ≤ K ≤ min {…}`. (With `R = 0` the statement would
    be false — atomicity is vacuous without reads — but the paper's "multi-reader" excludes it.)
19. We prove the bound for **every** write-round number `K` with `1 ≤ K ≤ min {R, ⌊log₂ ⌈(3t+1)/2⌉⌋}`
    ("completes in" read as "at most").

## Proposition 2 (`Main.proposition2`)

20. **Proof gap (🛠️, R1).** "By carefully choosing `c = t/t_k`, we obtain a lower bound proof for
    `S' = 3t + ⌊t/t_k⌋` and `t` faults": multiplying every block by `c` requires an integer `c`, i.e.
    `t_k ∣ t`; for other `t` it yields only `3c t_k + c < 3t + c` objects. Statement true: we add
    `d = t − c·t_k` objects to each of `B_k`, `C_k`, `B_{k+1}` (`Arith.exists_fits`; total `3t + c`),
    and use that the construction only needs upper bounds. Smaller `S` is handled by shrinking blocks.
21. `⌊log ⌈(3t_k + 1)/2⌉⌋ = k` (`Arith.log_tseq`), so the bound is `min {R, k}`; for `K < k` we use
    `t / t_k ≤ t / t_K`.

## Not formalized

22. The upper-bound discussion of §5 (2-round-write / 4-round-read implementations via regular
    storage of [15] and the regular-to-atomic transformations of [4, 20]) and the secret-value model
    of [8]: they rely on other papers' algorithms.
23. The resilience bound `S ≥ 3t + 1` of [23] is not needed (see 8, 20).
