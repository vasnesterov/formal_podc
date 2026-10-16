# Differences between the formalization and the paper

Paper: Vaidya, Garg, *Byzantine Vector Consensus in Complete Graphs*, PODC 2013, arXiv 1302.2543v1.

## Errors and gaps in the paper

1. **Theorem 6, synchronous necessity (`n ≥ (d+2)f+1`) — false as stated (under-specified
   definition).** The restricted synchronous structure allows an arbitrary update function of
   the old state and the received vectors. A state in `ℝ^d` can injectively encode `(ℝ^d)^n`.
   For `n = 4`, `d = 2`, `f = 1` (`(d+2)f+1 = 5 > 4`), the two-round algorithm "store the
   received inputs; take the OM(1) majority of the relayed values for each process, output a point
   of `Γ`" is restricted and solves exact BVC. Lean: `theorem_6_sync_necessity_false`
   (`RestrictedSync.lean`). The intended class, probably with valid (hull-preserving) intermediate
   states, is not defined in the paper and is not formalized. The claim is likely true for it.
   - **Round number.** `RestrictedAlg.upd` receives the round number `t`, which the paper's text
     does not mention. This is harmless: in synchrony processes know `t`, and the paper's own
     algorithm stops after a fixed number of rounds.
   - **Round-independent counterexample.** `theorem_6_sync_necessity_false'` uses an update that
     ignores `t`. Inputs lie in the box `[0,1]²` (Section 3.2's known bounds with `ν = 0`,
     `U = 1`), and encodings have first coordinate `> 1`. So the own state tells round 1 from
     round 2.
2. **Theorem 6, asynchronous case — under-specified algorithm; necessity unproved.** "Step 2
   analogous to Section 3.2" with subsets of size `n − f` leaves `Z_i = {one point}`, since
   `|B_i| = n − f`. The paper's common-point argument fails. We use subsets of size `n − 3f` (any
   `s` with `(d+1)f < s ≤ n − 3f` works, `RoundExec.correct_of_valid`) and prove sufficiency for
   `n ≥ (d+4)f+1` (`theorem_6_async`). Necessity: no proof in the paper; not formalized. The
   objection of item 1 applies.
3. **Theorem 4 — minor presentational gap, true statement.** The scenario "`p_j` faulty,
   `p_{d+2}` slow but correct" yields the hull of `X_i^j ∪ {x_{d+2}}`, not `H(X_i^j)`. The paper's
   remark that `p_i` has no information about `x_{d+2}` already implies the fix: choose `x_{d+2}`
   per scenario inside `H(X_i^j)`. Only the later sentence fixing `x_{d+2} = 0` for all scenarios
   is inconsistent with it: for `j = d+1` the intersection would then contain the segment
   `[0, 4ε e_i]`. Our proof gives the slow group the input of the deciding process in each
   scenario.
4. **Theorems 1 and 4 for `n = 1`, `d = 0`, narrow inputs — false only in degenerate cases.**
   - Both need `n ≥ 2`. The paper assumes `n > 1`, and for `n = 1` BVC is trivially solvable
     (`ownInput_solves_of_card_one`).
   - Both need `d ≥ 1`. The paper assumes `d > 0`.
   - Theorem 4 needs input domains of width `> ε`. With the bounds `[ν, U]` of Section 3.2 and
     `U − ν ≤ ε`, deciding the own input works for every `n` (`ownInput_solves_of_narrow`). Our
     `theorem_4` assumes the domain contains `a` and `a + c e_i` with `c > ε`.
5. **"`n ≤ d+1` (resp. `d+2`) is also not sufficient" and the simulation for `f > 1` — proof gaps,
   true statements.** For `n = 2` a different argument is needed than the one given for `n = d+1`.
   The simulation is only sketched. We replace both by a direct partition of the processes into
   `d+1` (resp. `d+2`) groups of size `≤ f` by index residue (`card_mod_class_le`), with group inputs
   `a`, `a + c e_1`, …, `a + c e_d` (`lbPoint`). This covers every `n ≥ 2` at once.
6. **Theorem 1, `3f+1` part.** The citation of scalar consensus is fine. We reduce to CSLib's
   Fischer–Lynch–Merritt theorem for weak validity (diagonal inputs, `weak_of_bvc`), which needs
   `n ≥ 3`. The case `n = 2` follows from the `(d+1)f+1` part.
7. **Number of rounds in Step 3.** `1 + ⌈log_{1/(1−γ)}((U−ν)/ε)⌉` is undefined for `U = ν` and
   can be `≤ 0`. We use `1 + ⌈·⌉₊` (Lean's `Real.logb` and `Nat.ceil`), which works in all cases
   (`rounds_spec`).
8. **Typos.** Section 4 cites "the proof of Theorem 4" for the correctness of the restricted
   algorithms; it should be Theorem 5. Section 4's "relies crucially on
   `|B_i[t] ∩ B_j[t]| ≥ (d+1)f+1`" really needs a common sub-multiset of the size used in Step 2.

## Modelling choices and changed proofs

- **Execution model.** CSLib `Cslib.Byzantine.PartialSync`: deterministic state machines,
  complete network, Byzantine processes may send arbitrary messages that differ per receiver,
  sender identities are authentic, and there are no signatures.
  - Synchrony is `gst = 0` (any `δ`); with `δ = 0` it is lock-step rounds.
  - The paper's FIFO assumption is irrelevant to all formalized results.
  - Correct processes have synchronized clocks. This only strengthens the lower bounds.
- **Asynchrony.** Theorem 4 is proved in the partially synchronous model (all runs with finite
  `gst`). Every such run is an asynchronous run, and algorithms there may use clocks, so the
  result implies the asynchronous lower bound.
- **Multisets** are indexed families `y : ι → ℝ^d` restricted to a finite index set `C`
  (`GammaOn f C y`), matching Appendix B.
- **`Γ(Y)` with `|T| = |Y| − f`** is used literally. `GammaOn_subset_convexHull` gives the hull
  bound for every sub-multiset with `≥ |Y| − f` elements.
- **Lemma 1** is proved twice:
  - via Helly's theorem (Mathlib `Convex.helly_theorem'`) plus counting: any `d+1` of the
    `(|Y|−f)`-subsets share an index because `(d+1)f < |Y|`;
  - via Tverberg's theorem, as in the paper (`GammaOn_nonempty_of_tverberg`).
- **Tverberg's theorem** (Theorem 2) is proved by Sarkaria's proof: colorful Carathéodory by the
  minimal-norm argument, then the lifting written in coordinates. The statement covers multisets
  with `≥ (d+1)(r−1)+1` points, `r ≥ 1` (the paper's `f = r − 1 ≥ 1`), and asserts nonempty parts.
- **Exact BVC Step 1.** The paper performs `n·d` scalar Byzantine broadcasts. We use CSLib's
  interactive consistency protocol for `n > 3t` (exchange + vector consensus + majority). Its
  specification (common vector, correct entries = correct inputs) is exactly what Step 1 provides.
  Step 2's deterministic choice of a point of `Γ(S)` is `gammaPt` (classical choice); the LP
  implementation is not formalized.
- **Validity** in all specifications: decision in `convexHull ℝ {inputs of correct processes}`.
- **ε-agreement**: `|v_l − w_l| ≤ ε` for every coordinate in the specifications, which makes the
  lower bounds stronger. The algorithms achieve `< ε`.
- **Theorem 5 / AAD.** Component #1 of AAD is a black box with Properties 1–3, as in the paper.
  - Properties 2 and 3 are built into `RoundExec` (one value per sender; correct senders carry
    their state).
  - Property 1 and `|B_i| ≥ n − f` are the hypotheses `RoundExec.Valid f (n − f)`.
  - The sets `B` and the Byzantine values are arbitrary functions of round, receiver and sender.
    This covers every adaptive adversary, because the theorem quantifies over all of them.
  - The termination sub-protocol of AAD (Component #3) is replaced, as in the paper, by the fixed
    round count with known bounds `[ν, U]`.
- **Contraction proof (12).** We do not track weights. A point `z_ij ∈ Z_i ∩ Z_j` is a convex
  combination of the round-`r` correct states, so some state `u` has weight `≥ 1/n`
  (`exists_heavy`). Averaging (`avg_le`, `le_avg`) gives
  `v_i ≤ b − γ (b − u)` and `v_j ≥ a + γ (u − a)` with `γ = 1/(n·C(n, s))`, the paper's (11) for
  `s = n − f`. This is the paper's Appendix E argument.
- **Section 4 synchronous algorithm.**
  - In the abstract round model it is the instance `B_i = P`, `s = n − f` (`theorem_6_sync`).
  - As a restricted algorithm (`iterAlg`) it is `theorem_6_sync_restricted`.
  - Missing messages are "some default value", i.e. covered by arbitrary Byzantine values.
- **Not formalized:**
  - AAD Component #1 (reliable broadcast + witness technique);
  - Appendix F (witness-based optimization, `γ = 1/n²`);
  - the LP for Step 2 and the complexity remarks;
  - the necessity parts of Theorem 6 under any repaired definition of the restricted classes.
