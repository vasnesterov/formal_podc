# Differences between the formalization and the paper

Paper: T. Nowak, U. Schmid, K. Winkler, *Topological Characterization of Consensus under General
Message Adversaries*, PODC 2019. **The PODC'19 paper is arXiv:1905.09590 v1** (23 May 2019). Its
setting is synchronous, fault-free dynamic networks under an arbitrary message adversary, with
process-time graphs and the minimum topology. The local `paper.pdf` is v3 (2024), *Topological
Characterization of Consensus in Distributed Systems*. v3 generalizes v1 to a generic model with
benign faults. We formalized both. The PODC verdict concerns v1. Errors that appear only in v3 are
listed separately below.

## v1 (PODC'19): false statements

A. **Corollary 5.6, Theorem 5.11 and Theorem 6.7, "if" directions** (`V1Cex.v1_theorem_5_11_false`).
   - *The claims.*
     - Cor 5.6: consensus is solvable iff no connected component contains a `v`-valent and a
       `w`-valent execution.
     - Thm 5.11: consensus is solvable iff all connected components are broadcastable.
     - Thm 6.7: for non-compact adversaries, consensus is solvable iff every component of a valent
       execution is broadcastable.
   - *Counterexample.* Three processes. `σ_∞` has `1→0`, `1→2` in every round. `π_k` has no edges
     before round `k+1`, `2→0` in round `k+1`, and then `0→1`, `0→2` forever. The adversary is
     `MA = {π_k} ∪ {σ_∞}`; it is not limit-closed, since the edgeless pattern is a limit of the
     `π_k`.
   - *Every component is broadcastable, with at most one valence.*
     - For each `(a, c, k)`, the set `S_{a,c,k} = {((a,y,c), π_k)}` is clopen (`isClopen_S`): the
       `(k+2)`-round views determine `k`, `x₀`, `x₂`. It is broadcast by 0, and its valent
       executions all have value `a`.
     - The component of `(x, σ_∞)` is contained in `{(y, σ_∞) | y₁ = x₁}` (`comp_subset_K`). The
       proof uses preconnectedness with the open sets `W_c` ("`σ_∞` ⇒ `x₁ = c`"). This set is
       broadcast by 1 and has valence `x₁`.
   - *Consensus is impossible* (`not_solvable`, via `DN.dn_solvable_iff`). Process 0 never hears of
     process 1 in `π_k`, so `((1,0,1), π_k)` gets the label of `((1,1,1), π_k)`, which is 1. But for
     `k ≥ T`, process 1 has the same `T`-round view in `((1,0,1), π_k)` as in `((0,0,0), σ_∞)`,
     which has label 0.
   - *The failing step.* The meta-procedure (and Theorem 5.11 "⇐") puts the components of valent
     executions into `PS(v)` and assumes that these unions are open. With infinitely many
     components this fails: the components `{(y, σ_∞) | y₁ = c}` are not open. v3 adds condition
     (ii) (clopen strong broadcaster decision sets) to its Theorem 7.9 and restricts the
     meta-procedure to finitely many components.
B. **Corollary 6.1**: "for a compact message adversary [where consensus is solvable] there are only
   finitely many connected components". This is false (`CanonicalCex.v1_corollary_6_1_false`).
   - *Counterexample.* The limit-closed adversary `MAex = {σ_n} ∪ {σ_∞}` on two processes, with
     `σ_∞ = (1→0)^ω` and `σ_n` having `0↔1` in round `n+1`.
   - Consensus is solvable there, yet each `{(x, σ_n)}` is a component, so there are infinitely
     many.
   - *The failing step.* The proof's "open covering" by components is not open.
C. **Corollary 6.5**: "`PS^ε_z = PS_z` for small `ε`". This is false
   (`CanonicalCex.v1_corollary_6_5_false`). For every `ε`, the `ε`-approximation of `(y, σ_∞)`
   contains some `(x, σ_T)` from another component.
D. **Lemma 6.4 and Theorem 6.6.** Their proofs rely on Corollaries 6.1 and 6.5, so they are
   invalid. Statement status not determined.
E. **Corollary 5.15 "⇐"** (zero distance from limits with distance 0). The proof carries over the
   triangle inequality "literally" to `d_min`, which does not satisfy it; v3 drops this direction.
   Not formalized; `ClosureCounterexample.closure_not_setDistZero` illustrates the phenomenon.

## v1 (PODC'19): proof gaps and imprecisions (statements true)

F. **Lemma 4.7** (product topology induced by `d^ω`) holds for reflexive 0/1 distances (`lemma_4_2`).
   It fails without reflexivity, which "`d : X × X → {0,1}`" allows
   (`Lemma42Counterexample.lemma_4_2_false_without_refl`). Its proof claims that `B_1(C)` is open
   in `T_d`. This is false for `d_min` on configurations, to which v1 applies the lemma, because
   the zero-distance relation is not transitive (`BallCounterexample.ball_one_not_isOpen`).
G. **Theorem 5.9.** The sets `U(a)` are built by asymmetric forward reachability, so the claimed
   disjointness of `U(a)` and `V(a)` does not follow. It is repaired by equivalence classes. For
   message adversaries, the conclusion "a common broadcaster with constant input on every
   component" is `DN.dn_corollary_7_7`.
H. **Theorem 5.11 "⇒".** The execution `c` is asserted to lie in the component of `a_{i+1}`
   ("the same sequence of communication graphs ... can be used"), which is unjustified. The
   statement is true for message adversaries (`DN.dn_corollary_7_7`, via `DN.broadcaster_bProc`).
I. **Corollary 5.18** speaks of limit points "w.r.t. the minimum topology in `PT^ω`". For non-metric
   `d_min`, the topology induced on `Σ` by restricting `d_min` need not be the subspace topology. We
   state it in `Σ` (`Model.theorem_6_4_uniform_faultFree`).
J. **Theorem 5.5's universal algorithm** decides when `{b | π_p(b^t) = V} ⊆ PS(v)`, which is
   well-defined because the set contains the current execution. Our `universalU` is the same
   algorithm.

The remaining sections concern v3 only.

# Errors in the 2024 extension (v3 only)

## v3: false statements

1. **Theorem 5.2, "if" direction, is false** (uniform consensus, uniform topology `d_u`), even
   for lock-step synchronous full-information models. `d_u(γ, δ) = min_p d_p(γ, δ)`, and `d_p`
   counts only steps where `p` is obedient in *both* executions. But uniform agreement also binds
   a disobedient process that has the same view as an obedient one, as with a send-omission fault
   it cannot observe. Counterexample `CexUniform.theorem_5_2_false`: two non-communicating
   processes, view = (time, own input). Executions: `α` (inputs 0,0), `β` (inputs 1,1), and `δ`
   (inputs 0,1), where process 0 is disobedient from time 1 on. Then `d_u(α, δ) = 1/2` and
   `d_u(β, δ) = 0`, so `{α}`, `{β, δ}` is a `d_u`-clopen partition with validity. Yet uniform
   consensus is impossible: in `δ`, process 0 decides 0 (same views as in `α`) and process 1
   decides 1 (same views as in `β`).
   *Fix* (`Model.theorem_5_2c`): use the asymmetric distance `d_uc`, which requires obedience only
   in the first execution (`okU`). The paper's own `T_d` allows asymmetric distance functions. With
   `d_uc`, both directions hold under `LockstepRecall` (necessity holds in general). In fault-free
   models `d_uc = d_u`, so Theorem 5.2 holds as stated for message adversaries
   (`Model.theorem_5_2_faultFree`, `DN.dn_theorem_5_2`).
   Related inconsistency in Section 8.2 (general omission, `n ≤ 2f`): the text claims
   `d_u(α, α_0) = 0` because the processes of `P` cannot distinguish `α` from `α_0`. But these
   processes are faulty in `α`, so by the definition `d_p(α, α_0) ≥ 1/2`. With the paper's
   definitions the partitioning argument breaks down, through exactly the mechanism above.

2. **Theorems 5.2 and 5.3, "if" directions, are false in the generic model of Section 3.** That
   model requires only weak clocks `χ_p`, which the paper says also cover asynchronous executions.
   The termination proof of the universal algorithm uses
   `{δ | ∃ s, Cᵗ ∼_p Dˢ} ⊆ {δ | d_p(γ, δ) < 2^{-χ_p(Cᵗ)}}`. This holds only if a process's view
   determines the global time and its own earlier views. Counterexample
   `CexAsync.theorem_5_3_false_async`: two non-communicating, always obedient processes; view =
   (own input, number of own steps). In `α` (0,0) and `β` (1,1) both processes step at even times;
   in `δ` (0,1) they step at odd times. All pairwise distances are `≥ 1/2`, so `{α, δ}`, `{β}` is
   clopen in both topologies and satisfies validity. But process 0 sees the same sequence of
   views in `α` and `δ`, and process 1 the same in `β` and `δ`, so neither uniform nor non-uniform
   consensus is solvable.
   *Fix*: we add the assumption `Model.LockstepRecall`: `γ_s ∼_p δ_t ⇒ s = t ∧ ∀ u ≤ s, γ_u ∼_p δ_u`.
   Lock-step full-information models satisfy it, and so do the consistent-cut global times of
   Appendix A.2, which make global time "accessible to the processes". Under this assumption
   Theorem 5.3 holds as stated (`Model.theorem_5_3`).

3. **Theorem 7.9, Corollary 8.2 and Corollary 8.3 are false with the canonical strong broadcaster
   decision sets of Definition 7.8**, even for a limit-closed message adversary. The canonical set
   uses the lexically smallest broadcaster common to a connected component. Counterexample
   `CanonicalCex.theorem_7_9_canonical_false`. Take two processes and
   `MA = {σ_n} ∪ {σ_∞}` with `σ_∞ = (1→0)^ω`, where `σ_n` is `σ_∞` with round `n+1` replaced by
   `0↔1`; `MA` is limit-closed (`limitClosed`).
   * Consensus is solvable: decide the input of process 1.
   * Every `(x, σ_n)` is an isolated point, hence a connected component, with broadcasters
     `{0, 1}`, so its canonical broadcaster is 0.
   * In `(y, σ_∞)` only 1 is a broadcaster.
   * `(y, σ_∞)` is the limit of `(x, σ_n)` with `x = (0, y₁)`.

   So `Σ^0_0` is not closed, although condition (ii) of Theorem 7.9 / Corollary 8.2 and the
   clopenness claim of Corollary 8.3 require it. With an existentially chosen broadcaster
   (here always 1) the statement is true for message adversaries (`DN.dn_theorem_7_9_exists`).

4. **Lemma 8.6 and Corollary 8.7 are false** (same example, `CanonicalCex.corollary_8_7_false`).
   For every `ε > 0`, the `ε`-approximations `Σ^{0,ε}_0` and `Σ^{1,ε}_1` intersect: both contain
   `(1, σ_∞)`, which is not in `Σ^0_0`. So they are not at positive distance, and
   `Σ^{p,ε}_v ≠ Σ^p_v` for every `ε`. Theorem 8.8's proof relies on Corollary 8.7, so it is
   invalid. We did not determine whether Theorem 8.8 itself holds; in this example both of its
   conditions (i) and (ii) hold, which we checked by hand only.

## v3: false only in a degenerate case

5. **Lemma 4.2** (product topology = topology of the first-difference distance) is stated for any
   0/1-valued "distance function". It fails if `d(x, x) = 1` is allowed: `ProductTopology.lean`
   gives a counterexample on `Bool` (`Lemma42Counterexample.lemma_4_2_false_without_refl`). The
   proof also claims that the balls `B_1(C)` are `T_d`-open, which is false when `d = 0` is not
   transitive (`BallCounterexample.ball_one_not_isOpen`, on `Fin 3`). For reflexive `d` the
   statement is true; we prove it with a chain argument (`lemma_4_2`). All uses in the paper (discrete
   metric, `d_p` on configurations) are reflexive and transitive.

## v3: proof gaps (statement true or not affected)

6. **Theorem 7.12 / 7.13, (2) ⇒ (3).** The openness proof applies `g_I^{-1}` to `γ` for every
   assignment `I` with `I_p = v`. But `g_I^{-1}` is defined only on `Σ^{(I)}`, i.e. only for
   `I = I(γ)`. The bijections `f_{I,J}` of Definition 7.2 are not required to be coherent, so
   nothing relates executions with different input assignments. We did not formalize the generic
   Section 7. For message adversaries we prove (1) ⇔ (3) ⇔ (4) by a different argument
   (`DN.binary_iff_strong`, `DN.binary_iff_weak`). It uses the labels of the inputs
   `I_k = 1^k 0^{n-k}` under one fixed pattern. The broadcaster `b(σ)` is the first `k` where the
   label flips, as in the proof of Theorem 7.11. Its input is the strong decision value.
7. **Lemma 7.4.** The statement says "not broadcastable for some process"; "by any process" is
   meant. In the proof, the execution `δ = f(η)` shown to lie in `Σ_γ` is not the execution
   `α_p` of the induction. For message adversaries we prove the conclusion of Corollary 7.7
   (every component has a common broadcaster with constant input) by another route
   (`DN.dn_corollary_7_7`).
8. **Lemma 7.6.** The sets `U(γ)` are built by forward reachability with center-dependent
   radii. The claim "`U(γ) ∩ V(γ) = ∅` (as they would be the same otherwise)" does not follow,
   because this reachability is not symmetric. Using the equivalence classes of the generated
   equivalence relation repairs the argument (each class is open, so classes are clopen). Not
   formalized in the generic model; the message-adversary consequence is `DN.dn_corollary_7_7`.
9. **Section 6** (limit-based characterization): see `Limits.lean`. The text speaks of limit
   points "with respect to the uniform/non-uniform topology in `C^ω`". For non-metric `d`, the
   topology induced by `d` on `C^ω`, restricted to `Σ`, need not be the topology induced by `d`
   restricted to `Σ`. We state Theorem 6.4 with closures (equivalently accumulation points) in `Σ`
   (`Model.theorem_6_4_nonUniform`, `theorem_6_4_nonUniform'`, `theorem_6_4_uniform` with `τUc`).
   The `(⇒)` proof argues "`Σ_v` contains a limit point of `Σ_w` ⇒ `d(Σ_v, Σ_w) = 0`" via
   sequences and Lemma 6.2. This step fails for non-metric distance functions:
   `ClosureCounterexample.closure_not_setDistZero` gives a point in the closure of `{2}` at
   distance 1 from it. The statement follows instead from Lemma 6.3 and Theorems 5.2/5.3. The last
   sentence of Theorem 6.4 ("if consensus is not solvable then `d(Σ_v, Σ_w) = 0` for some
   `w ≠ v`") leaves the partition unspecified. We prove it for every valid partition, using
   pigeonhole over the finite `V` (`theorem_6_4_setDist_nonUniform`). Set distances are stated as
   "`∀ ε > 0`, there are points at distance `< ε`", which avoids the junk value of `inf ∅`
   (`setDistZero_iff_sInf`). `V` must be finite for "all parts closed ⇒ all parts open"; the
   paper assumes this implicitly.

## Under-specified definitions and modelling choices (both versions)

10. **Universal algorithm.** `Δ_p(C) = v` iff `{δ | ∃t, C ∼_p Dᵗ (∧ p ∈ Ob(δ))} ⊆ Σ_v`. This is
    ill-defined when the set is empty (it is then contained in every `Σ_v`). In the non-uniform
    version, the set can become empty after `p` becomes disobedient, which breaks
    irrevocability. We decide `v` iff, for some time `u` up to now, all executions where `p` is
    obedient and has the same time-`u` view lie in `Σ_v`, and there is one (`DecNU`). For the
    uniform version we use the current view (`DecU`), whose set always contains the current
    execution.
11. **"Reachable"** (irrevocability of decisions; disobedient processes do not recover) is not
    defined. We read "`C'` reachable from `C`" as "`C'` occurs later than `C` in an admissible
    execution".
12. **Validity** for non-uniform consensus is required of obedient processes only ("obedient
    processes must ... satisfy the specification"). For uniform consensus this is equivalent to
    validity for all processes (`SolvesUniform.validity_all`).
13. **Partitions** `Σ = ⋃_v Σ_v` are encoded as labellings `lab : Σ → V`, so parts may be empty.
    The topologies are those induced on `Σ` by the distance functions restricted to `Σ`.
    `d_nu` is `1` when `Ob(γ) ∩ Ob(δ) = ∅`, as in the paper. Processes are a finite nonempty type.
14. **Dynamic networks.** Configurations are (time, inputs, pattern truncated to the rounds
    played). `C ∼_p D` is equality of the full-information views (`DN.FIIndist`, defined by
    recursion on the round). All processes are correct, inputs are arbitrary and independent of
    the pattern, and message adversaries are arbitrary sets of patterns (not necessarily
    limit-closed). Limit-closedness (`LimitClosed`) is the combinatorial "every pattern whose
    prefixes all extend into `MA` is in `MA`".
15. **Section 7 in the generic model** (Definitions 7.1–7.2: HO functions, independent arbitrary
    input assignments) is not formalized. Its message-adversary instances are formalized with
    the concrete heard-of relation `DN.Heard`.

## Not formalized

Appendix A (process-time graphs, consistent-cut global time, Lemma A.2); Definition 6.6 and
Corollary 6.7 (fair/unfair executions); Section 8.2 (general omission faults); Theorem 8.1
(condition-based consensus); Theorem 8.8 and Theorem 8.9 (the latter is cited from [47]);
Section 8.5's ♦STABLE discussion; Section 8.6 (WTL labelling algorithm).

## Typos and slips

* Theorem 7.13 (2): "uniformly broadcastable" should be "non-uniformly broadcastable"; "Foy any" →
  "For any" (Theorems 7.12, 7.13).
* Before Theorem 6.4: "Applying Lemma 6.3 to the findings of Theorem 5.2 resp. Theorem 5.2" (second
  should be 5.3).
* Proof of Theorem 7.13: `2^{-χ_p(C^t)}` and `Δ_p` should use `q`; the displayed
  `{δ | d_q(γ,δ) < ε ∧ q ∈ Ob(δ)} = {δ | d_nu(γ,δ) < ε}` should be `⊆`.
* Proof of Lemma 4.4: the second line of the display writes `d_p(Cᵗ, Dᵗ)` for `d_p(γ, δ)`.
* Figure 3 caption: unresolved reference "cor:closeddecsetscompact".
