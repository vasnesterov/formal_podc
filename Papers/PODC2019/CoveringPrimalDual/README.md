# Optimal Distributed Covering Algorithms — PODC 2019

Ran Ben-Basat, Guy Even, Ken-ichi Kawarabayashi, Gregory Schwartzman. *Optimal Distributed Covering
Algorithms.* PODC 2019. DOI [10.1145/3293611.3331577](https://doi.org/10.1145/3293611.3331577).
Formalized version: arXiv [1902.09377](https://arxiv.org/abs/1902.09377) v2 (same text and numbering
as the PODC version). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Weakened.** The core of the paper stands: algorithm MWHVC is an `(f+ε)`-approximation for
minimum-weight hypergraph vertex cover (Corollary 4.3), it terminates within `O(log_α Δ + f·z·α)` iterations
(Theorem 4.8), and the choice of `α` in Theorem 4.9 gives the claimed
`O(f log(f/ε) + log Δ/log log Δ + min{log Δ, f log(f/ε) (log Δ)^γ})` bound. The extension to covering ILPs
announced in the abstract and introduction ("an `(f+ε)`-approximate integral solution … where `f` bounds the
number of variables in a constraint") is lost: its ratio is refuted and its stated degree parameter is too small.
The CONGEST details and the round bounds of Corollaries 4.10–4.12 were not checked.

## Mistakes in the paper

### ❌ Claim 5.7, abstract and introduction (approximation ratio for covering ILPs)
The covering-ILP algorithm is not an `(f(A)+ε)`-approximation: on `min x s.t. x ≥ 2` (`f(A) = 1`) it
outputs `x = 3` for every `ε ∈ (0,1]` and every `α`, while the optimum is 2 and `(f(A)+ε)·2 = 5/2` for
`ε = 1/4` (`ILPCex.claim_5_7_false`).

**Impact.** Refutes the ILP extension as stated in the abstract and introduction, including the claim
that `ε = 1/(nWM)` gives an `f`-approximation for ILPs. The true guarantee of the reduction is
`f(A)·⌈log₂ M + 1⌉ + ε` (from Corollary 4.3 and `fA_binExp`; not a named Lean theorem), which gives up the
claimed ratio and the comparison with [KMW06]. The hypergraph results of Section 4 are unaffected.

**Details.** The reduction (binary expansion, Claim 5.6, then Lemma 5.2) produces a hypergraph of rank
`f(A)·⌈log₂ M + 1⌉`, not `f(A)`. MWHVC only guarantees rank `+ ε`, and the proof of Claim 5.7 never
addresses the ratio. In the example, `M = 2` and `B = 2` bits `x = x₀ + 2x₁`. The reduced hypergraph
has edges `{x₀,x₁}` and `{x₁}` with weights `1, 2`. MWHVC with `ε = 1/4` makes both vertices stuck in
iteration 1 and puts both into the cover in iteration 2, so it outputs `x = 3` of cost 3. No vertex
ever sends "raise" and both become tight exactly in iteration 2, so the run is the same for every
`ε ∈ (0,1]` and every `α`: the ratio is 3/2. The paper's assumption `Δ ≥ 3` is not needed for the
approximation claim. A simulation of the same pipeline on `x ≥ 4` (3 bits, `Δ = 4`) gives `x = 5`
against an optimum of 4, which also violates the claim for `ε < 1/4`; that instance is not in Lean.
The hypergraph is shown to be exactly the Lemma 5.2 reduction of the Claim 5.6 expansion in
`ILPCex.edges_eq`.

### ❌ Claim 5.7 (degree parameter `Δ'`)
The proof writes `2^{f(1+log M)} = 2^f·2M`, but in fact `2^{f(1+log M)} = (2M)^f`, and the reduced
hypergraph can exceed the stated degree `Δ' = 2^{f(A)}·M·Δ(A)` (`Degree57.claim_5_7_degree_false`).

**Impact.** The running-time expression of Claim 5.7, which feeds the round bound in the abstract, is
unsupported; we did not try to repair it.

**Details.** For `x₁ + x₂ ≥ 8` (`f(A) = 2`, `Δ(A) = 1`, `M = 8`, `B = 4`), the top bit of `x₁` lies in
36 hyperedges, more than `2²·8·1 = 32`.

### 🔧 Lemma 4.7 (and Lemma C.2, number of stuck iterations)
The bound `#stuck ≤ α` is off by a ceiling: for `α = 29/10`, a vertex is stuck three times at level 1
(`Stuck.lemma_4_7_false`).

**Impact.** Theorem 4.8 keeps its asymptotic bound; we prove `≤ ⌈α/κ⌉` (`lemma_4_7`, `lemma_4_7_ceil`).

**Details.** The paper divides the slack by the minimum stuck increment, which only gives
`#stuck < α+1`. That is `≤ α` only for integral `α` (`lemma_4_7_of_nat`), while Theorem 4.9 uses
non-integral `α`. Here `κ = 1`, or `κ = 1/2` for Appendix C.

### 🔧 Claim 4.2, Eq. (1) ("for every `v ∉ C`")
Eq. (1) fails for a vertex that terminated without joining `C`, because its level is no longer updated:
on one edge `{0,1}` with weights `4, 7`, vertex 1 terminates in iteration 2 with level 0, but
`∑δ₁ = 4 > 7/2` (`Eq1.claim_4_2_eq1_false`).

**Impact.** The proof only uses Eq. (1) for active vertices, where it holds (`claim_4_2`).

### ✏️ Slips
- Corollary 4.10: with `W = max w/min w`, `ε = 1/(nW)` does not give an `f`-approximation: on three parallel edges
  `{0,1}` with weights `9, 10` the output costs `19 > f·OPT = 18` (`Cor410.corollary_4_10_false`). The error is in
  the definition of `W`: the introduction uses `W` for the maximum weight (`w : V → {1,…,W}`), and with
  `ε < 1/(n·max w)` the integrality argument works. Corollary 4.3 does not depend on this.
  - With the printed `W`, `ε·OPT` can be as large as `min w`, so integrality does not help.
  - In the example `Δ = 3`, `n = 2`, `W = 10/9`, `ε = 9/20`. Neither vertex ever sends "raise", so the run is the
    same for every `α`. Both vertices join in iteration 2. The Lean instance uses parallel edges only to reach
    `Δ = 3`.
  - A simulation also found a simple graph with `Δ = 3` (6 vertices, 7 edges, weights 31–33) on which the output
    costs more than `2·OPT`; that instance is not in Lean.
- Definition 5.4 drops the `max{1, ⌈·⌉}` of the introduction's `M = max{1, ⌈1/a_min⌉}`, with two consequences.
  With the introduction's `M` both statements hold.
  - Proposition 5.5 is false for non-integral `M`: for `2x ≥ 3`, `M = 3/2`, the ILP is feasible (`x = 2`), but no
    integer point of the box `[0, 3/2]` is feasible (`prop_5_5_false`). With the box `[0, ⌈M⌉]ⁿ` the proposition
    holds, since capping a feasible `x` at `⌈M⌉` keeps it feasible and does not increase the cost (`prop_5_5_ceil`).
  - Claim 5.6 fails for `M < 1`: for `2x ≥ 1` (`M = 1/2`) the stated bound `f(A') ≤ f(A)·⌈log₂ M + 1⌉ = 0` forces
    `A' = 0`, so no such zero-one program is feasible (`claim_5_6_false`). For `M ≥ 1` the claim holds (`claim_5_6`,
    `claim_5_6_bits`).
- The proof of Claim 5.6 uses `B = ⌈log₂ M⌉` bits, which loses solutions when `M` is a power of two: for `x ≥ 2`,
  one bit is not enough (`claim_5_6_proof_false`). With `B` bits such that `⌈M⌉ < 2^B` (for example the statement's
  `B = ⌈log₂ M + 1⌉` when `M ≥ 1`), the reduction is correct, `f(A') = f(A)·B` and `Δ(A') = Δ(A)` (`claim_5_6`,
  `claim_5_6_bits`, `fA_binExp`, `ΔA_binExp`).
- Lemma 5.2: the rank bound `f' < f(A)` is false: the hyperedge `σᵢ \ ∅ = σᵢ` has `f(A)` vertices, and on the single
  constraint `x₁ ≥ 1` no hypergraph with edges smaller than `f(A) = 1` has the feasible solutions as its covers
  (`lemma_5_2_rank_false`). The correct bound `f' ≤ f(A)` holds, and so does the degree bound, in the sharper form
  `≤ 2^{f(A)-1}Δ(A)`. Correctness of the reduction is proved (`lemma_5_2_cover_iff`, `lemma_5_2_rank`,
  `lemma_5_2_degree`).
- Theorem 4.9 for `f = 1, ε = 1`: here `f·log(f/ε) = 0`, the definition of `α` divides by zero, and
  `O(f log(f/ε) + …)` cannot absorb the additive constant. We use `F = f·z` with `z = ⌈log₂(1/β)⌉ ≥ 1` instead. This
  is `Θ(f log(f/ε))` whenever `f/ε ≥ 2`.

### Typos
- Appendix B sets `deal₀(e) = β·min w/|E|`, but Section 3 uses `0.5·min w/|E|`. Both satisfy the
  analysis; we parametrize by `c₀ ∈ (0, 1/2]`.
- In the proof of Theorem 4.8, "e-stuck" should read "e-raise".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous, deterministic, failure-free. One iteration of MWHVC (steps 3a–3f) is a function
  `step` on the global state: cover `C`, levels, deals, duals. `run I P i` is the state at the end of
  iteration `i`. The algorithm only exchanges information between a vertex and its incident edges.
  The analysis, like the paper's, is about the iteration count, so messages and the CONGEST encoding
  (Appendix B) are not modelled.
* Hypergraphs are `inc : E → Finset V` with nonempty edges; parallel edges are allowed (the set-cover
  reading). Weights are positive reals (the paper: positive integers). All instances are quantified
  over. `f` is any rank bound `≥ 1` and `Δ` any degree bound.
* Step 3a lets every `v ∉ C` join when `β`-tight, as written. The `while` loop of 3d is "least level
  `ℓ' ≥ ℓ` with `∑δ ≤ w(1-2^{-(ℓ'+1)})`" (`lvlUp`). Each level increment halves the deals of the
  uncovered incident edges.
* Parameters: `ε > 0` (the paper: `ε ∈ (0,1]`), `α > 1` (the paper: `α ≥ 2`), and `κ ∈ (0,1]` for the
  dual increment `δ += κ·deal`. `κ = 1` is Section 3 and `κ = 1/2` is Appendix C, so both variants
  are covered by one proof. The initial factor is `c₀ ∈ (0,1/2]` (Section 3: `1/2`; Appendix B: `β`).
* The approximation bound is proved against every fractional vertex cover, hence against the LP
  optimum and every integral cover. The LP machinery (fractional covers, packings, weak duality,
  Claim A.1) is in `Podc/Foundations/Combinatorics/HypergraphCover.lean`.
* Section 5: covering ILPs `min wᵀx, Ax ≥ b, x ∈ ℕⁿ` with nonnegative data. The Lemma 5.2 hypergraph
  is the set of hyperedges `σᵢ \ S` over all rows `i` and all `S ⊆ [n]` with `Aᵢ·I_S < bᵢ`, exactly as
  in the paper. The distributed simulation over `N(ILP)` is not modelled.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Algorithm MWHVC (Sec. 3, App. B/C variants) | `step`, `run`, `lvlUp`, `Params` | `Algorithm.lean` |
| Claim 4.1 | `claim_4_1` | `Correctness.lean` |
| Claim 4.2 (Eq. (1) for active vertices; feasibility) | `claim_4_2`, `claim_4_2_feasible` | `Correctness.lean` |
| Claim A.1 | `claim_A_1` (general: `Cslib.Hypergraph.sum_tight_le_of_isPacking`) | `Correctness.lean`, `Podc/…/HypergraphCover.lean` |
| Corollary 4.3 | `corollary_4_3`, `corollary_4_3_integral` | `Correctness.lean` |
| Claim 4.4 | `claim_4_4` | `Correctness.lean` |
| Corollary C.1 | `corollary_C_1` | `Correctness.lean` |
| Lemma 4.6 | `lemma_4_6` (general `c₀`: `lemma_4_6_general`) | `Rounds.lean` |
| Lemma 4.7 / C.2 (corrected: `< α/κ + 1`, `≤ ⌈α/κ⌉`; as stated for integral `α`) | `lemma_4_7`, `lemma_4_7_ceil`, `lemma_4_7_of_nat`, `lemma_C_2_of_nat` | `Rounds.lean` |
| Theorem 4.8 | `theorem_4_8` (bound `iterBound`), `iterBound_le`, `z_le` | `Rounds.lean` |
| Theorem 4.9 (with `f·z` for `f log(f/ε)`, explicit constant) | `theorem_4_9`, `alpha49`, `C49` | `Theorem49.lean` |
| Main result: terminates, cover, `(f+ε)`-approx., iteration bound; App. C variant | `mwhvc_main`, `mwhvc_appendixC` | `Main.lean` |
| Lemma 5.2 (correctness, nonempty edges, rank `≤ f(A)`, degree) | `lemma_5_2_cover_iff`, `lemma_5_2_nonempty`, `lemma_5_2_rank`, `lemma_5_2_degree` | `ILP.lean` |
| Lemma 5.2 rank `f' < f(A)` false | `lemma_5_2_rank_false` | `ILP.lean` |
| Proposition 5.5 false / repaired | `prop_5_5_false`, `prop_5_5_ceil` | `ILP.lean` |
| Claim 5.6 false / proof false / repaired | `claim_5_6_false`, `claim_5_6_proof_false`, `claim_5_6`, `claim_5_6_bits`, `fA_binExp`, `ΔA_binExp` | `ILP.lean` |
| Claim 5.7 ratio and degree false | `ILPCex.claim_5_7_false`, `Degree57.claim_5_7_degree_false` | `Counterexamples.lean` |
| Corollary 4.10 (`ε = 1/(nW)`) false | `Cor410.corollary_4_10_false` | `Counterexamples.lean` |
| Lemma 4.7 as stated false; Eq. (1) for terminated vertices false | `Stuck.lemma_4_7_false`, `Eq1.claim_4_2_eq1_false` | `Counterexamples.lean` |

Concrete executions are certified through a computable rational copy of one iteration (`stepQ`).
`step_castS` shows that it agrees with the real-valued `step` whenever the bounded loop sufficed, a
condition checked by `decide`. See `Compute.lean`.

**Not formalized.** The CONGEST implementation and message sizes (Appendix B), and the claim that the
local degree `Δ(e)` can replace `Δ`. Corollaries 4.10–4.12 as round bounds, including `O(f log n)` with
`ε < 1/(n·max w)` for polynomial weights, and the asymptotic simplification at the end of Section 5. Claim 5.3 (the simulation over `N(ILP)`).

**Trust.** No `sorry`, no `native_decide`. All listed theorems use only `propext`,
`Classical.choice`, `Quot.sound`. Concrete runs use `decide +kernel`. Non-vacuity: `Params.std_valid`
shows that the paper's parameters are valid for every instance, every `ε > 0` and `α > 1`. An
`example` in `Main.lean` applies `mwhvc_main` to every instance. The counterexample instances come
with `Valid` proofs.
