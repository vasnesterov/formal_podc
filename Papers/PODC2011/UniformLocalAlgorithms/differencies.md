# Differences between the formalization and the paper

Paper: A. Korman, J.-S. Sereni, L. Viennot, *Toward More Localized Local Algorithms: Removing
Assumptions Concerning Global Knowledge*, PODC 2011; formalized from the journal/arXiv version
arXiv:1512.03306v1 (Distributed Computing). Verdict rules: see `verdicts.md` (R1–R6).

## Errors in the paper

1. **Observation 3.3 is false (❌, R1/R5: a numbered observation, not a headline).** With the paper's
   encoding of matchings (page 6: `u, v` matched iff adjacent, `y(u) = y(v)` and no other neighbour of
   `u` or `v` has this output) the algorithm `P_MM` (page 10) does not satisfy gluing. Path
   `v₀ — u₀ — u — v`, `ŷ = (5, 5, 1, 2)`: `W = {v₀, u₀}`; the residual edge `u — v` is solved by
   `y' = (5, 5)`; the combined output `(5, 5, 5, 5)` matches no pair, so it is not a maximal matching.
   This holds whatever new inputs the pruning algorithm assigns (`observation_3_3_false`). Not an
   R3 typo: the fix changes the problem's output encoding (or the algorithm), it is not a local
   correction. Repair: encode a matching by partner identities (`mmId`); the same rule `W` is then a
   pruning algorithm, running in 2 rounds (`observation_3_3_repaired`). Corollary 1(vi) is
   unaffected for that encoding (`corollary_1_vi`), and converting the partner encoding to the
   paper's one takes one more round (output the pair `{Id u, Id v}` of the matched edge, or a fresh
   value `(Id u, Id u)` for an unmatched node; not formalized). Borderline call: a reviewer could
   see this as an encoding slip; we keep ❌ because the observation is false for the paper's own
   explicit definitions.
2. **Observation 3.3: "monotone with respect to any parameter" (⚠️, R3).** False for parameters that
   decrease under taking subgraphs (e.g. `max(1, 100 − n)`); Observation 3.2 and Section 3.2 make
   clear that "any non-decreasing parameter" is meant. Formalized as "every non-decreasing
   parameter" (`observation_3_3_repaired`, last component).
3. **Theorems 1–4: the bounds `O(f*·s_f(f*))` and `O(f_min)` fail when `f* < 1` (⚠️, R2).** The
   transformed algorithm needs at least one iteration (a constant number of rounds `≥ 1` with a
   non-trivial pruning algorithm), while `f*` may be `0` (and `s_f(f*)` may be `0` for small
   arguments: moderate slowness says nothing at `i = 1`). We prove `C·(f*·s_f(⌊f*⌋) + 1)`, resp.
   `C·(f_min + 1)`. `s_f` is a function on `ℕ`; the paper applies it to the real `f*`; we use
   `⌊f*⌋` (the strongest choice).
4. **Observation 3.2 needs `β ≥ 1` (⚠️, R2).** For `β = 0` gluing fails on a single edge; the
   `(2,0)`-ruling set problem only has solutions on edgeless graphs, so this is degenerate.

## Proof repairs

5. **Theorem 3, proof (🛠️).** The proof sets `g_j⁻¹(x) = min g_j⁻¹({x})` and uses
   `g_j(g_j⁻¹(x_{h(j)})) = x_{h(j)}`; this is undefined/false when `x_{h(j)}` is not a value of
   `g_j` (ascending functions need not be surjective onto `ℕ`), and `g_j` is real-valued while
   coordinates are integers. Repair: `g_j⁻¹(x) = max {y : g_j(y) ≤ x}` (`maxLe`). We also replace the
   paper's construction (a new bound `f'` on `ℓ + t` coordinates and a new set-sequence) by a direct
   reduction to Theorem 1: the Λ-guesses determine Γ-guesses `γ_j = max {y : g_j(y) ≤ q̃_{i_j}}`
   (or the guess of the shared parameter), which are good whenever the Λ-guesses are good.
6. **Theorem 2, proof (🛠️).** The bound on `E[T_τ]` uses `α_{i+1} ≤ K·α_i` "since `s_f` is
   moderately slow", where `α_i` is the number of rounds of the first `i` iterations of `τ`. This
   does not follow: `α_i` is driven by the actual sizes `|S_f(2^j)|`, which are only bounded above by
   `s_f(2^j)`. They can be `1` for many `j` and then jump to `s_f(2^j)`, so `α_{i+1}/α_i` is
   unbounded in general. Repair (`max_dur_le`): use the upper bound
   `max(s+i, α_{s+i}) ≤ (2K+1)·s_f(2^s)·2^s·(2a)^i`, where `a` is the moderate-slowness constant.
   Together with `P(still active after iteration s+i−1) ≤ (1−ρ)^{i(i+1)/2}` and the summability of
   `Σ (2a)^i (1−ρ)^{i(i+1)/2}` (`summable_pow_mul_pow_tri`), this gives the claimed
   `O(f*·s_f(f*))` (with `+1`, item 3). The paper normalizes to `ρ = 1/2`; we keep a general `ρ > 0`.
7. **Corollaries 3 and 4: families not closed under inclusion (proof gap, not formalized as
   stated).** Section 2 assumes every family `F` is closed under inclusion, and a pruning algorithm
   must map `F` into `F`. The families used in Corollary 3 (`F_large`: `a > log^{1+ε/2} n`; `F_med`:
   `log^{1/3} n < a ≤ log^{1+ε/2} n`) and Corollary 4 (`a = o(√log n)`, `a = O(log^{1/2−δ} n)`) are
   not closed under taking induced subgraphs (deleting isolated vertices lowers `n`; deleting
   edges lowers `a`), so Theorems 1 and 3 do not apply to them literally. For Corollary 3 the
   result can be recovered on the family of all graphs: Barenboim–Elkin's bound
   `a + a^δ log n ≤ 2a + (log n)^{1/(1−δ)}` is additive (`s_f = 1`), and on `F_large` it is `O(a)`
   for small `δ`; similarly for `F_med` with the product form and `s_f = O(log)`. We did not
   formalize Corollary 3. Corollary 4 additionally needs the time bound of [6, Thm 6.3] to hold for
   **every** good guess `ã` (including `ã = ñ`, the guess produced by weak domination via `a ≤ n`);
   the paper does not discuss this. `corollary_4` takes exactly this as its hypothesis, on the
   (inclusion-closed) family of all finite graphs.

## Modelling choices and imprecisions (no effect on the verdict)

- **Randomized model (Theorem 2).** Every node has a private tape in `R`, i.i.d. with law `ν`
  (`Measure.infinitePi`). A randomized algorithm is an `Alg V (α × R) β` run on the labels
  `(x v, ω v)`, so locality in the random bits comes for free. `τ` has tapes `ℕ → R`, and each
  sub-iteration reads its own coordinate (injective numbering), which gives the paper's "fresh random
  bits". A weak Monte-Carlo algorithm with guarantee `ρ > 0` (`WeakMonteCarlo`), with good guesses and
  `T ≥ f g`, solves the instance within `T` rounds with probability `≥ ρ`. Added assumptions, all
  true in the paper's setting (bit-string inputs and outputs, finite graphs): countable input and
  output types, instances with finite node set, and measurability of the outputs in the tapes
  (`OutputsMeasurable`). Las Vegas correctness is proved for every tape: whenever all nodes have
  output, the outputs form a solution. The expected running time is the `lintegral` of `runTime`, the
  first round at which all nodes have output (`∞` if never). An explicit almost-sure termination
  corollary is not stated; it would need measurability of `runTime`. `weakMonteCarlo_ignoreTape`
  shows non-vacuity.
- **Theorem 3, randomized case:** not formalized. Our reduction acts on the non-uniform algorithm,
  so it would transfer verbatim to `WeakMonteCarlo`.

- **LOCAL model, extensional.** Identifiers are the elements of a type `V`; an instance is
  `(G, x : V → Option α)` with node set `{v | x v ≠ none}` and graph `res G x` (induced subgraph),
  so that pruned instances live on the same type. A (uniform, deterministic) algorithm `Alg` gives
  for each round `t` the outputs `out t G x v : Option β` (`none` = not terminated) as a `t`-local
  function (CSLib `Cslib.Local.IsLocal`, equal radius-`t` views give equal outputs), with final
  outputs. Running time `≤ T` = all nodes of the instance have output a solution by round `T`
  (`Alg.SolvesWithin`).
- **Synchrony / Observation 2.1.** All stages of the alternating algorithms have lengths known to
  every node (`A` restricted to `c·2^i` rounds, then `P` for `rad` rounds), so all nodes stay
  synchronized and no synchronizer is needed; the paper's discussion of non-simultaneous wake-up
  (Observation 2.1, α-synchronizer) is not formalized. Nodes output at the end of the *phase*
  (iteration) in which they are pruned (`Pruning.alg`), slightly later than in the paper; the bounds
  are unaffected.
- **Problems** (`Problem`): only depend on the outputs of nodes of the instance (`congr`), and the
  empty output is a solution of the empty instance (`empty`; stated in Section 3.1 of the paper).
  Closure under disjoint union is not needed. Problems are predicates on `res G x` (enforced by
  `Family.res_eq`: members are normalized).
- **Families** (`Family`): closure under inclusion is not assumed; the pruning algorithm must map
  `F` to `F` (`Pruning.mem`), which is all the proofs use.
- **Pruning algorithms** (`Pruning`): constant running time `rad`, locality in `(x, ŷ)`, sub-instance,
  membership, solution detection, gluing — as in Section 3.2. "Uniform" = a single object not
  depending on guesses.
- **Running-time hypothesis** (`DependsWithTime`): with good guesses `g`, `A g` solves the instance
  within every `T ≥ f g` (equivalently within `⌈f g⌉`; the paper's `T_A ≤ f(g)` means within `⌊f g⌋`,
  a slightly stronger hypothesis, so our theorems are slightly more general). We require `f ≥ 0`
  (the paper's `f : ℕ^ℓ → ℝ⁺`).
- **Theorem 1:** the paper assumes `f` non-decreasing and the parameters non-decreasing; neither is
  used (only `Γ`-monotonicity of `P`). Bounding constant `c` real, rounds `⌈c⌉·2^i`.
- **Theorem 3:** only `Λ`-monotonicity of `P` is needed (the paper assumes `Λ ∪ Γ`); weak
  domination uses `g_j → ∞` (monotonicity of `g_j` is assumed, as in the paper, but unused). Shared
  parameters are given by `σ : Fin ℓ → Option (Fin r)` instead of the paper's index convention
  `p_i = q_i` for `i ≤ r'`.
- **Theorem 4:** stated as "running time `≤ C·(f_j(Λ_j*) + 1)` for every `j`", which is
  `O(min_j f_j)`; requires `k ≥ 1`.
- **Observation 4.1:** "ascending" is used only through `f_k → ∞`; the product case is stated for
  `ℓ = 2` with `s(i) = ⌈log₂ i⌉ + 1` (`Nat.clog 2 i + 1`).
- **Observation 3.1(2)** proved for the family `allFinite` of all finite instances
  (`observation_3_1_2`); Observation 3.1(1) (graph-parameters with input changes) is not
  formalized. Parameters `n = numNodes`, `Δ = maxDeg` on finite instances.
- **Corollaries:** the cited algorithms ([4], [22], [34], [19], [6]) are hypotheses with their
  claimed running times; the concrete functions (`2^{O(√log n)}`, `O(log⁴ n)`) are abstracted to an
  arbitrary non-negative ascending `g(ñ)`. Corollary 1(i) is formalized as its last step (Theorem 4
  applied to three uniform MIS algorithms); Corollary 2 bullet 1 with the explicit bound
  `C(Δ̃ + log* ñ)`. Corollary 1(ii)–(v) (coloring, Section 5, Theorem 5) and Corollary 3 are not
  formalized.
- **Not formalized:** Section 5 (Theorem 5, uniform colorings, the `G × K_{Δ+1}` reduction), the
  Monte-Carlo → Las Vegas remark of Section 3.1 beyond Theorem 2, Section 6.
