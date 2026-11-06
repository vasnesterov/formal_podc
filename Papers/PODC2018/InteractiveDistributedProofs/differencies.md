# Differences between the formalization and the paper

Kol, Oshman, Saxena, *Interactive Distributed Proofs*, PODC 2018 (author copy, 10 pp.).

## Errors in the paper

1. **Lemma 3.11 is false** (⚠️: the paper's proof reasons with the wrong object, and the fix changes the
   lemma's content).
   `μ_A(F)` is defined as the law of the random set `𝓜_A(F, r)`, but the event the proof uses to separate
   `μ_A(F₁)` from `μ_A(F₂)` ("intersects `𝓜_B(F₁, r)`") depends on `r` itself. Counterexample
   (`LowerBound.lemma_3_11_false`): 6-vertex asymmetric graphs `F₁`, `F₂ = F₁ + {01}`, a simple protocol
   with 1-bit challenges and 2-bit responses that masks the bit "is `01` an edge?" with the bridge nodes'
   challenges. It decides `Sym` on the dumbbell class with perfect completeness and soundness, and
   `μ_A(F₁) = μ_A(F₂)`.
   *Robustness (reviewer check).* The counterexample uses only what the paper's model grants: Definition 6
   restricts only the bridge nodes' decisions; Definition 1 lets every node read the responses of `N(v)`,
   and Section 2.2 explicitly gives `r_{N(v)}` to each node in the lower bound. `𝓜_A` and `μ_A` are
   modelled exactly as in Section 3.4 (law of the *set* `𝓜_A(F, r)`). The small family `|𝓕| = 2` is not
   what makes it work: for any family, the prover can give every node of `V_A` the full encoding `enc(F_A)`
   (checked locally) and the bridges `(enc(F_A) ⊕ r_{x_A}, enc(F_B) ⊕ r_{x_B})` with `n²`-bit challenges.
   This decides `Sym` on `𝒢`, and `𝓜_A(F, r)` is a uniform singleton for every `F`, so Lemma 3.11 fails for
   the paper's large family too (with `L = O(n²)`; the lemma has no bound on `L`).
2. **Theorem 1.4 (lower bound `Ω(log log n)`) is unestablished as proved** (⚠️, same mistake as item 1:
   its proof uses a false lemma). The intro's stronger claim ("even if the nodes share an unbounded amount
   of randomness with the prover and with each other") is not supported by any argument.
   **Repair** (`LowerBound/Repair.lean`): `𝓜_A(F, r)` depends only on the A-side challenges and on
   `r_{x_A}, r_{x_B}`, and `𝓜_B` only on the B-side challenges and the same two. So with
   `μ'_A(F)` = joint law of `((r_{x_A}, r_{x_B}), 𝓜_A(F, r))` we get
   `Pr[𝓜_A(F, r) ∩ 𝓜_B(F₁, r) ≠ ∅] = ∑_z μ'_A(F)(z) g(z)` with `0 ≤ g ≤ 1`
   (`uprob_inter_nonempty_eq_sum`), and Corollary 3.10 gives `‖μ'_A(F₁) − μ'_A(F₂)‖₁ > 2/3`
   (`lemma_3_11_repaired`). Lemma 3.12 on a domain of size `|R|²·2^{|M|}` gives
   `|𝓕| < 5^{|R|²·2^{|M|}}` (`card_family_lt`), hence `log₂|𝓕| < 3·2^{2^{L+1}}` for `L`-bit challenges
   and responses (`theorem_1_4_repaired_log`, `theorem_1_4_repaired`). This proves Theorem 1.4 under
   Definition 1/2 (challenges of `ℓ` bits), for simple protocols (Lemma 3.7 not formalized), assuming a
   family `𝓕` with `|𝓕| ≥ 2^{c n²}` (cited from the literature) and the paper's claim
   `Sym(G(F_A, F_B)) ↔ F_A = F_B` (hypothesis `hiff`; proved for the counterexample family,
   `cexFamily_hiff`). The repaired dimension grows with `|R|²`, so the intro's "unbounded randomness"
   claim remains unproved. (Definition 1 gives challenges length `ℓ`, so Theorem 1.4
   as formally defined is recovered by the repair, modulo the unformalized Lemma 3.7 and family facts; but
   the introduction says "for our lower bound we do not charge for [the random bits]" and claims the bound
   with unbounded shared randomness. That stronger claim is unestablished, not refuted.)
   Lemmas 3.8 and 3.9 and Corollary 3.10 are formalized as stated
   (`lemma_3_8`, `lemma_3_9`, `corollary_3_10`). `FamilyOK` is not needed there, only `hiff`.
3. **Protocol 1, line 2 counts the root as a child** (🔧: missing case in pseudocode; the intended
   version is the tree `T` "formed by the edges `{v, t_v}` for `v ≠ r`" of the proof of Lemma 3.3).
   The prover sends every node, including the root, a parent identifier `t_v`, and
   `C(v) = {u ∈ N(v) | t_u = v}` with `N(v) ∋ v`. If `t_r ∈ N(r)` (e.g. `t_r = r`), the root is in
   `C(t_r)`, the check at `t_r` contains `a_r`, and summing all checks gives `h_i(∑_v [v, N(v)]) = 0`
   instead of `a_r = h_i(∑_v [v, N(v)])`.
   * **Lemma 3.3 is false as written**: `lemma_3_3_false` (`K₂`, `p = 83`, `t_0 = t_1 = 0`, all challenges
     `-1`, `a_0 = b_0 = 1 ≠ 0 = h_{-1}(A)`; every node accepts).
   * **Theorem 3.4 (completeness) is false as written** for every graph in which each vertex moved by a
     non-trivial automorphism is adjacent to all others, e.g. `K_n`: the honest prover cannot avoid
     `t_r ∈ N(r) = V`, so every prover is accepted with probability `≤ (n² − 1)/p`
     (`accProb_top_literal_le`, `theorem_3_4_literal_false`).
   * Soundness of the literal protocol is fine (`soundness` holds for both versions: the extra case only
     adds the event `h_i(A) = 0`, of probability `≤ (n² − 1)/p`).
   * The same line is used in Protocol 2 (and in the DSym protocol of Section 3.3); we formalize Protocol 2
     only with the repaired line.
   Repair used: `C(v) = {u ∈ N(v) | u ≠ r ∧ t_u = v}` (flag `excl = true`); then `lemma_3_3` and
   `theorem_3_4` hold as stated.
   (Protocol 2 says explicitly `t_v ∈ V`, so the root's pointer cannot be `⊥`. But the paper's own proof of
   Lemma 3.3 uses only the edges `{v, t_v}` for `v ≠ r`, the honest prover gives each node "its parent in `T`"
   (the root has none), and the fix is local. Theorem 1.1 is existential and holds with the repaired protocol
   (`theorem_1_1`).)
4. **Proof gap in Theorem 3.5** (🔧, statement true). The proof fixes a root `r₀` and union-bounds over the
   `n^n` maps `σ`, but in Protocol 2 the prover names the root `r` (and must echo `i = i_r`) *after* seeing
   all challenges, so it can pick any node whose index is bad: the union bound must also range over `r`,
   which multiplies the paper's bound by `n`. Repair (`Protocol2.soundness_bound`, `soundness`): since `ρ`
   is broadcast as a permutation, union over `n · n!` pairs `(r, σ)`; `2 n · n! (n² − 1)/p < 1/3` for
   `p ≥ 10 n^{n+2}` because `n! ≤ n^{n−1}`. So the paper's parameters suffice.
5. **Lemma 3.12: statement true, proof sloppy** (🔧). The balls are intersected with `[0,1]^d`, which makes
   their volumes depend on the centre, and the ℓ₁-ball volume formula `(4r)^d/(d+1)!` is wrong (it is
   `(2r)^d/d!` in `ℝ^d`). Repair (`LowerBound/Packing.lean`): full ℓ₁ balls in `ℝ^d` and translation/scaling
   invariance of Haar measure; we even get `|U| ≤ 5^d − 3^d`. Also a typo: the ball is written
   `{x | ‖µ − η‖₁ < r}` instead of `‖µ − x‖₁ < r`.
6. **Theorem 3.2 is stated for inputs in `{0,1}^m`** but is applied to `∑_v [ρ(v), ρ(N(v))]`, whose entries
   lie in `{0, …, n}` when `ρ` is not injective (Lemma 3.1 is designed exactly for such `ρ`), and the
   linearity clause itself adds vectors mod `p`. (🔧: the intended domain `(Z_p)^m`
   is evident from the linearity clause.) We prove Theorem 3.2 on `(ZMod p)^m` (`theorem_3_2`), which the
   standard polynomial family satisfies. Taken literally (a family only known to be good on `{0,1}^m`),
   the protocols would not be sound: a linear family can vanish on a fixed non-0/1 difference vector while
   having small collision probability on `{0,1}^m`.

## Typos and small slips

* Protocol 1, line 3: `N_ρ(v)` "the vector whose `v`-th coordinate is 1 iff there exists `c ∈ C(v)` with
  `ρ_c = v`" should be `ρ(N(v))` (as in eq. (1), Lemma 3.3 and Protocol 2); with `C(v)` the honest prover
  fails. We use `ρ(N(v))`.
* `d_v ∈ [n]` but the root has `d_r = 0`; we use `Fin n = {0, …, n−1}`.
* The soundness proof of Theorem 3.4 cites "Theorem 3.1" for Lemma 3.1.
* Theorem 3.6: "does not have a Locally Checkable Proof … of length `Ω(n²)`" should read "requires length
  `Ω(n²)`" (Theorem 1.2 states it correctly).
* Section 3.4: `x_A, x_B < V_A ∪ V_B` (garbled `∉`), and the dumbbell construction needs `v_A`, `v_B` to be
  corresponding vertices (`u_j^A`, `u_j^B`) for `G(F, F)` to be symmetric; we use `v_A = a vA`,
  `v_B = b vA`. The claim "`G(F_A, F_B)` has a non-trivial automorphism iff `F_A = F_B`" also needs more
  than asymmetry and pairwise non-isomorphism of `𝓕` in general (e.g. no cut edges); we only use it for
  the concrete family of the counterexample, where it is proved.

## Modelling choices

* **Nodes and graphs.** Fixed finite vertex type `V` (identifiers known to all, as in the paper), network
  `G : SimpleGraph V`; `N(v)` contains `v` (`cnbhd`). Correctness is required on **connected** graphs
  (implicit in the paper: broadcasts and spanning trees need it; on a disconnected graph the depth checks
  reject anyway).
* **Locality** is enforced by the type: a node's decision receives `mask G v x` (values on `N(v)`, `none`
  elsewhere). Nodes may see their neighbours' challenges (as in the paper's lower-bound model); the upper-bound
  protocols only read their own.
* **Provers** are deterministic (`MAMProver`, `(V → R) → V → M`). Randomized provers are mixtures of
  deterministic ones, so `∃ P, Pr > 2/3` and `∀ P, Pr < 1/3` are unaffected.
* **Broadcast** messages are per-node copies plus neighbour comparison (the paper's convention).
* **Hash family**: `polyHash s x = ∑_q x_q s^{e(q)}` over `V × V` with a fixed enumeration `e`, seeds
  `s ∈ ZMod p` (so `|H| = p`); the paper only asserts existence.
* **Prime choice**: `theorem_3_4`, `theorem_3_5` hold for every prime `p ≥ 10 n³` (resp. `10 n^{n+2}`); the
  upper limits `100 n³`, `100 n^{n+2}` only matter for the cost, and `theorem_1_1`/`theorem_1_3` pick a prime
  in `(10 n³, 20 n³]` / `(10 n^{n+2}, 20 n^{n+2}]` by Bertrand.
* **Cost**: `InDMAM L ℓ` / `InDAM L ℓ` bound every alphabet (first message, challenge, second message) by
  `2^{ℓ(n)}`, i.e. `O(ℓ(n))` bits per node; Theorem 1.1 with `ℓ(n) = 30 (log₂ n + 1)`, Theorem 1.3 with
  `ℓ(n) = 30 n (log₂ n + 1)`.
* **Protocol 2's line 3** uses `ρ_u := ρ(u)` from each node's copy of `ρ`; after the neighbour comparison of
  the copies this is the paper's `ρ(N(v))`.
* **Lower-bound setting** (`LowerBound/Setup.lean`): vertices `a i`, `b i`, `xA`, `xB`; `𝓜_A`, `𝓜_B` as sets
  of responses; `μ_A` as a function `Set M → ℝ`; ℓ₁ distance as a finite sum.

## Not formalized

* Theorem 1.2 / 3.6 (DSym): the LCP lower bound is from [17]; the dAM upper bound is Protocol 1 with a fixed
  `σ` (note: there the root is again chosen after the challenges, so the union bound must run over the `n`
  roots; `2n(n²−1)/p < 1/3` still holds for `p ≥ 10 n³`).
* Lemma 3.7 (transformation into simple protocols), and the existence of a family `𝓕` of size `2^{Ω(n²)}`
  of asymmetric pairwise non-isomorphic graphs (cited).
* Section 4 (GNI ∈ dAMAM[O(n log n)], Theorem 1.5): the distributed almost-pairwise-independent hash is
  only sketched in the paper (no construction or proof is given in the proceedings version).
