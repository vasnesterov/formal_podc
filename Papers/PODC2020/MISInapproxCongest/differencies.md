# Differences between the formalization and the paper

Paper: Y. Efron, O. Grossman, S. Khoury, *Beyond Alice and Bob: Improved Inapproximability for Maximum
Independent Set in CONGEST*, PODC 2020 (arXiv:2003.07427v2; numbering follows it).

Classification: **false statement** / **false only in a degenerate case** / **proof gap (statement true)** /
**under-specified definition** / **typo** / **modelling choice**. Verdict rules: `verdicts.md` (R1–R6).

## Verdict reasoning

* No numbered statement checked here is false. The serious error is the cut count inside the proofs of
  Theorems 1 and 2 (item 1). Theorems 1 and 2 themselves are proved, conditional on Theorem 3 like the
  paper, by a repaired argument that uses a different code. By R1 a false claim inside a proof whose
  result is true is a proof repair, so the verdict is 🛠️.
* Borderline call: the repair changes an ingredient of the construction (the code). The *statements* of
  Theorems 1 and 2 are unchanged and are even strengthened. They are existential lower bounds on all
  algorithms, so the change of construction is a change of proof, not of claim. We therefore classify
  this as 🛠️ and not as ❌ ("headline unestablished"). Had the theorems been tied to the paper's specific
  family, ❌ would apply: the paper's argument with its own construction yields only `Ω(n/log⁴ n)`.

## Main issues

1. **Cut size (proof gap in Theorems 1 and 2; statements true).** The proofs use
   `|cut(G_x̄)| = t² log² k` (Thm 1) and `Θ(t² log² k)` (Thm 2). The construction has exactly
   `(t choose 2)·q²(q−1)` cut edges with `q = ℓ + α` (Thm 2: twice that), i.e. `Θ(t² log³ k)`
   (`paper_cut_edges`, `card_linFamily_Ecut`, `card_quadFamily_Ecut`; `Ecut` counts ordered arcs, i.e. twice
   the edges). Corollary 1 with this cut gives `Ω(n/log⁴ n)` and `Ω(n²/log⁴ n)`. Repaired: `theorem1`,
   `theorem2` use a Gilbert–Varshamov code over the constant alphabet `Fin (4^D)` (`D = ⌈2t/ε⌉ + 2`),
   length `M`, `2^M` messages, pairwise agreement `≤ ⌊M/D⌋` (`Cslib.exists_code_agree_le`). Heavy nodes get
   weight `M`. The cut has `O(M) = O(log n)` edges, and the results are `T·B·log n ≥ C n` and `≥ C n²`.
   These are stronger than the paper's `Ω(n/log³ n)`, `Ω(n²/log³ n)` for `B = O(log n)`.
2. **Lemma 3, choice of `t` (proof slip; statement true).** `t = 3/(4ε) − 1` is too small (see README). We
   use `t = ⌈3/(2ε)⌉ + 3` and the condition `3αt² ≤ 2εℓ` (`lemma3_gap`). Lemma 2's `t = 2/ε` is fine; we
   use `t = ⌈1/ε⌉ + 3` with `αt ≤ εℓ` (`lemma2_gap`).
3. **Corollary 1 / Definition 6, strictness (proof gap).** A γ-approximation algorithm separates
   "OPT ≥ β" from "OPT ≤ γ'β" only if `γ' < γ`; Definition 6 allows `γ' = γ`. `corollary1` assumes
   `hi < γ·lo`. In the applications we take the family for `ε/2` (more precisely, we prove the strict
   inequality directly in `lin_gap`, `quad_gap`).
4. **Theorem 4 (cited; over-general statement).** It is stated for any alphabet of size `q`, while the
   cited source (Reed–Solomon / Arora–Barak Lemma 19.11) needs a field. Proved for prime `q`
   (`theorem4`; distance `≥ M − L`, in fact `M − L + 1`). The paper's parameters can always be chosen with
   `ℓ + α` prime, so nothing else depends on this. Status for composite `q`: not investigated. Not counted
   for the verdict, since it is not formalized in that generality.

## Definitions and model

5. **Definition 5 (typo).** `w(I) ≥ OPT/γ` replaced by `w(I) ≥ γ·OPT` (`IsApprox`).
6. **What "an algorithm finds a γ-approximation" means (under-specified; modelling choice).** Each node
   outputs one bit (membership). The output must be an independent set of weight `≥ γ·OPT` with
   probability `≥ 2/3` on every graph with node set `V` and weights in `{0,…,|V|}` (`ApproxMIS`). The paper
   does not bound the weights. Without a bound the hypothesis is unsatisfiable for any finite `T·B`, which
   would make the theorems vacuous. Our hard instances use weights `≤ M ≤ n`. The theorems only use
   correctness on the family's graphs, so they hold a fortiori for algorithms working on all graphs.
7. **Randomness.** Private uniform random strings per node, finite coin types (`Fintype ρ`, nonempty). The
   simulation makes the protocol private-coin (player `i` draws the strings of `V^i`).
8. **CONGEST bandwidth.** `B` bits per edge, direction and round, with `B` a parameter. The results are
   stated as bounds on `T·B`; the paper's `O(log n)` is the case `B = Θ(log n)`.
9. **Theorem 3 (CKS) as hypothesis** `PPDLowerBound c`: `∀ t ≥ 2`, every private-coin blackboard
   protocol with nonempty coin spaces that computes PPD with error `≤ 1/3` on inputs that are pairwise
   disjoint or *uniquely intersecting* (CKS's promise, narrower than the paper's Definition 2, so the
   hypothesis is weaker) costs `≥ c·k/(t log₂ t)`. The cost charges `⌈log₂ m⌉` bits per `m`-ary symbol and
   maximizes over all branches. This cost is at least the binary transcript length, so the hypothesis is
   implied by CKS. Nonempty coins avoid the degenerate hypothesis (empty coin space ⇒ zero error count).
10. **Definition 4.** Formalized as `MPFamily`: graphs and node inputs indexed by all inputs, a partition
    `part : V → ι`, edges inside `V^i` and inputs of `V^i` depend only on `x^i`, and cut edges are fixed
    and listed (as ordered pairs) in `Ecut`. The paper only says "the existence of edges in `V^i × V^i` may
    depend on `x^i`" and leaves implicit that the cut edges are input-independent. This is needed for
    `|cut(G_x̄)|` to make sense.
11. **Theorem 5.** Proved with explicit constants: cost `≤ T·|Ecut|·B + |ι|` for decision, and
    `T·|Ecut|·B + |ι|·⌈log₂ |S|⌉` with per-player summaries (`MPFamily.simulation`, `rand_simulation`,
    `rand_lowerBound`). The paper writes `O(T|cut| log |V|)`.
12. **Corollary 1.** The players learn `w(I)` from the summaries `w(I ∩ V^i)`, at `t·⌈log₂(|V|W+1)⌉` extra
    bits. The paper does not mention this step. It requires `t ≥ 2`, so that the two promise cases are
    disjoint.

## Constructions and claims

13. **Generic code.** Section 4 is formalized for an arbitrary code `c : K → P → A` with pairwise
    agreement `≤ a` (positions `P`, `|P| = M`; alphabet `A`), heavy weight `W`. The paper's instance is
    `P = A = [ℓ+α]`, `W = ℓ`, `a = α`. The paper-form statements assume `|P| = ℓ + α` and agreement `≤ α`.
    `lemma2_paper` / `lemma3_paper` instantiate them with Reed–Solomon over `ZMod q`, `q = ℓ+α` prime.
14. **Property 2** is stated as "at `≥ M − a` positions the two code nodes are adjacent". These edges
    belong to different cliques `C_h` and hence form a matching. Property 3 bounds the common positions by
    the agreement of the codewords (`≤ α`).
15. **Claim 4** is proved in the sharper form `|I ∩ ⋃_{i∈S} Code^i_{m_i}| ≤ M + a·(|S| choose 2)`
    (`card_code_le`), which implies the paper's `ℓ + αt²`. It is used for arbitrary subsets of copies,
    which Corollary 2 and Propositions 1, 3 need ("apply Corollary 2 on the graph induced by …").
16. **Corollary 2** is stated for `t ≥ 1`, as in the paper ("positive integer `t`").
17. **Claims 5 and 7: induction replaced by direct counting.** The proofs split the copies into those with
    heavy node(s) in `I` (handled by Claim 4 / Propositions 1–3) and the others. This avoids the paper's
    induction on `t` over induced subgraphs, which needs the claim for subfamilies. Hypotheses:
    Claim 5 needs `t, ℓ, α ≥ 1` (the paper says "for any positive integer `t`" and uses `α ≥ 1`, `t > 2`;
    `t = 2` and `t = 1` also work, the latter with `ℓ ≥ 1`). Claim 2 needs `ℓ ≥ 1` (degenerate otherwise).
    Claim 7 holds for all `t ≥ 1`. We obtain `(3t+1)ℓ + …`, sharper than the stated `3(t+1)ℓ`.
18. **Claim 7, Proposition 1–3 bookkeeping.** The representatives of the classes are the minimal indices of
    each class. `Σ_j (q_j choose 2) ≤ (t choose 2)` replaces the paper's `αt²r ≤ αt³`.
19. **Lemmas 1–3: parameters.** The paper fixes `ℓ = log k − log k/log log k`, `α = log k/log log k` (not
    integers in general). We state the lemmas for all integers with `α ≤ εℓ`, `ℓ ≥ 1/ε` (Lemma 1),
    `αt ≤ εℓ` (Lemma 2), `3αt² ≤ 2εℓ` (Lemma 3). These conditions hold for the paper's parameters and large
    `k`.
20. **Theorems 1–2: quantifiers.** For every `ε > 0` there are `C > 0` and infinitely many `n` (the family
    sizes `t(2^M + MQ)`, resp. `2t(2^M + MQ)`) with a node set of size `n` on which every algorithm
    satisfies the bound. The paper states `Ω(·)` without specifying for which `n`. Padding to all `n` is
    not done. The paper restricts to `0 < ε < 1/2` (resp. `1/4`); we allow every `ε > 0`.
21. **Not formalized:** Remark 1 (unweighted instances), constant diameter of the instances, the CKS bound,
    Theorem 4 for non-prime alphabets.
