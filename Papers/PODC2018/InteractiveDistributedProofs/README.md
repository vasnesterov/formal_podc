# Interactive Distributed Proofs — PODC 2018

Gillat Kol, Rotem Oshman, Raghuvansh R. Saxena. *Interactive Distributed Proofs.* PODC 2018. DOI
[10.1145/3212734.3212771](https://doi.org/10.1145/3212734.3212771). Formalized version: the 10-page author
copy (full proofs; there is no arXiv version). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The upper bounds hold: `Sym ∈ dMAM[O(log n)]` (Theorem 1.1) and
`Sym ∈ dAM[O(n log n)]` (Theorem 1.3) are proved, after repairing a missing case in the protocols'
pseudocode (as written, Lemma 3.3 is false and Protocol 1 rejects `K_n`) and a gap in the soundness proof
of Protocol 2. **Lemma 3.11 is false**, so the paper's proof of the `Ω(log log n)` lower bound
(Theorem 1.4) does not work as written. It can be repaired by using the joint law of the bridge
challenges and `𝓜_A`. This repair gives `Ω(log log n)` when challenges have `O(L)` bits, as in
Definition 1, and it assumes the paper's family `𝓕` and its claim that `G(F_A, F_B)` is symmetric iff
`F_A = F_B`. The introduction's stronger claim, that the bound holds with unbounded shared randomness,
remains unproved.

## Mistakes in the paper

### ❌ Lemma 3.11 (the laws `μ_A(F)` are far apart)
Lemma 3.11 is false: a simple protocol that masks the bit "is `01` an edge?" with the bridge nodes'
coins decides `Sym` on the dumbbell class, yet `μ_A(F₁) = μ_A(F₂)` for the two 6-vertex graphs
`F₁` and `F₂ = F₁ + {01}` (`lemma_3_11_false`).

**Impact.** The paper's proof of the `Ω(log log n)` lower bound (Theorem 1.4) breaks; see the next
item for its repair. The upper bounds are unaffected.

**Details.** The lemma says that for distinct `F₁, F₂ ∈ 𝓕` the laws `μ_A(F₁)`, `μ_A(F₂)` of the
random sets `𝓜_A(F, r)` are at ℓ₁-distance `≥ 2/3`. The proof's separating "event", namely
"`𝓜_A(·, r)` meets `𝓜_B(F₁, r)`", depends on the challenge `r` itself, so it is not an event about
`𝓜_A(F, r)` alone. A correct protocol can hide `F` from the *marginal* law by masking with the
bridge nodes' coins. Take two asymmetric 6-vertex graphs `F₁` and `F₂ = F₁ + {01}`, and let `ι(F)`
be whether `01` is an edge, a bit that `v_A` sees locally. Each node draws one random bit, and the
bridge nodes both receive `(ι(F_A) ⊕ r_{x_A}, ι(F_B) ⊕ r_{x_B})`. `v_A` and `v_B` check their
halves, and `x_A`, `x_B` check that the two halves unmask to the same bit. This is a simple
protocol in the sense of Definition 6, and it decides `Sym` on the dumbbell class with probability
1 / 0. But `𝓜_A(F, r)` is a uniformly random singleton for both `F₁` and `F₂`.

**Repair.** `𝓜_A(F, r)` depends only on the A-side challenges and the two bridge challenges
`r_{x_A}`, `r_{x_B}`, and symmetrically for `𝓜_B`. So the two sets are independent once the bridge
challenges are fixed. Replacing `μ_A(F)` by the joint law of `((r_{x_A}, r_{x_B}), 𝓜_A(F, r))`
makes the lemma true (`lemma_3_11_repaired`, distance `> 2/3`).

### ❌ Theorem 1.4 (`Ω(log log n)` lower bound)
Theorem 1.4 is unestablished as proved, since its proof uses the false Lemma 3.11, and the
introduction's stronger claim that the bound holds with unbounded shared randomness remains
unproved.

**Impact.** Repaired for challenges of `O(L)` bits, as in Definition 1, assuming the paper's family
`𝓕` and its claim that `G(F_A, F_B)` is symmetric iff `F_A = F_B` (`theorem_1_4_repaired`).

**Repair.** With the repaired Lemma 3.11, Lemma 3.12 bounds the family:
`|𝓕| < 5^{|R|²·2^{|M|}}` (`card_family_lt`). With `L`-bit challenges and responses this gives
`log |𝓕| < 3 · 2^{2^{L+1}}`, so `|𝓕| ≥ 2^{c n²}` forces `L ≥ log log n − O(1)`. The factor `|R|²`
is why the repaired argument needs bounded challenges.

### ⚠️ Protocol 1 (counts the root as a child): Lemma 3.3 and Theorem 3.4
As written, Protocol 1 lets the root be a child of `t_r`, so Lemma 3.3 is false on `K₂`
(`lemma_3_3_false`) and completeness (Theorem 3.4) fails on `K_n` for `n ≥ 2`
(`theorem_3_4_literal_false`).

**Impact.** A missing case in the pseudocode with evident intent: the proof of Lemma 3.3 builds the
tree from `t_v` for `v ≠ r` only. With that fix Lemma 3.3 and Theorem 3.4 hold (`lemma_3_3`,
`theorem_3_4`); soundness is unaffected. Protocol 2 has the same line, and we formalize it repaired.

**Details.** The prover gives *every* node a parent `t_v`, and `C(v) = {u ∈ N(v) | t_u = v}` with
`v ∈ N(v)`. If the root's own pointer lies in `N(r)`, the root becomes a child of `t_r`. Summing all
the tree checks then gives `h_i(∑_v [v, N(v)]) = 0` instead of pinning down `a_r`. Lemma 3.3 fails
on `K₂` with `t_0 = t_1 = 0` and index `i = -1`: all nodes accept, but `a_r = 1 ≠ 0 = h_i(A)`. On
`K_n`, `t_r ∈ N(r) = V` is unavoidable, so every prover is accepted only with probability
`≤ (n² − 1)/p`.

### ⚠️ Theorem 3.2 (domain `{0,1}^m`)
Theorem 3.2 is stated on `{0,1}^m`, but it is applied to sums `∑_v [ρ(v), ρ(N(v))]` with entries in
`{0,…,n}` for non-injective `ρ`.

**Impact.** The intended domain is evident: the linearity clause already adds vectors mod `p`. We
prove it on `(ZMod p)^m` for the polynomial family (`theorem_3_2`).

### Typos and slips
- In Protocol 1, line 3, `N_ρ(v)` is defined through `C(v)` instead of `N(v)`.
- The protocol uses `d_v ∈ [n]` but needs `d_r = 0`.
- The proof of Theorem 3.4 cites "Theorem 3.1" for Lemma 3.1.
- Theorem 3.6 says "does not have an LCP … of length `Ω(n²)`" instead of "requires `Ω(n²)`".
- The ball in Lemma 3.12 is written with `‖µ − η‖`.
- The dumbbell needs corresponding `v_A`, `v_B`.

## Proof gaps (statements true)

### 🛠️ Theorem 3.5 (dAM protocol, soundness)
The proof fixes a root `r₀` and union-bounds over the `n^n` maps `σ`, but in a dAM protocol the
prover names the root, and the index `i = i_r` it must echo, after seeing the challenges, so it can
pick any node with a bad index.

**Impact.** Statement true with the paper's parameters (`Protocol2.soundness`, `theorem_3_5`).

**Repair.** Also union-bound over the root and use that `ρ` is broadcast as a permutation:
`n · n!` pairs, and `2 n · n! (n² − 1)/p < 1/3` for the paper's `p ≥ 10 n^{n+2}` since
`n! ≤ n^{n−1}`.

### 🛠️ Lemma 3.12 (packing bound)
The ℓ₁ balls are cut down to `[0,1]^d`, so their volumes depend on the centre, and the volume
formula `(4r)^d/(d+1)!` is wrong.

**Impact.** Statement true (`lemma_3_12`): full balls in `ℝ^d` and Haar-measure scaling give
`|U| ≤ 5^d − 3^d`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Fixed finite node set `V` (identifiers known to all), network `G : SimpleGraph V`. Correctness is
  required on connected graphs. `N(v)` contains `v`.
* One prover that sees `G`. Challenges are independent and uniform: hash indices in `ZMod p` for the
  upper bounds, any finite alphabet for the lower bound. Probability is counting (`uprob`).
* Provers are deterministic functions of all challenges, which is no loss against randomized provers.
* A node's decision receives only its masked local view: identifiers, messages and challenges of `N(v)`.
  Locality is therefore built into the type of a protocol.
* dMAM is prover → nodes → prover, dAM is nodes → prover. Broadcasts are per-node copies compared with
  the neighbours.
* Cost: `InDMAM`/`InDAM` bound every message alphabet by `2^{ℓ(n)}`. Theorem 1.1 uses
  `ℓ = 30 (log₂ n + 1)` and Theorem 1.3 uses `ℓ = 30 n (log₂ n + 1)`.
* Hash family: the polynomial hash `h_s(x) = ∑_q x_q s^{e(q)}` over `V × V`, with `s ∈ ZMod p`.

**Main results in Lean.** Namespace `Podc.InteractiveDistributedProofs` (`Protocol1.`, `Protocol2.`,
`LowerBound.` sub-namespaces).

| Paper | Lean | File |
|---|---|---|
| Definition 3 (`Sym`) ↔ nontrivial automorphism group | `Sym`, `sym_iff_nontrivial_aut` | `Basic.lean` |
| Observation 1 | `observation_1` | `Basic.lean` |
| Lemma 3.1 (and converse) | `lemma_3_1`, `permSum_eq_adjSum` | `Basic.lean` |
| Theorem 3.2 (on `(ZMod p)^m`) | `theorem_3_2`, `card_collision_le` | `Hash.lean` |
| Model (Definitions 1, 2; dMAM; classes) | `MAMProtocol`, `AMProtocol`, `Decides`, `InDMAM`, `InDAM` | `Model.lean` |
| Tree-sum checks (summation argument) | `treeSum_root`, `exists_treeSol` | `TreeSum.lean` |
| Lemma 3.3 (repaired / literal / false) | `Protocol1.lemma_3_3`, `lemma_3_3_literal`, `lemma_3_3_false` | `Protocol1.lean`, `Lemma33Counterexample.lean` |
| Theorem 3.4 (repaired) | `Protocol1.theorem_3_4` (`soundness`, `completeness_one`) | `Protocol1.lean` |
| Theorem 3.4 fails as written | `Protocol1.theorem_3_4_literal_false` | `Protocol1.lean` |
| Theorem 1.1 | `Protocol1.theorem_1_1` | `Protocol1.lean` |
| Theorem 3.5 | `Protocol2.theorem_3_5` (`soundness_bound`) | `Protocol2.lean` |
| Theorem 1.3 | `Protocol2.theorem_1_3` | `Protocol2.lean` |
| Lemma 3.11 is false | `LowerBound.lemma_3_11_false` | `LowerBound/Counterexample.lean` |
| Lemma 3.12 | `LowerBound.lemma_3_12` | `LowerBound/Packing.lean` |
| Lemma 3.8, Lemma 3.9, Corollary 3.10 | `LowerBound.lemma_3_8`, `lemma_3_9`, `corollary_3_10` | `LowerBound/Repair.lean` |
| Lemma 3.11 (repaired: joint law with bridge challenges) | `LowerBound.lemma_3_11_repaired` | `LowerBound/Repair.lean` |
| Theorem 1.4 (repaired, bounded challenges) | `LowerBound.card_family_lt`, `theorem_1_4_repaired` | `LowerBound/Repair.lean` |

**Not formalized.** Theorem 1.2/3.6 (DSym; the LCP lower bound is from [17]), Lemma 3.7 (the lower bound is stated
for simple protocols), the existence of large families `𝓕` and the dumbbell symmetry claim (hypotheses
`hF`, `hiff` of the repaired theorem; `hiff` is proved for the counterexample family), and Section 4 (GNI, Theorem 1.5, only sketched in the paper).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The asymmetry and non-isomorphism facts in the counterexample are checked by `decide +kernel`
on colour-refinement certificates (`LowerBound/ColourRefinement.lean`). Non-vacuity: the completeness
theorems exhibit accepted honest provers, and the counterexample protocol is shown to satisfy every
hypothesis of Lemma 3.11. The probability library is CSLib's `Cslib.Probability.uprob`.
CSLib candidates: the dAM/dMAM model (`Model.lean`), `TreeSum.lean`, the polynomial hash (`Hash.lean`),
the packing lemmas in `LowerBound/Packing.lean`, `LowerBound/ColourRefinement.lean`, and two probability
lemmas in `LowerBound/Repair.lean` (`uprob_eq_sum_uprob_key`, `sum_mul_sub_sum_mul_le_half_l1`).
