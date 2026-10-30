# Beyond Alice and Bob: MaxIS inapproximability in CONGEST — PODC 2020

Yuval Efron, Ofer Grossman, Seri Khoury. *Beyond Alice and Bob: Improved Inapproximability for Maximum
Independent Set in CONGEST.* PODC 2020. DOI [10.1145/3382734.3405702](https://doi.org/10.1145/3382734.3405702).
Formalized version: arXiv [2003.07427](https://arxiv.org/abs/2003.07427) v2; numbering follows it.

**Verdict: 🛠️ Proof repaired.** The t-party framework (Theorem 5, Corollary 1) and the combinatorial heart
of the paper (Properties 1–3, Claims 1–7, Corollary 2, Lemmas 1–3) are correct. The round bounds of
Theorems 1 and 2 do not follow from the paper's proof as written: it miscounts the cut, which has
`Θ(log³ k)` edges, not `Θ(log² k)`, so the argument only gives `Ω(n/log⁴ n)` and `Ω(n²/log⁴ n)`. Both
theorems are nevertheless true. Using a code over a constant-size alphabet in the same construction
proves them, and even improves the bounds to `Ω(n/log² n)` and `Ω(n²/log² n)` rounds. As in the paper,
the Chakrabarti–Khot–Sun communication lower bound is a hypothesis.

## Mistakes in the paper

* **The cut is miscounted, so the claimed round bounds are not established by the proof.** In the proofs
  of Theorems 1 and 2 the paper uses `|cut(G_x̄)| = t² log² k`. In the construction of Section 4, however,
  `C^i_h` and `C^j_h` are joined by a complete bipartite graph minus a perfect matching. That is
  `(ℓ+α)(ℓ+α−1)` edges for each of the `ℓ+α` positions `h` and each pair `i<j`. So the cut has exactly
  `(t choose 2)·q²(q−1)` edges, `q = ℓ+α ≈ log k`, which is `Θ(t² log³ k)`. Corollary 1 then gives only
  `Ω(k/(log³ k · log n)) = Ω(n/log⁴ n)` (resp. `Ω(n²/log⁴ n)`). Changing `ℓ, α` does not help: with
  Reed–Solomon codes the alphabet has size at least the code length, and the cut is at least
  `(log k/log log k)³`.
  **Repair.** The construction never needs the alphabet to be as large as the code length. Take a code
  over an alphabet of constant size `Q = 4^D` (`D ≈ 2t/ε`), with length `M = log₂ k` and pairwise
  agreement `≤ M/D`; such a code exists by Gilbert–Varshamov. Give heavy nodes weight `M`. All claims go
  through with the same proofs, and the cut has `t(t−1)/2 · M · Q(Q−1) = O(log n)` edges. Corollary 1
  then gives `T·B·log n = Ω(n)` (resp. `Ω(n²)`), so `T = Ω(n/log² n)` (resp. `Ω(n²/log² n)`) for
  `B = O(log n)`. This implies the paper's claims. (`paper_cut_edges`; `theorem1`, `theorem2`)
* **The choice of `t` in the proof of Lemma 3 is too small; statement true.** The proof picks
  `t = 3/(4ε) − 1`. But the gap between Claims 6 and 7 has leading terms `3(t+1)ℓ` versus `4tℓ`, with
  ratio `3/4 + 3/(4t)`. For `t = 3/(4ε) − 1` this ratio exceeds `3/4 + ε`; for `ε = 1/8` and `t = 5` it is
  `0.9 > 0.875`. With the paper's own simplified bounds `3(t+2)` vs `4(t−1)` it is even `21/16 > 1` at
  `ε = 1/8`.
  Any `t ≥ 3/(2ε) + 3` works. (`lemma3`, `lemma3_paper`)
* **Corollary 1 needs a strict gap (proof gap).** With Definition 6 a γ-approximation may output weight
  exactly `γβ` in both cases, so it does not decide the gap predicate. We require `hi < γ·lo`. This is
  harmless: Lemmas 2 and 3 hold for every `ε`, so one uses `ε/2`. (`corollary1`)
* **Theorem 4 is stated for arbitrary alphabets.** Reed–Solomon codes need a field, and the paper takes
  `Σ = [ℓ+α]` of arbitrary size. We prove Theorem 4 for prime `q`. That is enough, since `ℓ+α` can be
  chosen prime. We neither prove nor refute the statement for other `q`. (`theorem4`)
* Typos and small slips:
  * Definition 5 reads `w(I) ≥ OPT/γ`; it should be `w(I) ≥ γ·OPT`. As written, no `(1/2+ε)`-approximation
    could exist.
  * In the proof of Claim 6 the weight is written `t(4ℓ+α)` instead of `4tℓ + 2tα`.
  * The proof of Lemma 3 has a sign slip (`4t log k − 2t log k/log log k`) and drops the constants of
    Claim 7 (`t²` for `3t³`).
  * The base cases of Claims 2 and 5 need `ℓ ≥ 1`, and the inductive step of Claim 5 needs `α ≥ 1`. Both
    are implicit in `ℓ ≫ α ≥ 1`.
  * Step (4) of Claim 4 sums `2ψ` over `i ≠ j ∈ [t]`, but step (6) counts unordered pairs.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous CONGEST (CSLib `Cslib.Congest.Algorithm`). The node set `V` is fixed and its names are the
  IDs. In each round a node sends `B` bits on every edge and direction. A node's input is its weight;
  randomized algorithms also give each node a private uniform random string. The output is one bit per
  node: membership in the independent set.
* `ApproxMIS A γ T ε`: on every graph with node set `V` and weights in `{0,…,n}`, after `T` rounds the
  output is an independent set of weight `≥ γ·OPT` with probability `≥ 1−ε`. Weights must be bounded:
  with unbounded weights no algorithm with bounded `T·B` could exist, and the theorems would be vacuous.
  The paper's instances have `O(log n)`-bit weights.
* Multi-party communication is the number-in-hand blackboard model (Definition 1). Protocols are trees
  in which the designated player writes one of `m` symbols, costing `⌈log₂ m⌉` bits. Randomized protocols
  have **private** coins. Promise pairwise disjointness uses the Chakrabarti–Khot–Sun promise: pairwise
  disjoint, or uniquely intersecting.
* **Hypothesis.** The CKS bound (Theorem 3) is assumed as `PPDLowerBound c`. It says that every
  private-coin protocol with error `≤ 1/3` and nonempty coin spaces writes at least `c·k/(t log₂ t)`
  bits. This is implied by CKS (public-coin, binary). Everything else is proved.
* The lower bounds are for infinitely many `n`, namely the sizes of the families. They hold against
  algorithms that may depend on `V`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definitions 1–2 (blackboard CC, promise pairwise disjointness) | `BBProtocol`, `RandComputes`, `PairwiseDisjoint`, `UniquelyIntersecting` | `Podc/.../CommunicationComplexity/Blackboard.lean` |
| Theorem 3 (CKS, hypothesis) | `PPDLowerBound` | `Podc/.../CommunicationComplexity/Blackboard.lean` |
| Theorem 4 (prime `q`) | `theorem4`, `rsCode_agree` | `Code.lean` |
| Definition 4, Theorem 5 | `MPFamily`, `MPFamily.simulation`, `rand_simulation`, `rand_lowerBound` | `Podc/.../Congest/MultiParty.lean` |
| Definition 5 (corrected), Corollary 1 | `IsApprox`, `ApproxMIS`, `corollary1_protocol`, `corollary1` | `Reduction.lean` |
| Section 4.1 construction | `graph`, `weight`, `linFamily` | `Linear.lean`, `Families.lean` |
| Properties 1–3 | `property1`, `property2`, `property3` | `Linear.lean` |
| Claims 1, 2, 3, 4, 5; Corollary 2 | `claim1`, `claim2`, `claim3`, `card_code_le`, `claim5`, `corollary2` | `Linear.lean` |
| Lemmas 1, 2 | `lemma1`, `lemma2`, `lemma2_paper` (Reed–Solomon instance) | `Linear.lean`, `Families.lean` |
| Section 5.1 construction | `graph2`, `weight2`, `quadFamily` | `Quadratic.lean`, `Families.lean` |
| Claims 6, 7; Lemma 3 | `claim6`, `claim7`, `lemma3`, `lemma3_paper` | `Quadratic.lean`, `Families.lean` |
| cut size (error) | `paper_cut_edges`, `card_linFamily_Ecut`, `card_quadFamily_Ecut` | `Families.lean` |
| Theorem 1 (repaired, stronger) | `theorem1` | `Theorem1.lean` |
| Theorem 2 (repaired, stronger) | `theorem2` | `Theorem2.lean` |
| non-vacuity | `exists_approxMIS` | `NonVacuity.lean` |

`theorem1`: for every `ε > 0` there is `C > 0` such that for infinitely many `n` there is a node set `V` of
size `n` such that every randomized algorithm satisfying `ApproxMIS A (1/2+ε) T (1/3)` has
`C·n ≤ T·B·log n`. `theorem2` is the same with `3/4+ε` and `C·n² ≤ T·B·log n`. The generic claims
(`claim5_generic`, `claim7_generic`, `card_code_le`) hold for any code with pairwise agreement `≤ a`. They
serve both the paper's Reed–Solomon parameters and the repaired constant-alphabet instance.

**Not formalized.** The CKS lower bound itself; Remark 1 (unweighted graphs); constant diameter of the hard
instances; Theorem 4 for non-prime alphabet sizes; the paper's real-valued parameter choice
`ℓ = log k − log k/log log k` (we use integer `q`, `α`).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `exists_approxMIS` builds, for every finite `V`, a full-information flooding
algorithm that outputs an exact maximum-weight independent set on every graph on `V` with weights `≤ |V|`,
so the hypothesis `ApproxMIS` of Theorems 1–2 is satisfiable. The CONGEST model comes from CSLib
(`Cslib.Computability.Distributed.Congest.LowerBound`). The multi-party framework is new (`Podc/`, CSLib
candidate).

**CSLib candidates** (staged in `Podc/`, marked `-- CSLib candidate`):
`Podc/Computability/CommunicationComplexity/Blackboard.lean` (blackboard protocols, promise pairwise
disjointness, CKS statement); `Podc/Computability/Distributed/Congest/MultiParty.lean` (t-party lower-bound
families, deterministic/randomized simulation); `Podc/Foundations/InformationTheory/Agreement.lean`
(`q`-ary Gilbert–Varshamov in agreement form).
