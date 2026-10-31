# Byzantine Broadcast with Local Linear Coding (NAB) — PODC 2012

Guanfeng Liang, Nitin Vaidya. *Byzantine broadcast in point-to-point networks using local linear coding.*
PODC 2012. DOI [10.1145/2332432.2332492](https://doi.org/10.1145/2332432.2332492). Formalized version: arXiv
[1106.1845](https://arxiv.org/abs/1106.1845) v3 ("Network-Aware Byzantine Broadcast in Point-to-Point Networks using
Local Linear Coding"). Its numbering matches the proceedings version.

**Verdict: ⚠️ Minor statement issues.** Theorem 1 holds as stated: random coding matrices make the Equality Check
correct with probability ≥ `1 − 2^{−L/ρ}·C(n, n−f)(n−f−1)ρ`. It is proved for every finite field, given that each
`H ∈ Ω_k` carries `ρ` edge-disjoint spanning trees. The paper gets these trees from the cited Nash-Williams–Tutte
theorem. Lemma 2 holds once a typo in the field size is fixed. Lemma 1 is false when the field is small
(`2^{L/ρ} ≤ (n−f−1)/2`, `ρ` even). That case lies outside the regime the paper works in (large `L`). The proof that `A_q` is invertible
(Appendix C.3) has a gap; the claim itself is true. Theorem 3 is correct arithmetic.

## Mistakes in the paper

* **Lemma 1 fails for small fields.** Lemma 1 says that for any `ρ_k ≤ U_k/2`, `M̃_H` is invertible with probability
  at least `(1 − (n−f−1)/2^{L/ρ_k})^{ρ_k}`. Suppose `2^{L/ρ_k} < (n−f−1)/2` and `ρ_k` is even. Then the base
  `1 − (n−f−1)/2^{L/ρ_k}` is below −1 and the bound exceeds 1. When the base is exactly −1, the lemma claims that
  `M̃_H` is *always* invertible. Example: `n = 7`, `f = 2`, `H = K_5` with every link of capacity 2 (`U_k = 16`),
  `ρ_k = 2`, `L = 2`. The field is then GF(2) and the bound is `(1 − 4/2)² = 1`, but the all-zero coding makes `M̃_H`
  singular. The induction multiplies `Pr[M_q invertible] ≥ (1−w/q)^q` by the factor `1 − w/q`, which may be
  negative. The lemma holds when `n−f−1 ≤ |F|`, and we prove it under that hypothesis. Theorem 1 only needs
  `det M̃_H ≢ 0`, so it is unaffected. This is a minor issue: the paper states that NAB "is intended to be
  used for sufficiently large L", Theorem 1 itself is only meaningful for `2^{L/ρ} > C(n,n−f)(n−f−1)ρ`, and in
  that regime Lemma 1 holds (`lemma_1_false_small_field`; repaired: `TreePacking.lemma_1`).
* **Appendix C.3: the invertibility argument for `A_q` has a gap.** The argument uses only three facts:
  1. some column of `A_q` has a single nonzero entry;
  2. every row has a nonzero entry;
  3. no two columns have the same support.

  It never uses that the edges form a tree. The incidence matrix of the edges `(1,5), (2,3), (3,4), (4,2)` (root 5)
  has all three properties and is singular. The claim is still true: if `D·A_q = 0`, then `D` takes equal values at
  the two ends of every tree edge, and connectivity forces `D = 0`. Our proof uses exactly this, over any field
  (`c3_argument_insufficient`; repaired: `TreePacking.det_A_ne_zero`).
* Typos and small slips:
  - Lemma 2 and the text before it take the diagonal entries from `GF(2^{ρ_k})` and give the bound `1 − w/2^{ρ_k}`.
    The field is `GF(2^{L/ρ_k})`, so the bound is `1 − w/2^{L/ρ_k}`, as Lemma 2 is used in (16) (`lemma_2`).
  - In (11) the first two blocks of `P_q` are both written `A_{q+1}S_{q+1,1}`. In (8) two blocks are written
    `A_{ρ_k}C_{ρ_k,ρ_k}` instead of `A_{ρ_k}S_{ρ_k,p}`. (12)–(13) write `S_{1,k+1}` and `M_{k+1}` for `S_{1,q+1}`
    and `M_{q+1}`.
  - Proof of Lemma 2: `R` for `W`, and `det(S − R)`.
  - The definition of `U_k` has `Ω` where it means `Ω̄_k`. `Ω_k` must consist of *induced* subgraphs, otherwise
    `|Ω_1| = C(n, n−f)` and `U_k > 0` fail.
  - Section 5.1 sets `ρ* = U_1/2`, which can be a non-integer. `ρ_k` must be an integer dividing `L`. Rescaling the
    time unit (doubling all capacities) repairs this.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **One Equality Check (Algorithm 1) on the graph `G_k`.** Nodes form a finite type `V` with `|V| = n` and
  `3f < n`. `z a b` is the integer capacity of link `(a, b)` of `G_k`. A coded symbol (`Sym z`) is one unit of
  capacity of one link. The coding matrices are one function `c : Sym z × Fin ρ → F` over an arbitrary finite
  field `F`; `theorem_1_galois` instantiates `F = GF(2^{L/ρ})`.
- **Values and faults.** Each node holds its Phase-1 value as `X i : Fin ρ → F`. Synchronous, one round, no
  forwarding. Byzantine faults: faulty senders send arbitrary symbols `Y`, while fault-free senders send
  `X_i C_e` and fault-free receivers check `Y_e = X_j C_e`.
- **Admissible faulty sets.** At most `f` nodes, containing every node already removed from `V_k` and one node of
  every pair found in dispute. This is exactly what dispute control (Phase 3) guarantees.
- **Correctness.** `Correct` is property (EC): if no fault-free node detects a mismatch, all fault-free nodes hold
  equal values. It is quantified over all admissible faulty sets, all values `X` and all faulty behaviour `Y`.
- **Randomness.** The coding entries are i.i.d. uniform on `F`. Probability is counting (`Cslib.Probability.uprob`).
- **Hypothesis `ρ_k ≤ U_k/2`.** We use it in the form the paper actually uses. Each `H ∈ Ω_k` carries `ρ`
  edge-disjoint unit-capacity undirected spanning trees (`TreePacking`). The paper gets these from the
  Nash-Williams–Tutte packing theorem [16], which is not formalized. `TreePacking.star` and `theorem_1_complete`
  show that the hypothesis is met, e.g., when all capacities are `≥ ρ`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 | `theorem_1` | `Theorem1.lean` |
| Theorem 1 over `GF(2^{L/ρ})` | `theorem_1_galois` | `Examples.lean` |
| Theorem 1, no packing hypothesis (all capacities `≥ ρ`) | `theorem_1_complete` | `Examples.lean` |
| App. C.1: invertible `M̃_H` ⇒ all nodes of `H` agree | `TreePacking.eq_root_of_det_ne_zero` | `EqualityCheck.lean` |
| App. C.1/C.2: (EC) from `∏_H det M̃_H ≠ 0` | `correct_of_det_ne_zero` | `Theorem1.lean` |
| Lemma 1 (with `n−f−1 ≤ \|F\|`) | `TreePacking.lemma_1`, `lemma_1_blockM` | `Lemma1.lean` |
| Lemma 1 false for small fields | `lemma_1_false_small_field` | `Counterexample.lean` |
| Lemma 2 (field size fixed) | `lemma_2` | `Lemma1.lean` |
| App. C.3 (`A_q` invertible) | `TreePacking.det_A_ne_zero` | `EqualityCheck.lean` |
| App. C.3 argument insufficient | `c3_argument_insufficient` | `Counterexample.lean` |
| Eqs. (24)–(28) (throughput limit) | `throughput_eventually_ge`, `tendsto_throughput_Q`, `tendsto_throughput_L` | `Throughput.lean` |
| Theorem 3 (given Theorem 2) | `theorem_3` | `Throughput.lean` |

**Proof route for Theorem 1.** We do not go through Lemma 1. To show `det M̃_H ≢ 0`, we evaluate it at an explicit
coding: the symbol of tree `q` carries coordinate `q` only. There `M̃_H` is block-diagonal with blocks `A_q`. Then
Schwartz–Zippel applies to `∏_{H∈Ω_k} det M̃_H`, which has total degree `≤ |Ω_k|(n−f−1)ρ`. This gives the
paper's bound for every field size.

**Not formalized.**
- Theorem 2, the information-theoretic capacity upper bound. It enters Theorem 3 as a hypothesis.
- The Nash-Williams–Tutte packing theorem.
- Phases 1 and 3 and the multi-instance protocol: unreliable broadcast via spanning trees, dispute control,
  1-bit Byzantine broadcasts, and the time bound (24), which enters as a hypothesis.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Non-vacuity: `TreePacking.star` builds packings and `theorem_1_complete` discharges the packing hypothesis. The
shared Schwartz–Zippel wrapper is staged in `Podc/Probability/Finite/SchwartzZippel.lean`.

**CSLib candidates.**
- `Podc/Probability/Finite/SchwartzZippel.lean`: Schwartz–Zippel for an arbitrary finite variable type, in
  `uprob` form.
- In `Lemma1.lean`: `uprob_comp_equiv` and `uprob_comp_injective` (restricting a uniform function along an injection
  is uniform).
- In `EqualityCheck.lean`: `totalDegree_det_le` (Mathlib candidate).
