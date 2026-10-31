# Randomized Proof-Labeling Schemes — PODC 2015

Mor Baruch, Pierre Fraigniaud, Boaz Patt-Shamir. *Randomized Proof-Labeling Schemes.* PODC 2015.
DOI [10.1145/2767386.2767421](https://doi.org/10.1145/2767386.2767421). Formalized version: the 10-page
author copy (no arXiv version; the proof of Theorem 3.6 is omitted there).

**Verdict: ❌ False claim.** The main message holds. Theorem 3.1 holds: a PLS with `κ`-bit labels
becomes a one-sided RPLS with `2 log₂ κ + 6`-bit certificates. Corollary 3.5 holds: `O(log n + log k)`
certificates for every predicate. The crossing lower bounds hold for a legal `G` (Propositions 4.3,
4.6, 4.8; Theorems 4.4 and 4.7 in that case), and so do the acyclicity bounds of Theorem 5.1. But
Theorems 4.4 and 4.7, and Proposition 4.3, are stated for any `G` with `P(G) ≠ P(σ(G))`. They are
false when `G` is illegal and all its crossings are legal.

## Mistakes in the paper

* **The crossing tool fails for an illegal `G` (Proposition 4.3, Theorems 4.4 and 4.7).**
  Theorems 4.4 and 4.7 only ask that every crossing flips the predicate: `P(G_s) ≠ P(σ^{ij}₁(G)_s)`.
  The proof of Proposition 4.3 covers the case "`G_s` is rejected" with a single labelling of `G`
  (the pigeonholed prover labels). Rejection of the crossing, though, is about *every* labelling,
  and a legal crossing comes with its own prover labels.

  *Counterexample.* Take the windmill: a hub joined to `L_k` and `R_k` (`k < r`), plus the edges
  `L_k R_k`. These `r` edges are independent port-preserving copies of one edge (`s = 1`). States are
  identities, `F` is `G` together with its crossings, and `P` says "some `(k,·)` has a neighbour
  `(k',·)` with `k' ≠ k`". So `P(G)` is false and every crossing is legal, and all configurations
  are connected. A PLS with `3 + log₂ log₂ r` bits exists:
  * a crossed `L_k` raises a flag, and the hub checks that some flag is up;
  * each `R_m` publishes a bit position `t` and the bit `m_t`, and checks them;
  * a flagged `L_k` checks that its port-0 neighbour's bit differs from `k_t`.

  In `G`, the flagged `L_k` faces `R_k`, so `G` is rejected under every labelling.
  * Theorem 4.4 promises `Ω(log r / s) = Ω(log r)` bits (`thm_4_4_false`).
  * Compiling this PLS with Theorem 3.1 gives an edge-independent two-sided RPLS with
    `O(log log log r)` bits. Theorem 4.7 promises `Ω(log log r)` bits (`thm_4_7_false`).
  * For `r = 2^32` and 8-bit labels, Proposition 4.3 fails for every pair: `G` is rejected and the
    crossing is accepted (`prop_4_3_false`).

  All applications in Section 5 use a legal `G`. In that case we prove the tools
  (`prop_4_3`, `thm_4_4`, `thm_4_7_correct`, `prop_4_8`).
* **Proposition 4.6: a wrong step in the proof (statement true).** The proof rounds the *joint*
  distribution of the certificates of a copy. Eq. (6) then uses that one arc's *marginal* is
  `ε`-close, but equal joint roundings only give closeness `ε·2^((2s−1)κ)`. The chosen `ε` happens to
  absorb this factor (the total error is exactly `1/3`), so Eqs. (6)–(8) need fixing, but the
  conclusion survives. We round each arc separately and get `log₂ log₂ r ≤ 2κ + 5 + 2 log₂ s`
  (`prop_4_6`, `thm_4_7_loglog`).
* **Theorem 5.1 applies Theorem 4.7 outside its hypotheses (proof gap).** The crossed path is not in
  `F`; the proof uses its cycle component instead. This is sound because verification is local. We
  state the tools for crossings whose union of components is an illegal member of `F` (`Refuted`).
* **Smaller slips.**
  * Propositions 4.3, 4.6 and 4.8 count as if every label or certificate had exactly `κ` bits. With
    "at most `κ` bits" there are `2^(κ+1) − 1` strings, so our thresholds read
    `r ≤ (2^(κ+1)−1)^(2s)` (Prop. 4.3) and `r ≤ 2^((2^(κ+1)−1)·2s)` (Prop. 4.8). The asymptotics
    are the same.
  * Lemma 3.4 (cited) silently needs connected configurations, distinct identities and an
    isomorphism-invariant `P`; all three hold in the paper's model.
  * In the proof of Theorem 5.4 the first copy is printed as `H_1 = G_e{v₀, v₁}`. `v₀` is adjacent
    to every other node, so this copy is not independent of the others
    (`printed_H1_not_independent`); `{v₁, v₂}` as in Theorem 5.2 is clearly meant.
  * Theorem 5.6's graph ("`n/c` cycles, except one of at most `c` nodes") is vague when the leftover
    has 1–2 nodes; we take `n = m·c`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Configurations.** A configuration is port-numbered: a finite node type, neighbour lists by port,
  and states, which carry identities when the paper assumes them (`Config`, `Basic.lean`). Networks
  are connected wherever the paper needs it. The Section 5 lower bounds hold for every family that
  contains the connected configurations with distinct identities (`hFF`).
- **Verification.** One synchronous round, no failures.
  - PLS: the verifier sees its state, its label and its neighbours' labels by port. Labels are bit
    strings.
  - RPLS: every node draws private uniform coins. The coin space may depend on the node's state,
    label and degree, and so may the certificate it sends on each port. The decision is a function
    of the state, the label and the certificates received.
  - One-sided means acceptance with probability `1` and rejection with probability `≥ 1/2`;
    two-sided means `2/3` on both sides. Edge independence means one coin per port (`EIScheme`).
- **Complexity.** Verification complexity is a bound on label (resp. certificate) length on legal
  configurations. It may depend on the configuration, e.g. on `n`.
- **Crossings.** Crossings are built from `r` pairwise independent port-preserving copies of a
  pattern graph (`Copies.cross`). They keep ports, states and degrees.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 3.3 (EQ fingerprint protocol) | `lemma_3_3` | `Fingerprint.lean` |
| Theorem 3.1 (PLS → one-sided RPLS, `2 log₂ κ + 6` bits) | `theorem_3_1`, `theorem_3_1_oneSided`, `theorem_3_1_twoSided` | `Compile.lean` |
| Lemma 3.4 (universal PLS) | `Universal.lemma_3_4` | `Universal.lean` |
| Corollary 3.5 (`O(log n + log k)`) | `cor_3_5` | `Universal.lean` |
| Definitions 4.1, 4.2 (crossing) | `Copies`, `Copies.cross` | `Basic.lean`, `Crossing.lean` |
| Proposition 4.3 (legal `G`) / as printed refuted | `prop_4_3` / `prop_4_3_false` | `LowerBound.lean` / `Refutations.lean` |
| Theorem 4.4 (legal `G`) / as printed refuted | `thm_4_4`, `thm_4_4_log` / `thm_4_4_false` | `LowerBound.lean` / `Refutations.lean` |
| Proposition 4.6 | `prop_4_6` | `TwoSided.lean` |
| Theorem 4.7 (legal `G`) / as printed refuted | `thm_4_7_correct`, `thm_4_7_loglog` / `thm_4_7_false` | `TwoSided.lean` / `Refutations.lean` |
| Proposition 4.8 | `prop_4_8`, `prop_4_8_log` | `LowerBound.lean` |
| Counterexample (windmill PLS) | `Windmill.isPLS`, `Windmill.labelBound`, `Windmill.connected_of_F` | `Counterexample.lean` |
| Theorem 5.1, acyclicity: upper bound `O(log log n)` | `thm_5_1_upper` | `Acyclicity.lean` |
| Theorem 5.1, acyclicity: lower bounds (det., one-sided, two-sided edge-indep.) | `thm_5_1_lower_det`, `thm_5_1_lower_oneSided`, `thm_5_1_lower_twoSided` | `AcyclicLower.lean` |
| Theorem 5.2, lower bounds (det. `Ω(log n)`, one-sided `Ω(log log n)`) | `thm_5_2_det`, `thm_5_2_rand` | `Biconnectivity.lean` |
| Theorem 5.4, lower bounds (det. `Ω(log c)`, one-sided `Ω(log log c)`) | `thm_5_4_det`, `thm_5_4_rand` | `CycleAtLeast.lean` |
| Theorem 5.6, lower bounds (det. `Ω(log n/c)`, one-sided `Ω(log log n/c)`) | `thm_5_6_det`, `thm_5_6_rand` | `CycleAtMost.lean` |

**Not formalized.**
- Lemma 3.2 (randomized EQ lower bound, cited) and Theorem 3.6 (its proof is omitted in the paper).
- The MST parts of Theorem 5.1, which need the KKP `O(log² n)` MST scheme. The `k`-flow remark.
- The upper bounds of Theorems 5.2 and 5.3: the paper only sketches them ("details omitted").
- Theorem 5.5.
- The two-sided edge-independent versions of Theorems 5.2–5.6. They follow from `thm_4_7_loglog`
  exactly as for Theorem 5.1, but we did not instantiate them.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
- *The tools are not vacuous.* The acyclicity lower bounds apply them to the path, with the
  upper-bound scheme as a witness that the hypotheses can be met.
- *The counterexample meets the paper's hypotheses.* It satisfies them, including connectivity
  (`Windmill.connected_of_F`) and distinct identities.
- *Sources.* Probability is CSLib's `Cslib.Probability.uprob`; the encoding is CSLib's `encList`.
  Acyclicity uses CSLib's `isAcyclic_of_rank` and `IsAcyclic.eq_of_dist_add_one`.

**CSLib candidates** (marked `-- CSLib candidate`):
- The port-numbered PLS/RPLS model with crossings and restrictions.
- The marginal lemmas `uprob_comp_restrict` and `uprob_apply_eq`.
- `card_filter_eval_eq_le` (two polynomials agree on few points).
- The product-distribution bound `abs_sum_mul_prod_sub_le`.
- `idxOf_map_injOn` and `idxOf_map_of_injective`.
- The graph lemmas in `GraphTools.lean`, e.g. `cycle_support_of_cut`: a cycle through a cut vertex
  stays in one block.
