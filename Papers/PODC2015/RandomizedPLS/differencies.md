# Differences between the formalization and the paper

Paper: M. Baruch, P. Fraigniaud, B. Patt-Shamir, *Randomized Proof-Labeling Schemes*, PODC 2015
(10-page author copy; the proof of Theorem 3.6 is omitted there). Verdict rules: `verdicts.md` of the
`formalize-paper` skill.

## Model

* **Configurations** (`Config`, `Basic.lean`): any finite node type, neighbours listed by port
  (ports `0, …, deg-1` instead of `1, …, deg`), states in an arbitrary type `S` (identities are part
  of the state when needed). Connectivity is a property families may require (`Config.Connected`),
  not built in. The paper always takes networks connected; every configuration we use in a
  counterexample is connected.
* **PLS** (`IsPLS`): verifier = function of (own state, own label, neighbours' labels by port);
  labels are bit strings (`List Bool`); verification complexity = a bound `κ c` on label lengths on
  legal configurations (`LabelBound`), so `κ` may depend on `n` or on anything else.
* **RPLS** (`RScheme`, `IsRPLS`): each node draws private coins uniformly from a finite space that may
  depend on its state, label and degree (the paper: "independent random bits"; uniform finite spaces
  are slightly more general and needed because adversarial labels are unbounded); the certificate on
  each port is a function of the coins (we also allow it to depend on the state and degree, which
  only strengthens our lower bounds); the decision is a deterministic function of state, label and
  received certificates, as in the paper. Labels of an RPLS can be of any type (their size is not
  measured, Definition 2.1); our upper bounds use `List (List Bool)` (a list of bit strings, which
  could be bit-encoded without affecting certificate sizes). One-sided: `pacc = 1, prej = 1/2`;
  two-sided: `pacc = prej = 2/3`. Edge independence (Definition 4.5) is structural (`EIScheme`).
* **Copies and crossings** (`Copies`, `Copies.cross`): `r` copies `emb i : W → V` of a pattern graph
  `H`, pairwise vertex-disjoint and non-adjacent (Definition 4.1), port-preserving. Crossing
  (Definition 4.2) keeps port numbers. The paper counts `|V(H_i)| ≤ 2s`; we pigeonhole on the
  non-isolated pattern vertices (`card_supp_le`), which gives the same count.
* **Refuted crossings** (`Refuted`): Theorems 4.4/4.7/Proposition 4.8 are stated with the hypothesis
  that each crossing, *or a union of its connected components*, is an illegal member of `F`. The
  paper's theorems require the crossing itself to be in `F`, but the proof of Theorem 5.1 applies
  them to a component ("`σ₁(P) ∉ F`, but `C` is a connected component of `σ₁(P)` and `C ∈ F`"). The
  restriction lemmas (`Restrict.lean`) justify this (locality; for probabilities, a marginal lemma).
  Proof gap in Theorem 5.1, repaired.

## Statement-level issues

1. **Proposition 4.3, Theorem 4.4 and Theorem 4.7 are false when `P(G) = FALSE`** (decided by R1/R3/
   R4/R5, see "Verdict" below). Theorems 4.4 and 4.7 assume `P(G_s) ≠ P(σ^{ij}₁(G)_s)` (checked on the
   rendered page 5). Proposition 4.3's proof also treats "`G_s` is rejected" explicitly, but transfers
   one labelling of `G` to the crossing, while rejection of the crossing concerns all of its
   labellings. Counterexample (`Counterexample.lean`, `Refutations.lean`): windmill `G_r` (hub +
   triangles `hub, L_k, R_k`), copies `L_k R_k` (`s = 1`), states = identities, `F = {G_r} ∪
   {crossings}`, `P` = "some node `(k,·)` has a neighbour `(k',·)` with `k' ≠ k`". All hypotheses
   hold, all configurations are connected, and `(F, P)` has a PLS with `3 + ⌊log₂ log₂ r⌋`-bit
   labels (`isPLS`, `labelBound`):
   * `thm_4_4_false`: no `C > 0, D` with `κ ≥ C log₂ r / s − D` for all instances;
   * `thm_4_7_false`: compiling with Theorem 3.1 gives an edge-independent one-sided (hence two-sided)
     RPLS with `O(log log log r)`-bit certificates, so no `κ ≥ C log₂ log₂ r / s − D`;
   * `prop_4_3_false`: for `r = 2^32`, 8-bit labels (so `κ < log r / 2s`), every pair `i ≠ j` has
     `G` rejected and the crossing accepted with the prover's labels.
   The case `P(G) = TRUE` (the only one used in Section 5) is proved: `prop_4_3`, `thm_4_4`,
   `thm_4_7_correct` (`TwoSided.lean`), and Proposition 4.8 (which the paper states only for
   `P(G) = TRUE`).
2. **Proposition 4.3 and 4.8: exact constants.** The paper counts `2s` labels of `< log r / 2s` bits
   as `< r` bit strings, i.e. as if all labels had exactly `κ` bits ("w.l.o.g. exactly κ bits" in
   Prop. 4.6/4.8). With labels/certificates of *at most* `κ` bits there are `2^(κ+1) − 1` of them. We
   prove `r ≤ (2^(κ+1) − 1)^(2s)` (Prop. 4.3/Thm 4.4, i.e. `κ + 1 ≥ log₂ r / 2s`) and
   `r ≤ (2^(2^(κ+1) − 1))^(2s)` (Prop. 4.8, i.e. `2s(2^(κ+1) − 1) ≥ log₂ r`). The printed thresholds
   `κ < log r / 2s`, `κ < (1/2s) log log r` are not proved as such (a refutation would need a scheme
   exploiting variable lengths; not attempted). Same asymptotics; proof imprecision.
3. **Theorem 3.1**: `O(log κ)` made explicit: `2⌈log₂ 3(κ+1)⌉ ≤ 2 log₂ κ + 6` bits; the scheme is
   one-sided with rejection probability `> 2/3`, so it is also two-sided, and edge-independent.
   Fingerprints over `GF(2^m)` (`Fingerprint.lean`) instead of an unspecified protocol from [32];
   the message has a length that depends on the label length, and labels of different lengths with
   different field sizes are rejected deterministically.
4. **Lemma 3.4 / Corollary 3.5** (`Universal.lean`): Lemma 3.4 is cited by the paper. Our universal
   scheme needs three assumptions implicit in the paper's model (R4): connected configurations,
   distinct identities in the states, and `P` invariant under port-preserving isomorphisms
   (`Config.Iso`); states are encoded injectively with `≤ k` bits. Label bound
   `2 log n + 4 + 2n(4k+3) + 4(2 log n + 3) Σ deg = O(nk + m log n)`; the paper's
   `O(nk + min{n², m log n})` also uses an adjacency-matrix variant for dense graphs (not formalized;
   irrelevant for Corollary 3.5). Corollary 3.5: certificates of `2 log₂(32(k+1)n³) + 6` bits.
5. **Proposition 4.6 / Theorem 4.7** (`TwoSided.lean`): explicit threshold
   `r > (12 s 2^(κ+1) + 2)^(2s·2^(κ+1))`, giving `log₂ log₂ r ≤ 2κ + 5 + 2 log₂ s`
   (`thm_4_7_loglog`), i.e. `Ω(log log r)` for fixed `s` (stronger than the printed
   `Ω(log log r / s)`). The paper's `(1/2s − o(1)) log log r` threshold with its "technical
   observation" is not reproduced literally.

## Proof-level issues (true statements)

6. **Proposition 4.6 proof.** It rounds the *joint* distribution of the `2s` certificates of a copy,
   but Eq. (6) uses that a single arc's *marginal* is `ε`-close; equal joint roundings only give
   marginal closeness `ε·2^((2s−1)κ)`. With the chosen `ε = 1/(12s·2^(2sκ))` the total error is still
   `4s · 2^κ · ε · 2^((2s−1)κ) = 1/3`, so the argument survives after correcting Eqs. (6)–(8). We round
   every arc's distribution separately. Also "w.l.o.g. exactly κ bits" (see 2).
7. **Theorem 5.1** applies Theorem 4.7 to a connected component of the crossing, outside the
   theorem's hypotheses (see "Refuted crossings" above); repaired by the restriction lemmas.
8. **Theorem 5.1** is stated for MST; we formalize acyclicity (the predicate its lower-bound proof
   uses) on lines/cycles (`LinesCycles`; as for Theorems 5.2–5.6 the lower bounds are stated for every
   family `F` containing the lines and cycles with distinct identities, e.g. `F_con`) and the acyclicity upper bound on `F_con` (`thm_5_1_upper`, deterministic
   `⌊log₂ n⌋ + 1`-bit scheme + Theorem 3.1). The MST upper bound (KKP's `O(log² n)` MST scheme) is not
   formalized. The lower bounds use the paper's copies `{u_{3k}, u_{3k+1}}` (0-based, `k < ⌊n/3⌋`).

9. **Theorems 5.2, 5.4, 5.6** (`Biconnectivity.lean`, `CycleAtLeast.lean`, `CycleAtMost.lean`): only
   the lower bounds, deterministic (Theorem 4.4) and one-sided (Proposition 4.8); the two-sided
   edge-independent versions follow from `thm_4_7_loglog` as for Theorem 5.1 but are not
   instantiated. The upper bounds of Theorems 5.2 and 5.3 are only sketched in the paper and are not
   formalized; Theorem 5.5 is not formalized. Families: the lower bounds hold for *every* family `F`
   containing the connected configurations whose states (in `ℕ`) are distinct identities
   (hypothesis `hFF`; `F = F_con` with or without the distinctness requirement are instances), so
   they apply to schemes that only need to be sound in the paper's identifier model; `κ` is a
   function of `n`.
   * Copies are `{v_{3k+1}, v_{3k+2}}`, `k < ⌊n/3⌋` (resp. `⌊c/3⌋`), one more copy than the paper's
     range; the paper's ranges are consistent.
   * **Theorem 5.4: printed `H_1 = G_e{v₀, v₁}` is not independent** of the other copies (`v₀` is
     adjacent to all nodes; `printed_H1_not_independent`). Typo with evident intent (R3: `{v₁,v₂}` as
     in Theorem 5.2), local fix → at most ⚠️-level, inside a proof (R1: proof-level).
   * Theorem 5.4: the claim "every simple cycle of the crossing has `< c` nodes" is proved via a
     cut-vertex/block argument (`cycle_support_of_cut`); the paper only asserts it.
   * Theorem 5.6: the graph is a chain of `m` cycles of `c` nodes (`n = m·c`); the paper's "except one
     of at most `c` nodes" is not a cycle when 1–2 nodes are left over.

## Verdict reasoning

* Proposition 4.3 and Theorems 4.4, 4.7 are false as printed (item 1). Not excused by R3/R4: the
  paper explicitly states the general condition `P(G) ≠ P(σ(G))`, and Proposition 4.3's proof
  explicitly (and wrongly) argues the rejected case. The counterexample satisfies every hypothesis of
  the paper's model (connected networks, distinct identities, port-preserving independent copies).
* **Is "`G` legal" a standing assumption? No.** Propositions 4.6 and 4.8 explicitly assume
  `P(G_s) = TRUE`, while Proposition 4.3 has no legality hypothesis and its proof argues the case
  "`G_s` is rejected" explicitly, and Theorems 4.4 and 4.7 ask only `P(G_s) ≠ P(σ(G)_s)`. The
  authors distinguished the two forms, so R4 does not excuse it. For Theorem 4.7 alone one could
  argue R3 (it is announced as a corollary of Proposition 4.6, which assumes `P(G) = TRUE`), but
  Proposition 4.3 and Theorem 4.4 are argued with the general version, which R3 does not excuse.
* **Borderline ❌ vs 🚨 (R5).** The abstract's primary claim is the exponential saving of randomization
  (Theorem 3.1, Corollary 3.5), which is correct. The crossing technique is introduced "In addition"
  (abstract and contributions), and is correct in the form used everywhere in the paper
  (`P(G) = TRUE`). We therefore treat Theorems 4.4/4.7 as secondary results: **❌ False claim**. Even
  if the lower-bound technique is counted as a co-equal headline, what the abstract claims is that
  the technique exists and applies to deterministic and randomized schemes; that claim survives in
  the `P(G) = TRUE` form, which yields every bound of Section 5. Only the over-general formal
  statements are false, so R5 still gives ❌ rather than 🚨.
