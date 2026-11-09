# Differences between the formalization and the paper

Paper: F. Dufoulon, J. Burman, J. Beauquier, *Beeping a Time-Optimal Leader Election*, PODC 2018 brief
announcement (DOI 10.1145/3212734.3212779). Formalized version: the full version *Beeping a Deterministic
Time-Optimal Leader Election*, DISC 2018 (LIPIcs 121, paper 20); numbering follows it. Lemma 1 and Theorem 2
are "adopted" from [5] = Casteigts, Métivier, Robson, Zemmari (DISC 2016; we used arXiv:1605.01903v4,
*Deterministic Leader Election Takes Θ(D + log n) Bit Rounds*, Lemmas 2, 5, 6, Corollary 7, Theorem 8).

## Mistakes (labels of `mistakes-labeling.md`)

1. 🔧 **Lemma 1 is false for Algorithm 1 as printed.** The paper evaluates rule 1 strictly before
   rule 2; [5] (rule R1) applies whichever of R1.1/R1.2 deletes more letters. With the paper's order,
   on the 7-node path with identifiers `152, 1, 3, 2, 144, 4, 148`, after 18 phases nodes 2 and 3 hold
   `111111110100110` and `111111110100100` (same length 15, differing at bit 14), whereas Lemma 1 allows
   differences only from bit 15 on (`Counterexample.lemma_1_false`, `not_lemma1_at_18`). They still differ
   only in the last 6 bits, so the looser reading "identical except in the last ≤ 6 bits" survives here.
   Repair: take the largest deletion among rules 1 and 2 (`Priority.maxDelete`), as in [5]. Then
   Lemma 1 (`lemma_1`, via the five forms of Lemma 6 of [5], `form_step`, `invariants`), Theorem 2 and
   Theorem 3 hold. Whether Theorem 2 (or the looser Lemma 1 that Section 3.1.3 needs) holds for the printed
   priority is **unchecked**. In random simulations (20 000 runs, paths, trees and sparse graphs with up to
   12 nodes) the looser relation and Theorem 2's bound were never violated, but our per-edge proof method
   does not apply: the per-edge abstraction for the printed order is not closed (it diverges).
2. ✏️ **Section 3.1.2, decoding formula of k-balanced messages.** The printed formula
   `m_u = m_v + r_u − r_v − ⌊(r_u − r_v)/(k+1)⌋·M` (floor) is wrong whenever the floor and the truncation
   toward 0 differ. Example from the paper's own Table 2 (`k = 4`, `m_v = 19`, `r_u = 0`): it gives 27, not 18
   (`decodeFloor_table2`, `decodeFloor_false`); also `m_v = 17`, `m_u = 19` gives 28 (`decodeFloor_wrap`;
   exact characterization `decodeFloor_eq`). Table 2 uses truncation, and with truncation the formula is
   correct for all `|m_u − m_v| ≤ k` (`decodeTrunc_correct`). Slip: the intended version is in the paper
   (Table 2).

## Modelling choices and other differences

- **Words, order, α.** Words are `List Bool`, most significant bit first. The paper's "higher" order
  (`x ≻ y`: `y` is a proper prefix of `x`, or `x` has 1 where `y` has 0 at the first difference) is exactly
  the lexicographic order on `List Bool` (a total order), used as Mathlib's `LinearOrder (List Bool)`.
  `α(i) = 1^{|bin i|} 0 bin i`; proved: strictly monotone (`alpha_lt_alpha_iff`), prefix-free
  (`alpha_prefix_alpha`), `|α(i)| = 2⌊log₂ i⌋ + 3`, decoding `alphaInv`.
- **Rule ties not specified by the paper.** When several neighbours trigger rule 1 (or rule 2) with
  different amounts, we delete the largest amount (as [5] does). The paper's counterexample run has no
  such tie (each rule's amount is unique at each step), so the counterexample does not depend on this choice.
- **Phase-level model.** A diffusion phase is modelled as: every node receives the *set*
  `received G C v` of `(prefix, suspicious)` pairs of its neighbours (no senders, no multiplicities), then
  applies `ruleStep`. The beep-level implementation of Section 3.1.3 is proved to simulate it (see README).
- **Candidates.** A node becomes a follower as soon as any of rules 1–5 fires (the paper's text). [5] makes
  a node a follower only on a change (R2), but between a deletion and the following change nothing else can
  happen, so this does not matter for the prefixes.
- **Followers with no rule triggered.** The paper's prose says a node whose prefix is locally highest
  "appends a bit from its α-id" without restricting this to candidates; we let only candidates append
  (as R5 of [5] does). The counterexample run is unchanged under the other reading (and under either tie
  rule), checked by an independent simulation.
- **Own bit.** A candidate with no rule triggered appends `α(id)[|prefix|]` while `prefix` is a proper prefix
  of `α(id)` (the paper: "appends a bit from its α-id"). The output `leader` is `candidate ∧ prefix = α(id)`
  (lines 9–10) and `leaderId = α⁻¹(prefix)`.
- **Theorem 2 constant.** We prove the bound `|α(X)| + 2r` (the constant of [5], Theorem 8), which implies the
  paper's `|α(X)| + 6r` (`theorem_2_paper`). Theorem 2 needs no uniqueness of identifiers for the
  max-identifier node `l` (only `ident v ≤ ident l` for all `v`); the "unique candidate" part and Theorem 3
  assume injective identifiers.
- **Lemma 1 needs nothing.** `lemma_1` holds for every graph (connected or not) and every identifier
  assignment.
- **Identifier range.** The paper assumes ids in `{1, …, N}`, `N = n^c`; we state complexities in terms of
  `X` (the maximum id): `|α(X)| = 2⌊log₂ X⌋ + 3 = O(log N)`.

## Not formalized

- Section 3.2 (Algorithm 2: overlays, termination detection; Lemmas 4, 5; Theorem 6: uniform explicit leader
  election in `O(D + log n)` rounds) — **unchecked**. Only informal evidence: a phase-level simulation of
  Algorithm 2 under our reading of the informal description (border nodes after more than 6 phases in the
  overlay, relays one level per phase, roots decide from phase `|α(id)| + 6` on) elected exactly the
  maximum-identifier node in 7 000 random runs (both rule priorities), and joins happened exactly at phase
  `|α(id_r)| + 6d` (Lemma 4's claim) in 3 000 runs.
- Section 3.3 (arbitrary id space, subsets of candidates, non-unique ids), the wake-on-beep variant of
  Section 2.2, and Section 4 (randomized LE, MIS and 5-colouring of trees, multi-broadcast).
- Lower bounds quoted from the literature (`Ω(D + log n)`).
