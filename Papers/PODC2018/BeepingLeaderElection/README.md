# Beeping a Time-Optimal Leader Election — PODC 2018

Fabien Dufoulon, Janna Burman, Joffroy Beauquier. *Brief Announcement: Beeping a Time-Optimal Leader
Election.* PODC 2018. DOI [10.1145/3212734.3212779](https://doi.org/10.1145/3212734.3212779). Formalized
version: the full version *Beeping a Deterministic Time-Optimal Leader Election*, DISC 2018 (LIPIcs 121,
paper 20); numbering follows it. Lemma 1 and Theorem 2 are adopted from Casteigts, Métivier, Robson,
Zemmari [5]; for their proofs we used arXiv:1605.01903v4.

**Verdict: 🔧 Easy fix.** Lemma 1 is false for Algorithm 1 as printed, because rule 1 is given priority
over rule 2. With the rule of [5] (delete the larger amount) Lemma 1, Theorem 2 (even with `2r` instead of
`6r` phases) and the `O(D + log n)`-round eventual leader election of Theorem 3 are proved, including the
`O(1)`-round beeping implementation of a diffusion phase. The decoding formula for k-balanced messages has a
floor that should be a truncation. **The paper's headline result, the terminating (explicit) election
in `O(D + log n)` rounds of Section 3.2 (Lemmas 4–5, Theorem 6), was not checked**; the label covers
Section 3.1 (Algorithm 1, the eventual election it builds on) only.

## Mistakes in the paper

### 🔧 Lemma 1 (Algorithm 1, rule priority)
With the paper's priority (rule 1 strictly before rule 2), Lemma 1 fails: on the 7-node path with
identifiers `152, 1, 3, 2, 144, 4, 148`, after 18 phases the neighbours 2 and 3 hold `111111110100110` and
`111111110100100`, two words of length 15 that differ at bit 14, while Lemma 1 allows differences only from
bit 15 on (`lemma_1_false`).

**Impact.** Theorem 2's proof and the constant-size communication phase of Section 3.1.3 both rest on
Lemma 1. With the deletion rule of [5] (the larger of the two deletions) all of Section 3.1 is proved.

**Details.** In phase 18, node 3 holds `1111111101001000`. Its neighbour 4 is suspicious and holds
`111111110100100`, a proper prefix, so rule 1 deletes one letter. Its neighbour 2 holds `11111111010011`,
which branches higher two letters before the end, so rule 2 would delete two. The paper applies rule 1, and
node 2 appends a bit meanwhile. [5] (rule R1) deletes the larger amount, and then node 3 would hold
`11111111010010`. The paper says it uses "the same constant-size set of changes" as [5], so Lemma 8 of [5]
would carry over, but it changed how rules R1.1 and R1.2 combine. The two words still differ only within
their last 6 bits, so the looser reading "identical except in the last ≤ 6 bits" survives in this run.
Whether that looser relation (which Section 3.1.3 needs) and Theorem 2 hold for the printed priority is
unchecked. Random simulations found no violation, but the per-edge invariant method below does not apply
to it.

**Repair.** Rules 1 and 2 delete the larger of their amounts (`Priority.maxDelete`). The five forms of
neighbouring prefixes of [5] (Lemma 6) are invariant (`form_step`, `invariants`). Lemma 1 then holds on
every graph (`lemma_1`), and so do Theorem 2 (`theorem_2`, `theorem_2_paper`) and Theorem 3
(`theorem_3_phases`, `theorem_3`).

### ✏️ Slips
- Section 3.1.2: the decoding formula `m_u = m_v + r_u − r_v − ⌊(r_u − r_v)/(k+1)⌋·M` is wrong with a floor.
  On the paper's own Table 2 (`k = 4`, `m_v = 19`, `r_u = 0`) it gives 27 instead of 18 (`decodeFloor_table2`,
  `decodeFloor_eq`). Table 2 rounds toward zero, and with truncation the formula is correct
  (`decodeTrunc_correct`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Synchronous beeping model (BEEP) with a synchronous start, deterministic, no failures. In each round a
  node beeps or listens. A listener learns only whether at least one neighbour beeped; a beeping node
  learns nothing. The graph is static and arbitrary (`SimpleGraph V`, `V` finite). Nodes have identifiers
  (positive, unique where stated) and know nothing about `n`, `D` or `N`.
- Phase level (`Algorithm.lean`): in a diffusion phase every node receives the *set* of its neighbours'
  `(prefix, suspicious)` pairs, without senders or multiplicities, and applies rules 1–5 (`ruleStep`).
  `Priority.paper` is the printed rule order, `Priority.maxDelete` the repair.
- Beep level (`Beeping.lean`): a diffusion phase is a communication phase of `c = 1664` rounds. A node
  beeps in the slot of its message (`|prefix| mod 13`, last 6 bits, `suspicious`), listens in the others,
  and decodes the heard slots relative to its own prefix. A node cannot hear neighbours that use its own
  slot, which is harmless because its own pair never triggers a rule (`ruleStep_erase_self`). Decoding is
  correct whenever Lemma 1 holds (`decode_encode`), and the beep-level run reproduces the phase-level run
  (`beepRun_phase`).
- The paper's order "higher" is the lexicographic order on `List Bool`, which is total, so the rules and
  the α-encoding use it consistently (`alpha_lt_alpha_iff`, `alpha_prefix_alpha`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| α-encoding is order-preserving, prefix-free | `alpha_lt_alpha_iff`, `alpha_prefix_alpha`, `alphaInv_alpha` | `Words.lean` |
| Section 3.1.2, k-balanced decoding (Table 2) | `decodeTrunc_correct`, `decodeFloor_table2`, `decodeNat_correct` | `Balanced.lean` |
| Lemma 1 fails for the printed rule order | `Counterexample.lemma_1_false` | `Counterexample.lean` |
| Lemma 6 of [5] (five forms), one-edge step | `form_step` | `Forms.lean` |
| Lemma 2 of [5] + forms, invariant | `invariants` | `Lemma1.lean` |
| Lemma 1 (repaired priority) | `lemma_1` | `Lemma1.lean` |
| Theorem 2 (`|α(X)| + 2r`, and the paper's `6r`) | `theorem_2`, `theorem_2_paper` | `Theorem2.lean` |
| Theorem 2/3, unique candidate, `leaderId = X`, phases | `theorem_3_phases` | `Theorem2.lean` |
| Section 3.1.3, beep-level phase simulation | `decode_encode`, `beepRun_phase`, `beepRun_s` | `Beeping.lean` |
| Theorem 3 (rounds) | `theorem_3`, `theorem_3_log` (`1664·(2⌊log₂ X⌋ + 3 + 2D)` rounds) | `Beeping.lean` |

**Not formalized.** Section 3.2 (Algorithm 2, overlay networks, Lemmas 4–5, Theorem 6: uniform terminating
explicit election in `O(D + log n)` rounds), Section 3.3 and Section 4 (randomized election, MIS and
5-colouring of trees, multi-broadcast). A phase-level simulation of Algorithm 2 under our reading of the
informal description elected exactly the maximum-identifier node in all random runs; this is evidence, not
a check.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The counterexample is checked phase by phase by `decide` on explicit configurations. The
generic beeping model is staged in `Podc/` (`Podc/Computability/Distributed/Beeping/Basic.lean`: `Cslib.Beeping.Algorithm`, `run`, the bridge `run_eq_stoneAge` to CSLib's stone-age model, and the multi-slot pattern `heardSlots_eq`; CSLib candidate).
