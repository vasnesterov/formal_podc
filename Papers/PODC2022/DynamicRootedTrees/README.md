# Broadcasting Time in Dynamic Rooted Trees — PODC 2022

Antoine El-Hayek, Monika Henzinger, Stefan Schmid. *Brief Announcement: Broadcasting Time in Dynamic Rooted Trees is
Linear.* PODC 2022, pp. 54–56. DOI [10.1145/3519270.3538460](https://doi.org/10.1145/3519270.3538460). Formalized
version: the brief announcement (BA, arXiv:2211.11352) states the result. The proofs come from the full version (FV),
*Asymptotically Tight Bounds on the Time Complexity of Broadcast and its Variants in Dynamic Networks*, ITCS 2023,
arXiv:2211.10151v2. The lower bound is due to Zeiner, Schwarz and Schmid (DAM 2019) and appears as FV Figure 5.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** Both bounds of BA Theorem 3.1, `⌈(3n−1)/2⌉ − 2 ≤ t*(𝒯ₙ) ≤ ⌈(1+√2)n − 1⌉`, are proved
for all `n`. There are no errors, only small slips in FV's proofs.

## Mistakes in the paper

There are no false statements. Points worth knowing:

- **BA claims a bound one round sharper than FV proves (the claim is true).** BA Theorem 3.1 (and FV's abstract)
  states `⌈(1+√2)n − 1⌉`, but FV Theorem 3.6 only proves `⌈(1+√2)n⌉`. The BA bound follows from the same argument, because the pigeonhole in FV
  Lemma 3.5 has slack. Take `R = n + m − 1` rounds with `m = ⌈√2 n⌉`. The edge count is at least
  `m(m+1)/2 + (n−1)m`, and this exceeds the threshold `(n−1)(n+m−1)` iff `m(m+1) > 2(n−1)²`. Optimizing `m` gives
  the slightly sharper `m + n − 1` for the least `m` with `m(m+1) > 2(n−1)²`, about `(1+√2)(n−1)`.
  (`theorem_3_1`, `theorem_3_6`, `advBroadcastTime_trees_le_of_sq_lt`)
- **Trees are not needed.** The upper-bound proof only uses a self-loop at every node and a root that reaches
  everybody in each round. (`broadcasts_of_rooted`)
- **Slips in FV's proofs.**
  - Lemma 3.3 is stated for `t₁ ≤ t₂` but used in Lemma 3.5 with `t₁ = t₂ + 1` (round 1). That extra case is
    trivial.
  - In Lemma 3.5, the in-degree formula has `x` where `r_t` is meant.
  - The final comparison in Lemma 3.5 is not the actual pigeonhole threshold, although the inequality used is still
    sufficient.
  - Lemma 3.2 (ii) carries an unnecessary hypothesis `t ≤ t'`.
- **The lower bound is only a figure in FV (Figure 5), with no proof.** Our reading of the figure:
  - first, the path `1 → ⋯ → n` for `⌊(n−1)/2⌋` rounds;
  - then the tree rooted at `n` with two branches, up to round `n − 2`;
  - then a rotated path.

  With this reading the construction is correct for every `n ≥ 2`. (`lbSeq`, `lbSeq_not_broadcasts`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- `n` processes, synchronous rounds, no failures and no randomness. Communication is full-information flooding.
- An oblivious message adversary picks each round's communication graph from `𝒯ₙ`: rooted out-trees on `Fin n` with
  a self-loop at every node (`treesWithLoops`).
- Information flow after `t` rounds is the relational product `G₁ ∘ ⋯ ∘ Gₜ`. Broadcast has happened when some
  process reaches all others.
- `broadcastTime` is an `sInf` and `advBroadcastTime` is a `⨆`. Their junk values (0 if never or unbounded) are
  harmless:
  - the upper bound is also stated per sequence (`broadcasts_trees`: every sequence of trees has broadcast by then);
  - the lower bound is witnessed by an explicit sequence that has not yet broadcast.
- The empty product is the identity. This only matters for `n = 1`, where `t* = 0`.

**Main results in Lean** (namespace `DynamicRootedTrees`).

| Paper | Lean | File |
|---|---|---|
| **BA Theorem 3.1** (both bounds) | `theorem_3_1` | `Main.lean` |
| FV Theorem 3.6 (`⌈(1+√2)n⌉`); per-sequence form | `theorem_3_6`, `broadcasts_trees` | `Main.lean` |
| FV Theorem 3.7 (lower bound, all `n ≥ 2`) | `theorem_3_7`, `lbSeq_not_broadcasts` | `Main.lean`, `LowerBound.lean` |
| FV Lemmas 3.3, 3.5 | `lemma_3_3`, `lemma_3_5` | `UpperBound.lean`, `Main.lean` |
| FV Lemmas 2.3–2.5, 3.2 (neighbourhood algebra) | `Cslib.DynNet.mem_outNbhd_iff_mem_inNbhd`, `Cslib.DynNet.outNbhd_trans`, … | CSLib `DynamicNetworks/Product.lean` |
| (new) rooted rounds suffice; sharper `m + n − 1` | `broadcasts_of_rooted`, `advBroadcastTime_trees_le_of_sq_lt` | `Main.lean` |
| (new) exact `t*(𝒯ₙ) = 0, 1, 2, 4` for `n = 1..4` | `advBroadcastTime_trees_one` … `advBroadcastTime_trees_four` | `Small.lean` |

**Small cases.** Exhaustive search gives `t*(𝒯ₙ) = 0, 1, 2, 4, 5, 7` for `n = 1..6`, which equals the lower bound
for `n ≥ 2`. The upper bound gives `2, 4, 7, 9, 12, 14`. Only `n ≤ 4` is kernel-checked in Lean; `n = 5, 6` come from
unverified Python/C searches.

**Not formalized.** The rest of FV (other broadcast variants and `k`-rooted networks).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
small-case values use kernel `decide`. The dynamic-network products and neighbourhoods come from CSLib,
`Cslib/Computability/Distributed/DynamicNetworks/Product.lean`.
