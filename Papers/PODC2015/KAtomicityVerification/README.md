# Computing k-Atomicity in Polynomial Time — PODC 2015

Wojciech Golab, Xiaozhou (Steve) Li, Alejandro López-Ortiz, Naomi Nishimura. *Computing Weak Consistency in
Polynomial Time.* PODC 2015. DOI [10.1145/2767386.2767407](https://doi.org/10.1145/2767386.2767407).
Formalized version: the journal version *Computing k-Atomicity in Polynomial Time*, SIAM J. Comput. 47(2),
2018 (DOI [10.1137/16M1056389](https://doi.org/10.1137/16M1056389), authors' copy, complete proofs). All
statements, numbering (Theorem 3.5, Lemma 3.8, Algorithms 1–3, Lemmas 4.2–4.5, 5.5–5.10, …) and the input
ranges are those of the journal version; the PODC 2015 extended abstract is not openly available and was
not consulted, so its numbering and wording may differ.

**Verdict: ✅ Correct.** Every checked statement holds as written: the normalization procedure (Theorem 3.5),
the graph characterization of k-atomicity (Lemma 3.8), the correctness of GPO for histories satisfying
Assumption 4.1 (Lemmas 4.2–4.5, Theorem 4.10, for every `k ≥ 2`), and the correctness of CGS for arbitrary
histories with distinct written values (Lemmas 5.5–5.7, Theorem 5.8), plus the size bounds of the
configuration graph (Lemmas 5.9–5.10), which concern the graph built by CGS on its inputs `2 ≤ k ≤ n`.
The proofs go through with only routine additions.

## Mistakes in the paper

No mistakes in the statements.

### Typos and slips
- Lemma 4.5, `P(x)`-(c) asks for `b ∈ B_x[k-1-j]` for all `0 ≤ j ≤ i`, which mentions the nonexistent set
  `B[0]` when `i ≥ k-1`. Such edges cannot occur once `P(x)`-(a) holds, so only `j` with `k-1-j ≥ 1` matter.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- No execution model is involved. A history on one register is a finite set of operations, each an
  interval `[s op, f op]` with `s op < f op` and natural-number times. `<_H` is `f a < s b`.
- Writes are indexed by the values they write (`V`) and reads by `R`, with `val : R → V`. This builds in
  Assumption 3.2 in the form of the abstract ("all values written are distinct"), so `w(v)` is
  well defined.
- A `k`-atomic total order is a strict total order on operations that extends `<_H`, in which each read's
  dictating write precedes it with fewer than `k` writes in between.
- Unique event times (`DistinctTimes`) are never needed: every result holds for arbitrary natural-number
  times.
- The algorithms are deterministic functions or propositions. GPO is computable: its outer loop runs
  `|V|` times, each `step` is the identity once `U = ∅`, and ties between equal finish times (impossible
  in the paper's model) are broken by a linear order on `V`. CGS is a classical proposition (decision
  only, no implementation).

**Proof remarks.**
- Lemma 3.8 needs Assumption 3.4, which the paper assumes throughout. With only Assumption 3.3 it fails;
  we found a 6-operation counterexample by brute force for `k = 1`, but did not formalize it. Our proof of
  the "if" direction is shorter than the paper's three stages: each read is placed right after the last
  write that must precede it (`opKey`).
- GPO uses several invariants the paper leaves implicit: `B[i] ⊆ U`, `|B[i]| ≤ i` after each successful
  iteration, and the bound "an unplaced `G_R`-successor of a value placed `d` steps ago forces
  `d ≤ k-1`". These are the fields of `Inv`.
- Lemma 4.4 (YES ⇒ k-atomic) does not need Assumption 4.1; only Lemma 4.5 does.
- In Claim 4.9 the swap with `z` is shown to be topological by a short case analysis, which the paper
  leaves out.
- Lemma 5.5's proof establishes "distinct values, no inversion" and then needs a linear-extension step
  to reach "subsequence of a topological ordering". We supply it (`Good.exists_topoOrder_sublist`).
- Lemma 5.7 attributes distinctness of the induced sequence to Corollary 5.6; it actually comes from
  Lemma 5.5.
- Range of `k`. The abstract and Section 1 announce the algorithms "for any `k ≥ 3`" (the new range:
  `k ≤ 2` was solved before), while the inputs of Algorithms 2–3 and Section 7 say `2 ≤ k ≤ n`. Both
  ranges are correct: GPO is correct for `k ≥ 2` (`theorem_4_10`) and CGS even for `k ≥ 1`
  (`cgs_iff_kAtomic`). The proof of Lemma 4.4 says "since we are considering `k > 2`"; for `k = 2` the
  same argument works with the range `1 ≤ y < k-1` empty.
- Lemma 5.10 is about the graph `G_C` "computed at line 11 of the algorithm" (§5.3), so `k ≥ 2`. Its
  edge bound indeed needs `max(m,k) ≥ 2` (`card_edges_le`): for `m = k = 1`, `n_w` sequential writes and
  no reads give `n_w(n_w-1)/2` configuration-graph edges. The vertex bound holds for every `k ≥ 1`.
- Theorem 3.5: the paper processes the values one at a time; the moves do not interact, and we formalize
  the simultaneous version. The `k`-atomic total orders of `H` and of its normalization coincide
  (`normalize_isKAtomicOrder_iff`, no hypotheses).

**Main results in Lean.** All in namespace `Podc.KAtomicityVerification.History`.

| Paper | Lean | File |
|---|---|---|
| Def. 3.1, 3.6, 3.7, Assumptions 3.2–3.4, 4.1 | `KAtomic`, `ER`, `EW`, `Assumption33/34/41` | `Basic.lean` |
| Theorem 3.5 (Algorithm 1) | `theorem_3_5`, `normalize_isKAtomicOrder_iff`, `normalize_time_lt_iff`, `normalize_f_moved` | `Normalization.lean` |
| Lemma 3.8 | `kAtomic_iff_exists_valueOrder` | `Characterization.lean` |
| §2: `k ≥ n_w` reduces to Assumption 3.3 | `kAtomic_iff_assumption33_of_card_le` | `LargeK.lean` |
| Algorithm 2 (GPO) | `gpo`, `step`, `next`, `choice` | `GPO.lean` |
| Lemma 4.2 | `lemma_4_2` (invariant `Inv`, `inv_next`) | `GPOComplete.lean`, `GPOCorrect.lean` |
| Lemma 4.3 | `lemma_4_3` | `GPOCorrect.lean` |
| Lemma 4.4 | `lemma_4_4`, `valueOrder_of_gpo` | `GPOCorrect.lean` |
| Lemma 4.5 (Claims 4.6–4.9) | `lemma_4_5`, `exists_ext_next`, `PB_next` | `GPOComplete.lean` |
| Theorem 4.10 (correctness) | `theorem_4_10` | `GPOComplete.lean` |
| Def. 5.1–5.4, Algorithm 3 (CGS) | `writeConcurrency`, `IsConfig`, `Extends`, `induced`, `IsPath`, `CGS` | `CGS.lean` |
| Lemma 5.5 | `IsPath.exists_topoOrder_sublist`, `IsPath.good` | `CGS.lean` |
| Corollary 5.6 | `IsPath.length_sub_one_le`, `IsPath.head_ne_getLast` | `CGS.lean` |
| Lemma 5.7 | `kAtomic_iff_exists_path` | `CGS.lean` |
| Theorem 5.8 | `cgs_iff_kAtomic` | `CGS.lean` |
| Lemma 5.9 | `card_succSet_le`, `card_succSet_concurrent_le`, `card_succSet_after_le`, `card_config_successors_le` | `CGS.lean` |
| Lemma 5.10 | `card_configs_le`, `card_edges_le` | `CGS.lean` |
| Fig. 3.1 (3- but not 2-atomic; exactly two 3-atomic value orders), Table 5.1 | `fig31_kAtomic_three`, `fig31_not_kAtomic_two`, `fig31_valueOrders_three`, `fig31'_table51` | `Examples.lean` |
| §4.2 (GPO on Fig. 3.1, wrong without Assumption 4.1) | `fig31'_gpo_three`, `fig31'_gpo_two`, `fig31_gpo_three_wrong` | `ExamplesGPO.lean` |

**Not formalized.** The running-time bounds (second part of Theorem 4.10, Theorem 5.11), the locality of
k-atomicity (Section 2), and the experiments (Section 6).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: the Fig. 3.1 history satisfies Assumption 3.4, and without `w(5)` it also satisfies
Assumption 4.1 (`fig31_assumption34`, `fig31'_assumption41`). GPO is run on it by `decide`. Before the
formalization, GPO and CGS were also checked against the definition by brute force on thousands of random
small histories, with no mismatch. The model is self-contained (no CSLib modules). The interval-history
model is in `Basic.lean`.
