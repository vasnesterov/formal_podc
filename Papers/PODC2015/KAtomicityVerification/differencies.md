# Differences between the formalization and the paper

Golab, Li, López-Ortiz, Nishimura, *Computing k-Atomicity in Polynomial Time*, SIAM J. Comput. 47(2), 2018
(journal version of the PODC 2015 paper *Computing Weak Consistency in Polynomial Time*).

## Model (Section 3)

1. **Histories as intervals.** The paper's history is a sequence of invocation/response events with unique
   times `1, 2, …`. We keep only what the paper uses: every operation has a start `s` and a finish `f` in `ℕ`
   with `s < f`, and `a <_H b ⟺ f a < s b`. Unique event times are available as `DistinctTimes` but no
   result needs them.
2. **Assumption 3.2 is built in.** Writes are indexed by the values they write (`V`); every read returns some
   `val r : V`. This is the reading "all the values written to a given object are distinct" (abstract,
   Section 1), under which the paper's notation `w(v)` makes sense. Literally, Assumption 3.2 ("every read
   has exactly one dictating write") would still allow two writes of the same value that nobody reads; the
   paper never considers that case.
3. **One object.** Locality (Section 2) is not formalized; all operations act on one register, as the paper
   assumes "without loss of generality".
4. **k-atomic total order.** A strict total order `lt` on `V ⊕ R` that extends `<_H`, in which every read
   `r` is preceded by `w(val r)` and fewer than `k` writes lie strictly between them. This is the paper's
   "returns the value assigned by one of the last `k` writes that precede it".
5. **Value orders.** Lemma 3.8's `T = v₁ … v_{|V|}` is a list with no duplicates that contains every value,
   with the index conditions `EW T[i] T[j] → i < j` and `ER T[i] T[j] → i < j + k` (`IsKAtomicValueOrder`).
   The paper's notion "k-atomic value order = sequence of values consistent with some k-atomic total order"
   coincides with it by Lemma 3.8; the examples use the Lemma 3.8 form. Internally we also use ranks
   (`IsKAtomicRank`, gaps allowed) and, for GPO, bijections `V ≃ Fin |V|` counted from the right.

## Theorem 3.5 (normalization, `Normalization.lean`)

6. The paper moves responses one value at a time; we move them all at once. The moves do not interact
   (each `r(v)` is a read, whose events never move), and `normalize_time_lt_iff`/`normalize_f_moved` show
   that the result is exactly "the event order of `H` with each moved response placed immediately before
   the response of `r(v)`".
7. Times are rescaled (invocation `4t`, response `4t+2`, moved response `4 f(r(v)) + 1`). The trigger is
   "some read of `v` finishes no later than `w(v)`", which equals the paper's `f(r(v)) < f(w(v))` under
   unique times. With ties, a literal "move to time `f(r(v)) - ε`" can produce an operation that finishes
   before it starts; the rescaling avoids this, so `DistinctTimes` is not needed. This is a modelling
   remark, not a paper error.
8. We prove more than Theorem 3.5: `H` and its normalization have the same k-atomic total orders for every
   `k` (`normalize_isKAtomicOrder_iff`, no hypotheses). The paper's proof is correct. Two small steps are
   implicit: Assumption 3.4 needs `r(v)` to be the *earliest* read, and the "next event after the moved
   response" argument needs that later iterations never insert anything there. Our proof derives the new
   `<_H` edges directly.

## Lemma 3.8 (`Characterization.lean`)

9. Hypotheses: Assumption 3.4 (assumed globally by the paper) and `k ≥ 1` (the paper's `k` is a positive
   integer). Assumption 3.4 is really needed: a brute-force search found a 6-operation history satisfying
   Assumption 3.3 but not 3.4 for which the lemma fails at `k = 1` (not formalized, since the paper does
   not claim it).
10. The proof of the "if" direction differs from the paper's three-stage construction, which is correct.
    Each read is keyed by the latest position among its dictating write and the writes that happen before
    it (`opKey`).

## Section 2 claim (`LargeK.lean`)

11. "When `k ≥ n_w` … it suffices to verify that each read returns the value assigned by some write whose
    start time is less than the finish time of the read": `kAtomic_iff_assumption33_of_card_le`, for
    `k ≥ 1`. We state the condition as Assumption 3.3 (`¬ r <_H w(val r)`, i.e. `s(w) ≤ f(r)`); under unique
    times this is the paper's `s(w) < f(r)`. It holds without Assumption 3.4 (via normalization). Line 3 of
    CGS is the corollary `kAtomic_of_card_le`. The `O(n log n)` algorithm is not formalized.

## GPO (Algorithm 2, `GPO.lean`, `GPOCorrect.lean`, `GPOComplete.lean`)

12. **Loop.** `while U ≠ ∅` is modelled as `|V|` iterations of `step`, which is the identity once `U = ∅`.
    `card_run` shows that `U` is empty exactly at the end.
13. **Ties.** "The value whose write has the largest finish time" is unique under unique times. To be
    total, we break ties by a linear order on `V`. No correctness proof uses uniqueness, so
    `theorem_4_10` holds for every history, ties included.
14. **Obligation sets** are a function `ℕ → Finset V`. `B[0]` and `B[i]` for `i ≥ k` are kept empty, and
    the overfull/full tests range over `1 ≤ i ≤ k-1`.
15. **Hypotheses of Theorem 4.10:** Assumptions 3.4 and 4.1 and `k ≥ 2`, as in the paper (Assumption 3.3
    follows from 3.4). `k ≤ n` is not needed. Lemma 4.4 needs neither Assumption 4.1 nor anything beyond
    3.4.
    The paper's proof of Lemma 4.4 writes "since we are considering `k > 2`"; for `k = 2` the argument
    goes through with the range `1 ≤ y < k-1` empty (`v_j ∈ B_x[1]` directly). Routine; our proof covers
    `k ≥ 2` uniformly.
16. **Lemma 4.2** is stated for every state reached after `x` successful iterations. The paper uses further
    invariants without stating them: `B[i] ⊆ U` (so line 7 chooses an unplaced value), `|B[i]| ≤ i`, the
    acyclicity bookkeeping of Lemma 4.3, and a quantitative form of Lemma 4.4's obligation argument. All of
    them are fields of `Inv`.
17. **Lemma 4.5.** `P(x)`-(c) is used only for indices `k-1-j ≥ 1` (the paper's statement mentions `B[0]`,
    see the README). It holds for every run, so it lives in `Inv.oblig`. `P(x)`-(a)/(b) are
    `∃ σ, IsRevOrder σ ∧ Ext st σ` and `PB`. Claims 4.6–4.9 are inside `exists_ext_next`. Claim 4.9 is
    reorganized: if no value of `S` has a `G_W` edge into `v''`, the swap is topological and Claim 4.8
    applies; otherwise the paper's `z`-argument applies. The topological-swap fact for `z` gets an explicit
    case analysis.
18. The time bound `O(n² + n·k log k)` is not formalized.

## CGS (Algorithm 3, `CGS.lean`)

19. **Algorithm 3** is a classical proposition (`CGS`), not an implementation: YES iff `|V| ≤ k`, or (no
    line-5 witness and) `G_C` is nonempty and has a path with exactly `|V| - max(m,k)` edges. A path is a
    nonempty list of configurations, consecutive ones related by `Extends`.
20. **Theorem 5.8** is proved for every `k ≥ 1` under Assumption 3.4. The paper's input range is
    `2 ≤ k ≤ n`. For `k = 0` CGS is wrong only degenerately (a history with no reads is 0-atomic but CGS
    answers NO).
21. **Lemma 5.7** hypotheses: Assumption 3.4, `1 ≤ k ≤ n_w`. The paper's `n_w ≥ m` is proved
    (`writeConcurrency_le_card`).
22. **Corollary 5.6.** Acyclicity is stated as "no path with at least one edge starts and ends at the same
    configuration" (`IsPath.head_ne_getLast`). The length bound `IsPath.length_sub_one_le` does not need
    `n_w ≥ k`.
23. **Lemma 5.5.** The paper proves (i) distinct values and (ii) no inversion, and then concludes
    "subsequence of some topological ordering" without the linear-extension step. That step is
    `Good.exists_topoOrder_sublist`. Our induction runs from the front of the path, mirroring the paper's.
24. **Lemma 5.9** is stated for the set `succSet v` of values that can immediately follow `v` in a
    topological ordering of `G_W` (`card_succSet_le`, `≤ 2m-1`, with the two halves `≤ m-1` and `≤ m`).
    `card_config_successors_le` covers successors inside configurations.
25. **Lemma 5.10** bounds any finite set of configurations, resp. of `G_C` edges. The vertex bound needs
    `k ≥ 1`. The edge bound needs `max(m,k) ≥ 2`. For `m = k = 1` it fails (`n_w` sequential writes, no
    reads: `n_w(n_w-1)/2` edges), because "C′ adds a successor of the last value of C" needs
    configurations of length at least 2. This is not a statement-level error: §5.3 says "any references to
    the configuration graph `G_C` pertain to the graph structure computed at line 11 of the algorithm",
    and Algorithm 3's input is `2 ≤ k ≤ n` (rendered page 442), so the lemma's own scope has
    `max(m,k) ≥ k ≥ 2`. (§5.2's "CGS works correctly for all `k ≥ 1`" is about the Fig. 3.1 example and
    concerns correctness, not Lemma 5.10; CGS is indeed correct for `k ≥ 1`, `cgs_iff_kAtomic`.)
26. Theorem 5.11 (running time) is not formalized.

## Examples (`Examples.lean`, `ExamplesGPO.lean`)

27. The figure has no numeric times. We take the event ranks `1…18` read off Fig. 3.1 and check that they
    give exactly the drawn graphs `G_R`, `G_W` (`fig31_ER`, `fig31_EW`).

## Remarks

28. No mistake in a statement was found. The `k ≥ 3` (abstract, Section 1: the new range beyond the known
    `k ≤ 2` cases) vs `k ≥ 2` (Algorithms 2–3, Section 7) difference is between a weaker and a stronger
    true claim. The Lemma 5.10 edge bound fails only for `m = k = 1`, which is outside the lemma's own scope
    (`G_C` is the graph built by Algorithm 3, whose input has `k ≥ 2`; see item 25). The
    `B[0]` index in `P(x)`-(c) is inside a proof and is vacuous. Every proof goes through with only
    routine additions.
