# Differences between the formalization and the paper

Paper: O. Denysyuk, L. Rodrigues, *Brief Announcement: Order-Preserving Renaming in Synchronous
Message Passing Systems with Byzantine Faults*, PODC 2012. The 2-page brief announcement was not
accessible. **Formalized version: arXiv:1205.0477v2** (9 May 2012). It and v1 (2 May 2012) carry the
brief announcement's title and are taken as its full version. The later version (ICDCS 2013 =
arXiv v3 = Chapter 6 of O. Denysyuk's PhD thesis) has different algorithms and is treated in the
second part of this file.

# Part I: arXiv v1/v2 (the version judged)

## v1 vs v2

The two versions have the same Algorithm 1 and the same procedures (Algorithms 3–6). v1's
Algorithm 2 has a separate epoch 2 that only computes `minOffset := max(counter − t, 0)`, Algorithm 6
in epoch 3, and Algorithm 5 in epochs `4, …, 4⌈log t⌉ + 3`. v2 computes the minimum offsets at the end
of epoch 1 and runs Algorithm 6 in epoch 2 and Algorithm 5 in epochs `3, …, 4⌈log t⌉ + 3`. So v1 has
`K = 4⌈log t⌉ + 1` vote epochs and v2 has `K = 4⌈log t⌉ + 2`. In both, the skew starts at `3t²` and is
multiplied by `2t/N` after every vote epoch. `Alg2.alg2 n t K` covers both. v1's `isValid` also
takes the sender's link as input, which it does not use.

## Errors

1. **❌ Theorem 8, order preservation** (`Alg2.order_false`). Take `N = 7`, `t = 2`, correct ids
   `10, …, 14`. The Byzantine processes play only Round 1 of Algorithm 1 (fake ids `1, 2, 3`, each
   sent to three correct processes) and Round 2 (the echo `{10, 11, 12, 1, 2, 3, 4}` to process `0`).
   After that they are silent. Process `0` computes `newId[10] = 30` and the others `16`, a skew of
   `14 > Skew₂ = 12`. `isValid` then separates process `0` from the other correct processes in
   every vote epoch, and the values never change. Final outputs: ids `10, 11, 12` get `7, 6, 7` (v2)
   and `8, 6, 8` (v1), so both order and uniqueness fail.
2. **❌ "Lemmas 1 and 2 hold for `N > 3t`"** (Section 2, before Lemma 1). Lemma 2 fails for `N = 7`,
   `t = 2` (`ConstTime.lemma_2_false_of_gt_3t`: skew 14 > 12). The proof's count
   `⌊(Nt + t²)/(N − t)⌋ = t` of ids whose offsets jump to `N` needs `N − t > 2t²`. Lemma 2 is proved
   for `N > 2t² + t` (`ConstTime.lemma_2`). It is the source of item 1.
3. **❌ Theorem 8, namespace `2N`** (`Alg2.namespace_false`). For `N = 4`, `t = 1` a correct process
   outputs `9` (v2) or `12` (v1), both `> 2N = 8`. The validity proof claims
   `⌈(N² + Nt)/(N − t − Skew)⌉ < (N² + Nt)/(2t) < 2N`. The second inequality is equivalent to
   `N < 3t`, false for every `N > 3t`.
   The overshoot is small. `(N² + Nt)/(N − t − Skew) ≤ 2N` holds once `Skew ≤ (N − 3t)/2`, so more
   vote epochs would probably save the bound. This was not formalized, and it is moot because of item 1.

## Proved

- Lemma 1 (`ConstTime.lemma_1`), Lemma 2 for `N > 2t² + t` (`ConstTime.lemma_2`), Theorem 3:
  Algorithm 1 solves order-preserving renaming into `{1, …, N² + Nt}` for `N > 3t²`
  (`ConstTime.theorem_3`), with a non-vacuity instance `N = 4`, `t = 1`.

## Observations not formalized

- Lemma 6: equations (17)–(19) bound `mean(C ∪ B) − mean(C)` by `(2t/N) Skew_e`. The distance
  between two correct processes can then be twice that. The lemma also assumes that every correct
  process accepts all correct votes, which fails (item 1).
- Lemmas 4, 5, 7 and the message complexity were not formalized.

## Modelling choices (v1/v2)

- Algorithm 1 (`ConstTime.alg1`) reuses the two communication rounds and the sanity check of
  `TwoRound` (they are the same as in the thesis' Algorithm 8). `newId[v]` sums the offsets of the
  ids `≤ v` that occur in valid echoes. Ids received in Round 1 but never validly echoed have counter
  `0` and offset `0`, as in the paper (for `t < N`).
- Algorithm 2 (`Alg2.alg2`): a vote is the list of `⟨id, newId⟩` of all known ids, increasing.
  A vote received on link `i` is used iff the identical list was echoed by at least `N − t` links
  (the self-loop included) and `isValid` holds. Correct processes echo the list of all votes they
  received. `predecessorNewId(v, id)` takes the largest key of `v` below `id`. The average of an
  empty list is `0`, but this never occurs in our runs (a process always accepts its own vote there).
  `minOffset` uses natural subtraction for `max(counter − t, 0)`. In Algorithm 6, "repeat
  `t − missing` times" does nothing when `missing ≥ t`. The output is
  `⌈newId[my id] / (N − t − Skew)⌉` with the final computed `Skew = 3t²(2t/N)^K`.
- The model, ids, self-loop and specification are as in Part II.

# Part II: the later version (ICDCS 2013 / thesis Chapter 6)

Numbering follows the thesis. These labels rate the later version, not the brief announcement.

## Errors in the later version

1. **❌ Lemma 33 is false.** A correct process's vote can be invalid at another correct process.
   `Alg5.Cex7.lemma_33_false_paper` and `Alg5.Cex7.lemma_33_false_dlpsw` give the instance `n = 7`,
   `t = 2`; the execution is described in the module docstring of `Counterexample5.lean` and in the
   README. Root cause: `isValid` at `q` checks only the pairs of `timely_q`, but `q`'s vote must keep
   the `δ`-spacing of the pairs of `timely_p` for every correct `p`. Lemma 32 (true, `Alg5.lemma_32`)
   only covers pairs of the updating process's own `timely` set. The paper's induction in Lemma 33
   silently replaces one by the other.
2. **❌ Theorem 39 is false** (`Alg5.theorem_39_false`). For `n = 7`, `t = 2` a correct process
   drops every id from `accepted` in Round 5 and never decides. This holds for both readings of
   `select_t`, for any number `L ≥ 5` of rounds (the paper uses `L = 2⌈log t⌉ + 8 = 10`) and any
   target namespace. By Round 7 every correct process has an empty `accepted` set
   (`Alg5.Cex7.acc7_paper`). The attack needs two accepted Byzantine ids, so `t ≥ 2`. The case
   `t = 1` was not checked.
3. **❌ Theorem 42 (with Lemmas 40–41) is false** (`Alg5.theorem_42_false`). The same attack works for
   `n = 9 > t² + 2t`, `t = 2`, with `L = 7` (4 approximation rounds) or any `L ≥ 5`.
4. **❌ Proofs of Lemmas 38 and 41**: their final inequalities do not depend on `n` on the left and
   tend to `0` on the right, and they are false for large `n` (`lemma_38_step_false`: `t = 1`,
   `n = 100`; `lemma_41_step_false`: `t = 2`, `n = 9`). The round counts might still follow from the
   real contraction factor `≈ (n − 2t)/t` and the threshold `δ − 1`, which suffices for rounding
   (`round` is monotone and `round(y) > round(x)` when `y ≥ x + 1`). This was not formalized and is
   moot because of item 2.
5. **🔧 Algorithm 5, Lines 10–14**: read literally, `Ids` still holds the Round-1 ids, and every
   correct process sends Ready for every id it received in Round 1. Then Lemmas 29–30 fail
   (`Alg5.lemma_30_false_pseudocode`: `n = 4`, `t = 1`, 6 accepted ids `> n + t − 1 = 4`). We
   formalize the text's reading ("Only ids that have been echoed at least `n − t` times are
   considered for the following round"), for which Lemmas 27–30 hold.
6. **✏️ §6.3 heading and table of contents**: "Algorithm for `n > t² + 2t` with Only 2 Rounds".
   Algorithm 8 needs `n > 2t² + t` (its caption, the text and Theorem 45).
   `TwoRound.alg8_not_solves_t2_add_2t`: `n = 9`, `t = 2`, the correct ids 10 < 11 get the names
   17 > 16.
7. **✏️ `σ_t`** (§6.1.2): `select_t` is defined to return `⌊|set|/t⌋` elements, but
   `σ_t = ⌊(n−2t)/t⌋ + 1` is called "the number of elements returned by `select_t`". Dolev et al.'s
   selection ("the smallest and each `t`-th element after it") returns `⌈(n−2t)/t⌉` elements. Neither
   count equals `σ_t` when `t ∣ n − 2t`. The convergence factor in the proof of Lemma 37 is the number
   of selected elements.

## Typos (claims unaffected)

- Lemma 30's proof: "at the end of Round 4" should be Round 3.
- Lemma 44's proof: correct ids are sent "in Round 2" should be Round 1.
- Lemma 33's proof: "Line 28" (initial ranks) should be Line 21, and "Line 35" (update) should be
  Line 28 of Algorithm 5. Lemma 36 also says "Line 28" for Line 21.
- Lemma 37, proof of (6.2): "at least `t(i+1)+1` elements" and "at most `ti` elements" are each too
  large by `t`. Their difference, which is all the proof uses, is right.
- Lemma 36 states the bound `(t + ⌊t²/(n−2t)⌋)δ` but its proof ends with `(2t − 1)δ`. Both are
  valid for `n > 3t`, since the first is at most the second.
- Algorithm 5 Line 27, `votes := votes ∪ R`, must be a multiset union, one vote per link, as
  Algorithm 7 iterates "foreach `R ∈ all_ranks`". With a set union, identical correct votes would
  collapse and even fault-free runs would fail.

## Modelling choices

- **Model.** CSLib `LockStep` (synchronous rounds, complete network, static Byzantine set of size
  `≤ t`, reliable links, deterministic protocols). The adversary's messages are arbitrary functions
  of the round, sender and receiver. The paper adds corruption "at any time" and a rushing,
  eavesdropping adversary. For deterministic protocols this covers adaptive and rushing choices.
  Static corruption makes our counterexamples *stronger* (they use a weaker adversary). For
  Theorem 46 the adversary we need is also static.
- **Ids and anonymity.** The paper's processes know only their own id and their local link
  numbers. In LockStep, protocols may depend on the process (`Fin n`). For the impossibility
  (Theorem 46) this gives a stronger result. Algorithms 5 and 8 never use the process index except
  to put their own message on their own link; they only count links.
- **Self-loop.** The paper's link `n` is a self-loop. LockStep has none (a `SimpleGraph`), so a
  process inserts its own broadcast into its inbox (`Function.update`) before processing it.
- **Specification.** `OPRenamingOn S M`: if correct processes have distinct ids in `S`, then every
  correct process decides (first decision), on a name in `{1, …, M}`; names of correct processes
  are distinct and preserve the order of their ids. Termination is "eventually decides". The
  algorithms decide at a fixed round.
- **Theorem 46.** The `n = 3` proof uses an infinite line `0, 1, 2, …` of nodes (node `i` runs the
  code of process `i mod 3` with id `i`) instead of a ring of `M + 1` processes. With
  process-dependent code a ring would need length divisible by 3, and only `M` adjacent pairs are
  used. The original namespace is `{0, …, M}` as in the paper. For general `3 ≤ n ≤ 3t` we use
  CSLib's group simulation (`GroupSim.Solvable.of_groupSim`), as the paper does. The simulated ids
  are `x·n + k`, so the impossibility is stated for the original namespace `{0, …, n(M+1) − 1}`
  (and for arbitrary ids in `theorem_46_anyNamespace`). The case `M = 0` is trivial and handled
  separately. The paper's "for `t = ⌈n/3⌉`" is our hypothesis `n ≤ 3t` with `n ≥ 3` (the model of
  Chapter 3 has `n ≥ 3`).
- **Algorithm 8.** `newid[v]` is the sum of `min(counter, n − t)` over accepted ids `≤ v`, as in
  Lines 17–21. We also prove it equals the sum over all ids `≤ v` (`newid_eq_sum_range`). Lemma 43 is
  proved for every id (not only correct ones). It is the one-sided bound
  `newid_p[v] ≤ newid_q[v] + 2t²` for all correct `p, q`, which is the bound the theorem uses.
- **Algorithm 5.**
  - Rounds 2–3 follow the text (item 5 above). The Echo and Ready messages of one round are
    bundled into one message per link, as the model allows one message per link and round.
  - `ranks` is represented by its domain (`accepted`) and a value function `ℕ → ℚ`. A Byzantine
    `⟨AA, R⟩` is an arbitrary finite domain with arbitrary values.
  - `select_t` is a parameter. `selPaper` follows the formula of §6.1.2 (indices `it`,
    `i < ⌊|set|/t⌋`) and `selDLPSW` follows Dolev et al. (indices `it < |set|`). All counterexamples
    are proved for both.
  - `round` is Mathlib's `round` (half up), then `Int.toNat`. A process decides only after exactly
    `L` rounds and only if its own id is still accepted. If `ranks[my_id]` is undefined, Line 30
    has no value to return, and we model this as no decision.
  - "Remove `t` extreme values" on the filled multiset of `n` votes is `drop t` / `take (n − 2t)` of
    the sorted list (insertion sort).
- **Lemmas 27–30** are stated for the states `Alg5.run` (equal to the honest LockStep states by
  `Alg5.stateOf_hist`). Lemma 30 assumes distinct correct ids and `n > 3t`. The paper's bound
  `n + ⌊t²/(n−2t)⌋` is proved for any number `f ≤ t` of actual faults (the count is
  `n − f + ⌊f(n−f)/(n−2t)⌋`).
- **Lemma 32** is proved without the hypothesis `|votes[id]|, |votes[id']| ≥ n − t` (the new values
  are computed anyway). It assumes a selection function that depends only on positions and is
  non-empty on the reduced multiset (`GoodSel`), and `n > 2t`. Both selections qualify for
  `n > 3t` (`selPaper` needs `t ≥ 1`).

## Not formalized

- Theorem 47 (randomized impossibility with a non-rushing adversary).
- Lemma 36 (initial discrepancy), Lemma 37 (convergence of the approximation phase, after Dolev
  et al.), Corollaries 34–35, and the message and bit complexity claims.
- Whether Algorithm 5 is correct for `t = 1`, and whether any repair of the validation saves
  Theorem 39.
