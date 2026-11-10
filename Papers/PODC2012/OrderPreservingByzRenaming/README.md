# Order-Preserving Byzantine Renaming — PODC 2012

Oksana Denysyuk, Luís Rodrigues. *Brief Announcement: Order-Preserving Renaming in Synchronous
Message Passing Systems with Byzantine Faults.* PODC 2012. DOI
[10.1145/2332432.2332476](https://doi.org/10.1145/2332432.2332476). Formalized version: arXiv
[1205.0477](https://arxiv.org/abs/1205.0477) **v2** (9 May 2012). It and v1 (2 May 2012) carry the
brief announcement's exact title and appeared two months before PODC 2012. v3 (March 2013) is
retitled "… in Synchronous Systems with Byzantine Faults", the ICDCS 2013 title. So v1/v2 are taken as
the BA's full version. The ACM record (pp. 233–234) has no abstract. v1 differs only in the
epoch numbering of Algorithm 2: it has a separate local epoch for the minimum offsets and one vote
epoch less. Both variants are formalized. The 2-page brief announcement itself was not accessible.
The later version (ICDCS 2013, arXiv v3, Chapter 6 of O. Denysyuk's PhD thesis) has different
algorithms and an impossibility result. It is formalized too, in a separate section below, and it
does not enter the verdict.

**Verdict: ⚠️ Weakened.** The paper makes two contributions. The constant-time Algorithm 1
(`N > 3t²`, namespace `N² + Nt`, two communication rounds) is correct (Theorem 3). The second
contribution, Algorithm 2 for the optimal resilience `N > 3t` (`O(log N)` rounds, namespace `2N`),
is broken. With `N = 7`, `t = 2` the correct processes with ids 10 < 11 output 7 and 6. With
`N = 4`, `t = 1` a correct process outputs `9 > 2N`. The root cause is that the paper claims
Lemma 2 (`Skew ≤ 3t²`) for `N > 3t`, but it only holds for `N > 2t² + t`. The label is ⚠️ and
not ❌ because the abstract and the conclusions present the two algorithms as equal contributions.
The conclusions lead with the correct one ("the first renaming algorithm that runs in constant
time"), and the optimal-resilience algorithm is "complemented" to it.

## Mistakes in the paper

### ❌ Theorem 8 (Algorithm 2, order preservation for `N > 3t`)
For `N = 7`, `t = 2`, the correct processes with ids `10 < 11` decide `7 ≥ 6`, and the one with id `12` also decides `7`. This holds
for v2 and for v1, which gives `8 ≥ 6` (`Alg2.order_false`).

**Impact.** The paper's second contribution, order-preserving renaming with optimal resilience
`N > 3t`, is lost. Only the constant-time Algorithm 1 for `N > 3t²` stands (Theorem 3).

**Details.** The Byzantine processes act only in Algorithm 1 (epoch 1), as in the next item. They
create a skew of 14 for the correct id `10` between process `0` (value 30) and the others
(value 16). Algorithm 2 starts with `Skew₂ = 3t² = 12`. In every vote epoch `isValid` therefore
rejects all correct votes across this gap: process `0` accepts only its own vote, and the others
reject it. Nothing changes afterwards. Process `0` outputs `⌈30/(N − t − Skew)⌉` and process `1`
outputs `⌈23/(N − t − Skew)⌉`. Lemmas 4 and 6 assume that "all correct processors accepted `C`",
the correct votes. This assumption fails here.

### ❌ Lemma 2 for `3t < N ≤ 3t²` ("Lemmas 1 and 2 hold for `N > 3t`")
For `N = 7`, `t = 2` two correct processes compute values of a correct id that differ by
`14 > 3t² = 12` (`ConstTime.lemma_2_false_of_gt_3t`).

**Impact.** Algorithm 2's initial `Skew₂ := 3t²` is unjustified for `N > 3t`, and this breaks
Theorem 8 (previous item). For `N > 2t² + t`, which covers Algorithm 1's range `N > 3t²`, Lemma 2 is
true (`ConstTime.lemma_2`).

**Details.** The fake ids `1, 2, 3` are each received in Round 1 by three correct processes. Both
Byzantine processes echo `{10, 11, 12, 1, 2, 3, 4}` to process `0` only, which accepts the echo as
valid. At process `0` the three fake ids reach `N − t = 5` echoes, so each gets offset `N = 7`
instead of 3. The proof counts at most `⌊(Nt + t²)/(N − t)⌋ = t` such ids, which needs
`N − t > 2t²`. For `N = 3t + 1` the same counting gives only `2t − 1`.

### ❌ Theorem 8 (Algorithm 2, target namespace `2N`)
For `N = 4`, `t = 1`, the correct process with id `12` outputs `9 > 2N = 8` (v2), resp. `12` (v1)
(`Alg2.namespace_false`).

**Impact.** The namespace `2N` claimed in the abstract does not hold. The validity proof asserts
`(N² + Nt)/(2t) < 2N`, which is false for every `N > 3t`.

**Details.** All correct processes compute `newId = 4, 5, 9, 13, 17` for the ids `1, 2, 10, 11, 12`.
In each vote epoch the Byzantine process sends and echoes the common vote shifted up by the current
`Skew` (3, then 3/2). Every correct process accepts it. The final value `145/8` divided by
`N − t − Skew = 9/4` rounds up to 9. The overshoot is small. `(N² + Nt)/(N − t − Skew) ≤ 2N` holds
whenever `Skew ≤ (N − 3t)/2`, so more vote epochs would probably save the namespace. We did not
formalize this, and it cannot save Theorem 8, which fails on order preservation (first item).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## Later version (ICDCS 2013 / thesis Chapter 6)

These findings concern the later version. Its numbering follows the thesis. The labels rate that
version and do not enter the verdict above. Its main results are an `O(log t)`-round algorithm
(Algorithm 5, namespace `n + t − 1`, `n > 3t`), a 7-round tight variant for `n > t² + 2t`
(Theorem 42), the 2-round Algorithm 8 (`n > 2t² + t`, namespace `n²`), and an impossibility for
`n ≤ 3t` (Theorem 46). Algorithm 5 is broken like Algorithm 2 above: Theorems 39 and 42 are false.
Theorem 46, Theorem 45 and Lemmas 27–32 are proved.

### ❌ Thesis Lemma 33 (correct votes are always valid)
The vote of a correct process can fail `isValid` at another correct process
(`Alg5.Cex7.lemma_33_false_paper`, `Alg5.Cex7.lemma_33_false_dlpsw`).

**Impact.** The convergence argument for Algorithm 5 (Corollaries 34–35, Lemmas 37–38) rests on
this lemma, and Theorems 39 and 42 fail with it (next items).

**Details.** `isValid` at `p` checks the `δ`-spacing of all pairs of `timely_p`. A correct process
`q` only keeps that spacing for pairs of its *own* `timely_q` (Lemma 32, which is true). A Byzantine id
`x` can be timely at `p` but not at `q`. Then a Byzantine vote that is valid at `q` may put `x` anywhere.
After trimming, the averages of `q` for `x` and for the next correct id can be closer than `δ`. The
proof of Lemma 33 applies Lemma 32 to `timely_p`, but Lemma 32 only covers the updating process's
own `timely` set.

Concrete run, `n = 7`, `t = 2`: correct processes `0…4` have ids `3…7`, Byzantine processes `5, 6`
use the fake ids `x = 2` and `y = 1`. Round-1 ids, echoes and Readies are chosen so that
`timely₀ = {2,…,7}` and `timely_i = {3,…,7}` for the other correct processes. Processes `0` and `1`
accept `{2,…,7}`; processes `2`, `3`, `4` also accept `y`. So `x` and `3` are ranked `δ, 2δ` by two
correct processes and `2δ, 3δ` by three. In Round 4 both Byzantine processes send process `1` a
vote with `x ↦ 3δ`, `3 ↦ 2δ`, which is valid there. Process `1` computes `ranks[x] = 2δ` and
`ranks[3] = 2δ` (with the paper's `select_t`) or `2.5δ` (with that of Dolev et al.).

### ❌ Thesis Theorem 39 (Algorithm 5 solves order-preserving renaming for `n > 3t`)
In the run above, the correct process `0` never decides: Algorithm 5 with `n = 7`, `t = 2` fails
for every target namespace, either `select_t`, and any number `L ≥ 5` of rounds, including the paper's
`2⌈log t⌉ + 8 = 10` (`Alg5.theorem_39_false`).

**Impact.** The paper's main algorithm, the first Byzantine order-preserving renaming algorithm
(namespace `n + t − 1`, `O(log t)` rounds), is refuted for `t ≥ 2`. No repaired algorithm is known
to us. The resilience `n > 3t` is therefore not shown to be tight.

**Details.** In Round 5, process `0` rejects the vote of process `1`, and the Byzantine processes
send it nothing. Process `0` is left with 4 < `n − t` valid votes for every id. Algorithm 7 (line 08)
then removes every id from `accepted`, its own included, so `ranks[my_id]` is undefined forever
(`Alg5.not_decides_of_not_mem`). The failure spreads: after Round 7 no correct process has any id
left (`Alg5.Cex7.acc7_paper`). The attack needs two accepted Byzantine ids, which `t = 1` does not allow
(Lemma 30). We did not check whether Algorithm 5 is correct for `t = 1`.

### ❌ Thesis Theorem 42 and Lemmas 40–41 (tight namespace in 7 rounds for `n > t² + 2t`)
The same attack works for `n = 9 > t² + 2t = 8`, `t = 2`: with 4 approximation rounds (`L = 7`), or
any `L ≥ 5`, a correct process never decides (`Alg5.theorem_42_false`).

**Impact.** The `O(1)`-round tight-namespace result of the abstract and of Table 1.2 is lost. The
counting part of Lemma 40 (at most `n` ids are accepted) is true (`Alg5.lemma_40_count`).

### ❌ Thesis Lemmas 38 and 41 (number of approximation rounds)
Both proofs bound the final range by an expression that does not depend on `n` and then claim it is
below `(δ − 1)/2 = 1/(6(n+t))`, which tends to 0. The claimed inequalities are false, e.g. for
`t = 1`, `n = 100` in Lemma 38 and for `t = 2`, `n = 9` in Lemma 41 (`lemma_38_step_false`,
`lemma_41_step_false`).

**Impact.** None beyond the two items above, since the algorithm fails anyway.

**Details.** The real contraction factor grows with `n`. Rounding only needs a range of at most
`δ − 1`, not `(δ − 1)/2`. With these two changes the round counts look plausible, but we did not
formalize Lemma 37.

### 🔧 Thesis Algorithm 5, Lines 10–14 (which ids get a Ready message)
The pseudocode adds the ids echoed `n − t` times to `Ids`, which still holds the Round-1 ids, and
sends Ready for all of `Ids`. Then Lemma 30 fails: with `n = 4`, `t = 1` a correct process accepts
6 > `n + t − 1` ids (`Alg5.lemma_30_false_pseudocode`).

**Impact.** Local fix. The text of §6.1.1 and the proof of Lemma 29 send Ready only for the echoed
ids. With that reading, Lemmas 27–30 hold (`Alg5.lemma_27` … `Alg5.lemma_30`).

### ✏️ Slips in the thesis chapter
- The heading of §6.3 and the table of contents announce the 2-round Algorithm 8 for `n > t² + 2t`.
  The caption, the text and Theorem 45 say `n > 2t² + t`, which is needed. For `n = 9`, `t = 2` the
  correct process with id 10 gets name 17 and the one with id 11 gets name 16
  (`TwoRound.alg8_not_solves_t2_add_2t`).
- §6.1.2 defines `select_t(set)` as the elements `it + 1` for `0 ≤ i < ⌊|set|/t⌋`, which gives
  `⌊(n−2t)/t⌋` elements. It then calls `σ_t = ⌊(n−2t)/t⌋ + 1` "the number of elements returned". For
  "the smallest and each `t`-th element after it" (Dolev et al.) the count is `⌈(n−2t)/t⌉`. The
  convergence factor of Lemma 37 is the number of selected elements. We formalize both choices.

### Typos
- Lemma 30's proof says "at the end of Round 4" (Round 3). Lemma 44's proof says the correct id is
  sent "in Round 2" (Round 1). Lemma 33's proof refers to "Line 28" and "Line 35" for Line 21 and
  Line 28 of Algorithm 5.
- In the proof of (6.2) in Lemma 37, the counts "at least `t(i+1)+1`" and "at most `ti`" are each
  too large by `t`; their difference `t + 1`, which is what is used, is right.
- `votes := votes ∪ R` (Algorithm 5, Line 27) must be a multiset union, one vote per link, as
  Algorithm 7 uses it. A set union would merge identical correct votes.

## The formalization

**Model.**
- CSLib's synchronous lock-step Byzantine model (`Cslib.Byzantine.LockStep`) on the complete
  network: deterministic history-based protocols, a static set of at most `t` Byzantine processes,
  reliable links. The adversary picks every Byzantine message per round, sender and receiver. The
  counterexamples need neither rushing nor adaptivity.
- Inputs are the original ids (`ℕ`); correct processes have distinct ids. Byzantine processes may
  announce any ids. `OPRenamingOn S M` requires termination, validity (`1 ≤ name ≤ M`),
  uniqueness and order preservation for the correct processes whose ids lie in `S`.
- The paper's processes are anonymous and use local link numbers. CSLib protocols may depend on the
  process, which makes the impossibility (thesis Theorem 46) stronger. All algorithms are written
  anonymously: they only count links and compare contents. The self-loop (link `N`) is simulated:
  a process adds its own broadcast to its inbox.
- Algorithm 2 and thesis Algorithm 5 are state machines over the history (`Alg2.step`,
  `Alg5.step`). The counterexamples are computed by `decide +kernel` on `Alg2.run` / `Alg5.run`,
  which equal the honest states of the LockStep run (`stateOf_hist`). Algorithm 2 has a parameter
  `K`, the number of vote epochs (v2: `4⌈log t⌉ + 2`, v1: `4⌈log t⌉ + 1`).

**Main results in Lean (arXiv v1/v2).**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 | `ConstTime.lemma_1` | `ConstTime.lean` |
| Lemma 2 (for `N > 2t² + t`) | `ConstTime.lemma_2` | `ConstTime.lean` |
| Lemma 2 for `N > 3t`: **false** | `ConstTime.lemma_2_false_of_gt_3t` | `ConstTimeCex.lean` |
| Theorem 3 (Alg. 1, `N > 3t²`, namespace `N² + Nt`) | `ConstTime.theorem_3` | `ConstTime.lean` |
| Theorem 8, order preservation: **false** | `Alg2.order_false` | `Alg2Cex.lean` |
| Theorem 8, namespace `2N`: **false** | `Alg2.namespace_false` | `Alg2Cex.lean` |

**Main results in Lean (later version, thesis Chapter 6).**

| Paper | Lean | File |
|---|---|---|
| Thm 46 (`n = 3`, `t = 1`, namespace `M+1 → M`) | `theorem_46` | `Impossibility.lean` |
| Thm 46, general `3 ≤ n ≤ 3t` (simulation by 3 processes) | `theorem_46_general`, `theorem_46_anyNamespace` | `Impossibility.lean` |
| Lemma 43 (`Δ ≤ 2t²`), Lemma 44 | `TwoRound.lemma_43`, `TwoRound.lemma_44` | `TwoRound.lean` |
| Thm 45 (Alg. 8, `n > 2t² + t`, namespace `n²`) | `TwoRound.theorem_45` | `TwoRound.lean` |
| §6.3 heading (`n > t² + 2t`): **false** | `TwoRound.alg8_not_solves_t2_add_2t` | `Counterexample8.lean` |
| Lemmas 27, 28, 29, 30 | `Alg5.lemma_27` … `Alg5.lemma_30`, `Alg5.lemma_30_namespace`, `Alg5.lemma_40_count` | `IdSelection.lean` |
| Lemma 30 for the literal pseudocode: **false** | `Alg5.lemma_30_false_pseudocode` | `PseudocodeIds.lean` |
| Lemmas 31, 32 | `Alg5.lemma_31`, `Alg5.lemma_32` | `Spacing.lean` |
| Lemma 33: **false** | `Alg5.Cex7.lemma_33_false_paper`, `Alg5.Cex7.lemma_33_false_dlpsw` | `Counterexample5.lean` |
| Thm 39: **false** | `Alg5.theorem_39_false` | `Counterexample5.lean` |
| Thm 42: **false** | `Alg5.theorem_42_false` | `Counterexample5.lean` |
| Lemmas 38, 41 (arithmetic steps): **false** | `lemma_38_step_false`, `lemma_41_step_false` | `Lemma38.lean` |

Thesis Theorem 46 is proved with an infinite line of nodes instead of the paper's ring (FLM covering,
`CoverSystem.decides_scenario_iff`). Process-dependent code would force a ring length divisible by
3, and the line avoids this. The general case uses CSLib's `GroupSim` reduction, as in the paper.
There the simulated original namespace is `{0, …, n(M+1) − 1}`.

**Not formalized.** For v1/v2: Lemmas 4–7 individually. Whether Algorithm 2 works for `N > 3t²`,
or for `t = 1` with a larger namespace. The proof of Lemma 6 bounds only the distance of each
average to the mean of the correct votes, not the distance between two processes. Message
complexity. For the thesis: Theorem 47 (randomized impossibility), Lemmas 36–37, and whether
Algorithm 5 is correct for `t = 1`.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The concrete executions are checked by `decide +kernel` (no `native_decide`).
Non-vacuity: Theorem 3 is instantiated for `N = 4`, `t = 1` and thesis Theorem 45 for `n = 4`,
`t = 1`. The model and the FLM/group-simulation tools come from CSLib
(`Cslib/Computability/Distributed/Byzantine/LockStep/{Basic,Cover,GroupSim}.lean`).
