# Self-stabilizing Systems in Spite of High Dynamics — PODC 2020

Karine Altisen, Stéphane Devismes, Anaïs Durand, Colette Johnen, Franck Petit. *Brief Announcement: Self-stabilizing
Systems in Spite of High Dynamics.* PODC 2020. DOI
[10.1145/3382734.3404502](https://doi.org/10.1145/3382734.3404502). Formalized version: the full version, Theoretical
Computer Science 2023 (DOI 10.1016/j.tcs.2023.113966), author manuscript HAL hal-04109662. The brief announcement
has no proofs. Numbering follows the full version.

**Verdict: 🔧 Easy fix.** Every result is true, and we proved all of them. This covers the impossibilities (no closed
legitimate set for size-ambiguous algorithms in `TC_B(Δ)`, the need for exact knowledge of `n` in `TC_Q(Δ)` and `TC_R`,
unbounded stabilization time) and the three algorithms with their bounds `3Δ`, `2Δ` and `Δ + 1`. Corollary 1 is stated
more strongly than what Theorem 1 gives, and Theorem 6 relies on two implicit model assumptions. The proofs of Lemma 6
(Algorithm 2) and Lemma 11 (Algorithm 3) each miss a counting step, which needs a short local repair.

## Mistakes in the paper

### ✏️ Slips
- **Corollary 1** says that a closed set of legitimate configurations for one `V` means `A` is not size-ambiguous at
  all. It is meant as the contrapositive of Theorem 1, "`A` is not `(k, V)`-ambiguous", and the printed form is false.
  Algorithm 1 is size-ambiguous, yet for a single process it has a closed set of legitimate configurations
  (`corollary_1_as_stated_false`). The contrapositive holds (`corollary_1`), and Theorem 3 only uses that.
- **Theorem 6, Corollary 8, Lemma 13, Corollary 9** rely on two implied assumptions. The proof swaps the leader for a
  fresh process `v ∉ V` and keeps the other processes' states. So `IDSET` must have more than `n` identifiers: with
  `IDSET = Fin 2`, an algorithm that knows `n` elects `0` when `n = 2` and is correct from round 0
  (`theorem_6_needs_large_IDSET`). Also, the possible local states must depend on `V` only through `n` (`SizeOnly`):
  an algorithm whose state is `V` elects `min V` at once (`theorem_6_needs_sizeOnly`). Both counterexamples are
  pseudo-stabilizing (`knowsN2_pseudoStab`, `knowsV_pseudoStab`). The paper's algorithms know at most `n` and `Δ`
  and satisfy both assumptions (`alg2_sizeOnly`, `alg3_sizeOnly`).
- Section 3.3 says Algorithm 1's legitimate configurations cannot be closed. That holds only for systems of at least
  two processes (`alg1_not_closed`, `alg1_singleton_closed`).

### Typos
- Algorithm 3, line 7: `insert(p, ⟨id(0), 0⟩)` should be `insert(p, ⟨id(p), 0⟩)`.
- Lemma 11, proof case 2: "edge `(r, p)`" should be "edge `(r, q)`".

## Proof gaps (statements true)

### 🔧 Lemma 6 (Algorithm 2, identifiers inserted after round `Δ` are never evicted)
The proof claims that after `id` is pushed, evicting it requires inserting `n` new distinct identifiers. This is false:
re-inserting identifiers already in the queue (lines i2–i3) moves `id` towards the head
(`Alg2.lemma_6_counting_claim_false`: with `n = 3`, one new identifier evicts `5` from `[1, 2, 5]`).

**Impact.** Statement true; repaired (`Alg2.lemma_6`), so Lemma 7, Lemma 9 and Theorems 5 and 7 stand.

**Repair.** From round `Δ + 1` on, the longest suffix of the queue with real identifiers only grows, and its elements
are never evicted. If its first element is the head, the queue holds `n` distinct real identifiers, i.e. all of `V`, so
no new identifier can arrive (`Alg2.lemma_6_suffix`).

### 🔧 Lemma 11 (Algorithm 3, `id(p)` reaches `members(q)` along journeys)
"`id(p)` cannot be removed by Lemma 10" and "this pair is not rejected" need a counting step that the proof does not give.

**Impact.** Statement true; repaired (`Alg3.lemma_11`), so Theorems 8 and 9 stand.

**Repair.** An entry with timestamp `≤ i − 2` is evicted at line i6 only if it has the maximal timestamp. Then all
entries are `≤ i − 2`, so by Lemma 10 all keys are real, and the full map is exactly `V`. So no absent identifier can
arrive. This argument applies at every step of the loop, for every processing order and tie-break, and also at line
7, which the proof does not discuss (`Alg3.mem_keys_of_full_lt`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Synchronous rounds over dynamic graphs: `G t` is the snapshot of Round `t + 1`, edges join distinct processes of `V`.
  The classes `TC_B(Δ)`, `TC_Q(Δ)`, `TC_R` are defined through temporal distance (journeys with strictly increasing
  times). They are the all-pairs classes of `Papers/PODC2021/StabilizingLEDynamic` (same authors).
- Processes are their identifiers, taken from a linear order. There are no crashes, the algorithms are deterministic,
  and the initial configuration is arbitrary. The adversary is the choice of the graph within the class.
- An algorithm (`SAlg`) is defined for every set of processes. The code of a process does not depend on `V`, and
  knowledge (for instance `n`) is an input in the state. So it shows up as the sets of possible states `S V p`,
  which is the paper's `S_A^V(p)` used in Definition 3.
- Communication is full-information local broadcast: each process receives the whole states of its current
  in-neighbours. This is stronger than sending part of the state, so the impossibilities are not weakened. The
  algorithms of Sections 4–6 use only the part the paper sends.
- Algorithms 2 and 3 process the received pairs in an arbitrary order, and every round lemma holds for every order
  and every tie-break of `max(p)`.
- Definitions 1, 2 and 6 are stated for recurring classes, as in Remarks 1 and 2.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Property 1 | `splice_mem_JssQ` | `Classes.lean` |
| Theorem 1 | `theorem_1` | `Section3.lean` |
| Corollary 1 (contrapositive / as stated false) | `corollary_1` / `corollary_1_as_stated_false` | `Section3.lean` / `Alg1Closure.lean` |
| Remark 3 (`Δ ≥ 2` needed in Theorem 1) | `remark_3` | `Remark3.lean` |
| Theorem 2, Corollary 2 | `theorem_2`, `corollary_2` | `Section3.lean` |
| Theorem 3, Corollary 3 | `theorem_3`, `corollary_3` | `Section3.lean` |
| Algorithm 1: Remark 6, Lemmas 1–4, Corollaries 4, 5 | `Alg1.remark_6`, `Alg1.lemma_1` … `Alg1.lemma_4`, `Alg1.corollary_4`, `Alg1.corollary_5` | `Alg1/Main.lean` |
| Theorem 4, Corollary 6 (`≤ 3Δ` rounds) | `Alg1.theorem_4`, `Alg1.corollary_6`, `Alg1.selfStab` | `Alg1/Main.lean` |
| Algorithm 1 is size-ambiguous, not closed | `Alg1.sizeAmbiguous`, `alg1_not_closed` | `Alg1/Main.lean`, `Alg1Closure.lean` |
| Algorithm 2: Lemmas 5–9, Corollary 7 | `Alg2.lemma_5` … `Alg2.lemma_9`, `Alg2.corollary_7` | `Alg2/Main.lean` |
| Theorem 5 (with closure) | `Alg2.theorem_5`, `Alg2.theorem_5_isLegit`, `Alg2.theorem_5_closed` | `Alg2/Main.lean` |
| Theorem 7 (`≤ 2Δ` rounds in `TC_B(Δ)`) | `Alg2.theorem_7` | `Alg2/Main.lean` |
| Theorem 6, Corollary 8 | `theorem_6`, `corollary_8` | `Unbounded.lean` |
| Lemma 13, Corollary 9 | `lemma_13`, `corollary_9` | `Unbounded.lean` |
| Theorem 6's implicit assumptions are needed | `theorem_6_needs_large_IDSET`, `theorem_6_needs_sizeOnly` | `Counterexamples.lean` |
| Algorithms 1–3 satisfy `SizeOnly`; Algorithm 2 satisfies Theorem 2's `Invariant` | `alg1_sizeOnly`, `alg2_sizeOnly`, `alg3_sizeOnly`, `alg2_invariant` | `Main.lean` |
| Algorithm 3: Lemmas 10–12 | `Alg3.lemma_10`, `Alg3.lemma_11`, `Alg3.lemma_12` | `Alg3/Main.lean` |
| Theorem 8 (with closure) | `Alg3.theorem_8`, `Alg3.selfStab` | `Alg3/Main.lean` |
| Theorem 9 (`≤ Δ + 1` rounds in `TC_B(Δ)`) | `Alg3.theorem_9` | `Alg3/Main.lean` |
| Algorithms 2 and 3 are not size-ambiguous | `Alg2.not_sizeAmbiguous`, `Alg3.not_sizeAmbiguous` | `Alg2/Main.lean`, `Alg3/Main.lean` |

Remarks:
- Theorem 1 is proved with a simpler TVG than the paper's: the complete graph on a `k`-subset without the leader in
  even rounds, and the complete graph on `V` in odd rounds. No rotating window is needed.
- Theorem 3 is proved directly from the core of Theorem 1 and the set of the proof of Theorem 2. So, unlike Theorem 2,
  it does not need executions to stay in the configurations of `A` for `V`.
- Theorem 6 holds for every algorithm whose states depend on `V` only through `n`, pseudo-stabilizing or not.

**Not formalized.** The memory and message-size claims of Corollary 6 and Theorem 5, and Remarks 4 and 5 (other
problems).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. Non-vacuity:
the three algorithms satisfy the hypotheses of the general theorems (self-stabilizing; Algorithm 1 is size-ambiguous
and Algorithms 2 and 3 are not, consistent with Theorems 1 and 3; all three are `SizeOnly`, and Algorithm 2 satisfies
the `Invariant` hypothesis of Theorem 2). The static complete graph is in all three classes (`K_mem_JssB`). The model reuses
`Papers/PODC2021/StabilizingLEDynamic/Model.lean` and CSLib `DynamicNetworks/{HeardOf,Journey}`.
