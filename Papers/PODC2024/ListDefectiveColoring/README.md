# List defective colouring — PODC 2024

Marc Fuchs, Fabian Kuhn. *Simpler and More General Distributed Coloring Based on Simple List Defective Coloring
Algorithms.* PODC 2024 (brief announcement). DOI
[10.1145/3662158.3662808](https://doi.org/10.1145/3662158.3662808). Formalized version: full version, arXiv
[2405.04648](https://arxiv.org/abs/2405.04648) v1.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** The main algorithmic result (Two-Sweep, Theorem 1.1) and Theorem 1.4 are proved, and no
stated theorem is refuted. The construction in the proof of Lemma 4.5 and the proofs of Lemmas 3.1 and A.1 need
local repairs, which we made. The round bounds of the `(Δ+1)`-colouring applications (Theorems 1.2, 1.3 and 1.5) rest
on cited black boxes and were not checked.

## Mistakes in the paper

### ✏️ Slips
- Theorems 1.1/1.2 say "`β_v` is the outdegree" while Section 2 defines `β_v = max(1, outdeg)`, and read literally
  they fail in a degenerate case: an isolated node with an empty list. We use Section 2's convention, and then the
  theorems hold.
- Lemma 3.2: the displayed inequality `r_v(x_v) + k_v(x_v) ≤ |N_>(v)| < d_v(x_v) + 1` is garbled (and `l'_v` should
  be `S_v`); the step is a pigeonhole on sums against (6) (`exists_phaseII_color`).
- Section 4.1: the setup of Lemma 4.2 states `deg~(v,i) ≤ ∑_x a_v(x,i)`, but the proof needs (and the truth is) the
  reverse (`Sec41.lemma_4_2`).
- Eq. (9) omits the factor `deg(v)` (`Sec41.theorem_1_4`).
- Theorem 1.2, proof: `ε = 1/(3⌈log₄ C⌉)` is undefined for `C = 1`.

### Typos
- "Let `ε > 0` be an integer" (`ε` is real).
- Lemma 3.5 assumes a non-strict slack while Theorem 1.1 gives a strict one.

## Proof gaps (statements true)

### 🔧 Lemma 4.5 (colour space reduction: a node may pick a useless subspace)
Every node is offered all `p` colour subspaces, so it may pick one disjoint from its list (nothing forbids it when
no neighbour picks the same subspace) and is left with an empty list (`ColorSpace.paper_counterexample`).

**Impact.** A gap in the construction, not in the statement (`lemma45`).

**Details.** Smallest case: one isolated node, `L = {0}`, two subspaces. The slack chain also divides by `deg(v)`,
which may be `0`.

**Repair.** Offering only subspaces that meet `L_v` repairs it; the slack bound survives because `L_v ≠ ∅`
(`lemma45`).

### 🔧 Lemma A.1 (slack of the sub-instances)
The proof claims `deg(v) − deg~(v) ≥ Δ − Δ/2 ≥ µ·deg_{G_i}(v)`, but the first step fails for nodes of degree `< Δ`
(`SlackReduction.paperA1_counterexample`).

**Impact.** The statement about existence is unaffected: the node still has slack 1, so what breaks is the
round-complexity argument, not existence; repaired (`lemmaA1`). Slack and halving are proved at specification
level; eq. (22) itself is not formalized.

**Details.** In a 15-node instance with `Δ = 6`, `µ = 2`, `ε = 1/4`, a node of degree 4 with 3 coloured neighbours
and one neighbour in its class ends with residual weight exactly `µ·deg_{G_i}(v)`, so its sub-instance lacks
slack `µ`.

**Repair.** Compare `deg~(v)` with half of the node's own residual degree and take the defective colouring on the
residual graph; per-node residual degrees then halve each phase (`lemmaA1`, `SlackReduction.lemmaA1_halving`).

### 🔧 Lemma 3.1 (final pigeonhole, case `|L_v| > p`)
The final pigeonhole bounds the wrong right-hand side (all of `L_v` instead of `S_v`), so it does not give (4).

**Impact.** Statement true; repaired (`lemma_3_1`).

**Repair.** Averaging the *difference* of the two sides of (4) over all `p`-subsets works and also proves the
Remark that Algorithm 1's sorted choice satisfies (4).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Any `SimpleGraph V`; out-neighbourhoods are arbitrary sets `out v ⊆ N(v)` (an orientation is a special case;
  `out v = N(v)` gives plain list defective colouring). The initial `q`-colouring need only be proper along
  out-edges. This is more general than the paper.
- Section 3: synchronous, deterministic, fault-free LOCAL rounds (CSLib's `Cslib.LocallyIterative.Algorithm`: a
  node's new state depends on the round, its state and the *set* of neighbour states); states carry IDs, lists
  and defects. Two-Sweep runs in exactly `2q` rounds, and its outputs are `2q`-local functions of the
  initial states (`twoSweep_isLocal`). Neighbours are counted through the set of neighbour states with the
  shared identifier API `Cslib/Computability/Distributed/Local/Identifiers.lean`. CONGEST message sizes are not modelled.
- Algorithm 1's "sort and take the first `p`" is modelled as any best `p`-subset; the sorted prefix is shown to be
  one, so every tie-breaking is covered.
- Section 4.1 and Lemmas 4.4, 4.5, A.1 are specification-level: the arbdefective subroutine is replaced by its
  output specification and all its outputs are quantified over; Lemma 3.4's defective colouring (cited by the
  paper) is a hypothesis. `Δ ≥ 2` per the paper's Section 2 convention.

**Main results in Lean** (namespace `FK24`).

| Paper | Lean | File |
|---|---|---|
| Lemma 3.1 (+ Remark), Lemma 3.2 | `lemma_3_1`, `exists_phaseII_color` | `SubsetSelection.lean`, `TwoSweep.lean` |
| Lemma 3.3 = Theorem 1.1 (`ε = 0`) | `twoSweep_correct`, `twoSweep_correct_of_isProper` | `Distributed.lean` |
| Theorem 1.1 (`ε > 0`, Algorithm 2) | `fastTwoSweep_correct` | `FastTwoSweep.lean` |
| Section 1.1 corollaries | `twoSweep_listColoring`, `twoSweep_threeColoring` | `Distributed.lean` |
| Theorem 1.2 (arithmetic only) | `theorem12_slack` | `Theorem12.lean` |
| Claim 4.1, Lemmas 4.2, 4.3 | `claim_4_1`, `Sec41.lemma_4_2`, `Sec41.lemma_4_3_sharp` | `NeighborhoodIndependence.lean`, `Section41.lean` |
| Theorem 1.4 (paper's `d' = ⌈(d+1)/(7θ)⌉ − 1`) | `Sec41.theorem_1_4`, `Sec41.theorem_1_4_paper_slack` | `Section41.lean` |
| Floor variant of eq. (10) fails (not the paper's definition) | `Sec41.theorem_1_4_paper_defects_false` | `Section41Counterexample.lean` |
| Lemma 4.4; Lemma 4.5 (fixed) | `lemma44`; `lemma45` | `SlackReduction.lean`, `ColorSpaceReduction.lean` |
| Lemma A.1 (fixed) and counterexample | `lemmaA1`, `SlackReduction.paperA1_counterexample` | `SlackReduction.lean` |

**Eq. (10).** arXiv v1 uses a ceiling, `d' = ⌈(d+1)/(7θ)⌉ − 1 = ⌊d/(7θ)⌋`, which is non-negative and satisfies
(11). The Lean file `Section41Counterexample.lean` shows that a *floor* variant would colour no node; that variant is
not the paper's definition, and `differencies.md` item 1 (which attributes the floor to the paper) is a misreading.

**Lemma 4.3.** It can be sharpened to `X_v ≤ 4θ d'` (`Sec41.lemma_4_3_sharp`), so the constant 7 could be 4.

**Not formalized.**
- The cited black boxes (Lemma 3.4, Lemma 3.5, [FK23a] Thm. 4), hence Theorems 1.2/1.3 beyond their arithmetic,
  Theorem 1.5 and Lemma 4.6 (`O`-recursions), and all round/message-size bounds that go through them.
- Round count of Theorem 1.2: as written, the argument gives `O(log³C + log C · log* q)` rather than
  `O(log³C + log* q)`, because Lemma 3.4 is recomputed at each level. We did not check whether it can be shared
  across levels.
- Round count of Lemma A.1: as written, every phase recomputes Lemma 3.4, which gives `O(log Δ · log* q)` rather than
  `+ O(log* q)`.
- The arithmetic of eq. (20), `log⁷Δ` against the `log⁸Δ` of Theorem 1.5, which would only weaken the bound.
- The "w.l.o.g. `d_v(x) ≤ Δ`" reduction of Theorem 1.4 (hypothesis `hdΔ`).
- The `O(Δ + log* n)` round bound of the Section 1.1 3-colouring corollary, which needs an initial `O(Δ)`-colouring
  the paper does not mention.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: Section 4.1 runs exist (`Sec41.exists_isRun`, via a greedy list-arbdefective colouring;
`Sec41.theorem_1_4_exists`), and the floor-variant counterexample comes with an explicit run.
