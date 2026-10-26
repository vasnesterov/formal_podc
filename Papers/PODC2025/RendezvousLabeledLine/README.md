# Optimal Deterministic Rendezvous in Labeled Lines — PODC 2025

Yann Bourreau, Ananth Narayanan, Alexandre Nolin. *Brief Announcement: Optimal Deterministic
Rendezvous in Labeled Lines.* PODC 2025. DOI
[10.1145/3732772.3733537](https://doi.org/10.1145/3732772.3733537). Formalized version: the full
version, arXiv [2505.04564](https://arxiv.org/abs/2505.04564) v2 (24 pp.); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The main result, Theorem 1.1, holds: rendezvous within
`O(D log* ℓ_min)` rounds of the first wake-up. We prove it with an explicit constant, with no
assumption left open: Lemma 2.1, the cited MIS/colouring subroutine, is also proved. Theorem 3.1
(CarefulWalk), Proposition 3.2 and Lemma 3.4 hold as stated. The complexity proof of Lemma 3.5
(early-stopping coloured ruling sets) does not work as written. The lemma itself is true; we repair
the colouring step of Algorithm 3. Part (2) of Lemma 3.5 is imprecise as worded (it holds for the ruling set
committed by `v`'s commitment round, not for the final one). Lemma 4.5 is proved with `8L` instead of `7L`.

## Mistakes in the paper

* **Lemma 3.5: the running-time proof is invalid (statement true).** The proof bounds the
  commitment round of level `V_i` by `T_i ≤ max(O(R·i), T_{i-1}) + O(R·i)`. It then concludes "by
  induction `T_i ∈ O(R·i)`". This recurrence only gives `T_i = O(R i²)`: `T_i = 1+2+⋯+i` satisfies
  it with equality (`lemma_3_5_recurrence_gap`). The `+O(R·i)` comes from the
  `(deg+1)`-list colouring (line 11), run with Lemma 2.1 in `Θ(R log* n_i) = Θ(R i)` rounds. It
  starts only after all lower levels have committed, because the lists depend on their colours.
  Line 4's "wait `Θ(R·i)` rounds" is therefore also unjustified. Left unrepaired, Theorem 1.1
  would only give `O(D (log* ℓ_min)²)`.
  *Fix.* Keep the membership computation as in the paper: membership of level `i` is decided after
  `816 R i` rounds, because the chain through lower levels only adds `O(R)` per level. Split the
  colouring into two parts:
  * Linial's colour reduction on `G^{9R-1}[N_i]`, where `N_i` is the set of new ruling-set nodes of
    level `i`. It does not need the lower levels' colours.
  * A sweep over the resulting 4096 classes, in which each node takes the least colour in `[17]`
    not used within distance `9R-1`. This costs `O(R)` rounds after the lower levels' colours are
    known.

  Then colours of level `i` are fixed after `40000 R i` rounds, and Lemma 3.5 holds with
  `κ₃ = 40001` (`ES.rule`, `ES.colLe_isLocal`).
* **Lemma 3.5 (2) is imprecise.** "If outside `S`, `v` knows the members of `S` at distance
  `≤ R-1`" holds if `S` means `S_T` at `v`'s commitment round `T`, but is false for the final `S`:
  members of *higher* levels may be missed. Such a node can join `S` within `R-1` of `v`
  after `v` committed, if it is at distance `≥ R` from `v`'s ruling-set neighbour. What `v` knows at
  commitment time is `S_T ∩ N^{R-1}(v)`, which contains at least one node by part (3). That is all
  Algorithm 5 needs (it only needs *some* known ruling-set node). Our interface `ColRuling.knows`
  is stated this way.
* **Lemma 4.5: arithmetic slip; we prove `T_{α,L} + 8L`.** The proof says the `ZWalk(8R_α)` of
  `SearchingWalk` happens between rounds `T+5L` and `T+6L`. It lasts `32R ≤ 2L` rounds, so it can
  end at `T+7L`. In the case `R_β > R_α` the extra delay `τ` then gives `T+τ+5L+24R_β < T+8L`
  rather than `T+7L`. We do not know whether `T+7L` itself fails; the slip only changes the
  constant of Theorem 1.1 (`lemma_4_5`).
* **Minor slips in the proof of Lemma 3.4 (statement true).**
  * The claim that a node `w` with locally maximal `b_w` lies within `2R-3` of `v` is not justified
    as stated: a hill-climbing argument can end farther away (up to `3R-4`).
  * "`N^{3R-4}(v)` contains at most 6 ruling-set nodes, therefore 6 iterations suffice" is off by
    one. With that count one would need 7 iterations.
  * The correct count is that at most 2 added nodes lie on each side of `v`, at distance in
    `[R, 3R-3]`. So 5 iterations suffice and the algorithm's 6 are enough. The same argument
    gives 3 iterations, against Algorithm 3's 4 (`gIter_spec`).
* Typos and conventions:
  * `N^k(v)` is defined as an *open* neighbourhood (distance in `[1, k]`). Line 4 of Algorithm 5
    and the proofs of Lemmas 4.4–4.7 need closed balls.
  * Lemma 4.7 uses "the first bit where the colours differ"; any differing bit works.

Full list of differences (modelling choices, constants, imprecisions):
[differencies.md](differencies.md).

## The formalization

**Model.**
* The line is `ℤ`, with an injective labelling `ℓ : ℤ → ℕ`.
* Time is synchronous rounds. The second agent wakes up `τ` rounds after the first; `τ` is
  arbitrary and unknown. A sleeping agent sits at its start node and can be found there
  (`delayed τ b t = b (t - τ)`).
* The agents are deterministic and identical, with no communication. They know neither `D` nor
  `τ`, neither positions nor orientation.
* **Frame model** (`Algo`, `Line.lean`). An agent cannot see the orientation of the line, but it
  knows the port it entered by, so it can keep walking straight or turn back. We therefore describe
  an algorithm by its trajectory `pos μ t` in the agent's own frame: start node `0`, port 0 at the
  start is `+1`, and `μ` is the labelling read in that frame. The algorithm is *causal*: the move
  in round `t+1` depends only on the labels of the nodes visited by round `t`. The adversary picks
  the start nodes, the delay, the labelling and both frame orientations `ε = ±1`.
  This model allows fewer algorithms than raw port numbers, which an algorithm could exploit, and
  every frame algorithm is implementable with ports. So our upper bounds hold in the paper's model.
* Rendezvous means being at the same node in the same round (`thm_1_1`). The variant with
  simultaneous edge-crossing detection (`MeetOrCross`) is used for Algorithm 5 itself, as in the
  paper.
* **LOCAL / ES-LOCAL** (`LocalBasic.lean`). A `T`-round LOCAL algorithm is a rule
  `(ℤ → ℕ) → ℤ → α` whose value at `v` depends only on the labels within distance `T` of `v`
  (`IsLocal`). Early stopping means the radius depends on the node's own label. Algorithms on the
  unoriented line commute with the isometries of `ℤ` (`IsEquivar`); this is what lets both agents
  simulate the same ruling set.
* `log*` is `lstar n = Nat.logStar n + 1`, the paper's convention `log* ≥ 1` (with `⌊log₂⌋`).

**Main results in Lean** (namespace `Podc.RendezvousLabeledLine`).

| Paper | Lean | File |
|---|---|---|
| Theorem 3.1 (CarefulWalk), any labelled graph | `care_meet` | `Model.lean` |
| Theorem 3.1, agent algorithms on the line | `Algo.care`, `thm_3_1` | `Line.lean` |
| Proposition 3.2 (1), (2) | `prop_3_2_swap`, `prop_3_2_scan` | `Line.lean` |
| Lemma 2.1 (MIS / colouring on `G^k[S]`, max degree `Δ`, `O(k log* n)` rounds) | `misRule_spec`, `misRule_isLocal`, `colRule_spec`, `colRule_isLocal` | `LineLocal.lean` |
| Greedy extension steps (Alg. 2 l. 6–8, Alg. 3 l. 7–9) | `gIter_spec`, `gIterRule_isLocal` | `Greedy.lean` |
| Algorithm 2, Lemma 3.4 | `prsRule`, `lemma_3_4`, `lemma_3_4_isLocal` (`3R(log* n + 267)` rounds) | `PathRulingSet.lean` |
| Algorithm 3 (membership), Lemma 3.5 (ruling set) | `ES.Sle`, `ES.Sle_spec`, `ES.Sle_isLocal` (`816 R i` rounds) | `ESRuling.lean` |
| Algorithm 3 (corrected colouring), Lemma 3.5 (colours) | `ES.colLe`, `ES.colLe_spec`, `ES.colLe_isLocal` (`40000 R i` rounds) | `ESColor.lean` |
| Lemma 3.5 (interface used by Section 4) | `ColRuling`, `ES.rule : ColRuling 40001` | `Rule.lean`, `Lemma35.lean` |
| Gap in the proof of Lemma 3.5 | `lemma_3_5_recurrence_gap` | `Gaps.lean` |
| Algorithms 4, 5, 6 | `zw`, `sw`, `plan`, `alg5`, `algFinal = (alg5 _).care` | `Algorithm.lean` |
| Proposition 4.1, 4.2 | `prop_4_1`, `prop_4_2_1`, `prop_4_2_2`, `prop_4_2_2'` | `Analysis.lean` |
| Lemma 4.3 | `lemma_4_3` | `Analysis.lean` |
| Lemma 4.4 | `lemma_4_4` | `InSync.lean` |
| Lemmas 4.5, 4.6, 4.7 | `lemma_4_5` (bound `8L`), `lemma_4_6`, `lemma_4_7` | `Main.lean` (generic forms `lemma_4_*_gen` in `InSync.lean`) |
| Theorem 1.1, crossing detection, any rule with commitment time `κ R log* ℓ` | `thm_1_1_cross` (bound `(896κ + 14336) D log* ℓ(u₀)`) | `Main.lean` |
| Theorem 1.1, node meetings, any such rule | `thm_1_1` (bound `4 ×` that) | `Main.lean` |
| **Theorem 1.1 (unconditional)** | `thm_1_1_final` (bound `4 (896·40001 + 14336) D log* ℓ(u₀)`) | `Lemma35.lean` |

The bound in Theorem 1.1 holds for every node `u₀` within distance `D` of either starting node, in
particular for the one with the smallest label `ℓ_min`.

**Not formalized.**
* Corollary 1.2 and Remark 5.1 (finite paths, cycles, half-lines).
* The cited Miller–Pelc lower bound `Ω(D log* ℓ_max)`, which is what makes the result "optimal".

**Trust.** No `sorry`; `thm_1_1_final`, `thm_3_1`, `lemma_3_4_isLocal`, `lemma_3_5_recurrence_gap`
and the other listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Theorem 1.1 is unconditional: the ruling-set rule it relies on is constructed (`ES.rule`), not
assumed. CSLib is reused for:
* Linial's colour reduction (`Cslib.LocallyIterative.linial`, `linial_lt`);
* `firstFree`;
* `Nat.logStar` / `Nat.tower`;
* `Nat.pow_clog_lt_mul`.

CSLib candidates:
* the extensional LOCAL-on-`ℤ` framework (`IsLocal`, `IsEquivar`, `Packed`);
* `colRule` / `misRule` (Linial colouring and MIS of `G^k[S]` for sparse `S ⊆ ℤ`);
* `care_meet` (CarefulWalk for any injectively labelled graph).
