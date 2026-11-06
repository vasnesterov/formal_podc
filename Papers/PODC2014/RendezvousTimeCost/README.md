# Time vs. Cost of Deterministic Rendezvous — PODC 2014

Avery Miller, Andrzej Pelc. *Time versus cost tradeoffs for deterministic rendezvous in networks.*
PODC 2014. DOI [10.1145/2611462.2611473](https://doi.org/10.1145/2611462.2611473). Formalized
version: arXiv [1508.02471](https://arxiv.org/abs/1508.02471) v1 (the only version; same text as
the proceedings copy we have). Numbering follows it.

**Verdict: 🔧 Easy fix.** Both main lower bounds hold (Theorem 3.1: cost `E + o(E)` forces time `Ω(EL)`; Theorem 3.2:
time `O(E log L)` forces cost `Ω(E log L)`), and so do Propositions 2.1 (Cheap) and 2.2 (Fast) as stated. The cost
bound of Proposition 2.3 (FastWithRelabeling) needs a new constant, `(8w+6)E`, which keeps Corollary 2.1 (cost `O(E)`,
time `O(L^{1/w}E)`). The proof of Theorem 3.2 relies on the false Fact 3.11, and 10 sectors instead of 6 get around it.

## Mistakes in the paper

### 🔧 Proposition 2.3 (FastWithRelabeling, cost `2·w(L)·E`)
The cost bound `2·w(L)·E` is false: on the oriented 3-ring (`E = 2`) with `L = 2`, `w ≡ 1` and
simultaneous start at nodes 0 and 1, the agents first meet at time 4 with cost `6 > 2wE = 4`
(`prop_2_3_cost_false`).

**Impact.** The time bound `(4t+5)E` is true, and the correct cost bound `(8w+6)E` is still `O(E)` for
constant `w`, so Corollary 2.1 survives, although its proof quotes the false `2cE`
(`prop_2_3_cost_repaired`, `cor_2_1`).

**Details.** FastWithRelabeling runs Algorithm Fast on the new `t`-bit labels (here `t = 2`, labels `01`
and `10`). Its schedule starts with an exploration (`T[1] = 1`) and doubles every bit of `M(ℓ')`. With
simultaneous start, both agents explore in segment 1 in lock-step, which in an oriented ring cannot
produce a meeting. So `2E` is spent before anything distinguishes the agents, and at least one more move
is needed. The failure is not specific to `w = 1`: agents whose new labels share a leading `1` explore in
lock-step for 5 segments (cost `10E > 4E` for `w = 2`), and a simulation of the oriented 5-ring with
simultaneous start gives worst-case cost `44 > 2wE` for `w = 2, 3` (`E = 4`).

**Repair.** Each agent explores in at most `4w+3` segments, so the true bound is `(8w+6)E`
(`prop_2_3_cost_repaired`, `cor_2_1`).

### ✏️ Slips
- The abstract, Section 1.3 and Section 3 say that simultaneous-start Cheap has "cost exactly `E`". Agents may finish
  earlier or meet before finishing, so it is "at most `E`", as Section 2 says (`Upper.cheapSim_bounds`).
- Facts 3.6–3.8 (proof of Theorem 3.1) need `F > 3φ`, which the paper leaves implicit in `φ = o(E)`
  (`thm_3_1_explicit`).
- Fact 3.7's index range is off by one: it is stated for `i ≤ ⌊L/2⌋ - 1` but refers to `α_{i+1}` (`LBCost.step`).
- Proposition 2.2's proof mixes `τ ≥ 1` with `0 ≤ τ ≤ E`, an off-by-one in the round numbering (`Upper.prop_2_2`).

### Typos
- Proposition 2.2's proof says "`i ∈ {2,…,m}`" for "`i ∈ {1,…,m}`".
- Corollary 2.1 uses `t' = c L^{1/c}` as if it were an integer.

## Proof gaps (statements true)

### 🔧 Theorem 3.2 (Fact 3.11)
Fact 3.11 is false: on the ring with `n = 12`, `x` moving `+1,+1,+1,-1` from node 0 and `y` moving
`-1,-1,-1,+1` from node 6 have all partial surpluses `±1`, yet both are at node 3 after round 3
(`Fact311.fact_3_11_false`).

**Impact.** Fact 3.15 is not established as written; the rest of the proof of Theorem 3.2 stands with different
constants (`thm_3_2_core`, `thm_3_2`).

**Details.** The proof cuts the ring into 6 sectors of size `n/6` and time into blocks of `n/6` rounds,
and it tracks the sector of each agent only at block boundaries. Fact 3.11 claims that partial surpluses
of absolute value at most 1 keep `x` inside `P_{j-1} ∪ P_j ∪ P_{j+1}`. In mid-block, however, an agent at
the end of `P_{j+1}` can step into `P_{j+2}` and return. In the counterexample `Agg_x = (1,0)` and
`Agg_y = (-1,0)`. The vectors come from a correct 2-label algorithm and survive trimming
(`Fact311.V_correct`, `Fact311.mx_ge_four`). Fact 3.15 (distinct labels have distinct progress vectors)
uses Fact 3.11 on every zero run.

**Repair.** Blocks and sectors of size `⌊n/10⌋`. Two agents with equal progress vectors then stay within
distance `< 5⌊n/10⌋ ≤ n/2` relative to their antipodal starts. This also removes the assumption `6 ∣ n`.
The rest of the argument is the paper's, with different constants. (`thm_3_2_core`, `thm_3_2`)

### 🔧 Theorem 3.2 (Fact 3.16, count of vectors)
The count of `{-1,0,1}`-vectors with at most `k` non-zero entries forgets the factor `2^i` for signs.

**Impact.** Only constants change (`thm_3_2_core`).

### 🔧 Theorem 3.1 (Fact 3.1, witness)
Fact 3.1's shifted start `p'_B = p_A + forward(A) + 1 + back(B)` uses `B`'s solo extent instead of its
extent during the execution.

**Impact.** The fact itself is true (`LBCost.back_le_phi`).

**Details.** With `B`'s solo extent the segments can overlap around the ring; the extent within the
execution works.

Full list of differences (including modelling choices and minor imprecisions):
[differencies.md](differencies.md).

## The formalization

**Model.**
* *Upper bounds (Section 2, `Segments.lean`).*
  - Nodes form an arbitrary type `V`. `EXPLORE` is any walk that visits all nodes within `E`
    rounds from every start (`Explore V E`). The paper only uses this property; no graph or port
    structure is needed, so the bounds hold more generally.
  - Synchronous rounds; one agent wakes at time 0 and the other `δ ≥ 0` rounds later (adversarial).
    A sleeping agent waits at its start node and can be found there.
  - Labels are distinct integers in `[1, L]`. The algorithms are deterministic segment schedules
    (Cheap, simultaneous-start Cheap, Fast, FastWithRelabeling).
  - Time is the first meeting time, counted from the earlier wake-up. Cost is the number of moves
    of both agents before it.
* *Lower bounds (Section 3, `Ring.lean`).*
  - The network is the oriented ring `ZMod n` with `E = n - 1`, and the agents start
    simultaneously.
  - An algorithm is a behaviour vector `V : Fin L → ℕ → {-1,0,1}` per label, exactly as in the
    paper. This loses no generality: before meeting, an agent's observations (degree 2, entry
    port) are determined by its own moves.
  - Meeting means the same node at the end of the same round. "Time" and "cost" are worst-case
    over distinct labels and distinct start nodes; `m_x` (procedure Trim) is `mx`.
  - These restrictions only strengthen lower bounds, as in the paper.
* No randomness, no faults.

**Main results in Lean** (namespace `Podc.RendezvousTimeCost`).

| Paper | Lean | File |
|---|---|---|
| Prop. 2.1 (Cheap: cost ≤ 3E, time ≤ (2L+1)E) | `Upper.prop_2_1` (also `Upper.prop_2_1_min`: time ≤ (2ℓ_min+3)E) | `Cheap.lean` |
| Simultaneous-start Cheap (cost ≤ E, time ≤ (L−1)E) | `Upper.cheapSim_bounds` | `Cheap.lean` |
| Prop. 2.2 (Fast) | `Upper.prop_2_2`, `Upper.prop_2_2_min` | `Fast.lean` |
| Prop. 2.3, time `(4t+5)E` | `Upper.prop_2_3_time` | `Fast.lean` |
| Prop. 2.3, cost `2wE` — **false** | `Upper.prop_2_3_cost_false`; repaired `Upper.prop_2_3_cost_repaired` (`(8w+6)E`) | `Fast.lean` |
| Cor. 2.1 | `Upper.cor_2_1` | `Fast.lean` |
| Thm. 3.1 (cost `E+o(E)` ⇒ time `Ω(EL)`) | `thm_3_1`; finite forms `thm_3_1_explicit`, `thm_3_1_linear` (cost ≤ E + E/7 ⇒ time ≥ EL/112) | `LowerBoundCost.lean` |
| Facts 3.3, 3.5–3.8 | `LBCost.back_le_phi`, `LBCost.eager_or`, `LBCost.step`, `LBCost.chain_bound` | `LowerBoundCost.lean` |
| Thm. 3.2 (time `O(E log L)` ⇒ cost `Ω(E log L)`) | `thm_3_2` (repaired proof); finite core `thm_3_2_core` | `LowerBoundTime.lean` |
| Fact 3.11 — **false** | `Fact311.fact_3_11_false`, `Fact311.V_correct`, `Fact311.mx_ge_four` | `Fact311.lean` |

**Not formalized.** The memory discussion of Section 1.2, the remarks about alternative wake-up
models in the Conclusion, and the general reduction from port-labelled-graph agents to behaviour
vectors. The paper states that reduction in one sentence; we take behaviour vectors as the model.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity:
- Simultaneous-start Cheap in the ring is correct with cost `≤ E` and time `≤ (L−1)E`
  (`RingCheap.thm_3_1_tight`). So the hypotheses of Theorem 3.1 are satisfiable and its `Ω(EL)` is
  tight.
- The hypothesis of Theorem 3.2 is met by Algorithm Fast (Prop. 2.2). That is proved in the
  Section 2 model only; there is no formal bridge to the behaviour-vector model.

All models are paper-local; no CSLib or `Podc/` code is used.
