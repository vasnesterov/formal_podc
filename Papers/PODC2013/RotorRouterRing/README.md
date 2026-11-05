# The Multi-Agent Rotor-Router on the Ring — PODC 2013

Ralf Klasing, Adrian Kosowski, Dominik Pająk, Thomas Sauerwald. *The Multi-Agent Rotor-Router on the Ring: A
Deterministic Alternative to Parallel Random Walks.* PODC 2013. DOI
[10.1145/2484239.2484260](https://doi.org/10.1145/2484239.2484260). Formalized version: the full version
HAL hal-00735113v2 (September 2014, 28 pp.); numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The delayed-deployment technique (Lemmas 2.1–2.3, the slow-down lemma) is correct
on every graph. The best-case lower bound (Theorem 3.7, cover time `Ω((n/k)²)` for every start set) is true; we
prove it with a new argument and explicit constant, for `n ≥ 8k` instead of `n ≥ 440k²`. Two lemmas are false as
stated. Lemma 3.1 is contradictory because of a misprinted identity, which the proof of Theorem 3.2 then uses.
The first property of Lemma 2.4 fails when two agents cross on an edge. The upper bounds (Theorems 3.2, 3.4,
3.5) and the return-time result (Theorem 4.1) are not formalized. So the headline `Θ(n²/log k)` worst case rests
on the misprinted Lemma 3.1 (plausibly true, needs the corrected lemma and a reworked deployment), and the
headline `O((n/k)²)` best-case upper bound (Theorem 3.5) has a proof gap; neither is established here.

## Mistakes in the paper

### ❌ Lemma 3.1 (the sequence `a_i`, identity (4))
No sequence satisfies (1)–(4) for any `k ≥ 2`: summing (4) `a_i · a₁ = 2/a_i − 1/a_{i−1} − 1/a_{i+1}` over
`i = 1..k` telescopes to `a₁ Σ a_i = 1/a₁`, so (3) `Σ a_i = 1` forces `a₁ = 1`, which is impossible
(`lemma_3_1_false`).

**Impact.** The intended identity is `a_i / a₁ = …`, which is what the lemma's own construction gives
(`a_i = 1/(c b_i)`, `a₁ = 1/c²`). With it, all six properties hold for every `k ≥ 2`
(`lemma_3_1_corrected`). But the proof of
Theorem 3.2 computes with the misprinted form. It obtains `B₁ ∈ Θ(n²/a₁)`, and then, with `a₁ = Θ(1/H_k)`,
writes `Θ(n²/log k)`. That would really be `Θ(n² log k)`. Two slips cancel; with the corrected identity the
computation gives `Θ(n² a₁) = Θ(n²/log k)` as claimed. Theorem 3.2 is not formalized here.

**Details.** The telescoping uses `1/a₀ = 0` (property (1), `a₀ = +∞`) and `a_{k+1} = a_k` (property (2)).
The right-hand sides sum to `1/a₁ + 1/a_k − 1/a_{k+1} = 1/a₁`. Only (1)–(4) and positivity are used; (5)
and (6) are irrelevant. The borderline between ❌ and ⚠️ is discussed in [differencies.md](differencies.md):
the fix is a one-symbol change visible in the lemma's proof, but a later proof reasons with the wrong version.

### ⚠️ Lemma 2.4 (agent domains on the ring, first property)
In a deployment where no two agents ever share a node, a domain need not be a sub-path: on the 6-ring, agents
on `0` and `3` with pointers `0→1, 1→2, 2→1, 3→2` swap along the edge `{1, 2}` in round 2, giving
the agent that started on `0` the domain `{0, 2}` after round 2 (`lemma_2_4_false`; both agents are stopped afterwards).

**Impact.** The intended hypothesis also excludes agents passing each other on an edge, as the proof of
Theorem 4.1 says explicitly ("no two agents meet or pass each other on an edge"). Alternatively a swap can be
re-read as two bounces, since agents are indistinguishable. A label-free form of the domain picture holds in
the undelayed system for every initialization (`pattern_invariant`). The lemma is stated without proof and is
used by Lemmas 2.5–2.9, which are not formalized.

### Typos and slips
- Proof of Lemma 2.1, equation (4) (and the recurrence in the proof of Lemma 2.2): the arrivals up to round
  `t + 1` must use the exits `e_v(t + 1)`, not `e_v(t)` (cf. equation (2)). The lemma is unaffected.
- Lemma 2.8: "holds for `2n²` consecutive time steps `t, …, t + n² − 1`".
- Proof of Lemma 3.6: step (a) uses windows of length `r(n/k)` and step (c) jumps by `r(n/k)`, while step (b)
  and the definition of good vertices use `r(n/(10k))`.
- Lemma 2.5 is stated with the constants `22k` and `11k`. Theorem 3.7 applies it with initial interiors
  `n/(20k)` and needs the scaled conclusion `Ω(n/k)`. The proof of Lemma 2.5 only supports a loss of `11k`
  (the "minimum configuration" `22k, 22k − 11, …`), i.e. `M − 11k ≥ M/2`.

## Proof gaps (statements true)

### 🛠️ Theorem 3.7 (best-case lower bound `Ω((n/k)²)`)
The proof rests on Lemmas 2.5/2.6, whose proofs are sketches, and it misstates its own tools.

**Impact.** Statement true; proved with a new argument and explicit constants (`theorem_3_7`): for `n ≥ 8k`,
every start multiset has a node `v` such that, with all pointers pointing away from `v`, the ring is not covered
before time `n²/(8192 k²)`.

**Details.** The proof
- initializes "in each node the pointer points away from the closest agent". It needs the opposite, the
  negative initialization of Lemma 2.5, where an agent entering a new node is sent back;
- concludes "by Lemma 2.1", which only gives upper bounds on the undelayed cover time. A lower bound needs the
  left inequality of Lemma 2.2/2.3;
- needs Lemmas 2.5/2.6 at scale `n/(20k)` instead of `22k` (see Typos);
- argues that the unexplored stretch "will be explored by agents having domains of sizes at least `Ω(n/20k)`,
  so it takes `Ω(n²/400k²)`". This is not derived from anything proved.

**Repair.** We use a rotor-router potential instead of domains. For `h : ZMod n → ℤ`,
`Φ_h = 2 Σ_u pos(u) h(u) + Σ_v h(pointer target of v)`. Every release of an agent from `v` changes `Φ_h` by
exactly `h(v+1) + h(v−1) − 2h(v)` (`potential_run`). With pointers pointing away from `v`, the pointer part
can only grow for radially non-increasing `h` (`ptr_term_ge`). This gives two inequalities:
- *hit lemma* (`hit_lemma`, parabola `(R − d)²`): reaching `v` from distance `> R` costs `R²` agent-rounds
  within distance `R` of `v`;
- *scale step* (`scale_step`, bump of radius `2R`): `R² N_R(s) ≤ 2R² N_{2R}(0) + Σ_{s'<s} N_{2R}(s')`, where
  `N_R` counts the agents within distance `R` of `v`.

Iterating over the radii `2^m R₀` (`multiscale`) and choosing `v` by counting (`exists_good_center`, which
replaces the good vertices of Lemma 3.6) gives `n² < 8192 k² T` at any covering time `T`. Lemma 2.5 is not
needed.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- *Graph and rotors* (`RotorGraph`, `Model.lean`): finitely many nodes; node `v` has `deg v ≥ 1` outgoing arcs
  in a fixed cyclic order (multi-arcs allowed). A configuration (`Config`) is the number of indistinguishable
  agents per node and a port pointer per node, as in Section 1.3.
- *Rounds*: synchronous. In a round with delays `d`, node `v` keeps `min(pos v, d v)` agents. It releases the
  others one by one along consecutive arcs starting at the pointer, and the pointer advances by the number
  released (`step`). A delayed deployment `D` gives the delays of every round (more stopped agents than present
  means all stop); `undelayed` is `R[k]`.
- *Visits*: `visits c₀ D t v` is the paper's `n_v^D(t)`, i.e. initial agents plus arrivals in rounds `1..t`;
  `Covered`/`CoverTime` are defined from it. `visits_eq_visitsOf` is the paper's description by cumulative exit
  counts, the basis of Lemmas 2.1–2.3.
- *Ring* (`ring n`, `Ring.lean`): `ZMod n`, port 0 to `v + 1`, port 1 to `v − 1`. The initial pointers are
  arbitrary or adversarial as each statement says; no randomness (Section 3.3 on random walks is not covered).
- *Labelled model* (`lstep`, `Domains.lean`): used only for Lemma 2.4, since domains need agent identities.
  Agents on the same node are released in index order.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2.1 (more delays, fewer visits) | `RotorGraph.lemma_2_1` | `Delayed.lean` |
| Remark after Lemma 2.1 (`R[k−1] ≤ R[k]`) | `RotorGraph.visits_remove_agent` | `Delayed.lean` |
| Lemma 2.2 | `RotorGraph.lemma_2_2` | `Delayed.lean` |
| Lemma 2.3 (slow-down lemma) | `RotorGraph.lemma_2_3` | `Delayed.lean` |
| Lemma 2.4, first property, false | `lemma_2_4_false` | `Domains.lean` |
| Lemma 2.4, label-free repaired form | `pattern_invariant` | `Invariant.lean` |
| Lemma 3.1 false as stated | `lemma_3_1_false` | `Lemma31.lean` |
| Lemma 3.1 corrected (`a_i / a₁` in (4)), all six properties | `lemma_3_1_corrected` | `Lemma31Corrected.lean` |
| Theorem 3.7 (for `n ≥ 8k`, constant `1/8192`) | `theorem_3_7` | `Theorem37.lean` |
| Potential identity (tool) | `potential_run` | `Ring.lean` |

**Not formalized.**
- Theorem 3.5 (well-spaced starts, cover time `O((n/k)²)`). Its proof has a gap: an agent "returns to `q_i`"
  after each step, but `q_i`'s pointer then points left, so the next step cannot start "to the right". Also two
  of the `q_i` may coincide. Simulation with hill-climbing over pointer initializations finds cover times
  `≤ 1.25 (L+1)²` for gaps `L ∈ {3, 5, 8}` and up to 32 agents (16 for `L = 8`), so the statement looks true. A rigorous proof needs the
  domain-size dynamics.
- Lemmas 2.5–2.9, Theorems 3.2, 3.4 and 4.1. The proof of Theorem 3.2 uses "cover time is monotone in the ring
  size" without proof; simulation confirms it for its initialization, `n ≤ 60`, `k ≤ 16`.
- Lemma 3.6 and the random-walk results (Section 3.3).

**Trust.** No `sorry`; all listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The counterexamples are checked by `decide` (kernel). Lemmas 2.1–2.3 hold on every rotor graph and every
initialization. `theorem_3_7` quantifies over all start multisets. Paper-local code; the general rotor graph
and delayed-deployment layer (`Model.lean`, `Delayed.lean`) and the potential identity are CSLib candidates.
