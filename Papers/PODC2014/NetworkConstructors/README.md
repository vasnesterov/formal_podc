# Network Constructors — PODC 2014

Othon Michail, Paul G. Spirakis. *Simple and Efficient Local Codes for Distributed Stable Network Construction.*
PODC 2014. DOI [10.1145/2611462.2611466](https://doi.org/10.1145/2611462.2611466). Formalized version: arXiv
[1309.6978](https://arxiv.org/abs/1309.6978) v2 (full version); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** **Theorem 10 is false**: Protocol 6 (Global-Ring) does not construct a spanning ring, but
nothing depends on it and the paper's own 2RC (Theorem 11) gives the spanning ring with fewer states. The other
correctness claims checked hold: Theorems 3, 5, 6, 8, 11, 12 (after a typo fix in Protocol 8, and with a new argument),
the state bound of Theorem 7, and Theorem 13 for `c ≥ 3`. The running times and the universality half of the paper
were not checked.

## Mistakes in the paper

### ❌ Theorem 10 (Protocol 6, Global-Ring)
Protocol 6 does not construct a spanning ring: for `n = 6` a globally fair execution switches forever
between spanning lines and a spanning ring, because the closing rule `(l, q₁, 0) → (l', q₁', 1)` can also
join two *different* lines (`GlobalRing.globalRing_not_constructs`).

**Impact.** The protocol is correct for `n ≤ 5` (exhaustive model checking), so `n = 6` is the smallest
counterexample. No repair of Protocol 6 is proved. Nothing else in the paper depends on Theorem 10, and the separate
Protocol 7 (2RC), with 6 states instead of 9, constructs a spanning ring (`TwoRC.twoRC_constructs`).

**Details.** The proof says the closing rule applies "whenever one endpoint is in state `l` and the other
is in state `q₁`" of the same line. But an `l` endpoint of one line can also meet the `q₁` endpoint of
another line, since every pair of agents may interact. Then the two lines are joined, and two blocked nodes
sit next to each other in the middle. Later merges can leave a blocked `q₁''` as an internal node of
degree 2. Such a node is never unblocked, because its only unblocking rules need an active edge to an
`l'`/`l''`.

Concrete run on `n = 6`:
1. Form two lines, `0–1` and `3–4`, with leaders at `1` and `4`.
2. `(l, q₁, 0)` on agents `4` and `0` joins the two lines.
3. The leader of line `0–1` (agent `1`) absorbs agent `2`.
4. Its endpoint `2` closes onto `3`. The result is a ring `0–1–2–3–4–0`.
5. Agents `0` and `3`, both `q₁'` and not adjacent, meet: by `(x', y', 0) → (x'', y'', 0)` both become
   `q₁''`.
6. The pair `4` (`l'`), `3` (`q₁''`) reopens the edge `{3, 4}`, and agent `4` (now `l`) absorbs the last
   agent `5`.

From there the system stays inside a closed set of 8 configurations, which the scheduler can visit
forever. This set alternates between spanning lines (path `2–1–0–4–5` with agent `3` hanging at `2` or at
`5`) and the spanning ring `0–1–2–3–5–4–0`, and agent `0` stays `q₁''` forever. Under global fairness
every one of these configurations recurs, so the output never stabilizes.

### 🔧 Theorem 13 (Protocol 9, c-Cliques): `c ∈ {1, 2}`
The theorem claims every positive `c`, but Protocol 9 does not make sense for `c ∈ {1, 2}`.

**Impact.** With `c ≥ 3` and `Q_out` = states of completed components the theorem holds for every `n`
(`Cliques.cliques_constructs`).

**Details.** For `c ∈ {1, 2}` indices go out of range, and for `c = 2` there are two contradictory rules
for `(l₀, l₀, 0)`.

### ✏️ Slips
- Protocol 8 (kRC, Theorem 12): the rule `(l_{k+1}, l_i, 1) → (l_k, l_{i−1}, 0)` for `1 ≤ i ≤ k` produces the
  non-state `l₀` when `i = 1`, and if `l₀` is kept as a dead state the protocol fails (`k = 3`, `n = 5`: a `K₄` plus
  an isolated `l₀`, found by the model checker). Protocol 7 has `(l₃, l₁, 1) → (l₂, q₀, 0)` at the same place. We
  read `l₀` as `q₀`; with this fix Theorem 12 holds for all `k ≥ 2` and `n ≥ k + 1` (`KRC.kRC_constructs`).
- Theorem 6 (Cycle-Cover): the paper leaves `Q_out` unspecified, and with `Q_out = Q` the claim is false: for
  `n = 4` the protocol can stop at a triangle plus an isolated `q₀`. With `Q_out = {q₂}` the statement holds: the
  output stabilizes to a cycle cover on at least `n − 2` agents (`CycleCover.constructs_cycleCover`). Waste 2 does
  occur, for example at `n = 5` (`CycleCover.waste_two_attained`).
- Theorem 13 (c-Cliques): with the unspecified `Q_out = Q` the leftover `n mod c` agents form an extra star in the
  output. The statement speaks of the completed cliques only, so we take `Q_out` = states of completed components.
- Theorem 11 needs `n ≥ 3`, which is left implicit (for `n ≤ 2` there is no spanning ring); proved for `n ≥ 3`
  (`TwoRC.twoRC_constructs`).

### Typos
- Protocols 7 and 8 list rules for both orientations of some pairs with different outcomes, e.g.
  `(l₁, l₂, 0)` and `(l₂, l₁, 0)`. This contradicts the convention of Definition 1 but is harmless when read
  nondeterministically.
- Protocol 9, rule `(l'_i, l'_j, 1) → (l'_{i−1}, l'_{j−1}, 0)`: for `i = 1` or `j = 1` it would produce the non-state
  `l'₀`. This case is unreachable: our invariant shows it never occurs.

## Proof gaps (statements true)

### 🛠️ Theorem 12 (kRC, proof)
The paper's proof is a single sentence ("almost the same ideas as Theorem 11") and misses that a
`k`-regular component may have bridges.

**Impact.** Statement true (after the typo fix above); proved with two extra ideas that do not occur in the proof of
Theorem 11 (`KRC.kRC_constructs`).

**Details.** The component's leader must first walk to a cycle edge before opening. Otherwise the
component splits and nothing is gained. Also, two `k`-regular components are joined by `(l_k, l_k, 0)`
and must each drop a cycle edge.

### 🔧 Theorem 6 (Cycle-Cover, waste 2, proof)
The paper's justification of "waste 2" is a single sentence: it overlooks leftovers such as an isolated `q₀` and never
rules out a lone `q₁` hanging on a cycle.

**Impact.** Statement true with `Q_out = {q₂}` (`CycleCover.constructs_cycleCover`).

**Repair.** A counting invariant, and the handshake lemma to rule out a lone `q₁` hanging on a cycle.

### 🔧 Theorem 13 (c-Cliques, proof)
The paper's proof is a sketch: it does not treat the release of sub-followers (`f_j`) or why merging terminates.

**Impact.** Statement true for `c ≥ 3` (`Cliques.cliques_constructs`).

**Repair.** Our proof lets a partial leader of maximal index absorb the others.

### 🔧 Theorem 7 (state bound for stars)
The proof argues that a one-state protocol that activates edges "ends with a global clique", overlooking
protocols that also deactivate edges, where the output never stabilizes.

**Impact.** Statement true; our proof covers this case (`Star.star_needs_two_states`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Network constructors as in Section 3.1, in the shared library
  `Podc/Computability/Distributed/NetworkConstructors/`.
* Agents form any finite type `V` with `n = |V|`; the interaction graph is complete.
* A configuration consists of agent states and symmetric binary edge states. Initially all agents are in `q₀`
  and all edges are inactive.
* In each step the scheduler picks a pair of distinct agents **and** an orientation, and the deterministic
  `δ : Q × Q × {0,1} → Q × Q × {0,1}` is applied. This is the paper's "`C → C'` via encounter `uv`". It covers
  both the `(a,b,c)`/`(b,a,c)` convention and the random choice when `a = b`.
* The adversary is arbitrary subject to **global fairness**, CSLib's `Run.GloballyFair`: a configuration that
  occurs infinitely often has all its successors occur infinitely often.
* "Constructs `T`" means: in every globally fair execution from the initial configuration, the output graph is
  eventually constant and satisfies `T`. The output graph is the set of agents in output states plus the active
  edges among them.
* No randomness. The uniform random scheduler and the expected-time bounds are not modelled.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 3 (Simple-Global-Line, correctness, `n ≥ 2`) | `SimpleLine.constructs_spanningLine` | `SimpleLine.lean` |
| Thm 5 (Fast-Global-Line, correctness, `n ≥ 2`) | `FastLine.constructs_spanningLine` | `FastLine.lean`, `FastLineReach.lean` |
| Thm 6 (Cycle-Cover, waste ≤ 2) | `CycleCover.constructs_cycleCover` | `CycleCover.lean` |
| Thm 6 (waste 2 attained, `n = 5`) | `CycleCover.waste_two_attained` | `CycleCover.lean` |
| Thm 7 (≥ 2 states for a star) | `Star.star_needs_two_states` | `Star.lean` |
| Thm 8 (Global-Star, correctness) | `Star.constructs_spanningStar` | `Star.lean` |
| Thm 10 (Global-Ring) — **false** | `GlobalRing.globalRing_not_constructs` | `GlobalRing.lean` |
| Thm 11 (2RC, `n ≥ 3`) | `TwoRC.twoRC_constructs` | `TwoRC.lean` |
| Thm 12 (kRC, typo fixed, `k ≥ 2`, `n ≥ k+1`) | `KRC.kRC_constructs` | `KRC*.lean` |
| Thm 13 (c-Cliques, `c ≥ 3`) | `Cliques.cliques_constructs` | `Cliques*.lean` |

All names are in namespace `Podc.NetworkConstructors`. The problem definitions of Section 3.2 are in
`Problems.lean`.

Every correctness proof uses the paper's method (`Protocol.constructs_of_reach`). We exhibit an inductive invariant
of the reachable configurations and a closed set of output-stable target configurations. We then show that this
set is reachable from every configuration satisfying the invariant. Under global fairness on a finite
configuration space this is equivalent to construction (CSLib `globallyFair_iff_reach`).

The invariants used:
* lines: a forest of paths with one token per component;
* kRC: degree = state index, plus every component has a leader;
* stars and cycle covers: simple counting invariants;
* Fast-Global-Line: the paper's proof treats mainly the running time and describes the correctness mechanism without
  an invariant; our proof supplies one (`FastLine.constructs_spanningLine`).

**Not formalized.**
* All running-time results: Propositions 1–6, Theorems 1, 2 and 9, and the time parts of Theorems 3–8.
* Theorem 4 (Intermediate-Global-Line); it was only model-checked, for `n ≤ 6`.
* Tightness of the waste in Theorem 6 for `n` other than `5`.
* Replication (Theorem 14) and Section 6 (universality, Theorems 15–19).

**Trust.** The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
* Non-vacuity: globally fair executions exist (`Protocol.exists_fair_execution`), and the hypotheses of
  Theorems 11–12 are satisfiable (examples in `TwoRC.lean` and `KRCMerge.lean`).
* The counterexample for Theorem 10 is checked by `decide` on 6 agents. It works for every choice of `Q_out`
  (the paper gives none for Protocol 6) and also refutes the theorem under the uniform random scheduler,
  since the trap is reached with positive probability.
* One proof (`Cliques.Inv.interact`, the invariant step of c-Cliques) raises `maxHeartbeats` to 1000000.
* Before proving, every protocol was model-checked exhaustively for small `n` (bottom strongly connected
  components of the configuration graph).
* The model is staged in `Podc/` (CSLib candidate) and builds on CSLib's `SelfStabilization/TransitionSystem`
  (global fairness, `exists_globallyFair`).
