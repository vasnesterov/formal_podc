# Network Constructors — PODC 2014

Othon Michail, Paul G. Spirakis. *Simple and Efficient Local Codes for Distributed Stable Network Construction.*
PODC 2014. DOI [10.1145/2611462.2611466](https://doi.org/10.1145/2611462.2611466). Formalized version: arXiv
[1309.6978](https://arxiv.org/abs/1309.6978) v2 (full version); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** **Theorem 10 is false**: Protocol 6 (Global-Ring) does not construct a spanning ring.
For `n = 6` there is a globally fair execution in which the network switches forever between a spanning line and a
spanning ring. The other correctness claims checked hold: Theorems 3, 5, 6, 8, 11, and 12 after an obvious typo
fix in Protocol 8, plus the state bound of Theorem 7. Theorem 13 also holds, for `c ≥ 3` and with the output
states we chose. Some of these needed missing details or new proofs. The running-time bounds were not formalized.

## Mistakes in the paper

* **Theorem 10 (Global-Ring) is false.** The proof says the closing rule `(l, q₁, 0) → (l', q₁', 1)` applies
  "whenever one endpoint is in state `l` and the other is in state `q₁`" of the same line. But an `l` endpoint
  of one line can also meet the `q₁` endpoint of another line, since every pair of agents may interact. Then
  the two lines are joined, and two blocked nodes sit next to each other in the middle. Later merges can leave
  a blocked `q₁''` as an internal node of degree 2. Such a node is never unblocked, because its only unblocking
  rules need an active edge to an `l'`/`l''`.

  Concrete run on `n = 6`:
  1. Form two lines, `0–1` and `3–4`, with leaders at `1` and `4`.
  2. `(l, q₁, 0)` on agents `4` and `0` joins the two lines.
  3. The leader of line `0–1` (agent `1`) absorbs agent `2`.
  4. Its endpoint `2` closes onto `3`. The result is a ring `0–1–2–3–4–0`.
  5. Agents `0` and `3`, both `q₁'` and not adjacent, meet: by `(x', y', 0) → (x'', y'', 0)` both become `q₁''`.
  6. The pair `4` (`l'`), `3` (`q₁''`) reopens the edge `{3, 4}`, and agent `4` (now `l`) absorbs the last
     agent `5`.

  From there the system stays inside a closed set of 8 configurations, which the scheduler can visit forever.
  This set alternates between spanning lines (path `2–1–0–4–5` with agent `3` hanging at `2` or at `5`) and the
  spanning ring `0–1–2–3–5–4–0`, and agent `0` stays `q₁''` forever. Under global fairness every one of these
  configurations recurs, so the output never stabilizes. This is a false statement, not a proof gap. Exhaustive model checking
  shows the protocol is correct for `n ≤ 5`, so `n = 6` is the smallest counterexample. A natural repair is
  Protocol 7 (2RC), which we prove correct. (`GlobalRing.globalRing_not_constructs`)
* **Protocol 8 (kRC) has a typo.** The rule `(l_{k+1}, l_i, 1) → (l_k, l_{i−1}, 0)` for `1 ≤ i ≤ k` produces
  the non-state `l₀` when `i = 1`. Protocol 7 has `(l₃, l₁, 1) → (l₂, q₀, 0)` at the same place. We read `l₀` as
  `q₀`. If `l₀` is instead kept as a dead state, the model checker finds a violation (`k = 3`, `n = 5`: a `K₄` plus
  an isolated `l₀`). With the fix, Theorem 12 holds for all `k ≥ 2` and `n ≥ k + 1` (`KRC.kRC_constructs`). The
  paper's proof is a single sentence ("almost the same ideas as Theorem 11"). It misses that a `k`-regular
  component may have bridges, so its leader must first walk to a cycle edge before opening. Otherwise the
  component splits and nothing is gained. Also, two `k`-regular components are joined by `(l_k, l_k, 0)` and must
  each drop a cycle edge.
* **Theorem 6 (Cycle-Cover) leaves `Q_out` unspecified.** With `Q_out = Q` the claim is false. For `n = 4` the
  protocol can stop at a triangle plus an isolated `q₀`. With `Q_out = {q₂}` the statement holds: the output
  stabilizes to a cycle cover on at least `n − 2` agents (`CycleCover.constructs_cycleCover`). Waste 2 does
  occur, for example at `n = 5` (`CycleCover.waste_two_attained`). The paper's justification of "waste 2" is a
  single sentence. Our proof uses the handshake lemma to rule out a lone `q₁` hanging on a cycle.
* **Theorem 13 (c-Cliques) is under-specified.** Protocol 9 does not make sense for `c ∈ {1, 2}`: indices go out of
  range, and for `c = 2` there are two contradictory rules for `(l₀, l₀, 0)`. The theorem claims every positive
  `c`. `Q_out` is again unspecified, and with `Q_out = Q` the leftover `n mod c` agents form an extra star in the
  output. We take `c ≥ 3` and `Q_out` = states of completed components; then the theorem holds for every `n`
  (`Cliques.cliques_constructs`). The paper's proof is a sketch: it does not treat the release of sub-followers
  (`f_j`) or why merging terminates; our proof lets a partial leader of maximal index absorb the others.
* **Smaller slips.**
  * Theorem 11 needs `n ≥ 3`, which is left implicit.
  * Protocols 7 and 8 list rules for both orientations of some pairs with different outcomes, e.g.
    `(l₁, l₂, 0)` and `(l₂, l₁, 0)`. This contradicts the convention of Definition 1 but is harmless when read
    nondeterministically.
  * Theorem 7's state bound argues that a one-state protocol that activates edges "ends with a global clique".
    It overlooks protocols that also deactivate edges, where the output never stabilizes. The theorem still
    holds (`Star.star_needs_two_states`).
  * Theorem 5's proof only treats the running time. The correctness of Fast-Global-Line is asserted without an
    invariant; our proof supplies one.

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
* stars and cycle covers: simple counting invariants.

**Not formalized.**
* All running-time results: Propositions 1–6, Theorems 1, 2 and 9, and the time parts of Theorems 3–8.
* Theorem 4 (Intermediate-Global-Line); it was only model-checked, for `n ≤ 6`.
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
