# Differences between the formalization and the paper

Paper: O. Michail, P. G. Spirakis, *Simple and Efficient Local Codes for Distributed Stable Network Construction*,
PODC 2014; formalized from the full version arXiv:1309.6978v2.

## Model

- **Transition semantics.** Definition 1 says that for distinct states `a, b` the protocol specifies a rule for
  either `(a, b, c)` or `(b, a, c)`, and that for `a = b` with `δ(a, a, c) = (a', b', c')`, `a' ≠ b'`, either agent
  may get `a'`. We take a total `δ : Q → Q → Bool → Q × Q × Bool` (unlisted triples are the identity) and let the
  scheduler choose the pair **and** the orientation (`Protocol.Step`); this is exactly the paper's
  "`C → C'` via encounter `uv`" (Section 3.1) and covers the `a = b` case. Protocols 7 and 8 list both orientations
  for some pairs (e.g. `(l_1, l_2, 0)` and `(l_2, l_1, 0)` in kRC) with different outcomes, contradicting the
  "either … or" convention; under our semantics they are nondeterministic, which is the only sensible reading
  (and what the correctness proofs need).
- **Fairness.** The paper's fairness ("if `C` occurs infinitely often and `C → C'` then `C'` occurs infinitely
  often") is CSLib's `Run.GloballyFair` on the configuration space (agent states and edge states).
- **Configurations.** Edge states are a symmetric function `V → V → Bool` (its diagonal is never read); the agent set
  is any finite type `V` with `n = Fintype.card V`.
- **Output.** `Protocol.output C` is the subgraph of `⊤` with vertices the agents in output states and the active
  edges between them (Section 3.1). "Constructs `G`" (Definition 2) is formalized for graph *classes* `T`
  (isomorphism-closed predicates on the output): the output is eventually constant and in `T`.
- **Problem definitions** (`Problems.lean`) follow Section 3.2 literally (degrees and connectivity):
  `IsSpanningLine`, `IsCycleCover`, `IsSpanningStar`, `IsSpanningRing`; `IsAlmostRegular k` is the conclusion of
  Theorem 12; `IsCliquePartition c` (`c ⌊n/c⌋` output vertices, transitive adjacency, all degrees `c − 1`) is
  "partition into `⌊n/c⌋` cliques of order `c`".
- **Waste (Definition 3).** Not formalized as a "greatest function"; for Theorem 6 we prove the upper bound on the
  waste for every `n` and that waste 2 occurs (`n = 5`).

## Theorems

- **Theorem 3 (Simple-Global-Line).** Correctness proved for every `n ≥ 2` (`SimpleLine.constructs_spanningLine`).
  The running-time bounds `Ω(n⁴)`, `O(n⁵)` are not formalized.
- **Theorem 4 (Intermediate-Global-Line).** Not formalized (only model-checked for `n ≤ 6`).
- **Theorem 5 (Fast-Global-Line).** Correctness proved for every `n ≥ 2` (`FastLine.constructs_spanningLine`). The
  paper's proof only discusses running time; the invariant (one token `l`/`l'`/`l''`/`f₁` per component, the `q₂'`
  mark next to `l'`/`l''`) and the reachability argument are ours. `O(n³)` not formalized.
- **Theorem 6 (Cycle-Cover).** The paper does not specify `Q_out`. With `Q_out = Q` the claim fails (e.g. `n = 4`:
  a triangle plus an isolated `q₀`, or `n = 5`: a triangle plus an edge between two `q₁`); we take `Q_out = {q₂}`
  (which matches "a cycle cover on `n − 2` nodes"). Proved: every fair execution stabilizes to a cycle cover on at
  least `n − 2` agents (`CycleCover.constructs_cycleCover`), and waste 2 is attained for `n = 5`
  (`CycleCover.waste_two_attained`). The tightness for other `n`, the `Θ(n²)` time and the time optimality are not
  formalized.
- **Theorem 7 (Star Lower Bound).** Only the state bound is formalized, for `n = 3` and state set `Unit` (any
  one-state protocol): `Star.star_needs_two_states`. The paper's argument "if `(q₀, q₀, 0)` activates the edge then
  eventually all edges become active" overlooks protocols whose rule `(q₀, q₀, 1)` deactivates; then edges toggle
  forever and the output never stabilizes, which also refutes construction (our proof covers this case).
  The `Ω(n² log n)` time bound is not formalized.
- **Theorem 8 (Global-Star).** Correctness proved for every `n ≥ 1` (`Star.constructs_spanningStar`). Time not
  formalized.
- **Theorem 10 (Global-Ring).** **False.** For `n = 6` some globally fair execution never stabilizes its output
  (`GlobalRing.globalRing_not_constructs`); see README. The closing rule `(l, q₁, 0) → (l', q₁', 1)` also joins two
  *different* lines. The paper does not give `Q_out` for Protocol 6; we take `Q_out = Q`. The counterexample
  does not depend on this choice: in the closed set, configurations whose active graph is the spanning ring
  `0–1–2–3–5–4–0` and configurations missing the edge `{2,3}` or `{3,5}` both recur, so for any `Q_out` the
  output never stabilizes to a spanning ring. Since the closed set is reached with positive probability, the
  protocol also fails with positive probability under the uniform random scheduler.
- **Theorem 11 (2RC).** Proved for `n ≥ 3` (the paper leaves `n ≥ 3` implicit; for `n ≤ 2` there is no spanning
  ring) — `TwoRC.twoRC_constructs`. Protocol 7 is formalized literally and shown to be Protocol 8 with `k = 2`
  (after the typo fix below) rule by rule (`TwoRC.δ_compat`); Theorem 11 is derived from Theorem 12 plus the
  handshake lemma.
- **Theorem 12 (kRC).** Protocol 8 contains a typo: `(l_{k+1}, l_i, 1) → (l_k, l_{i−1}, 0)` for `1 ≤ i ≤ k`
  produces `l_0 ∉ Q` for `i = 1`. We read `l_0` as `q_0` (as in Protocol 7). With `l_0` kept as an extra dead
  state the statement fails (model checker: `k = 3, n = 5`, a `K₄` plus an isolated `l₀`). Proved for every `k ≥ 2`
  and `n ≥ k + 1` (`KRC.kRC_constructs`). The paper's proof is one sentence ("almost the same ideas as Theorem 11");
  the formal proof needs two extra ideas: before opening a `k`-regular component its leader must be moved onto a
  cycle edge (dropping a bridge makes no progress), and two `k`-regular components are joined by
  `(l_k, l_k, 0)` with one non-bridge edge dropped in each.
- **Theorem 13 (c-Cliques).** Proved for every `c ≥ 3` and every `n` (`Cliques.cliques_constructs`). Protocol 9 is ill-defined for `c ∈ {1, 2}` (indices
  `l_{c−2}`, `l̄_1` out of range; for `c = 2` two contradictory rules for `(l₀, l₀, 0)`), so `c ≥ 3`. `Q_out` is not
  specified; with `Q_out = Q` the leftover `n mod c` agents form a star that is part of the output, so we take
  `Q_out = {l, r, 1, …, c − 1, l'_1, …, l'_{c−1}}`. The rule `(l'_i, l'_j, 1) → (l'_{i−1}, l'_{j−1}, 0)` would
  produce the non-state `l'_0` for `i = 1` or `j = 1`; we make it ineffective there (the invariant shows the case
  never occurs). `(l_i, l_j, 0)` is given only for `j ≤ i`, the other orientation coming from the scheduler. The
  paper's proof sketch omits the release of sub-followers `f_j` and the termination of merging; ours is new.
- **Not formalized:** Propositions 1–6 and all expected-time bounds (Theorems 1, 2, 9 and the time parts of
  3–8), Theorem 4, Theorem 14 (Leader-Replication, randomized), Section 6 (Theorems 15–19, TM simulation).
