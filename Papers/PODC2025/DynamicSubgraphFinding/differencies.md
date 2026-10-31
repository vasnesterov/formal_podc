# Differences between the formalization and the paper

Paper: Y.-J. Chang, L. Chen, Y. Chen, G. Mishra, M. Yang, *The Complexity Landscape of Dynamic
Distributed Subgraph Finding* (brief announcement at PODC 2025). Formalized version: arXiv
2411.11544v3 (full version, 51 pp.). Checked: Theorems 1.3, 1.6 (lower bounds, Section 4),
Theorem 1.4 and the algorithm of Theorem 1.7 (Section 5). Sections 2, 6–8 and Appendix A are not
formalized.

## Errors in the paper

1. **The algorithm of Theorem 1.7 is unsound (false claim, ❌).** In the case
   `t_uv − t_uw ≤ d` of the correctness proof (Section 5.3), node `v` lists `{u, v, w}` "by the same
   argument as for node `v` in the proof of Theorem 1.4": it gets `R_edge(u) ∋ j` from its new
   neighbour `u` and had received `(Signal)` from `w` `j` rounds earlier, and concludes that the
   single topological change of that round was the edge `{u, w}`. With node insertions allowed, that
   change can instead be the insertion of a new node `x` adjacent to `u` and `w`. Counterexample
   (maximum degree 2): `G⁰ = {v, w}`; round 2: insert `x` with edges `{x, u}`, `{x, w}`; round 3:
   insert `{u, v}`. Then `v` lists `{u, v, w}`, which is not a triangle.
   Lean: `Alg17.theorem_1_7_algorithm_unsound` (`Theorem17Counterexample.lean`) — for *every* window
   `d ≥ 1`, every implementation of the remaining message parts (Steps 2 and 4: bit reports and
   periodic `1-DBList` updates are an arbitrary extra component `oth`) and every additional output
   rule, an algorithm that sends Steps 1 and 3 as in the paper and lists what the paper's rule for
   `v` infers is not a one-round `List(K₃)` algorithm.
   *Decision rule.* The paper describes only the messages (Steps 1–4); which node lists which
   triangle is stated in the correctness proof. We formalize exactly the rule of that proof for this
   case (`VRule`). *Not formalized:* that no other decision rule rescues the paper's messages. Pen and
   paper (reviewer-checked, assuming `T ≥ 2` and that Step 2 uses only completely received
   `1-DBList`s). The naive triangle variant of (B) (`{u, w}` inserted in round 2 instead of `x`, with
   `{v, w} ∈ G⁰`) does **not** work: there `u` knows `{v, w}` from `G⁰` and can list the triangle.
   Use instead (A'): `G⁰` has no edges. Round 1 inserts `{v, w}`, round 2 inserts `{u, w}` and
   round 3 inserts `{u, v}`. This is the paper's case `t_vw < t_uw < t_uv`, `t_uv − t_uw = 1 ≤ d`.
   Choose identifiers so that `DB(v, w) = DB(v, x)` and `DB(u, v) = DB(u, w) = DB(u, z)`, where
   `DB = 1-DistinctBit`. Then each node of the triangle has the same view as in a triangle-free
   network:
   * `v`, as in (B') = (B) with `{v, w}` inserted in round 1;
   * `u`, as in (C'): round 1 inserts a node `z` with edges to `v` and `w` instead of `{v, w}`.
     `R_edge`s, Signals and `1-DBList` indices coincide;
   * `w`, as in (D'): round 3 inserts a node `x` with edges to `u` and `v` instead of `{u, v}`.
     `u` has no complete `1-DBList_u(w)` yet (its period started in round 2), and `v`'s list from
     `w` is still the empty one of round 1, so no bit reports arrive.
   Hence nobody can list the triangle of (A') soundly.
   *Status of Theorem 1.7 itself.* It is an existence claim; it is **not established** by the paper.
   A repair seems possible at no asymptotic cost (a newly inserted node knows it is new; flag it in
   `(Signal)`, and let `u` report its own insertion age in `R_edge`), but we have not formalized it.
   Corollary 1.8 (`Θ(log log log n)` for `Detect(K₃)` under node and edge insertions) loses its upper
   half accordingly; its lower half is Theorem 1.6.
   Rule R5/R1: the correctness claim of the paper's algorithm is a statement and it is false; the
   theorem is existential and only unestablished, hence ❌ rather than 🚨. Borderline call: the
   abstract presents the upper bounds as a main contribution ("we demonstrate new algorithms to show
   that our lower bounds are tight"). This is a tightness claim, i.e. existential; it does not name
   the specific algorithm. So R5 gives ❌.

2. **Proof of Theorem 1.3, Lemma 4.2: wrong count (proof repaired).** The classes are vectors over all
   `j ∈ [t]` of message patterns, so there are `(2^{O(Bt)})^t = 2^{O(Bt²)}` of them, not
   `t · 2^{O(Bt)}`. The conclusion survives (`2^{O(Bt²)} = n^{o(1)}` for `t = log^{0.1} n`,
   `B = o(log log n)`); Lean: the hypothesis `h2` of `Hard.not_solves_13` is the correct count.

3. **Proof of Theorem 1.3: the friend `c` may coincide with `d`, and `b` may lie in `I*`
   (proof repaired).** Lemma 4.1 only guarantees that `b` has *some* friend w.r.t. `(a, i)`; if `d` is
   its only friend, then `c = d` and (S2) degenerates (`d` is attached to both `K^i` and `K^{i*}`, and
   `a` may learn about `K^{i*}` through `d`). Also `I*` is chosen before `b` and may contain `b`, in
   which case `a` or `d` may equal `b`. Repair: choose `b ∉ I*` and require `b`'s class to have at
   least three elements; the number of bad nodes is at most `2 · #patterns` per `(w, j)` instead of
   `#patterns` (`card_filter_small_class_le`, `select13`).

4. **"`Ω(·)`" is proved as "not `o(·)`" (imprecision).** Both lower-bound proofs assume
   `B = o(log log n)` (resp. `o(log log log n)`) and derive a contradiction; that only shows that the
   bandwidth complexity is not `o(·)`. The counting works with `B ≤ c log log n` for a small explicit
   `c`, which is what we prove: `c = 1/8` for Theorem 1.3, `c = 1/16` for Theorem 1.6, for all `n ≥ N(s)`.

5. Typos / small slips.
   * Section 4.1, "Hard instances": for Theorem 1.6 "`A` is an `o(log log n)`-bandwidth ... algorithm"
     should be `o(log log log n)`.
   * Proof of Theorem 1.6, last paragraph: "if node `b` is responsible ..., as node `a` cannot
     distinguish between (S1) and (S3)" — should be node `b`.
   * Proof of Theorem 1.6: only nodes of `K^i ∪ {a, b}` are considered as possible reporters in (S1);
     the other present nodes (the untouched cliques `K^j`) must also be handled — they see the same in
     (S1) and (S4) (`K_state_none`). Harmless.
   * Proof of Theorem 1.4: the periodic neighbourhood updates start only "when an edge is inserted",
     so edges of `G⁰` never get updates, but node `v`'s case `t_uv − t_uw > d` needs updates along
     `{v, w}` even if `{v, w} ∈ G⁰`. Example: `{v,w} ∈ G⁰`, `{u,w}` inserted in round `t ≥ 1`, `{u,v}`
     more than `d` rounds later — read literally, `v` never learns `{u,w}`. Repair: start the streams
     of `G⁰` edges in round 1 (`Theorem14Alg.lean`). Not checked in Lean as a counterexample.
   * Proof of Theorem 1.4: the WLOG `t_vw < t_uw < t_uv` ignores ties at time 0 (two `G⁰` edges), where
     the argument would use Signals in round 0, which do not exist; covered by `G⁰` knowledge (rule
     `EvG0`).

## Modelling choices

* **Network model** (`Model.lean`). Insertion-only dynamic networks `InsNet V`: present nodes and
  edges per round, monotone. The paper's four change types are reduced to the two insertion types
  needed by the checked theorems: `EdgeIns` (each round inserts at most one edge, no node) and
  `NodeEdgeIns` (additionally: one new node with an arbitrary set of edges to present nodes). Deletions
  are not modelled. Identifiers are the node type `V` (`Fin n` in the final theorems; all identifiers
  are global knowledge).
* **Algorithms.** Deterministic, synchronous; every node knows `G⁰` (present nodes and edges), its
  identifier and the round number; in round `r` the topology change happens first, then every node
  sends one message to each current neighbour (function of its state and current neighbourhood),
  then updates its state. Bandwidth `B` bits is modelled as a message alphabet `M` with
  `|M| ≤ 2^B`. A one-round algorithm must output a correct answer after every round (`Solves`), for
  every network of the model with maximum degree `≤ Δ`.
* **Absent nodes** run the algorithm with local input `none` (so they know the round number and
  `G⁰`, and know whether they are present). This gives them at least as much knowledge as in the paper,
  so the lower bounds are at least as strong; their outputs are ignored.
* **Problems.** `MemDetect(K_s)`: every present node outputs whether it lies in an `s`-clique.
  `Detect(K_s)`: some present node outputs yes iff an `s`-clique exists. `MemList(K₃)`: every present
  node lists exactly its triangles. `List(K₃)`: every triangle is listed by some present node and
  nodes list only triangles (the paper does not say the second half explicitly; without it the
  problem is trivial).
* **Hard instances** (`HardInstance.lean`, `Scenarios.lean`). `create(x, K^i, y)` inserts the edges
  `x–K i k` in rounds `2qi + k + 1` and `y–K i k` in rounds `2qi + q + k + 1` (`q = s − 2`, 0-based
  `i`); the paper does not fix the order inside an interval. In the node-insertion model a node of `I`
  is inserted together with its first edge (the paper: "nodes in `I` without incident edges are
  considered as not yet inserted").
* **Parameters.** Theorem 1.3: `t = 2^{B+1}` instead of `log^{0.1} n` (any `t` with `|M| < t` and
  `2^{O(Bt²)} ≪ n` works); Theorem 1.6: `t = 4^{B+1}` instead of `log^{0.1} log n`. The colour of
  Lemma 4.4 contains only the messages that the proof uses (from `K^i` to `x` and `y` in rounds
  `1..t_final`, and from `x` and `y` to `K^i` in round `t_final`); the two messages across `{x, y}` are
  handled separately by Lemma 4.5, as in the paper's proof.
* **Statements.** Theorems 1.3/1.6 are stated as: for every `s ≥ 3` there is `N` such that for all
  `n ≥ N`, every one-round algorithm on `[n]` with `B`-bit messages solving the problem on networks of
  maximum degree `s − 1` has `B ≥ (1/8) log₂ log₂ n` (resp. `(1/16) log₂ log₂ log₂ n`).
* **Theorem 1.7 algorithm** (`Theorem17Counterexample.lean`): `R^d_edge` contains the ages
  `a ∈ [1, d]` (rounds `r − a`) in which the node got a new neighbour; a node "obtains a new edge"
  iff a new identifier appears in its neighbour list (it cannot tell edge from node insertions).
* **Theorem 1.4** (`Theorem14Alg.lean`, `Theorem14Correct.lean`, `Theorem14.lean`).
  * Parameters `d = ⌊log₂ n⌋ + 2` (instead of `⌈log n⌉`, so that `T = ⌊d/2⌋ ≥ 1` for every `n`); the
    correctness theorem `alg14_solves` holds for every `T ≥ 1` with `2T ≤ d`.
  * Messages: Signal bit; to a new neighbour, `R_edge` and `R_signal` as padded lists of ages
    `a ∈ [1, d]` (sizes `≤ Δ`, `≤ Δ²` proved, no truncation); one block of the periodic update. Each
    period encodes the neighbourhood at the start of the period via an injection
    `(Fin Δ → Option V) → (Fin T → Fin K)`, `K = 2^{2Δ}`, which exists by counting
    (`(n+1)^Δ ≤ 2^{2ΔT}`); the receiver decodes by choosing the unique preimage.
  * Bandwidth statement: `|M| ≤ 2^{10 Δ² (⌊log₂ ⌊log₂ n⌋⌋ + 1)}` for `Δ ≥ 1`, i.e. `O(Δ² log log n)` bits.
  * Output rules (the paper argues only completeness): `G⁰` edge; two Signals in the same round
    (node `w`); periodic list contains the third node (case `> d`); `R_signal` of the new neighbour
    contains the age of the own edge (node `u`, "`j ∈ R_edge(u)`" made precise as "my edge to `y`
    appeared in round `t − j`"); `R_edge` of the new neighbour contains the age of a Signal from `y`
    (node `v`). Soundness (no non-triangle listed) is proved using "at most one edge per round, no
    deletions"; the paper's node-`u`/node-`v` cases are unified via `m = max(t_zy, t_xy)`.
