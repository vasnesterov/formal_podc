# Dynamic Distributed Subgraph Finding — PODC 2025

Yi-Jun Chang, Lyuting Chen, Yanyu Chen, Gopinath Mishra, Mingyang Yang. *Brief Announcement: The
Complexity Landscape of Dynamic Distributed Subgraph Finding.* PODC 2025.
DOI [10.1145/3732772.3733522](https://doi.org/10.1145/3732772.3733522). Formalized version: arXiv
[2411.11544](https://arxiv.org/abs/2411.11544) v3 (full version).

**Verdict: ❌ False claim.** The two lower bounds hold: Theorem 1.3 (`Ω(log log n)` for one-round
`MemDetect(K_s)` under edge insertions) and Theorem 1.6 (`Ω(log log log n)` for one-round
`Detect(K_s)` under node and edge insertions), both on bounded-degree networks, with explicit
constants. Theorem 1.3's proof needs two small repairs. The algorithm of Theorem 1.7 (`List(K₃)` under
node and edge insertions) is incorrect: the rule by which a node infers a triangle is unsound once
node insertions are allowed. So Theorem 1.7 and the upper half of Corollary 1.8 are not established.
Theorem 1.4 (`O(Δ² log log n)` one-round `MemList(K₃)` under edge insertions) holds, once the
periodic updates are also run on the edges of `G⁰`.

## Mistakes in the paper

* **The algorithm of Theorem 1.7 lists a non-existent triangle (false claim).** In the case
  `t_uv − t_uw ≤ d`, the proof lets `v` list `{u, v, w}` by reusing the argument for node `v` in
  Theorem 1.4. When `{u, v}` appears, `v` receives `R_edge(u) ∋ j` from `u`. It had received
  `(Signal)` from `w` `j` rounds earlier. Since only one change happens per round, it concludes that
  that change was the edge `{u, w}`. With node insertions, that change can instead be a new node `x`
  adjacent to both `u` and `w`. Network of maximum degree 2: `G⁰ = {v, w}`; round 2 inserts `x` with
  edges `{x, u}` and `{x, w}`; round 3 inserts `{u, v}`. In round 3, `u` reports `R_edge(u) = {1}` and
  `w` signalled in round 2, so `v` lists `{u, v, w}`, but `u` and `w` are not adjacent. The Lean
  theorem covers every window `d ≥ 1`, every implementation of the remaining message parts (bit
  reports, periodic `1-DBList` updates) and every additional output rule.
  We also checked on paper, but not in Lean, that no other decision rule rescues these messages
  (for `T ≥ 2`). This needs a slightly different network: `{v, w}` is inserted in round 1 rather than
  being in `G⁰`. Otherwise `u` could list the triangle from its knowledge of `G⁰`. Then `{u, w}` is
  inserted in round 2 and `{u, v}` in round 3, which is exactly the paper's case `t_vw < t_uw < t_uv`,
  `t_uv − t_uw ≤ d`. With suitable identifiers, each of `u`, `v`, `w` sees the same messages as in
  some triangle-free network. For `v` it is the network above. For `u` it is a network where a node `z`
  adjacent to `v` and `w` is inserted in round 1 instead of `{v, w}`. For `w` it is a network where a
  node `x` adjacent to `u` and `v` is inserted in round 3 instead of `{u, v}`. Theorem 1.7 itself
  (existence of some `O(Δ log log log n)` algorithm) may
  still be true. A fix seems cheap: a freshly inserted node flags itself, and `u` reports its own
  insertion age. We have not formalized such a fix (`Alg17.theorem_1_7_algorithm_unsound`).
* **Theorem 1.3, proof of Lemma 4.2: wrong count; statement true.** A class is a vector of message
  patterns over all `j ∈ [t]`. So there are `2^{O(Bt²)}` classes, not `t · 2^{O(Bt)}`. This is still
  `n^{o(1)}`, so the argument survives (hypothesis `h2` of `Hard.not_solves_13`).
* **Theorem 1.3, choice of `b` and `c`: proof gap; statement true.** Lemma 4.1 only gives `b` *one*
  friend w.r.t. `(a, i)`, so `c = d` is possible. Then `d` is attached to both cliques in (S2), and
  `a` can learn about `K^{i*}` through `d`. Also `I*` may contain `b`. We choose `b ∉ I*` with at least
  two friends besides itself, which costs a factor 2 in the count (`Hard.select13`).
* **Both lower bounds are proved as "not `o(·)`" rather than `Ω(·)`.** The proofs only use
  `B = o(log log n)` (resp. `o(log log log n)`), but the counting works for `B ≤ c · log log n`. We
  prove the `Ω` form with `c = 1/8` (resp. `c = 1/16`).
* Small slips: for Theorem 1.6, the hard-instance paragraph says `o(log log n)` instead of
  `o(log log log n)`. The last paragraph of the proof of Theorem 1.6 says "node `a`" for node `b`.
  The same paragraph forgets the untouched cliques `K^j`, `j ≠ i`, as possible reporters; they see
  the same in (S1) and (S4). Theorem 1.4 never starts periodic updates for edges of `G⁰`; we start
  them in round 1. Example: `{v, w} ∈ G⁰`, `{u, w}` inserted in round `t ≥ 1`, and `{u, v}` more
  than `d` rounds later. Read literally, `v` never learns `{u, w}` (no Lean counterexample).
  The paper also argues only that the true triangles are listed. We add explicit listing rules and
  prove that no node lists a non-triangle.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Deterministic, synchronous, failure-free; no randomness. Insertion-only dynamic networks on the
  identifier set `V` (`Fin n` in the main theorems), with two change models. `EdgeIns`: each round
  inserts at most one edge. `NodeEdgeIns`: alternatively one new node with arbitrary edges to present
  nodes. The adversary is any such network. Deletions are not modelled; no checked result uses them.
* Every node knows `G⁰`, its identifier and the round number. In each round the change happens first.
  Then each node sends one message from the alphabet `M` to each neighbour; `B` bits means
  `|M| ≤ 2^B`. A one-round algorithm must be correct after every round on every network of maximum
  degree `≤ Δ`.
* Theorem 1.4's algorithm (`Theorem14Alg.lean`) uses full-history states (`FullHist.lean`). It uses
  `d = ⌊log₂ n⌋ + 2` and `T = ⌊d/2⌋`. A neighbour list is sent in `T` blocks of `2Δ` bits, using an
  injective encoding that exists by counting. Each round's message also carries a Signal bit and,
  to a new neighbour, the two recent records as lists of ages.
* Not-yet-inserted nodes run with input "absent". They know more than in the paper, so the lower
  bounds are at least as strong; their outputs are ignored.
* The lower bounds quantify over all algorithms (arbitrary state spaces). `NonVacuity.lean` shows
  that with unbounded messages both problems are solvable in one round.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| **Theorem 1.3** (`B ≥ (1/8) log₂ log₂ n`, max degree `s − 1`) | `theorem_1_3` | `Theorem13.lean` |
| Theorem 1.3, finite form (Lemmas 4.1–4.3) | `Hard.not_solves_13`, `select13` | `Theorem13.lean`, `Counting.lean` |
| **Theorem 1.6** (`B ≥ (1/16) log₂ log₂ log₂ n`, max degree `s − 1`) | `theorem_1_6` | `Theorem16.lean` |
| Theorem 1.6, finite form | `Hard.not_solves_16` | `Theorem16.lean` |
| Lemma 4.4 (abstract) | `lemma_4_4` | `Counting.lean` |
| Indistinguishability (S1)/(S2), (S1)/(S3), (S1)/(S4) | `Hard.a_state_S2`, `Hard.a_state_S2F`, `Hard.b_state_S3F`, `Hard.K_state_S4` | `Theorem13.lean`, `Theorem16.lean` |
| **Theorem 1.4** (`card M ≤ 2^{10 Δ² (⌊log₂⌊log₂ n⌋⌋+1)}`) | `theorem_1_4` | `Theorem14.lean` |
| Algorithm of Theorem 1.4 is correct (any `T ≥ 1`, `2T ≤ d`) | `alg14_solves` | `Theorem14Correct.lean`, `Theorem14Alg.lean` |
| Algorithm of Theorem 1.7 is unsound | `Alg17.theorem_1_7_algorithm_unsound` | `Theorem17Counterexample.lean` |
| Non-vacuity (`n`-bit messages suffice) | `memDetect_solvable`, `detect_solvable` | `NonVacuity.lean` |

**Not formalized.** Sections 2, 6–8 (membership listing, one-round detection/listing
characterizations, `r`-round results), Appendix A (randomized), deletion models, and a repaired
Theorem 1.7 algorithm. Corollaries 1.5/1.8 are not stated separately.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The hard scenarios are checked to be valid networks of the respective model with
maximum degree `s − 1` (`edgeIns_S1`, `nodeEdgeIns_S4`, `degLE_S2`, …). Model, full-history algorithms
and the two counting lemmas are CSLib candidates (`Model.lean`, `FullHist.lean`, `Counting.lean`).
