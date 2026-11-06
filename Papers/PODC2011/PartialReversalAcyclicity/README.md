# Partial Reversal Acyclicity — PODC 2011

Tsvetomira Radeva, Nancy Lynch. *Brief Announcement: Partial Reversal Acyclicity.* PODC 2011. DOI
[10.1145/1993806.1993880](https://doi.org/10.1145/1993806.1993880). Formalized version: the full version, MIT
technical report MIT-CSAIL-TR-2011-022 (April 14, 2011, 20 pp.), whose numbering we follow.

**Verdict: 🔧 Easy fix.** The main result holds: Gafni–Bertsekas Partial Reversal keeps the graph acyclic in every
reachable state (Theorem 5.5), and the proof via the parity-based variant `NewPR` and the two simulation relations
is formalized in full. The only real repair is a changed case condition in Lemma 5.3 (b), which keeps the paper's
one-or-two-step scheme. Invariant 3.2's "exactly one of the two parts" fails only for an isolated node, where both
parts hold.

## Mistakes in the paper

### ✏️ Slips
- Invariant 3.2, "exactly one" of the two parts: for a node without neighbours, both parts hold in every reachable
  state, so "exactly one" is false (`Counterexamples.inv_3_2_exactlyOne_false`, two nodes and no edges). "At least
  one part" holds for every node and "exactly one" holds for every node with a neighbour (`PR.inv_3_2`,
  `PR.inv_3_2_exactlyOne`). Only "at least one" is used later (Corollaries 3.3, 3.4), so nothing else is affected.
  The case is degenerate whether or not `G` is assumed connected: for connected `G` it only occurs in the one-node
  graph `V = {D}`. The proof of the base case says "if `u` is a source, part 1 does not hold because the direction
  of the edges to all out-nbrs is `out`". This presumes `out-nbrsᵤ ≠ ∅`. For an isolated node, `list[u] = ∅` and
  both parts are vacuous. The paper does not assume that `G` is connected; it only says that nodes need not have a
  path to the destination.
- Proofs of Invariant 3.2 (Case 2), Lemma 5.1 (Part 2, Case 2) and Lemma 5.3 (Part 2, Case 2) say that every
  neighbour of `u` that takes a step adds itself to `list[u]`. Only those that reverse their edge to `u` do: a
  sink `v` with `u ∈ list[v] ≠ nbrsᵥ` keeps that edge. The other neighbours change neither `list[u]` nor `u`'s
  edges, so the arguments go through unchanged.

### Typos
- §4.2 says Invariants 4.1, 4.2 and Theorem 4.3 conclude "that PR maintains acyclicity"; they are about `NewPR`.
- Proof of Lemma 5.1, Part 2, Case 2: "In NewPR, all nodes in T take a step one at a time" should be `OneStepPR`.
  The proof also writes `R` for `R0`.
- Proof of Theorem 5.2: the last step should be `(s'', reverse(S), s')`, not `reverse(u)`.
- Proof of Lemma 5.3, Part 1: "We prove that `t.G' = s.G'`" should be `t'.G' = s'.G'`.

## Proof gaps (statements true)

### 🔧 Lemma 5.3 (b) (simulation `OneStepPR → NewPR`), Cases 1 and 2 of Part 1
The step "`s.list[w] ⊆ in-nbrs_w` (odd parity), so by Corollary 3.4 `s.list[w] = in-nbrs_w`" fails when
`s.list[w] = ∅ = out-nbrs_w`, and then the prescribed single `reverse(w)` of `NewPR` reverses nothing while
`OneStepPR` reverses all of `w`'s edges (`Counterexamples.lemma_5_3_paper_step_fails`).

**Impact.** Statement true; repaired (`lemma_5_3_b`) by choosing the matching sequence differently. Theorems 5.4
and 5.5 stand. The counterexample needs a connected component without the destination. The paper never assumes that
`G` is connected, so it allows such graphs.

**Details.** The even case is symmetric. Corollary 3.4 gives `list[w] = in-nbrs_w` or `list[w] = out-nbrs_w`. Together with
`list[w] ⊆ in-nbrs_w`, the second option only gives `list[w] = out-nbrs_w = ∅`; it does not give
`list[w] = in-nbrs_w`.

The counterexample is a related pair of reachable states. `G'init` is the single edge `0 → 1`, and the
destination `2` is isolated. `s` is the initial state of `OneStepPR`. `t` is reached in `NewPR` by `reverse(1)`,
`reverse(0)` (dummy), `reverse(0)`, so it has the initial orientation and counts `(2, 1, 0)`. Then `(s, t) ∈ R`,
node `1` is a sink, `t.parity[1]` is odd and `s.list[1] = ∅ ≠ nbrs₁`. The paper prescribes one `reverse(1)`, which
reverses `out-nbrs₁ = ∅`, while `OneStepPR`'s `reverse(1)` reverses the edge `{0,1}`.

**Repair.** If the set that `NewPR` would reverse (`in-nbrs_w` for even parity, `out-nbrs_w` for odd) is
nonempty, `OneStepPR` reverses exactly that set, and one step suffices. Otherwise `OneStepPR` reverses all of
`nbrs_w`, which is then the other set, and `NewPR` takes a dummy step followed by a real one
(`NewPR.exists_steps`). Claim 5.4 is proved as in the paper, from Invariants 4.1 and 4.2 (`claim_5_4_even`,
`claim_5_4_odd`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- As in the paper, the whole system is one I/O automaton (no message passing, no failures, no randomness): each
  automaton is a step relation, and "reachable" means reachable from the unique initial state. There is no fairness, since only safety
  (acyclicity) is claimed.
- The initial directed graph `G'init` is primitive: `Network.init u v` means "initially `u → v`, i.e. `u` is left
  of `v`". It is required to be acyclic (`Relation.TransGen init` irreflexive). `G` is its underlying undirected
  graph, and `nbrs`, `in-nbrs`, `out-nbrs` are derived from it. The node type `V` is arbitrary.
- The destination `D` is a field `Network.dest`. No node `D` ever steps, and no result depends on it.
- The state has a direction variable `dir[u,v] ∈ {in, out}` for every ordered pair; only pairs that are edges
  matter. `s.G'` is `arcs N s.dir`: `u → v` iff `{u,v} ∈ E` and `dir[u,v] = out`.
- `PR`'s action `reverse(S)`, with `S` a nonempty set of sinks and `D ∉ S`, is given in closed form
  (`PR.effect`). It equals the paper's `for each u ∈ S` loop whenever `S` is an independent set, which holds in
  every reachable state. `OneStepPR` is `reverse({u})`. `NewPR` reverses `in-nbrsᵤ` or `out-nbrsᵤ` according to
  the parity of `count[u]`.
- Simulating `PR` by `OneStepPR` (Lemma 5.1 (b), Theorems 5.2 and 5.5) assumes a finite node set
  (`[Finite V]`), because `reverse(S)` becomes `|S|` single steps. Everything else holds for arbitrary `V`.
- "Left/right" of the paper's planar embedding is only used for neighbours, so it is the relation `init`.
  Theorem 4.3's "rightmost node of the cycle" argument is reorganized. All nodes on a cycle have the same count
  (Invariant 4.2 (d)). By Invariant 4.1, every arc between two such nodes then goes the `G'init` way (even count)
  or every arc goes the reverse way (odd count), so the cycle would be a cycle of `G'init` or of its reverse.

**Proof remarks.** Invariants 4.1 and 4.2 are derived from a single inductive invariant per edge (`NewPR.EdgeInv`:
equal counts, or the left node one ahead with even count, or the right node one ahead with the left count even).
This replaces the paper's case-by-case induction, which we checked by hand and found correct. The proofs of
Section 4 use, without stating it, the analogue of Invariant 3.1 for `NewPR` (`dir[u,v] = in ↔ dir[v,u] = out`). It
holds (`NewPR.consistent_of_reachable`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Invariant 3.1 | `PR.inv_3_1` | `PR.lean` |
| Invariant 3.2 | `PR.inv_3_2`, `PR.inv_3_2_exactlyOne`; counterexample `Counterexamples.inv_3_2_exactlyOne_false` | `PR.lean`, `Counterexamples.lean` |
| Corollary 3.3 | `PR.cor_3_3` | `PR.lean` |
| Corollary 3.4 | `PR.cor_3_4` | `PR.lean` |
| Invariant 4.1 | `NewPR.inv_4_1` | `NewPR.lean` |
| Invariant 4.2 | `NewPR.inv_4_2` | `NewPR.lean` |
| Theorem 4.3 (`NewPR` acyclic) | `NewPR.thm_4_3` | `NewPR.lean` |
| Lemma 5.1 (a), (b) | `lemma_5_1_a`, `lemma_5_1_b` | `Simulation.lean` |
| Theorem 5.2 | `thm_5_2` | `Simulation.lean` |
| Lemma 5.3 (a), (b) | `lemma_5_3_a`, `lemma_5_3_b`; paper's step fails: `Counterexamples.lemma_5_3_paper_step_fails` | `Simulation.lean`, `Counterexamples.lean` |
| Claim 5.4 | `claim_5_4_even`, `claim_5_4_odd` | `Simulation.lean` |
| Theorem 5.4 | `thm_5_4` | `Simulation.lean` |
| Theorem 5.5 (`PR` acyclic) | `thm_5_5` | `Simulation.lean` |

All names are in the namespace `Podc.PartialReversalAcyclicity`. The model is in `Model.lean`.

**Not formalized.** The complexity remarks of the introduction (Θ(n_b²) reversals, the game-theoretic results of
the cited work). They are quoted from other papers and are not claims of this one. Open: whether the paper's
single-step prescription in Lemma 5.3 ever fails for connected `G`, as is usual for link reversal. The paper's
inference is still unjustified there, but exhaustive search over all DAGs with at most 6 nodes (`modelcheck/bf.py`)
found failing pairs only in disconnected graphs, and we did not prove that the prescription always works. The lemma
itself is proved for all `G`.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
counterexamples are concrete reachable states with explicit executions (`Counterexamples.t3_reachable`), which
also shows that the hypotheses of Lemma 5.3 (b) are satisfiable by nontrivial states. Self-contained, on top of
Mathlib only.
