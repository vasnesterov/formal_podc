# Differences between the formalization and the paper

Paper: Radeva, Lynch, *Partial Reversal Acyclicity*, PODC 2011 brief announcement; formalized from the full
version MIT-CSAIL-TR-2011-022.

## Statement-level issues (decide the verdict)

1. **Invariant 3.2, "exactly one of the following is true" — false for isolated nodes.** For a node with no
   neighbours, both parts hold in every reachable state (`Counterexamples.inv_3_2_exactlyOne_false`). We prove
   "at least one" for every node and "exactly one" for every node with a neighbour (`PR.inv_3_2`,
   `PR.inv_3_2_exactlyOne`); in fact both parts hold iff `nbrsᵤ = ∅ ∧ list[u] = ∅` (`PR.part1_and_part2_iff`).
   Rule: **R2** (degenerate: the isolated node is a one-vertex component; the paper never assumes `G` connected
   but routing towards `D` makes connectivity natural; even for connected `G` it fails in the one-node graph
   `V = {D}`, so R2 applies either way) → ⚠️. Borderline between ⚠️ and a mere slip: the
   "exactly one" part is never used later, but it is part of a numbered statement, so ⚠️.

No other numbered statement is wrong; Theorems 4.3, 5.2, 5.4, 5.5, Lemmas 5.1, 5.3, Invariants 3.1, 4.1, 4.2,
Corollaries 3.3, 3.4 are proved as stated (modulo the modelling choices below).

## Proof gaps (statements true)

2. **Lemma 5.3 (b), Part 1, Cases 1/2.** "By Corollary 3.4, because `w` is a sink, `s.list[w] = out-nbrs_w`"
   (even parity), resp. `= in-nbrs_w` (odd parity), does not follow: Corollary 3.4 plus `list ⊆ in-nbrs`
   (odd case) also allows `list = out-nbrs = ∅`. In that case the paper's prescription (one `reverse(w)` step
   whenever `list[w] ≠ nbrs_w`) is wrong: `NewPR` reverses `out-nbrs_w = ∅`, `OneStepPR` reverses `nbrs_w`.
   Concrete related reachable pair: `Counterexamples.lemma_5_3_paper_step_fails` (edge `0 → 1`, isolated
   destination `2`, `t` with counts `(2,1,0)`). The lemma is true: we choose one step if the parity set of `w`
   is nonempty and two steps (dummy + real) otherwise (`lemma_5_3_b`, `NewPR.exists_steps`). The even-parity
   analogue (`in-nbrs_w = ∅ = list[w]` with `w` a sink) cannot occur in reachable `OneStepPR` states but is not
   excluded by the paper's argument either; our proof covers it uniformly. An exhaustive search over all DAGs on
   ≤ 6 nodes, every destination and `NewPR` counts ≤ 4 (`modelcheck/bf.py`) found failing related pairs only in
   disconnected graphs (a component without `D`). This counterexample is within the paper's stated model (connectivity
   is never assumed). For connected `G` the paper's inference is unjustified but not refuted. Either way it is a proof
   gap, not a statement error (R1), so it does not affect the verdict.

3. **"All neighbours in `T` are added to `list[u]`"** (proofs of Invariant 3.2 Case 2, Lemma 5.1 Part 2 Case 2,
   Lemma 5.3 Part 2 Case 2). Only stepping neighbours that actually reverse their edge to `u` are added (a sink
   `v` with `u ∈ list[v] ≠ nbrsᵥ` does not reverse `{u,v}`). Harmless: the other neighbours change neither
   `list[u]` nor `dir[u,·]`. Our proofs use `T = {y ∈ S | u ∈ revSet y}`.

4. **Consistency invariant for `NewPR`.** The Section 4 proofs use "u is a sink, so the edge is directed from v
   to u" for `NewPR`, i.e. the analogue of Invariant 3.1, which is not stated. Proved as part of `NewPR.Inv`
   (`NewPR.consistent_of_reachable`).

## Modelling choices

5. **Graph data.** `G'init` is the primitive (`Network.init`, required acyclic: `TransGen init` irreflexive);
   `G` is its underlying undirected graph (so `nbrsᵤ = in-nbrsᵤ ∪ out-nbrsᵤ` by definition, as in the paper).
   The node type is arbitrary (possibly infinite); `[Finite V]` is assumed only for Lemma 5.1 (b), Theorem 5.2
   and Theorem 5.5, because a parallel step `reverse(S)` is simulated by `|S|` single steps. `OneStepPR.acyclic`
   (acyclicity of `OneStepPR`) needs no finiteness.

6. **Direction variables** `dir[u,v]` exist for all ordered pairs (the paper: only for edges); values on
   non-edges are never read by the automata or by `arcs`. `in` is spelled `Dir.inc`.

7. **`PR`'s effect** is written in closed form (`PR.effect`): `dir[x,y] := out` if `x ∈ S` reverses `y`,
   `:= in` if `y ∈ S` reverses `x`, `list[x] := ∅` for `x ∈ S`, else `list[x] ∪ {y ∈ S | y reverses x}`. The
   paper's sequential loop over `u ∈ S` gives the same result whenever no two nodes of `S` are adjacent, which
   holds in every reachable state (two neighbours are never both sinks, by Invariant 3.1). `OneStepPR` is the
   `S = {u}` instance, so its reachable states are reachable states of `PR` (`OneStepPR.Reachable.toPR`) and
   Section 3 applies to it (the paper uses Corollaries 3.3/3.4 for `OneStepPR` without comment).

8. **Left/right.** The paper's planar embedding of `G'init` is replaced by the relation `init` ("`u` left of
   `v`" for neighbours). Invariants 4.1, 4.2 are stated with `init` (4.1 for the ordered pair with `u` on the
   left; "directed from left to right" = `arcs u v`). Invariant 4.2 (a) `count[v] ∈ {n−1, n, n+1}` is written
   `count v + 1 = count u ∨ count v = count u ∨ count v = count u + 1` (natural numbers).

9. **Proof of Invariants 4.1/4.2.** Derived from one inductive invariant per edge (`NewPR.EdgeInv`) plus
   consistency, instead of the paper's two separate inductions. The paper's inductions were checked by hand and
   are correct.

10. **Proof of Theorem 4.3.** Instead of "take the rightmost node of the cycle", we show that all nodes of a
    cycle have the same count (from 4.2 (d), via `transGen_level`), so by 4.1 every arc of the cycle is a
    `G'init` arc (even count) or every arc is a reversed `G'init` arc (odd count), contradicting acyclicity of
    `G'init`. Same ingredients (4.1, 4.2 (d)), no global embedding needed.

11. **Lemma 5.1 (b)** is proved without the hypothesis that `t` is reachable (not needed). The simulating
    sequence is `reverse(u)` for `u ∈ S` in an arbitrary order (finite-set induction), as in the paper.

12. **Relation `R` of Section 5.3** is `Rel`; "parity odd" is `Odd (count u)`. Claim 5.4 is split into
    `claim_5_4_even` (Part 2) and `claim_5_4_odd` (Part 3, "symmetric" in the paper); both are proved from
    Invariants 4.1 and 4.2 as in the paper.

13. **Typos** (no effect): "PR maintains acyclicity" in §4.2 (means `NewPR`); "In NewPR" in the proof of
    Lemma 5.1 (means `OneStepPR`); `R` for `R0` in the same proof; `reverse(u)` for `reverse(S)` in the proof
    of Theorem 5.2; "`t.G' = s.G'`" for "`t'.G' = s'.G'`" in Lemma 5.3 Part 1.
