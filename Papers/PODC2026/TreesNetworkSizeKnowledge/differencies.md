# Differences between the formalization and the paper

Paper: Balliu, Brandt, Kuhn, Olivetti, Picavet, Schmid, *The Distributed Complexity Landscape on Trees
Depends on the Knowledge About the Network Size*, PODC 2026 (arXiv 2605.12787 v1). Formalized: Theorem 1
(Section 3) with its proof; non-vacuity of its hypotheses.

## Model and definitions

1. **LOCAL model, extensional.** Algorithms are pairs `(time, out)` with a locality condition
   (`Alg.IsLocal`) instead of message-passing state machines. Every full-information LOCAL algorithm
   with per-node termination satisfies it. The view at round `t` contains all edges incident to nodes
   at distance `≤ t` (`GAgree … (t+1)`), one hop more than standard LOCAL. This only enlarges the class
   of algorithms, so the lower bound is stronger. No input besides the IDs; `n` is not available.
2. **IDs.** Nodes are natural numbers and their names are the IDs (unbounded, arbitrary). The paper
   says IDs are "arbitrary natural numbers"; same.
3. **Graph class.** The algorithm must be correct on all trees of maximum degree `≤ Δ` for a fixed
   `Δ ≥ 3` (the paper assumes a constant `Δ`). Our hard instances have maximum degree 3, so the result
   holds for every constant `Δ ≥ 3`. (For `k = 1` the instances are paths, so `Δ = 2` would also do;
   we do not state that case separately.)
4. **`k`-hierarchical 2½-colouring** is the node-labelled description of Section 2.3 (constraints
   1–4), not the half-edge LCL encoding of Section 2.2. Constraint 3's "same level" is read as: both
   nodes lie in the same level `i ≤ k` (remainder nodes output `D` by constraint 1 anyway).
5. **`Ω(n)`** is Knuth's (the paper says Section 3 uses Knuth's definition): `∃ ε > 0, ∃ n₀, ∀ n > n₀`,
   some `n`-node tree has a node with `time ≥ εn`. The runtime of an algorithm on a graph is the
   largest termination time of a node. The proof's contradiction hypothesis is the exact negation
   ("`< εn` on all `n`-node trees"), where the paper writes "at most `εn`". This is immaterial.

## Lower bound graph (Definition 16, Observation 17)

6. Definition 16 is encoded with explicit identifiers (`comp`; path node `t` = `Nat.pair 0 t`, node `y`
   of the `b`-th attached component of path node `t` = `Nat.pair (2t+b+1) y`). The paper allows an
   arbitrary ID assignment, but its proof needs only one, so fixing it is harmless.
7. Observation 17: only the upper bound is used and proved, with `c₂ = 3^j ≤ 3^k` (`card_comp_le`).
   The lower bound `c₁ L_i` is not needed.
8. That the levels of the 2½-colouring problem on the lower bound graph are the path levels is used
   implicitly in the paper. We prove it via a general criterion (`levelSet_eq`) for every host.

## Proof of Theorem 1

9. **Gap (repaired; decides the verdict 🛠️).** Property 4 is proved with the modified graph `Ĝ`. The
   conclusion "the produced 2-colouring cannot be proper" needs the `u`–`v` path in `Ĝ` to be properly
   2-coloured. That needs all lower-level nodes adjacent to it to output `D` in `Ĝ`, so that no path
   node may output `E`. The induction hypothesis is stated only for `G` ("by running `A` on `G`"), and
   `Ĝ` is not a `k`-hierarchical lower bound graph. Repair: we prove the induction claim (`claim`) for
   every *host*, i.e. every rooted tree with a level labelling satisfying local degree conditions
   (`HostOK`), and every level-`j` component embedded in it by an ID renaming (`Emb`). Hosts are closed
   under the surgery (`hostOK_hat`), and the attached components stay embedded (`emb_hat_child`).
   Verdict rule: a gap in a proof whose statement is true → 🛠️ (R1). The statement is not affected.
   Borderline call (✅ vs 🛠️): one could argue that "the induction hypothesis also holds in `Ĝ`" is
   routine. We count it as a genuine repair for two reasons. The paper explicitly fixes the induction
   to runs on `G`. And applying it in `Ĝ` needs the induction itself to be re-run on surgered graphs,
   whose own property-4 steps do further surgery. So the claim has to be generalised to a class closed
   under surgery.
10. **Induction claim.** We prove "every node of the component outputs `D`" directly, instead of the
    paper's properties 1–4 for two nodes `u`, `v` followed by "this implies that the whole graph is
    labelled `D`". Property 3 is proved for every path node at position `≥ T + 1`
    (`time_le_of_pad`). The padding is attached at position 0, so the upper end needs no condition.
11. **`T_i = ⌊ℓ_i/10⌋`** instead of `ℓ_i/10`, which need not be an integer. Positions: `u` at
    `T+1`, `z` at `2T+3`, `v` at `3T+5` (all `< ℓ_i` since `ℓ_i ≥ 100`), instead of `u`, `v` at
    distance `T_i + 1` from the two ends. `z` is at distance `≥ T + 2` from `u` and `v`; this is
    needed with our generous views (the neighbours of `z` change in `Ĝ`). The paper's "distance at
    least `2T_i + 1`" (property 2) alone would not give a node at distance `> T_i` from both; its
    actual choice of `u`, `v` does.
12. **Padding (`G''`).** The paper extends "an arbitrary path `P₁` at distance `> T_i` from `v`". We
    attach a pendant path of fresh IDs to a level-1 node at position 0 of the component (`leafCode`).
    This keeps the maximum degree at 3 and covers `i = 1`, where `G'` is the path `P₁` itself.
13. **Parameters.** As in the paper, `N_{i+1} = f(1/(20 c₂ L_i), 100 c₂ L_i)` and
    `ℓ_{i+1} = ⌊N_{i+1}/(c₂ L_i)⌋` (`NOf`, `ellOf`, `Lseq`), with `c₂ = 3^k`. From `time < εN` we get
    `time ≤ ℓ_{i+1}/20 ≤ T_{i+1}`.
14. The final contradiction uses constraint 2 at the first node of the level-`k` path. The paper goes
    through Observation 18; this is equivalent.

## Not formalized

15. Theorem 2 (`k`-rake-and-compress). Lemma 19 and Observation 20 are not formalized either. The
    proof of property 1 is a sketch. The parity surgery of Theorem 1 does not transfer directly,
    because a single-sink orientation of a path can be locally consistent (e.g. with increasing IDs,
    every node points to its larger-ID neighbour). We neither verified nor refuted it. It does not
    enter the verdict.
16. Theorems 3–7, Lemma 21 onwards, and the randomized results of Section 7.
