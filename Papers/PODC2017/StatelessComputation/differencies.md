# Differences between the formalization and the paper

Paper: Dolev, Erdmann, Lutz, Schapira, Zair, *Stateless Computation*, PODC 2017; full version
arXiv 1611.10068v1, the only arXiv version. Numbering follows the arXiv version.

Each item is classified as one of: **false statement**, **false only in a degenerate case**,
**proof gap (statement true)**, **under-specified definition**, **typo**, or **modelling choice**.

## Model (Section 2)

1. **Modelling choice.** The paper's communication graph `G = ([n], E)` is Mathlib's `Digraph V`
   on any finite type `V`. Labels live on `Arc G = {(i, j) // G.Adj i j}`. The paper's `Σ` is the
   type `L`. Inputs `X` and outputs `Y` are arbitrary types; the paper uses `{0,1}`.
2. **Modelling choice.** A schedule is `σ : ℕ → Finset V`, and `σ t` is the paper's `σ(t+1)`.
   `IsRFair r σ` requires that every `σ t` is nonempty, as in the paper, and that every node is
   activated in every window of `r` consecutive steps. With `r = 0` no schedule is `0`-fair, so
   "label 0-stabilizing" holds vacuously. This only matters for Example 1 with `n = 2`.
3. **Under-specified definition.** The paper never says whether `E` may contain self-loops.
   The paper implicitly excludes them; with self-loops a node can keep state on its own loop, and Theorem 3.1 would fail (item 6).
   The formal Theorem 3.1 assumes `∀ v, ¬ G.Adj v v`.
4. **Modelling choice.** "Converges" means "eventually constant". `LabelStabilizing r P` is the
   paper's notion: for every input, initial labeling, initial outputs and `r`-fair schedule, the
   outputs converge and so do the labelings. Part II of the paper works with synchronous
   executions. There we use `SyncLabelStabilizing` and `SyncComputes f`, which require
   convergence, and convergence of the outputs to `f x`, only under the synchronous schedule and
   from every initial labeling. Every `r`-fair notion implies these, so the lower bounds proved
   under these hypotheses are stronger than the paper's.

## Theorem 3.1 (two stable labelings ⇒ not label (n−1)-stabilizing)

5. **Proof gap (statement true).** The valency argument does not work as written. We prove it
   with the following repairs (`Impossibility.lean`).
   - *Valency is ambiguous.* "Attractor regions" are defined by "every path", but the paper never
     says whether paths are taken in the full countdown graph `G'` or in the restricted graph `H`.
     Lemma 3.4 needs valency with respect to `H`: a bivalent state all of whose `H`-successors are
     univalent. If valency is taken in `G'`, its bivalence could come from successors outside `H`.
     If it is taken in `H`, the proof of **Lemma 3.2** does not work: it activates a single node
     from an initial state, and the successor `(r−1, …, r−1, r)` is not in `H`, because `H` needs
     two countdowns equal to `r`. We take valency in `H` (`val`) and prove Lemma 3.2 (`exists_biv`)
     from Lemma 3.3 instead, along a chain of hybrid labelings.
   - *The description of the `H`-successors is false* (in the final paragraph of the proof of
     Theorem 3.1, after Lemma 3.4; Lemma 3.4 itself, the existence of a critical bivalent state, is
     fine). The paper says the `H`-successors of the critical state are all `T` with `|T| ≥ 2` (containing the node with countdown 1, if any). This is
     wrong. Take `r = 4` and countdowns `(2,2,4,4,4)`, whose sorted vector dominates `(1,2,3,4,4)`.
     Activating two of the nodes with countdown 4 gives `(1,1,4,4,3)`, which is not in `H`. The
     argument only needs the admissible sets to be upward closed (`Good.mono`, `cd_mono_set`).
     Then any two admissible sets are joined through `univ` by single-node insertions, and these
     give the pair `S`, `S ∪ {i}` with different valencies (`stable_unique`, the `hall` step).
   - *Lemma 3.3* is correct. We checked the counting step behind "`c(x,{j,j'})` is in `H`"
     (`good_cd_pair`). Its use of the stabilization hypothesis on paths that start at arbitrary
     states of `H` is justified because every `H`-path from a state with countdown `≤ r` is an
     `r`-fair execution from its first labeling (`HPath.fair`).
   - The "assume `H` contains no such cycle" framing is replaced by a direct argument
     (`exists_critical`): otherwise one can choose bivalent successors forever, which gives a
     non-converging `r`-fair execution.
6. **Under-specified definition.** The paper implicitly excludes self-loops: a node communicates
   with "another node `j`", and processors "cannot store information". It never says so explicitly,
   and if self-loops were allowed Theorem 3.1 would fail. On the complete digraph
   with loops on 2 nodes, let every node copy its own loop label to all its outgoing arcs. This
   protocol has 4 stable labelings, yet it is label `r`-stabilizing for every `r`. Lean:
   `SelfLoops.thm_3_1_false_with_loops`.
7. **Modelling choice.** The formal theorem is stronger than the paper's in several ways. It
   speaks about labels only (the run constructed has non-converging labels). Stable labelings are
   taken for one fixed input `x`. `Σ` may be infinite. `G` need not be strongly connected. The
   conclusion holds for every `r ≥ n − 1` (`not_labelStabilizing`), and the theorem exhibits the
   bad initial labeling and schedule (`exists_nonconvergent_run`).

## Example 1 (tightness)

8. **Proof gap (statement true).** The argument only considers labelings in which each node's
   outgoing arcs carry the same bit. Initial labelings with mixed outgoing bits are transient
   (they disappear once every node has been activated, within `r` steps), but the paper does not
   say so. We prove the claim for all initial labelings; it needs only "the activated set is
   contained in `{I(t), I(t+1)}`", not the paper's conditions (1)–(2). For `n = 2`, "label
   0-stabilizing" holds vacuously (item 2). Lean: `Example1.or_tight`. Brute force also confirms
   the claim for `n = 3, 4`.

## Section 2.3 (Propositions 2.1–2.3)

9. **Proof gap (statement true), Prop. 2.1.** The proof is informal ("at least two time steps
   for `j`'s neighbours …"). The round complexity is used without fixing its off-by-one
   convention, and "radius" is not defined for digraphs. We prove the following: if, from every
   initial labeling, all outputs computed from `ℓᵗ` for `t ≥ R` are correct, and `f` is not
   constant, then some node reaches every node by a walk of length `≤ R` (out-radius `≤ R`). Lean:
   `exists_center`. The proof is the paper's "restart from `ℓ_{R}` with a one-bit-different input"
   argument, made precise by a locality lemma (`syncRun_local`).
10. **Prop. 2.2** holds as stated, for any function of the labeling sequence (outputs or labels):
    `Protocol.const_of_converges`, `out_const_of_converges`, `syncRun_const_of_converges`.
11. **Prop. 2.3** holds. The construction is the paper's two-tree protocol. We prove it for any
    rank-certified in-tree and out-tree (`Trees`), and build BFS trees of depth `≤ n − 1` in
    strongly connected digraphs (`exists_trees`). The bound is slightly better than `R_n = 2n`: the
    labeling is constant from step `2n − 1` on and the outputs are correct from step `2n − 1` on.
    Lean: `UpperBound.prop_2_3`, `card_lbl` (`|Σ| = 2^{n+1}`). Only synchronous executions are
    considered, as in Part II of the paper.

## Theorem 5.10 (counting lower bound)

12. **Proof gap (statement true).** The proof counts protocols over one fixed `Σ`, but the
    statement needs a single `f` that no `Σ` with `L_n < n/(4k)` can compute. We sum the count
    over all sizes `s ≤ S` and transport protocols to `Fin |Σ|`.
13. **Proof gap (statement true).** One algebra step is wrong. Going from
    `log n + log(2|Σ|^k) + log log(2|Σ|^k) ≥ n` to `log n + 2k log|Σ| ≥ n` needs
    `1 + log₂(1 + kL) ≤ kL`, which fails for `kL < 3` (e.g. `|Σ| = 2, k = 1`). The final step
    `n − log n ≥ n/2` needs `n` large enough; it holds for `n > 8`.
14. **Under-specified definition.** "A protocol computes at most one function" needs a node, an
    initial labeling (`Nonempty Σ`) and an admissible schedule; otherwise every function is
    computed vacuously. "Maximal degree" of a digraph is read as "in-degree and out-degree `≤ k`".
15. **Strengthening.** We prove the theorem for `n ≥ 6` (instead of `n > 8`), with one `f` for
    all label spaces, and with the weakest notion of computing (synchronous). Lean:
    `exists_hard_function`, `exists_hard_function_logb`. Below `n = 6` the counting argument fails
    (for `n = 5, k = 1` there are already more than `2^{32}` protocols). We did not decide whether
    the theorem itself holds there.

## Section 6 (Theorem 6.2, Corollaries 6.3, 6.4)

16. **Proof gap (statement true; hypotheses unused).** Theorem 6.2 has two bullet conditions
    (`xᵢ = x'ᵢ` on arcs of `C`, `yᵢ = y'ᵢ` on arcs of `D`). The proof never uses them, and we
    prove the theorem without them. We also allow an arbitrary node set `A` in place of `[m]` and
    arbitrary input and output types. Lean: `FoolingSet.card_le_of_isFoolingSet`
    (`|S| ≤ |Σ|^{|C ∪ D|}`) and `logb_le_of_isFoolingSet` (the paper's logarithmic form).
17. **Under-specified definition.** `Nonempty Σ` is needed (see item 14).
18. **False only in a degenerate case (Cor. 6.3).** The paper defines `EQ_n = 1` iff `n` is even
    and the halves are equal, so for odd `n` the function is constantly 0 (and `m = n/2` is not an
    integer). Then `EQ_n ≡ 0` is computed with `|Σ| = 1`, i.e. label complexity
    `0 < (n−2)/8`. Lean: `FoolingSet.cor_6_3_false_odd`. For even `n` we prove the stronger
    bound `2^{n/2} ≤ |Σ|^4`, i.e. `L_n ≥ n/8` (`cor_6_3`, `cor_6_3_logb`), using the full fooling set
    `{(x, x)}`.
19. **Proof gap (corollary still true).** The fooling set of Cor. 6.3, `{(x, x) : x₁ = 1}`,
    violates the paper's own bullet conditions, for example on the arc `(m, m+1)`, which would
    also need `x_m` to be fixed. The corollary survives only because those conditions are
    unnecessary (item 16).
20. **Typo.** In the proofs of Cor. 6.3/6.4 the sets named `C` and `D` are swapped (the set
    written as `C = {(n,1), (n/2+1, n/2)}` consists of arcs into `[m]`). The count
    `|C| + |D| = 4` is unaffected.
21. **Cor. 6.4** holds as stated, for every `n`. The cut of the ring has at most 4 arcs for all
    `n` (`ring_cut_le`). Lean: `cor_6_4` (`⌊n/2⌋ ≤ |Σ|^4`), `cor_6_4_logb`.

## Not formalized

22. Section 4 (Theorems 4.1, 4.2: communication complexity `2^{Ω(n)}` and PSPACE-completeness of
    deciding label `r`-stabilization, Appendix B). Section 5 Theorems 5.2, 5.4 (`OS^u_log = L/poly`,
    `OS^b_log = P/poly`), the counter protocols of Claims 5.5 and 5.6 (the notion of a "D-counter"
    is only described informally), and Corollaries 5.7–5.9.
