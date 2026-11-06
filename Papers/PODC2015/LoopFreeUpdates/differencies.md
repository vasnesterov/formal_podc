# Differences between the formalization and the paper

Ludwig, Marcinkowski, Schmid. *Scheduling Loop-free Network Updates: It's Good to Relax!* PODC 2015.

## Model

* **Instances.** As in §2, only the nodes on both routes are kept: an instance is a pair of duplicate-free
  lists `old` (r₁) and `new` (r₂) that are permutations of each other with the same first node `s` and the
  same last node `d` (`Instance`, `Model.lean`). `out₁`/`out₂` are the successors in these lists.
  The paper additionally assumes `U = V` (every node except `d` must change its rule); we do not. Nodes with
  `out₁ v = out₂ v` are allowed, are never required to be scheduled, and updating them changes nothing
  (`fwd_inter`).
* **Schedules.** A schedule is a list of pairwise disjoint rounds whose union contains every node of
  `U = toUpdate`. Rounds may contain nodes outside `U` (harmless no-ops) and may be empty; the paper asks for
  an exact partition of `U`. This does not change which round counts are achievable (intersect every round
  with `U`).
* **Strong loop-freedom (SLF).** "For all `t` and any `X ⊆ U_t`, `G_t(U, X, E_t)` is loop-free", with
  `E_t = out₁(U_{>t} ∪ X̄) ∪ out₂(U_{<t} ∪ X)`: our `IsSLF` asks `LoopFree (done rounds t ∪ X)` for every
  `X ⊆ rounds[t]`, where `LoopFree A` = the functional forwarding graph of state `A` has no directed cycle.
  Same definition.
* **Relaxed loop-freedom (RLF).** "Only edges reachable from the source": `RelaxedLoopFree A` = no directed
  cycle reachable from `s`; equivalent to "the walk from `s` reaches `d`" (`relaxedLoopFree_iff`).
* **Node types** `FF/FB/BF/BB` (§3.1) are defined with positions on the two routes (`DashedFwd`,
  `SolidFwd`), only for nodes of `U`.
* "A `k`-round schedule" is read as "exactly `k` rounds" (`HasSLF k`); empty rounds make this the same as
  "at most `k` rounds".

## Section 3 (strong loop-freedom)

* **§3.1, 2 rounds** (`hasSLF_two_iff`): as stated (no `BB` node ⇔ 2 rounds suffice).
* **Lemma 1.** Statement: "If there exists a 3-round update schedule S which updates any nodes `V′ ⊆ V` of
  type FB, then there is also a 3-round update schedule which updates all nodes of `V′` in the first round.
  The same holds true for nodes of type FF." Every schedule updates every node, so read literally the FF part
  says that all FF nodes can be moved to round 1. That is false (`lemma_1_FF_literal_false`, 7-node instance;
  it is also contradicted by the paper's own Fig. 4 and would make the 3-round problem trivial). The proof
  only moves nodes **from round 2** to round 1, which is correct; we prove this version for any schedule
  with ≥ 2 rounds (`lemma_1`) and the backward version (round 2 → round 3, `lemma_1_backward`). The FB part
  is true as stated (FB nodes are never in round 3, `solidFwd_of_mem_last`).
  *Label:* ✏️ (the intended version is the one the proof proves; local fix "updates in round 2").
* **Normal form** (§3.2.1, "the problem boils down to finding a distribution of the FF updates"): proved
  as `hasSLF_three_iff` (with our `ofType` sets).
* **Theorem 2 is false** (`gadget_cycle`, `theorem_2_false`). We formalize the gadgets of §3.2.3 for one
  variable `x` with `pₓ = 1`, `nₓ = 0`: 22 nodes, edges and colours exactly as in the text and Figs. 5–6.
  Details the paper leaves open and how we fixed them: (i) the order of the `x₀` and `x̄₀` blocks on the
  assignment path — both orders are covered (`o : Bool`); (ii) the block of a copy is `x^H, x^IN, x, x^BB`
  bottom-up ("`x^H_i` slightly below `x_i` (in the figure we draw it below `x^IN_i` as well)", `x^BB_{i+1}`
  "slightly above `x_{i+1}`"); (iii) the text of §3.2.3 places `x_l^H` "just below `x_l` on the first path" while also saying `v₂` points
  "back to the second solid path"; we follow Fig. 6 and the implication gadget (`x_l^H` below `x_l^IN` on
  `x_l`'s own path), which the paper's own listing of the Fig. 6 cycle (`…, v₂, x_l^H, x_l^IN, x_l, …`)
  confirms; the ring for `x` true does not use `v₂`'s edge at all; (iv) any additional grey nodes on the paths are `B·` and only lengthen the
  solid paths, so they do not affect the cycles. Theorem 2 (⇒) states that setting a satisfying assignment's
  true variables gives a cycle-free second round; for every assignment of the five copies there is a
  second-round cycle, and for `x` true it is the ring
  `x₀ ⇢ x₁^IN → x₁ ⇢ x_l^IN → x_l ⇢ v₃ → v₄ ⇢ x̄_l^H → x̄_l^IN → x̄_l → x̄_l^BB ⇢ x̄₀^H → x̄₀ → v₁ᴬ ⇢ v₂ᴬ → x₀^H → x₀`.
  The proof's step "it will need to continue with edges starting at `x_{i+1}` up to `x_l`, and there is no
  way back from there" overlooks that `x_l`'s dashed edge enters the exclusive gadget, whose `BB` edge
  `v₄ ⇢ x̄_l^H` leads to the false copy `x̄_l`, from which the implication `BB` edges lead backwards through
  all false copies.
  *Label:* ❌ (the failure holds for every formula with at least one variable).
* **The reduction (end of §3.2.4) fails.** `not_hasSLF_three_of_realizes`: every instance containing these
  gadgets with the colours the paper requires (white = FF, black = BB, grey = B·) has no 3-round SLF
  schedule. The paper's instance for any satisfiable 3-CNF formula (e.g. `x ∨ y ∨ z`) contains them, by the
  paper's own description and its claim that §3.2.4 keeps all gadget edges and types. So the reduction maps
  satisfiable formulas to no-instances; the claim "the possibility of making the second round cycle-free in
  our instance is still equivalent to the satisfiability of C′" is false. We did not formalize §3.2.4's
  connection procedure itself (it is under-specified); instead the result quantifies over all completions,
  and `realizes_example` shows that completions exist (a 41-node instance built in the spirit of §3.2.4).
  The defect is not in the connection step: it is already in the gadget graph (Theorem 2).
* **Theorem 1** (3-round decision problem NP-complete). Membership in NP is clear and not formalized.
  NP-hardness is **unestablished**: its only proof is the broken reduction. We neither prove nor refute it.
  The ring is inherent to the gadget design (each implication cycle must lead from the consequent's old rule
  back to the antecedent, so false copies are always traversable backwards); dropping the redundant
  assignment clauses does not help (for `(x̄ ∨ y) ∧ (ȳ ∨ x)` cross-variable rings appear for every
  satisfying assignment; checked by hand, not in Lean).
  *Label:* ❌ (NP-hardness is unestablished).
* **Fig. 2 / §2.2 example** (`LowerBound.lean`): "a strong loop-free schedule needs to go through the backward
  edges one by one … `n − 1` rounds are required": proved exactly (`fig2_slf_lower`, `fig2_hasSLF`,
  `fig2_not_hasSLF`), with `n = |U| = l − 1`; the RLF 3-round schedule of §2.2 is `fig2_hasRLF`. "This is
  worst possible" is read as "every instance has an SLF schedule with `n − 1` rounds"
  (`hasSLF_card_sub_one`, assuming `s ∈ U`, which holds by the paper's definition of `s` as the first node with
  `out₁ ≠ out₂`, and `n ≥ 2`).
* **Appendix A** (greedy can need Ω(n) rounds where O(1) suffice): not formalized.

## Section 4 (relaxed loop-freedom, Peacock)

* **Algorithm 1 as a recursion on merged lines.** The paper merges every updated node into its new successor
  and argues on "trees". We formalize one odd+even pair of rounds on a line `I`: the shortcut set `C`, the
  pruned set `prune C` (all non-updated nodes off the s–d walk), and the merged line `reduce` (both routes
  filtered to the remaining nodes), which is again an `Instance`; then `peacock I = C :: prune C :: peacock
  (reduce I)` (`Peacock.lean`). Soundness of merging is `rlf_of_reduce`.
* **Shortcut selection.** Line 8 of Algorithm 1 is formalized as `Blocks`; the greedy order (non-increasing
  distance) is a merge sort, ties broken arbitrarily (`greedy`). Lemma 2 is proved for any selection with the
  greedy's properties (`GoodSelection`), so every tie-breaking is covered. Line 7 of Algorithm 1 iterates over
  all of `X`; it must range over the forward edges sorted in line 6 (a backward edge outside all chosen
  intervals would otherwise be added and could create a loop). *Label:* ✏️ (evident from line 6 and the
  prose "updating a disjoint set of far-reaching forward edges").
* **Candidates include merged no-op nodes.** After merging, a node may have the same old and new successor in
  the merged line although it still has to be updated in the real network; it is a forward edge of distance
  1 and stays a candidate (the paper's `X = U ∖ U_{<t}` contains it too). Rounds cover all nodes but `d`
  (a superset of `U`); some rounds may be empty.
* **Lemma 2** ("reduces the number of nodes on the solid path from s to d by `n_t/3`"): proved as
  `3 N′ + 1 ≤ 2 N` (`lemma2`, `reduce_length`), where `N′` counts the non-updated nodes on the s–d walk after
  the odd round, i.e. the path *after merging*. With the updated start nodes counted as path nodes the claim
  is false (old `0,1,2,3`, new `0,2,1,3`: the walk `0 → 2 → 3` keeps 3 of 4 nodes). The paper uses merging
  throughout §4 and its Theorem 3 proof counts merged nodes, so we read Lemma 2 this way (✏️). The
  paper's covering argument ("loses at most twice the distance") is correct; it
  even gives the slightly better `N − 1 ≤ Σ (3x_c − 2)`.
* **Lemma 3** (`even_round`, `reduce`): as stated.
* **Theorem 3** (`theorem3`): the explicit bound `#rounds ≤ 2 log_{3/2} n`, where `n` is the number of nodes
  (the paper: `O(log n)`, `n = |U|`; with `U = V ∖ {d}` the two differ by one node). The running time of
  Peacock is not formalized (it is a computable Lean function).

