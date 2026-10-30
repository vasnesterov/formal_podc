# Differences between the formalization and the paper

Paper: R. Ostrovsky, M. Perry, W. Rosenbaum, *Space-Time Tradeoffs for Distributed Verification*,
arXiv:1605.06814 v2 (full version of the PODC 2016 brief announcement by Baruch, Ostrovsky and
Rosenbaum). Numbering follows the arXiv version.

## Model

1. **Views.** A `t`-round verifier is any function of the labelled radius-`t` ball of the node, up to
   isomorphism (`BallIso`, `TPLS.isLocal` in `Basic.lean`). The ball holds the nodes at distance `≤ t`
   with their states and labels, and the edges incident to nodes at distance `< t`. The paper
   (Section 2.1) describes synchronous message passing. It says that with identifiers "an algorithm has
   the same output for all legal assignments of unique IDs", and Sections 1.1 and 4 claim that the lower
   bounds hold in this identifier model. A deterministic algorithm with identifiers whose output does not
   depend on them computes exactly such a function, so the ball model is the paper's identifier model.
   Message size, memory and the run time of the paper's algorithms are not modelled. Only label size and
   verification radius are.
2. **Vertex types.** A scheme must work on configurations over every finite vertex type `V : Type`. This
   lets the lower bound run the verifier on a connected component of a graph, as the paper does in the
   proof of Proposition 4. The verifier does not know `n`, and neither does the paper's.
3. **Verifier output.** It is a `Prop`, and verifiers need not be computable, as is usual for PLS lower
   bounds. The upper-bound verifiers are explicit predicates.
4. **Identifiers.** For Theorem 1 the identifiers are part of the states, and the verifier sees them
   through the states in its ball (`Universal.lean`). This is identity-aware, as Section 3.1 requires.
5. **Anonymous model** (`Anonymous.lean`). Views are depth-`t` view trees, i.e. what a node learns by
   anonymous broadcast. They are used only to show that Proposition 4 holds without identifiers.

## Section 3.2: Definitions 2–3, Proposition 4, Theorem 5

6. **Proposition 4 and Theorem 5 are false in the identifier model for `t ≥ 2`.** Decided by R1/R4: the
   paper claims explicitly that "the lower bounds of Subsections 3.2 and 4.1 hold for a stronger model
   where vertices have unique identifiers" (Section 1.1, repeated at the start of Section 4).
   - The counterexample has `r ≥ 2` disjoint triangles, `e_i = ((i,0),(i,1))`, `t = 2`, `q = 3`, and
     `P` = "every node lies on a triangle". All hypotheses hold (`triangles_hyp`, `theorem_5_false`).
     The crossing of two triangles is a 6-cycle on which `P` fails. Yet a 2-round verifier with empty
     labels decides `P` (`triScheme`): in two rounds a node learns whether two of its neighbours are
     adjacent, which is ID-independent.
   - So the label size is `0` for all `r`, not `Ω(log r / 3)`. For every `i ≠ j` the 6-cycle component
     is rejected under every labelling (`proposition_4_false`).
   - The false step is the proof's claim that every node of `N_t(e_i) ∪ N_t(e_j)` has "the same
     `t`-neighbourhood" in `G` and in `C(e_i, e_j, G)`. This fails whenever `e_i` lies on a cycle of
     length `≤ 2t+1`.
7. **Severity of item 6 (borderline ❌/🚨).** The abstract presents "a general technique to prove lower
   bounds" as a contribution. The technique is sound without identifiers (item 8), where `F` arbitrary
   and Proposition 4 as stated are fine. It is also sound in the identifier model for the paper's own
   application (Theorem 7, a path). What is false is the explicit extension to the identifier model, a
   secondary claim. Hence ❌, not 🚨.
8. **The anonymous model** (`Anonymous.lean`). In the identifier-free broadcast model, where views are
   view trees, Proposition 4 holds. The crossing preserves every depth-`t` view, and this is the repaired
   proof (`proposition_4_view`, `proposition_4_accept`; pigeonhole form `proposition_4_anon`; Theorem 5
   as `theorem_5_anon`, `theorem_5_anon_length`). Theorem 5's item 3 needs the violating component to
   belong to `F`, which the paper leaves implicit. Crossing two triangles changes no depth-2 view
   (`triangles_view_eq`). With port numbers, the isomorphisms must also preserve ports.
9. **Proof gap in the counting.** "`|ℓ| < (log r)/q` ⇒ `|L_i| < log r` ⇒ fewer than `r` options" is
   right only for fixed-length labels. Distinct tuples of variable-length strings can have the same
   concatenation, and there are `2^{|ℓ|+1} - 1` strings of length `≤ |ℓ|`. We count label tuples
   instead: a labelling with values in `A` forces `r ≤ |A|^q`. For strings of length `≤ L` this gives
   `log₂ r < q (L+1)` instead of `log₂ r ≤ qL`. The asymptotics are unaffected. This is a proof repair
   (🛠️).
10. **Hypotheses.** `CrossingHyp` asks for isomorphisms between any two neighbourhoods, not only from
    `N_t(e_1)` to each `N_t(e_i)`. The two are equivalent, and our version is stronger, which is the
    right direction for a counterexample. States are trivial in the counterexample.

## Section 4.1: Theorem 7

11. **Proof route.** Theorem 7 is proved directly in the ball model, without going through Theorem 5,
    which is false there.
    - Every node of the crossed path sees the same labelled ball as some node of the path relabelled by
      a block swap (`crossGraph_accepts`, `key_*`).
    - The cycle component is connected and cyclic and accepts, which contradicts soundness
      (`false_of_equal_windows`).
    - The construction is the paper's: `q = 2t+2`, `r = ⌊n/(2t+2)⌋ - 1`, edges `(q·i, q·i+1)`.
12. **Statement.** The exact bound is `⌊n/(2t+2)⌋ - 1 ≤ |A|^{2t+2}` (`lowerBound_card`). For bit-string
    labels of length `≤ L(n)` this gives `log₂(⌊n/(2t+2)⌋ - 1) < (2t+2)(L(n)+1)` (`theorem_7`), which is
    `Ω(log n / t)` for `t ≤ n/c`.
13. **Large `t` (R2, degenerate).** For `t ≥ n` a verifier with empty labels sees the whole graph, so
    "`Ω(log n / t)`" cannot hold uniformly in `t`. Our exact statement is trivially true there and claims
    nothing. This is not formalized, and the paper's range is `t ≤ log n`.
14. **States.** States are empty (`ι = Unit`), as in the paper's proof.

## Section 4.2: Definitions 10–14, Proposition 16, Lemma 17, Theorem 8

15. **Condition 4 of "correct block labels" is off by one (R3 typo, ⚠️).** It reads "an oriented path
    `w_0, …, w_{k-1} = v` of length `k < t`" with `b(w_0) = head`. A tail is `t - 1` edges, i.e. `t`
    vertices, below its head, so taken literally no tail can satisfy it.
    - For `t = 2` no graph with an edge has a correct labelling (`correctLiteral_two_no_edges`).
    - So Proposition 16 is false as printed, e.g. for the acyclic path on 2 nodes
      (`not_correctLiteral_path`).
    - The intended `k ≤ t` is recoverable from the proof of Lemma 17 ("distance `i_v < t` from a head")
      and from Fig. 1.
    - With `k ≤ t`, Proposition 16 holds for every `t ≥ 2` (`prop16`). Both readings are formalized
      (`Correct`, `CorrectLiteral`).
16. **`t = 1` (R2, degenerate, ⚠️).** Even with `k ≤ t`, no nonempty graph has a correct labelling for
    `t = 1`, since a node would be both head and tail (`correct_one_isEmpty`). In the proof of
    Proposition 16 the labels "head if `d ≡ 0`, tail if `d ≡ -1 (mod t)`" collide. Theorem 8 for
    `t = 1` is the classical 1-round scheme. We state Proposition 16 and Theorem 8 for `t ≥ 2`.
17. **Lemma 17 and Algorithm 1 are not formalized as an algorithm.** `Check` (`AcyclicUpper.lean`) is the
    radius-`t` predicate that Algorithm 1 is meant to compute: each tail checks its block and its child
    blocks, and every node checks the local conditions. `lemma17` proves `(∀ v, Check v) ↔ Correct`.
    By inspection (page 14), Algorithm 1 as printed has slips:
    - `HEAD_CHECK` starts `false` and is set only by messages received from ancestors. A root receives
      only `∅`, so it fails line 35, and every correct labelling is rejected at the root. The evident fix
      is to initialize `HEAD_CHECK ← (b(v) = head)`.
    - The relay loop runs `for i = 1 to t-1`, while the prose and the proof of Lemma 17 use the labels
      "received in the `t`-th round" from the `t`-th ancestor. The message timing is not fully specified.
    These are typos with evident intent and are not counted in the verdict, since Algorithm 1 is not
    formalized.
18. **Theorem 8 radius and range.** The radius is exactly `t`, versus the paper's `O(t)` rounds (`3t`).
    It holds for every `t ≥ 2`, not only `t ≤ min{log n, D}`. Label size is
    `5 + ⌈⌈log₂ n⌉ / t⌉` bits (`theorem8_bits`). The verifier reads the share width off the labels and
    does not know `n`.
19. **Soundness.** It needs neither the colours nor condition 1 of the distance labels. The paper
    includes them for the message-passing implementation, and we keep them in `Correct`.
20. **Lemma 12 and Remarks 11, 15** are not formalized. Soundness is proved through an infinite ancestor
    chain (`AcyclicLabels.lean`).
21. **Typos.**
    - Proof of Proposition 16: "`d(v) = mid` otherwise" should be `b(v)`.
    - The 1-round scheme before Definition 10: "`d(w) = b(v) + 1`" should be `d(v) + 1`.

## Section 3.1: Theorem 1

22. **"For every `t ∈ Ω(D)`": the scheme needs `t ∈ O(D)` (R3 typo; at most ⚠️).** The shares sit at
    distances `0, …, t/4` from the distinguished node `v`, so `v` needs eccentricity `≳ t/4`. The
    introduction says "for every `t ∈ O(diam(G_s))`". We assume `t ≤ 2·diam(G) + 2`. The statement as
    printed is nevertheless true: a node whose eccentricity is `< t` sees the whole configuration in `t`
    rounds and can decide `P` itself (the ball is closed: no node at distance exactly `t`). So the
    combined verifier "decide `P` directly if the ball is closed, otherwise run the universal check"
    works for every `t` (if any node has eccentricity `≥ t`, the diameter is large enough for the
    universal labels). This extension is not formalized; the issue is in the proof's range, not in
    the statement.
23. **Implicit assumptions (R4, ⚠️ at most).**
    - `P` must be invariant under state-preserving isomorphism, as any universal scheme requires
      (`IsoInvariant`).
    - Configurations must be connected.
    - States must be pairwise distinct; this follows from the identifiers that Section 3.1 assumes.
24. **Different verifier.** It is a property of the radius-`(2k-1)` ball, with `k = ⌈t/2⌉` shares (the
    paper uses `t/4`). Each label holds a binary share index (`⌊log₂ t⌋ + 1` bits) instead of the
    paper's `O(1)` bits of orientation, "first in block" and "v-indication". The index term is
    `O(R/t)` in the paper's range. The bound is `2R/t + ⌊log₂ t⌋ + 2` bits with
    `R = n(2s+3) + 2 + min{n(2n+1), m(4⌈log₂(n+1)⌉+1)}` (`theorem1`). Message size is not modelled.
25. **Proof gap in soundness.** "All vertices hold the correct representation" is asserted without
    showing that a decoded configuration consistent with every local view is isomorphic to `G`. We prove
    it by sending each node to its entry and using that the decoded graph is connected (`verify_sound`).
    This is a proof repair (🛠️).

## Not formalized

- Section 4.3 (the recursive `O(log* n)`-space verifier, Theorem 18, Lemma 23) and Appendix A
  (Proposition 25).
- Space and message-size claims of Theorems 1 and 8.
