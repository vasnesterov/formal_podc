# Differences between the formalization and the paper

Paper: Y. Emek, C. Pfister, J. Seidel, R. Wattenhofer, *Anonymous Networks: Randomization = 2-Hop
Coloring*, PODC 2014 (authors' copy, 10 pages, with proofs).

## Statement-level issues

1. **Lemma 9 / correctness of `A*` as written: unestablished (🔧).** The proof of Lemma 9 claims
   that "the first `k` rounds in `η` for a single node `v` are fully determined by `L_k(v, I)` and
   the first `k − i` bits of each node `u ∈ H_i(v)`". With `L_1` = root only (the paper's
   definition), `k` rounds depend on the view of tree depth `k` (`L_{k+1}`) even without ports. In
   the paper's port-numbering model the message from `u` to `x` may depend on the port number at
   `u`, which depends on `u`'s other neighbours, so `k` rounds depend on `L_{k+2}`
   (`locality_gap`: equal `L_2`, different states after one round, colour-sorted ports, 2-hop
   coloured instances). `A*` compares `L_p(v, I^p)` with candidates and simulates up to
   `l ≤ p − 1` rounds (all bit strings have length `≤ p − 1` in phase `p`). For `l = p − 1` the
   output of `v*` in the simulation is not shown to equal the output of `v` in `η`. The paper also
   does not say which port numbering the simulations use; with any numbering that is a local
   function of the colours the gap remains. We neither prove nor refute Lemma 9 for the original
   `A*`. A full counterexample needs a problem in GRAN with an adversarial Las Vegas algorithm
   `A_R` and an analysis of `A*`'s selection among all candidate graphs; we did not attempt it.
   *Repair (used in the formalization):* Update-Graph uses the view `L_{p+1}(v, I^p)` (tree depth
   `p`) in condition C2 and for `v*` (`AStar.Lv`). This costs `p` rounds, which is the paper's own
   round count for this step ("requires `p` rounds"). With it, Lemmas 5–9 and Theorem 1 hold.
   *Scope of the repair.* Lemma 9 is verified only for `A*` with Update-Graph's view changed from
   `L_p` to `L_{p+1}`, i.e. for a changed algorithm (the false locality claim inside the proof is
   not the only issue; the repair had to change the algorithm, not just the argument). The change
   is a local index fix whose intent is recoverable from the paper (Update-Graph is said to take
   `p` rounds, which is what `L_{p+1}` costs). Lemma 9 for the original `A*` is unestablished, not
   refuted. Theorem 1 (existential) is proved. The paper's §1.3 says randomized algorithms need no
   port numbers, and for a port-oblivious `A_R` the original depth suffices, but `A*` is stated for
   an arbitrary `A_R` that solves `Π` in the port model. Note also that the bits `b^p` encode
   information from beyond the view radius, so the original `A*` may well be correct by a different
   argument; we have neither such a proof nor a counterexample.

## Proof gaps and proof differences (statements true)

2. **Lemma 3.** The proof establishes "every prime factor is isomorphic to `G∞`" but not that `G∞`
   is prime (needed for existence and used in Lemma 7). Repaired: distinct nodes of `G∞` have
   distinct views, so factorizing maps out of `G∞` are injective (`lemma_3`).
3. **Lemma 7.** Compares views of nodes in two different graphs. Theorem 3 (as stated, from Norris)
   is about one graph; the printed proof is terse, truncating subtrees of equal depth-`p` views and
   using Corollary 1 inside each graph. We take another route, colour refinement on the disjoint union (`teq_stable_two`): agreement to
   tree depth `m + n − 1` suffices, and `p ≥ 2n ≥ n + n'`. Our proof then shows the candidate's set
   of views equals that of `I^p` (`AStar.eq_of_mem_Fam`) instead of the truncating-map argument.
4. **Corollary 2** is said to follow from Theorem 3. Theorem 3 gives depth `|V|`, Corollary 2 needs
   depth `|V∞|`. It follows by applying Theorem 3 to `G∞` together with Fact 1 (`corollary_2`).
5. **Corollary 3** is said to follow from Corollary 1; it follows from Fact 1 and Lemma 2
   (`AStar.phase_spec` + `lab_eq_of_trunc_eq`; we use it in the form "the view of `v*` equals the
   node's view").
6. **Lemma 1** depends on how ties and orders are resolved. We make every choice a function of the
   canonical data (`V∞`, the selected view set), so Lemma 1 holds by construction.

## Modelling choices and changed definitions

7. **Port numbering model.** CSLib's `PNGraph`, ports `0 … deg − 1`, two-sided (receiver learns the
   sender's port). Solvability is required for every simple port numbering of every instance.
8. **Randomness.** One bit per node and round, delivered with the round's messages (`RAlg.recv`).
   An algorithm that needs the bit before sending can be simulated with one round of delay, so the
   class GRAN does not change. Deterministic = `recv` ignores the bit (`IsDeterministic`).
9. **Irrevocable outputs**: `out : State → Option O`. A node's output is its *first* output
   (`decided`), so later changes are ignored instead of being forbidden.
10. **Las Vegas solvability.** The proofs use `Solves`: every finite prefix of bits extends to a run
    in which all nodes output, and every run in which all nodes output is valid. The paper's
    definition (termination with probability 1, validity of every labelling of positive
    probability, fair independent coins) is `SolvesAS`. `SolvesAS.solves` proves it implies
    `Solves`. The validity parts are equivalent; `Solves`' termination is weaker. Hence our
    `GRAN` is weaker than the paper's (`GRAN_AS.gran`), and Theorems 1 and 2 are stated for both
    (`theorem_1_AS`, `theorem_2_AS`).
11. **Inputs and degrees.** The paper assumes that the input label of every node contains its
    degree. We do not need this (more general): nodes learn their degree from the port numbering,
    and all view comparisons are of trees whose branching encodes degrees.
12. **Problems** are arbitrary predicates on labelled graphs plus arbitrary validity predicates. No
    isomorphism invariance is assumed (GRAN's decider forces it for the instance set anyway).
13. **Colours** come from a type with a linear order (`[LinearOrder C]`), used for the
    colour-sorted port numbering of the simulations. The paper's colours are bit strings.
    `theorem_2` also assumes `[Nonempty Out]` (the infinity-model function must be total).
14. **Local views.** We define equality of views (`TEq`, `ViewEq`) recursively, never the trees
    themselves. `L_∞(u) = L_∞(v)` is defined as equality at all finite depths, which for finitely
    branching trees is equality of the infinite trees. In 2-hop coloured graphs the view is
    represented canonically by the set of label words of walks (`lang`, `forall_teq_iff_lang`).
    This is the representation of `V∞` and of the input of `A∞`.
15. **Infinity model.** `A∞` is a function of the walk language `⟪X⟫ v`, which is determined by
    `L_∞(v)` (`lang_eq_of_forall_teq`). So it is an infinity-model algorithm in the paper's sense.
16. **Infinite/finite view graph.** `G∞` is `viewLGraph`, with node type the set of walk languages.
    The finite view graph `G*` is not constructed. Corollary 2 is stated as "depth-`|V∞|` views
    separate exactly the infinite-view classes", which is what makes `f_n : V∞ → V*` a bijection. `A*`
    simulates on the infinite view graph of a canonical realizer of the selected view set, which is
    isomorphic to the paper's finite view graph.
17. **Orders and choices in `A*` and `A∞`.** The paper's total orders (on `V∞` via canonical tree
    encodings, on bit assignments, on finite view graphs via bit-string encodings) are replaced
    as follows. A view set with the fewest nodes is selected, with ties broken by a fixed
    well-order (`select`). The successful assignment and the smallest extension are picked by
    choice functions of the canonical data. The analysis only uses that the choices are functions
    of the data all nodes share, and Lemma 7 shows the minimum is unique for `p ≥ 2n`.
18. **Port numbering of the simulations** (unspecified in the paper): colour-sorted (`colorPN`).
    Coverings preserve it (`runC_localIso`), and it is local (`decided_local`).
19. **Message-passing implementation of `A*`.** The paper's phase `p` lasts `p` rounds. We implement
    `A*` as a full-information algorithm (`floodAlg`): nodes flood their truncated walk languages
    and in round `r` evaluate phase `⌊√r⌋` on their current knowledge. Phase `p` needs depth
    `p(p+1)/2 ≤ p²` (`Db`, `outPhase_depthLocal`). The outputs are the same as in the paper's
    schedule, only the rounds at which they are produced differ. Messages are elements of an arbitrary
    type; the flooded truncated walk languages are finite sets, so messages have finite size as the
    paper requires (no bound is imposed, as in the paper). Round complexity is irrelevant in
    the paper.
20. **Computability** of local computations (e.g. deciding C3, enumerating candidates) is not
    modelled. The paper's motivation for `A*` (replacing infinite views by finite ones) is about
    finite rounds, which we do model.
21. **Phase 0.** `bL 0 = []` and phase 0 is vacuous (no candidate has `≤ 0` nodes), matching the
    paper's phases `1, 2, …`.

## Not formalized

- Section 4 (connection to Boldi–Vigna fibrations).
- The introduction's claims: 2-hop colouring, MIS and colouring are in GRAN, and the `k`-hop variant
  of colouring is not in GRAN for `k > 2`. Also the remark `|V| = m |V'|` for factors.
