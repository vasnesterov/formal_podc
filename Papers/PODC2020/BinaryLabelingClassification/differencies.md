# Differences between the formalization and the paper

Paper: Balliu, Brandt, Efron, Hirvonen, Maus, Olivetti, Suomela, *Classification of distributed binary labeling
problems*, arXiv:1911.13294v3 (full version of the PODC 2020 brief announcement).

## Verdict reasoning

All formalized statements (Observation 3.2, Theorems 8.1–8.3, Lemmas 10.4, 10.8, 10.9) are true as stated.
Two proofs need repairs:
- Theorem 8.3: the orientation goes the wrong way.
- Theorem 8.2: an intermediate claim is false for general trees.

Both are claims inside proofs, so by R1 they are proof repairs, not statement errors. Verdict: 🛠️ (R6: worst label).
Borderline: the Theorem 8.3 slip is a wrong direction ("towards" for "away from"). A referee would flag it, so we
count it as a repair rather than a routine detail.

## Proof gaps and errors

1. **Theorem 8.3 proof.** "Choose a leaf as a root and orient all edges towards the leaf." With the paper's convention
   (`X`-edges point black → white) the hardest VI.b problem `(010⁺, 0⁺10)` needs every relevant node to have
   indegree exactly 1. Orienting towards the root gives indegree `deg − 1`. The correct choice is away from the leaf
   (`viHard_exists`). The same slip appears in "always possible to orient a tree towards a root" for the 8.2 problem.
2. **Theorem 8.2 proof.**
   - The paper claims that in any valid orientation at most one vertex has all its edges outgoing, so the problem
     equals the "oriented tree problem". This fails in general trees: only relevant nodes are constrained, and nodes
     of other degrees can have several incoming edges, so several sources can exist.
   - What is true and used: on a path all of whose nodes are relevant, edge directions are monotone (`dirR_mono`).
   - We run the paper's 4-node mirror argument directly on the caterpillar: path nodes are relevant, with leaves
     attached. Our version uses 3 nodes `w_c, w_k, w_e` and two mirrored instances.
   - We do not formalize the intermediate "almost oriented path" problem as a separate problem.
3. **Theorem 8.1 upper bound proof.**
   - The paper argues only for `d`-regular subdivided trees, via a 2-colouring of the underlying tree. General
     bipartite trees (black nodes of degree `≠ 2`) are not covered.
   - We prove that every tree has a solution (`va_exists`). Root the tree at a node of degree `≤ 1`. An edge
     `{u, b}` (`u` white) is in `X` iff `⌊dist(r,u)/2⌋` is even.
4. **Theorem 8.1 lower bound proof.**
   - The paper reduces 2-colouring of a path ("well known to need `Ω(n)`"), simulated on a caterpillar.
   - We prove it directly. Labels alternate along the spine of relevant nodes (`va_alternate`). Mirroring a spine
     segment with an odd number of steps changes the parity of the spine distance between two far nodes whose
     radius-`T` views are unchanged.
5. **Lemma 10.4 proof**, case `1010`: the paper writes "if `Π = (111⁺, 0∗⁺0)` then `Π ∈ III.b`". This misses
   `B = 0⁺`, which is type II.b; the hypothesis excludes it. Case `0101`: the equivalence needed is the colour swap
   (`Π₀₁`); the complement maps `0101` to itself (the paper does not say which equivalence it means).
6. **Lemma 10.8 proof** (2): "consisting of `δ` labels" should be `d` labels (typo).
   The statement of part (2) in the same proof also writes `Z₁ … Z_δ` for the white configurations (should be
   `Z₁ … Z_d`).
7. **Lemma 10.9 proof**, items (1)–(2): the colours are swapped. (1) should say "a *white* configuration for `Π₁`"
   (the proof itself then uses the white constraint of `Π₁`), and (2) should read "configurations `Z₁ … Z_δ` …
   a *black* configuration for `Π₁`". Typos; the proof reasons with the correct versions, and so do we
   (`lemma_10_9_white` uses `allChoices (W1 d s)`, `lemma_10_9_black` uses `exChoice (B1 δ)`).

## Statements: modelling choices and changes

- **Problems.** `Problem` carries the constraints `2 ≤ d`, `2 ≤ δ`, `W ⊆ [0,d]`, `B ⊆ [0,δ]` (§3.1).
- **Solutions.** A solution is an edge labelling `x : V → V → Bool`, required to be symmetric on edges. This is the
  same as a set `X ⊆ E`.
- **Instances.** Finite trees with a proper 2-colouring, the colouring being a local input (§3.6).
- **LOCAL model.**
  - Nodes are the elements of a finite type `V`, the identifiers; `n = |V|` is known.
  - An algorithm is a function `A G f u w` (label written by `u` on edge `uw`). It is `T`-round iff `T`-local in the
    sense of CSLib's `IsLocal` (radius-`T` view).
  - Port numbers are not modelled. For lower bounds this is without loss of generality: fix ID-induced ports.
  - Identifiers are exactly the `n` nodes, not a `poly(n)` range. This is a restriction of the instances, so the
    lower bounds are stronger. The upper bound only needs the whole tree, which an `n`-round algorithm sees.
  - The paper's model (§5) is message passing; we use the equivalent view-based formulation that the paper also
    mentions ("two equivalent perspectives").
  - The radius-`T` view of `IsLocal` contains the edges at nodes of distance `< T` and the inputs (colours) up to
    distance `T`, but not the degrees of the nodes at distance exactly `T`, which a `T`-round message-passing
    algorithm learns. So a `T`-round LOCAL algorithm is a `(T + 1)`-local function here, and our lower bounds hold
    for message-passing algorithms with `T + 1` in place of `T`. This only shifts the explicit constants
    (the paper itself works "up to some additive constants in the number of communication rounds").
- **Complexity as concrete bounds.** "Complexity `Θ(n)`" is stated with explicit constants, for every `n`:
  - `WhiteSolvable Π V |V|` (upper bound);
  - `WhiteSolvable Π V T → |V| < (3T+6)d` (V.a), `< (3T+9)δ` (V.b), `< (6T+10)(d+δ−2)` (VI.a/VI.b).

  For fixed degrees this is `T = Ω(n)`. The constants are ours; the paper gives none.
- **Observation 3.2** is formalized as:
  - exact solution correspondences (complement; colour swap);
  - complexity transfers: complement with the same `T`, colour swap with `T + 1` (via Observations 5.1–5.2).

  The paper's "same complexity up to ±1 rounds" is the combination.
- **Families.** VI.b is defined as the colour swap of VI.a, and V.b as the colour swap of V.a.
  - We use VI.a → VI.b by complement (`IsVIa.compl`; also an equivalence, with no extra round) where the paper uses
    the colour swap.
- **Lemma 10.4** assumes only "not of type II, III, IV" (type I is not needed). "Equivalent to" is made explicit:
  the relaxation `Π'` is FD or BSO, or `Π'.compl` is BSO, or `Π'.swap` is FD.
- **Lemmas 10.8–10.9.**
  - Configurations are tuples `Fin k → α` whose multiset of labels is what the constraint sees.
  - "Maximal configurations" uses domination up to a permutation of ports.
  - The "(1)" parts characterize the maximal configurations exactly: every maximal configuration is one of the
    listed ones, and every listed one is maximal. The paper also claims the latter ("straightforward to check").
  - The "(2)" parts are stated for configurations built from the bold labels only, as in the paper.
  - The black-side statements hold for every `δ`.
  - Configurations with an empty entry are vacuously in the "for all choices" constraint, but are not maximal; this
    is handled automatically.
- **Not formalized.**
  - Sections 6, 7, 9, 11.
  - Lemmas 10.5 (local failure probability decay), 10.7 (FDSO easier than FD/BSO), 10.10.
  - Theorem 10.11, Corollary 10.12 (needs the external gap theorem [12]), Theorem 10.1, Theorem 4.1, and the
    completeness of Table 2.
  - The "simplification via maximality" (that keeping only maximal configurations does not change complexity) is
    taken from Brandt [8] and not formalized; Lemmas 10.8–10.9 are formalized as the combinatorial identities they
    state.
