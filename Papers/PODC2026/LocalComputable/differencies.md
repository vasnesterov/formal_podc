# Differences between the formalization and the paper

Paper: Cruciani, Das, Equi, Lievonen, Luong-Le, Modanese, Suomela, *Is a LOCAL algorithm
computable?* (PODC 2026 brief announcement; full version arXiv 2602.21022 v2, whose numbering we
follow).

## Errors and gaps in the paper

1. **Definition 5.1 / Theorems 5.3, 5.4: "maximally `T`-safe" is not a property of the view.
   Under-specified definition, proof gap; the statements are true.**
   `t` is maximally safe for `v` if `t` is safe and `t+1` is not, where safety of `t+1` is defined
   with the radius-`(t+1)` neighbourhoods. So maximal safety of `t` depends on `N^{t+1}(v)`. A node
   that has gathered only `N^t(v)` cannot tell whether to stop. The paper nevertheless "extends these
   notions to the rooted neighbourhoods themselves". Both of its algorithms (phase two of
   Theorem 5.3, and the sandbox and `B` of Theorem 5.4) say "grow the view until it is maximally
   `T`-safe", and the paper claims this stays within `T(n)` rounds.
   Concrete counterexample, in the model of Section 3 with `T(n) = ⌊(n-1)/2⌋` (computable,
   non-decreasing): take node `0` of the triangle `C₃` and node `0` of the 5-cycle `C₅`, with
   matching identifiers and ports. Their radius-1 views coincide. In `C₃`, radius `1 = T(3)` is
   maximally safe: every network containing the radius-1 view has ≥ 3 nodes, while `C₃` itself
   shows that radius 2 is unsafe. In `C₅` radius 2 is still safe, because every network containing
   the radius-2 view has ≥ 5 nodes. So no radius `≤ 1` is maximally safe there. Hence no ball-growing
   algorithm stops exactly at the maximally safe radius. In `C₃` a node needs radius `2 > T(3)` to
   find out that radius 1 was maximally safe. Read literally, the algorithms of Theorems 5.3/5.4
   exceed the time bound by one round: any algorithm that never stops before a maximally safe radius
   does not stop within `T(3) = 1` rounds in `C₃`.
   (`maxSafe_not_view_determined`, `no_alg_stops_at_maxSafe`, `maxSafe_rule_exceeds`)
   *The view-level reading.* The paper's sentence "if `t` is (maximally) `T`-safe for `v`, then we
   say that `N^t(v)` is also (maximally) `T`-safe" can be read existentially: a view `X` of radius
   `t` is maximally safe if `t` is maximally safe for *some* node with view `X`. This is a
   property of `X`. It holds iff `X` is safe and `T`-critical (definition below). One direction:
   the unsafety of `t+1` gives a network `G''` with `T(|G''|) ≤ t` containing `X`. Conversely, a
   critical witness `G''` makes `t+1` unsafe for its own node. Moreover, the first radius at which a
   node's view is critical is always safe, since a safety violation at `t` would make the
   radius-`(t−1)` view critical. So under this reading, "grow until maximally safe" stops exactly
   at the first critical radius, within `T(n)`. This is the formalization's `B`. The C₃ node and
   the C₅ node both stop at radius 1. The paper's arguments, however, do not establish what this
   reading needs. Lemma 5.2's procedure checks safety only (item 5). Lemma 5.5 does not show that
   `A_N` stops inside the view (item 2). So in either reading this is a proof gap with true
   statements, not a false claim. `maxSafe_rule_exceeds` refutes only the per-node reading; under the view-level reading a view is maximally safe iff it is safe and critical, and the first such radius is the first critical radius (`maxSafeView_iff`, `first_critical_maxSafeView`).
   *Fix.* We call a radius-`t` view `x` **`T`-critical** if `x` occurs in some network `G'` with
   `T(|V(G')|) ≤ t` (`Model.Critical`). This depends only on `x`. Every node has a critical radius
   `≤ T(n)` (its own network is a witness). Any algorithm of locality `T` has stopped at a node
   whose view is critical, since that node is indistinguishable from the witness node
   (`out_of_critical`). Maximal safety implies criticality (`MaxSafe.critical`). With this notion,
   Lemma 5.2 and Theorem 5.4 go through.

2. **Lemma 5.5 (inside Theorem 5.4): wrong witness. Proof gap, statement true.**
   The proof sets `G_i = X_i`. But a rooted neighbourhood is not a network: the degree labels of
   boundary nodes count edges that are not in `X_i`. It then argues "`A_N` must stop after
   `T(N_i)` rounds". The sandbox, however, needs `A_N` to stop within the radius `r_i` of `X_i`, and
   we only know `r_i ≤ T(N_i)`. Our fix: take `N_i` to be the size of a criticality witness `G'`
   (`T(|V(G')|) ≤ r_i`). For `N ≥ N_i`, `A_N` is correct on `G'`, so it stops by `r_i` there, and
   hence at every node with view `X_i`. (`out_of_critical`, used in `exists_boundFree`)

3. **Theorem 5.3's proof: the graph class of "safe" is not specified. Proof gap, statement true.**
   The algorithm collects the maximally safe neighbourhoods of the networks with
   `n ≤ N ≤ f(n)`. The final contradiction then uses "some concrete network `G' ∈ 𝒢` containing `N`
   with `T(|G'|)` equal to its radius". If safety is taken over all graphs, as in Definition 5.1, this
   witness need not satisfy the promise for the same `N`. Then `A` (which knows `N`) is not required
   to stop on it, and the contradiction fails. With safety taken relative to the promise class for
   `N`, it works, up to item 1. Our proof does not use safe neighbourhoods at all. For fixed `N`
   only finitely many (view, radius) pairs can be consulted before the deadline in legal networks.
   A table on these pairs is a finite object, and whether it solves the problem on all legal
   networks is decidable. The restriction of the uncomputable algorithm is a good table, so an
   unbounded search finds one. (`exists_computable_of_promise`)

4. **Definition 3.5: wrong justification of "`T` is non-decreasing"; claim true.** The paper argues
   that "the set of graphs with `n₁` nodes is contained in the class of graphs with `n₂` nodes".
   This is false as stated. The claim holds in the model of Section 3 for a different reason: add
   isolated nodes with fresh identifiers. This is possible because identifiers range over
   `[1, n^c]` with `c ≥ 1` and disconnected graphs are allowed. The views of the old nodes do not
   change. (`stops_of_le`)

5. **Minor imprecisions** (typo / under-specified level).
   * Definition 5.1 says "maximal with this property (i.e., `t` is safe but `t + 1` is not)". These
     two readings agree only if safety is downward closed in `t`, and the paper does not show
     that. (Our fix avoids the issue: `B` stops at the *first* critical radius.)
   * Lemma 5.2's case 2 ("`t = T(N') = C` for every `N' ≥ N₀`") should read "`T` is bounded with
     supremum `C ≤ t`". Step 1 should accept whenever `t ≥ C`. The procedure is non-uniform: it
     hard-codes `C`, as the paper notes. Step 3 ("reject if `X` is isomorphic to the radius-`t`
     neighborhood of `v` in `G` and `t < T(n)`") has the inequality reversed; the text before it
     requires `T(n) < t`. Even then the procedure tests only *safety* of `t`, never that `t + 1`
     is unsafe. So it does not decide maximal safety in either reading of item 1.
   * Lemma 4.17's proof: "do not see farther than the first `k − 1` layers" must also avoid the
     constantly many special layers near the bottom (inputs differ there between `G_k` and
     `G_{k'}`), i.e. the bound is `k − O(1)`. "The value computed by `T` will equal `k₀`" is not
     true in general: `T` finds the least `k` with the property, while `k₀` is the least threshold
     beyond which it holds for all `k`. This is immaterial; any such `k` works, as in our
     `exists_far_of_computable`. The input conventions of `U`, `D` and `x_T` are informal.
     Kleene's recursion theorem settles them.

## Modelling choices and generalizations

* **Abstract model.** Section 5 is formalized for an abstract `Model Net View`: networks with
  sizes, and views of every node and radius such that the radius-`t` view determines the smaller
  ones (`Model.restrict`). This is the only property of neighbourhoods used. The concrete
  networks of Section 3 are an instance (`concreteModel`). They are simple graphs of maximum
  degree `Δ`, with port numbering given by the order of the neighbour lists, unique identifiers in
  `[1, n^c]`, inputs `< k`, and nodes `0, …, n−1`.
* **Views.** In the concrete model, the view of radius `t` is the full-information view: own
  identifier, input and degree, plus the neighbours' radius-`(t−1)` views in port order. With unique
  identifiers this carries the information of `N^t(v)` of Definition 3.1 (nodes at distance
  `≤ t` with degrees, edges with an endpoint at distance `≤ t−1`, ports, identifiers, inputs)
  **except one item**: the port number, at a distance-`t` node `u`, of its edge to a
  distance-`(t−1)` node. `u` occurs only through its radius-0 view (identifier, input, degree). For
  example, at radius 1 node `v` does not learn on which port of a neighbour `u` the edge `uv`
  lies, whereas `N^1(v)` restricted as a network contains `p_u`. So the concrete model is a
  slightly weaker-view variant: messages are not tagged with the sender's port. The `C₃`/`C₅`
  counterexample is unaffected: the ports match there too. We did not formalize the relation
  between the two notions. All abstract results hold for either notion, since
  both satisfy the restriction property. Edge inputs ("`Σ_in` may refer to port numbers") are not
  modelled. They can be folded into node inputs.
* **Problems.** A problem is an arbitrary predicate on node labellings of each network. LCLs are a
  special case, and half-edge outputs can be folded into node outputs. Theorem 5.4 needs only a
  finite output alphabet (`[Finite Out]`). Theorem 5.3 needs only a computable validity check.
  This matches the paper's remark "for LCLs and beyond".
* **Algorithms** are maps `View → ℕ → Option Out` (`none` = `⊥`). Outputs are taken at the first
  radius with a non-`⊥` value. The "sensible algorithm" convention of Definition 3.5 is not
  needed. *Computable-LOCAL* means `Computable` (Mathlib, via `Primcodable` encodings) as a function
  of `(N, view, radius)`, or of `(view, radius)` without `N`.
* **Knowledge of `n`.** This is a promise `Adm N G` on the common input `N`: `UpperBound`
  (`n ≤ N`) or `Sandwich f` (`n ≤ N ≤ f(n)`, `f : ℕ → ℕ∞`). Computability of `f` is stated through
  `enatToOption` (`∞ ↦ none`).
* **Generalizations.**
  * Theorem 5.3 needs neither `T` nor `f` to be non-decreasing, and it works for any promise
    whose legal networks for each `N` form a computable finite list.
  * Theorem 5.4 needs no computability or monotonicity of `T`, and `P` need not be locally
    checkable. Its stabilization step uses a non-principal ultrafilter on `N`, equivalent to the
    paper's nested infinite subsequences. We also prove that `B` agrees with some `A_N` on every
    network and stops exactly at the first critical radius.
* **Computability hypotheses of the abstract theorems.** We assume computable size, view, `T` and
  checker, and computable lists of the networks with `≤ N` nodes. The paper states these in words
  ("bounded-degree recursively enumerable graph family", "Turing machines that decide validity").
  For the concrete model they are discharged in `ConcreteComputable.lean`; there views are coded
  as natural numbers by an injective code.

## Not formalized

* **Section 4's LCL `Π`.** The trees, rows, growing grids, Turing machine layer and consensus layer
  (Definitions 4.2, 4.6, 4.10, Theorem 4.3, Lemmas 4.4–4.15, Corollary 4.14) are not formalized.
  Neither is the uncomputable `O(log n)` algorithm (Lemma 4.16). Hence Theorem 4.1, and the
  strictness I < II of Table 1 for LCLs, are not verified.
* **The diagonalization of Lemma 4.17 is formalized abstractly.** We use a "separation family"
  `G_K(x)` with two properties. (a) Validity forces the result bit of a halting program for all
  large `K`. (b) The node holding `x` has the same radius-`r` view in `G_K(x)` and `G_{K'}(x)` once
  `K, K' ≥ depth x r`. With `|G_K(x)| ≤ C(K+1)²` and `depth x r ≤ r + D(x)`, no computable
  algorithm has locality `o(√n)` (`not_littleO_sqrt`). Programs are Mathlib's `Nat.Partrec.Code`
  run on input `0`. Lemma 4.18 is `diagonalizer`, via Kleene's recursion theorem. Whether the
  paper's `Π` really forms such a family (local checkability of the grid and of the Turing machine
  trace, the `Θ(k²)` size, the consensus constraints) is not verified. Non-vacuity: a toy family on
  promised paths (`SeparationToy.lean`) satisfies the hypotheses. There, uncomputable-LOCAL needs
  locality 0 and computable-LOCAL needs `n − 1`. This is not the paper's `Π`.
* **The direct computable `O(log n)` algorithm with a bound `N`** (end of §2.1) is not formalized.
  It is subsumed by Theorem 5.3 once Lemma 4.16 is given.
