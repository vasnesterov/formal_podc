# Is a LOCAL Algorithm Computable? — PODC 2026

Antonio Cruciani, Avinandan Das, Massimo Equi, Henrik Lievonen, Diep Luong-Le, Augusto Modanese,
Jukka Suomela. *Brief Announcement: Is a LOCAL Algorithm Computable?* PODC 2026. DOI
[10.1145/3796701.3815908](https://doi.org/10.1145/3796701.3815908). Formalized version: the full
version, arXiv [2602.21022](https://arxiv.org/abs/2602.21022) v2; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues — for Section 5 only.** **The headline result, the separation
Theorem 4.1 (an LCL `Π` with complexity `O(log n)` in uncomputable-LOCAL but `Ω(√n)` in
computable-LOCAL, i.e. classes I < II of Table 1), is *not* verified.** The LCL `Π` of Section 4 is
not formalized, only the diagonalization core of Lemma 4.17 (on abstract hypotheses) and Lemma 4.18.
The verdict covers the equivalence results of Section 5. They hold, in slightly greater generality,
and are proved:
* with a bound `n ≤ N` (or `n ≤ N ≤ f(n)`), uncomputable and computable LOCAL coincide (Theorem 5.3);
* in uncomputable LOCAL the bound does not help (Theorem 5.4 / Corollary 5.6);
* critical views are decidable (Lemma 5.2).

The paper's central tool, "maximally `T`-safe neighbourhoods", is under-specified. Defined per
node, it depends on the next, unseen radius, and an algorithm that stops only at such radii exceeds
the time bound by one round. Lifted to views, it is not what the paper's proofs of Lemma 5.2 and
Lemma 5.5 handle. We give a corrected notion ("critical" views) with which the proofs go through.

## Mistakes in the paper

* **"Maximally `T`-safe" depends on the radius-`(t+1)` view (Definition 5.1, used in Lemma 5.2 and
  Theorems 5.3–5.4). Under-specified definition and proof gap; the statements are true.**
  `t` is maximally safe for `v` if `t` is safe and `t+1` is not, and safety of `t+1` is defined with
  radius-`(t+1)` neighbourhoods. A node that has seen only `N^t(v)` cannot evaluate this. Yet both
  algorithms "grow the view until it is maximally `T`-safe" and are claimed to run within `T(n)`
  rounds.
  Counterexample with `T(n) = ⌊(n-1)/2⌋`: a node of the triangle and a node of the 5-cycle have the
  same radius-1 view (same identifiers and ports). Radius `1 = T(3)` is maximally safe in `C₃`,
  since radius 2 is unsafe because of `C₃` itself. In `C₅` it is not maximally safe: every network
  containing the radius-2 view has ≥ 5 nodes, so radius 2 is still safe. So no ball-growing rule
  stops exactly at maximally safe radii. Any algorithm that never stops before a maximally safe
  radius fails to stop within `T(3) = 1` rounds in `C₃`
  (`maxSafe_not_view_determined`, `no_alg_stops_at_maxSafe`, `maxSafe_rule_exceeds`); the view-level reading is sound (`maxSafeView_iff`, `first_critical_maxSafeView`).
  The paper's sentence "if `t` is maximally safe for `v`, then `N^t(v)` is maximally safe" can
  also be read as a property of views: maximally safe for *some* node with this view. Under that
  reading the radius-1 view above is maximally safe, also in `C₅`, and the algorithms stay within
  `T(n)`. A view is then maximally safe iff it is safe and critical (below). The first such radius
  of a node is exactly its first critical radius, which is where our `B` stops. But then the
  paper's arguments do not establish what is needed. Lemma 5.2's procedure tests only safety of
  `t`, never criticality. Lemma 5.5 does not show that `A_N` stops within the view (next item).
  So in either reading this is a proof gap, not a false claim.
  *Fix.* Call a radius-`t` view **critical** if it occurs in some network `G'` with
  `T(|V(G')|) ≤ t`. Every node meets a critical radius by `T(n)`, and any algorithm of locality
  `T` has already stopped there (`Model.Critical`, `out_of_critical`). Maximal safety implies
  criticality (`MaxSafe.critical`).
* **Lemma 5.5 (inside Theorem 5.4) uses the wrong witness. Proof gap; statement true.** It takes
  the neighbourhood `X_i` itself as a graph. That is not a network: boundary degree labels count
  unseen edges. It then only gets that `A_N` stops within `T(N_i)` rounds, while the sandbox needs
  `A_N` to stop within the radius of `X_i`. Taking `N_i` to be the size of a criticality witness
  repairs the argument (`exists_boundFree`).
* **Theorem 5.3's proof leaves the class of "safe" unspecified. Proof gap; statement true.** If
  safety ranges over all graphs, the final contradiction uses a network that need not satisfy the
  promise `n ≤ N ≤ f(n)` for the same `N`, and the uncomputable algorithm owes nothing there. We
  prove the theorem differently: for fixed `N`, search over the finitely many finite tables
  "(view, radius) ↦ output" for one that solves the problem on all legal networks. The
  uncomputable algorithm's table shows that the search terminates
  (`exists_computable_of_promise`).
* **Definition 3.5's reason why the locality `T` is non-decreasing is wrong; the claim is true.**
  The paper says "the set of graphs with `n₁` nodes is contained in the class of graphs with
  `n₂` nodes", which is false. The correct reason is to pad with isolated nodes that have fresh
  identifiers (identifiers lie in `[1, n^c]`, `c ≥ 1`); this does not change the views
  (`stops_of_le`).
* **Minor.** "Maximal" vs. "safe with `t+1` unsafe" (Definition 5.1) coincide only if safety is
  downward closed, which is not shown. Lemma 5.2's case "`t = T(N') = C`" should read "`T` bounded
  with supremum `C ≤ t`". Its step 3 ("reject if ... `t < T(n)`") has the inequality reversed: it
  should be `T(n) < t`. In Lemma 4.17, "do not see farther than the first `k−1` layers" must
  also avoid the constantly many special layers near the bottom. "The value computed by `T` will
  equal `k₀`" is not true in general, but this is immaterial.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Deterministic synchronous LOCAL, ball-growing formalism (Definition 3.5).** An algorithm is
  `A : View → ℕ → Option Out` (`none` = `⊥`). A node outputs `A (view, t)` at the least radius
  `t` with a non-`⊥` value. Locality `T` means every node of every `n`-node network stops by
  radius `T(n)`.
* **Abstract networks** (`Model Net View`). Networks have sizes, and views of every node and
  radius. The radius-`t` view determines all smaller ones; this is the only property used.
* **Concrete instance** (`concreteModel Δ c k`): the networks of Section 3. Simple graphs of
  maximum degree `Δ`, port numbering = neighbour order, unique identifiers in `[1, n^c]`, inputs
  `< k`, full-information views (own identifier, input, degree, and the neighbours' radius-`(t−1)`
  views in port order). With unique identifiers these carry the information of `N^t(v)`
  (Definition 3.1) *except* the port numbers, at the distance-`t` nodes, of their edges towards
  distance-`(t−1)` nodes. So the concrete model sees slightly less than Definition 3.1 (as if
  messages were not tagged with the sender's port). The abstract theorems apply to either kind of
  view. The `C₃`/`C₅` counterexample also holds for Definition 3.1 views: the ports match.
* **Knowledge of `n`**: a common input `N` with promise `n ≤ N` (`UpperBound`) or `n ≤ N ≤ f(n)`
  (`Sandwich f`). An algorithm is then a family `A N`.
* **Problems** are arbitrary validity predicates on output labellings (LCLs and beyond).
  Theorem 5.4 uses a finite output alphabet. Theorem 5.3 uses a computable validity check.
* **Computability** is Mathlib's `Computable` on `Primcodable` encodings of `(N, view, radius)`.
  Uncomputable-LOCAL algorithms are arbitrary functions.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 5.3 (computable = uncomputable under `n ≤ N ≤ f(n)`; any computable `T`, `f`) | `Model.sandwich_computable` | `ComputableEquiv.lean` |
| Thm 5.3, general promise with computable finite lists of legal networks | `Model.exists_computable_of_promise` | `ComputableEquiv.lean` |
| Thm 5.4 (bound-free `B`; agrees with some `A_N`; stops at first critical radius) | `Model.exists_boundFree` | `Basic.lean` |
| Cor 5.6 | `Model.solvable_upperBound_iff` | `Basic.lean` |
| Lemma 5.2 (for critical views; `T` computable, non-decreasing) | `Model.critical_decidable` | `Decide.lean` |
| Table 1, class II (three models equivalent) / class III / I ≤ II / II ≤ III | `Model.classII_iff` / `Model.classIII_iff` / `classI_le_classII` / `classII_le_classIII` | `Collapse.lean` |
| Table 1 class II / class III / Lemma 5.2 **for the concrete model of Section 3** (all computability hypotheses discharged) | `concrete_classII`, `concrete_uncomputable_iff_computable`, `concrete_classIII`, `concrete_critical_decidable'` | `ConcreteComputable.lean` |
| Def 5.1 is not view-determined (`C₃` vs `C₅`); the literal rule exceeds `T` | `maxSafe_not_view_determined`, `no_alg_stops_at_maxSafe`, `maxSafe_rule_exceeds`; view-level reading is fine: `maxSafeView_iff`, `first_critical_maxSafeView` | `MaxSafe.lean` |
| Def 3.5: locality non-decreasing (padding) | `stops_of_le` | `Padding.lean` |
| Lemma 4.18 (diagonalizer) | `diagonalizer` | `Separation.lean` |
| Lemma 4.17, abstract core (separation family ⇒ not `o(√n)`) | `Model.exists_far_of_computable`, `Model.not_littleO_sqrt` | `Separation.lean` |

**Not formalized.** The LCL `Π` of Section 4 (trees, rows, growing grids, Turing machine and
consensus layers; Lemmas 4.4–4.16, Corollary 4.14). Hence Theorem 4.1 and the strictness
I < II are not verified. Only the diagonalization of Lemma 4.17 is formalized, for an abstract
family `G_K(x)` whose two properties (validity forces the halting result; the node holding `x` does
not see the bottom) are hypotheses. The equivalence of full-information views and Definition 3.1
balls is not formalized.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity checks:
* every node has a critical radius (`critical_self`);
* the concrete model satisfies the abstract hypotheses: restriction in `Concrete.lean`;
  computability in `ConcreteComputable.lean`: primitive recursive well-formedness, enumeration of
  networks with `≤ N` nodes, computable injectively coded views;
* a toy separation family on promised paths (`SeparationToy.lean`): uncomputable locality 0
  (`toy_uncomputable_solves`) versus computable locality `≥ n − 1` (`toy_computable_lower`).

Computable list combinators (`Computable.list_foldl/map/all/any/findSome?/filterMap/flatMap/filter`,
`Computable.nat_find`) and `Primrec.list_all/any`, `Primrec.nat_pow` are shared code in
CSLib `Cslib/Computability/Partrec/List.lean` and `Cslib/Computability/Primrec/List.lean`.
The abstract ball-growing model (`Basic.lean`) is a CSLib candidate.
