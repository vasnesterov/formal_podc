# Differences between the formalization and the paper

Paper: S. V. Jayanti, R. E. Tarjan, *A Randomized Concurrent Algorithm for Disjoint Set Union*,
PODC 2016 (DOI 10.1145/2933057.2933108). Text used: arXiv 1612.01514 v1 (the only arXiv version),
which describes itself as "a significantly revised version of the conference paper". Section and
theorem numbers below are those of the arXiv version. We could not consult the proceedings text, so
items about Sections 4–5 are labelled with the version they concern.

## Modelling choices (no effect on the results)

1. **Shared-memory model.** CSLib's asynchronous shared-memory model
   (`Cslib/Computability/Distributed/SharedMemory/Model.lean`): deterministic processes, every
   primitive access to a base object is one atomic step, local computation is folded into the
   continuation of the preceding access, returning a response is a separate step. Any set `P` of
   processes; every process may invoke any operation (`allowed` is `True`). No crashes. The paper's
   APRAM with `Cas` is this model.
2. **Base objects.** One compare&swap object per element `a`, storing `a.parent`, initially `a`
   (CSLib `casObject E a`). The algorithms only use `read` and `cas`. Node ids are not stored in
   memory: they are a fixed function `key : E → ℕ` known to all processes (the paper's `x.id`,
   "fixed initially").
3. **Node order.** The paper chooses the total order uniformly at random. Sections 3 and 6 (the only
   parts formalized as theorems) hold for **every** fixed total order, so the results are stated for
   an arbitrary injective `key`. Injectivity is necessary: with two equal ids, concurrent `Unite`s
   could link two roots to each other.
4. **Sequential specification.** The state of the DSU object is the relation "same set" (initially
   equality); `unite x y` merges the two classes (`joinRel`), `sameSet x y` answers membership.
   `Unite` has no result in the paper; here it returns the dummy response `true`.
5. **Algorithm 1 (`Find` without compaction)** reads `u.parent` twice per iteration, once for the
   test `u ≠ u.parent` and once for `u ← u.parent`, as written. Linearization point: the last test.
6. **"Do twice" generalized.** `FindKind.split k` tries every parent update `k + 1` times;
   Algorithm 4 is `split 0`, Algorithm 5 is `split 1`. Similarly the early-termination algorithms
   (Section 6) are formalized for `k + 1` tries, `k = 1` being Algorithms 6/7 and `k = 0` the
   one-try variant mentioned in the text.
7. **The local test `u = v` of line 7** (Algorithms 2, 3) and of line 4 (Algorithms 6, 7) is folded
   into the step that produced the new value of `v` (resp. `u`), or into the invocation. The
   linearization point "`u = v*`" of `Unite` is therefore the read that found `v` to be a root, i.e.
   the paper's linearization point of the last `Find(v)`.
8. **Linearizability** is CSLib's `IsLinearization` (Herlihy–Wing linearizability in the amended
   form, see `wiki/shared-memory.md`). **Wait-freedom** is CSLib's `Impl.WaitFree`: in every
   infinite execution, a process whose operation stays pending takes only finitely many steps.

## Statements

9. **Lemma 3.1** is formalized twice. `lemma_3_1_union` is the paper's statement. The union forest
   `uf α` is computed along the execution: a step that turns a root `a` into a non-root with
   parent `b` adds the edge `a → b`. The theorem says that the union forest has the same roots as
   the parent forest, that ids increase along its edges, and that every parent is an ancestor in
   it. Every step either changes nothing, or links a root below a node with a larger id in another
   tree, or (in a `Find`) replaces a parent `v` by a proper ancestor of `v` in the union forest.
   `lemma_3_1` is the same without the union forest: the new parent lies in the same tree and has
   a larger id than the old one.
10. **Lemma 3.2** is formalized as linearizability (`linearizable`, `linearizable_with_state`) with
    the paper's linearization points, plus the extra fact that the abstract state of the
    linearization is the partition into trees of the current memory.
11. **Lemma 3.3** is formalized as wait-freedom (`waitFree`). The step bound `O(h + 1)` per
    operation (`h` = height of the union forest) is **not** formalized. The potential used gives
    only a much weaker per-operation bound, and that bound is not stated.
12. **Theorem 3.4** = `theorem_3_4` (linearizable ∧ wait-free, for all three versions of `Find`).
13. **Section 6** (Algorithms 6 and 7) has no numbered theorem; the paper presents them as
    implementations of `SameSet` / `Unite` with marked linearization points. Formalized as
    `et_linearizable` and `et_waitFree` (for `k + 1` tries).

## Findings in the paper

14. **Proof of Lemma 3.1: "u, v and w are distinct" is false (imprecision; the lemma holds).** The
    proof claims that each `Cas(u.parent, v, w)` done in a `Find` has `u`, `v`, `w` distinct. With
    splitting, `Find` may read `v ← u.parent = u` while `u` is a root. If another process then links
    `u`, the `Find` reads `w ← v.parent ≠ v` and executes `Cas(u.parent, u, w)` with `u = v`. Such a
    `Cas` necessarily fails, because `u` is no longer a root and non-roots never become roots again,
    so nothing breaks. Lean: concrete 2-process execution `cas_same_node`; the case is handled in
    `fRes_spec`. The same execution gives a loop iteration of `Find` in which `u` does not move,
    which the proof of Lemma 3.3 ("each update of u in Find replaces u by a proper ancestor")
    overlooks. It can happen only once per `Find`, so the step bound is unaffected.
15. **Proof of Lemma 3.2, `SameSet` returning false (gap in exposition; statement true).** The
    linearization point (the last read of `Find(v)`) precedes the test `u = u.parent` that decides the
    answer. The argument needs that `u` was a root at the linearization point. This holds because `u`
    was a root when `Find(u)` returned, is a root at the test, and non-roots never become roots
    again. The paper leaves this implicit. Linearizing at the test itself would be wrong, because `v`
    may have been linked into `u`'s tree in between. In Lean this is a retroactive linearization
    point (`IsLinearization.insert`, invariant field `QOK.chk`).
16. **Proof of Lemma 3.2, link case (gap in exposition; statement true).** "The smaller of u and v
    is a root just before the Cas. It follows that x and y are in different trees." This also needs
    that the larger node is not in the smaller root's tree, which holds because ids increase along
    parent pointers (Lemma 3.1). Used in `same_update_link`.
17. **Lemma 4.2: the Chernoff bound does not give the stated exponent (proof gap; arXiv version).**
    The claimed bound is `1/exp((c/2 − 1)² h² / c)`. The Chernoff bound applied in the proof gives
    `1/exp((c/2 − 1)² h / c)`, linear in `h`. The quadratic bound fails in the model the proof
    reduces to: with each of the `ch` links good with probability exactly `1/2`, which Lemma 4.1
    allows, `c = 4` and `h = 6`, the probability of fewer than 6 good links among 24 is
    `55455/2²⁴ ≈ 3.3·10⁻³ > e⁻⁹ ≈ 1.2·10⁻⁴` (`chernoff_step_fails`; the linear exponent is consistent
    with this case, `chernoff_linear_ok`). We do not know whether the statement of Lemma 4.2 is
    false for the actual union forest; only its proof is broken.
    *Consequences.* Corollaries 4.2.1–4.2.2 and Theorem 4.3 survive with the linear exponent: choose
    `c` larger (e.g. `c ≥ 10` for `1/n²` with `h = lg n + 1`). The case `d < 1` of the proof of
    Theorem 5.1 uses the quadratic form ("the expected number of middle nodes is at most
    `n/2^{h²/16}`", total charge `O(hpn/2^{h²/4}) = O(m)`). With the linear exponent and the paper's
    threshold `4h` for "low" nodes, the charge is `O(h·m·(np/m)^{1−1/(4 ln 2)})`, which is not
    `O(m)`. Raising the threshold to `c·h` with `(c/2 − 1)²/c > ln 2` (e.g. `c = 7`) restores
    `O(m)` and keeps the `O(m log(1/d))` count of low nodes, so Theorem 5.1 is very likely still
    true. Not formalized beyond the numeric witness.
18. **One-try splitting in the PODC version (acknowledged by the authors; not checked by us).** The
    arXiv version states that the conference version claimed the bound of Theorem 5.1 for one-try
    splitting and that the proof "is not correct for this algorithm". The arXiv version proves a
    weaker bound (Theorem 5.2, with `m/(np²)` in place of `m/(np)`) and leaves the original claim
    open. The probabilistic analysis is not formalized, so we neither confirm nor refute this.
19. **Typos and slips** (none affects the formalized results):
    * Algorithm 4, line 7: `Cas(u.p, v, w)` should be `Cas(u.parent, v, w)`.
    * Proof of Lemma 4.1: "the rank of a node is never less than the rank of its parent" should be
      "never more" (ranks are non-decreasing along parent pointers, `x.r ≤ x.p.r`, as stated just
      before).
    * Proof of Lemma 4.2: "there are fewer than h bad links among the ch links" should be "fewer than
      h *good* links" (a good link increases the rank, and the rank stays below `h`).
    * Proof of Theorem 5.1 (case `d < 1`): the middle-node bound is given as `n/2^{h²/16}` and the
      total charge as `O(hpn/2^{h²/4})`. The two exponents are inconsistent (see also item 17).
    * Proof of Lemma 5.3: "The Find on x can decrease one or more node depths only if x has depth 1
      before the Find and 1 after" should be "depth 2 before and 1 after". A `Find` from a node of
      depth ≤ 1 changes nothing, and the subsequent bound `2^{i−2}` via invariant (3) is for depth 2.

## Not formalized

20. Sections 4 and 5 (randomized analysis: Lemma 4.1, which relies on Goel et al. (SODA 2014),
    Corollaries 4.1.1–4.2.2, Theorems 4.3, 5.1, 5.2, 5.4, Lemma 5.3). These depend on the
    independence assumption (∗) and on properties (i)–(vi) of Goel et al., which the paper only
    cites. Only the numeric witness of item 17 is in Lean.
21. The `MakeSet` remark (lock-freedom with an unbounded universe) and the remarks of Section 7.
22. The `O(h + 1)` step bound of Lemma 3.3 (see item 11).
