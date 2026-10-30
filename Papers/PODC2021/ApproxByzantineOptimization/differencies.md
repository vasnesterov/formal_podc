# Differences between the formalization and the paper

Paper: S. Liu, N. Gupta, N. H. Vaidya, *Approximate Byzantine Fault-Tolerance in Distributed
Optimization*, PODC 2021, DOI 10.1145/3465084.3467902. We formalize the full version, arXiv:2101.09337v5,
Section 3 (Lemma 1, Theorems 1, 2).

## Issues in the paper

1. **Theorem 1 is under-specified.** *Classification: under-specified statement; literal reading
   false, excused by R4 (borderline, see the verdict section).* Definition 2 defines resilience of an
   algorithm for the agents' cost functions at hand. Theorem 1 says resilience exists "only if the
   agents' cost functions satisfy `(2f, ε)`-redundancy". It does not fix the class of inputs on which
   the algorithm must be correct.
   - *(a) Per profile (literal): false* (`theorem_1_false_per_profile`). Take `n = 3`, `f = 1`,
     `E = ℝ`, `Q = ((x − a)², (x + a)², 2a|x|)` with `a = ε + 1`. All three costs are convex. Every
     non-empty aggregate has a unique minimum point, so Assumption 1 holds. All pairs have
     `arg min = {0}`, so the constant algorithm `0` is `(1, 0)`-resilient. Yet
     `dist({0}, arg min Q₀ = {a}) = a > ε`. In general, per profile, resilience exists iff the
     `(n − f)`-`arg min`s have a common `ε`-close point (`exists_isResilient_iff`).
   - *(b) All profiles satisfying Assumption 1: true but vacuous* (`theorem_1_uniform`). The proof
     needs this reading, because the faulty agents' fabricated functions become the true costs of
     scenario (ii). But for `1 ≤ f < n` no algorithm is resilient on this class, even on quadratic
     costs (`no_uniform_resilience`). So the redundancy of the given profile is irrelevant. The proof
     is valid in this reading. Its "it is always possible to pick such functions" holds; it is not
     needed in our proof, which uses quadratic costs directly.
   - *(c) Class of `(2f, ε')`-redundant profiles: true, proved by us; the paper's proof does not
     establish it* (`theorem_1_corrected`, `theorem_1_class`). For `1 ≤ f`, `2f < n` and `ε < ε'`,
     every deterministic algorithm fails `(f, ε)`-resilience on some profile satisfying Assumption 1
     and `(2f, ε')`-redundancy. The paper's second profile (faulty functions with the reflected
     minimum `x_{B∪Ŝ}`) need not be `(2f, ε')`-redundant. Our proof uses a single profile `gridProfile`
     instead. It is supported on `{−v, 0, v}` with `‖v‖ = ε'` and has value `1` elsewhere, so the
     costs are discontinuous. Section 3 allows arbitrary functions ("need not even be
     differentiable", non-convex). Whether continuous or convex costs give the same bound is not
     investigated.
   We take (c) as the corrected Theorem 1. With Theorem 2 it gives `resilience_window`.
2. **The algorithm in the proof of Theorem 2 is undefined in a case.** *Proof gap (missing case),
   statement true.* Step 2 computes `x_T ∈ arg min ∑_{i∈T} Qᵢ` for every set `T` of `n − f` received
   functions, and `dist(x_T, arg min ∑_{T̂})`. If `T` contains faulty agents, these `arg min` sets can
   be empty, and Assumption 1 only covers non-faulty sets. `dist(x, ∅)` is also undefined in (3).
   Repair (`candidate`, `score`): pick an arbitrary point if the `arg min` is empty, and use the
   extended distance (`dist(x, ∅) = ∞`). The proof uses `x_T ∈ X_T` only for `T = G` non-faulty, and
   the minimum in (12) exists over a finite set.
3. **Lemma 1 fails for `f ≥ n`.** *False only in a degenerate case (R2).* For `f = n`, Definition 2
   only constrains `S = ∅`, whose `arg min` is `ℝ^d`, so every algorithm is `(n, 0)`-resilient
   (`lemma_1_false_of_le`, via `isResilient_of_le`). For `f > n` there is no `S` at all. For
   `n/2 ≤ f < n`, `lemma_1` proves the lemma in the reading of its proof: no algorithm is resilient
   for all profiles satisfying Assumption 1. Read per profile, Lemma 1 is false as well (identical
   costs make the constant algorithm resilient), like Theorem 1 (a). Its proof treats only `n = 2`
   and says "extends easily for `n > 2` and `f > n/2`". The case `f = n/2`, `n > 2` is not mentioned
   but is equally easy. Our proof uses two `(n − f)`-sets with far-apart quadratic minima and works
   for every `1 ≤ f < n`.
4. **Closedness in Assumption 1 is not needed for Theorem 2.** *Remark, no error.* The paper picks
   nearest points `z ∈ X_Ĝ` and `x* ∈ X_G` using closedness. We use
   `infEDist x X_G ≤ infEDist x X_Ĝ + hausdorffEDist X_Ĝ X_G` (`theorem_2_strong`). Likewise, only
   redundancy and non-emptiness for sets of non-faulty agents are used. Definition 3 asks for
   redundancy for all subsets of `{1,…,n}`. `theorem_2` is the paper's statement, and
   `theorem_2_of_nonempty` drops closedness.
5. **Minor.**
   - Theorem 2's proof assumes `f > 0` "to avoid the trivial case"; `theorem_2` covers `f = 0` too.
     It needs `2f ≤ n`, which is implied by the standing assumption `f < n/2`.
   - Theorem 1's proof writes `n − 2f ≤ |Ŝ| < n − f`, whereas Definition 3 uses `|Ŝ| = n − 2f`. This is
     harmless.
   - The claim "2f-redundancy is equivalent to `(2f, 0)`-redundancy" is not formalized. It needs
     closed `arg min`s, since Hausdorff distance `0` only gives equal closures. It also needs an
     averaging argument to pass from `|Ŝ| = n − 2f` to `|Ŝ| ≥ n − 2f`.

## Verdict

Worst label ⚠️, from items 1 and 3.
- Item 3 is a degenerate case (R2).
- Item 1 is borderline between ⚠️ and ❌/🚨. The literal per-profile statement is false, and Theorem 1
  is a co-headline ("necessary and sufficient conditions"). We apply R4: a competent reader takes
  "necessary" to mean "for an algorithm that must work on a class of inputs". Under the natural class
  (the `(2f, ε')`-redundant profiles) the statement is true, and the paper's message ("the redundancy
  level controls the achievable resilience") is not misleading. The repair needed for (c) is at the
  proof level. This agrees with the treatment of the same issue in
  `Papers/PODC2020/RedundantOptimization`.
- Item 2 is a proof-level gap (🛠️).

## Modelling choices

- **One-shot full-information model.** This is the paper's "server has full knowledge of all the
  agents' cost functions". A deterministic algorithm is a map from received vectors to points.
  Theorem 2's algorithm lives in this model. The impossibility results only use executions in which
  faulty agents send their true costs. Any deterministic protocol in which a Byzantine agent can
  imitate an honest one therefore inherits them; the reduction is stated in words only (see
  `Protocol.resilient_toAlg` in `PODC2020/RedundantOptimization` for a formal version).
- **Profiles.** A profile fixes a cost for each of the `n` agents. The faulty agents' entries are
  irrelevant for resilience, since their reports are arbitrary. `IsResilient` quantifies over all
  faulty sets `|B| ≤ f`, so "up to `f`" faults, including fewer than `f`, is covered.
- **Assumption 1 for all agents.** Since the faulty set is not fixed in advance, `Assumption1 Q`
  is stated for every non-empty set of agents of the profile (the paper: "every non-empty set of
  non-faulty agents"). This makes the impossibility results stronger. For Theorem 2,
  `theorem_2_strong` assumes non-emptiness only for the non-faulty sets of the execution at hand.
- **Distances.** `Metric.infEDist` and `Metric.hausdorffEDist` are valued in `ℝ≥0∞`. They agree with
  (3) and (4) on non-empty sets; the distance to `∅` is `∞`. `ε : ℝ≥0`.
- **Spaces.** The paper uses `ℝ^d`. Theorem 2 is proved in any pseudo-emetric space with a point. Lemma
  1 is proved in real inner product spaces `≠ 0` and Theorem 1 (c) in real normed spaces `≠ 0`; an
  `example` in `Main.lean` instantiates `EuclideanSpace ℝ (Fin d)`, `d ≥ 1`. Theorem 1 (a) is on
  `ℝ`, i.e. `d = 1`, which suffices to refute a statement claimed for all `d`.
- **Cardinalities** are additive (`|S| + f = n`, `|Ŝ| + 2f = n`). So for `2f > n` Definition 3 has
  no pairs, as in the paper's integer reading.
- **Algorithm of Theorem 2.** Ties in Step 3 are broken by `Classical.choose`. The paper allows any
  minimizer, and the proof works for each.
