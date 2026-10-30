# Delay-Optimal Transaction Order Fairness — PODC 2026

Zhuo Cai, Amir Goharshady. *Brief Announcement: Delay-Optimal Transaction Order Fairness.* PODC 2026. DOI
[10.1145/3796701.3815912](https://doi.org/10.1145/3796701.3815912). Formalized version: the 4-page brief
announcement (no arXiv version; the full version, HAL hal-05625798, was not used). The BA gives proof ideas only;
we wrote complete proofs.

**Verdict: ⚠️ Minor statement issues.** Theorem 5.1 (the feasible region `θ > Δ/k`, `φ > 1 − h/k` gives an acyclic
AOF graph) is correct, and its proof idea works as written. Theorems 3.1 and 5.2 (cycle constructions) are true
only when the number of nodes `n` may be taken large. Read with the model's fixed `n`, both are false: for
`n = 4`, `h = 3/4` the cycles claimed by Theorem 5.2 do not exist. Their proofs ("as the number of Byzantine groups
grows") show that a large `n` was intended. With `n` large we prove both.

## Mistakes in the paper

* **Theorem 5.2 needs many nodes; false for the standard `n = 3f + 1 = 4`.** The theorem says that in the model
  (`n` nodes, honest fraction `h`), every `θ ≤ Δ/k` and `φ < 1 − h/(k+1)` admit a synchronous profile whose AOF
  graph has a cycle. Take `n = 4` with 3 honest nodes (`h = 3/4`), `k = 1`, `θ = Δ > 0` and `φ = 0.6 < 0.625`. All
  hypotheses hold, including `1 − h/k ≤ h`. An edge then needs `⌈0.6·4⌉ = 3` supporters, so at least 2 honest ones,
  more than `|H|/2`. The counting argument of Theorem 5.1 with `k = 2` (`θ = Δ > Δ/2`) applies, so *no*
  `Δ`-synchronous profile has a cycle. The proof idea gets support "arbitrarily close to `1 − h/(k+1)`" by
  splitting the Byzantine nodes into more and more groups, which needs `n → ∞`. For a fixed `n`, each edge of the
  construction loses about `⌈hn/(k+1)⌉` honest supporters and one Byzantine supporter. We prove the intended
  statement: for all sufficiently large `n` with `hn` integral (explicitly, whenever
  `φn + hn/(k+1) + 2 ≤ n`) the rotating construction gives a cycle. (`theorem_5_2_fixed_n_false`;
  repaired: `theorem_5_2`, `theorem_5_2_finite`)
* **Theorem 3.1 also needs many nodes.** "For any `φ ∈ (1/2, 1)` … there is a `Δ_sync`-synchronous arrival profile"
  with a `φ`-majority cycle. Fix `n` and take `φ > 1 − 1/n`. Then every vote edge needs all `n` nodes, and no node
  can receive the transactions of a cycle in strictly increasing order, so no profile has such a cycle. The proof
  idea picks `k > 1/(1 − φ)` groups, so the intended reading lets the profile choose `n ≥ 1/(1 − φ)`. Under that
  reading the theorem holds (for any `φ < 1`, even with all nodes honest). (`theorem_3_1_fixed_n_false`;
  `theorem_3_1`)
* **The "boundary gap" of §5/§7 is closed by the paper's own Theorem 5.1.** §7 says the feasible and infeasible
  regions "intentionally leave a small boundary gap" between `1 − h/k` and `1 − h/(k+1)`, and that closing it
  "would require a sharper characterization". But if `θ ≤ Δ/k`, Theorem 5.2 applies with `k`, and if
  `θ > Δ/(k+1)`, Theorem 5.1 applies with `k + 1` instead of `k`. So on every band `Δ/(k+1) < θ ≤ Δ/k` the
  threshold is exactly `1 − h/(k+1)` (up to the large-`n` caveat above). This is a remark, not a theorem, so it
  does not affect the verdict. (`threshold_tight`)
* Minor: the hypothesis `1 − h/k ≤ h` of Theorems 5.1 and 5.2 is never used. Theorem 5.1 needs `n ≥ 1`; with
  `n = 0` every pair is an edge.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* A finite node type (`n` nodes) with an honest finset `H`; the rest are Byzantine. The honest fraction `h` is
  linked by `|H| = h·n`. A profile `ts : Node → Tx → ℝ` gives every node's reported timestamp for every
  transaction. Byzantine timestamps are arbitrary.
* `Δ`-synchrony: honest timestamps of each transaction differ by at most `Δ`. Every honest node receives every
  transaction of the profile. There is no clock skew; timestamps are real times.
* `I_θ(tx, tx') = {i | ts_i(tx) + θ ≤ ts_i(tx')}`, `tx ≺_{θ,φ} tx'` iff `|I_θ| ≥ φn` (`Prec`), exactly as in §2.
  A "cycle" is `TransGen Prec x x`. In §3 the vote relation (`VotePrec`) uses strict receive order with support
  `≥ φn`.
* No protocol, no randomness: these are combinatorial statements about profiles. The positive result quantifies
  over all profiles; the constructions exhibit one profile (and choose `n`, see above). §6 (the HotStuff-based
  protocol sketch) is not formalized.

**Main results in Lean.** (namespace `Podc.DelayOptimalOrderFairness`)

| Paper | Lean | File |
|---|---|---|
| §2: AOF implementable iff the constraint graph is acyclic | `exists_strictTotalOrder_iff_not_hasCycle` | `Defs.lean` |
| Theorem 5.1 (acyclic for `θ > Δ/k`, `φ > 1 − h/k`) | `theorem_5_1` | `Feasible.lean` |
| Theorem 5.1, counting form (`kθ > Δ`, each edge missed by `< |H|/k` honest nodes) | `not_hasCycle_of_count` | `Feasible.lean` |
| Theorem 5.1, "hence topological sorting" | `theorem_5_1_order` | `Feasible.lean` |
| Theorem 5.2 for fixed `n`: **false** (`n = 4`, `h = 3/4`) | `theorem_5_2_fixed_n_false` | `Feasible.lean` |
| Theorem 5.2 (large `n`) | `theorem_5_2` | `Boundary.lean` |
| Theorem 5.2, explicit finite condition `φn + hn/(k+1) + 2 ≤ n` | `theorem_5_2_finite` | `Boundary.lean` |
| Exact threshold on `Δ/(k+1) < θ ≤ Δ/k` (remark §7) | `threshold_tight` | `Boundary.lean` |
| Theorem 3.1 (large `n`, all nodes honest) | `theorem_3_1` | `TimedCycle.lean` |
| Theorem 3.1 for fixed `n`: false | `theorem_3_1_fixed_n_false` | `TimedCycle.lean` |

**Not formalized.** §4 (comparison with other fairness notions) and §6 (protocol sketch, `Order(R)`, Sync HotStuff
carrier, the partially synchronous `n − 2f` remark).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
`theorem_5_1_nonvacuous` exhibits a synchronous profile with a real AOF edge to which Theorem 5.1 applies.
The constructions of Theorems 3.1/5.2 are explicit profiles (`driftProfile`, `cycProfile`). Self-contained
(Mathlib only). CSLib candidates (marked `-- CSLib candidate` in `Defs.lean`): the iff between "respected by a
strict total order" and acyclicity, and the acyclicity criteria `not_hasCycle_of_lt` / `not_hasCycle_of_kstep`
with `HasCycle.exists_periodic`.
