# Differences between the formalization and the paper

Paper: M. Pacut, M. Parham, S. Schmid, *Brief Announcement: Deterministic Lower Bound for Dynamic
Balanced Graph Partitioning*, PODC 2020 (3 pages, no full version).

## Gaps and errors in the paper

1. **Theorem 2.1: the algorithm is assumed to keep ground sets collocated.** The proof assumes
   ("Any competitive algorithm ... maintains a perfect partition of ground sets") that after each
   step the algorithm keeps every revealed ground set in one cluster. A deterministic online
   algorithm need not do so. *Fix:* the adversary issues a request inside a ground set whenever the
   current configuration splits one (`LB.splitPair`, `LB.next`). Each such request costs the
   algorithm `≥ 1` (`one_le_stepCost`). The next pivot step happens only once all ground sets are
   collocated again. The migration cost between two consecutive such configurations is `≥ 2α`
   (`LB.two_le_dist`, via the triangle inequality on the migrations in between). The adversary
   stops after `2α·S + 1` requests at the latest; if it has not finished by then, the algorithm
   has already paid `> 2α·S`.
2. **Theorem 2.1: the pivot `z`.** Let `z` be the node of `B`'s home cluster outside `B`. The paper
   does not exclude that `z` becomes a pivot `xᵢ` for `i ≥ 1`. It can, if the algorithm moved `z`
   away while `B` was requested and later picks `z` as a new pivot. Then no ground set of `z`'s
   origin lies in another cluster (the only one is `B`), the step is undefined, and following the
   text (`Cᵢ = B`) yields an internal request after which no pivot exists. *Fix:* `z ∈ {x₀, y₀}`.
   In our adversary the first pivot step happens in the initial configuration, so `x₀ = z`, and
   `y₀ = (1, 0)`.
3. **Theorem 2.1: off-by-one slips (harmless).** The count `Σ(|C*| - 1) - (k - 1)` should subtract
   `k - 2` (`B` has `k - 1` nodes). The stopping threshold `ℓ + 3` can be `ℓ + 2`, because the
   isolated nodes avoid `B`'s home cluster and `ℓ` of them already force two of the same origin.
   We prove `ALG ≥ 2α((k-2)(ℓ-1) - 2)`. The paper's `((k-2)(ℓ-1) - 4)/2` follows
   (`theorem_2_1_paper`).
4. **Competitive ratio not defined.** See the README: the bound holds for strict competitiveness or
   an additive constant independent of `α`. We state it as
   `c ≥ ((k-2)(ℓ-1)-2)/2 - β/(4α)` (`theorem_2_1_competitive`; requires `c ≥ 0`).
5. **Theorem 2.2 has no proof in the paper.** We supply one, with ratio `2(n-1) = 2(kℓ-1)` and no
   additive constant. It holds only in the static model where communicating pairs communicate
   forever. On finite inputs PPL is not `O(kℓ)`-competitive: for a single external request, OPT
   pays `1` and PPL pays `≥ 2α`. This is not a counterexample to the paper: Section 2 defines the learning model
   with pairs that "communicate forever", which is our static form. (We did not formalize this remark.)
6. **Lemma 3.1 has no proof in the paper.** We prove it. "Exchanges at most two pairs of nodes" is
   formalized as "the closest component-respecting configuration is at distance `≤ 4`" (distance =
   number of nodes placed differently).
7. **Theorem 3.2 has no proof in the paper** (and ALG3's phase structure is only sketched); not
   formalized.

## Modelling choices

* **Costs.** Integer costs in `ℕ`: `α ∈ ℕ`, `α ≥ 1` (the paper: `α ∈ ℤ⁺`). Migration cost is
  `α · dist P Q`, where `dist` is the number of nodes in different clusters. A "swap" is two
  migrations. The paper counts swaps; we count migrations, and the ratio is the same.
* **Online algorithm.** `OnlineAlg.conf : List (Req V) → Config` gives the configuration after the
  revealed requests; the last request is served in it (repartition before serving). It must be
  balanced; `conf [] = init`. Cost: `algCost`, via `schedCost` of the induced schedule.
* **OPT.** `optCost` is the infimum (a minimum) over balanced schedules `O` with `O 0 = init`. For
  infinite inputs we do not define OPT as a number. Theorem 2.2 compares PPL with every schedule
  prefix-wise: `∀ T, ∃ T', PPL(σ≤T) ≤ c·O(σ≤T')`, which is `sup PPL ≤ c · sup O`.
* **Learning model.** Finite form: some balanced configuration makes every request internal. Static
  form: the same for an infinite sequence, plus every requested pair is requested again after any
  time. The lower bound is given in both forms. In the static form it is witnessed by an offline
  schedule paying `≤ 4α` on every prefix, while `ALG ≥ 2α((k-2)(ℓ-1)-2)` on all long prefixes.
* **Lower-bound instance.** Nodes `Fin ℓ × Fin k`, initial partition `Prod.fst` (the paper: "an
  arbitrary initial partition"). The paper first issues requests inside `B`; we never request `B`
  unless the algorithm splits it. `B` is still a ground set, and `P*` collocates it.
* **Choice of the ground set joined by the pivot.** The paper joins the pivot to the *largest*
  ground set of the same origin. We join it to the unique non-trivial ground set of its origin, or
  to a fresh node of its origin (`LB.fresh`) if there is none. This is the paper's invariant ("no
  two non-singleton ground sets have the same origin") made explicit.
* **OPT ≥ 1** is proved (`one_le_optCost`; the first request is external initially), so the ratio
  statement is meaningful.
* **PPL components** are represented by a labelling `comp : V → V`; a merge relabels one
  component. PPL merges only on inter-cluster requests and moves to a balanced component-respecting
  configuration closest to the *initial* configuration (`closest`). Ties are broken arbitrarily
  (choice). The fallback when no such configuration exists never occurs on learning inputs.
* **ALG3 / Lemma 3.1.** The merged component structure is "respect `comp` and collocate `a`, `b`".
  The cluster size is fixed to `3` with `|V| = 3ℓ`.
