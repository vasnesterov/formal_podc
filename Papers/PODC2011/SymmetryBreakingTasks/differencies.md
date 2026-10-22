# Differences between the formalization and the paper

Paper: Imbs, Rajsbaum, Raynal, *The universe of symmetry breaking tasks*, PODC 2011; full version
IRISA PI 1965 (January 2011), whose numbering we follow.

## Errors and missing hypotheses (see README for details)

1. **Lemma 1** lacks `ℓ_v ≤ u_v` for all `v`. Counterexample `lemma_1_false`; corrected `lemma_1`.
2. **Theorem 4** is false in integer arithmetic when `ℓ = 0` and `u(m−1) > n`
   (`theorem_4_int_false`: `⟨6,3,0,6⟩`; `theorem_4_int_false_renaming`: `⟨n,2n−1,0,1⟩`, `n ≥ 3`).
   `theorem_4` uses truncated subtraction (equivalently `max(0, n − u(m−1))`) and assumes `m ≥ 1`.
   For `m = 0` the statement fails even in ℕ: `n = 0`, any `ℓ ≥ 1` is feasible and trivially anchored.
3. **Theorem 9 / Section 2.3.** The paper restricts all algorithms to index-independent and
   comparison-based ones. Theorem 9 holds only without the comparison-based restriction. With it, a
   no-communication decision function is constant (`ComparisonBased.const`), and solvability becomes
   `ℓ = 0 ∧ n ≤ u` (`noComm_comparisonBased_iff`, counterexample `theorem_9_comparisonBased_false`).
   We formalize Theorem 9 for index-independent algorithms (`theorem_9`). Theorem 2's
   "without loss of generality comparison-based" does not preserve "no communication".
4. **Theorem 9 proof**: "the task specification requires `|G_i| ≤ u`" replaced by choosing `u+1`
   identities of a large group and completing them to `n` distinct identities. This uses
   `u + 1 ≤ ⌈(2n−1)/m⌉ ≤ n` for `m ≥ 2`.
5. **Theorem 6**: as stated, it is Lemma 5 / Lemma 4 (`theorem_6`). We also prove the intended
   equality (synonymy), without a feasibility assumption (`theorem_6_eq`).
6. **Theorem 10 proof**: uses Lemma 4 in the wrong direction. We prove the reduction directly with the
   parity map for every `u` (`parity_mem_wsb`).
7. **Theorem 8** needs feasibility ("any GSB task" → any feasible GSB task); typos `m/n` for `n/m` in
   the proof.
8. **Corollary 2** needs `x ≥ 1` (`corollary_2 (hk : 1 ≤ k)`); **Corollary 4** needs `k ≤ n`.
9. **Theorem 11** (not formalized) needs `n ≥ 2`; its proof cites "Lemma 2" instead of Theorem 2.
10. **Canonical representative** (Section 4.2): the definition is ambiguous for `u > n` (and for
    `m = 1`); `canonical_not_unique` exhibits two synonymous `(ℓ,u)`-anchored tasks. We take
    Theorem 7's `f` as the definition and prove it gives a canonical form (`theorem_7_iff`).
11. **Table 1** omits the feasible task `⟨6,3,2,6⟩` (`table_1_missing_row`). All printed entries are
    correct (`table_1`).
12. **Text typos**: kernel set of `⟨6,3,1,4⟩` printed as `{[4,1,1],[4,1,1],[2,2,2]}` (should be
    `{[4,1,1],[3,2,1],[2,2,2]}`); in the §4.1 Remark `[4,2,1]` sums to 7; Theorem 7's proof asserts
    `u ≤ n`, which need not hold (e.g. `⟨4,2,0,5⟩`), though it is not used.

## Modelling choices

* **Values and identities.** Values are `Fin m` = `0..m−1` (paper: `1..m`); identities are `Fin N`
  (paper: `1..N`). In Theorem 8 the map `d ↦ ((d−1) mod m) + 1` becomes `d ↦ d mod m`. In
  Corollary 2 the map `id ↦ ⌈id/x⌉` becomes `a ↦ ⌊a/x⌋`. In Figure 2, names `n`, `n+1` become `n−1`, `n`
  and slots are `0..n−2`.
* **Tasks** are sets of output vectors (`gsb`, `sgsb`). Since `Δ(I) = O` for all `I`, the input
  vectors play no role in the combinatorics (Sections 3–4). In the algorithmic statements the inputs are
  the distinct identities (`gsbTask`).
* **Arithmetic** in ℕ (truncated subtraction, `⌊·⌋ = /`, `⌈·⌉ = ⌈/⌉`). For Theorem 3 and all other
  statements this matches the paper on the relevant (feasible) instances; for Theorem 4 see item 2.
* **Feasibility** of a symmetric task is `Feasible n m ℓ u := mℓ ≤ n ≤ mu`, equivalent to non-emptiness
  by Lemma 2 (`feasible_iff`). The paper's "`ℓ ≤ n/m ≤ u`" (Corollary 1, Theorem 5) is stated this way.
* **Definition 5** uses `ℓ − 1` in ℕ for `max(0, ℓ−1)`.
* **Kernel vectors** are non-increasing count vectors `Fin m → ℕ`. Lemma 3 is the (trivial) totality of
  the lexicographic order `Lex (Fin m → ℕ)`. We add `kernelSet_eq_iff`: the kernel set determines the
  task, which justifies the paper's identification of tasks with kernel sets.
* **Theorem 5** is stated as: `⟨n,m,⌊n/m⌋,⌈n/m⌉⟩` is feasible and its output set is contained in
  that of every feasible `⟨n,m,ℓ,u⟩`.
* **Theorem 7** is stated as: one application of `f` gives a fixed point; it is feasible and a synonym;
  its bounds are the largest lower bound and the smallest upper bound among all synonyms
  (`theorem_7`); and synonymy of feasible tasks iff equal `f`-images (`theorem_7_iff`). The paper
  states existence of "the fixed point" and canonicity informally.
* **Algorithm model** for Theorems 8, 10 and Corollary 5: CSLib's iterated full-information model
  (`Cslib.Iterated`), arbitrary round model `M` and number of rounds `t`, instead of the paper's
  `ASM_{n,n−1}[T]`. The reductions are local post-processing maps, so they are model-independent. Using
  a task as an object (`ASM[T1]`) is represented by "any algorithm that solves `T1`" (Theorem 8: "from
  any solution to the `⟨n,n,1,1⟩`-GSB task").
* **Index independence** in the iterated model (`Alg.IndexIndependent`) means uniform code: the same
  box-input and decision functions for every process. For `0` rounds it coincides with the paper's
  permutation-invariance definition (§2.2); for `t ≥ 1` it is weaker, because full-information views
  are indexed by process. It is used only as a side claim of `theorem_8` (post-processing preserves
  it) and, with `0` rounds, in `noComm_iff`.
* **"No communication"** (Theorem 9): a single decision function `δ : Fin N → Fin m`
  (`NoCommSolvable`). `noComm_iff` shows equivalence with 0-round index-independent solvability in
  `Cslib.Iterated` (for `n ≥ 1`).
* **Comparison-based** (no communication): `ComparisonBased n δ` says decisions are unchanged under any
  order-preserving change of the identity vector, as in Section 2.2.
* **Theorem 10 and Corollary 5**: the cited impossibility results (WSB / `(2n−2)`-renaming
  unsolvability under the binomial gcd condition [Castañeda–Rajsbaum]; Theorem 11 for election) are
  hypotheses. We prove only the reductions.
* **Theorem 12**: executions are abstracted as described in `SlotRenaming.lean`. We use the `KS`
  outputs (a `(n−1)`-slot output vector) and write/snapshot linearization times with `w i < r i`, all
  distinct; `p_i`'s snapshot contains `STATE[j]` iff `w j < r i`. Only executions where all processes
  decide are considered. Decisions are write-once and Definition 1's validity concerns only such
  extensions, so this loses nothing. Wait-freedom (straight-line code) is not formalized. When several
  conflicting processes are visible, which one `p_i` compares with is chosen by `Classical.choose`; in
  the relevant executions there is only one.

## Not formalized

* Theorem 1 (identity space larger than `2n − 1`) and Theorem 2 (WLOG comparison-based): both rely on
  a cited comparison-based, index-independent `(2n−1)`-renaming algorithm.
* Theorem 11 (election not wait-free solvable): topological argument (pseudomanifold, connectivity of
  the protocol complex of immediate-snapshot executions).
* Section 5.3's citations (equivalence of WSB and `(2n−2)`-renaming) and Section 6's remarks on the
  `2`-slot task.
