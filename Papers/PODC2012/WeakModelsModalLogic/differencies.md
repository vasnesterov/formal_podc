# Differences between the formalization and the paper

Paper: Hella et al., *Weak models of distributed computing, with connections to modal logic*, arXiv 1205.2051v3.

## Model and definitions (no effect on the results)

1. **Ports are 0-based.** Ports are `0, …, deg v − 1` instead of `1, …, deg v`, and `μ` takes a port index in `ℕ`;
   only indices `< Δ` matter (`IsBroadcast` quantifies over `i, j < Δ`).
2. **Port numbering.** It is the paper's bijection `p : P(G) → P(G)` with `A(p) = A(G)`, stated as two inclusions
   (`PortNumbering.adj`, `cover`; `A_eq` restates the set equality). From it we derive that out-ports and in-ports of
   a node are in bijection with its neighbours (`injective_outNbr`, `injective_inNbr`), which the paper uses
   implicitly ("in any port numbering `π(v, vᵢ) ≠ π(v, vⱼ)`").
3. **Degree** is `Nat.card` of the neighbour set. `G ∈ F(Δ)` is `[Finite V]` plus `MaxDegLE G Δ`.
4. **`Δ` ranges over all of `ℕ`, including 0.** The paper uses positive `Δ`. This is equivalent: `F(0) ⊆ F(1)`, so
   `A₀ := A₁` works.
5. **Output sets.** `Y` is an arbitrary type, not necessarily finite, and is shared by the problem and the machines'
   stopping states. The equalities (Theorems 4, 8, 9; Corollaries 7, 10; `collapse`, `collapse1`) hold for every
   `Y`. The strict inclusions are stated for `Y = Bool`, the paper's `{0, 1}`.
6. **Graph problems** are functions on all graphs `G : SimpleGraph V` (`V : Type`); only finite `V` matter.
7. **Classes.** The paper's classes become `VV Y` etc. via `Solvable C`, and the constant-time ones via `Solvable1 C`
   (time `T'(Δ)`). `VVc` uses `SolvesInC` (only consistent port numberings).
8. **Bisimulation, condition (B1).** The paper requires agreement on the propositions `qᵢ` (`deg = i`, `i ∈ [Δ]`); we
   require `deg v = deg v'`. These are equivalent on `F(Δ)`. We only use bisimulations of a model with itself (all
   uses in the paper are of this kind). The modal indices range over all `i, j ∈ ℕ`; `R(i,j)` is empty for indices
   `≥ Δ` anyway.

## Proofs

9. **Corollary 3** is proved directly: bisimilar nodes have identical states at all times for every algorithm of the
   class (`state_eq_of_bisimPP`/`PM`/`MM`). The paper goes through Theorem 2 and Fact 1 instead. Same statement.
   Our version allows any `Y` and replaces "`u ∈ S`, `v ∉ S`" by `S u ≠ S v`.
10. **Theorem 4.**
    * Running time `T + 2Δ + 1` (the paper says `T + O(Δ)`; since its `Δ ≥ 1`, this is `≤ T + 3Δ`).
    * `C_Δ` runs `2Δ + 1` rounds and the simulation uses the label `β_{2Δ+1}`, which refines `β_{2Δ}`.
    * The paper's "all messages received by a node are distinct" is false: stopped neighbours and padding all
      deliver `m0`. Our `Set` machine reconstructs `A`'s multiset anyway (`canon`, `multiset_eq_of_noDupSome`). The
      non-`m0` entries are pairwise distinct by Lemma 6, so any vector with the same set and pairwise distinct
      non-`m0` entries has the same multiset.
    * The values `β_t` are encoded injectively in `ℕ` (`Encodable`); only their equalities are used.
    * Proof repair, minor (decides the 🛠️ verdict only together with item 12).
11. **Lemma 5** is proved for `t ≥ 3` (`lemma5'`); the paper's statement for `t ≥ 4` is `lemma5`. "Order `k`" is
    formalized as "`v` has at least `k` distinct neighbours with the same `β_t`" (the same notion). The case `k = 0`
    is handled separately; the paper's proof needs `v₁`. In Lemma 6's consequence the paper uses order 2 without
    saying so.
12. **Theorems 8/9: genuine repair (🛠️).**
    * The paper's `B` cannot receive the histories of neighbours that have stopped (they send `m0`). Our `B` stores
      the multiset of received histories and extends the missing ones by `m0`:
      `H' = R + (H − R.map dropLast).map (· ++ [m0])`.
    * The family `P_t` of compatible port numberings is replaced by one port numbering `simPort`. It copies the
      out-ports of `p₀` and sorts in-ports by the time-`T` histories of `B`'s run on `p₀` (`Tuple.sort` with an
      arbitrary well-order on messages).
    * Equality of `A`'s run on `simPort` with `B`'s run is proved by induction, using `take_le_take`: truncation is
      monotone for the lexicographic order.
    * Same running time `T`, as claimed.
13. **Theorem 11.** The problem is unspecified on stars with `k ≤ 1`; `starProblem` leaves them unrestricted (as for
    non-stars). The non-membership witness is the 2-star on `Fin 3`. The algorithm checks "degree 1 and message `1`
    received" (the received set also contains `m0` when `Δ > 1`; the paper writes "the set `{1}`").
14. **Theorem 13.** The graph is the paper's figure, numbered 0–22 (`g13`). The five classes are `g13Kind`, and the
    bisimulation is checked by `decide`.
15. **Lemma 15.** We use CSLib's `Matrix.exists_perm_decomposition` (a `k`-regular `ℕ`-matrix is a sum of `k`
    permutation matrices, via Hall) on the adjacency matrix. This replaces the 1-factorisation of the bipartite
    double cover; it is the same argument.
16. **Lemma 16.** We show that `F` is an involution with a fixed point via a parity argument on the support of a
    permutation. The empty graph is handled separately.
17. **Theorem 17.**
    * Local types are computed from in-ports (what an algorithm can see). With consistency this equals the paper's
      out-port definition.
    * Types are encoded as lists of length `deg v` (no 0-padding, which would clash with 0-based ports); equal types
      imply equal degrees.
    * "Equal types ⇒ all nodes bisimilar" does not need consistency.
    * The step "`t(u) < t(v)` with `t(v)` maximal gives `S(u) = 0`" is repaired: by connectivity there is an edge with
      endpoints of different types, and its smaller endpoint outputs `0` (minor; the paper invokes connectivity
      for exactly this).
    * `thm17Problem` is `{S | G ∈ 𝒢 → S non-constant}`, which is equivalent to the paper's case split.
    * The Figure 9a graph is `fig9a`. "No 1-factor" is proved by the parity argument (two gadgets suffice).
18. Corollaries 12, 14, 18 are derived from Theorems 11, 13, 17 and the trivial inclusions, as in the paper.

## Not formalized

* Theorem 2 (modal-logic characterisations) and the observations (a)–(d) of §5.4.
* Remark 2 (`SB_o`) and §3.4 (local inputs).
* "It is easy to construct `k`-regular graphs in `𝒢` for each odd `k ≥ 3`" (only `k = 3` is used).
* The explicit numbering of Figure 9b; the remark after Lemma 15 (its converse).

## Verdict rule

The worst issue is a proof gap in Theorems 8/9: the simulation as described does not handle stopped neighbours, and
the fix needs an extra mechanism. All statements are true as written, so the verdict is **🛠️ Proof repaired** (R1: false claims inside a proof of a
true result — "all messages received are distinct" in Theorem 4, the history-based reconstruction in Theorems 8/9 —
are proof repairs; R6: worst label wins).
Borderline: one could call the gap routine, which would give ✅. We chose 🛠️ because the paper's construction, read
literally, does not work as soon as some node stops before others, and that is the generic case.
