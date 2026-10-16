# Differences between the formalization and the paper

Paper: Fraigniaud, Paz, Rajsbaum, *A Speedup Theorem for Asynchronous Computation with Applications to
Consensus and Approximate Agreement*, PODC 2022; formalized from arXiv:2206.05356v2 (full version, which
contains the proofs of Claims 3, 4 and Section 5.3 that the proceedings version omits).

Classification: **[F]** false statement, **[D]** false only in a degenerate case, **[G]** proof gap
(statement true), **[U]** under-specified definition / implicit assumption, **[T]** typo,
**[M]** modelling choice of the formalization (no claim about the paper).

## Model and definitions

1. **[M] Combinatorial topology replaced by executions.** Complexes, simplicial maps and the carrier
   map `Ξ` are not formalized. A one-round model is a set of *patterns* `Model.Pat I a` (who sees whom
   and what the box returns, for a participating set `I` and box inputs `a`). Views are full-information
   views (`View`, `step`). A `t`-round algorithm is a pair (box-input function, decision function), i.e.
   the decision map `f` of the paper. "`f : P^(t) → O` agrees with `Δ`" becomes `Solves`: for every
   input simplex `σ = (I, x)` and every execution in which exactly `I` participates, the decisions of `I`
   form an element of `Δ(σ)`. Executions are unique given the patterns, so simpliciality is automatic.
2. **[U] Meaning of "solvable" when `Δ` is not a carrier map.** The paper explicitly drops the
   carrier-map requirement on `Δ` (Section 2.2) but keeps the complex-based definition
   `f(P^(t)(σ)) ⊆ Δ(σ)`. If `P^(t)(σ)` is read literally as a complex containing `P^(t)(σ')` for faces
   `σ' ⊂ σ`, then an execution of two processes would also have to respect `Δ` of every 3-process
   superset. Under that reading the liberal approximate agreement (Definition 4) would be no different
   from approximate agreement and the 2-process clause of `consensus3` would be void. We use the
   standard reading: participation is exact (`Solves`), and crashes during a round are faces of
   failure-free executions (item 3). All results of the paper hold in this reading.
3. **[U] Implicit model assumptions of Theorems 1/2.** The proof of Theorem 1 uses `P^(1)(τ') ⊆ P^(1)(τ)`
   for faces `τ' ⊂ τ` (a round of a subset of processes extends to a round of all of them). This is
   explicit here as `Model.Extendable`. It also uses that every process sees itself and only
   participants (`Model.WellFormed`), besides solo executions (`Model.AllowsSolo`). All are proved for
   IIS, iterated snapshot, IIS+test&set and IIS+binary consensus (`Podc/IteratedModel/Patterns.lean`).
4. **[U] Black boxes (Section 4).** The "consistent box" remark is formalized by letting patterns depend
   only on the participating set and the box inputs. The proof of Theorem 2 also needs that a process
   running solo gets an answer determined by its own box input ("`b_i = B_t(a_i)` ... whenever process `i`
   is running solo"). This is the explicit hypothesis `Model.SoloDet b₀`. It holds for test&set (the solo
   caller wins) and binary consensus (the solo caller gets its proposal). We did not determine whether
   Theorem 2 can fail for boxes with nondeterministic solo answers.
5. **[U] Placement of the box call under immediate snapshot.** Algorithm 2 calls the box between the
   write and the collect, while an immediate snapshot is an atomic write+snapshot. We model the
   test&set winner (resp. the binary consensus proposal that wins) as a process of the first
   concurrency class of the round, i.e. a process seen by every participant. This is exactly the set of
   first callers compatible with write–call–read. It gives 7 vertices per colour in Figure 5 and makes
   the solo caller win. Only the executions `ϱ_{i,j,k}`, `ϱ_{j,i,k}` and the solo answer are used by the
   lower-bound proofs.
6. **[M] Tasks as relations.** A task is `(Inp, Δ)`; the output complex `O` and the vertex set
   `V(O') = V(O)` of Definition 2 are not represented (they play no role in solvability). Equalities of
   tasks ("`CL_M(Π) = Π`", Claims 2–4, 6) are stated as equalities of `Δ(σ)`. Output vectors are total
   functions `P → Y`, and only their values on `id(σ)` matter.
7. **[M] Local task (Definition 1).** Its inputs are the faces `(J, τ)` with `∅ ≠ J ⊆ id(σ)`. A single
   participant must output its input; for `|J| > 1` the outputs must coincide on `J` with some element of
   `Δ(σ)` (= `proj_J Δ(σ)`). Hard-coding `σ`, `τ`, `ρ` into the one-round algorithm is allowed, as in the
   paper ("one can think of τ, σ, ρ and f as hard-coded").
8. **[M] "Solvable in at most one round" (Definition 2)** is formalized as "solvable in one round";
   these are equivalent (`Solvable.succ`).
9. **[M] Approximate agreement on the grid.** Values are scaled by `m`: inputs/outputs in
   `{0,…,m} ⊆ ℤ`, precision `ε = e/m` with `e ∈ ℤ`. Outputs are automatically on the grid. Binary
   consensus uses `Bool` inputs and the (equivalent) validity + agreement specification. The
   participants are restricted to a set `S` (`S = univ` for the paper's tasks, smaller `S` in Section 5.3).
10. **[M] Algorithms in Section 5.3** "whose call to binary consensus depends only on the ID and the
   round" = `IdOnly` (box input `γ r i`); the closure "w.r.t. `β`" is `closureβ`.

## Statements

11. **[U] Domain of `ε`.** Definition 3 requires `ε ∈ (0, 1]`, but the proofs of Corollary 3 and
    Theorems 3, 4 apply Claims 2–4, 6 to `3^k ε` and `2^k ε`, which may exceed 1. All claims are proved
    for every `e ≥ 0` (inclusions `Δ' ⊆ ...` for every `e`).
12. **[M] Claim 2 holds for any `n` in the direction used.** The inclusion `Δ'_ε ⊆ Δ_{3ε}` holds for
    every number of processes (`closure_aa_subset`); the equality is proved for two processes (`claim2`).
13. **[G] Claim 6 and the iteration in Theorem 4.** Claim 6 assumes `|S| ≥ 5`. The iteration in the
    proof of Theorem 4 applies it to every `S_k`, `k ≤ t − 2`, but checks only `|S_{t−1}| ≥ 3`. The
    missing check holds (`|S_k| ≥ n/2^k > 4`). In fact the inclusion of Claim 6 needs no size hypothesis
    (for `|S'| ≤ 2` it is trivial), and we iterate with the invariant `|S| ≤ 2^(t+1) ∨ 1 ≤ 2^t ε`
    (`theorem4_aux`). This yields exactly the paper's bound `min(⌈log₂ n⌉ − 1, ⌈log₂ 1/ε⌉)`.
14. **[U] Scope of the binary-consensus result (abstract, Section 1.2, Conclusion).** The abstract says
    test&set and binary consensus "are not more powerful as far as helping solving approximate agreement
    faster is concerned". The conclusion says binary consensus is "not useful ... (at least when
    `n ≥ 1/ε`)". Theorem 4, the only result about binary consensus, covers only algorithms whose
    consensus inputs depend on ids and rounds. Its bound `⌈log₂ n⌉ − 1` is one round below the IIS bound
    `⌈log₂ 1/ε⌉` whenever `1/ε ≤ n ≤ 2^⌈log₂ 1/ε⌉` (e.g. `n = 4`, `ε = 1/4`: bound 1 versus 2); it
    reaches the IIS bound only for `n > 2^⌈log₂ 1/ε⌉` (e.g. `n ≥ 2/ε`). The claims
    are informal, so we classify this as an overstatement, not a false theorem. Theorem 4 itself is
    proved as stated.
15. **[T] Proof of Claim 4.** It says "the simplices of `P^(1)(σ)` considered in the proof of
    Corollary 2". They are simplices of `P^(1)(τ)`, the protocol complex of the local task (as in
    Corollary 2's own proof, which also writes `P^(1)(σ)` and `f : P^(1) → O`).
16. **[T] Proof of Theorem 1 (proceedings version).** "`f(𝜚') ∈ Δ(σ)`. Since `id(f(ρ')) = id(ϱ')`"
    mixes `ρ'` and `ϱ'`.
17. **[M] Corollary 2** is proved via the paper's relaxed task (`consensus3`), including the fixed-point
    equality `CL(Π) = Π` (`consensus3_fixedPoint`), for any `n ≥ 3`.
18. **[M] Logarithmic forms.** Corollary 3 and Theorems 3, 4 are proved in the scaled form
    (`m ≤ 3^t e`, `m ≤ 2^t e`, `n ≤ 2^(t+1) ∨ m ≤ 2^t e`) and then converted to the paper's
    `⌈log_b (1/ε)⌉ ≤ t` with `ε = e/m` and `Real.logb` (assuming `e, m > 0`).

## Additions (not claimed formally in the paper)

19. **Tightness (Remark after Corollary 3).** We prove the upper bounds: `ε`-agreement is solvable in
    IIS in `t` rounds when `1 ≤ 2^t ε` for any `n` (`aa_solvable_many`), and when `1 ≤ 3^t ε` for two
    processes (`aa_solvable_two`). This uses a composition lemma for uniform one-round reductions
    (`solvable_succ_of_reduction`) and Equations (3) and (2). Equation (2) is used in a sign-symmetric form
    (`clamp`) that equals Equation (2) when `y₁ ≤ y₂` and its mirror image otherwise.
20. **Figure 4.** Two-process consensus is solvable in one round of IIS + test&set
    (`twoConsensus_iisTS`). This shows that `n ≥ 3` is needed in Corollary 2 and that the model is
    non-vacuous.

## Not formalized

- The topological pictures (Figures 1–3, 5–7) and the iterated *collect* model (Theorem 1 is proved
  for an abstract model; instances: IIS, iterated snapshot, IIS + test&set, IIS + binary consensus).
- The "essentially tight" remark for Theorem 4 (the `⌈log₂ n⌉`-round consensus algorithm with binary
  consensus objects).
