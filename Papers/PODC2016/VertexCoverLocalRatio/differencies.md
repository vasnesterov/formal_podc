# Differences between the formalization and the paper

Paper: R. Bar-Yehuda, K. Censor-Hillel, G. Schwartzman, *A Distributed (2+ε)-Approximation for Vertex
Cover in O(log Δ/ε log log Δ) Rounds*, PODC 2016, arXiv 1602.03713v2 (numbering follows it).

No false statements were found. Items are classified as in the project conventions.

## Statements

1. **Theorem 2.1 is proved in a stronger form** (no issue). We compare `w(S_δ)` with the weight of
   *every* vertex cover, not only a minimum one, and we do not need `w ≥ 0`. The function `δ` is a
   function on `Sym2 V`. Only its values on edges matter: it must be nonnegative there. (`theorem_2_1`)
2. **"ε = O(1)"** (precise reading of an asymptotic claim). Theorem 3.1 and Lemma 3.3 hold "for every ε
   = O(1)". We fix an arbitrary bound `E` and assume `0 < ε ≤ E`. The constants depend on `E`:
   `3(34+2E)/ε` rounds for `d(v) ≤ 16` and `3(2+3E)·log d/(ε log log d)` rounds for `d(v) > 16`. The exact
   count `n ≤ 2K/ε + log d/log K` (item 4) has no `K` term. `E` is needed for the other two parts of the
   bound. The `log_K d` term (at most `2K` for `K = log d/log log d`, and `< 1` for `K = d+1`) and the `+1`
   (every vertex takes part in at least one iteration) become `O(K/ε)` only through `1 ≤ E/ε`. For large `ε`
   the number of iterations is `Θ(K + log_K d)`, not `O(K/ε)`.
   The headline bound in terms of `Δ` follows from the per-vertex bound in `d(v)`. The function
   `log x/log log x` is increasing for `x > e^e ≈ 15.2`, so for `16 < d(v) ≤ Δ` we get
   `log d(v)/log log d(v) ≤ log Δ/log log Δ`. This step is not stated in Lean.
3. **Logarithms** (no issue). We use natural logarithms in `K_v = log d/log log d` and in the final bound.
   The paper does not fix the base. With base 2 the bound changes only by a constant factor, and all the
   paper's side conditions also hold for `ln` when `d > 16`: `ln ln d > 1` and `ln K_v ≥ 1`.
4. **Lemma 3.3, counting step** (proof correct, made exact). The paper uses the dichotomy
   "`d_{i+1} ≤ d_i/K` or `w_{i+1} ≤ w_i − ε'w_0/K`". We prove the exact inequality
   `w_i − w_{i+1} ≥ vault·d_{i+1}/d_i` (`drop`). Then we count for every real `K > 1`: if `v` is still
   running at the start of iteration `n`, then `n ≤ K(1−θ)/a + log d/log K` (`count_bound`,
   `active_bound`). With `a = θ = ε'` this is `n ≤ 2K/ε + log d/log K`. So `v` takes part in at most
   `n+1 < K/ε' + log_K d` iterations, which is the paper's count. We checked that the off-by-one and the
   real (non-integer) `K` are harmless.
5. **Round count** (made explicit). One iteration is three synchronous rounds: answer requests, collect
   answers and decide, notify. Round `t` belongs to iteration `⌊t/3⌋` (`cfg_st`). Requests are not sent
   in a separate round: `vault(u)/d_i(u)` is part of `u`'s state, which its neighbours read. The paper only
   says "a constant number of rounds".

## Model and algorithm

6. **Model** (modelling choice). We use the synchronous LOCAL model as CSLib's SET-LOCAL/locally-iterative
   model, where a node sees the set of its neighbours' states. Nodes carry identifiers so that an answer
   can be addressed to one neighbour, and they know their initial weight and degree. The algorithm depends
   only on `ε` and the processing order. It needs no `n` and no `Δ`, as the paper says.
7. **"Arbitrary order" in line 17** (generalized). Line 20 is formalized for *every* processing order: a
   duplicate-free enumeration `ord v S` of the requesters, which may depend on the responder
   (`greedyRule`, `greedy_spec`). All correctness and round results are in fact proved for an abstract
   response rule `R`. Its specification `Rule.Spec σ` says: each answer is in `[0, request]`, the answers
   sum to at most the bank, and if some request is not answered in full, the answers sum to at least
   `bank − σ·w_0`. The paper's rule has `σ = 0`.
8. **Neighbourhood bookkeeping** (equivalent reformulation). Lines 9, 15–16 and 29–31 maintain `N_i(v)`
   explicitly. We define `N_i(v)` as the set of running neighbours and prove the two agree (`actN_step`).
   A neighbour is removed at line 16 only if its bank is exhausted, and then it returns `InCover` in the
   same iteration. The paper's proof uses this symmetry (`u ∈ N_i(v) ⇔ v ∈ N_i(u)`) implicitly.
9. **The weight function** (no issue). `w : V → ℝ` with `w ≥ 0`, so zero weights are allowed. A vertex
   of weight 0 returns `InCover` after its first iteration.
10. **Not formalized: anonymity and asynchronous start.** The paper says the algorithm also works without
    identifiers (port numbering) and with vertices starting at different times. Neither claim is
    formalized. Our model uses identifiers only to address answers, which port numbers could do as well.

## Section 4 (CONGEST)

11. **Under-specified rule; our reading** (under-specified definition, claims hold). Section 4 halves the
    vault to `ε'w_0/2`. A partial answer becomes `t·ε'w_0(v)/2` for the largest integer `t` with
    `t·ε'w_0(v)/2 ≤ budget_i(v,u)`. The paper leaves two things open. (a) Which amount does `v` deduct,
    the rounded one or the original `budget_i(v,u)`? If `v` deducted the original amount while `u`
    deducted the rounded one, the two endpoints would disagree on `δ(e)`, and Theorem 2.1 would not apply
    directly. (b) What happens to the requests processed after a partial answer? We read it as: `v`
    grants and deducts exactly the rounded amount and goes on with the remaining bank (`congestRule`).
    With this reading the rule meets `Rule.Spec (ε'/2)`. After a partial answer less than `ε'w_0/2` is
    left in the bank, which is the paper's own remark. Then `a + σ = ε'`. Correctness holds
    (`congest_correct`), and the round bounds hold with constant `4` instead of `2`: `3(68+2E)/ε` and
    `3(4+3E)·log d/(ε log log d)` (`congest_small`, `congest_large`).
12. **Message sizes not formalized.** We do not model the `O(log n)`-bit messages, the assumption that
    weights and the max/min weight ratio fit in `O(log n)` bits, or the initial round in which `w_0`
    is broadcast. CSLib's LOCAL model has no bandwidth accounting.

## Section 5 (discussion of [KMW10])

13. **Arithmetic checked; the `Ω`-constant is implicit in the paper** (imprecise, conclusion unaffected).
    Section 5 drops the constant hidden in `Ω`. With a constant `c > 0` and `n = 2^L`, the smallest `δ`
    allowed by `n ≤ 2^{2k³+4k}δ^{4k²}` is at least `c·n^{(1/4−ε)/k²}` iff
    `2k³+4k ≤ 4εL − 4k²log₂ c`. Hence `k ≤ 4log₂(1/c)` or `k³ ≤ 4εL`, i.e. `k = O((log n)^{1/3})`. For
    the second constraint, `δ = Δ^{1/(k+1)}/2^{k/2} ≥ c·Δ^{(1−ε)/(k+1)}` iff
    `k(k+1) ≤ 2εD − 2(k+1)log₂ c`, so `k = O(√log Δ)` (`KMW.first_constraint_iff`,
    `KMW.second_constraint_iff`, `KMW.first_constraint_k_le`, `KMW.second_constraint_k_le`). With `c = 1`
    these are exactly the paper's conditions. That these constraints are the only ones available in
    [KMW10] is a claim about another paper and is not formalized. The abstract's "contradicts the lower
    bound of [KMW10]" is therefore not formalized either.
