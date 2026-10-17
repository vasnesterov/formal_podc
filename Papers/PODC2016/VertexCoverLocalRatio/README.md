# Distributed (2+ε)-approximation for weighted vertex cover — PODC 2016

Reuven Bar-Yehuda, Keren Censor-Hillel, Gregory Schwartzman. *A Distributed (2+ε)-Approximation for
Vertex Cover in O(log Δ/ε log log Δ) Rounds.* PODC 2016. DOI
[10.1145/2933057.2933086](https://doi.org/10.1145/2933057.2933086). Formalized version: arXiv
[1602.03713](https://arxiv.org/abs/1602.03713) v2; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** The local-ratio template (Theorem 2.1) and Theorem 3.1 hold as stated: Algorithm 1
is a deterministic `(2+ε)`-approximation for minimum-weight vertex cover, and a vertex of degree `d`
finishes in `O(1/ε)` rounds if `d ≤ 16` and in `O(log d/(ε log log d))` rounds otherwise, for
`ε = O(1)`. The CONGEST variant (Section 4) also holds once its under-specified rounding rule is pinned
down, with twice the constant. The arithmetic of Section 5 checks out.

## Mistakes in the paper

There are no mathematical mistakes. Minor points:

* **Section 4 is slightly under-specified.** After a partial answer `t·ε'w_0(v)/2`, the paper does not say
  explicitly which amount `v` deducts (the rounded one or `budget_i(v,u)`), nor how later requests are
  handled. Its remark that the remainder is "at most ε'w_0(v)/2" almost forces the reading "`v` deducts
  exactly the rounded amount and goes on with the remaining bank", which we formalize. Then the claims
  hold: `(2+ε)`-approximation and the same round bounds. Our constant 4 instead of 2 is just what halving
  the vault gives; the paper states no constant for Section 4, so this is not a deviation.
  (`congest_correct`, `congest_small`, `congest_large`)
* **Implicit constants.** "ε = O(1)" is needed: for large ε the `K_v` term of `K_v/ε'` dominates. We
  assume `ε ≤ E` and give explicit constants. Section 5 drops the constant hidden in `Ω`. With it the
  conditions become `2k³+4k ≤ 4ε log n − 4k² log₂ c` and `k(k+1) ≤ 2ε log Δ − 2(k+1) log₂ c`, which
  still force `k = O((log n)^{1/3})` and `k = O(√log Δ)`. (`KMW.first_constraint_k_le`,
  `KMW.second_constraint_k_le`)
* The symmetry of the neighbourhoods `N_i` (needed for lines 18–21 to make sense) is used without
  comment. It holds: a neighbour is dropped at line 16 only when its bank is exhausted, so it returns
  `InCover` in the same iteration. (`actN_step`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous LOCAL model, deterministic, no failures. We use CSLib's locally-iterative (SET-LOCAL)
  model `Cslib.LocallyIterative.Algorithm`: in each round a node maps its state and the *set* of its
  neighbours' states to a new state. States carry identifiers, so a node can address an answer to one
  neighbour (shared identifier API `Cslib/Computability/Distributed/Local/Identifiers.lean`: `pickId`,
  `exists_mem_nbrColors_id`); the state after `t` rounds is a `t`-local function of the initial states
  (`dist_isLocal`). Local input: identifier, weight `w(v) ≥ 0`, degree. Global knowledge: only `ε` and the
  processing order (no `n`, no `Δ`). Graphs are finite simple graphs; all weights and graphs are
  quantified over.
* One iteration of Algorithm 1 is three rounds: answer requests / collect answers and decide / notify.
  Requests `vault(u)/d_i(u)` are read from the neighbour's state.
* The order in which a vertex processes requests (line 17) is arbitrary: every theorem holds for every
  enumeration `ord`. More generally, correctness and running time are proved for any response rule
  meeting a specification (`Rule.Spec σ`). This is how the CONGEST variant is covered.
* The analysis works on a global-state iteration (`Algorithm.lean`). The LOCAL implementation simulates it
  exactly (`run_dist`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 2.1 (local-ratio template; against every vertex cover) | `theorem_2_1` | `LocalRatio.lean` |
| Algorithm 1, line 20 (any order) meets the response spec | `greedyRule`, `greedy_spec` | `Algorithm.lean` |
| Lemma 3.2 (δ is G-valid, `C = S_δ` is a vertex cover, weight ≤ (2+ε)·OPT) | `lemma_3_2`, `isValid_delta`, `alg1_correct` | `Correctness.lean`, `Paper.lean` |
| Lemma 3.3, key step (exact weight drop) | `drop` | `Rounds.lean` |
| Lemma 3.3, counting (`n ≤ K(1−θ)/a + log d/log K` for every `K > 1`) | `count_bound`, `active_bound`, `alg1_active_bound` | `Rounds.lean`, `Paper.lean` |
| Lemma 3.3 (`d ≤ 16`: `(34+2E)/ε` iterations; `d > 16`: `(2+3E) log d/(ε log log d)`) | `lemma_3_3_small`, `lemma_3_3_large` | `Paper.lean` |
| Theorem 3.1 (LOCAL algorithm: termination, (2+ε)-approx., per-vertex round bounds, outputs final) | `theorem_3_1` | `Main.lean` |
| LOCAL implementation simulates the iteration | `run_dist`, `cfg_st`, `dist_frozen` | `Distributed.lean` |
| Section 4 (CONGEST variant: correctness, rounds with constant 4) | `congest_spec`, `congest_correct`, `congest_small`, `congest_large` | `Congest.lean` |
| Section 5 (arithmetic of the [KMW10] discussion) | `KMW.first_constraint_iff`, `KMW.second_constraint_iff`, `KMW.*_k_le` | `KMWDiscussion.lean` |

The headline bound in `Δ` follows from the per-vertex bound in `d(v)`, because `log x/log log x` is increasing
for `x > e^e ≈ 15.2`. This step is not stated in Lean.

**Not formalized.** Message sizes in the CONGEST variant; the claims about anonymous networks and
non-simultaneous start; the claim that [KMW10]'s Theorem 9 depends only on the two constraints analysed
in Section 5 (and hence the abstract's "contradicts the lower bound of [KMW10]").

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: `Finset.toList` is a valid processing order (`isOrdering_toList`), so
`theorem_3_1` applies to every finite graph, every `ε > 0` and all nonnegative weights (`example` in
`Main.lean`). The model is CSLib's `Cslib/Computability/Distributed/Local/LocallyIterative.lean`. Vertex
covers are Mathlib's `SimpleGraph.IsVertexCover`.
