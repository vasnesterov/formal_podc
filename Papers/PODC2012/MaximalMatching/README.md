# Distributed Maximal Matching: Greedy is Optimal — PODC 2012

Juho Hirvonen, Jukka Suomela. *Distributed Maximal Matching: Greedy is Optimal.* PODC 2012. DOI
[10.1145/2332432.2332464](https://doi.org/10.1145/2332432.2332464). Formalized version: arXiv
[1110.0367](https://arxiv.org/abs/1110.0367) v1 (the only version); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** On anonymous `k`-edge-coloured graphs, maximal matching needs exactly
`k - 1` deterministic rounds; the greedy algorithm is optimal (Lemma 1, Theorem 2). For `k ≥ 3` the
lower bound holds already on `(k-1)`-regular graphs (Theorem 6), which gives `Ω(Δ)` (Corollary 3).
All of this is proved. The template / extension / critical-pair argument of §3 goes through as
written. We also extend the lower bound from the paper's formal model, which uses infinite trees,
to finite simple graphs.

## Mistakes in the paper

There are no substantive mistakes.

* **Finite graphs: minor proof gap, statement true.** Theorem 2 and Corollary 3 talk about
  `k`-edge-coloured *graphs*, but the formal model (§2.3) only has colour systems. These are
  edge-coloured trees, and the trees built in the proof (realisations, and the final `U`, `V`) are
  infinite. For finite graphs one more step is needed: every finite ball of a `d`-regular colour
  system must appear as the view of a node in a finite, simple, `d`-regular, `k`-edge-coloured
  graph. The paper does not give this step. We add it with a `2^k`-copies construction, so all
  lower bounds hold for finite simple graphs. (`completion`, `findsMaximalMatching_of_finite`,
  `theorem2_lower_messagePassing`, `theorem6_messagePassing`)
* **Typo.** The proof of Lemma 8 says "`w ∈ ȳY`"; it should be "`w ∈ ȳX`".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **View model (§2.3, used in the proofs).** `G_k` is the free product of `k` copies of `ℤ/2`,
  implemented as reduced words (`FreeCox k`). A colour system is a prefix-closed `V ⊆ G_k`, i.e.
  a `k`-edge-coloured tree, possibly infinite. An algorithm is any function
  `A : Set G_k → G_k → Option (Fin k)`; `none` means unmatched, `some c` means matched along
  colour `c`. It has running time `r` if `(ūU)[r+1] = (v̄V)[r+1]` implies `A U u = A V v`.
  Correctness is (M1)–(M3). The model is deterministic and anonymous; local computation and
  message size are unbounded.
* **Message-passing model (§1.2).** A `k`-edge-coloured network is a `ColouredGraph k α`: each
  colour class is a partial involution, and `IsSimple` means a simple graph with a proper edge
  colouring. Nodes may be finite or infinite in number, and cycles are allowed. A node starts
  knowing its incident colours. In each synchronous round it sends one message per colour, then
  receives and updates. It outputs after `r` rounds.
* **Equivalence.** We prove that the two models are equivalent (`state_eq_of_view`,
  `hasRunningTime_toAlgorithm`, `out_ofView`, `isMaximalMatching_view`). The lower bound needs
  correctness only on finite simple (regular) networks. The upper bound holds on all networks (on non-simple networks the maximal-matching spec lets a node be matched along a half-loop, so its usual meaning is for simple graphs).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (greedy, `k-1` rounds) | `lemma1`, `lemma1_messagePassing` | `Greedy.lean`, `Main.lean` |
| Theorem 2 (`k-1` is optimal) | `theorem2`, `theorem2_lower`, `theorem2_messagePassing` | `Greedy.lean`, `LowerBound.lean`, `Main.lean` |
| Corollary 3 (`Ω(Δ)`) | `corollary3`, `corollary3_messagePassing` | `LowerBound.lean`, `Main.lean` |
| Lemma 4 | `IsColourSystem.inv_smul`, `colours_inv_smul` | `Cslib/Computability/Distributed/ColourSystem/Basic.lean` |
| Lemma 5 (`k ≤ 2`) | `lemma5` | `LowerBound.lean` |
| Theorem 6 | `theorem6`, `le_runningTime`, `theorem6_messagePassing` | `LowerBound.lean`, `Main.lean` |
| Lemma 7 | `Template.isTemplate_extend`, `Template.isRegular_real` | `Templates.lean` |
| Lemma 8 | `ColouredGraph.view_inv_smul`, `Template.extend_symm` | `Cslib/Computability/Distributed/ColourSystem/Graph.lean`, `Templates.lean` |
| Corollary 10 | `Good.apply_real` | `Outputs.lean` |
| Corollary 11 | `Template.real_extend`, `Good.out_extend` | `Templates.lean`, `InductiveStep.lean` |
| Lemma 12 | `Good.out_ne_none` | `Outputs.lean` |
| Lemma 13 | `lemma13` | `BaseCase.lean` |
| Lemma 14 (base case) | `exists_critical_one` | `BaseCase.lean` |
| §3.9 observations (a)–(h) | `stepHyp_of_critical` | `InductiveStep.lean` |
| §3.9 observations (a), (d), (e) for `X` | `isTemplate_glue`, `compatible_glue_left`, `compatible_glue_right` | `Glue.lean` |
| Lemma 15 (parity argument) | `lemma15` | `InductiveStep.lean` |
| Lemma 16 / induction | `exists_critical_succ`, `exists_critical` | `InductiveStep.lean` |

**Not formalized.** Lemma 9 (commutation of extensions); Corollary 11 is proved directly instead.
Also not formalized: the cited `O(Δ + log* k)` and `Ω(log* k)` bounds, and the informal remarks of
§1.3–1.4 (port-numbering and broadcast models, the trivial case `d = k`, greedy's small messages).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The hypotheses of Theorem 6 are satisfiable: greedy satisfies them (`good_greedy`).
In the message-passing model, `lemma1_messagePassing` gives an algorithm that is correct on all
networks. The reusable infrastructure is in CSLib (`Cslib/Computability/Distributed/ColourSystem/`):
the free Coxeter group, colour systems, coloured graphs and their views (universal covers), the
view-based and message-passing models with bridges between them, and finite completions.
