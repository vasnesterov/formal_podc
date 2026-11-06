# Partially Replicated Causally Consistent Shared Memory — PODC 2018

Zhuolun Xiang, Nitin H. Vaidya. *Brief Announcement: Partially Replicated Causally Consistent
Shared Memory.* PODC 2018. DOI [10.1145/3212734.3212790](https://doi.org/10.1145/3212734.3212790).
Formalized version: arXiv [1703.05424](https://arxiv.org/abs/1703.05424) v3 (full version, *…: Lower
Bounds and An Algorithm*); numbering follows it.

**Verdict: 🛠️ Hard fix.** The paper's necessary and sufficient condition survives: the edge-indexed timestamp
algorithm achieves replica-centric causal consistency (Theorem 3), and tracking every edge of the timestamp graph is
necessary (Theorem 1). Both take new arguments: Lemma 4, on which the correctness proof rests, is false (also in its
only well-typed reading), and the executions in the proof of Theorem 1 had to be redesigned. Footnote 2's claim that
the algorithm satisfies Constraint 1 of the lower-bound section is also false, but it is a side remark nothing is
derived from, and the paper's third contribution, the timestamp-size lower bound, was not checked.

## Mistakes in the paper

### ❌ Footnote 2 (the algorithm satisfies Constraint 1)
Footnote 2's claim that the algorithm's timestamp is a function of the causal past (a *set* of updates) is false: on six replicas, two executions give replica `0` the same causal past but different `τ₀[e_25]` (`Footnote2.footnote_2_false`).

**Impact.** The lower bound of Section 4 (which assumes Constraint 1) does not apply to the paper's
algorithm in general. Nothing is proved in place of the footnote.

**Details.** Take six replicas with `X₀ = {e,b}`, `X₁ = {a,b}`, `X₂ = {a,c}`, `X₃ = {c,d}`,
`X₄ = {e,d}`, `X₅ = {c,e,d}`. Replicas `2, 3, 4, 5` write once each. In both executions replica `0`
ends up with the same causal past (all four updates). In one, `2`'s update reaches `0` through `5`,
which tracks `e_25`; in the other, only through `4`, which does not. So `τ₀[e_25]` is `1` vs. `0`.

### 🛠️ Lemma 4 (Appendix B, timestamps along causal chains), and with it the proofs of Lemma 5 and Theorem 3
Lemma 4 (if `u'` from `k` to `i` with timestamp `T'` happened before `u` from `j` to `i` with timestamp `T`, then `T[e_ki] ≥ T'[e_ki]`) is false even when `e_ki ∈ E_j`, its only well-typed reading, on five replicas (`Lemma4.lemma_4_false`, `Lemma4.not_lemma4Statement`).

**Impact.** The correctness proof of Theorem 3 rests on it, through Lemma 5, but Theorem 3 is true: we prove it by a
new argument (`chain_main`, `lemma_5`, `theorem_3_safety`). Safety is not violated in the counterexample.

**Details.** When `e_ki ∉ E_j`, `T` has no such entry, and the proof of Lemma 5 nevertheless
applies the lemma there. Even when `e_ki ∈ E_j` it fails. Take five replicas with
`X_A = {f,e,b}`, `X_B = {e,a}`, `X_C = {a,g}`, `X_D = {g,b}`, `X_I = {f,a,g}`. `A` writes `f`
(`u'`, delayed on its way to `I`), then `e`. `B` applies `e` and writes `a`; `C` applies that and
writes `g`; `D` applies that and writes `g` (`u`). Then `u' ↪ u` and `e_AI ∈ E_D` (triangle
`D, I, A`). But `e_AI ∉ E_C` (`X_C ⊆ X_I`, so condition (iii) fails on every loop through `C`), so
`C` drops the information and `T[e_AI] = 0 < 1 = T'[e_AI]`. Safety is not violated: `B`'s and
`C`'s updates also go to `I` and must be applied first. The lemma's proof also assumes that causal
chains form simple loops.

**Repair.** We replace it by a strong induction on the length of a causal chain
`a ↪ v₀ ↪ ⋯ ↪ v_m = u`. If a replica repeats, or an intermediate update also goes to the receiver
`i`, the chain gets shorter (the latter by safety of earlier steps). Otherwise, either every replica
on the chain tracks `e_ji` and the counter reaches `u`'s timestamp, or the chain closes with `i`
into a simple loop that is not a `(p_q, e_ji)`-loop. Each of the three failing conditions of
Definition 6 then exhibits an update sent directly further down the chain, which again shortens it.

## Proof gaps (statements true)

### 🛠️ Theorem 1 (necessity of tracking every timestamp-graph edge)
In Case 2 applying `u₁` also brings `j`'s whole causal past into `i`'s graph, so the two graphs differ in more than updates on `e_ji`, and Case 3 delays all other messages "indefinitely", which breaks its liveness arguments.

**Impact.** The statement holds for every deterministic metadata algorithm and every quiescent state `R₀`
(`Necessity.theorem_1`), with redesigned executions.

**Details.** Also, in Case 3 an earlier update on the path `l₁ … l_s` may already reach `k`, and in
Case 3.2 the execution without `u₀` loses `j`'s causal past.

**Repair.** Both executions share a first update `u_A` of `j`, which `k` applies, and one execution
adds a second update `u_B`. Every relay applies all updates sent to it (liveness forces this). The
critical message is the first path update stored at `k`. The two executions are compared by an
explicit simulation.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Peer-to-peer architecture with `R` replicas (`ι`), registers `Reg`, and replica `i` storing `X i`.
  Asynchronous, reliable, non-FIFO channels, no failures, deterministic replicas. The scheduler
  (delivery order, delays, client writes) is adversarial. Liveness is under weak fairness: an update
  that stays applicable is eventually applied.
* "Receive" is merged into "apply": an update can be applied at any time after it was issued, if
  the predicate of Step 4 holds. Values and reads are omitted (irrelevant to Definition 5).
* `↪` (Definition 4) is defined through a ghost set `pre` per update: the updates applied at the
  issuer before it was issued.
* Theorem 1 quantifies over *all deterministic metadata algorithms* (`Necessity.Alg`). A replica
  keeps metadata, attaches it to its updates, and decides when to apply a received update from its
  metadata, the sender, the register and the attached metadata only (Section 2). The decision may
  see sender and register, which enlarges the class. The class assumes deterministic replicas
  whose metadata changes only when they write or apply an update (not on receipt). The paper's
  model (Section 2) does not discuss other algorithms, and its proofs assume this.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definitions 1, 6, 7 (share graph, `(i,e_jk)`-loop, timestamp graph) | `Adj`, `IsLoop`, `TsEdge` | `Model.lean` |
| Algorithm of Section 3.2 | `Step`, `Ready`, `incr`, `merge` | `Model.lean` |
| Lemma 3 | `lemma_3` | `Theorem3.lean` |
| Lemma 4: **false** | `Lemma4.lemma_4_false`, `Lemma4.not_lemma4Statement` | `Lemma4.lean` |
| Lemma 5 (new proof) | `lemma_5` (core: `deps_applied`, `chain_main`) | `Theorem3.lean`, `Chain.lean` |
| Theorem 3, safety | `theorem_3_safety` | `Theorem3.lean` |
| Theorem 3, liveness | `theorem_3_liveness`, `eventually_applied` | `Theorem3.lean` |
| Theorem 1 (necessity; all deterministic metadata algorithms, quiescent `R₀`) | `Necessity.theorem_1` (cases: `Necessity/Cases.lean`, `Necessity/Case3.lean`) | `Necessity/Theorem1.lean` |
| "necessary and sufficient": the algorithm is in the class of Theorem 1 and implements causal consistency | `Necessity.paperAlg_implements` | `Necessity/Bridge.lean` |
| Footnote 2 (algorithm satisfies Constraint 1): **false** | `Footnote2.footnote_2_false` | `Footnote2.lean` |

**Not formalized.** Lemma 2 / Theorem 2 (lower bound `σ_i(m) ≥ χ(H_i)`: "possible causal pasts"
and the spanning-tree executions of Appendix D are too informal to pin down, not found broken), the closed-form
"Implication" bullets and the tightness claims for trees, cycles and full replication, Section 3.3, Appendices C, E, F (client–server architecture).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: the counterexamples are reachable states of the algorithm. The
hypothesis of Theorem 1 is satisfied by the paper's algorithm (`paperAlg_implements`). Random
testing scripts used to find the counterexamples are in [`modelcheck/`](modelcheck/) (not part of the
Lean development). The model is self-contained (Mathlib only). CSLib candidate: `Necessity.T1.exists_path` (a `ReflTransGen` path as a function `ℕ → α`, `Necessity/Frozen.lean`).
