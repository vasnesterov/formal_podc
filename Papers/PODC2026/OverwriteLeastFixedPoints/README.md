# Least Fixed Points with Overwrite Semantics — PODC 2026

Vijay K. Garg, Rohan Garg. *Brief Announcement: Computing Least Fixed Points with Overwrite Semantics in
Parallel and Distributed Systems.* PODC 2026. DOI
[10.1145/3796701.3815932](https://doi.org/10.1145/3796701.3815932). Formalized version: the brief
announcement (numbering: Theorems 2.1, 3.1, 4.1, Lemma 3.2), plus the full version arXiv
[2602.10486](https://arxiv.org/abs/2602.10486) v1 for proofs, Theorem 2, Corollaries 4.1/4.2 and Section 6.

**Verdict: ⚠️ Weakened.** The three convergence theorems (interleaving, parallel with update-only-on-change, distributed
with bounded staleness) hold and are formalized after local proof repairs, and so are Theorem 2's necessity examples;
strong fairness is not needed in Theorem 4.1: plain fairness is enough. Two applications in the full version's
Section 6, for stable marriage and shortest paths, which the abstract advertises, do not satisfy the theorems'
hypotheses: Algorithm 5 (lock-free
Gale–Shapley) is not monotone, although the paper says it is, and Algorithm 7 (Bellman–Ford with levels) has no common
fixed point at all. Nothing we proved replaces their conclusions, and the other shortest-path algorithms were not
checked.

## Mistakes in the paper

### ❌ Full version §6.1 ("Algorithm 5 is inflationary and monotone")
Algorithm 5 (lock-free Gale–Shapley) is not monotone: with two men who both rank `w₀` first, `G = (1,1) ≤ H = (1,2)`
but `f₀(G) = (2,1) ≰ (1,2) = f₀(H)` (`Apps.alg5_not_monotone`).

**Impact.** The derivations "from Theorem 3 / Theorem 4 it follows that Algorithm 5 yields the man-optimal stable
marriage" are invalid, and no replacement is proved, but the conclusion itself seems true.

**Details.** Let both men rank `w₀` first and `w₁` second, and let `w₀` prefer `m₁`. In `G = (1,1)` both propose
to `w₀`; in `H = (1,2)` `m₁` has moved on to `w₁`. Then `f₀(G) = (2,1)`: `m₀` is rejected because `m₁` is at `w₀`.
But `f₀(H) = (1,2)`, because nobody `w₀` prefers is at `w₀`. The test "`mpref[j][G[j]] = w`" looks at where `j`
proposes *now*, which is not monotone in `G[j]`. A monotone test would ask whether `j` has *ever* proposed to `w`.

We model-checked an over-approximation that covers the interleaving, parallel and stale-view executions:
exhaustively for `n ≤ 3`, and for 300 random profiles with `n = 4`. Every reachable common fixed point was the
man-optimal matching (`scripts/alg5_modelcheck.py`). That is evidence, not a proof.

### ❌ Full version §6.2 (Algorithm 7, Bellman–Ford with levels, as an instance of Corollary 4.2)
Algorithm 7 has no common fixed point at all, whatever the weights and the relaxation rule, and its functions are
not monotone (`Apps.alg7_no_common_fixed_point`, `Apps.alg7_not_monotone`).

**Impact.** "From Corollary 4.2, it follows that Algorithm 7 converges to the cost of the shortest paths" has no
basis. The distance components may still converge; we did not check.

**Details.** Its `fᵢ` increments `G[i].level` whenever no vertex lags behind `i`. So the vertex of minimal level
always changes, and **no state is a common fixed point**. The level component is unbounded, so the lattice is not
finite either. Non-monotonicity: take one edge `0 → 1` of weight 1, `G = ((0,1),(5,1)) ⊑ H = ((0,1),(5,2))`.
Vertex 1 relaxes in `G` to distance 1, but in `H` it waits for vertex 0 and keeps distance 5.

### 🔧 §2, before Theorem 2.1 ("the fixed points of each `fᵢ` form a sublattice")
The fixed points of one `fᵢ` are not closed under joins: `f x = if (1,1) ≤ x then (2,2) else x` on `{0,1,2}²` is
monotone and inflationary and fixes `(1,0)` and `(0,1)` but not `(1,1)` (`fixedPoints_not_supClosed`).

**Impact.** The paper's use survives: these fixed points are closed under meets and contain `⊤`, which is
enough for the least common fixed point to exist (`isCommonFixed_inf`).

### ✏️ Slips
- Theorem 3.1 on a proper sublattice (the parallel model): the brief announcement states the theorem for "a finite
  distributive lattice of vectors", but on a proper sublattice the coordinatewise last-writer-wins commit can leave `L`
  (`sublattice_round_escapes`). In the distributive sublattice `{000, 010, 110, 021, 121}` of `{0,1,2}³` (for instance
  a lattice of consistent cuts would be such an `L`), take `f_A = · ⊔ 110` and `f_B = · ⊔ 021`. One round from `000`
  can commit `111 ∉ L`. The full version's reading "for simplicity, each `G[i]` is between 0 and m" (the whole box
  `{0,…,m}ⁿ`) is what the proof uses, and the theorem holds for it; distributivity is never used. Theorem 4.1 is
  different: with `i`-local functions its commit is a join of admissible states, so it does stay inside any join-closed
  `L` (`distCommit_mem`).
- Algorithm 10 (fair division): `G[i] + maxEnvy` can exceed `mΔ`, so `fᵢ` does not map `{0,…,mΔ}ⁿ` into itself.
  Example: 2 agents, 1 item valued 1 by both, `G = (1,1)` gives `G[1] = 2`. Capping the update fixes this.
  (`Apps.alg10_out_of_range`)
- §2.1 starts the transitive-closure computation from `R₀ ≠ ⊥`. Theorem 2.1 needs the version "converges to the
  least common fixed point above `G₀`", which the paper only mentions in Theorem 2's proof. Proved here as
  `converges_from`.
- Corollaries 4.1 and 4.2 say "`fᵢ : L′ → L′` monotone and deflationary". They mean deflationary on `L`, that is,
  inflationary on `L′`.

## Proof gaps (statements true)

### 🔧 Theorem 3.1 (parallel convergence, fixed-point step)
The proof says "the update rule gives `G_{t+1}[j] > G_t[j]`" but never argues that process `i` actually reads
`G*`.

**Impact.** Statement true; repaired (`theorem_3_1`).

**Repair.** A round that changes nothing has no writes at all (Lemma 3.2(3)), so every read returns the committed
value.

### 🔧 Theorem 3.1 (parallel convergence, leastness step)
The proof's "all writes in round `t` are `≤ Y` and so `X ≤ Y`" is circular as stated, since the writes depend on what
was read in the same round.

**Impact.** Statement true; repaired (`RoundExec.commit_le`, `theorem_3_1`).

**Repair.** Strong induction on the causal order of reads, a causality already implied by the paper's real-time model.

### 🔧 Theorem 4.1 (distributed convergence, fixed-point step)
The proof picks a round `t ≤ U + τ` in which `i` is active and concludes that its view equals `G*`, which needs
`t ≥ U + T`.

**Impact.** Statement true; repaired, and then **strong fairness is unnecessary**: plain fairness suffices
(`theorem_4_1_fair`).

**Repair.** Take a round after `U + T`, so that every coordinate of the view dates from after stabilization. Any
round `t ≥ U + T` with `i ∈ S_t` works.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Deterministic functions, no failures, no randomness. The schedule is arbitrary, subject to fairness:
  every index infinitely often. Strong fairness (`StronglyFair τ`, Definition 6) is also defined.
* *Interleaving* (§2): `G (t+1) = f (σ t) (G t)` on any finite poset with `⊥`. The general-start
  version works on any poset without infinite ascending chains.
* *Parallel* (§3): states are `(k : κ) → β k`, a finite product of finite posets (the paper:
  `{0,…,m}ⁿ`). A round (`RoundExec`) is given by each active process's read vector and the instant
  its reads end. A read returns the committed value or the value of any write, in this round, by a
  process whose reads ended earlier. This causality is implied by the paper's real-time description;
  without it, values can appear out of thin air (`acausal_round_breaks_leastness`). A process writes
  exactly the coordinates whose computed value differs from the read one (update-only-on-change), and
  every written coordinate commits the value of *some* write. This allows every read and commit
  behaviour the paper allows, and more. The naive rule (write everything) is the same structure with
  another write policy.
* *Distributed* (§4): process `i` owns coordinate `i`. The view `V t i` has the current own
  coordinate, and every other coordinate is `G s j` for some `t − T ≤ s ≤ t` (bounded staleness). The
  commit is `G (t+1) i = f i (V t i) i` for active `i`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 2.1 (Thm 1): interleaving convergence | `theorem_2_1` (general start: `converges_from`) | `Interleaving.lean` |
| Thm 2: necessity of each assumption | `theorem_2_finite`, `theorem_2_fair`, `theorem_2_bot`, `theorem_2_monotone`, `theorem_2_inflationary` | `Interleaving.lean` |
| "fixed points form a sublattice": false | `fixedPoints_not_supClosed` (meet-closure: `isCommonFixed_inf`) | `Interleaving.lean`, `Basic.lean` |
| Cor 4.1 (greatest fixed points, interleaving) | `corollary_4_1` | `Interleaving.lean` |
| §3 naive-write example | `naive_round_stuck` | `Parallel.lean` |
| Lemma 3.2 (1)–(3) | `RoundExec.lt_write`, `RoundExec.le_commit`, `RoundExec.commit_eq_iff` | `Parallel.lean` |
| Thm 3.1 (Thm 3): parallel convergence | `theorem_3_1` (general start: `parallel_converges_from`) | `Parallel.lean` |
| Thm 3.1 on a proper sublattice | `sublattice_round_escapes` | `Parallel.lean` |
| Cor 4.2 (parallel) | `corollary_4_2_parallel` | `Parallel.lean` |
| §4 unbounded-staleness example | `unbounded_staleness_cex` | `Distributed.lean` |
| Thm 4.1 (Thm 4): distributed convergence | `theorem_4_1`; with plain fairness `theorem_4_1_fair` | `Distributed.lean` |
| Cor 4.2 (distributed) | `corollary_4_2_distributed` | `Distributed.lean` |
| §2.1/3.1/4.1 transitive closure (Alg. 1, 3) | `TC.isLeast_rtc`, `TC.tc_interleaving`, `TC.tc_parallel`, `TC.tc_distributed` | `TransitiveClosure.lean` |
| §3.1 round bound: paths of length `2^t` after `t` rounds; closure once `n − 1 ≤ 2^t` | `TC.tc_parallel_rounds` | `TransitiveClosure.lean` |
| Alg. 5 is monotone: false | `Apps.alg5_not_monotone` | `Applications.lean` |
| Alg. 7 satisfies Cor 4.2: false | `Apps.alg7_no_common_fixed_point`, `Apps.alg7_not_monotone` | `Applications.lean` |
| Alg. 10 maps `L` to `L`: false | `Apps.alg10_out_of_range` | `Applications.lean` |

Lemma 3.2(1): the full version says `≥ G_t[j]` and the brief announcement says `>`. Both hold.

**Not formalized.** Algorithm 2 (CAS counting), Algorithm 4, the correctness of Algorithms 5, 6, 8, 9
and 10 (shortest paths, Floyd–Warshall, Johnson, subsidies), Table 2's informal necessity claims for `i`-locality and
product lattice, and the termination-detection remark. In Algorithms 6 and 8 the rule "`∃k` … `G[i] ← G[k] + w[k,i]`" is
ambiguous (not monotone with the first witness, monotone with the minimum), and Algorithm 6's initialization
`G[1] = w[1,1]` was noted only.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: every state and active set admits a round (`exists_parRound`), and an atomic
step is a round (`parRound_single`). The transitive-closure family satisfies all hypotheses of the three
theorems. Self-contained on Mathlib's order theory; no CSLib model was needed.
