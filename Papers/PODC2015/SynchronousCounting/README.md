# Towards Optimal Synchronous Counting — PODC 2015

Christoph Lenzen, Joel Rybicki, Jukka Suomela. *Towards Optimal Synchronous Counting.* PODC 2015. DOI
[10.1145/2767386.2767423](https://doi.org/10.1145/2767386.2767423). Formalized version: arXiv
[1503.06702](https://arxiv.org/abs/1503.06702) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The resilience-boosting construction (Theorem 1) and the main result
Theorem 3 are verified: `f = n^{1−o(1)}`, `O(f)` stabilisation time, `O(log² f / log log f + log c)`
state bits. Corollaries 1 and 2 are verified for the network sizes the constructions produce (Corollary 1
only for `n = 3f+1`). Theorem 2 is verified with a weaker time constant than claimed. Theorem 1 *as
stated* is false in the boundary case `n = 1`: it would yield a 1-resilient counter on 3 nodes. §4.1 and
Corollary 1 use `n = 1` but avoid the problem by assuming `F < N/3`, so nothing downstream is affected.
For `n ≥ 3` the theorem holds exactly as stated.

## Mistakes in the paper

* **Theorem 1 is false for `n = 1` (false statement in the boundary case `n = 1`; downstream unaffected).** The paper says (§3.4) that
  `F < N/3`, which the phase king needs, "follows from the preconditions of Theorem 1". Take `n = 1`,
  `f = 0`, `k = 3`. The precondition `F < (f+1)⌈k/2⌉ = 2` allows `F = 1` on `N = 3` nodes. The base
  counter exists (one node incrementing its counter), but no 1-resilient counter on 3 nodes exists. We
  prove this impossibility by an FLM-style covering argument on an infinite line of node copies. The
  paper's construction also fails concretely: the Byzantine node echoes each correct node's own
  phase-king register back to it. Every correct node then sees its own value `N − F = 2` times and the
  other correct value only `F = 1` time, so whatever instruction it executes it keeps counting on its own,
  and the two correct counters stay apart forever. For `n ≥ 2` with `f < n/3` the claim `F < N/3` is right,
  and Corollary 1 (which uses `n = 1`) explicitly replaces the hypothesis by `F < N/3`. So nothing
  downstream breaks. (`theorem1_as_stated_false`, `construction_fails`; repaired: `boost`,
  `theorem1_paper`, `theorem1_of_three_le`)
* **Lemma 3 relies on an unproved impossibility (proof gap, statement true for `n ≥ 3`).** The proof
  needs the correct nodes of a non-faulty block to form a strict majority. It justifies `f < n/3` by "as
  otherwise counting cannot be solved". We proved that impossibility for `3 ≤ n ≤ 3f`. So for `n ≥ 3`,
  Theorem 1 holds exactly as stated (`theorem1_of_three_le`). For `n = 2, f ≥ 1` it holds iff no 1-resilient
  counter on two nodes exists; we did not prove that. (`not_isCounter_of_three_le_card`)
* **§4.3 miscomputes `n/f` (statement true).** With the stated `R_p = 2k_p` iterations, `n/f = 2^{8·2^P−6}`,
  not `2^{2(2^P−1)}`. The paper's value corresponds to `R_p = 2·2^{P−p}` and drops a factor 4. Still
  `log(n/f) = Θ(k_1)`, so `f = n^{1−O(1/log log f)}` survives. (`thm3N`, `theorem3_asymptotic`)
* **Theorem 2's time bound is not established (proof gap).** The proof uses a per-step cost `h^k`, but
  Theorem 1 gives `(2m)^k = k^k`. So the proof does not establish the claimed `O(2^{2^{1/ε}} f)`. We prove
  the weaker bound `2^{2^{O(1/ε)}} f` and do not know whether the claimed one holds. Corollary 2 (constant
  `ε`) is unaffected. (`theorem2`, `corollary2`)
* **Imprecise statements.** Corollary 1 is stated for every `n > 3f` but proved only for `n = 3f+1`.
  Theorems 2 and 3 produce counters only for special network sizes. The bit count
  `S(B) = S(A) + ⌈log(C+1)⌉ + 1` is an upper bound, not an equality. The instruction `min{j : z_j > F}` does
  not define the empty case (we use `∞`).
* **Typos:** `c_k` for `c_{k−1}` (Lemmas 2–3, §3.5); `u + (β−1)c_{i−1}` for `u + βc_{i−1}` (Lemma 1);
  "Checking `I₃ℓ₊₂`" for `I₃ℓ₊₁` (Lemma 4); `mod c` for `mod C` (Lemma 5); `π_F(x) = d` for `π_F(x) = e`
  (§2); "fewer than `f`" for "at most `f`" faulty nodes (§3.1); `(3f+2)(2m)^k` for `3(f+2)(2m)^k`
  (Corollary 1).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Cslib/Computability/Distributed/Byzantine/SyncCounting/Model.lean`, shared).
* Complete network of nodes `V`, synchronous lock-step rounds. A deterministic algorithm is
  `(X, g, h)`. Each round, every node broadcasts its whole state and moves to `g i m`, where `m` is the
  received state vector. Its output is `h i s ∈ Fin c`.
* Static Byzantine set `F`. A Byzantine node may send arbitrary, different states to different nodes.
  **Arbitrary initial states**: an execution is any sequence `x : ℕ → V → X` such that every correct node's
  next state is `g i m` for some `m` that agrees with the current states on the correct nodes (`IsExec`).
* `IsCounter A f T`: every execution with `|F| ≤ f` stabilises within `T` rounds. That is, there is a `v`
  such that every correct node outputs `(v + r) mod c` in round `T + r`. `Achievable n f c T S`: such a
  counter on `Fin n` exists with a nonempty state set of size `≤ 2^S` (`≤ S` state bits). Nonemptiness
  excludes the vacuous empty-state "counter".
* The construction `B` (`Construction.lean`) is exactly the paper's: the base counter runs per block,
  then come majority votes for the leader block and its round counter, then the phase-king instruction set
  `I_R` (Table 2) on registers `a ∈ [C] ∪ {∞}` and `d ∈ {0,1}`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1, Lemma 2 (arithmetic cores) | `lemma1`, `lemma2`, `ptr_eq` | `Pointers.lean` |
| Lemma 3 (voting) | `Rval_eq` (+ window inside `theorem1`) | `Construction.lean`, `Theorem1.lean` |
| Lemma 4, Lemma 5 (phase king) | `lemma4`, `lemma5`, `lemma5_step` | `PhaseKing.lean` |
| Theorem 1, for the construction (`2f < n`, `3F < kn`) | `theorem1` | `Theorem1.lean` |
| Theorem 1, time and space (`Achievable`) | `boost`, `theorem1_paper` (`f < n/3`, `n ≥ 2`) | `Boost.lean` |
| Theorem 1 exactly as stated, `n ≥ 3` | `theorem1_of_three_le` | `Counterexample.lean` |
| Theorem 1 as stated: **false** for `n = 1` | `theorem1_as_stated_false`, `construction_fails` | `Counterexample.lean` |
| Impossibility `3 ≤ n ≤ 3f` (used by the paper, cited) | `not_isCounter_of_three_le_card`, `not_isCounter_of_card_eq_three` | `Cslib/Computability/Distributed/Byzantine/SyncCounting/Impossibility.lean` |
| §4.1 base case, Corollary 1 | `achievable_one`, `corollary1`, `corollary1_bounds` | `Recursive.lean` |
| Theorem 2, Corollary 2 | `theorem2`, `corollary2` | `Recursive.lean` |
| Theorem 3, Lemmas 6–7 | `theorem3` (explicit), `theorem3_asymptotic` | `Recursive.lean` |

`theorem3`: for `P ≥ 1` phases there is a `C`-counter on `n = 2^{8·2^P−6} f` nodes with resilience
`f = 2^{(P−1)2^{P+3}+8}`, time `≤ 2^33 f` and `≤ 128·4^P(P+1) + ⌈log₂(C+1)⌉ + 13` bits.
`theorem3_asymptotic` restates this as `T ≤ K f`, `S ≤ K log² f / log log f + log C + K`,
`log n ≤ log f + K log f / log log f`, for arbitrarily large `f`.

**Not formalized.** Section 5 (randomised sampling in the pulling model: Theorem 4, Lemmas 8–9,
Corollaries 3–5), and counters for network sizes other than the special ones produced by the constructions.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The hypotheses are satisfiable: Section 4 instantiates Theorem 1 repeatedly, starting from the trivial
one-node counter. The model and the impossibility theorem are in CSLib,
`Cslib/Computability/Distributed/Byzantine/SyncCounting/`. No external result is assumed: the `n ≤ 3f` impossibility, which the paper only
cites, is proved here.

**Shared infrastructure.** Vote counts `cnt`, `cntA` are `Finset.countEq` (`Cslib/Foundations/Data/Finset/Quorum.lean`);
the computable majority vote `maj` is the library selector `Finset.majority?` (`maj_eq_majority?`);
the king round of Lemma 4 is the generic phase-king lemma `Cslib.Byzantine.kingPhase_agreement`
(`Cslib/Computability/Distributed/Byzantine/KingPhase.lean`, with `keep = +1 mod C` and `adopt = min {C, ·} + 1 mod C`).
