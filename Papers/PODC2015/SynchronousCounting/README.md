# Towards Optimal Synchronous Counting — PODC 2015

Christoph Lenzen, Joel Rybicki, Jukka Suomela. *Towards Optimal Synchronous Counting.* PODC 2015. DOI
[10.1145/2767386.2767423](https://doi.org/10.1145/2767386.2767423). Formalized version: arXiv
[1503.06702](https://arxiv.org/abs/1503.06702) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** The resilience-boosting construction (Theorem 1) and the main result Theorem 3 are verified:
`f = n^{1−o(1)}`, `O(f)` stabilisation time, `O(log² f / log log f + log c)` state bits, with only constants corrected
in §4.3; Corollaries 1 and 2 are verified for the network sizes the constructions produce (Corollary 1 only for
`n = 3f+1`). The one loss is the time constant of Theorem 2, verified only in the weaker form `2^{2^{O(1/ε)}} f`, and
neither Corollary 2 nor Theorem 3 depends on it. Section 5 (the pulling model) was not checked.

## Mistakes in the paper

### ⚠️ Theorem 2 (time bound unestablished)
The proof of Theorem 2 uses a per-step cost `h^k`, but Theorem 1 gives `(2m)^k = k^k`, so the claimed
`O(2^{2^{1/ε}} f)` time is not established (`theorem2`).

**Impact.** We prove the weaker bound `2^{2^{O(1/ε)}} f` and do not know whether the claimed one holds.
Corollary 2 (constant `ε`) is unaffected (`corollary2`).

### ✏️ Slips
- Theorem 1 for `n = 1`: with `f = 0`, `k = 3` its precondition `F < (f+1)⌈k/2⌉ = 2` allows `F = 1` on `N = 3` nodes,
  but no 1-resilient counter on 3 nodes exists (`theorem1_as_stated_false`, `construction_fails`). So `F < N/3`, which
  the phase king needs, does not "follow from the preconditions of Theorem 1" (§3.4) here. The base counter exists
  (one node incrementing its counter). We prove the impossibility by an FLM-style covering argument on an infinite
  line of node copies. The paper's construction also fails concretely: the Byzantine node echoes each correct node's
  own phase-king register back to it. Every correct node then sees its own value `N − F = 2` times and the other
  correct value only `F = 1` time, so whatever instruction it executes it keeps counting on its own, and the two
  correct counters stay apart forever. Nothing downstream breaks: for `n ≥ 2` with `f < n/3` the claim `F < N/3` is
  right, §4.1 and Corollary 1 use `n = 1` but explicitly replace the hypothesis by `F < N/3`, and for `n ≥ 3` the
  theorem holds exactly as stated (`boost`, `theorem1_paper`, `theorem1_of_three_le`).
- The bit count `S(B) = S(A) + ⌈log(C+1)⌉ + 1` is an upper bound, not an equality.
- The instruction `min{j : z_j > F}` does not define the empty case (we use `∞`).
- §3.3 defines majority for vectors of length `kn` with threshold `kn/2`, but uses it for vectors of length `n` and
  `k`.
- `c_k` for `c_{k−1}` (Lemmas 2–3, §3.5); `u + (β−1)c_{i−1}` for `u + βc_{i−1}` (Lemma 1); `mod c` for `mod C`
  (Lemma 5); `π_F(x) = d` for `π_F(x) = e` (§2); "fewer than `f`" for "at most `f`" faulty nodes (§3.1); `(3f+2)(2m)^k`
  for `3(f+2)(2m)^k` (Corollary 1).

### Typos
- "Checking `I₃ℓ₊₂`" for `I₃ℓ₊₁` and "some any non-faulty node" (proof of Lemma 4).
- Corollary 1 is stated for every `n > 3f` but proved only for `n = 3f+1`. Theorems 2 and 3 produce counters only for
  special network sizes.

## Proof gaps (statements true)

### 🔧 §4.3 (computation of `n/f`)
With the stated `R_p = 2k_p` iterations, `n/f = 2^{8·2^P−6}`, not `2^{2(2^P−1)}`; the paper's value
corresponds to `R_p = 2·2^{P−p}` and drops a factor 4.

**Impact.** Statement true: still `log(n/f) = Θ(k_1)`, so `f = n^{1−O(1/log log f)}` survives (`thm3N`,
`theorem3_asymptotic`).

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
Also open: the proof of Lemma 3 needs the correct nodes of a non-faulty block to form a strict majority, and justifies
`f < n/3` only by "as otherwise counting cannot be solved", pointing at the cited lower bounds. We proved that
impossibility for `3 ≤ n ≤ 3f` (`not_isCounter_of_three_le_card`), so Theorem 1 holds exactly as stated for `n ≥ 3`
(`theorem1_of_three_le`). For `n = 2, f ≥ 1` it holds iff no 1-resilient counter on two nodes exists; we did not prove
that.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The hypotheses are satisfiable: Section 4 instantiates Theorem 1 repeatedly, starting from the trivial
one-node counter. The model and the impossibility theorem are in CSLib,
`Cslib/Computability/Distributed/Byzantine/SyncCounting/`. No external result is assumed: the `n ≤ 3f` impossibility, which the paper only
cites, is proved here.

**Shared infrastructure.** Vote counts `cnt`, `cntA` are `Finset.countEq` (`Cslib/Foundations/Data/Finset/Quorum.lean`);
the computable majority vote `maj` is the library selector `Finset.majority?` (`maj_eq_majority?`);
the king round of Lemma 4 is the generic phase-king lemma `Cslib.Byzantine.kingPhase_agreement`
(`Cslib/Computability/Distributed/Byzantine/KingPhase.lean`, with `keep = +1 mod C` and `adopt = min {C, ·} + 1 mod C`).
