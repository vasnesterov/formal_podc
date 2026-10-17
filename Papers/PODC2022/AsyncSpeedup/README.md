# Asynchronous Speedup Theorem — PODC 2022

Pierre Fraigniaud, Ami Paz, Sergio Rajsbaum. *A Speedup Theorem for Asynchronous Computation with
Applications to Consensus and Approximate Agreement.* PODC 2022. DOI
[10.1145/3519270.3538422](https://doi.org/10.1145/3519270.3538422). Formalized version: arXiv
[2206.05356](https://arxiv.org/abs/2206.05356) v2 (full version with the proofs of Claims 3, 4 and of
Section 5.3); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** All the paper's results are proved, for any number of processes: the speedup
theorem (Theorems 1 and 2), Lemma 1, Corollaries 1–3, Theorems 3 and 4, and Claims 1–6. The speedup
theorems need two model properties that the paper uses without stating them (made explicit below). The
abstract and conclusion overstate the binary-consensus result. We also prove that the bounds of
Corollary 3 are tight.

## Mistakes in the paper

There are no false statements. Imprecisions, by decreasing importance:

* **Overstated scope of the binary-consensus result (abstract, Section 1.2, Conclusion).** The abstract
  says binary consensus objects "are not more powerful as far as helping solving approximate agreement
  faster is concerned". The conclusion says they are not useful "at least when `n ≥ 1/ε`". Theorem 4,
  the only supporting result, covers only algorithms whose consensus inputs depend on the process id and
  the round. Its bound `min(⌈log₂ n⌉ − 1, ⌈log₂ 1/ε⌉)` is one round below the IIS bound whenever
  `1/ε ≤ n ≤ 2^⌈log₂ 1/ε⌉`: for `n = 4`, `ε = 1/4` it gives 1 round, the IIS bound gives 2. It matches the
  IIS bound only for `n > 2^⌈log₂ 1/ε⌉` (e.g. `n ≥ 2/ε`). Theorem 4
  itself is correct as stated (`theorem4_log`).
* **Implicit assumptions in Theorems 1 and 2 (under-specified, true for the paper's models).** The proof
  uses that a round in which only some processes take part extends to a round of all of them, with
  the same views for the early ones (`P^(1)(τ') ⊆ P^(1)(τ)`). It also needs that a box called solo
  returns a value determined by the caller's input ("`b_i = B_t(a_i)`"). Both are explicit hypotheses
  (`Model.Extendable`, `Model.SoloDet`), proved for IIS, iterated snapshot, IIS + test&set and
  IIS + binary consensus. A related ambiguity: the paper drops the carrier-map requirement on `Δ` but
  keeps the complex-based definition of solvability, under which the liberal task of Definition 4 would
  not be liberal. We use the standard reading: the processes of `σ` participate exactly.
* **Unchecked side condition in the proof of Theorem 4 (gap, statement true).** Claim 6 assumes
  `|S| ≥ 5`, and the iteration applies it to every `S_k` but only checks `|S_{t−1}| ≥ 3`. The missing
  inequality holds. Claim 6 in fact needs no size hypothesis, and we iterate with the cleaner invariant
  "`|S| ≤ 2^(t+1)` or `1 ≤ 2^t ε`" (`theorem4_aux`).
* Slips: the claims are applied to `3^k ε` and `2^k ε` beyond Definition 3's range `ε ≤ 1` (we prove
  them for every `ε ≥ 0`). Claim 4's proof (and Corollary 2's) says `P^(1)(σ)` for the protocol
  complex `P^(1)(τ)` of the local task. The proceedings version of Theorem 1's proof mixes `ρ'`/`ϱ'`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* `n` asynchronous wait-free processes `P` (any finite type, decidable equality), iterated
  full-information protocols (Algorithms 1 and 2): in round `r` every participant writes its view to a
  fresh memory, optionally calls a fresh black-box object, and reads. One round is a *pattern* (who sees
  whom, box answers) admissible in the model for the participating set and box inputs
  (`Cslib/Computability/Distributed/IteratedModel/Basic.lean`). Models: IIS (`iis`, the chromatic-subdivision condition of
  Section 2.2), iterated snapshot (`isnap`), IIS + test&set (`iisTS`: the winner is a process of the
  first concurrency class), IIS + binary consensus (`iisBC`: the proposal of such a process wins),
  all in `Cslib/Computability/Distributed/IteratedModel/Patterns.lean`.
* Crash failures: a task is solved if, for every input simplex `σ` and every execution in which exactly
  `id(σ)` participates, the decisions form an element of `Δ(σ)`. Crashes mid-execution are faces of
  such executions (`Model.Extendable`). Deterministic processes, adversarial scheduler, no randomness.
* Tasks are relations `Δ(σ)` without carrier-map assumption; approximate agreement on the grid
  `{0, 1/m, …, 1}` is scaled to integers `{0,…,m}` with `ε = e/m`.

**Main results in Lean.** (namespace `AsyncSpeedup`)

| Paper | Lean | File |
|---|---|---|
| Definition 1 (local task), Definition 2 (closure), closure w.r.t. `β` (§5.3) | `localTask`, `closure`, `closureβ` | `Speedup.lean` |
| Remark after Def. 2 (`Δ ⊆ Δ'`) | `closure_contains` | `Speedup.lean` |
| Theorem 1 / Theorem 2 (speedup) | `speedup_noBox` / `speedup` | `Speedup.lean` |
| Claim 5 | `speedup_idOnly` | `Speedup.lean` |
| Lemma 1 | `solvable_zero_of_fixedPoint` | `Speedup.lean` |
| `CL(consensus) = consensus`, Corollary 1 | `consensus_fixedPoint`, `corollary1` | `Consensus.lean` |
| Relaxed task fixed point, Corollary 2 | `consensus3_fixedPoint`, `corollary2` | `Consensus.lean` |
| Figure 4 (2-process consensus with test&set, 1 round) | `twoConsensus_iisTS` | `Consensus.lean` |
| Definitions 3, 4; Claim 1 | `aa`, `libAA`; `claim1_aa`, `claim1_lib` | `ApproxAgreement.lean` |
| Claim 2 (`CL(ε-AA) = 3ε-AA`, `n = 2`) | `claim2` (inclusion for all `n`: `closure_aa_subset`) | `Tightness.lean` |
| Claims 3, 4 (`CL(lib ε-AA) = lib 2ε-AA`) | `claim3`, `claim4` | `Tightness.lean` |
| Claim 6 | `claim6` (inclusion: `claim6_subset`) | `Tightness.lean`, `LowerBounds.lean` |
| Corollary 3 (`⌈log₃ 1/ε⌉`, `n = 2`; `⌈log₂ 1/ε⌉`, `n ≥ 3`) | `corollary3_two_log`, `corollary3_many_log` | `LowerBounds.lean` |
| Theorem 3 (test&set, `n ≥ 3`) | `theorem3_log` | `LowerBounds.lean` |
| Theorem 4 (binary consensus, id-only inputs) | `theorem4_log` | `LowerBounds.lean` |
| Remark after Cor. 3 (tightness) | `aa_solvable_two` (`3^t ε ≥ 1`), `aa_solvable_many` (`2^t ε ≥ 1`) | `Tightness.lean` |

The scaled forms `corollary3_two` (`m ≤ 3^t e`), `corollary3_many`, `theorem3` (`m ≤ 2^t e`) and
`theorem4` (`n ≤ 2^(t+1) ∨ m ≤ 2^t e`) are also available. Tightness uses a composition lemma for
uniform one-round reductions (`solvable_succ_of_reduction`).

**Not formalized.** The topological figures and the iterated *collect* model (the speedup theorem is
proved for an abstract model; the paper's instances above are covered); the "essentially tight" remark
on Theorem 4.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: all four models satisfy the hypotheses of the speedup theorem, and concrete
algorithms solve tasks in them (`aa_solvable_two`, `aa_solvable_many`, `twoConsensus_iisTS`). So the
lower bounds are tight and the solvability notions are not empty. The framework
(`Cslib/Computability/Distributed/IteratedModel/`, now in CSLib) is new and independent of CSLib's `Impl`-based shared-memory
model.
