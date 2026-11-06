# Bounded-Size Registers — PODC 2024

Carole Delporte-Gallet, Hugues Fauconnier, Pierre Fraigniaud, Sergio Rajsbaum, Corentin Travers. *The Computational
Power of Distributed Shared-Memory Models with Bounded-Size Registers.* PODC 2024. DOI
[10.1145/3662158.3662789](https://doi.org/10.1145/3662158.3662789). Formalized version: the conference paper, with
the proofs of the full version arXiv [2309.13977](https://arxiv.org/abs/2309.13977) v1 (Sections 4–5 there =
Sections 3–4 of the conference paper).

**Verdict: 🔧 Easy fix.** Theorem 1.1 (bounded registers are not universal when `n/2 < t < n`) is proved, together with
the two results it cites (Lemma 2.1, FLP for read/write memory; Lemma 2.2, wait-free ε-agreement), and so is Algorithm 1
(two-process ε-agreement with 1-bit registers, Proposition 5.1). Theorem 1.2 (3-bit registers are universal for two
processes) is proved from the Biran–Moran–Zaks characterization, which the paper cites: its "only if" direction
(solvable with unbounded registers ⇒ connectivity and covering) is **assumed** as the hypothesis `BMZ Δ`; the rest (BMZ
conditions ⇒ Algorithm 2 with 3-bit coordination registers solves the task) is proved. All repairs are local, namely
Algorithm 2's parameters and a few missing proof cases, while Theorems 1.3–1.5, which include the `t < n/2` and iterated
results, were not checked.

## Mistakes in the paper

### 🔧 Algorithm 2 (full version), resolution
The pseudocode calls `A_{L/2}` with ε = 1/(L+1) and then indexes the node `Y_{dL}`, while the text and Lemma 5.8 use
ε = 1/L; `dL` is not an integer as printed, and `L/2` need not be one either.

**Impact.** Nothing else in the construction changes, and Theorem 1.2 holds.

**Repair.** We use resolution `1/L` with odd `L = 2k+1` and call Algorithm 1 with parameter `k`, so the decision
indexes the path node directly (`alg2`).

### ✏️ Slips
- In Section 5.2.4, "for every `j ∈ {1,…,L}`, `Y_j ∈ Δ(X)`" should read `j ∈ {0,…,L−1}`, as in Section 5.2.2; the last
  step of Lemma 5.8 repeats the index range (`PathSystem.legal`).
- In the proof of Theorem 1.1, `w_ℓ` is taken "after each process has decided", but a process may crash. The word
  `w_ℓ` should be the register contents at the *end* of `E_ℓ` (`not_solves_epsAgreement`).
- Claim 3.1's "`D ⊆ O_ℓ'` for some `ℓ' ≠ ℓ`" fails for `D = {0}`, `ℓ = 0`. This is harmless, since singletons are
  handled separately (`solves_binConsensus_of_not_claim`).
- Proposition 5.1 says "for every `k ≥ 0`", but for `k = 0` the loop is empty and `r` is undefined. Algorithm 2 only
  needs `k ≥ 1`, which we assume (`alg1_solves`).
- In the proofs of Lemmas 5.1 and 5.4 the registers `R1`/`R2` are swapped.
- The caption of Figure 1 says "1-bit registers are universal (Theorem 1.2)"; Theorem 1.2 says 3 bits (which is what is
  proved: Algorithm 1's ternary input register plus its 1-bit register).

### Typos
- `|W| = …` should be `|W| ≤ …`.

## Proof gaps (statements true)

### 🔧 Claim 3.1 and Theorem 1.1 (inputs of the absent processes)
The inputs of `p_{n−t+2}…p_n` are never fixed: the reduction to consensus uses the validity of ε-agreement, which only
applies when *all `n`* inputs are equal, while consensus fixes only the inputs of `p₁…p_{n−t+1}`, and the final step
needs `E_{2i}` and `E_{2j}` to agree on everything that `p_{n−t+2}…p_n` can observe, including those processes' own
inputs, which the paper calls "arbitrary".

**Impact.** Statements true. The proof works because `p_{n−t+2}…p_n` never take a step, so their inputs do not matter;
the paper does not say this.

**Repair.** In the validity argument those inputs are set to the common value (`solves_binConsensus_of_not_claim`).
Everywhere else they are fixed the same way in all executions `E_ℓ` (`not_solves_epsAgreement`).

### 🔧 Lemma 5.8 (Algorithm 2, one process deciding)
Lemma 5.8 assumes that both processes decide, yet Theorem 1.2's proof concludes correctness from it, so the case where
one process decides and the other crashes is not treated.

**Impact.** Statement true. This is exactly the case where the covering condition is needed.

**Repair.** Solo decisions are legal too (covering condition); we prove that case (`alg2_safe`).

### 🔧 Lemma 5.5 (Algorithm 1, case `k = 1`)
Lemma 5.5's case "`I_j` read as ⊥" says the other process decides at line 17 with `r_j = 2`, which is wrong for `k = 1`.

**Impact.** Statement true (`alg1_solves`).

**Repair.** For `k = 1` the other process completes the loop and decides at line 14 instead. The value is the same, so
the statement holds.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* The asynchronous read/write shared-memory model (`Podc/Computability/Distributed/SWMR/Basic.lean`).
  - Processes are deterministic state machines with arbitrary state spaces, and there is no randomness.
  - Each process owns a bank of SWMR atomic registers. A step is one read of any register, one write to an own
    register, or an irrevocable decision; processes may keep stepping after deciding.
  - The adversary picks the inputs and the schedule.
  - Crash failures: in an infinite schedule a process is faulty iff it takes finitely many steps.
  - `t`-resilient solvability (`Alg.Solves A t T`) means two things. Every finite execution's decisions are legal.
    In every infinite execution with at most `t` faulty processes, every correct process decides. Wait-free is
    `t = n − 1`.
* "Registers of at most `f(n)` bits" means that the register bank of each process has at most `2^{f(n)}` contents.
  This allows several registers per process, so the impossibility is stronger than the paper's.
* Unbounded registers (positive side of Theorem 1.1): one register per process holding a `List ℚ`.
* Two-process tasks (Theorem 1.2) are relations `Δ` on full input/output vectors over *all* input pairs `In × In`
  (the paper allows an arbitrary input set `I`).
* The model is a new, self-contained one. CSLib's shared-memory `Impl` framework (registers as base objects, `Task`,
  `WaitFree`, valency) has no crashes or `t`-resilience, and CSLib's `FLP/` folder is Völzer's message-passing model.
  So neither could express `t`-resilient solvability or the register version of FLP. A bridge (an `Alg` as an
  `Impl (taskObj In Out)` over the registers `P × K`, plus a `t`-resilient fairness predicate on CSLib's `InfExec`)
  is left for the CSLib migration.
* Algorithm 1 uses, per process, a write-once input register (`Option Bool`, ⊥ = `none`) and a 1-bit register.
  Algorithm 2 additionally has the write-once task-input register. These are the paper's special input registers;
  the coordination registers hold 3 bits.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1.1 | `theorem_1_1`, `theorem_1_1_single` (one register per process) | `Theorem11.lean` |
| Proposition 4.1 (full version) | `proposition_4_1`; general form `not_solves_epsAgreement` (any `G`, any `k > 2·M^{|G|}`) | `Theorem11.lean`, `NonUniversality.lean` |
| Claim 3.1 | `claim_3_1` (reduction: `solves_binConsensus_of_not_claim`) | `NonUniversality.lean` |
| Lemma 2.1 (1-resilient binary consensus impossible) | `Cslib.SWMR.Alg.not_solves_binConsensus` | `Podc/…/SWMR/FLP.lean` |
| Lemma 2.2 (wait-free ε-agreement, unbounded registers) | `approxAgreement_solvable` (iterated collect + midpoint, `aaAlg_solves`) | `ApproxAgreement.lean` |
| Algorithm 1, Proposition 5.1 | `alg1`, `alg1_solves` | `Alg1.lean` |
| Lemma 5.6 | `alg1_lemma_5_6` | `Alg1.lean` |
| Algorithm 2, Lemma 5.8 | `alg2`, `alg2_safe`, `alg2_solves` (ε-agreement as black box `EBox`) | `Alg2*.lean` |
| Lemma 5.7 ⇒ paths of Section 5.2.2 | `BMZ`, `exists_pathSystem` | `BMZ.lean` |
| Theorem 1.2 (from Lemma 5.7) | `theorem_1_2` | `Theorem12.lean` |

**Not formalized.**
* The "only if" direction of the Biran–Moran–Zaks characterization (Lemma 5.7), which the paper cites. It turns
  "solvable with unbounded registers" into the hypothesis `BMZ Δ` of `theorem_1_2`. The paper's remark that this
  message-passing characterization transfers to shared memory is covered by the same hypothesis and was not checked.
* Theorem 1.2 for a restricted input set `I ⊊ In × In`: `theorem_1_2` covers only the full product.
* Theorem 1.3 (`t < n/2`: `O(t)`-bit registers suffice), Theorem 1.4 (1-bit iterated immediate snapshot) and
  Theorem 1.5 (6-bit `O(log 1/ε)` ε-agreement). Their proofs are only sketched in the full version and rely on further
  cited simulations.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`. The
model is staged in `Podc/Computability/Distributed/SWMR/` (CSLib candidates `Basic`, `Restrict`, `FLP`). The
hypotheses of Theorem 1.1 are not vacuous: its positive half exhibits a concrete algorithm.
