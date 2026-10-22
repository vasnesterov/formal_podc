# Differences between the formalization and the paper

Paper: Delporte-Gallet, Fauconnier, Fraigniaud, Rajsbaum, Travers. *The Computational Power of Distributed
Shared-Memory Models with Bounded-Size Registers.* PODC 2024. Proofs follow the full version, arXiv:2309.13977v1
(Section 4 = Section 3 of the conference version, Section 5 = Section 4).

## Model

- **Model** (`Podc/Computability/Distributed/SWMR/Basic.lean`, namespace `Cslib.SWMR`). Deterministic processes with
  arbitrary (possibly infinite) local state spaces; every process owns a bank of SWMR atomic registers `∀ i : K, V i`
  (the paper: one register `R_i` per process, plus a write-once input register `I_i` in the positive results). A step is
  one write to an own register, one read of any register, or a decision. An execution is given by the inputs and a
  schedule (list or `ℕ`-sequence of process ids).
- **Decisions** are explicit irrevocable actions; a process may keep taking steps after deciding (the paper allows
  this too, Section 6/7 remark). Impossibility results are therefore proved for the stronger class of algorithms that do
  not have to halt.
- **Crashes / `t`-resilience.** In an infinite schedule the faulty processes are those taking finitely many steps.
  `Alg.Solves A t T`: every finite execution satisfies the task (safety: every finite prefix is legal, outputs of
  undecided processes are `none`) and in every infinite execution with at most `t` faulty processes every correct
  process eventually decides. Wait-free = `t = n - 1` (then every infinite schedule qualifies).
- **Tasks** are predicates on input vectors and partial output vectors (`Task P In Out`), checked on every finite
  prefix. This is the usual "outputs of the deciding processes extend to a legal output" condition for the two tasks
  used here (consensus, ε-agreement), whose legality is a conjunction of conditions on pairs of decided values.
- **Binary consensus** uses the weak validity condition (if all inputs are `b`, only `b` can be decided); the paper's
  validity ("the decision is some input") implies it, so the impossibility (Lemma 2.1) is stronger as formalized.
- **Resilience count.** `Alg.Solves` bounds `(Faulty σ).ncard`; this is meaningful only for finite `P` (all results
  here assume `[Fintype P]`; for infinite `P`, `ncard` of an infinite set is `0`, so a CSLib version should use `encard`).
- **Relation to CSLib.** The model is self-contained and parallel to CSLib's `SharedMemory` `Impl` framework (registers
  as base objects, `Task` with partial inputs, `WaitFree`, `Valency`, `AgreeOn`), which has no crashes / `t`-resilience,
  and to CSLib's `FLP/` (Völzer, message passing). `binConsensus` corresponds to CSLib's `weakConsensus`. A bridge
  (an `Alg` as an `Impl (taskObj In Out)` over registers indexed by `P × K`, `Solves (card P - 1)` ↔ `Impl.Solves` +
  wait-freedom on one-shot executions, and a `t`-resilient fairness predicate on `InfExec`) is not built.
- **ε-agreement** is the discretized binary version of Section 2: outputs `m/k`, `m ∈ {0,…,k}`, represented by
  `m : ℕ`; validity "all inputs equal `b` ⇒ every decision is `b`"; agreement `|m − m'| ≤ 1`.
- **Register size.** "Registers of at most `f(n)` bits" is formalized as "the register bank of a process has at most
  `2^{f(n)}` possible contents" (`Nat.card (∀ i, V i) ≤ 2 ^ f n`; `theorem_1_1_single` is the special case of one
  register per process with `card W ≤ 2^{f(n)}`). This is more general than the paper (several registers per process
  are allowed, of any total size), so the impossibility is stronger. (A register "of at most `f(n)` bits" holding bit
  strings of length ≤ `f(n)` has `2^{f(n)+1} − 1` values; apply the theorem to `f' = f + 1`.)

## Theorem 1.1 / Proposition 4.1 (non-universality, `n/2 < t < n`)

- Generalized: `not_solves_epsAgreement` holds for any finite process set `P` and any set `G` of "early" processes with
  `2 ≤ |G|`, `|Gᶜ| + 1 ≤ t`, `|G| ≤ t`, `Gᶜ ≠ ∅`, and any `k > 2·M^{|G|}` (`M` = number of contents of a register
  bank). The paper's `k = 2 (2^{f(n)})^{n−t+1} + 1` is the instance used in `proposition_4_1`; `k` need not be odd.
- Lemma 2.1 (1-resilient binary consensus is impossible) is **proved** (`Cslib.SWMR.Alg.not_solves_binConsensus`), not
  cited. Lemma 2.2 (wait-free ε-agreement with unbounded registers, cited by the paper) is **proved** for a concrete
  algorithm (`approxAgreement_solvable`; iterated collect + midpoint with history registers).
- **Claim 3.1 (4.1), inputs of the absent processes.** The reduction to consensus must use the validity of
  ε-agreement, which only applies when *all `n`* inputs are equal, while consensus only fixes the inputs of
  `p_1..p_{n−t+1}`. The paper does not address the inputs of `p_{n−t+2..n}`; since these processes never take a step,
  the restricted algorithm does not depend on them, and we instantiate them by `b` in the validity argument and by a fixed
  vector `z` everywhere else (`solves_binConsensus_of_not_claim`, `ClaimHolds`).
- **Claim 3.1, "D ⊆ O_ℓ' for some ℓ' ≠ ℓ".** False for `D = {0}` and `ℓ = 0` (no such `ℓ'`); harmless because singletons
  are handled separately. Our proof argues directly on two decided values.
- **"w_ℓ = registers immediately after each process has decided".** Some process of `p_1..p_{n−t+1}` may crash, and the
  registers of `p_{n−t+2..n}` and their local states must also coincide; we take the whole memory and the local states
  at the end of the finite execution `E_ℓ` (`AgreeOn Gᶜ`).
- **`|W| = (2^{f(n)})^{n−t+1}`** should be `≤`.

## Lemma 2.2 (cited) — `ApproxAgreement.lean`

- Proved for a concrete algorithm of our choice (the paper only cites [16, 26]): `k` rounds of "write the list of round
  values, collect all registers, take the midpoint of the round-`r` values seen"; decision `⌊k·v⌋`. One register per
  process holding a `List ℚ`. The local state also stores ghost data (all values read). Wait-free with
  `R·(|P|+2)+1` own steps.

## Algorithm 1 / Proposition 5.1 — `Alg1.lean`

- Faithful to the pseudocode, one shared-memory access per step. Line 8 (`x_me ← I_me.read()`, a read of the own
  write-once register) is not a step: `x_me` is kept in the local state (equivalent). Deciding is a separate step;
  afterwards the process reads its own register forever.
- Registers: per process an input register `Option Bool` (⊥ = `none`) and a 1-bit register `Bool`, as in the paper.
- `k ≥ 1` is assumed (the paper says `k ≥ 0`; for `k = 0` the loop is empty and `r` is undefined).
- Step bound: a process decides within `2k + 3` own steps (the paper: `2k + 3` operations).
- Lemma 5.5's proof, case "process `i` reads ⊥ from `I_j`", claims `r_j = 2` and a decision at line 17; for `k = 1`
  process `j` finishes the loop with `r_j = 1` and decides at line 14 (same value). Our proof is an inductive invariant
  (facts F1–F5 of the paper's Lemmas 5.1–5.4) and does not follow this case split.
- Typos in the proofs of Lemmas 5.1 and 5.4 (`R1`/`R2` swapped).

## Theorem 1.2 — `Alg2*.lean`, `BMZ.lean`, `Theorem12.lean`

- **Assumption.** The "only if" direction of Lemma 5.7 (Biran–Moran–Zaks: wait-free solvable with unbounded registers ⇒
  the connectivity and covering conditions) is cited by the paper and is the hypothesis `BMZ Δ` of `theorem_1_2`;
  so Theorem 1.2 is formalized as "BMZ conditions ⇒ solvable wait-free with Algorithm 2 (3-bit coordination registers
  + write-once task-input register)". Tasks: finite input set `In`, arbitrary output set; `Δ` a relation on full
  input/output vectors; a partial output is legal iff it extends to a legal full output (`taskOf`). The input set is
  always the full product `In × In` (every `X : Bool → In` is an input, and connectivity/covering range over all of
  them); the paper (and BMZ) allow an arbitrary input set `I ⊆ In × In`. Tasks with a restricted input set are covered
  only if `Δ` can be extended to all input pairs while keeping the BMZ conditions.
- **Figure 1** of the conference version says "1-bit registers are universal (Theorem 1.2)"; Theorem 1.2 (and what is
  proved) is 3 bits.
- **Paths (Section 5.2.2).** `exists_pathSystem` builds the paths from the BMZ conditions; all paths get the same
  length `L` by repeating the last node of `Δ(X) ∩ O'` (the paper: "adding adjacent copies"). `δ(X^i)` is only used
  through the entry of the process whose input is known, so `PathSystem.part` only fixes that entry.
- **Resolution.** The full version calls `A_{L/2}` with ε = 1/(L+1) and then uses the node `Y_{dL}`; inconsistent. We
  use paths of odd length `L = 2k + 1` and Algorithm 1 with parameter `k` (ε = 1/L), so the decision `d` (numerator)
  indexes the node `Y_d`.
- "For every `j ∈ {1,…,L}`, `Y_j ∈ Δ(X)`" should be `j ∈ {0,…,L−1}` (`PathSystem.legal`).
- Line 11 (`x_other ← I_other.read()`) is performed in the same step in which the ε-agreement subroutine returns
  (the subroutine's return is not a memory access).
- Algorithm 1 is used as a black box through `EBox` (safety, Lemma 5.6, "an intermediate decision implies distinct
  inputs and a step of the other process", step bound); the composition is justified by a simulation
  (`Alg2Sim.lean`): every execution of Algorithm 2 projects to an execution of Algorithm 1 from the ε-agreement inputs.
- Lemma 5.8 assumes both processes decide; we also prove that a single decision extends to a legal output (covering).
- The paper's registers: "3 bits" for Algorithm 1's input register (⊥/0/1) and 1-bit register; we keep them as two
  registers of the same process (`card_alg1Reg : 6 ≤ 2³` joint values).

## Not formalized

- Theorem 1.3 (`t < n/2`: `O(t)`-bit registers suffice; ABD emulation + routing + alternating bit),
  Theorem 1.4 (1-bit IIS), Theorem 1.5 (6-bit `O(log 1/ε)` ε-agreement): their proofs are only sketched in the full
  version and rely on further cited simulations ([4], [10], [14]).
- The "only if" direction of Lemma 5.7 (see above).
