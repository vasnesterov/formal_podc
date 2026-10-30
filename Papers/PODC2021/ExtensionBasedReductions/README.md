# Reductions and Extension-Based Proofs — PODC 2021

Kayman Brusse, Faith Ellen. *Reductions and Extension-Based Proofs.* PODC 2021. DOI
[10.1145/3465084.3467906](https://doi.org/10.1145/3465084.3467906). Formalized version: the PODC proceedings
version (no arXiv version; the "full version" cited for Sections 5–7 was not available).

**Verdict: 🛠️ Proof repaired.** We prove Theorem 1 (an augmented extension-based impossibility proof transfers
from `T` to `S` along a reduction) for reductions `(R₁, R₂)` in which `R₂` needs no communication, i.e. each
process applies a function to its own output of `S`. `R₁` is an arbitrary NIS-solvable task. One step of the
paper's "Why the prover wins" argument fails as written; we fix it by choosing the initial configuration
`D₀` of `A` canonically. The general case, where `R₂` needs the NIS composition `A₂ ∘ (A ∘ A₁)` of
Section 6, is **not** formalized. Its correctness proof is deferred by the paper to a full version, and its
assignment-query step depends on an unproved claim. The Section 4 claim (extension-based ⇒ augmented
extension-based) and the cited fact "NIS-solvable ⇒ IS-solvable" are proved.

## Mistakes in the paper

* **Theorem 1, "Why the prover wins", first case: proof gap; the statement holds in the case we check.**
  The paper argues: "if the values output in `D₀γ'` did satisfy the specifications of `S`, then the values
  output in `C` would satisfy `R₂ ∘ S ∘ R₁`". Here `D₀` is any initial configuration of `A` compatible with
  `C₀γ₁`, so its inputs are only fixed for processes that finished `A₁`. The prover may also reach `C`
  before every process has finished `A₁`. Then `D₀` gives the other processes arbitrary inputs, and its
  input vector need not be an output vector of `R₁` (it need not even be an input vector of `S`). A valid
  `S`-output for that input vector then tells nothing about `T`. The step is correct only for final
  configurations, but the paper's prover also wins by reaching partial configurations that already violate
  `T`. Our repair: `𝒫` keeps the `A`-part with **canonical** inputs: the outputs of a fixed completion of
  the `A₁`-part (`toA`, `ucan`). After every simulated step of `A₁`, not only the last one, `𝒫` re-reaches
  this configuration by a chain of queries from the start of its phase. We also handle the
  infinitely-many-phases case by a potential argument, since "`𝒫_T` can only end a finite number of phases
  with `A₁`/`A₂`-only steps" needs one. (`theorem1_local`, `step_queryA1`, `ucan_mem`)
* **General Theorem 1 (non-local `R₂`): two gaps we did not try to resolve.**
  * The assignment-query step enumerates "the initial configurations `C₂` of `A₂` such that there is a
    `P'`-only schedule from `C₂` that results in a configuration satisfying `f`". This ignores the steps of
    `A₂` that other processes, possibly outside `P`, already took during `γ`. Such a step can be necessary
    for `f`, so the filter can drop the right `g`, and the prover then answers `None` although a schedule
    exists. The later exhaustive search over `μ₂` makes the filter unnecessary: enumerating all `g` repairs
    this.
  * More seriously, the claim that the `A₂`-schedules simulable from `C μ₁ μ'` "do not depend on the
    particular schedule `μ'`" is asserted without proof. It is needed for the `None` answers to be correct.
    With estimate vectors, the composite configuration after `μ'` records more than the outputs of `A`:
    composite rounds and copied estimates. So the claim needs a real argument, which the paper defers
    together with the correctness of the composition. We neither prove nor refute it.
* **Typos.** "Suppose `R₂ ∘ S ∘ R₂` is a reduction" (§1) and "`R₁ ∘ S ∘ R₂`" / "`R₂ ∘ S ∘ R₂`" (§7, "Why the
  prover wins") should read `R₂ ∘ S ∘ R₁`. In §3, "if `δ(s'ᵢ) ≠ ⊥` then `pᵢ` outputs `δ(sᵢ)`. If `δ(sᵢ) = ⊥` …" should read
  `δ(s'ᵢ)` in both places.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **NIS model.** Full-information non-uniform iterated snapshot model: asynchronous and wait-free, `n` = a
  finite type `P` of processes (any `n`), deterministic, no randomness. A protocol is its decision function
  `δ` on full-information states. A state is `init i x`, `upd s` (the paper's `s·1`) or `scan s v`, which
  stores the pre-scan state `s` together with the paper's `(i, v)`. A configuration is the vector of
  states; the memory is determined by the states. Crashes are processes that stop being scheduled. Every
  input vector over the input type is an initial configuration; the task constrains only the runs from its
  input vectors.
* **Game.** A prover is a deterministic strategy: a function of the history. The protocol is a decision
  function together with arbitrary correct answers to assignment queries; these answers are adversarial
  and may depend on the history. Each query response carries the new configuration and the outputs of all
  processes.
* **Reached configurations.** In a phase these are `reinit base u` (the paper's `C₀' α(φ)`) plus the query
  responses. `endPhase C` requires `C` to be a response of the current phase.
* **Winning.** The prover wins if all its moves are legal and one of these holds:
  1. it reaches a configuration whose partial outputs cannot be extended to a valid output vector;
  2. there are infinitely many phases;
  3. from some point on, every move is a query from the previous response (an infinite chain).

  An infinite last phase that is not eventually one chain is a loss. This is the rule "finitely many chains
  and assignment queries per phase".
* **Reductions.** The paper's definition (`IsReduction`), with the implicit well-formedness made explicit:
  outputs of each task are inputs of the next one. Theorem 1 is proved under the extra hypothesis
  `LocallySolvable R₂ h`. `R₁` only needs to be NIS-solvable: the paper's "w.l.o.g. `A₁` is an IS protocol"
  is proved (`exists_isIS_of_solves`, which needs finitely many inputs, as in the paper).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| §3 tasks, composition, solving; reductions | `Task`, `Task.comp`, `Solves`, `IsReduction`, `LocallySolvable` | `Podc/.../NIS/Model.lean`, `Main.lean` |
| §4 (augmented) extension-based proofs | `HasEBProof`, `HasAugEBProof`, `outputSpec`, `assignSpec` | `Podc/.../NIS/Game.lean` |
| §4 "every EBP is an augmented EBP" | `hasAugEBProof_of_hasEBProof` | `Podc/.../NIS/OutputQueries.lean` |
| §2/§7 cited [8]: NIS-solvable ⇒ IS-solvable | `exists_isIS_of_solves` | `Podc/.../NIS/ISConversion.lean` |
| §6 composition `A ∘ A₁` with `A₁` an IS protocol | `compP`, `stepY_A1`, `stepY_A`, `reach_decomp`, `decompY` | `Composite.lean` |
| **Theorem 1** (with `R₂` local) | `theorem1` (from `theorem1_local`) | `Main.lean` |
| §8 transfer of "no augmented EBP" | `no_augEBProof_of_reduction` | `Main.lean` |
| non-vacuity | `hasAugEBProof_of_spec_empty`, `isReduction_self`, `idProt_solves` | `NonVacuity.lean` |
| soundness of the game: solvable ⇒ no (augmented) EBP | `not_hasProof_of_solves`, `not_hasAugEBProof_of_solves` | `NonVacuity.lean` |

The prover of §7 is `proverS` (`Prover.lean`); its correctness is in `Theorem1.lean`: `step_queryA`,
`step_queryA1`, `step_oracle` (with `assign_sound` and `assign_complete`) and `step_end`. The generic
"prover simulating another prover" machinery is `simulate_spec` and `SimData.transfer` in
`Podc/.../NIS/Simulation.lean` and `Transfer.lean`.

**Not formalized.**
* Theorem 1 for reductions whose `R₂` needs communication, and the general composition `A₂ ∘ A₁` of
  Section 6 (estimate vectors).
* Section 5 (no augmented EBP for `k`-set agreement), which the paper defers to the full version.
* Corollary 2 (anonymous protocols).
* The specific reductions cited in §2/§8.

**Trust.** No `sorry`; `theorem1`, `theorem1_local`, `hasAugEBProof_of_hasEBProof` and
`exists_isIS_of_solves` use only `propext`, `Classical.choice` and `Quot.sound`. Non-vacuity:
* augmented EBPs exist (`hasAugEBProof_of_spec_empty`);
* every task reduces to itself through identity tasks solved by the one-round IS protocol "output your
  input" (`isReduction_self`, `idProt_solves`), so the hypotheses of `theorem1` are satisfiable.
* the game is sound: a task solvable in the NIS model (finite input type) has no extension-based or
  augmented extension-based impossibility proof (`not_hasProof_of_solves`, `not_hasAugEBProof_of_solves`),
  so the conclusion `HasAugEBProof S` of `theorem1` is a genuine impossibility statement.

The NIS model, the game and the simulation framework are staged in `Podc/Computability/Distributed/NIS/`
(CSLib candidates). Everything else is in this folder.
