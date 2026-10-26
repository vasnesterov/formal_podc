# Wait-free hierarchy for multi-threaded systems — PODC 2020

Matthieu Perrin, Achour Mostéfaoui, Grégoire Bonin. *Extending the Wait-free Hierarchy to Multi-Threaded
Systems.* PODC 2020. DOI [10.1145/3382734.3405723](https://doi.org/10.1145/3382734.3405723). Formalized
version: the 10-page proceedings version (there is no arXiv version); numbering follows it.

**Verdict: 🛠️ Proof repaired.** All formalized claims hold:
* the impossibility results for window registers in `MA₃` (Lemmas 8–9, Proposition 5);
* the impossibility result for binary consensus + window registers in `M₂` (Proposition 4), for algorithms
  whose objects are all allocated at set-up;
* the finite-memory reduction (Lemma 4);
* the two consensus algorithms (Algorithm 2 for Theorem 3, Algorithm 3 for Proposition 3).

The proof of Proposition 4 needs real repairs (partition invariant, counting, last step). We proved
Proposition 4 only for algorithms whose objects are all allocated at set-up. The universal construction
(Theorem 1) is stated without proof in the paper and is not formalized.

## Mistakes in the paper

* **Proposition 4: the partition invariant is too weak for the merging step (proof gap, statement true).**
  * Definition 4 asks that the restriction of `α` to each *class* be a valid execution. Equality of the
    shared memory (condition 3) is required for one process `p` only.
  * After a block `β`, the classes of the `l·i` processes of `Φ` are merged. The new class's restriction is
    an interleaving of several classes, which could now read each other's writes. Validity for each class
    alone does not imply that the merged restriction gives its members their real local states.
  * What makes it work is that every block overwrites *all* objects of `Xᵢ`: windows are written `l > k`
    times, and consensus objects are decided on the common value `b`.
  * We prove the invariant for every *union* of classes, together with "objects outside `Xᵢ` are untouched
    everywhere" and "consensus objects of `Xᵢ` are initial or decided `b`". After each block, the memory of
    any restriction containing the block equals the real memory. (`Prop4.Inv`, `Prop4.Inv.block_memEq`)
* **Proposition 4: the end of the proof and the counting are garbled (proof gap).**
  * The final paragraph says two processes "are about to write … to the last register" and decide
    differently. That does not follow from the construction.
  * The correct end reuses the argument of the `γ` step. In the last stage `Xₘ` is the whole memory, so the
    solo run of `p` must decide. Another class then performs a block, and its representative runs solo and
    decides an input of its own class, which contradicts agreement.
  * The coverage after `j` scheduling steps is `uᵢ − l·j`, not `uᵢ − j`; likewise "`uᵢ − v = 2 l u_{i+1}`"
    should be `uᵢ − l·v`.
  * The w.l.o.g. "registers `first`/`last`" assumption is unnecessary.

  (`Prop4.iteration`, `Prop4.not_consensus`)
* **Proposition 4: run-time allocation is ignored (proof gap; only the static version is proved).**
  * In `M₂` processes may allocate finitely many fresh objects at run time.
  * The `γ` step runs `p` "until it covers an object not in `{x₁, …, xᵢ}`", which may be an object `p`
    just allocated. The pigeonhole over the `m − i` set-up objects then fails.
  * The natural repair is to stop only at set-up objects and to treat objects allocated inside a class as
    private to that class. It needs a model of references and allocation that we did not build.
  * Our theorem covers algorithms whose (finitely many) objects are all allocated at set-up.
* **Unproved claims.** The paper states the following without proofs: Theorem 1 (Algorithm 1, Propositions
  1–2, Lemmas 1–3), Claim 2 and Lemmas 5–7 (Algorithm 2), and Proposition 3 (Algorithm 3). We proved
  Claim 2, Lemmas 5–7 and the consensus part of Proposition 3 (`Alg2.alg2_solvesCons`,
  `Alg3.alg3_solvesCons`).
  * For Algorithm 3, wait-freedom cannot be argued by *arrival* order. A process may have written
    `proposed[j]` but not `isSet[j]` when it is overtaken.
  * It works with the order in which the `isSet` flags are set: the first process to set its flag never
    sees its `cons` decided `false`.
* **Typos.**
  * Definition 3: "`node′ = listₙ`" should be `nodeₙ`, and "a value `v` precedes a value `v`" should end
    with `v′`.
  * Proposition 4 uses "separable" for "partitioned" and indexes `i ∈ {0, …, m−1}` for a sequence starting
    at 1.
  * "it is is" (Definition 6); "multi-treaded" (Figure 1).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Podc/Computability/Distributed/SharedMemory/Arrival/Basic.lean`, staged CSLib candidate).
* Asynchronous shared memory with crash-stop processes `p₀, p₁, …`, which are deterministic and start with
  their inputs. A process arrives at its first step. Every step is one atomic operation on one object.
* A finite execution is a schedule `List ℕ`, an infinite one a sequence `ℕ → ℕ`. Arrival models are classes
  of infinite schedules:
  * `M₃`: all schedules;
  * `M₂`: schedules with finite range;
  * `Mⁿ₁`: schedules in which only processes `< n` step.
* Wait-freedom: a process taking infinitely many steps outputs. Agreement and validity range over all
  finite schedules.
* Objects are indexed by an arbitrary type, all allocated at set-up. An infinite index type is *infinite
  allocation* (`MA`); a finite one is a memory without run-time allocation. Dynamic finite allocation with
  references is **not** modelled (see above).
* Objects:
  * atomic consensus `cons⟨V⟩`;
  * `consₙ⟨V⟩`, whose responses after `n` invocations are arbitrary;
  * CSLib window registers of per-object size.
* Universality is not formalized. Results are stated for the consensus task: impossible ⇒ not universal;
  possible ⇒ universal by Theorem 1. Substituting implemented objects for atomic ones (composition) is not
  formalized either.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 4, Claim 1 | `consensus_finiteMemory`, `finite_reach`, `finite_usedObjs` | `FiniteMemory.lean` |
| Theorem 2 (step "cons⟨N⟩ from finitely many cons⟨B⟩ in `Mⁿ₁`") | `Alg3.alg3_solvesCons_bounded`, `Alg3.alg3_poised_lt` | `Alg3.lean` |
| Algorithm 2, Claim 2, Lemmas 5, 6, 7 (Theorem 3) | `Alg2.alg2_solvesCons`, `Alg2.claim2`, `Alg2.waitFree`, `Alg2.agreement`, `Alg2.validity` | `Alg2.lean` |
| Algorithm 3, Proposition 3 (consensus in `MA₃[cons⟨B⟩]`) | `Alg3.alg3_solvesCons` | `Alg3.lean` |
| Definitions 4–5 (partitioned / covered executions) | `Prop4.Inv`, `Prop4.Covers`, `Prop4.SSt` | `Partition.lean`, `Prop4.lean` |
| Proposition 4 (`M₂[cons⟨B⟩, WReg]`, static memory) | `Prop4.not_consensus` | `Prop4.lean` |
| Definition 6, Lemma 8 | `Cslib.SharedMemory.Arrival.Crit`, `Cslib.SharedMemory.Arrival.exists_crit` | `Podc/…/Arrival/Valency.lean` |
| Lemma 9 | `crit_write_same` | `WindowRegisters.lean` |
| Proposition 5 (`MA₃[WReg]`) | `window_not_consensus` | `WindowRegisters.lean` |

All Lean names are in namespace `Podc.InfiniteArrivalHierarchy` unless fully qualified.

**Not formalized.**
* Theorem 1 (Algorithm 1, the weak log, Propositions 1–2, Lemmas 1–3) and Remark 1.
* The hierarchy-placement statements Theorems 2–6 as such: they need universality and composition.
* Section 8 (iterator stacks: Proposition 6, Lemma 10, Theorem 6).

**Trust.**
* No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
* Non-vacuity: Algorithms 2 and 3 satisfy the model's correctness notions. For example,
  `alg3_solvesCons` shows that agreement, validity and wait-freedom in `M₃` are satisfiable. `Alg2.lean`
  also contains a concrete solo run checked by `rfl`.

**Infrastructure** (staged in `Podc/Computability/Distributed/SharedMemory/Arrival/`, CSLib candidates):
* `Basic.lean`: the model, `run_on` for block steps, solo runs, and limits of schedule chains.
* `Valency.lean`: valency with respect to a finite set of processes, critical executions, and the team /
  commutation / read-invisibility lemmas.
