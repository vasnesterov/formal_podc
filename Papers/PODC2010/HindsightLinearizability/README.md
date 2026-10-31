# Verifying Linearizability with Hindsight — PODC 2010

Peter W. O'Hearn, Noam Rinetzky, Martin T. Vechev, Eran Yahav, Greta Yorsh. *Verifying Linearizability
with Hindsight.* PODC 2010. DOI [10.1145/1835698.1835722](https://doi.org/10.1145/1835698.1835722).
Formalized version: the 10-page author copy (no arXiv version); numbering follows it.

**Verdict: ⚠️ Minor statement issues.** The main results hold. The optimistic set algorithm of Fig. 1
satisfies all the integrity invariants and is memory safe (Thm 4.1). `contains` is wait-free (Thm 6.4),
and the algorithm is linearizable (Thm 7.5). The Hindsight Lemma (Lemma 5.2) and the Local Window Lemma
(Lemma 5.7) are proved as intended. The Backbone Lemma (Lemma 5.4) is false as printed: the claimed
`j₀ < j₁ < … < j_k = i_k` must be weakened to `j₀ ≤ j₁ ≤ … ≤ j_k ≤ i_k`. That weaker form is what its
proof gives and what Thm 7.5 uses.

## Mistakes in the paper

* **Lemma 5.4 (Backbone Lemma) is false as stated.** It claims that for a temporal backbone `ζ` through
  `τ(i₀), …, τ(i_k)` there are indices `i₀ = j₀ < j₁ < … < j_k = i_k` such that `ζ(m)` is a backbone
  link in `τ(j_m)`. Both `j_k = i_k` and the strict inequalities fail. The counterexample is a real
  execution of the algorithm: thread 0 runs `add(5)`, giving `H → a → T`, then thread 1 runs
  `remove(5)`. Let `i₀` be the state just before the atomic section of `remove` and `i₁ = i₀ + 1` the
  state right after it. Then `⟨H, a⟩, ⟨a, T⟩` is a temporal backbone through `τ(i₀), τ(i₁)`, since the
  removed node `a` keeps its successor. But `⟨a, T⟩` is a backbone link only at `i₀`. So `j₁ = i₁` is
  impossible, and so is `j₀ < j₁ ≤ i₁`. The trace is shape-legal by Thm 4.1, so every hypothesis of the
  lemma holds. The last link of a temporal backbone need not be a backbone link when it is crossed; that
  is the whole point of hindsight. The intended statement is `i₀ = j₀ ≤ j₁ ≤ … ≤ j_k ≤ i_k`, and we
  prove it. The paper itself shows this is the intent: the lemma's clause `i₀ ≤ j_m ≤ i_m`, its
  one-line proof via Lemma 5.2, and the choice of `ι` for `contains` in Thm 7.5 ("the last state at or
  before the last crossing state in which the last crossed link is a backbone link") all fit only the
  weak form. The fix is local and nothing downstream is affected. (`lemma_5_4_false`,
  `lemma_5_4_as_stated_false`; corrected: `backbone_lemma`)
* **Typo in Lemma 5.7.** The conclusion is printed as `K_σ ∩ {u.k_σ, v.k_σ} = {u.k_σ, v.k_σ}`. That only
  says both keys are backbone keys, which is trivially true (`local_window_as_printed`). The proof of
  Thm 7.5 uses the interval form `K_σ ∩ {u.k_σ, …, v.k_σ} = {u.k_σ, v.k_σ}`, which we prove
  (`local_window`). The interval form needs only `φ_s` and the backbone being a single heap path.
* **Imprecisions that do not affect the results.**
  - The Hindsight Lemma silently uses that nodes are never reclaimed and that pointers point to
    allocated nodes. Our shape properties include both. Its proof also does not need `δ_e`; ours
    avoids it.
  - In Thm 7.5, "the transition in which `t` executes its atomic section" must mean the *successful*
    one. An `add`/`remove` may run its atomic section several times, restarting after failed
    validations.
  - Def. 7.2 is sloppy: it mixes indices of `H` and of `π`, and "linearizable with respect to a
    sequential history". We use CSLib's standard (amended Herlihy–Wing) definition.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory, sequentially consistent, in CSLib's `Impl` model with arbitrarily many
  threads (`P` any type with decidable equality). The scheduler is adversarial. There are no crashes and
  no randomness.
* The whole heap with the shared variables `H` and `T` is one base object. Its operations are the
  shared-memory accesses of Fig. 1: read `H`; `c = p.n` (atomic, as in footnote 1); read `c.k`; and the
  atomic sections of `add` and `remove`.
* Nodes are natural numbers, and node `u` is allocated iff `u < cnt`. `alloc(E)` returns the fresh
  node `cnt`, and memory is never reclaimed, as the paper assumes. The initialized state comes from
  `init()`: tail `0` with key `∞`, head `1` with key `-∞`. Keys live in `WithBot (WithTop ℤ)`.
* A null dereference sends the thread to an error state `err`. Memory safety means `err` is never
  reached.
* Threads may run many operations one after another; the paper assumes at most one per thread, so
  this is more general. Linearizability is CSLib's `Impl.Linearizable` against the set specification
  of Fig. 2, with abstract states `Set ℤ`. Wait-freedom is over infinite executions: a thread whose
  `contains` stays pending forever takes finitely many steps.
* Sections 4–5 (heap states, Fig. 4 properties, shape-legal traces, Lemmas 5.2/5.4/5.7) are stated for
  arbitrary heap traces (`HeapState N K`), independently of the algorithm, as in the paper. The trace of
  every execution of the algorithm is shown to be (data-)shape-legal.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Fig. 4 properties, Def. 5.1, 5.3, 5.5, 5.6 | `PhiH` … `PhiUB`, `DeltaH` … `DeltaBN`, `ShapeLegal`, `TemporalBackbone`, `DataShapeLegal`, `backboneKeys` | `Heap.lean` |
| Lemma 5.2 (Hindsight) | `hindsight` (core: `hindsight_node`) | `Heap.lean` |
| Lemma 5.4 (Backbone), corrected | `backbone_lemma` | `Heap.lean` |
| Lemma 5.4 as stated is false | `lemma_5_4_false`, `lemma_5_4_as_stated_false` | `Counterexample.lean` |
| Lemma 5.7 (Local Window) | `local_window` (interval form), `local_window_as_printed` | `Heap.lean` |
| Fig. 1, Fig. 2, `Abs` | `impl`, `setSpec`, `Abs` | `Algorithm.lean` |
| Thm 4.1 | `theorem_4_1_memSafe`, `theorem_4_1_state`, `theorem_4_1_step` | `Invariants.lean` |
| Thm 4.1 ⇒ traces are (data-)shape-legal | `shapeLegal_trace`, `dataShapeLegal_trace` | `Trace.lean` |
| Lemma 6.3 + 5.4 for `contains` | `temporal_traversal` | `History.lean` |
| Thm 6.4 (wait-freedom of `contains`) | `theorem_6_4` | `WaitFree.lean` |
| Lemma 7.4 | `lemma_7_4` | `Linearizability.lean` |
| Thm 7.5 (linearizability) | `theorem_7_5` (`contains` case: `contains_hindsight`) | `Linearizability.lean` |

Supporting files: `MemInv.lean` (the memory invariant, with an explicit backbone list, and the effect of
the two atomic sections on `Abs`) and `History.lean` (the history invariant carrying the hindsight
argument along executions). The generic criterion "linearization points, retroactive for read-only
operations" (`Cslib.SharedMemory.exists_isLinearization_of_points`) is staged in
`Podc/Computability/Distributed/SharedMemory/PastLinPoints.lean`.

**Not formalized.** The separation-logic proofs of the technical report [18] (replaced by our own
invariant proof of Thm 4.1). Lemma 6.3 is formalized only for `contains`, which is the only case the
paper's proofs use, and in the combined form "the current link was a backbone link at some state after
the invocation" rather than via traversal trail tails. The lazy-list variants of §8–10 are not
formalized.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The counterexample execution is evaluated by `decide` (CSLib's computable `Impl.crun`).
The same execution (one `add`, one `remove`, both succeeding) shows that the algorithm model has
non-trivial executions. CSLib candidate: `PastLinPoints.lean` (above).
