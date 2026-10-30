# MemSnap — PODC 2024

Prasad Jayanti, Siddhartha Jayanti, Sucharita Jayanti. *MemSnap: A Fast Adaptive Snapshot Algorithm
for RMWable Shared-Memory.* PODC 2024. DOI
[10.1145/3662158.3662820](https://doi.org/10.1145/3662158.3662820). Formalized version: the
proceedings version (no arXiv version); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The main result, Theorem 7.3, holds. MemSnap (Algorithm 1)
is a linearizable, wait-free checkpointable object, with at most 9 shared-memory steps per
operation. This holds for every set of updaters and every family of RMW primitives. We prove it by
the paper's own route, meta-configuration tracking. Lemma 7.1 (the Forwarding Invariant `I₁`) holds
as stated. **Lemma 7.2 as printed is false.** The third disjunct of the set `Q` (Figure 2) lacks
the condition `x_μ = X`. With that condition, which the paper's prose states, the lemma holds and
gives `P ≠ ∅`. The paper omits the proofs of both lemmas; we supply them.

## Mistakes in the paper

* **Lemma 7.2 is false as printed; corrected version proved.** For a component `j` with
  `B[j].seq ≠ X`, the third disjunct of `Q` allows `p.snap[j] = a_μ` for every process `μ` at line 12
  whose CAS would succeed (`b_μ = B[j]`). It does not ask that the CAS make `B[j].seq` equal to `X`.
  If `μ` read `X` before the latest click (`x_μ < X`), then `a_μ` can be stale. Counterexample: one
  component, initially `0`; updaters `ν`, `μ`; scanner `σ`.
  1. `ν` starts `update(write 1)` and finishes `forward`.
  2. `μ` starts an update and reads `B = (0, 0)`.
  3. `σ` clicks (`X = 1`).
  4. `μ` reads `X = 1` and `A = 0`; it is now at line 12.
  5. `ν` writes `A = 1` and returns.
  6. `σ` clicks again (`X = 2`) and is at line 2.

  `Q` now contains the possibility `val = 1`, `snap = 0`, click linearized (`S = ∅`, third disjunct
  with witness `μ`). No linearization realizes it: `ν`'s write returned before the second click was
  invoked, so the snapshot holds `1`. Hence it is not in `P`, and `Q ⊆ P` fails. The text before the
  lemma says the third disjunct is about "a successful CAS at Line 12 that will cause `B[j].seq` to
  become equal to `X`". Adding `x_μ = X` makes the lemma true, and `P ≠ ∅` follows as the paper
  says. The fix is local, and the intent is in the paper; there is no published proof that uses the
  wrong version. So this counts as a slip with evident intent (rule R3), not a false claim.
  (`Counterexample.lemma_7_2_false`, `Counterexample.not_tracked`; corrected: `lemma_7_2_fixed`)
* **Lemma 7.1: `I₁` is an invariant, but not an inductive one (proof omitted in the paper).** Part (6)
  covers a process in its second `forward` iteration only at line 9. Once such a process `μ` has
  read `b_μ = B[i]` and is at lines 10–12, no part of `I₁` records that every process `μ'` poised
  with `b_μ' = B[i]` has `x_μ' ≥ x̂_μ`. Then a successful CAS of such a `μ'` with `x_μ' < x̂_μ`
  would break Part (7) from a state that satisfies `I₁`. That state is unreachable, but an
  induction on `I₁` alone fails. We extend Part (6) to that case and add a few shape facts
  (`FInv`); then `I₁` follows (`lemma_7_1`). The non-inductiveness is argued by hand, not in Lean.
* **Small imprecisions.** `X ← X + 1` is declared atomic because "only the scanner writes `X`". We
  model it as a read followed by a write, which needs no such assumption. The proof of Theorem 7.3
  appeals to the tracker theorem of [21] for "the augmentation satisfies the two rules"; we prove
  this soundness directly in CSLib's linearizability model (`tracked_of_mem_PP`,
  `Poss.linearizable_of_tracked`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory (CSLib `Impl`/`IsLinearization`), arbitrary adversarial scheduler (a
  crashed process is one that is never scheduled again; wait-freedom covers it), deterministic
  processes, no randomness. Any type `P` of processes (possibly infinite)
  with a designated scanner `σ`. `σ` only clicks and observes; every other process only updates
  (`Allowed`).
* Components: any type `K` (the paper has `[1, m]`). Component words: an arbitrary deterministic
  sequential specification `W` (any RMW primitives with any responses: read, write, CAS, F&A,
  FAS, …).
* Base objects: `A[i]` (a `W`-word that also supports `read`), `B[i]` (a CAS word over
  `(val, seq)` pairs, the paper's double-word CAS), and `X` (a read/write register over `ℕ`, so
  counters are unbounded). Every primitive access is one atomic step.
* Algorithm 2 is a deterministic ghost run `arun` next to Algorithm 1. Its ghosts are `x̂_π` and
  the meta-configuration `P`, updated by the rules of Algorithm 2 (`augStep`). Its configuration
  component is exactly Algorithm 1 (`arun_fst`, `exists_arun`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 7.3: linearizable | `theorem_7_3_linearizable` | `Main.lean` |
| Theorem 7.3: wait-free | `theorem_7_3_waitFree` | `Main.lean` |
| Theorem 7.3: `O(1)` time (≤ 9 accesses per operation, 2 per click) | `theorem_7_3_steps` | `Main.lean` |
| `P ≠ ∅` is an invariant of Algorithm 2 | `P_nonempty` | `Main.lean` |
| Lemma 7.1 (Figure 1, `I₁`) | `lemma_7_1` (statement `I1`; inductive form `FInv`) | `Forwarding.lean` |
| Lemma 7.2 (Figure 2, `I₂`), as printed: **false** | `Counterexample.lemma_7_2_false` | `Counterexample.lean` |
| Lemma 7.2, corrected (`x_μ = X` in the third disjunct) | `lemma_7_2_fixed` | `Possibilities.lean` |
| Soundness of the augmentation ("satisfies the two rules" + tracker theorem of [21]) | `tracked_of_mem_PP`, `Poss.linearizable_of_tracked` | `Augmented.lean`, `Podc/…/MetaConfig.lean` |
| Section 4 (specification), Algorithms 1 and 2 | `checkpointable`, `memSnap`, `augStep`/`arun` | `Defs.lean`, `Augmented.lean` |

`QSet σ fixed C G` is the set `Q` of Figure 2 (`fixed = false`: as printed, `fixed = true`:
corrected), stated with the paper's `UnLin`, `TransitionsOK` (Definitions 6.1, 6.2) and base
possibility `p*` (`pstar`).

**Not formalized.** Space complexity (the implementation uses `2|K| + 1` base objects by
construction). The far-future-linearization scenario of §5.3. Parallel observation and dynamic
addition (§8).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The concrete execution of the counterexample is evaluated by `simp` (`run_exec`), so
the allowed-invocation discipline is satisfiable. A bounded explicit-state model checker
([`modelcheck/mc.py`](modelcheck/mc.py), not part of the Lean development) computes the paper's
`P` exactly. On one component, two updaters (one operation each), two clicks and one observe
(about 2·10⁶ states) it found the violation of the printed `I₂` and none of `I₁` or of the
corrected `I₂`. The generic meta-configuration tracking soundness (CSLib candidate) is in
`Podc/Computability/Distributed/SharedMemory/MetaConfig.lean`.
