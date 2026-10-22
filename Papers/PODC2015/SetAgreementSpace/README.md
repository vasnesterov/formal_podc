# On the Space Complexity of Set Agreement — PODC 2015

Carole Delporte-Gallet, Hugues Fauconnier, Petr Kuznetsov, Eric Ruppert. *On the Space Complexity of Set
Agreement.* PODC 2015. DOI [10.1145/2767386.2767406](https://doi.org/10.1145/2767386.2767406). Formalized
version: arXiv [1505.02690](https://arxiv.org/abs/1505.02690) v2 (full version with appendices); numbering
follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The algorithms of Figure 3 (one-shot) and Figure 4 (repeated) are safe, but
they are **not** `m`-obstruction-free, and not even obstruction-free. This holds for every `1 ≤ m ≤ k < n`.
So the termination part of Theorems 7 and 8, as proved through these algorithms, is false. A one-line
change to the adoption rule repairs Figure 3. For the repaired one-shot algorithm we prove the full
statement of Theorem 7, in its snapshot version. The repeated lower bound, Theorem 2 (`n + m − k`
registers), is correct. We prove it from the wait-free set-agreement impossibility, which is a hypothesis.

## Mistakes in the paper

* **Figures 3 and 4 livelock: Lemma 5 is false.** The adoption rule (lines 11–13) makes a process adopt
  the *value* `w` of a duplicated pair `(w, q)` written by another process `q`. The process then writes
  `(w, id)`. This is a *different pair*, so it does not destroy the duplicate. Smallest case: `n = 2`,
  `k = m = 1`, `r = 3` components. `p₁` runs solo and decides, leaving `A = [(v,p₁),(v,p₁),(v,p₁)]`.
  Then `p₀` runs solo forever. It writes `(v₀,p₀)` into `A[0]` and sees two different pairs (more than
  `m = 1`), so it does not decide. Line 11 holds: there is no `⊥`, no copy of its own pair, and a
  duplicated pair. It adopts `v`, writes `(v,p₀)` into `A[0]`, and is in the same situation again,
  without ever changing `i`. Both processes are correct, and `p₀` never terminates.
  For general `m` we use crashed processes `1,…,m` that leave `m` different pairs and a duplicate in
  `A[1..r−1]`. With them the livelock exists for every `1 ≤ m ≤ k < n` with `r = n + 2m − k`, even when
  all inputs are equal.
  The proof of Lemma 5 breaks in Case 2: "as `p` changes its preferred value … it must have found
  another pair that appears twice". In the example, `p` re-adopts the same value forever. Figure 4
  inherits the bug verbatim: run everything above inside the first instance. So the paper's proofs of
  the upper bounds of Theorems 7 and 8, and of the "exactly `n` registers for obstruction-free
  repeated consensus" corollary, are invalid. (`fig3_not_mObstructionFree`, `fig3_not_obstructionFree`,
  `fig4_not_mObstructionFree`; summary `theorem7_figure3_false`, `theorem8_figure4_false`)
  arXiv v2 is the latest version and has the same Figure 3. The authors' PODC'15 talk slides give the
  same rule: "if … some other pair `(v, id′)` appears twice then `pref ← v`".
  *Repair.* At line 11, also require that the value of the first duplicated pair differs from `pref`;
  otherwise advance `i` (line 14). The repaired Figure 3 is `m`-obstruction-free. The new Case 2 of
  Lemma 5: after some time all duplicates lie in the frozen components, so the first duplicated value
  `w*` is constant. A process that adopted `w*` must then advance. Safety (Lemmas 3–4, `k`-agreement)
  is unaffected. (`theorem7_corrected`)
  The same repair of Figure 4 passes bounded exhaustive model checking (`n = 2`, `k = m = 1`, two
  instances per process; see `differencies.md`). It is **not** proved in Lean, so the repeated upper
  bound `min(n + 2m − k, n)` (Theorem 8) remains unverified.
* **Lemma 1 is used outside its statement (statement true).** Lemma 1 talks about executions from the
  initial configuration. Theorem 2 applies it from a reachable configuration `D_j`, to the fresh
  `(s+1)`-th instance. The reduction to the wait-free impossibility works there too: restart the
  algorithm from `D_j`. We prove that generalized form. (`lemma1`)
* **Lemma 3 holds only for one-shot executions (not a mistake).** If a decided process were invoked
  again, its old and new pairs could coexist. The algorithm is one-shot, so the paper's statement and
  proof are fine. Our Lean proof uses a stronger inductive invariant. (`lemma3`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`): `n` deterministic processes,
  atomic base objects, invocations by the environment, executions as label lists, crash = stop taking
  steps.
* High-level object `saObj V`: `Propose v` returns a value.
  - One-shot `k`-set agreement: `kSetAgreement`, validity plus at most `k` outputs, on one-shot
    executions.
  - Repeated `k`-set agreement: `Impl.SolvesRepeated`, the conditions `Out_i ⊆ In_i` and
    `|Out_i| ≤ k` for every instance `i`, in every execution.
* `m`-obstruction-freedom (Taubenfeld): `Impl.MObstructionFreeOn m E`. In every infinite execution
  where at most `m` processes take infinitely many steps (invocations count as steps), a process whose
  operation stays pending forever takes only finitely many steps. One-shot algorithms use one-shot
  executions; the repeated problem uses all executions.
* Upper bounds: the algorithms use one atomic snapshot object with `r = n + 2m − k` components
  (`snapObjOpt`). Implementing the snapshot from registers ([5], [1,13] in the paper) is not
  formalized.
* Lower bound: an arbitrary algorithm over a finite family of read/write registers (`RegFamily ι W w₀`)
  with arbitrary local states and values. It assumes all invocations are allowed and that the inputs
  include `|P|` distinct values, as in the paper's proof, where processes propose their ids.
* The wait-free set-agreement impossibility (Borowsky–Gafni, Herlihy–Shavit, Saks–Zaharoglou) is the
  explicit hypothesis `BGImpossibility`. It says that no wait-free register algorithm, from any
  initial state, solves `(q−1)`-set agreement among `q` processes with fixed distinct inputs.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (generalized to reachable configurations and fresh instances; from `BGImpossibility`) | `lemma1`, `Lemma1Prop` | `LowerBoundLemma1.lean` |
| Theorem 2 (`≥ n + m − k` registers for repeated `m`-OF `k`-set agreement) | `theorem2'` (from BG), `theorem2` (from `Lemma1Prop`) | `LowerBound.lean` |
| Figure 3 | `fig3 false` (`fig3 true` = repaired) | `Algorithm.lean` |
| Lemma 3 | `lemma3`, `lemma3_injOn` | `Lemma3.lean` |
| Lemma 4, validity and `k`-agreement (both versions) | `safety_inv`, `fig3_solves` | `Safety.lean` |
| Lemma 5 false for Figure 3: livelock | `fig3_livelock`, `fig3_not_mObstructionFree`, `fig3_not_obstructionFree` | `Counterexample.lean` |
| Lemma 5, Corollary 6 (repaired algorithm) | `Liveness.lemma5`, `Liveness.cor6`, `fig3Fixed_mObstructionFree` | `Liveness.lean` |
| Theorem 7 (snapshot version): false for Figure 3, true for the repair | `theorem7_figure3_false`, `theorem7_corrected` | `Main.lean` |
| Figure 4 and Theorem 8: Figure 4 livelocks | `fig4`, `fig4_livelock`, `theorem8_figure4_false` | `Repeated.lean`, `Main.lean` |

**Not formalized.**
* The repaired Figure 4: Lemmas 12–14 and the corrected Theorem 8. It is only model-checked.
* Snapshot-from-registers implementations.
* Section 5: Lemma 9 and Theorem 10, the anonymous lower bound.
* Section 6: Theorem 11, the anonymous algorithm.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
* Non-vacuity of the hypotheses:
  - `Lemma1Prop` is satisfiable: `lemma1Prop_trivialImpl`.
  - `MObstructionFreeOn` is not trivially true: it is refuted for Figure 3.
  - `BGImpossibility` is the standard theorem: fixed distinct inputs, validity required, and
    termination forced by wait-freedom.
* Model from CSLib `SharedMemory/{Model,Task,Progress,Covering,FullInfo}`.
* Shared code staged as CSLib candidates:
  - `Podc/Computability/Distributed/SharedMemory/MObstructionFree.lean`: `m`-obstruction-freedom, and
    "a solo livelock refutes it".
  - `Podc/Computability/Distributed/SharedMemory/Splice.lean`: hidden fragments under block writes,
    restarting an implementation from a configuration, and m-OF ⇒ wait-freedom for at most `m`
    invokers.
