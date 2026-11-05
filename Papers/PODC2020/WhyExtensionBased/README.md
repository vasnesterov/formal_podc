# Why Extension-Based Proofs Fail — PODC 2020

Dan Alistarh, James Aspnes, Faith Ellen, Rati Gelashvili, Leqi Zhu. *Brief Announcement: Why
Extension-Based Proofs Fail.* PODC 2020. DOI
[10.1145/3382734.3405743](https://doi.org/10.1145/3382734.3405743). Formalized version: the full
version, arXiv [1811.01421](https://arxiv.org/abs/1811.01421) v3 (August 2020, NIS model, the model of
the brief announcement); numbering follows it.

**Verdict: 🛠️ Proof repaired.** Theorem 5.7 is true: for every `k ≥ 2`, no extension-based prover can
refute every wait-free `k`-set agreement protocol in the NIS model. We prove it for any number of
processes and any finite input set. The adversary of Section 5 needs genuine repairs. Its answers
`none` to output queries are not shown to stay correct after later subdivisions, and its
schedules in Cases 1 and 2 rely on an unstated invariant. The proof of Lemma 4.13 also ends with an
unjustified inequality. All three are fixed. The Lean theorem covers only provers whose infinite
chain is eventually played alone (see Scope below).

**Scope of the Lean theorem.** The shared game counts an infinite chain of queries as a prover win
only if, from some point on, the prover plays nothing but that one chain. The paper (§3) also lets a
prover interleave finitely many chains in a phase, one of which is infinite. So our provers are a
strict subclass of the paper's, and `theorem_5_7` does not formally imply the paper's Theorem 5.7.
The paper's argument (every chain of phase 1 is finite, Lemma 5.6, and a phase has finitely many
chains and output queries) covers interleaving. Our proof of Lemma 5.6 (`IsChain.false`) assumes
that the adversary state changes only through the chain's own queries, so it would need to be
generalised. This case is not formalized.

## Mistakes in the paper

No mistakes in the statements.

### Typos and slips
- §5 defines `X_t(a)` as the set of descendants in all levels `V_r`, `r ≤ t`. The adversary instead
  adds sets of vertices of `G_t` to `X_t(a)`. Invariant 6 only makes sense for the vertices of `G_t`:
  a non-terminated vertex of a lower level is not a vertex of `G_t`.
- Lemma 5.5's proof writes `χ(N_t(a), Δ)` and `χ(T_t(t), δ)` for `χ(N_t(a), δ)` and `χ(T_t(a), δ)`.

## Proof gaps (statements true)

### 🛠️ Theorem 5.7 (adversary, output queries answered `none`; Lemma 5.5, invariant 6)
The adversary answers `none` by looking only at the vertices of `G_t`, although its promise covers all
future `Q`-only executions from `C`, and Lemma 5.5 asserts without proof ("by the definition of `χ`")
that invariant 6 survives a subdivision.

**Impact.** The correctness of the adversary, hence the proof of Theorem 5.7, is not established
as written. Theorem 5.7 is true: we prove it with a modified rule for output queries and a stronger
invariant (`not_hasEBProof_setAgreement`, `oq_spec`).

**Details.** After `t` is incremented, `X_{t+1}(a)` contains the new descendants `(i, τ)` of the
recorded vertices. A carrier `τ` may mix a vertex `u` of Case 3, which is adjacent to `T_t(b)` only
through *another* clique, with vertices of other processes. Then `(i, τ)` has seen `a`, so it is not
in `N_{t+1}(a)`. It is adjacent to a terminated vertex only if some clique contains `τ` and a
terminated vertex, which need not exist. The paper gives no argument that such vertices are protected.
This matters twice. Later in phase 1, the adversary terminates a vertex with `a` whenever this keeps
the invariants, and it uses invariant 6 to argue that this vertex is not in `X_t(a)`. In phase 2, it
outputs `a` at every vertex of `F'` that is not adjacent to a terminated vertex. Either step could
make a vertex in `X_t(a)` output `a`, contradicting an earlier `none`. We did not try to build a
prover that triggers this.

**Repair.** For a query `(C, Q, y)` our adversary considers the `Q`-descendants of `C` at *all*
levels, in the protocol where all undecided states stay active (`oq`).
* If one has already output `y`, it returns a schedule to it.
* Otherwise, if some undecided descendant with at least `t` rounds has seen `y` and is not adjacent
  to a vertex terminated with another value, it lets that process run alone until it is ahead of
  everybody. It then subdivides and terminates the next state with `y`. That state is safe
  (`safe_solo`); the paper's Cases 1 and 2 are special cases.
* Otherwise it answers `none`. Then every undecided descendant is *protected*: it has not seen `y`,
  or it is adjacent to a vertex terminated with another value (`RecOK`).

Protection survives later terminations (`adj_transfer`, which keeps an edge alive by restricting an
execution to the causal past of its two endpoints). A safe vertex is never protected, so no later
termination contradicts a `none` (`AInv.terminate`, `dstar_none`).

### 🛠️ Theorem 5.7 (adversary, Cases 1 and 2 of output queries; minor)
The `Q`-only schedule "from `C` that results in process `p_i` being in state `v = (i, {u})`" exists
only if no process has updated `S_{t+1}` in `C`, which the paper never states (invariant 3 allows
`2t + 1` steps).

**Impact.** Statement true. The schedule exists for the paper's own adversary, so this is a missing
justification, not an error. Our adversary is different and uses its own construction
(`oq_some_of_unprot`).

**Details.** The paper's strategy keeps a stronger, unstated invariant. After every response,
active processes are at levels `< t`, and processes at level `t` are terminated (invariant 2 and
the query rule). So nobody has written to `S_{t+1}` in a reached configuration. A schedule that
brings `p_i` to `u` can be cut to the causal past of `u`, and then `p_i p_i` gives `(i, {u})`.
If some process had written to `S_{t+1}`, as invariant 3 permits, `p_i`'s scan would return
`(i, τ)` with `|τ| ≥ 2`. That vertex can be adjacent to vertices that have not seen `y`.

**Repair.** In Lean, undecided states are active. So `p_i` runs alone, round after round, until no
other process has written to the next snapshot object. Each new state stays unprotected
(`unprot_round`), and the next solo state is safe (`safe_solo`).

### 🛠️ Lemma 4.13 (subdivision increases distances)
The last inequality, "distance(A, A'∩C) + 2 + distance(B'∩C, B) > distance(A, B)", does not follow
from the preceding decomposition of shortest paths, which only gives the reverse inequality (the
points of `A'∩C` and `B'∩C` closest to `A` and `B` need not be adjacent).

**Impact.** Statement true; proved by a different argument (`Far.subdiv_succ`, `far_layer_succ`).

**Repair.** We use a carrier argument. Every vertex of `G_{t+1}` has a carrier in `G_t`, and the
carriers of adjacent vertices lie in a common clique. Mapping a walk of `G_{t+1}` to its carriers
gives a walk of `G_t` that is no longer. If the image walk uses an edge between two active vertices,
their carriers are nested, so one step can be saved. The same argument gives Lemma 4.11 directly
(`Far.subdiv`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **NIS model** (shared with the PODC'21 companion `ExtensionBasedReductions`). Asynchronous,
  wait-free, deterministic, full information. `n` processes form any finite type, and each process
  updates and then scans each snapshot object `S_1, S_2, …` at most once. A protocol is its decision
  function `δ`, consulted after each scan. There is no randomness, and crashes are processes that stop
  being scheduled.
* **Extension-based proofs.** A prover is a deterministic strategy on the history. It uses queries
  `(C, q)`, output queries `(C, Q, y)` and phase ends, as in §3. Output queries may name any set `Q`
  (the paper requires `Q` active), which only helps the prover. The protocol may answer correct
  output queries adversarially. The prover wins if all its moves are legal and it reaches a violating
  configuration, or plays infinitely many phases, or from some point on plays one infinite chain of
  consecutive queries.
* **Task.** `k`-set agreement `setAgreement X k`: every input vector over a finite set `X` is allowed,
  and the outputs are inputs, with at most `k` distinct values. The paper's case is
  `X = {0, …, k}` and `n > k`.
* **Graphs `G_r`.** Defined semantically: two states are adjacent if they belong to different
  processes and occur together in a reachable configuration (`Adj`). The paper's `N_r(a)` is replaced
  by the set `Uset` of vertices that have not seen `a`, which is its vertex set by Lemma 5.3. The
  adversary's partial protocol treats undecided states as active (`AState.term`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 5.7 (`n > k ≥ 2`, inputs `{0,…,k}`; provers whose infinite chain is eventually played alone, see Scope) | `theorem_5_7` | `Main.lean` |
| Theorem 5.7, general form (any `n`, any finite inputs, `k ≥ 2`; same restriction) | `not_hasEBProof_setAgreement` | `Main.lean` |
| Lemma 4.11 (carrier form) | `Far.subdiv`, `far_layer` | `Podc/.../NIS/Subdivision.lean`, `Layers.lean` |
| Lemma 4.13 (carrier form) | `Far.subdiv_succ`, `far_layer_succ` | `Podc/.../NIS/Subdivision.lean`, `Layers.lean` |
| Lemma 4.5/4.10 ingredients (carriers, nesting) | `Adj.car_cases`, `Adj.nested`, `car_Tset`, `car_Uset` | `Podc/.../NIS/Layers.lean` |
| Proposition 5.1 / 5.2 (as carrier facts) | `car_Tset`, `car_Uset`, `Occ.seen_iff_car` | `Podc/.../NIS/Layers.lean` |
| Lemma 5.4 | `actCut_T` | `Defs.lean` |
| Lemma 5.5 (distances and invariants after subdivision) | `subdiv_far`, `AInv.subdiv` | `Defs.lean`, `Actions.lean` |
| Strategy for queries in phase 1 | `qstep`, `qstep_spec`, `AInv.terminate` | `Actions.lean` |
| Strategy for output queries in phase 1 (repaired) | `oq`, `oq_spec`, `safe_solo` | `OutputQuery.lean` |
| "The prover does not win in phase 1" (agreement, validity) | `not_violates_p1` | `Main.lean` |
| Lemma 5.6 (chains in phase 1 are finite) | `IsChain.false` | `Chain.lean` |
| Strategy for later phases | `dstar`, `dstar_none`, `depth_le`, `not_violates_dstar` | `Phase2.lean` |
| Non-vacuity: some task has an extension-based proof | `hasEBProof_setAgreement_zero` | `NonVacuity.lean` |

**Proof remarks.**
* Lemma 5.6 uses the input of the process with the smallest view of `S_r` as the common seen
  value, instead of "the first process to scan `S_{t'+2}`" (`common_seen`).
* The completion at the start of phase 2 assigns values on all states with `t + 1` rounds, not only
  on `F'`; states outside `F'` are never reached by the prover.

**Not formalized.** Section 3's example (the FLP-style valency proof is extension-based). Lemmas
4.4–4.9 and Corollary 4.9: connectivity is not needed, and the χ-construction is replaced by the
semantic graph. Lemma 5.3 is avoided by working with `Uset`. Provers that interleave several
chains, one of them infinite (see Scope above and `differencies.md`, item 8).

**Trust.** No `sorry`. `theorem_5_7` and `not_hasEBProof_setAgreement` use only `propext`,
`Classical.choice` and `Quot.sound`. Non-vacuity: `hasEBProof_setAgreement_zero` shows that the game
can be won (`0`-set agreement has an extension-based impossibility proof). The NIS model and the game
come from `Podc/Computability/Distributed/NIS/{Model,Game}.lean`, staged by the PODC'21 companion
`ExtensionBasedReductions`.

**Infrastructure (CSLib candidates, staged in `Podc/Computability/Distributed/NIS/`).**
* `Views.lean`: causal past (`InPast`, `Seen`) and structural facts about reachable configurations. It
  also has the restriction lemma (`exec_restrict`), truncation to a level (`trunc`) and keeping a
  causal past (`exists_sched_restrict`).
* `Layers.lean`: the layer graphs `G_r`, carriers, persistence of edges (`adj_transfer`).
* `Subdivision.lean`: abstract distance lemmas for subdivided graphs.
