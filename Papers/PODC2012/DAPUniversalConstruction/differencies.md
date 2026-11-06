# Differences between the formalization and the paper

Paper: Ellen, Fatourou, Kosmas, Milani, Travers, *Universal Constructions that Ensure Disjoint-Access Parallelism
and Wait-Freedom*, PODC 2012; full version HAL hal-00697198v2 (numbering as there).

## Issues in the paper

The checked statements are Theorem 5 (with Lemma 4 and the claims of its proof), and the claims of Section 3 that
`Append` is value oblivious and `Search` is not. With the implied assumptions below they are true and the proof of
Theorem 5 goes through without repairs; we only had to make precise notions the paper leaves informal (below).

- ✏️ Theorem 5 is stated as "No feebly disjoint-access parallel universal construction is wait-free", without
  "linearizable", "satisfying Assumption 3" or "with at least two processes". The text says the result is about
  linearizable universal constructions and that "the proof relies on" Assumption 3, and a one-process system is
  degenerate. `theorem_5` takes them as hypotheses.
- ✏️ The wording of Assumption 3 ("the sets of base objects … during any solo execution of a sequence of consecutive
  instances") can be read as the union over the whole sequence; the proof needs per-instance sets (`B(ℓ)` is the
  set written by one instance, and "only base objects in `∪{B(k) | j ≤ k ≤ i}` can differ in `Cᵢ` and `Cᵢʲ`" is
  not justified if only the union is fixed). The intent is clear from the proof.

## Model and definitions

- **Shared memory.** CSLib's `Impl A B P L`: deterministic processes with arbitrary local states, arbitrary base
  objects `B i` given by sequential specifications, one primitive per step; returning is a separate step that
  accesses no base object (harmless). Crash failures are not modelled separately: wait-freedom
  (`Impl.WaitFree`: in every infinite execution, a process whose operation stays pending forever takes finitely
  many steps) covers them.
- **Determinism.** Only deterministic implementations. The paper's remark "if it is randomized, we fix a sequence
  of coin tosses for each process" is not formalized.
- **Allowed invocations.** We assume every process may invoke every operation (`AllowsAll`, `hall`).
- **Trivial primitives.** The paper: "non-trivial if it may change the value of the base object". We use
  "trivial = never changes the state of the base object" (`ObjSpec.ReadOnly`). For objects whose state is their
  value (registers, CAS, fetch&add, …) this is the paper's notion. CSLib base objects cannot see the caller, so an
  LL/SC object cannot keep "the caller's link" implicitly. Encoded as CSLib's `llscObj` (link set in the state),
  `LL` would be non-trivial and feeble DAP a stronger hypothesis. Encoded with versions (`versionedLLSC` in
  `NonVacuity.lean`: `LL` returns value and version and is `ReadOnly`; `SC v ver` succeeds iff the version is
  still `ver`, then increments it; the caller keeps `ver` in its local state), LL/SC behaves exactly as in the
  paper and `LL` is trivial, `SC` non-trivial. So `theorem_5_list` covers LL/SC-based implementations with the
  paper's notion of contention; no weakening.
- **"Read from" and "written to".** `B(i)` (written) = objects to which `αᵢ` applies a non-trivial primitive
  (`Impl.written`); `A(i) ∪ B(i)` = objects to which it applies any primitive (`Impl.accessed`). This is the reading
  under which the proof works (contention needs a non-trivial primitive; `βᵢʲ` may apply trivial primitives to
  objects of `A(k)`).
- **Data structures.** The paper's data structures are sequential code accessing data items through
  `CreateDI`/`ReadDI`/`WriteDI`. We abstract the code into its sequential specification and its data sets
  (`SeqDS.dataSet s o`: the items `o`'s code accesses when run from `s`). The universal construction is a map from
  such data structures to implementations. Since the proof only uses the implementation of the list, the
  impossibility does not depend on how much of the code the construction sees.
- **The list.** States are the lists of keys (only the states reachable by appends matter). Data items: `L.start`,
  `L.end`, and node `k` = the node created by the `(k+1)`-st append. Data sets from Figure 6 (`listDataSet`):
  `Append(v)` from `m` nodes: `{L.end, node m}` plus `node (m-1)` (or `L.start` if `m = 0`); `Search(v)`:
  `L.start` and the nodes up to the first one with key `v` (all if none). `Append` returns a dummy `true`.
- **State represented by a quiescent configuration.** The paper takes "the" state given by the linearization of the
  execution reaching `C`. `FeeblyDAP` requires disjoint data sets from `s` only when *every* linearization of the
  execution `α` reaching `C` ends in `s` (`RepresentsState`). This is the weakest reading of Definition 1 (hence the
  strongest theorem); in the proof the executions are sequential and the state is unique
  (`representsState_pre`).
- **Solo executions in Definition 1** may be partial (any number of steps, `soloPrefix`), and the two operations are
  performed by two different processes (`p₁ ≠ p₂`). The proof applies Definition 1 to a partial solo `Search(0)`;
  under wait-freedom one could equivalently use the complete one.
- **Assumption 3** is formalized per instance (`ImplValueOblivious`): for every reachable quiescent `C`, process
  `r` and parameter sequences `f`, `g`, the `n`-th instance `op (f n)` of `r`'s solo sequence from `C` accesses and
  writes the same base objects as `op (g n)`. It is stated without requiring the solo runs to terminate; under
  wait-freedom (the only case the theorem uses) they do, so this changes nothing. Value obliviousness of an
  operation of a data structure (`SeqDS.ValueOblivious`) quantifies over the states reachable from the initial
  state.
- **Two processes.** `theorem_5` assumes two distinct processes `p ≠ q`.
- **`theorem_5` vs `theorem_5_list`.** The paper applies a universal construction only to data structures given by
  code, whose data sets are determined by that code. Our `SeqDS.dataSet` is a free annotation, and
  `UniversalConstruction.FeeblyDAP`/`Linearizable`/`ValueObliviousAssumption` quantify over all `SeqDS`, including
  annotations no code produces. With all data sets empty, feeble DAP forbids any contention between solo
  executions from a quiescent configuration, which together with linearizability and obstruction-freedom is
  already contradictory (a `Search(1)` from `C₀` that does not see `Append(1)`'s writes answers the same from
  `C₁`). So `theorem_5` alone would be weaker than the paper's claim; the faithful statement is
  `theorem_5_list`, whose hypotheses concern only the implementation of the list with the data sets of Figure 6,
  and `theorem_5` is derived from it.

## Proof

- Indices: we index appends from `0` (`f₀ k = k + 1` appends `Append(k+1)`); `W k` / `Ac k` are the paper's
  `B(k+1)` / `A(k+1) ∪ B(k+1)`; `Dc i` is `Cᵢ` after `p`'s invocation of `Search(0)`; `blen t D` is the length of
  `β` for the paper's `j = t + 1`; `M i` is the length of `βᵢⁱ⁻²`.
- Lemma 4 is `blen_stable` (iterated first part, with the agreement of `p`'s states along `β`) and `M_mono`.
- The paper's claim "`α'` is a valid execution" is `run_exec`: each prefix ending with `γ_{k+4}` reaches the
  configuration "`α₁ ⋯ α_{k+4}` then `β_{k+4}^{k+2}`", proved by commuting `p`'s fragment with the next append.
- "There exists `j > i` with `γⱼ` nonempty" is `M_lt` (`M i < M (i+3)`), following the paper's argument through
  `C_{ℓ-1}^{ℓ-3}`; `M_unbounded` and a counting argument give infinitely many steps of `p`, and `rest_labels`
  shows `p` never returns in `α'`.

## Not formalized

- Section 5–6: the DAP-UC algorithm, Theorem 6 (Theorem 24, Theorem 32, Lemmas 33–41), Definition 2 and the
  conflict graph.
- The remarks that feeble DAP is weaker than every DAP variant of Section 2, and that the impossibility extends to
  TM implementations that re-execute aborted transactions and abort each transaction finitely often (abstract and
  Section 2; no proof is given).
