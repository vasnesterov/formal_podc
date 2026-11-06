# Easy Impossibility Proofs for k-Set Agreement — PODC 2011

Martin Biely, Peter Robinson, Ulrich Schmid. *Easy Impossibility Proofs for k-Set Agreement in
Message Passing Systems.* PODC 2011 (brief announcement). DOI
[10.1145/1993806.1993846](https://doi.org/10.1145/1993806.1993846). Formalized version: arXiv
[1103.3671](https://arxiv.org/abs/1103.3671) v2 (full version, latest arXiv version, March 2011);
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Weakened.** Theorem 1, the paper's main tool, is saved by local repairs and its asynchronous
consequences hold: k-set agreement is impossible with `f` crashes when `k ≤ (n−1)/(n−f)` (Theorem 2 with
asynchronous processes, Corollary 5, by the paper's reduction to FLP), and with up to `f < n` initially dead
processes it is solvable iff `kn > (k+1)f` (Theorem 8). But the claim that Theorem 2 tightly captures the
impossibility is lost: its bound is not matched, and the exact border is proved only for initial crashes, by a
separate partitioning argument. The failure-detector part (Section VII) was not checked.

## Mistakes in the paper

### ⚠️ Section VI opening and contribution list ("Theorem 2 tightly captures the impossibility")
The bound `(n−1)/(n−f)` of Theorem 2 is not matched by the solvability bound `f/(n−f)` for initial crashes,
because the two results are about different failure models.

**Impact.** A tight border is proved only in the initial-crash model, by a separate partitioning argument
(`theorem8`). Tightness of Theorem 2's own bound is not saved.

**Details.** Theorem 2 assumes a different and harsher failure model (`f − 1` initial crashes plus one crash
during the run). Example: `n = 5, f = 3, k = 2` is impossible under Theorem 2's failures but solvable with initial
crashes only (`theorem2_vs_theorem8`).

### 🔧 Theorem 1 (unstated property of the model)
Theorem 1's proof tacitly assumes that the processes of `D̄` cannot decide a value proposed only in `D`,
and without this the theorem fails in a model where process 0's input is fixed
(`Abstract.Counterexample.theorem1_statement_false`).

**Impact.** The theorem fails only in the literal "arbitrary system model" generality the paper claims; the
statement is under-specified. In the paper's own models the missing hypothesis holds, and the applications
are not affected. Repaired by one added condition (E): `Abstract.theorem1_corrected`.

**Details.** Fact 1 ("in every run of `R(D̄)` all of `D̄` decide on a common value") is derived from (B)
and k-agreement alone. Then `A|D̄` is said to solve consensus in `M'`. Both steps need the unstated
property. Otherwise `D̄` may split between `v₁` and a new value `w`, which together with
`v₁, …, v_{k−1}` are still only `k` values, and `A|D̄` need not be valid in `M'`.

Counterexample: `n = 3`, `k = 2`, `D₁ = {0}`, `D̄ = {1, 2}`, no communication, and process 0 always
proposes 0 in `M`. "Everybody decides 0" solves consensus in `M`, yet (A)–(D) hold, with `M'` = two
silent processes with inputs in `{1,2,3}`.

The counterexample needs a model in which `D̄`'s view is correlated with `D`'s inputs (here: process 0's
input is fixed). The paper's models ([DDS87]-style, all inputs `x_q ∈ V` possible, admissibility
independent of input values) exclude this. There the missing hypothesis follows by changing the inputs
of `D`.

### 🔧 Theorem 1, condition (B) (fixed values `v_i`)
Condition (B) cannot hold as written in the applications: the values `v_i` are fixed in advance, so a
run of `R(D̄)` in which a process of `D̄` proposes `v₁` has no `D̄`-indistinguishable partner in
`R(D, D̄)` (`Abstract.condB_fails`).

**Impact.** The statement is under-specified: the values must be allowed to depend on the run, and the proof
works verbatim then (`Abstract.theorem1_corrected`).

**Details.** `R(D, D̄)` requires `v_i` to be proposed in `D`. With arbitrary distinct inputs (Theorems 2
and 10) such runs exist.

### 🔧 Theorem 1, proof ("Therefore, we have that, in fact, ρ ∈ R(D̄)")
"Clearly ρ ∈ R(D̄)" does not follow from indistinguishability *until decision*.

**Impact.** Requiring the runs given by (D) to lie in `R(D̄)` repairs it, and this holds by construction in
the applications (`Abstract.theorem1_corrected`).

**Details.** A process of `D̄` that decided early may hear from `D` in ρ before the other processes of
`D̄` decide.

### 🔧 Theorem 1, proof (termination of `A|D̄`)
Termination of `A|D̄` in `M'` is never argued: a process correct in `ρ'` might be faulty in the compatible run ρ.

**Impact.** One clause added to (D), preserving correctness, closes the gap, and it holds in the applications
(`Abstract.theorem1_corrected`). Condition (A) is never used.

### 🔧 Section VI ("complete and consistent knowledge of G after the second stage")
The claim that processes have "complete and consistent knowledge of G" after stage 2 is too strong: a process only
learns its ancestors.

**Impact.** The algorithm is correct as intended (`InitDeadAlg.kSafe`).

**Details.** Ancestor knowledge suffices, but one must also argue that a chosen root's ancestor set is frozen once
all its ancestors have chosen their in-lists.

### ✏️ Slips
* Theorem 8 (in the form `kn > (k+1)f`) fails for `f = n ≤ k`, where "decide your own input" works
  (`theorem8_false_of_f_eq_n`, `theorem2_false_of_f_eq_n`). The paper implicitly assumes `f < n` (its sets `D_i` of
  size `n − f` must be nonempty). Theorem 2's bound `(n−1)/(n−f)` is undefined at `f = n`; in the multiplied-out form
  `k(n−f) ≤ n−1` it would fail for `f = n = k`.
* Lemma 6 needs a nonempty graph: the empty graph has no source component (`SourceComp.exists_sourceComponent`).
* For `k = 1`, what Section VI chooses is a source component, not a "clique" (a fully connected subgraph).

### Typos
* In the proof of Theorem 10, "applying Theorem 2" should be Theorem 1.
* The proof of Lemma 7 cites "the previous theorem", meaning Lemma 6.

## Proof gaps (statements true)

### 🔧 Theorem 8, "only if" (proved only for `kn = (k+1)f`)
The paper proves impossibility only for the border case `kn = (k+1)f` and for `kn < (k+1)f` relies on
"Theorem 2 tightly captures the impossibility", which does not transfer.

**Impact.** The paper's partitioning argument works unchanged for all `kn ≤ (k+1)f`, with `k+1` groups of size
`n−f` (`initDead_impossible`).

**Details.** Theorem 2's failure model is harsher than initial crashes, so its impossibility does not transfer, and
its bound `(n−1)/(n−f)` is not `f/(n−f)`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous message passing on top of CSLib's FLP model (`Cslib.FLP.Algorithm`), with `n`
  processes, deterministic state machines and reliable, unordered channels. A step receives one
  message and atomically updates the state, sends messages and possibly decides.
* A crash means the process stops receiving; crashes are clean (no partial last broadcast). This
  adversary is weaker than the paper's, so our impossibilities imply the paper's.
* `KAlgorithm` lets a process have an input in an arbitrary `V`. Messages arriving before a
  process' first step are buffered (only restricts schedules).
* k-set agreement: k-agreement and validity in every reachable state, for faulty processes too;
  termination of every non-faulty process in every admissible infinite run.
* Failure models: `InitDead f` (up to `f` processes never take a step, all others correct),
  `OneCrash f` (Theorem 2's pattern: `f − 1` initially dead plus one more crash) and `Crash f`
  (CSLib's runs with ≤ `f` faulty processes).
* Theorem 2 is proved for **asynchronous** processes (Corollary 5's setting) with Theorem 2's
  failure pattern. The paper's version with synchronous processes and atomic broadcast relies on
  [DDS87, Table I] and is not formalized.
* Theorem 1 is formalized twice. `Abstract.lean` has the generic version (a model is a set of runs
  with views, Definition 2 is equality of views); there the literal statement is refuted and a
  corrected one proved. `theorem1_async` is the concrete asynchronous instance: (C) is CSLib's FLP
  theorem, and the other conditions follow from solo runs, merging and lifting.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 1 (restricted algorithm `A\|D̄`) | `KAlgorithm.restrict` | `Restrict.lean` |
| Theorem 1, as stated: false | `Abstract.Counterexample.theorem1_statement_false` | `Abstract.lean` |
| Theorem 1, corrected (generic) | `Abstract.theorem1_corrected` | `Abstract.lean` |
| Theorem 1, asynchronous instance (via CSLib FLP) | `theorem1_async` | `Theorem2.lean` |
| Theorem 2 (asynchronous processes, `f−1` initial + 1 crash) | `theorem2` | `Theorem2.lean` |
| Corollary 5 | `corollary5` | `Theorem2.lean` |
| Lemma 6 (needs a nonempty graph), Lemma 7, `≤ ⌊n/(δ+1)⌋` source components | `SourceComp.exists_sourceComponent`, `SourceComp.exists_sourceComponent_anc`, `SourceComp.card_sourceComponents_le` | `SourceComponents.lean` |
| Theorem 8, "if" (generalized FLP initial-crash algorithm) | `InitDeadAlg.initDead_possible` (safety `kSafe`, termination `terminates`) | `Algorithm*.lean` |
| Theorem 8, "only if" (all `kn ≤ (k+1)f`) | `initDead_impossible` | `InitDeadImpossible.lean` |
| Theorem 8 (iff, `f < n`, `\|V\| ≥ n`) | `theorem8` | `Main.lean` |
| Theorem 2 vs Theorem 8 (`n=5, f=3, k=2`) | `theorem2_vs_theorem8` | `Main.lean` |
| Degenerate case `f = n` | `theorem8_false_of_f_eq_n`, `theorem2_false_of_f_eq_n` | `Degenerate.lean` |

**Not formalized.** Section VII (failure detectors `Σ_k`, `Ω_k`: Lemmas 9, 11, 12, Theorem 10,
Corollary 13) needs a failure-detector framework and cited results (weakest failure detector for
consensus, the `Ω₂` vs `Ω` separation). Also not formalized: T-independence (Definition 6) as a
separate notion, and the synchronous-process version of Theorem 2, whose condition (C) rests on [DDS87, Table I].
Whether the repaired conditions of Theorem 1 hold for Theorem 10 is open: it is not checked here.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The model and the consensus impossibility are CSLib's
`Cslib/Computability/Distributed/FLP/`. Non-vacuity: Theorem 8's algorithm satisfies the
specification, and the trivial algorithm `own` solves k-set agreement for `k ≥ n`.
Source components are the shared library's `Digraph.IsSourceComponent` (`Cslib/Foundations/Combinatorics/Digraph/Walk.lean`)
on finsets of vertices; `SourceComp.isSourceComponent_iff` gives the elementary characterization
(nonempty, strongly connected, closed under in-neighbours); `SourceComp.IsRoot`/`anc` are the shared
`Digraph.InSourceComponent`/`Digraph.ancestors` (CSLib,
`Cslib/Foundations/Combinatorics/Digraph/Walk.lean`, with `exists_inSourceComponent` and `reachable_iff_of_closed`). Reusable pieces (CSLib candidates):
`AgreeOn`/`replay_mTr`/`agreeOn_mTr_outside` (`Replay.lean`) and the counting lemmas of
`SourceComponents.lean`.
