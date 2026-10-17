# Easy Impossibility Proofs for k-Set Agreement — PODC 2011

Martin Biely, Peter Robinson, Ulrich Schmid. *Easy Impossibility Proofs for k-Set Agreement in
Message Passing Systems.* PODC 2011 (brief announcement). DOI
[10.1145/1993806.1993846](https://doi.org/10.1145/1993806.1993846). Formalized version: arXiv
[1103.3671](https://arxiv.org/abs/1103.3671) v2 (full version, latest arXiv version, March 2011);
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The concrete results hold: k-set agreement is impossible in
asynchronous message passing with `f` crashes when `k ≤ (n−1)/(n−f)` (Theorem 2 with asynchronous
processes, Corollary 5), proved by the paper's reduction to FLP, and with up to `f < n` initially
dead processes k-set agreement is solvable iff `kn > (k+1)f` (Theorem 8). But the generic
Theorem 1, the paper's main tool, is imprecisely stated: its condition (B) is not satisfiable
as written, and its proof needs an unstated hypothesis (processes of `D̄` can only decide values
proposed in `D̄`). That hypothesis holds in the paper's own models, where inputs are free, but
fails for models that restrict inputs. With these repairs it holds and covers the paper's
applications.

## Mistakes in the paper

* **Theorem 1 relies on an unstated property of the model.** Fact 1 ("in every run of `R(D̄)` all of `D̄` decide on a
  common value") is derived from (B) and k-agreement alone. Then `A|D̄` is said to solve consensus
  in `M'`. Both steps tacitly assume that `D̄` cannot decide a value proposed only in `D`.
  Otherwise `D̄` may split between `v₁` and a new value `w`, which together with `v₁, …, v_{k−1}`
  are still only `k` values, and `A|D̄` need not be valid in `M'`. Counterexample: `n = 3`,
  `k = 2`, `D₁ = {0}`, `D̄ = {1, 2}`, no communication, and process 0 always proposes 0 in `M`.
  "Everybody decides 0" solves consensus in `M`, yet (A)–(D) hold, with `M'` = two silent
  processes with inputs in `{1,2,3}`. The counterexample needs a model in which `D̄`'s
  view is correlated with `D`'s inputs (here: process 0's input is fixed). The paper's models
  ([DDS87]-style, all inputs `x_q ∈ V` possible, admissibility independent of input values)
  exclude this. There the missing hypothesis follows by changing the inputs of `D`. So Theorem 1
  is false only in the literal "arbitrary system model" generality the paper claims. This is an
  under-specified statement, and the applications are not affected. (`Abstract.Counterexample.theorem1_statement_false`; repaired:
  `Abstract.theorem1_corrected`)
* **Condition (B) of Theorem 1 cannot hold as written in the applications.** The values `v_i` are
  fixed in advance, and `R(D, D̄)` requires `v_i` to be proposed in `D`. A run of `R(D̄)` in which a
  process of `D̄` proposes `v₁` therefore has no `D̄`-indistinguishable partner in `R(D, D̄)`. With
  arbitrary distinct inputs (Theorems 2 and 10) such runs exist. The values must be allowed to
  depend on the run, and the proof works verbatim then. Under-specified statement.
  (`Abstract.condB_fails`)
* **Two more gaps in the proof of Theorem 1.** First, "clearly ρ ∈ R(D̄)" does not follow from
  indistinguishability *until decision*: a process of `D̄` that decided early may hear from `D`
  in ρ before the other processes of `D̄` decide. Second, termination of `A|D̄` in `M'` is never
  argued, and it needs (D) to preserve correctness. Both hold in the applications. Condition (A)
  is never used. Proof gaps. (`Abstract.theorem1_corrected`)
* **Theorem 8 "only if" is proved only for the border case `kn = (k+1)f`.** For `kn < (k+1)f`
  the paper relies on "Theorem 2 tightly captures the impossibility". But Theorem 2 assumes a
  different and harsher failure model (`f − 1` initial crashes plus one crash during the run), so
  its impossibility does not transfer, and its bound `(n−1)/(n−f)` is not `f/(n−f)`. Example:
  `n = 5, f = 3, k = 2` is impossible under Theorem 2's failures but solvable with initial crashes
  only (`theorem2_vs_theorem8`). The paper's partitioning argument works for all `kn ≤ (k+1)f`.
  Proof gap; statement true. (`initDead_impossible`)
* **Degenerate case `f = n`.** Theorem 8 (in the form `kn > (k+1)f`) fails for `f = n ≤ k`:
  "decide your own input" works there. Theorem 2's bound `(n−1)/(n−f)` is undefined at `f = n`.
  In the multiplied-out form `k(n−f) ≤ n−1` it would fail for `f = n = k`. The paper implicitly assumes `f < n`
  (its sets `D_i` of size `n − f` must be nonempty). False only in a degenerate case.
  (`theorem8_false_of_f_eq_n`, `theorem2_false_of_f_eq_n`)
* **Section VI, minor slips.** Lemma 6 needs a nonempty graph; the empty graph has no source
  component. The claim that processes have "complete and consistent knowledge of G" after stage 2
  is too strong: a process only learns its ancestors. That suffices, but one must also argue that
  a chosen root's ancestor set is frozen once all its ancestors have chosen their in-lists. For
  `k = 1`, what is chosen is a source component, not a "clique". The algorithm is correct as
  intended. (`SourceComp.exists_sourceComponent`, `InitDeadAlg.kSafe`)
* **Typos.** In the proof of Theorem 10, "applying Theorem 2" should be Theorem 1. The proof of
  Lemma 7 cites "the previous theorem", meaning Lemma 6.

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
separate notion, and the synchronous-process version of Theorem 2.

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
