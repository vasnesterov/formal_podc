# Safety-Liveness Exclusion in Distributed Computing — PODC 2015

Victor Bushkov, Rachid Guerraoui. *Safety-Liveness Exclusion in Distributed Computing.* PODC 2015.
DOI [10.1145/2767386.2767401](https://doi.org/10.1145/2767386.2767401). Formalized version: the authors'
full version with proofs (EPFL Infoscience record 207929, 19 pages); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** Theorem 4.4 (when a weakest excluded liveness property exists)
and Lemma 4.8 are correct. Theorem 4.9 ("a strongest non-excluded liveness property must be `Lmax`")
holds, with a repaired proof, if processes take steps only while they execute an operation. The
paper's formal I/O-automaton model does not impose this, and there the theorem is false even with
`Lmax` = wait-freedom. The `(l,k)`-freedom theorems of §5 follow from the cited (im)possibility results
once "progress" for TM is read as the authors' earlier work defines it.

## Mistakes in the paper

### ⚠️ Theorem 4.9 (the strongest non-excluded liveness property must be `Lmax`)
In the paper's I/O-automaton model, which lets a process take steps while it executes no operation,
Theorem 4.9 is false even for `Lmax` = wait-freedom: for two processes, a safety property `S` meeting all
the paper's assumptions has a strongest non-excluded liveness property strictly weaker than
wait-freedom (`theorem_4_9_false_waitFree`).

**Impact.** Implied assumption. §2 describes processes as running their algorithm when invoked, and every
implementation in the paper does so. For such *reactive* implementations Theorem 4.9 holds
(`theorem_4_9`), and Corollaries 4.10–4.11 follow from the cited impossibilities (`corollary_4_10`).
This is a borderline call against 🚨; see [differencies.md](differencies.md).

**Details.** `S` contains every well-formed history except those in which `p₀` receives a response after
`p₁` crashed before `p₀`'s first invocation without ever having invoked. `S` is prefix- and
limit-closed, every invocation can be answered sequentially, and every history of `S` is a history of
an implementation ensuring `S`, namely `Is`.

The implementation `Is` has a single-writer register `(counter, flag)` written by `p₁`. `p₁` increments
the counter at every step, *also while idle* (a heartbeat), and sets the flag in each operation. On its
first invocation `p₀` reads the counter, then waits until the counter changes or the flag is set. Either
event proves that `p₁` was alive after `p₀`'s invocation, or had invoked. Later invocations of `p₀` are
answered at once.

Two facts make the counterexample work:

* In every valid implementation ensuring `S`, the histories `Y` are fair (`Y_subset_fairH`). In these
  histories `p₁` crashes, possibly after invoking, `p₀` invokes and waits forever, and nobody responds.
  The reason: if the inputs of `Y` are applied without internal steps, the state is the one reached
  after `crash₁ · inv₀`, because `p₁`'s inputs touch only `p₁`'s local state and the crash erases it.
  From that state `S` forbids any answer to `p₀`.
* Every other fair history of `Is` is wait-free (`Is_fairH_subset`).

So `WaitFree ∪ Y` is the strongest non-excluded liveness property (`isStrongestNonExcl_waitFree_Y`), and
it is not wait-freedom.

The proof breaks at its claim "because `A_I'` is input-enabled, every history `h'` with a single
response and `h'|pᵢ = invᵢ · resᵢ` is a history of `A_I'`". This needs the other processes'
invocations and crashes to commute with `pᵢ`'s run. That fails as soon as `pᵢ` waits for an idle
process. `Is` is valid but not reactive (`Is_not_reactive`).

**Repair.** We assume that processes take no step while idle, and repair the proof (see Proof gaps).
`theorem_4_9` holds for every class of reactive valid implementations that contains the two trivial
implementations of the paper's proof. One example is the reactive implementations from registers.
The hypotheses can be met (`nonvacuous_4_9`).

### ⚠️ §3.2 (the order on liveness properties)
The claim "`L₁` is weaker than `L₂` iff `L₂ ⊆ L₁`" is false: for reactive implementations, wait-freedom
and wait-freedom plus the never-fair history `inv₀` (with `p₁` idle forever) are ensured by exactly the
same implementations (`weaker_iff_subset_false`).

**Impact.** All proofs of the paper use `⊆`, and we formalize every result with `⊆`. With the paper's
semantic definition, strongest and weakest properties are determined only up to equivalence: "it
should be `Lmax`" in Theorem 4.9 then holds only up to equivalence.

### ⚠️ Definition 5.1 and Theorem 5.3 (progress for transactional memory)
Read literally, Definition 5.1 makes Theorem 5.3 false: if "good" responses are those that do not abort,
a TM that aborts every commit request is opaque and `(n,n)`-free, and if they are commits, a correct
process that never invokes `tryC` makes every `(1,k)`-freedom unimplementable (argued, not formalized).

**Impact.** The intent can be recovered from §4 ("the set of 'good' events is restricted to commit
events") and from the authors' [4], which exempts parasitic processes. With that reading, the cited
results give Theorem 5.3. We formalize it from those results, taken as hypotheses (`theorem_5_3`).

### Typos and slips
- §5.1: "`LF_l ∪ OF_k` is the set of all executions that ensure `(l,k)`-freedom" is false. Only `⊆`
  holds: two correct processes, one of them stepping and progressing alone, give an execution that is
  2-obstruction-free but not `(2,2)`-free (`lf_union_of_not_iff`). The remark is not used.
- §4.1, example before Corollary 4.5: some histories listed in `F₁` (e.g. `propose₁(v) · v₁ ·
  propose₂(v')`) are never fair, because correct idle processes must keep invoking. For `n ≥ 3`, `F₁`
  must also crash the other processes. The corollary is unaffected.
- §5.3: the second requirement of `S` says the transactions "should be aborted in `h`". This is not
  prefix-closed; "none of them commits" is meant.
- §2: input-enabledness is stated for every state at which `pᵢ` is "not pending". Read literally, this
  includes unreachable states and the crashed state, where nothing may be enabled. We require it along
  executions (see [differencies.md](differencies.md)).

## Proof gaps (statements true)

### 🛠️ Theorem 4.9 (proof, reactive implementations)
The proof derives `invₗ · resₗ ∈ S` from `h · resₗ ∈ S`, which does not follow, and it ignores the case
where every process crashed in `h`.

**Impact.** Statement true for reactive implementations; repaired (`core_subset_Lmax`, `theorem_4_9`).

**Details.** For consensus, `propose₂(1) · propose₁(0) · decide₁(1)` satisfies agreement and validity,
but `propose₁(0) · decide₁(1)` violates validity. The paper's second and third steps pick the response
`resₗ` in opposite orders. If every process crashed in `h`, there is no correct pending process to
answer.

**Repair.** We use the characterization `Setting.isStrongestNonExcl_iff`: a strongest non-excluded
property is `Lmax ∪ core`, where the core is the set of histories fair for every implementation
ensuring `S`. It then suffices to show `core ⊆ Lmax`.

* Take a core history `h`. The silent implementation ensures `S`, so `h` has no response, and every
  process is pending or crashed at its end.
* If all processes crashed, `h` has no well-formed extension, so the assumption on `Lmax` puts `h`
  into `Lmax`.
* Otherwise take a pending correct `p_l` and its invocation `x`. First choose `r` with
  `inv_l x · res_l r ∈ S` (the paper's assumption on `S`), then an implementation `I'` ensuring `S`
  with this history. The one-shot responder that answers `r` ensures `S`: each of its histories is a
  history of `I'` by the frame lemma `Run.frame`, which uses reactivity. Yet `h` is not fair for the
  responder.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory, `n` processes, crash failures (any number), deterministic adversary
  (scheduler and environment), no randomness. An implementation is the paper's composition
  `A_{I₁} × … × A_{Iₙ} × A_B` (`Impl`). Each process has a local state, or the crashed state. The
  base objects have a state. Invocations, responses and crashes touch only their process's local
  state. Internal steps of a process may access the base objects. `A_B` may have internal actions.
* Fairness is the paper's (§3.2), and `fairH I` is `fair(A_I)`. Histories are finite or infinite
  sequences of `inv`/`res`/`crash` events. Well-formedness also forbids events after a crash.
* Valid implementations (`Impl.Valid`) have an initial state, produce only well-formed histories, and
  are input-enabled along executions. Reactive implementations (`Impl.Reactive`) take no step of a
  process that is not pending.
* Safety and liveness properties follow Definitions 3.1–3.2. The paper's assumptions on `S` and `Lmax`
  are `SafetyAssumptions` and `LmaxAssumptions`. The class of admissible implementations, e.g. "from
  registers", is a parameter `𝓒`.
* Sections 3–4 are proved in an abstract setting (`Abstract.lean`) and instantiated in the model
  (`setting`).
* Section 5 works on what Definition 5.1 sees of a fair execution: the correct, infinitely-stepping
  and progressing processes. The cited (im)possibility results are hypotheses.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definitions 3.1, 3.2, 4.1–4.3, 4.7 | `Hist.IsSafety`, `Setting.IsLiveness`, `Setting.Excludes`, `Setting.IsAdversarySet`, `Setting.IsWeakestExcl`, `Setting.IsStrongestNonExcl` | `Model.lean`, `Abstract.lean` |
| Remark after Definition 4.3 | `Setting.excludes_iff_exists_adversarySet` | `Abstract.lean` |
| Theorem 4.4 | `Setting.theorem_4_4`; in the model `theorem_4_4` | `Abstract.lean`, `Model.lean` |
| Corollaries 4.5–4.6 (from two disjoint adversary sets) | `Setting.no_weakest_of_disjoint` | `Abstract.lean` |
| Lemma 4.8 | `Setting.lemma_4_8` | `Abstract.lean` |
| Strongest non-excluded property = `Lmax ∪ core` | `Setting.isStrongestNonExcl_iff` | `Abstract.lean` |
| Theorem 4.9, reactive implementations (repaired proof) | `theorem_4_9`, `theorem_4_9_reactive` | `Theorem49.lean` |
| Corollaries 4.10–4.11 (from `Lmax` excluding `S`) | `corollary_4_10`, `Setting.no_strongest_of_excludes_Lmax` | `Theorem49.lean`, `Abstract.lean` |
| Theorem 4.9 false with idle steps, `Lmax` = wait-freedom | `Counterexample.theorem_4_9_false_waitFree` | `CounterexampleWF.lean` |
| Theorem 4.9 false, simpler `Lmax` | `Counterexample.theorem_4_9_false` | `Counterexample.lean` |
| §3.2 order remark is false | `Counterexample.weaker_iff_subset_false` | `Order.lean` |
| Hypotheses of `theorem_4_9_reactive` can be met | `Counterexample.nonvacuous_4_9` | `NonVacuity.lean` |
| Definition 5.1 | `LK.LKFree` | `LKFreedom.lean` |
| Theorem 5.2 | `LK.theorem_5_2` | `LKFreedom.lean` |
| Theorem 5.3 | `LK.theorem_5_3` | `LKFreedom.lean` |
| §5.3: no weakest excluded `(l,k)`-freedom (given Lemma 5.4) | `LK.section_5_3` | `LKFreedom.lean` |
| §5.1: `(1,3)` and `(2,2)` incomparable | `LK.incomparable_1_3_2_2` | `LKFreedom.lean` |
| §5.1: `LF_l ∪ OF_k` remark is false | `LK.lf_union_of_not_iff` | `LKFreedom.lean` |

**Remarks.** Theorem 4.4 needs no property of the model except that fair histories of an
implementation ensuring `S` lie in `S` (limit closure), and that some implementation ensures `S`; both
follow from the paper's assumptions. Its statement is also correct when there is no adversary set
(`Gmax` is then everything). Theorem 4.9 is equivalent to "`core ⊆ Lmax`" whenever a strongest
non-excluded property exists (`Setting.core_subset_of_eq_Lmax`).

**Not formalized.** Lemma 5.4 (Algorithm `I(1,2)`: opacity, the second requirement of `S`,
`(1,2)`-freedom) and the TM model. The cited results [4], [5], [9], [17], [20] enter only as hypotheses:
the concrete adversary sets of Corollaries 4.5–4.6, and "`Lmax` excludes `S`" in Corollaries 4.10–4.11.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `nonvacuous_4_9`. The trivial implementations used by `theorem_4_9` are
shown valid and reactive (`silent_valid`, `responder_valid`, …). The counterexample implementation `Is`
is shown valid (`Is_valid`). The model is self-contained (Mathlib only).
