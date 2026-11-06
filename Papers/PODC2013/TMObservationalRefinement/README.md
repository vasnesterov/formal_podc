# TM Consistency via Observational Refinement — PODC 2013

Hagit Attiya, Alexey Gotsman, Sandeep Hans, Noam Rinetzky. *A Programming Language Perspective on
Transactional Memory Consistency.* PODC 2013. DOI
[10.1145/2484239.2484267](https://doi.org/10.1145/2484239.2484267). Formalized version: the PODC author
copy (10 pp.; no arXiv version); numbering follows it. The journal version (JACM 2017) was only used to
confirm intended definitions.

**Verdict: ⚠️ Weakened.** Sufficiency holds after fixing two slips in the definitions: the opacity relation implies
observational refinement with respect to traces and to states (Theorem 21, Corollary 19). Necessity is proved for
trace-observational refinement, which makes the opacity relation an exact characterization there. Necessity for
state refinement (Theorem 24) is not saved: it is false as printed, only because of the Figure 2 mistake that also
breaks Proposition 13, and for the abort semantics the prose states it is neither proved nor refuted, since the proof
sketch's program cannot tell an aborted call from a returned one and a marker assignment after each call is a
plausible fix that is not proved here.

## Mistakes in the paper

### ⚠️ Theorem 24 (third implication of Theorem 16, necessity)
Unestablished: the proof sketch's `P_H` cannot tell an aborted last call from a call that returned
the initial value, and the marker fix is plausible but unproved; as printed (literal Figure 2,
deterministic commands) the theorem is even false (`theorem_24_false`), but that counterexample
fails for the abort semantics the prose states (`theorem_24_cex_fails_intended`).

**Impact.** Half of the necessity claim is lost: for states the proof is broken and the statement is neither
proved nor refuted for the intended semantics. Figure 2 as printed lets an atomic block run on
after one of its calls was aborted, against the prose "Once this happens, the execution of C
terminates"; our refutation needs exactly this mistake, so it does not refute the intended theorem. For
trace-observational refinement necessity holds outright (`trace_necessity`).

**Details.** Let `H_C` be the prefixes of `H = (t,txbegin)(t,OK)(t,call o.f(1))(t,aborted)`, and
`H_A` the prefixes of `S_v = (t,txbegin)(t,OK)(t,call o.f(1))(t,ret(v) o.f)(t,txcommit)(t,aborted)`
for all `v ∈ ℤ`. Both are transactional systems. No complete history of `H_A` has the per-thread
projection of `H`, so `H_C|complete ⋢ H_A|complete`.

With Figure 2 as printed, `H_C ⊑_state H_A`. Take a program trace whose history is `H`. Replace the
`aborted` response by `ret(v)`, where `v` is the current value of the call's target variable `x`;
`x := v` changes nothing. If the call ended its atomic block, also let the transaction abort at
`txcommit`. The new trace has a history in `H_A` and, with deterministic commands, the same final
states. This uses Figure 2 as printed: if the body has more commands after the call, say `z := 1`,
an aborted call there never lets the block finish with `r := aborted`. The trace with history `H`
can only run on into `z := 1`, and the successful call reproduces that.

With the intended semantics, `r := atomic { y := o.f(1); z := 1 }` has a trace with history `H` that
ends with `r = aborted` and `z` unchanged. Every trace with a history in `H_A` that sets `r` runs
`z := 1` first, so `H_C ⋢_state H_A` (`theorem_24_cex_fails_intended`, minimal language, one
thread).

The proof sketch's `P_H` really is insufficient, even for the intended semantics. It records each
return value in a dedicated variable that starts at a "distinguished initial value". When the
aborted call is the last command of its block, "aborted" and "returned the initial value, then
aborted at commit" leave the same final state. So the claim "from the final state … we can
reconstruct the interaction of each thread" is false as stated. A marker assignment after each call
(the device `TraceNecessity.lean` uses for traces) separates the two cases. We did not formalize this
repair for states.

**Repair.** Necessity from refinement with respect to traces holds for all histories, not only
complete ones (`trace_necessity`, `trace_necessity_complete`). Combined with Theorem 21 this gives
`H_C ⊑ H_A ⟺ H_C ⊑_trace H_A` (`theorem_16_repaired`).

### 🔧 Figure 2 and Proposition 13 (`A(P)` contains only well-formed traces)
Proposition 13 is false: Figure 2 lets the body of an atomic block continue after a method call in it was aborted,
so `txbegin OK call aborted call` is the history of a trace in `A(P)` (`prop_13_false`).

**Impact.** The prose says "once this happens, the execution of C terminates", so the intent is clear
and the fix is local (stop the body at the aborted call, as JACM Figure 4 does). What the paper uses
it for holds: a program trace with a well-formed history is a well-formed trace (`wfTrace_of_inA`).
The same clause of Figure 2 is what makes Theorem 21 fail with the printed Definition 2, and Theorem 24 fail as
printed (above).

### ✏️ Slips
- Definition 2 (`txcommit` outside transactions): the third condition lists only `call`/`ret`, so a "stray"
  `txcommit` outside any transaction is well-formed, and then Lemma 17 and Theorem 21 are false
  (`lemma_17_false_literal`, `theorem_21_false_literal`). The intent is evident: `txcommit` is "issued when a
  transaction tries to commit upon exiting an atomic block", and the journal version adds it to the condition. With
  the fix, Lemma 17 and Theorem 21 hold (`rearrangement`, `theorem_21`). A stray `txcommit` is a non-transactional
  action, so `∼` fixes its position among the non-transactional actions of other threads, while `⊑` can move it.
  Lemma 17 fails for `H = (t₁,txcommit)(t₂,txcommit) ⊑ S = (t₂,txcommit)(t₁,txcommit)`. Programs really produce
  stray `txcommit`s, because of the Proposition 13 issue above. Two threads run `x := atomic { x := o.f(1); x := 1 }`.
  Both calls abort, both threads go on with `x := 1` and then issue `txcommit`. This is a trace with a history in
  `H_C` whose stray `txcommit`s `H_A` reorders, and no trace of `H_A` is observationally equivalent to it.
- Definition 12 (global accesses inside transactions): the third condition looks for `committed`/`aborted` of *any*
  thread after `t`'s `txbegin` (the projection `τ₁|t` is missing), and then Lemma 18 is false
  (`lemma_18_false_literal`). The intent is evident (the journal version uses `τ₁|t`). With the fix, Lemma 18 holds
  (`lemma_18`, even without the hypothesis `eval(s, τH) ≠ ∅`). Program traces satisfy the repaired condition, so
  Corollary 19 is unaffected. Counterexample: thread `t₁` opens a transaction, thread `t₂` runs a whole transaction,
  then `t₁` writes `g := x` inside its transaction and `t₂` writes `g := x` outside. Swapping the two writes
  preserves `∼`, because `t₁`'s write is transactional, but changes the final value of `g`.

### Typos
- Lemma 18's statement binds `s` twice ("`eval(s, τH) ≠ ∅ ⟹ ∀s. …`"). The proof shows equality of the
  evaluations for every `s`.

## Proof gaps (statements true)

### 🔧 Lemma 22 (rearrangement step), footnote 3
The footnote classifies the actions of `τ₃` on their own ("all non-transactional" without
`txbegin`), and read literally this gives `τ^{i+1} = τ^i`, breaking the invariant
`H^{i+1}_{i+1} = S_{i+1}`.

**Impact.** Statement true; the classification must be taken relative to the whole trace
(`nontransFrom` with the status after the prefix). Repaired in `rearrange_step`. Theorem 21's proof
also needs `τH` to be well-formed, which the paper takes from the false Proposition 13; repaired by
`wfTrace_of_inA`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Histories and traces are lists of actions of a fixed finite set of threads; there is no
  scheduler or failure model beyond the paper's: finite traces, prefix-closed trace sets (incomplete
  computations, preempted threads), no liveness.
- The transactional system is a set of histories. `IsTS` uses repaired Definition 2, `IsTSLit` the
  printed one.
- The language is a class `Lang`. Primitive commands are an arbitrary type with classes
  `LPcomm_t`/`GPcomm_t` and a nondeterministic semantics that only reads and writes the variables its
  class allows. It provides `assume(b)`, `assume(e = n)` and the assignments `x := n`, `g := x`,
  `x := g`; expressions are abstract.
- Programs (`Cmd`, `Cmd.Allowed`) obey the syntactic restrictions of Section 2. Figure 2 as printed
  is the inductive `Tr`, and `A(P)` is the prefix closure of interleavings (`InA`). All positive
  results use `Tr`. `TrI` (`Theorem24Intended.lean`) is Figure 2 with the intended abort semantics:
  the body of an atomic block stops at its first aborted call.
- Observational refinement: `StateRef` (Definition 14) and `TraceRef` (Definition 15). There is no
  randomness. The results are proved for every instance of `Lang`; the Theorem 24 counterexample
  needs deterministic commands and Figure 2 as printed.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 2 (repaired) ⇔ per-thread automaton | `wellFormed_iff_run` | `Basic.lean` |
| Definition 4, inductive form | `opac_cons_iff` | `Opacity.lean` |
| Lemma 17 (Rearrangement), repaired defs | `lemma_17`, `rearrangement` | `Rearrangement.lean` |
| Lemma 22 | `rearrange_step` | `Rearrangement.lean` |
| Lemma 17 false as printed | `lemma_17_false_literal` | `Rearrangement.lean` |
| Proposition 23 | `prop_23` | `Semantics.lean` |
| Lemma 18, repaired Definition 12 | `lemma_18` | `Semantics.lean` |
| Lemma 18 false as printed | `lemma_18_false_literal` | `Semantics.lean` |
| Proposition 13 false; repair | `prop_13_false`, `wfTrace_of_inA` | `Program.lean` |
| Lemma 20 | `lemma_20` | `Sufficiency.lean` |
| Theorem 21 | `theorem_21` | `Sufficiency.lean` |
| Corollary 19 | `corollary_19` | `Sufficiency.lean` |
| Theorem 16, first two implications | `theorem_16_sufficiency` | `Sufficiency.lean` |
| Theorem 21 false as printed | `theorem_21_false_literal` | `Literal.lean` |
| Theorem 24 false for Figure 2 as printed (deterministic commands; minimal language) | `theorem_24_false`, `theorem_24_false_minLang` | `Theorem24.lean` |
| That counterexample fails for the intended abort semantics | `theorem_24_cex_fails_intended` | `Theorem24Intended.lean` |
| Necessity for trace refinement (repair) | `trace_necessity`, `theorem_16_repaired` | `TraceNecessity.lean` |
| Non-vacuity: minimal deterministic language | `instLangMinCmd`, `minCmd_det` | `NonVacuity.lean` |

**Remark.** For trace observation the opacity relation is an exact characterization: with
`τ'|t = τ|t` for every thread, even pending actions are reproduced. This closes, for traces, the gap
Section 8 attributes to incomplete histories. The proof (`TraceNecessity.lean`) builds the
program `P_H` and adds unique non-transactional marker assignments before and after each atomic
block, so that `nontrans` carries the real-time order. It needs one local variable (`Inhabited LV`)
and no global variables.

**Not formalized.** Proposition 10 (equivalence with the original definition of opacity; proved only
in the technical report). Theorem 24 for the intended abort semantics (`TrI`), with a repaired `P_H`.
The positive results only use per-thread projections of `A(P)`, so they should carry over to `TrI`; this
is not formalized.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. `instLangMinCmd` shows the language hypotheses are satisfiable (and deterministic, so
`theorem_24_false` applies to it); `Opac.refl` gives a non-trivial instance of Theorem 21. Self-contained;
no CSLib model is used.
