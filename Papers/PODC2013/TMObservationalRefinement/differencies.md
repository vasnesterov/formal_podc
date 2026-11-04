# Differences between the formalization and the paper

Paper: Attiya, Gotsman, Hans, Rinetzky, *A Programming Language Perspective on Transactional Memory
Consistency*, PODC 2013 (author copy, 10 pp.). Numbering follows the PODC version. The journal version
(JACM 2017, *Characterizing Transactional Memory Consistency Conditions Using Observational
Refinement*) was used only to confirm intended definitions; its numbering is not used.

## Statement-level issues (verdict rules from `verdicts.md`)

1. **Theorem 24 / third implication of Theorem 16 is unestablished** (R5 → ❌: a headline whose
   proof is broken and which is neither proved nor refuted; reviewer correction of an earlier 🚨).
   It is false for Figure 2 as printed (R3 would excuse that alone). `H_C ⊑_state H_A ⟹ H_C|complete ⊑ H_A|complete` fails
   with the literal trace sets of Figure 2 (`Tr`) whenever all primitive commands are deterministic,
   e.g. for the minimal command set the paper requires (assignments and `assume`; instance
   `instLangMinCmd`, `minCmd_det`). Counterexample (`theorem_24_false`, `Theorem24.lean`):
   `H_C` = prefixes of `H = (t,txbegin)(t,OK)(t,call o.f(1))(t,aborted)`; `H_A` = prefixes of
   `S_v = (t,txbegin)(t,OK)(t,call o.f(1))(t,ret(v) o.f)(t,txcommit)(t,aborted)` for all `v ∈ ℤ`.
   Every program trace with history `H` is matched by the trace in which the call returns the current
   value `v` of its target variable (so the assignment `x := v` does not change the state) and, if
   the call ended its block, the transaction aborts at commit. Final states coincide, but no complete
   history of `H_A` has the per-thread projection of `H`.
   *Why the literal failure is not a refutation (no 🚨)*: the counterexample depends on the Figure 2 slip of item 4. As printed, the
   body of an atomic block runs on after an aborted call, and the block can finish with
   `x := aborted` only if the whole body trace ends in `aborted`. So with commands after the call
   (`r := atomic { y := o.f(1); z := 1 }`), an aborted call never completes the block, and the
   continuation `z := 1` is reproduced by the successful call. With the semantics the prose states
   ("Once this happens, the execution of C terminates"; JACM Figure 4), the block ends with
   `r := aborted` and `z` unchanged, which no trace with a history in `H_A` can reproduce:
   `theorem_24_cex_fails_intended` (`Theorem24Intended.lean`, repaired trace sets `TrI`, minimal
   language, one thread) proves `¬ (H_C ⊑_state H_A)` there. By R3 (intent recoverable from the
   prose, local fix of Figure 2) the literal failure is excused, as for Proposition 13.
   *Status for the intended semantics*: neither proved nor refuted. The proof sketch has a real gap
   there: `P_H` records return values in never-rewritten variables with "distinguished initial
   values"; if the aborted call is the last command of its block, "call aborted" and "call returned
   the initial value, then the commit was aborted" leave the same final state, so the claim "from the
   final state of an execution of P_H we can reconstruct the interaction of each thread" is false.
   Adding a marker assignment after each call (inside the block; local variables are not rolled
   back) separates the two cases, and the rest of the sketch (status variables, global flags for
   the real-time order) then looks sound; not formalized. *Deciding rule*: R5, an unestablished
   headline → ❌. *Borderline note*: if the marker repair were proved, the item would drop to a
   proof repair and the verdict to ⚠️ (from the R3 slips, items 2–4); a proof of Theorem 24 false
   for the intended semantics would make it 🚨. The journal
   version drops state-based refinement and proves necessity only for trace-based notions.
   *Nondeterministic commands*: with `x := *` in `Pcomm` the counterexample does not apply even for
   Figure 2 as printed (evaluation sets of states would differ).
   *Repair*: necessity holds for observational refinement with respect to **traces**
   (`trace_necessity`: for all histories; `trace_necessity_complete`; `theorem_16_repaired`:
   `⊑ ⟺ ⊑_trace` for transactional systems), as in the journal version. Our proof uses no global
   variables: unique non-transactional local marker assignments around each atomic block make
   `nontrans` record the real-time order. `trace_necessity` needs only that `H_C` consists of
   (repaired) well-formed histories, nothing about `H_A`.

2. **Definition 2 omits `txcommit` from its third condition** (R3 → ⚠️). As printed, a `txcommit`
   need not occur inside a transaction. The intent (txcommit is "issued when a transaction tries to
   commit upon exiting an atomic block"; JACM Definition 3.2(vi) lists it) is clear and the fix is
   local. Consequences of the printed version, all formalized:
   - Lemma 17 is false (`lemma_17_false_literal`): two pending stray `txcommit`s of different threads.
   - Theorem 21 (first implication of Theorem 16) is false (`theorem_21_false_literal`): together with
     the Figure 2 issue below, a program can produce stray `txcommit`s; two such actions of different
     threads are unordered by `⊑` but ordered by `∼` (both are non-transactional).
   - Theorem 24 is also false for the trivial reason that `H_C = {ε, (t,txcommit)}` is a
     transactional system no program can exercise (not formalized separately; item 1 is stronger).
   Formalization: `WellFormedLit` (as printed), `WellFormed` (repaired, used for all positive
   results); `wellFormed_iff_run` characterizes the repaired version by a per-thread automaton.

3. **Definition 12, third condition, misses the projection `τ₁|t`** (R3 → ⚠️). As printed, a global
   command of thread `t` inside `t`'s transaction is allowed as soon as *any* thread has committed or
   aborted since `t`'s `txbegin`. Lemma 18 is then false (`lemma_18_false_literal`: two writes to the
   same global variable, one inside a transaction, swapped by `∼`). The repaired `WFTrace` uses `τ₁|t`
   (as JACM Definition 3.2(viii)). Program traces satisfy the repaired condition (`Tr.props`), so
   Corollary 19 is unaffected.

4. **Proposition 13 is false** (R3 → ⚠️, borderline). Figure 2 lets the body of an atomic block
   continue after a method call in it was aborted (`A(C₁;C₂)` concatenates any trace of `C₁`, including
   one ending in `aborted`, with a trace of `C₂`), contradicting the prose "Once this happens, the
   execution of C terminates". Hence `A(P)` contains traces with ill-formed histories
   (`prop_13_false`: `txbegin OK call aborted call`). Conversely, an aborted call followed by more
   body commands cannot end the block with `x := aborted` unless the body trace also ends in
   `aborted`; this is what `theorem_24_false` exploits (item 1). Borderline between ⚠️ and ❌: the intended
   semantics is stated in the prose and the fix is local (stop after `aborted`, or intersect `A(P)`
   with well-formed traces as JACM does), so we apply R3. What the paper needs from Proposition 13 —
   traces of `[[P]](s, H)` are well-formed when `H` contains well-formed histories — is proved
   (`wfTrace_of_inA`). With the repaired Definition 2, the continuation is harmless; with the printed
   Definition 2 it is what makes Theorem 21 fail (item 2).

5. **Lemma 18's statement is garbled** (typo): "τH ∼ τS ∧ eval(s, τH) ≠ ∅ ⟹ ∀s. eval(s, τH) =
   eval(s, τS)" binds `s` twice. We prove the strongest reading: for well-formed `τH ∼ τS`,
   `eval(s, τH) = eval(s, τS)` for every `s` (no non-emptiness needed) (`lemma_18`).

## Proof gaps (statements true after the repairs)

- Lemma 22, Case I: "all the actions performed by t in τ₃ are transactional" needs `txcommit` to occur
  inside transactions (item 2). With the repaired definition the step is correct (`rearrange_step`).
- Lemma 22, Case II, footnote 3: "in the absence of txbegin actions in τ₃, the definition of nontrans
  considers all actions in τ₃ non-transactional". Read literally (classifying `τ₃` on its own) this
  makes `τ^{i+1} = τ^i` whenever no `txbegin` is in `τ₃` and the induction invariant `H^{i+1}_{i+1} =
  S_{i+1}` fails; the classification must be taken relative to the whole trace `τ^i`. We use
  `nontransFrom st τ₃` with the status `st` after the prefix.
- Theorem 21's proof applies Lemma 17 to `τH ∈ [[P]](s)` without justifying that `τH` is well-formed
  (implicitly Proposition 13, which is false). Repaired by `wfTrace_of_inA` (well-formed history +
  program trace ⇒ well-formed trace).
- Theorem 24's proof sketch: see item 1 (the claimed reconstruction of the history from the final
  state fails even for the intended Figure 2; markers after calls would repair it, not formalized).
  The detailed proof is in the technical report (Appendix B), which we did not have.

## Modelling choices

- **Language parameters** (`Lang`): threads `T` (finite, `Fintype`; the paper's `{1, …, m}`), local
  variables `LV` (the same name set for every thread; `Var = GV ⊕ (T × LV)`), global variables `GV`,
  values `ℤ`. Primitive commands are an arbitrary type `C` with a class (`LPcomm_t`/`GPcomm_t`, fields
  `thr`, `glob`) and a nondeterministic semantics `sem : C → State → Set State` that must be the
  lifting of a transformer of the accessible variables (`sem_lifted`, exactly Section 4's
  requirement). Boolean and integer expressions are arbitrary types `BE`, `IE` with evaluation on the
  thread's local variables; `IE` has constants (`cst`). The commands the paper assumes are fields:
  `assume(b)`/`assume(¬b)`, `assume(e = n)`, `x := n`, `g := x`, `x := g`; `committed`/`aborted` are
  distinct integers `vCom ≠ vAb`.
- **Programs**: `Cmd` (Section 2 syntax), `Prog = T → Cmd`. The restrictions of Section 2 are
  `Cmd.Allowed` (thread-local commands, no global commands or nested atomic blocks inside atomic
  blocks, calls only inside atomic blocks, no direct `assume`). Definitions 14 and 15 quantify over
  allowed programs.
- **Figure 2** as printed is `Tr`; `TrI` (`Theorem24Intended.lean`) is the intended version, where
  the body of an atomic block stops at its first aborted call (JACM Figure 4, without its
  immediate-abort and `abort`-command rules). All positive results are proved for `Tr` only; they
  rely on per-thread projections of `A(P)` and should carry over to `TrI` (not formalized).
- **Figure 2** is `Tr` (inductive): the Kleene star of a loop is unfolded one iteration at a time;
  `A(P)` (`InA`) is "prefix of a list whose per-thread projections are traces of the threads"
  (= prefix closure of `interleave`).
- **`eval`** is defined by left-to-right folding (`evalSet`); `eval_concat` is the paper's
  definition `eval(s, τφ) = …`.
- **Transactional/non-transactional actions**: computed by annotating the trace with a per-thread
  "inside a transaction" status (`ann`, `nontrans`); `trans_flag_iff` shows this is the paper's
  definition.
- **Definition 4** (`Opac`) uses a `Fin` bijection as in the paper; `opac_cons_iff` gives the
  inductive description used in proofs.
- Transactional systems: `IsTS` (repaired Definition 2) and `IsTSLit` (as printed).
- Lemma 17 (`rearrangement`) does not need `H` and `S` to be well-formed; `lemma_17` keeps the
  paper's hypotheses. Theorem 21 needs nothing of `H_A`; Corollary 19 needs well-formed histories in
  both systems.
- The counterexamples are generic: they hold for every instance of `Lang` (Theorem 24: every instance
  with deterministic commands), for any two distinct threads, any object/method.

## Not formalized

- Proposition 10 (equivalence with the original opacity, Definition 9) — proved only in the TR.
- Section 8 (discussion).
