# Differences between the formalization and the paper

Paper: Raynal, Stainer, Taubenfeld, *Distributed Universality: Contention-Awareness; Wait-Freedom;
Object Progress, and Other Properties*, PODC 2014 (BA); full version IRISA PI-2014 (hal-00947657v2).

## Statement-level issues and the verdict rule applied

1. **Theorem 2 / abstract property (4), contention-awareness — false (🚨, R5).** Counterexample
   `theorem_2_not_contention_aware` (`ContentionCex.lean`): a sequential execution (in the paper's
   sense: an operation is in progress from its first proposal to its return, Section 3.4) in which a
   process running alone invokes `kSC[1]`.
   - *Borderline call.* The claim holds for the weaker notion "only one process ever takes steps"
     (`fig2_solo_from_init_no_sc`). That is not the paper's notion: it says "interval contention" and
     "no contention during the execution of an operation". Under the other conceivable reading, where
     an operation is pending from `next()`, every process that ever started is in contention forever
     (Figure 1 fetches the next operation, at line 11/22, before returning the previous one at line
     31), so the property would reduce to the weak one. That reading also clashes with the paper's
     well-formedness assumption (Section 2.2: no new operation on `m` is invoked before the previous
     one terminated), which Figure 1 would violate at line 22.
   - R4 does not excuse the gap. A reader taking the paper at its word, with long-lived objects and
     sequential use, is misled substantively. The authors' own justification ("adopt … This means that
     there is contention", Section 4.1) is exactly the false step.
   - R5: the title names contention-awareness, the abstract lists it as property (4) of *the proposed
     construction*, and Theorem 2 names *the algorithm of Figure 2*. Hence 🚨.
   - Robustness. The run satisfies the strong reading of the adopt-commit no-conflict property
     (`strongAC = true`), so it is valid under both readings. Its line-N1 responses at `AC[1][0]`
     coincide with those of the standard register implementation (`ACImpl.adopt_on_stale`).
     Under the weak reading (satisfied by the standard implementation, which violates the strong
     one: `ACImpl.adopt_after_solo_commit`) even a fully sequential run, in which no two proposed
     operations overlap, invokes `kSC[1]` (`theorem_2_not_contention_aware_sequential`). Under the
     strong reading, sequential runs do not use SC objects; the concurrent prefix of the main
     counterexample is needed, and interval contention (the paper's explicit notion) allows it.
2. **Section 4.3, line 4M — typo (⚠️, R3).** The text proposes `oper_i[m]`; Figure 2 proposes
   `ac_op_i[m]`. The literal text is unsafe (`Typo4M.section_4_3_line_4M_unsafe`). The intent is
   evident: Section 4.3 says the algorithm is Figure 2 with only the SC objects replaced. We
   formalize Figure 2's version (`Mode.Good`).
3. **Lemma 5** is stated "∀ r ≥ 1" without requiring that some process reaches the end of round `r`'s
   adopt-commit part. We require it (`Lemma5.lemma5_general`, hypothesis `DoneAC`); in infinite
   executions it always holds (`Exec.round_commits`). This is a degenerate case (R2) and does not
   affect the verdict.
4. **Theorems 6 and 7 (Appendix G.2)** — not formalized and not checked. For `ℓ < k` their proofs
   seem to rely on "(k,ℓ)-universal ⇒ wait-free implementation of any single object", which does not
   obviously follow; a possible counterexample via the set-consensus hierarchy is only a lead (README).
   Unformalized parts do not count for the verdict.

## Proof gaps (statements true; repaired)

- **Lemma 3.** The "valid history" definition and its consequences (i), (ii) presuppose that an
  operation is never committed in non-consecutive rounds. This is argued only inside the proof, and
  case (a) of that argument overlooks proposers that adopted the operation while already having it in
  their history. We give a full invariant proof (`InvB`: chain property `hist_G`, knowledge `know`,
  proposal invariant `PIa`, collect invariant `CI`, birth records `GS1/GS3/GS4`; core step
  `chain_next`).
- **Lemma 6.** The proof counts rounds with a commit instead of distinct operations, and assumes the
  committer survives until it writes `GSTATE`. Repaired via `NoRepeat` (an operation committed in
  round `ρ` is never proposed from round `ρ + 2` on) and the knowledge invariant.
- **Theorem 3.** The proof's final sub-case is left open. We repaired it with a new argument: the
  helping window `Wst` opens at the first moment the object's sequence reaches a length `≡ j mod n`
  (`Wst.start`, `Wst.step`, `Wst.close`).
- **Theorem 4(b).** The register-based proof fails when the UC is a black box
  (`Abstract.register_counterexample`). Repaired with sticky (first-value) objects
  (`Abstract.scFromUC`).
- **Lemma 4 under helping.** With L1–L5, a helper may propose `p_j`'s operation before `p_j` itself
  does, so an operation can be linearized before the paper's start point (first proposal by its
  owner). We use the invocation time (`next()`, ghost `invAt`) as the start, which is standard
  linearizability.
- **Adopt-commit validity.** Section 2.1 says only "`v` has been proposed by a process". All proofs
  (paper and ours) need "proposed before the response", the standard meaning. This is our `acOK`.

## Modelling choices

- **Black-box base objects.** Adopt-commit and `(k, ℓ)`-SC objects have separate invocation and
  response steps; the adversary chooses any response allowed by the specification. The
  no-conflicting-values property is taken in the weak reading (it constrains the returning process
  only); the strong reading is available (`Mode.strongAC`) and used in the counterexample. Responses
  always exist (`NonVacuity.enabled`).
- **(k, ℓ)-SC** returns exactly `ℓ` pairs with distinct objects (Section 4.3). `ℓ = 1` is `k`-SC.
- **Atomicity.** Each step performs at most one base-object access or one register read.
  - `GSTATE[i]` is one register holding all `k` histories, as in the paper.
  - The local computation of lines 6–13 is one step; lines 16–28 take one step per object, including
    the read of `LAST_OP[j][m]` (L1).
  - A process's writes to its own `LAST_OP` registers, implicit in `next()`, are merged with the
    surrounding local step. They are single-writer registers on which these steps commute with other
    processes' accesses; the merge is not formally justified.
- **Loop orders.** "For each `m`" loops run in increasing order. Lines 3M are executed on the decided
  objects in increasing order, before lines 4M (the paper allows any order within 3M; we fix one).
- **Line 7** ("longest history containing `ℓ_hist`") is a deterministic left fold over
  `g_state[1..n]`; since all histories are prefix-comparable (proved), every resolution gives the
  same result.
- **Operations and outputs.** `my_listᵢ[m]` is static: operation `c` of `pᵢ` on `m` is `(i, c)`
  (operations unique, as the paper assumes). Outputs are represented by the history they are
  computed from (`retH`): we prove it is a prefix of the common sequence containing the operation, so
  the output is the sequential specification applied to the operations preceding it. Dynamic lists
  are not modelled.
- **Linearizability** is stated with explicit linearization points (Lemma 4's "first write of a
  `GSTATE` register containing the operation", ghost `lin`) and a real-time corollary, not via a
  general Herlihy–Wing history notion. Per-object; locality is not formalized.
- **Executions.** Infinite executions are sequences of enabled steps (`Exec`). A correct process takes
  infinitely many steps; a crashed one stops. "An object progresses forever" means its sequence
  `G x` grows unboundedly. "Process `j` completes infinitely many operations on `x`" means `retAt j x
  c` is set for arbitrarily large `c` (`CompletesInf`). The `ℓ`-wait-freedom of Appendix G is
  `theorem_4a`.
- **Ghost state** (`time`, `G`, `born`, `opRec`, `invAt`, `retH`, `retAt`, `lin`, `firstL`, `finR`,
  `acFree`) never influences the algorithm.
- **Round numbering.** The paper's `AC[r]` (Figure 1) and `AC[2r−1]`, `AC[2r]` (Figure 2) are
  `acI r false m` / `acI r true m`; Figure 1 uses only the `true` instance.
- **Process indices** are 0-based: L1's `j = |ℓ_hist| mod n + 1` becomes `|ℓ_hist| mod n`.

## Not formalized

- Theorem 5 (needs composition of implementations), Theorems 6–7, Section 4.4's equivalence
  `k`-SA ≡ `k`-SC (cited from [1]).
- Generosity / obstruction-freedom remarks (Section 3.4, Appendix F).
- Property (3) of the abstract (an object that stops progressing stops in the same state at all
  correct processes). It follows from the knowledge invariant but is not stated.
- Appendices A (Gafni–Guerraoui construction and its flaws), C (state-based variant), E (fewer SC
  uses).
