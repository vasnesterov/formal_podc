# Asynchronous Fault-Tolerant Language Decidability for Runtime Verification — PODC 2025

Armando Castañeda, Gilde Valeria Rodríguez. *Asynchronous Fault-Tolerant Language Decidability for
Runtime Verification of Distributed Systems.* PODC 2025. DOI
[10.1145/3732772.3733514](https://doi.org/10.1145/3732772.3733514). Formalized version: arXiv
[2502.00191](https://arxiv.org/abs/2502.00191) v3 (31 May 2025); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Weakened.** Theorem 5.2, the paper's main result, and the remaining impossibility results hold as
stated, and Theorem 4.1 holds once the Figure 4 construction is replaced. But Lemma 5.3, "`WEC_COUNT ∈ WD`" (also
stated in Table 1), is false for the language as the paper defines it (Definition 2.7), so Theorem 5.1 (`SD ⊊ WD`)
survives only with a modified language (finitely many increments). The proof of Lemma 6.4 is broken and nothing we
proved replaces it, which leaves the hierarchy `PSD ⊂ PWD` of Theorem 6.3 unestablished; the rest of the positive side
of Section 6 was not checked.

## Mistakes in the paper

### ❌ Proof of Lemma 6.4 (`SEC_COUNT ∈ PWD`), hence Theorem 6.3 (`PSD ⊂ PWD`)
The proof claims that the proof of Lemma 5.3 shows "every process reports `NO` infinitely often" when one of
properties (1)–(3) fails, but that proof shows this only for *some* process, while predictive weak decidability
(Definition 6.2) needs *every* process.

**Impact.** Nothing we proved saves Lemma 6.4 or Theorem 6.3. We found this step by inspection; Lean refutes only the
printed Figure 9 (`Counter.fig9_fails`, see below).

**Details.** `flag_i` and the read checks are local, and Figure 9 has no mechanism to spread a `NO`. A transformation
such as Figure 3 would be needed.

### ⚠️ Lemma 5.3 and Table 1 (`WEC_COUNT ∈ WD`)
For `WEC_COUNT` as defined (Definition 2.7), property (3) holds vacuously on words with infinitely many increments,
and a diagonal argument shows that no algorithm weakly decides (or weakly-all decides) the language, already for
`n = 2` (`Counter.not_WD_WEClit`, `not_WAD_WEClit`).

**Impact.** The lemma holds only for the modified language `WEC` that also requires finitely many incs
(`Counter.lemma_5_3`, `wec_mem_WD`), and Theorem 5.1 (`SD ⊊ WD`) survives with that language (`Counter.thm_5_1`).
Since `SD ⊆ WD`, `WEC_COUNT ∉ SD` (Lemma 5.2) still holds.

**Details.** Property (3) says: "for every finite prefix α such that the (infinite) suffix β has only reads,
eventually all operations in β return the number of incs in α". This is a precise universal condition, the
quiescent-convergence clause of eventual counters [2]. It holds vacuously when there are infinitely many increments,
so `WEC_COUNT` contains such words. A linearizable counter history with infinitely many incs, for example, satisfies
(1)–(3).
- The proof of Lemma 5.3 assumes instead that every word of the language has finitely many incs ("eventually every
  process always picks read operations").
- Diagonal argument: each time `p₀` reports `NO` on a word outside the language, insert one more inc. The limit word
  has infinitely many incs, so it is in the language, yet `p₀` reports `NO` infinitely often. Hence
  `WEC_COUNT ∉ WD` (n = 2), contradicting Lemma 5.3 and Table 1.

### 🔧 Figure 5 (monitor of Lemma 5.3) and Figure 9 (Lemma 6.4)
The monitor rejects correct histories, including words of `SEC_COUNT`: the second clause of Line 06 also runs in
`inc` iterations, so a process that increments after reading a smaller value flags and reports `NO` forever
(`Counter.fig5_not_weakAllDecides`, `Counter.fig9_fails`).

**Impact.** The paper's algorithm is wrong under any reading of the language; a local fix gives a correct monitor for
the modified language (`wecAlg`, proved in `Counter.lemma_5_3`). The same line in Figure 9 has no separate Lean repair.

**Details.** The clause tests `curr_read < snap[i] ∨ curr_read < prev_read`, where in an `inc` iteration
`curr_read` holds the value of the last read. Example independent of the initial value of `curr_read`, which the
paper never sets: `p₀` reads `0`, increments, then reads `1` forever. The read overwrites `curr_read`, and the `inc`
iteration then flags (`0 < snap[0] = 1`).
- In Lean, `p₁` reads `1` throughout; that word is in the modified `WEC` (`Counter.fig5_not_weakAllDecides'`).
- If `p₁` instead reads `0` before the inc and `1` after, the word is in `SEC_COUNT` (by inspection).
- With `curr_read` initially 0, already "`p₀` increments, then all reads return 1" is in `SEC_COUNT` and is
  rejected (`Counter.fig5_not_weakAllDecides`). For Figure 9 against `A_τ`, on a tight execution whose sketch is
  this `SEC_COUNT` word, see `Counter.fig9_fails`.

**Repair.** Apply the clause only to `read` responses, and also flag ill-typed operations (`wecAlg`, proved in
`Counter.lemma_5_3`).

### ✏️ Slips
- Definition 5.1 ("decidability predicate", used in Theorem 5.2): if `P(E)` may be any predicate of the execution,
  Theorem 5.2 is false, since `P(E) := x(E) ∈ L` makes every language decidable (`decides_literal`). We take `P` to be
  any predicate of the reports, as the text intends, and Theorem 5.2 holds (`thm_5_2`). We let `P` see the global report
  trace, including the order and timing of reports.
- Theorem 5.2 is called a "characterization" in the abstract, but it is only a necessary condition, as Section 5.2
  itself notes.
- In Lemma 6.5, "`x₁ ∈ WEC_COUNT`" should be `EC_LED` and `x(H)` should be `x(F')`.

### Typos
- Lemma 4.2's proof concludes "weakly-one" for "weakly-all", and Lemma 4.3's proof cites "weakly-all" for
  "weakly-one".
- Lemma 6.2 ends with "`∉ SD`" for "`∉ PSD`".

## Proof gaps (statements true)

### 🔧 Lemma 4.3 (Figure 4), hence `WOD ⊆ WAD` in Theorem 4.1
Figure 4 reports `YES` iff some counter `C[j]` is unchanged since the process's *previous* snapshot, but a counter
can change infinitely often without changing between two consecutive snapshots of a given process
(`Fig4.fig4_fails`).

**Impact.** The statements are true (`lemma_4_3`, `thm_4_1`), but the printed construction does not prove them.

**Details.** The proof argues that if no counter stabilizes, then all processes report `NO` infinitely often. This
does not follow. Counterexample: `n = 2`, `L = ∅`, and a `V` in which every process alternately reports `YES`/`NO`;
this `V` weakly-one decides `∅`. In the schedule `p₀,p₀,p₁,p₁,…` (two iterations at a time), the `W` of Figure 4
reports `YES` forever at both processes.

**Repair.** Report `NO` iff *every* counter has grown since the last time the process reported `NO`
(`lemma_4_3`, `thm_4_1`).

### 🔧 Lemmas 5.2 and 6.2 (the words in the proofs)
The proofs use `x = <⁺₁ >₁ <₂ >⁰₂ <₁ >⁰₁ …`, where `p₁` reads `0` after its own inc, which violates property (1), so
every continuation `x'` is also outside the language and the argument gives no contradiction
(`Counter.xPaper_cut_not_mem`).

**Impact.** The statements are true, for the modified language and also for Definition 2.7.

**Repair.** A corrected word (other processes read `0`; continuations read `1`) works (`Counter.lemma_5_2`,
`Counter.lemma_6_2`).

### 🔧 Lemmas 5.2 and 6.2 (the step from `WEC_COUNT` to `SEC_COUNT`)
The step "since `SEC ⊂ WEC`, `SEC ∉ SD`" is invalid as an inference: a subset of an undecidable language can be
decidable.

**Impact.** `SEC ∉ SD` is still true, directly or because `SEC` is not real-time oblivious.

**Repair.** The same word argument applies directly to `SEC_COUNT` (`Counter.sec_not_SD`, `Counter.lemma_5_2`,
`Counter.lemma_6_2`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* `n` processes, asynchronous, failure-free fair executions (the executions the definitions
  quantify over). Each process runs the loop of Figure 1:
  * Lines 01–02: pick an invocation chosen by the adversary, then an atomic block;
  * Line 03: send;
  * Line 04: receive a response chosen by the adversary;
  * Lines 05–06: an atomic block that reports one value.
* Blocks are atomic transitions on an *arbitrary* shared memory (any base objects, any
  consensus number) and may read a global clock. This is stronger than the paper's model, so
  the impossibility (Theorem 5.2) holds a fortiori for predicates of the report sequence. The
  positive results are proved in this atomic-block model. Their algorithms use one register
  write or one snapshot per block (Lemma 5.3), or put the extra code of Figures 2–4 inside the
  Line-06 block.
* An execution is a schedule of `pre/send/recv/post` events, constrained only by each process's
  program counter; the configurations and reports of an algorithm along it are derived. The
  input `x(E)` is the subsequence of send/receive symbols. `P` ranges over predicates of the
  report trace, with arbitrary report values.
* Section 6 (timed adversary `A_τ`): separate `tw` (announce in `M`) and `ts` (snapshot) steps.
  The sketch `x~(E)` is read off the `tw`/`ts` order. `PSD`/`PWD` omit the conjunct "∃ `E' ≡ E`
  with `x(E') = x~(E)`", which makes them weaker, so impossibility results for them are
  stronger.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 2.1, 5.2, 5.3; RTO ⇔ closure under adjacent transpositions | `WF`, `RTO`, `rto_iff_swapClosed` | `Words.lean` |
| Defs. 4.1–4.4, 5.1; literal reading of 5.1 | `Decides`, `SD`, `WAD`, `WOD`, `WD`, `decides_literal` | `Model.lean` |
| Claim 3.1 | `isExec_canon`, `hasInput_canon` | `Canonical.lean` |
| **Theorem 5.2** | `thm_5_2`, `rto_of_SD`, `rto_of_WD` | `Characterization.lean` |
| Lemmas 4.1, 4.2, 4.3 (corrected), **Theorem 4.1** | `lemma_4_1`, `lemma_4_2`, `lemma_4_3`, `thm_4_1` | `Classes.lean` |
| Figure 4 is wrong | `Fig4.fig4_fails` | `Fig4Counterexample.lean` |
| Lemma 5.1, Cor. 5.1–5.3, Appendix A | `Objects.lemma_5_1`, `cor_5_1`, `cor_5_2`, `cor_5_3`, `not_rto_*` | `Objects.lean` |
| Lemma 5.2 (corrected words), `SEC_COUNT` not RTO | `Counter.lemma_5_2`, `not_SD_of_extend`, `sec_not_rto`, `sec_not_WD` | `CounterA.lean`, `CounterAWords.lean` |
| Lemma 5.3 (corrected algorithm), **Theorem 5.1** | `Counter.lemma_5_3`, `wec_mem_WD`, `thm_5_1` | `CounterA.lean`, `CounterAInv.lean` |
| inputs of fair executions are well-formed | `wf_of_exec` | `CounterAExec.lean` |
| Figure 5 wrong; literal property (3); Lemma 5.2's word | `fig5_not_weakAllDecides`, `not_WD_WEClit`, `xPaper_cut_not_mem` | `CounterCex.lean` |
| Section 6 model, tight executions | `TIsExec`, `PSDecides`, `PWDecides`, `tcanon`, `psd_closed` | `Timed.lean` |
| Lemma 6.2 (corrected words); Figure 9 is wrong | `Counter.lemma_6_2`, `fig9_fails` | `TimedCounter.lean` |

**Remark on Lemma 5.1.** The paper focuses on `n = 2` and says the argument can be extended to any `n`. Its execution has no steps by `p₃, …, pₙ`,
so it is not well-formed for `n > 2`; adding reads by them fixes this (`Objects.lemma_5_1`).

**Not formalized.**
* Section 6, positive side: Theorem 6.1 and Lemma 6.1 (from [17]), Theorem 6.2
  (linearizability `∈ PSD`, from [17]), Lemma 6.3, Lemma 6.4 (corrected), Theorem 6.3.
* Lemma 6.5 (`EC_LED ∉ PWD`). By inspection its proof is correct up to typos.
* Section 7 (discussion).
* Read/write implementations of snapshots, and fine-grained (non-atomic) blocks for the positive
  results.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: the words used are exhibited and shown well-formed and in or out of
the languages (`x5_mem_SEC`, `regWord_mem_LIN`, `ledWord_mem_EC`, …). `∅` is weakly decidable by
an explicit algorithm (`Fig4.altAlg_weakAll`), and `WEC_COUNT ∈ WD` by an explicit algorithm.
Registers and ledgers use CSLib's Herlihy–Wing histories and `detSpec`
(`Cslib/Computability/Distributed/SharedMemory/HerlihyWing/`).

CSLib candidates (not upstreamed): `rto_iff_swapClosed` (shuffle closure = adjacent
transpositions), `wf_of_exec` (`CounterAExec.lean`), and the generic lemma `legal_seqHist_detSpec` in
`Objects.lean` (the former `linearizable_of_isExtension` is now the shared
`Cslib.SharedMemory.HerlihyWing.Linearizable.of_isExtension`, in
`Cslib/Computability/Distributed/SharedMemory/HerlihyWing/SeqLin.lean`).
