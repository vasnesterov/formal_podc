# Differences between the formalization and the paper

Paper: Castañeda, Rodríguez, *Asynchronous Fault-Tolerant Language Decidability for Runtime
Verification of Distributed Systems*, PODC 2025, arXiv 2502.00191v3 (31 May 2025).

Classification: **false statement**, **false only in a degenerate case**, **proof gap (statement
true)**, **under-specified definition**, **typo**, **modelling choice**.

## Errors and gaps

1. **Proof of Lemma 4.3 / Figure 4 — wrong construction (proof gap, statement true).**
   Figure 4 compares each entry of `C` with the *previous snapshot* and reports `YES` iff some
   entry is unchanged. The proof claims that if `x(E) ∉ L` then "no entry of `C` ever stabilizes,
   and hence all processes report NO infinitely often". This does not follow: an entry can change
   infinitely often while staying unchanged between two consecutive snapshots of a given process.
   Lean counterexample (`Fig4.fig4_fails`): `n = 2`, `L = ∅`, `V` = each process alternately
   reports `YES`/`NO` (it weakly-one and weakly-all decides `∅`); in the execution
   `p₀, p₀, p₁, p₁, p₀, p₀, …` (two iterations at a time) the algorithm `W` of Figure 4 reports
   `YES` forever at both processes, so `W` neither weakly-one nor weakly-all decides `∅`.
   Consequently the proof of `WOD ⊆ WAD` in Theorem 4.1 is broken. The statement is true:
   a process should report `NO` iff *every* entry has grown since the last time *it reported
   `NO`* (`Classes.wodAlg`, `Classes.lemma_4_3`), and Theorem 4.1 holds (`Classes.thm_4_1`).

2. **Definition 5.1 / Theorem 5.2 — "decidability predicate" (under-specified definition).**
   Definition 5.1 writes `P(E)`, a predicate of the execution. Read literally, Theorem 5.2 is
   false: with `P(E) := x(E) ∈ L` every language is `P`-decidable by every algorithm
   (`Model.decides_literal`). The text says that `P` "describes a property that reported values
   satisfy"; we formalize `P` as an arbitrary predicate of the *report trace* (the value reported
   at each global step, with the reporting process), which covers that reading and more
   (`P` may also look at the global order and timing of reports).

3. **Figure 5 (Lemma 5.3) — wrong algorithm (proof gap; statement true for the intended
   reading of property (3)).** The second clause of Line 06 is also evaluated in `inc`
   iterations, where `curr_read` is stale (and never initialized; we use 0). A process that
   increments after a smaller read sets its flag and reports `NO` forever, also on words of the
   language. Independent of the initial value: "`p₀` reads `0`, increments, then reads `1`;
   `p₁` reads `1`" (in `WEC`) is rejected (`Counter.fig5_not_weakAllDecides'`); with `p₁`
   reading `0` before the inc this word is in `SEC_COUNT` (by inspection).
   Lean: `x5` (`p₀` increments once; all reads return 1) is in `SEC_COUNT ⊆ WEC_COUNT`, and in
   its canonical execution `p₀` reports `NO` infinitely often (`Counter.fig5_noSet_infinite`,
   `fig5_not_weakAllDecides`, `fig5_not_weaklyDecides`). Corrected algorithm `wecAlg`: the
   clause is applied only to `read` responses, and ill-typed operations also set the flag
   (`Counter.lemma_5_3`, `Counter.wec_mem_WD`).
4. **Lemma 5.3 (and Table 1's "`WEC_COUNT ∈ WD`") — false statement for Definition 2.7 as
   written; true for a modified language.** Property (3) ("for every finite prefix `α` such that
   the suffix `β` has only reads, eventually all operations in `β` return the number of incs in
   `α`") is a precise universal condition, the quiescent-convergence clause of eventual counters
   from [2]. It is vacuous when there are infinitely many incs, so e.g. every linearizable counter
   history with infinitely many incs satisfies (1)–(3). The proof of Lemma 5.3 instead assumes
   that words of the language have finitely many incs. Lean (`n = 2`): `WEClit` (Definition 2.7
   as written) is neither in `WD` nor in `WAD` (`Counter.not_WD_WEClit`, `not_WAD_WEClit`,
   diagonal argument). Lemma 5.2 (`∉ SD`) also holds for it, via `SD ⊆ WD`. Lemma 5.3, Theorem 5.1 and
   Lemmas 5.2/6.2 are proved for the modified language `WEC` (finitely many incs and eventually
   all reads return their number). Theorem 5.1 (`SD ⊊ WD`) therefore survives with a different
   witness language.
5. **Proof of Lemma 5.2 (and Lemma 6.2) — wrong word (proof gap, statement true).** The word
   `<⁺₁ >₁ <₂ >⁰₂ <₁ >⁰₁ …` violates property (1) (`p₁` reads 0 after its own inc), so the
   continuation `x'` built after the first `NO` need not be in `WEC_COUNT`: for every prefix of
   length ≥ 6 and every continuation it is not (`Counter.xPaper_cut_not_mem`). Also, "since
   `SEC ⊂ WEC`, `SEC ∉ SD`" is not a valid inference. Both lemmas hold with other words
   (`Counter.lemma_5_2`, `Counter.lemma_6_2`, for every `n ≥ 2`); `SEC ∉ SD, WD` also follows
   from Theorem 5.2 since `SEC_COUNT` is not real-time oblivious.
6. **Figure 9 (Lemma 6.4) — same bug as Figure 5.** Lean (timed model, weaker Definition 6.2):
   in the tight execution of `x5 ∈ SEC_COUNT` (sketch = input) `p₀` reports `NO` infinitely
   often (`Counter.fig9_fails`). Moreover (by inspection, not formalized) the proof of Lemma 6.4
   claims that the proof of Lemma 5.3 shows that *every* process reports `NO` infinitely often
   when properties (1)–(3) fail; it shows this only for *some* process, while Definition 6.2
   requires every process.
7. **Lemma 5.1 — only `n = 2`.** The execution `E` has no steps of `p₃, …, pₙ`, so for `n > 2`
   its input is not well-formed. We use words in which the other processes also read; the result
   holds for every `n ≥ 2` (`Objects.lemma_5_1`, `cor_5_1`).
8. **Example 4 / Definition 2.9 (`EC_LED`) — imprecise.** Property (1) says "a permutation of
   the operations" with no process order (we formalize this literally: `PermConsistent`); "every
   append in `α`" is ambiguous for pending appends (we include them, the stronger reading).
   Appendix A is correct for every `n ≥ 2` (`Objects.not_rto_*`, `cor_5_2`, `cor_5_3`); note that
   `α'` itself is sequentially consistent, only its strict prefix is not, as the paper says.

## Modelling choices

* **Atomic blocks, arbitrary memory, global clock.** Each of the blocks of Lines 01–02 and 05–06
  (Figure 1) is one atomic transition of the local state and of an arbitrary shared memory `M`,
  and may read the global step number. This includes all base objects (any consensus number) and
  is the model of the companion formalization. A wait-free block executed solo is such a
  transition; the executions we build run blocks solo, so the impossibility (Theorem 5.2) holds
  a fortiori for the paper's model, for predicates `P` of the sequence of reports. The positive
  results (Lemmas 4.1–4.3, Theorem 4.1, Lemma 5.3) are proven in this atomic-block model; the
  extra code of Figures 2–4 (register accesses and a snapshot) is executed inside the atomic
  block of Line 06.
* **Executions** are schedules of events `pre`/`send`/`recv`/`post` per process (the program
  counter enforces the order of Figure 1); executions are fair and failure-free (every process
  completes infinitely many iterations), exactly the executions the decidability definitions
  quantify over. The adversary chooses the schedule, the invocations and the responses. Every
  iteration reports exactly one value, as in the paper.
* **Input `x(E)`**: the subsequence of send/receive events (`HasInput`, unique by
  `HasInput.unique`).
* **Alphabets** are dependent: `Σᵢ< = I i`, `Σᵢ> = O i` (possibly different per process).
* **Shuffles (Definition 5.2)**: `α' ∈ α|1 ⧢ ⋯ ⧢ α|n` is formalized as `α'|p = α|p` for every
  process `p`, which is equivalent.
* **Well-formed words (Definition 2.1)**: condition (3) (fairness) is automatic for
  `ℕ`-indexed ω-words.
* **Claim 3.1** is `isExec_canon` + `hasInput_canon` (the canonical sequential execution).
* **Proof of Theorem 5.2.** The paper moves a whole block of `pᵢ`'s steps before the event `v`
  and then moves `v'`. We instead build, for every adjacent pair of symbols of different
  processes, an execution with input `x` in which their send/receive events are adjacent
  (`vari`), and transpose them (`swapSched`). We also prove that real-time obliviousness is
  equivalent to closure under such transpositions (`rto_iff_swapClosed`).
* **Theorem 4.1** is proven as `SD ⊆ WAD`, `WAD ↔ WOD`, `WAD ↔ WD`. In Figure 3 the process
  writes `C[i] + 1` (it is the only writer of `C[i]`) instead of `prev[i] + 1`; these coincide.

9. **Inputs of executions are well-formed** — used without proof in the paper ("If `E` is fair
   and failure-free, then `x(E) ∈ Σ^ω`"); proved as `wf_of_exec`.
10. **Lemma 5.2's proof** takes the *first* `NO`; any `NO` suffices (`not_SD_of_extend`).

## Typos and small slips (not formalized)

* Proof of Lemma 4.2: "Thus, `W` weakly-one decides `L`" should be "weakly-all".
* Proof of Lemma 4.3: "by definition of weakly-all decidability" should be "weakly-one".
* Abstract and introduction call Theorem 5.2 a "characterization"; it is only a necessary
  condition (as Section 5.2 itself says: "Theorem 5.2 is not a full characterization").

## Not formalized

* Section 6, positive side: Theorems 6.1, 6.2, Lemma 6.1 (from [17]; the companion
  formalization `Papers/PODC2023/RuntimeVerification/` covers [17]), Lemma 6.3, Lemma 6.4,
  Theorem 6.3; Lemma 6.5 (`EC_LED ∉ PWD`; by inspection correct up to typos: "`x₁ ∈ WEC_COUNT`"
  should be `EC_LED`, `x(H)` should be `x(F')`). Section 7.
* Section 6 model (`Timed.lean`): `A_τ`'s announce and snapshot are separate steps (`tw`, `ts`);
  views are per-process lists of announced invocations (at least as informative as the paper's
  sets); the sketch `x~(E)` is the word of `tw`/`ts` events (the paper builds it from views, up
  to the order inside groups with equal views; in the tight executions we use, these coincide);
  Definitions 6.1/6.2 are formalized *without* the conjunct "∃ `E' ≡ E` with
  `x(E') = x~(E)`", a weaker requirement, so our impossibility results are stronger.
* Lemma 6.2's last line says "`SEC_COUNT ∉ SD`" (should be `PSD`).
