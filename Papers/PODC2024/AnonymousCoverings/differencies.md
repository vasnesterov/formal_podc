# Differences between the formalization and the paper

Paper: G. Losa, E. Gafni, *Understanding Read-Write Wait-Free Coverings in the Fully-Anonymous
Shared-Memory Model*, PODC 2024 (brief announcement); formalized from the full version
arXiv:2405.03573v2. Numbering follows the arXiv version.

**Reading note.** Lemmas 4.5–4.7 and the proof of Theorem 4.8 use the complement `Ā` (an
overline), which plain-text extraction of the PDF drops. Read without the overlines, Lemma 4.5
and Lemma 4.6 look false and Lemma 4.7 looks vacuous. On the rendered page (p. 8–9) all three
are as stated below, and true with `N ≤ |R|`.

## Errors in the paper (statement level)

1. **Lemmas 4.6, 4.7 and Theorem 4.8 need at least `N` registers.** The verdict rests on this
   item. Decided by R4, **not excused**; borderline with ⚠️.
   * With 2 registers and 4 processors with inputs `0, 0, 1, 1`, the two groups take turns
     covering both registers and scanning. Each processor reads only its own group, so the stable
     views `{0}`, `{1}` are incomparable (`theorem_4_8_needs_registers'`).
   * With one register and two processors alternating *write; scan*, the same happens
     (`theorem_4_8_needs_registers`).
   * The same execution refutes Lemma 4.6 for `A = {0}`: at most `1 = |A|` register is last
     written by `Ā = {1}`, `Ā` is live, and `Ā` never reads from `A`
     (`lemma_4_6_needs_registers`). Lemma 4.7 then fails as well, since `A` is closed.
   * Arguments for ❌: Section 2 fixes an arbitrary number `M > 0` of registers, and Section 4
     never restricts it. Section 4 says its pathological executions arise "regardless of the
     number of registers". Its running example (§4.1, the 5-processor extension of Figure 2,
     reused in §5.1 to reason about stable views) has 5 processors and 3 registers.
   * Arguments for ⚠️: the proof of Lemma 4.6 counts `N` registers. Section 2.1 shows that fewer
     than `N` registers are useless for wait-free synchronization, and Section 5 uses `N`
     registers.
   * The `N = 4, M = 2` instance is not degenerate (R2).
   * An exhaustive state-space search over Figure 1 finds no two-source execution for
     `(N, M) = (2, 2)` or `(3, 2)`. In general, `Exec.false_of_two_closed` shows that the two
     groups with minimal views must together have more than `M` members.
   * Section 4 is labelled a warm-up, so Theorem 4.8 is not a headline result (R5): ❌, not 🚨.
   * We prove Lemmas 4.5–4.7 as printed (`Exec.lemma_4_5`; `Exec.lemma_4_6`, `Exec.lemma_4_7`
     with `N ≤ |R|`) and Theorem 4.8 with `N ≤ |R|`.
2. **Lemma 5.2 is false as printed.** Decided by R1 + R3, not excused; not formalized, so it does
   not enter the verdict.
   * Lemma 5.2 says: if `W` is durably stored despite `P` at `t`, every processor that takes a
     step after `t` and then terminates has `W ⊆ view`.
   * Counterexample with `N = 2`: `q` runs solo to level 2 with view `{1}` and stops at label
     `write`. Then `p` (input 2) writes `{1,2}` into both registers, so `W = {1,2}` is durable
     (`|R_W| = 2 > |P \ Q_W| = 1`). `q` then takes its `write`/`output` steps and terminates with
     `W ⊄ view[q]`.
   * The intended statement concerns scans that *start* after `t`. It is true, and our
     `durable_scan` proves it for a stronger durability notion.
   * The paper's derivation of safety from Lemmas 5.2 and 5.3 needs the printed version: a final
     scan of `q` may still be in progress when `p` terminates. So R3 does not excuse it.
   * Our model merges the output step into the last read of the scan, so this counterexample is
     not expressible in it.

## Gaps in proofs (statements true)

3. **Lemma 4.5** is true as printed (`Exec.lemma_4_5`). We prove the stronger bound for registers
   *not* last written by `A`, which also counts registers never written
   (`Exec.card_notWrittenBy_le`).
4. **Lemma 4.6's proof** ignores registers that still hold their initial value. In case
   `|R_t^Ā| < |A|`, the register `p` reads outside `R_t^Ā ∪ (written by Ā)` might be unwritten.
   The fix is to start the argument after every register has been written, which happens because
   `Ā` is live.
   * Our proof of Lemma 4.6 avoids the paper's case split. Suppose `Ā` never reads from `A`. Then
     `Ā` eventually reads only from itself, so by Lemma 4.5 at most `|Ā|` registers are not last
     written by `Ā`. With the hypothesis and `|R| ≥ N`, both counts are then exact.
   * The next write of a live member of `Ā` into a register not last written by `Ā` breaks the
     count (`Exec.false_of_card_notWrittenBy_eq`).
5. **Theorem 4.8's proof is wrong.**
   * It claims, "by the contrapositive of Lemma 4.4", that live processors with a view in `X` (the
     views reachable from a source `S`) read only from `P_X`. Lemma 4.4 gives this for `X̄`
     instead. A processor with view `V₂ ∈ X̄` reading from a view `V₁ ∈ X` would have
     `S ⊆ V₁ ⊆ V₂`. A processor with a view in `X`, however, may read a smaller view in `X̄`.
   * Applied to the closed set `P_X̄`, Lemma 4.7 only says that some member of `P_X` reads from
     `P_X̄`, which is no contradiction.
   * Our proof takes two distinct minimal stable views `S₁ ≠ S₂`. After stabilization, the live
     processors with view `Sᵢ` read only from each other (`readsOnlyFrom_minimal`).
   * By Lemma 4.5, at most `|Aᵢ|` registers are not last written by `Aᵢ`. With
     `M ≥ |A₁| + |A₂|` registers this forces exactly `|A₁|` registers to belong to `A₂` at all
     times. The first round-robin write of an `A₁` member into one of them breaks the count
     (`Exec.false_of_two_closed`).
6. **GST (Definition 4.1) is too weak for Lemma 4.4.** After the paper's GST, a register may still
   hold an old, pre-stabilization view of a live processor. The proof of Lemma 4.4 needs the value
   read to be the writer's stable view.
   * Our `exists_gst` also waits until every register has been rewritten after the views
     stabilized. Such a time exists because a live processor writes round-robin.
   * Lemma 4.4 itself has no time restriction in the paper. It is used only after GST, and we
     prove only that use (`readsOnlyFrom_minimal`).
7. **Wait-freedom (§5.3.3)** invokes Theorem 4.8 for an execution of Figure 3; only the existence of
   a minimal stable view is needed, and the level-increase argument ("they keep incrementing their
   minimum level") needs the register contents to be fresh; formalized as `snapshot_live_false`.
8. **Safety (§5.3.2): the statement is true, the proof does not go through; we give a new proof.**
   Not formalized as counterexamples, but noted:
   * Lemma 5.2 as printed is false (item 2).
   * The deduction of safety from Lemmas 5.2 and 5.3 does not cover two *overlapping* final scans:
     a scan of `q` that is in progress when `p` terminates may already have read (before they
     received `W`) the registers that keep `W` forever.
   * In the proof of Lemma 5.8, "`W` durably stored despite `Q` at the end of `q`'s scan, *thus*
     despite `Q ∪ {p}` at the end of `p`'s scan" assumes the count condition of Definition 5.1 is
     preserved over time; it is not (a write of a value `⊇ W` can turn several "harmless" scanning
     processors into "threats"). Lemma 5.5's "the result follows" does not bound the threats that
     did not write during `p`'s scan.
   Our proof (`Safety.lean`): call `W` durable at `t` if `|R_W(t)| + |H_W(t)| > N` (registers and
   processors containing `W`; Definition 5.1 with `Q = P` but without the exemption of scanning
   processors). (i) If `W` is durable at `t₀`, every scan starting at or after `t₀` ends with a
   view `⊇ W` (`durable_scan`, first-completing-counterexample counting). (ii) Below a terminated
   view `W` there is a chain of nested scans with view `W` and decreasing levels, each nested scan
   written by a new processor with view `W`; with `L ≥ N − 1` the chain must reach a scan at whose
   start `W` is durable (`chain`). (iii) For incomparable terminated views `W`, `W'` the two
   durable starts would each have to precede the other. The proof needs `|R| ≥ N` and `L ≥ N − 1`,
   so it also proves **footnote 4** ("reaching level `N − 1` is sufficient"), which the paper
   states without proof.

## Modelling choices

* **Anonymous memory.** The paper fixes a wiring permutation per processor and lets the algorithms
  choose registers nondeterministically (`with (r ∈ R \ written)`). We let every write/read name a
  *physical* register chosen nondeterministically (subject to the round-robin `written` set and to
  reading each register once per scan). This over-approximates every wiring and every deterministic
  resolution, so all our positive results (Theorem 4.8, wait-freedom) hold for them; the
  counterexamples use concrete schedules that are realizable with suitable wirings.
* **Atomicity.** As in the PlusCal code: a write together with the reset of the read set is one
  step; each read is one step; the end-of-scan computation is merged into the last read of the scan
  (the paper has a separate control step). For Figure 3 the output step is merged too: a processor
  whose level reaches `L` stops at the write label and afterwards only takes idle steps.
* **`written` reset.** Figures 1 and 3 write `written ∪ {r} = P`; we read it as `= R` (typo).
* **Safety** is stated for two processors that are terminated (level `≥ L` at the write label) at
  the same time (`snapshot_safety`) or at different times (`snapshot_safety_outputs`; a terminated
  processor's state is frozen). Generalized to `|R| ≥ |P|` registers and `L ≥ N − 1`; the paper's
  setting is `snapshot_safety_paper`. Validity: own input `∈` view `⊆` inputs (`snapshot_view_valid`).
* **Executions** are infinite sequences of steps; a stopped (terminated) processor can take idle
  steps so that infinite executions exist when everybody terminates. *Live* = infinitely many
  non-idle steps (the paper: infinitely many steps; same for Figure 1). Wait-freedom is stated as:
  no processor is live; equivalently every processor scheduled infinitely often terminates.
* **Inputs/views** are `Finset V`; groups (Section 3) are inputs.
* **Stable view** (Definition 4.2) is "the eventual view of a live processor"; Theorem 4.8 is stated
  as "some stable view is contained in every stable view", plus the unique-source form.
* **Section 3/6** are formalized at the level of outcomes (participants, groups, outputs), not of
  executions: `renaming_of_groupSnapshot` shows that the Bar-Noy–Dolev names computed from any group
  solution of snapshot group-solve adaptive renaming with `n(n+1)/2` names. The paper's "saving
  grace" argument (incomparable snapshots reserve all sizes in between) is not needed: two
  different groups with equal-size snapshots appear together in some output sample, so their
  snapshots are equal and their ranks differ.

## Not formalized

* Section 2.1 (informal impossibility with `N − 1` registers).
* The paper's own induction (Definition 5.6, Lemmas 5.7–5.8) and the informal argument of §5.3.1.
* Section 7 (long-lived snapshot, obstruction-free consensus): the paper only sketches it
  ("clearly", "safety follows like in [4]").
* The 5-processor extension of the Figure 2 execution (Section 4.1).
