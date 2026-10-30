# Differences between the formalization and the paper

Paper: Kuznetsov, Sutra, Toyos-Marfurt, *Conflict-Freedom as a Progress Condition*, PODC 2026,
extended version arXiv 2605.19531v1 (numbering as there).

## Statement-level issues in the paper

All checked statements hold as stated, so no statement-level rule (R2–R4) is needed. The verdict is 🛠️
because of the proof repairs listed below. Under R1, wrong steps inside proofs count as proof repairs.

1. **Lemma A.2 (Adoption), wrong step.** For the case `w_i = True` the proof says "since the snapshot is
   linearizable, necessarily no flag `c_k` is set to False". This is false. Take inputs `a`, `b`, `c` with
   `b ≍ c` and `a` independent of both. `p₂` writes `b`, `p₃` writes `c`, and then `p₂` takes
   `A₂ = {a, b, c}` (here `p₁` wrote `a` and took its snapshot `{a}` earlier). `p₂`'s co-entries are
   `a`, `ε`, `ε`, so it writes `(a, False)`. Then `p₁` writes `(a, True)` and snapshots `B`. Its view
   holds a `False` flag, yet `w₁ = True`. The conclusion still holds: all entries seen by `p₁` equal its
   input. We reprove Adoption differently (`GCA.adoption_of_reach`; see its docstring).
2. **Lemma A.3 (Commitment), wrong step.** "`B_{f(i)} = β`, therefore `f(i) ∈ P_β`" is false.
   Counterexample (independent letters `a`, `c`; inputs `a`, `ε`, `c`):
   - `p₂` writes `A[2] = ε`.
   - `p₁` writes `A[1] = a`, snapshots `A = {a, ε}`, writes `B[1] = (a, True)`, snapshots `B = {(a, True)}`
     and adopts `β₁ = a`: `a₂ = ε ≤ a`, but `b₂ = ⊥`.
   - `p₃` writes `A[3] = c`; `p₂` snapshots `A = {a, ε, c}` and writes `B[2] = (ac, True)`.

   The least output is `β = a`, `P_β = {p₁}`, and `f(p₁) = p₂`, but `b₂ = ac ≠ β`. Commitment still holds
   here: `p₂` later sees `{a, ac}` and commits `a ⊒ ε`. We replace the
   `f`-chain by a maximality argument. Let `β₀` be the least candidate. Among the processes whose input is
   `≤ β₀` and whose `B`-view contains `β₀`, pick one with a ⊆-maximal `B`-view. It must commit, since a
   witness `k` against it would be such a process with a larger `B`-view (`GCA.commitment_of_reach`).
3. **Algorithm 2: coherence is used silently.** "`A_i^co` contains only compatible traces", and Lemma
   A.4's step from incompatible LUBs to incompatible elements, both need *coherence*: a pairwise compatible
   finite set of traces has an upper bound. The paper never states this property. We prove it for traces
   of duplicate-free schedules (`NTrace.compat_of_pairwise`) and make it an axiom of the abstract domain
   (`GCADomain.compat_of_pairwise`).
4. **Theorem 4.4, invariant (I).** The proof claims (I) for *every* round `r > r₀`, using "u_i contains
   only commands from pending operations". The claim is imprecise. Operations that complete between `τ`
   and `τ'` commit at rounds `> r₀`, and their commands may be outside the common prefix `t` of a round
   `r ≤` their commit round. Showing that such commands do not conflict with the others needs an extra
   real-time argument: a command proposed after an operation completed only appears in later rounds. The
   proof only uses (I) at round `r* + 1`, where every operation is pending forever. We prove exactly that
   (`Setup.compat_round`). By Lemma A.1, completed operations committed at rounds `≤ B` (the registers no
   longer change), so their commands lie in the common prefix. The remaining commands belong to pending
   operations of distinct processes and do not conflict.
5. **Proposition 3.4, second item (lock-freedom ⇒ weak conflict-freedom), incomplete proof (not
   formalized).** The proof says "if Φ did not complete, there would exist a suffix in which Φ is pending
   and no other operation takes steps, contradicting lock-freedom". That suffix does not contradict
   lock-freedom as defined: a process with no pending operation is correct and vacuously "completes each of
   its operations". The argument has to let the idle processes invoke an operation and crash. This works
   when every process may invoke some operation, which holds in the paper's model. We prove the other three
   equivalences of Proposition 3.4. This direction is documented but not formalized.

## Observations (no error)

- **Definition 3.2 (2) is weak.** "Some correct process completes all of its operations" also holds when
  some process is idle forever (it has no pending operation, so it is correct, and it completes all of its
  operations vacuously). The Lean definition `WeakConflictFree` follows the paper verbatim, and so does
  `LockFreeP`. Theorem 4.4's proof in fact rules out "every correct process has an operation pending
  forever", which is what the definition means.
- **The model checker** (`ConflictFreedom-work/scripts/gca.py`, 2–4 processes, traces over 3 letters) found
  no violation of any GCA property for Algorithm 2.

## Modelling choices

- **Model.** CSLib's `Cslib.SharedMemory.Impl`: deterministic processes, atomic base objects,
  executions as label sequences (`inv`/`tau`/`ret`), any number of crashes (a process stops taking
  steps). A response is a separate step that accesses no memory.
- **Progress conditions** (`Progress.lean`) are defined on CSLib's `InfExec`.
  - Two operation instances are concurrent iff they are pending at a common time. "Eventually
    conflict-free" means: from some time on, no two simultaneously pending operations of distinct processes
    conflict.
  - "Correct" means: takes infinitely many steps, or eventually has no pending operation.
  - "Every operation of a correct process completes" is `¬ PendingFrom`.
  - We prove that the paper's wait-freedom coincides with CSLib's `WaitFree`, and that the paper's
    obstruction-freedom implies CSLib's `ObstructionFree`.
  - Proposition 3.3's implication CF ⇒ WCF needs finitely many processes (`[Finite P]`), as in the paper
    (`n` processes).
- **Composition: Algorithm 2 is flattened into Algorithm 1.** CSLib has no composition theorem, so
  `Alg1.impl` uses, for every round `r`, Algorithm 2 on its own pair of atomic snapshot objects
  `Obj.A r` and `Obj.B r`. The proofs of Theorems 4.3–4.4 only use the six GCA properties of each round
  (via Theorem 5.1 on the per-round projection `gst C r`) plus wait-freedom (4 steps). This matches the
  paper's modular argument, and it proves the paper's *concrete* algorithm (Alg. 1 + Alg. 2).
- **Line 5 (`max` over `S[1..n]`)** is a collect: `n` separate reads, in index order, not an atomic
  snapshot. Ties in round numbers are broken towards the first maximum read. Committed traces of equal rounds
  are equal (Adoption), so tie-breaking does not matter.
- **Ghost variables** are added to the local state and never influence the behaviour: `hist` holds the
  final local GCA state of each completed round, and `cr` the commit round of each operation.
- **Typeclass hypotheses.** The construction assumes `[Inhabited A.Op]` (an initial dummy command),
  `[Inhabited A.Resp]` (a default for `ret*` of an absent command, never used) and `[NeZero n]`.
- **Traces.** Lemmas 4.1–4.2 are proved for arbitrary schedules with the paper's occurrence-based
  equivalence (`TraceEquiv`). The domain of the GCA objects is the set of traces of **duplicate-free**
  schedules (`NTrace`), which is all Algorithms 1–2 ever handle: commands are unique, and `s · cmd` is
  only formed when `cmd ∉ ops(s)` (`NTrace.snoc`). We prove that the paper's equivalence agrees with the
  simple one on duplicate-free lists (`traceEquiv_iff_nequiv`).
- **Abstract domain for Algorithm 2.** Theorem 5.1 is proved for any `GCADomain`: a meet-semilattice
  with least upper bounds of compatible finite sets, plus coherence. Traces are an instance
  (`TraceDomain.lean`). Validity is stated for any notion of "operations of a trace" that is monotone and
  subadditive on least upper bounds. For traces this is the set of letters.
- **GCA properties** are proved for every reachable state of Algorithm 2, i.e. for every finite
  execution, with `P` = processes that have invoked and `P_r` = processes that have returned. Common
  prefix is stated as "every common lower bound of the inputs is below every output". This is equivalent
  to the paper's `⊓ s_j ≤ t_i`. Commitment additionally assumes that there is at least one participant.
  Taken literally, the paper's Commitment fails when nobody participates (`P = P_r = ∅`), which is a
  degenerate case (R2).
- **`⊥` in line 9 of Algorithm 2.** The commit condition `∀ a_k : a_k ≤ β_i ⟹ b_k ≠ ⊥` is read over
  the non-`⊥` entries of `A_i`. The paper's `⊥` conventions (Appendix A.4) leave this case open. If
  `⊥` counted as `≤ β_i`, then a non-participant would block commitment forever. Elsewhere `⊓` is
  only applied to non-`⊥` traces, except that `a_k^co = ⊥` when `a_k = ⊥`, so the paper's convention
  `⊓ S = ⊥` for `⊥ ∈ S` agrees with ours.
- **Theorem 4.3: incremental linearization.** The paper builds the representative `t̂` block by block
  from the committed traces. We build it incrementally (ghost list `L` in `LinInv`): whenever a larger
  round commits a trace `t`, `L` is extended to a representative of `t`. The new commands belong to
  operations that have not completed, which gives the real-time order.
- **Algorithm 3, Lemmas 6.1–6.2, Theorems 6.4 and 6.6** (conflict-free construction with helping,
  conflict resolution) are not formalized. They were not among the targets.
