# Differences between the formalization and the paper

Paper: Eli Gafni, Giuliano Losa, Michel Raynal, Gadi Taubenfeld. *Brief Announcement: Stranger-Free
Tasks.* PODC 2025, pp. 203–206, DOI 10.1145/3732772.3733545.

## Errors in the paper

1. **Algorithm 1 is not wait-free for any `k ≥ 2`** (Theorem 3.1, §3.1, "Wait-freedom is ensured, even
   with infinitely many processes, because processes that keep interfering … have seen sets that
   converge to the same value or eventually grow in cardinality past `k`"). Counterexample, already
   with **two** processes `a`, `b` (so `|seen| = 2 ≤ k` never triggers line 23): once both have
   `seen = {a, b}`, schedule `a`: first collect; `b`: write; `a`: second collect (fails, `b`'s new
   triple differs); `b`: first collect; `a`: write; `b`: second collect (fails); repeat. Both stay
   pending forever and take infinitely many steps; the execution is one-shot. Converging `seen`
   sets do not help: the double collects keep invalidating each other (the double-collect scan of
   Afek et al. is only obstruction-free without helping). Lean: `exists_livelock`,
   `alg1_not_waitFree`, `theorem_3_1_alg1_not_waitFree`. Found by an explicit-state model checker
   (k = 2, n = 2). Line 21 is modelled literally and is irrelevant to the livelock: the variant
   `seen ∪ A[j][3]` livelocks as well (all seen-sets stay inside `{a, b}`); replacing `> k` by `≥ k`
   in line 23 would only repair `k = 2`.
   Consequently **the upper bound of Theorem 3.1 (wait-free, `k + 1` registers, infinitely many
   processes) is not established for `k ≥ 2`**, and neither is the "infinite hierarchy" of the
   abstract in the wait-free sense. What we prove instead (all `k ≥ 1`, every set of processes,
   possibly infinite): Algorithm 1 is **safe** (`alg1_solves`) and **obstruction-free**
   (`alg1_obstructionFree`); with the lower bound this gives the obstruction-free hierarchy
   (`theorem_3_1_obstructionFree`). Whether `k`-bounded lattice agreement is wait-free solvable with
   `k + 1` registers for unboundedly many processes when `k ≥ 2` remains open here.
   For `k = 1` the paper's claim is true (`alg1_waitFree_one`, `theorem_3_1_k1`, any — also infinite —
   set of processes), but with a different argument than the sketch: a process `x ≠ p` can write
   `A[1]` only as its second write and only if it read `⊥` from `A[1]` before anybody wrote it, so only
   finitely many interfering writes on `A[1]` exist, while every two failed iterations of `p` need one.

2. **Gap in the safety argument of §3.1 (the claim is true).** "`k` processes are not
   enough to obliterate all `k + 1` registers before they have to read the whole array" — with more
   than `k + 1` participants, `k + 1` processes poised on distinct registers *can* obliterate all
   registers after a successful snapshot. The claim (containment) is nevertheless true; our proof
   (`Alg1SafetyObliterate.lean`, `card_union_of_obliterate`): after a configuration in which every
   register is `S`-dirty (`S ⊆ seen`), a later write is "type 0" if its writer has not completed a
   collect since, else "type 1"; a clean type-1 write carries a seen-set of size `≥ k + 1`, each
   process makes at most one type-0 write, so if all `k + 1` registers become clean the union of
   their seen-sets has `≥ k + 1` elements — impossible for a later snapshot output of size `≤ k`.
   The double-collect ⇒ atomic snapshot step needs freshness of `(id, seq)` (`Alg1SafetySnapshot.lean`).

3. **§3.2, "and thus `k`-bounded lattice agreement for `k + 1` processes is stranger-free"**: the
   routine step from "`j` belongs to `i`'s output" to "`j` appears in `i`'s view" (validity plus
   indistinguishability) is omitted. Formalizing it needs a causal-erasure argument: if `j` did not appear in `i`'s view, erase the causal
   future of `j` to get an execution in which `j` does not participate but `i` outputs the same set
   (`Impl.fullInfo_exists_erase`, `mentions_of_mem_output`). The claim holds
   (`boundedLA_strangerFree`), for every progress condition.

## Modelling choices / changed definitions

* **Model.** CSLib `Cslib.SharedMemory`: deterministic processes, atomic MWMR registers
  (`RegFamily ι V v₀`, any value type), one shared-memory access per step, returning an output is a
  separate step. A task is an `Impl` of the dummy object `taskObj In Out`; inputs/outputs are the
  first invocation/response (`inputs`, `outputs`); the task relation `Δ` is required on every finite
  **one-shot** execution (`Impl.Solves`), i.e. on partial executions (participating = has invoked).
  Every result assumes the relevant processes are *allowed* to invoke (`Impl.allowed`).
* **Full-information version.** `Impl.fullInfo I` stores in registers the pair (value of `I`, view of
  the writer) and in processes the pair (state of `I`, view). The paper recomputes `I`'s state from the
  view; since `I` is deterministic the cached state is a function of the view, so the behaviour is the
  same. Views are `View.mk owner hist` with `hist` a list of inputs and read values (`none` = initial
  value `⊥`); "`q` appears in the view" is `View.Mentions` (identifiers occurring inside *inputs* do
  not count). The paper's remark "an algorithm and its full-information version solve the same tasks
  and use the same number of registers" is proved (`fullInfo_solves`, `fullInfo_waitFree`,
  `fullInfo_obstructionFree`, `fullInfo_oneShotOF`, same register index type `ι`, `fullInfo_covers`).
* **Stranger-freedom** (`Task.StrangerFree T prog`) quantifies over the full-information versions of
  all read/write algorithms solving `T` with progress `prog` (instead of "all full-information
  algorithms"; every full-information algorithm is behaviourally its own full-information version),
  that accept every input at every process (`∀ p x, I.allowed p x`; otherwise the hypothesis would
  be stronger than the paper's for input-dependent tasks), over one-shot executions, and compares the views at the end of the execution (which, in one-shot
  executions, are the views at output time). `prog = .waitFree` is the paper's definition. The
  obstruction-free variant of Theorem 2.1 (remark after its proof) needs the **stronger hypothesis**
  `T.StrangerFree .obstructionFree` (quantifying over obstruction-free algorithms); the paper does not
  say this. For `k`-bounded lattice agreement both hold.
* **Theorem 2.1** is stated for a finite process type `P` with `|P| = n ≥ 2`, a finite register index
  type `ι`, a nonempty input type, and an algorithm accepting every input at every process: `n ≤ |ι|`; the covering form (`covering_of_strangerFree`, any `n ≥ 2` distinct processes,
  any `P`, `ι`) gives a one-shot execution where the `n` processes cover `n` distinct registers. Only
  obstruction-freedom on one-shot executions (`OneShotOF`) is used.
* **Proof of Theorem 2.1.** Invariant (3) "`p₁` has not been written into any register" is
  formalized as `FIClean p₁`: `p₁` appears in no register and in no view other than its own (needed:
  the paper's "`p_{j+1}` cannot know that `p₁` is active" also requires that no other process carries
  information about `p₁`). Instead of "let all processes run until they terminate" after the block
  write we only run `p₁` solo (obstruction-freedom suffices). "`δ₂` would be indistinguishable from the
  run without `p_{j+1}`" is realized by comparing the configurations before `p_{j+1}` started and after
  its solo run: they agree on `p₁ … p_j` and outside `R`, hence agree completely after the block write
  (`Impl.blockWrite_agreeOn`), which transports `FIClean p_{j+1}`.
* **`k`-bounded lattice agreement**: outputs are `Finset P`; containment is required for outputs of
  cardinality `≤ k` that have been produced so far.
* **Algorithm 1** (`Alg1.lean`): registers indexed by `Fin (k + 1)` (0-based); initial triple
  `⟨none, 0, ∅⟩`; each register access is an atomic step, local computation is folded into the
  preceding access; the decision (lines 23–27) happens in the step of the last read of the second
  collect; line 21 is taken literally (`seen ∪ collect[j][3]`, a no-op — probably a typo for `A[j][3]`);
  a process that has output and is invoked again returns the same output immediately.
* **Lower bound of Theorem 3.1** is stated for obstruction-free algorithms (hence also wait-free) for
  `k ≥ 1` and `|P| = k + 1`, every process allowed to participate.

## Not formalized

* The anonymous-memory / anonymous-process remarks at the end of §3.1 (Guerraoui–Ruppert collect
  `k(n − 1) + 2` times).
* The introduction's claims about Delporte-Gallet et al., splitters, adopt-commit, and the
  Moir–Anderson renaming discussion / open question.
