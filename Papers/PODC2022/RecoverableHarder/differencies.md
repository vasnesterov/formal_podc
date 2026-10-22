# Differences between the formalization and the paper

Delporte-Gallet, Fatourou, Fauconnier, Ruppert, *When Is Recoverable Consensus Harder Than Consensus?*,
PODC 2022 (arXiv 2205.14213v1, with appendices).

**Summary.** All results of Section 3 (Theorems 8, 14, 16, 22, Observations 5, 6, Lemmas 7, 9–13, 15,
Propositions 18, 19, 21, 30, Corollaries 17, 20) are formalized and true. Ruppert's characterization
(Theorem 3, cited) is formalized as well. One claim used by Corollary 20 is unproved in the paper (we prove it);
two steps of the proofs of Propositions 19 and 21 are false as stated and are repaired. Sections 2 and 4 and
Appendix H are not formalized.

## Modelling choices (not errors)

1. **Model.** The crash-recovery model of CSLib (`SharedMemory/Recoverable.lean`, also used for Ovens'24):
   configurations store the inputs; a crash resets a process to its initial local state (same input); shared
   memory persists; each non-output step is one operation on one object; steps in output states are no-ops.
   The paper's "a process re-executes its code from the beginning" is exactly this.
2. **Binary consensus.** Inputs and outputs are `Bool`. The paper's RC is for arbitrary input values. Necessity
   results (Theorem 14, Ruppert's necessity, Corollary 20's upper bounds, Theorem 22) are therefore *stronger*
   than the paper's (binary consensus is easier); sufficiency results (Theorem 8, Ruppert's sufficiency,
   Corollary 17, Propositions 18, 21's lower bounds) are proved for binary consensus only. The algorithms
   (Figure 2, the tournament) carry values only through registers and work verbatim for any value type; we did
   not formalize the multi-valued version.
3. **Agreement** covers all outputs of all incarnations of all processes (as in the paper). **Recoverable
   wait-freedom** is formalized on infinite executions (CSLib `Solves.prog`); for our algorithms it follows from
   a rank of program counters (`Ranked`, `prog_of_rank`): the code has no loops.
4. **Registers** are generalized to read/write-like objects (`RWLike`) in `RecSolvable`/`WFSolvable` (Ovens'24
   definitions); the algorithms use registers with values `Option Bool` (`⊥ = none`).
5. **Readable** = some read-only operation whose response determines the state (`ObjSpec.Readable`), i.e.
   "returns the entire state" up to encoding. The paper's footnote 3 (piecewise readable) is not formalized.
6. **Unboundedly many objects**: objects are indexed by the nodes (paths `List Bool`) of the tournament tree;
   each algorithm uses finitely many of them.
7. **Recording/discerning definitions** are those of `Papers/PODC2024/RecoverableConsensus/Defs.lean`
   (processes `Fin n`, teams `Bool`, `false` = team `A`). Condition 2/3 of Definition 4 are stated as "if a
   schedule starting on team `x` returns to `q₀`, the other team has exactly one member", which is equivalent.
   Definition 2's sequences "including `j`" are formalized with an explicit position of `j`.
8. **Theorem 14's execution set.** The paper defines valency w.r.t. `E_A` (only `p₁` crashes, never more often
   than the others step). We use Ovens' sets `E*_1` (every process `p` crashes at most `n` times the number of
   steps of processes with smaller identifiers, in every prefix) with the crashing process `c` = the process with
   the *largest* identifier (the paper's `p₁`). The proof only uses that a crash of `c` after a step of another
   process is admissible (Lemma 15) and the generic valency lemmas, which hold for both sets.
9. **Theorem 14, "not all `v_i` equal".** The paper argues with Figure 3(a) (crash of `p₁`, then `p₂` runs
   solo). We use the CSLib lemma `Crit.teams` (Ovens' Lemma 7: both teams are nonempty at a critical
   execution), proved by a similar argument. The "standard argument" that all processes are poised on one object
   is CSLib's `Crit.poised`; that the step "cannot be a read operation" is not needed.
10. **Theorem 14, team construction.** Instead of relabelling processes ("WLOG `i < n`", "swap `p_{n-1}` and
    `p_n`"), we choose the reserve process `r` (the paper's `p_n`) and `ℓ` directly, with `r ≠ c` and
    `v_r ≠ v_ℓ`; the teams are the processes other than `r` with valency `v_ℓ` (team `A`) or not (team `B`).
    In Case 2 we prove that *no* cycle starts on team `B` (Cases a/b/c), without the hypothesis `|A| > 1`.
11. **Proof of Theorem 8 by an invariant.** Lemmas 9–13 reason about the first update `s`, the return `s''` to
    `q₀`, etc. We prove an invariant of configurations (`InvV`, file `Fig2Inv.lean`) with ghost state: the list
    `L` of distinct processes that updated `O` in the current epoch (`O = apply q₀ L`), a flag for the second
    epoch of Lemma 11 (after `O` returned to `q₀`), and the decided value. It is checked for every step of every
    program counter and for crashes. The facts used are exactly those of the paper (Lemma 7 for `X = B`,
    condition 1 for disjointness, conditions 2/3).
12. **Proposition 30 / tournament.** The paper's recursion ("processes on each team agree recursively, then use
    team consensus") is formalized as a generic sequential composition (`comp`, `comp_safe`: an execution of the
    composition is projected to executions of the side algorithms and of the team consensus algorithm, whose
    inputs are the decisions of the sides) and a tournament over a binary tree of object footprints
    (`tournament`). Splits are `kA = min(|A|, k-1)`, `kB = k - kA` (any split with `kA ≤ |A|`, `kB ≤ |B|` works,
    as in the paper); the team consensus instances use the recording data restricted to `kA` processes of `A`
    and `kB` of `B` (`RecOn.comap`) — the paper's remark "the `n`-process team consensus algorithm still works if
    only `k` processes use it". Teams are swapped when `q₀ ∈ Q_B` (`RecOn.swap`).
13. **Consensus numbers.** `ConsensusNumber S n` / `RecConsensusNumber S n` (Ovens'24) quantify over all
    `m > n`; Corollary 17's inequality is `corollary17_bounds` for types having both numbers. Theorem 22 is
    stated as: if no type of the family solves RC among `r + 1`, the family does not solve RC among any
    `m ≥ r + 2` (`RecSolvableSet`: every object read/write-like or of a type of the family).

## Section 3.1 (Theorem 8)

14. **Lemma 7** needs the schedule to be nonempty (the empty schedule trivially takes `q₀` to `q₀`); implicit
    in the paper (`Q_X` uses schedules with a first process).
15. **Lemma 11** (minor gap): "the state of `O` can never be `q₀` after `s'''`, by Lemma 7" assumes the updates
    after `s''` are by distinct processes, which is shown afterwards using this fact; the circularity is
    resolved by induction on the execution (in our invariant: `notin`, `ep2`).
16. **Lemma 13, Case 3** (minor gap): "any run of `p_j` that ends before `s` evaluates the test at line 19 to
    false" — true because `R_A` is never reset and the run of `p_j` that performs `s` reads `R_A = ⊥` later.
17. Registers read at lines 11–12, 26–27 are never `⊥` (needed for outputs to be inputs); implicit in the paper,
    an invariant here (`fstR`).

## Section 3.2 (Theorem 14)

18. Lemma 15 and the case analysis are formalized as in the paper (Figures 3(b)–(f)); see items 8–10.
19. As in the paper, `n ≥ 3`. With Ovens' Theorem 13 the stronger `n`-recording conclusion holds for `n ≥ 2`
    (`theorem14_of_ovens`).

## Section 3.3

20. **Theorem 16.** The choice of the two reserve processes ("WLOG … the ids can be permuted") is made
    explicit (three cases on the team sizes); the proof is the paper's.
21. **Corollary 17** uses Ruppert's necessity (`cons(T) ≥ n` ⇒ `n`-discerning), formalized here
    (`isDiscerning_of_wfSolvable`; readability is not needed for this direction). For `cons(T) ≤ 3` the
    inequality `cons − 2 ≤ rcons` follows from `rcons ≥ 1` (one process).
22. **Proposition 19, proof** — the claim "if `q₀ ≠ (⊥,0,0)` any pair of operations commute or overwrite" is
    false for `q₀ = (w, ⌈n/2⌉−1, ⌊n/2⌋−1)` (both updates reset the object, see README); repaired by adding "or
    reach the same value" (`TT.pair_of_ne_bot`). Also "processes on opposite teams assigned the same operation"
    includes `Read`, which is excluded by the same argument. Statement proved for all `m ≥ n − 1`
    (`TT.not_isRecording`). The type is parametrized as `TT a b` with `⌊n/2⌋ = a + 1`, `⌈n/2⌉ = b + 1`.
23. **Corollary 20** — `cons(T_n) ≤ n` (i.e. `T_n` not `(n+1)`-discerning, with Ruppert's necessity) is used
    but not proved in the paper; proved here for all `m ≥ n + 1` (`TT.not_isDiscerning`). Without it the
    corollary only gives `rcons(T_n) < n ≤ cons(T_n)`.
24. **Proposition 21, proof** — "`q₀` must be `(B,0)`" needs, besides commute/overwrite, the case
    `q₀ = (w, n−1)` where `op_A` and `op_B` reach the same value (excluded with a third process; `SS.pair_disc`). A `Read`
    is excluded by the paper's overwrite argument (every operation overwrites `Read`; the paper's wording "the
    result `ack`" covers only updates, a slip). For `n = 1` the paper uses a read-only
    type; we state the proposition for `n ≥ 2` (`S_1` is trivial).
25. Theorem 3 (Ruppert) sufficiency is formalized with the team consensus algorithm described in Section 3
    (write own register, apply `op_i`, read `O`, decide from `(response, value)`) and the same tournament, in the
    crash-free model (`discTC`, `theorem3_suff`).

## Section 3.4 (Theorem 22)

26. Formalized with the paper's proof (Theorem 14 at the critical execution, then Theorem 8). Ovens'24 shows the
    bound `n + 1` is never attained (`theorem22_ovens`).

## Not formalized

27. Section 2 (Theorem 1, Appendix A: simultaneous crashes), Section 4 (Theorem 23, Corollary 24, the
    universal construction, Appendices F, G), Appendix H (`rcons(stack) = 1`), the multi-valued version of the
    sufficiency results.
