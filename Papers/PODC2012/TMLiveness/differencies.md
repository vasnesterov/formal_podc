# Differences between the formalization and the paper

Paper: Bushkov, Guerraoui, Kapałka, *On the liveness of transactional memory*, PODC 2012 (preprint
dated 2011/12/5, EPFL Infoscience 170486). "Chapter" = Bushkov, Guerraoui, *Liveness in Transactional
Memory* (Euro-TM book chapter), the later write-up of the same results.

## Statement-level issues (with the rule from `verdicts.md` that decides them)

1. **PODC framework is vacuous for TMs that do not answer** (R4 implied assumption / R3 evident intent →
   ⚠️). In PODC §2.2–3.1 a TM is an I/O automaton over events with no internal steps and no fairness.
   A process crashes iff its projection is finite and non-empty, and Definition 3 constrains only
   infinite histories. The silent TM (accept one invocation per process, never respond) has no
   infinite history when there are finitely many processes, and it is opaque. So it ensures local
   progress and opacity in every fault-prone system, contradicting Theorem 1 read literally
   (`PodcModel.silent_ensures`). The same TM satisfies the hypotheses of Lemma 1 vacuously and has no
   infinite history at all, so Lemma 1 and Theorem 2 fail literally too. Why ⚠️ and not ❌: the
   assumption that a process taking steps is eventually answered holds in the paper's own §2.1 model
   ("classical asynchronous shared memory"). The proofs use it explicitly ("receives as a response"),
   and local progress is presented as the analogue of wait-freedom. The chapter version repairs the
   framework exactly this way: steps, and crash = finitely many steps. Borderline call: the fix
   changes the model (I/O automaton → step semantics), but not the statements.
2. **Degenerate parameters** (R2 → ⚠️). The theorems say "for every fault-prone system" with no
   restriction on the number of processes `n`, the t-variables `X` or the values `V`. They fail for
   `n = 1`, `X = ∅` or `|V| = 1`: a TM answering every operation at once from one store and never
   aborting is opaque and ensures local progress. We assume `p₁ ≠ p₂`, `x : X` and `Infinite V` (the
   paper's proof writes `v + 1`, i.e. integer values). Not formalized as Lean counterexamples.
3. **Theorem 2's safety hypothesis.** The statement says "serializable safety property", §5.1 defines
   "strictly serializable safety property", and the introduction claims "at least as strong as
   serializability". We prove the strongest reading, for serializability without real-time order
   (`theorem_2_serializable`), and the §5.1 reading (`theorem_2`). No issue.

## Proof-level issues (→ 🛠️ if alone)

4. **Crash-free case (Algorithm 2 / chapter Strategy 2)** (R1: the algorithm is part of the proof, not
   of a stated claim → 🛠️ if alone). In the literal PODC framework the proof just assumes that every
   invocation is answered; under that assumption Algorithm 2 works for `n = 2`. The gap appears in the
   repaired framework (item 1, the chapter's step model). The proof schedules one process at a time
   until its operation returns, and only `p₁`, `p₂` take steps. In a crash-free system this execution
   is admissible only if every operation returns while its process runs alone, and only when
   `n = 2`. In the step model a TM may legitimately make `p₂` wait until `p₁` steps again; then the
   sequential execution is not admissible, and the "operations are obstruction-free" argument proves
   nothing. With `n ≥ 3` the idle processes crash. (In the PODC literal model idle processes are
   *correct*, by the "non-empty" crash definition: item 9.) Repair: round-robin schedule
   (`rrSched`), a strategy robust to interleaving (`Setup.script`), and a new analysis
   (`lemma1_crashFree`). The robust strategy:
   - filler reads for idle processes;
   - `p₂` writes `bump a` for the *current* first read `a` of `p₁`'s transaction, and invokes `tryC`
     only when `p₁` is not ready;
   - `p₁` writes only when the last committed transaction of `p₂` that had not completed when `T₁`
     began wrote a value `≠ a`, and `p₂` has no pending `tryC`. It then writes a value that *no*
     committed transaction of `p₂` read first (`Setup.pick`, using `Infinite V`).

   This handles stale commits: a `tryC` of `p₂` pending when `T₁` is aborted may commit after the next
   `T₁` began. The key invariant is `Setup.Good`, preserved by every scheduler
   (`good_step_inv`, `good_step_res`). The conflict is `conflict_seq`, a generalization of PODC
   Figure 8 to several concurrent commits of `p₂`.
5. **Parasitic-free case.** The paper's Algorithm 1 argument (with the chapter's "operations return,
   otherwise that process runs alone" step) goes through. We use the same scripts as in item 4 with
   the sequential schedule `seqSched` (`lemma1_parasiticFree`). The case analysis is: `p₁` crashes,
   `p₂` crashes, or neither. In the last case `p₂` is not parasitic, because a parasitic `p₂` freezes
   the schedule on `p₂` and `p₁` would crash. The paper's text instead argues per step of the
   algorithm.
6. **"Both read the same v" (PODC Algorithms 1, 2 write `v + 1` for each process's own read).** For a
   committing `T₁` this follows from opacity or strict serializability of prefixes: both reads must
   return the current committed value. The PODC text does not say so. The chapter uses cross values
   (`p₂` writes `v' + 1`, `p₁` writes `v'' + 1`), which needs no such argument. We use cross values,
   generalized as in item 4.

## Definitions and modelling choices

7. **Execution model.** We use the chapter's step-based model. An execution is an infinite sequence
   of steps: invocations by idle processes, responses, and internal steps `tau k` of a process with a
   pending invocation. The TM is any nondeterministic agent that knows the whole execution so far
   (`TM.next`). This only strengthens the impossibility.
8. **Crash.** Chapter definition: finitely many steps (an empty projection counts as crashed).
9. **PODC's "finite non-empty" crash definition** (typo, R3). With it, a process that never takes a
   step is correct and starving, so every history in which some process does not participate
   violates local progress. The chapter drops "non-empty". We follow the chapter.
10. **PODC's well-formedness `H|p_k ∈ Σ_k^∞`** (typo, R3). Histories are prefix-closed, so a literal
    reading forbids any pending invocation. We use the chapter's `Σ_k^∞ ∪ Σ_k^* · Inv_k` in
    `PodcModel`. In the step model well-formedness holds by construction.
11. **Responses record their invocation** (`Ev.res k i r`). This is redundant in well-formed histories
    and convenient for computing operations.
12. **Transactions** are identified as `(k, j)`, the `j`-th transaction of `k`. Their data is computed
    by one fold (`info`). The real-time order (`Prec`) says that some prefix of the history contains
    all of `t₁` and nothing of `t₂`; this is the paper's "last event of `t₁` precedes the first event
    of `t₂`".
13. **Sequential histories** are represented as sequences `σ` of transactions. Equivalence and the
    real-time order are expressed through `σ`.
14. **Legality** uses the standard semantics: reads see the transaction's own earlier writes, else the
    last committed write before it in `σ`, else `init`. This matches PODC's definition. The chapter's
    variant counts own writes only in committing transactions; that matters only for live or aborted
    transactions reading their own writes, which our strategy never does.
15. **Strict serializability.** PODC removes all commit-pending transactions; the chapter lets some of
    them commit. We follow the chapter. This is weaker, so a TM ensuring the PODC notion ensures ours
    and the impossibility covers both. **Opacity**: PODC aborts all incomplete transactions; the
    chapter (and we) may commit some commit-pending ones. The same remark applies.
16. **Serializability** (`Serializable`): `σ` respects the order of each process's transactions but
    not the real-time order. Used for the stronger versions `lemma_1_serializable` and
    `theorem_2_serializable`.
17. **TM-liveness properties** are predicates on executions rather than sets of fair histories. A set
    `L` of fair histories induces `{α | F_α ∈ L}`; correctness, progress and "runs alone" are functions
    of `F_α`, so Definitions 4 and 5 transfer and Theorem 2 for predicates implies the paper's version.
    The hypothesis `L_local ⊆ L` (Definition 1) is not needed for Theorem 2 and is dropped
    (`IsTMLiveness` is defined, and local progress satisfies it).
18. **Runs alone** follows PODC (§3.2.3): the process is correct and no other process is correct. The
    chapter's definition (all other processes crash) is weaker as a hypothesis of solo progress, and
    with it the chapter's Lemma 1 is false (README, "About the chapter"); not formalized.
19. **Fault-prone systems** (`FaultProne.Admissible`): crashes and parasitic processes allowed (all
    executions), parasitic-free (no parasitic process), crash-free (no crash). These are the three
    systems of PODC §2.3; the chapter's crash-prone and parasitic-prone systems cover them.
20. **Lemma 1's conclusion** also states that the execution is admitted by the system. The paper's
    proof needs this to derive Theorem 2 but does not state it. We prove it for every fault-prone
    system separately. The PODC phrase "in any fault-prone system" is read as "in a given fault-prone
    system", which is the stronger reading.
21. **Finitely many processes** (`Fintype P`) is used only for round-robin scheduling. The paper has
    `n` processes.

## Not formalized

- Theorem 3 (§6): the automaton `F_gp` ensures opacity and global progress in every fault-prone system.
- Finite value sets with `2 ≤ |V| < ∞`. Our strategy picks a value outside all first reads of `p₂`,
  which needs infinitely many values.
- The counterexample to the chapter's Lemma 1 and Theorem 2 (with its definition of "runs alone").
- The examples (Figures 1–7, 14–16) and the remarks on existing TM implementations (§3.2).
