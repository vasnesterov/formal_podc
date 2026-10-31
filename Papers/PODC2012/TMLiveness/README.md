# Liveness of Transactional Memory — PODC 2012

Victor Bushkov, Rachid Guerraoui, Michał Kapałka. *On the liveness of transactional memory.* PODC 2012.
DOI [10.1145/2332432.2332435](https://doi.org/10.1145/2332432.2332435). Formalized version: the PODC
preprint (EPFL Infoscience record 170486, dated 2011/12/5, 10 pages); numbering follows it. We also used
the later write-up of the same results, V. Bushkov and R. Guerraoui, *Liveness in Transactional Memory*
(Euro-TM book chapter, 20 pages), called "the chapter" below. Its Theorem 1, Lemma 1 and Theorem 2 are
the PODC ones.

**Verdict: ⚠️ Minor statement issues.** Theorem 1, Lemma 1 and Theorem 2 hold in the model the paper
intends, in all three fault-prone systems. They even hold with plain serializability, as the
introduction claims. Read literally, the PODC formal framework makes them false: a TM that never answers
satisfies its definitions of opacity and local progress vacuously. Separately, the proof of the
crash-free case had a gap; a new schedule repairs it.

## Mistakes in the paper

* **The PODC formal framework does not force a TM to answer (Theorem 1, Lemma 1, Theorem 2 false if
  read literally).** In §2.2 a TM is an I/O automaton over invocation and response events. It has no
  internal steps and no fairness. §2.3 says a process crashes in an infinite history iff its projection
  is finite and non-empty, and liveness (Definition 3) only constrains the automaton's infinite
  histories. So a process whose invocation is never answered just counts as crashed. Take the
  *silent* TM, which accepts one invocation per process and never responds. With finitely many
  processes it has no infinite history, so it ensures every TM-liveness property. All its transactions
  are live, so it is opaque. Hence it "ensures local progress and opacity in any fault-prone system",
  contradicting Theorem 1. The proofs silently assume that every operation eventually returns
  ("p₁ invokes a read operation … and receives as a response v or A"). The intent is clear from §2.1
  (classical asynchronous shared memory) and from the introduction (local progress as the analogue of
  wait-freedom). The chapter fixes the model: executions consist of steps, a process crashes iff it
  takes finitely many steps, and a process that keeps taking steps in an operation that never returns
  is correct. We prove the results in that model (`theorem_1`, `lemma_1`, `theorem_2`).
  (`PodcModel.silent_ensures`)
* **The crash-free case of the proofs has a gap; the statements are true.** The gap appears once the
  framework is fixed as in the previous item; the PODC proof simply assumes that every invocation is
  answered, and under that stronger assumption Algorithm 2 works with two processes. Algorithm 2
  is part of the proof, not of a stated claim, so this is a proof repair. Algorithm 2 (Strategy 2 in
  the chapter) runs one process at a time until its operation returns, and only p₁ and p₂ ever take
  steps. A crash-free system admits only executions in which every process takes infinitely many
  steps. Such a system may block p₂'s operation until p₁ takes another step: if p₂ runs alone,
  p₁ "crashes", the execution is not admissible, and the obstruction-freedom argument ("if the
  operation does not return, pₖ takes infinitely many steps and is correct") yields nothing. With
  three or more processes the idle processes crash as well. (The PODC definition of a crash as a
  *non-empty* finite projection hides this; see the last item.) Our repair uses a round-robin
  schedule. It needs a sturdier environment strategy, since p₁ must now keep taking steps while p₂
  works. Idle processes invoke filler reads of `x`. p₂ writes `bump a`, where `a` is the first read
  of p₁'s current transaction, and invokes `tryC` only while p₁ is not "ready". p₁ writes a value
  that no committed transaction of p₂ read first, and only once p₂'s last commit wrote a value
  `≠ a` and p₂ has no pending commit request. This handles the "stale" commits that interleaving
  creates: a `tryC` of p₂ that is pending when p₁ is aborted can commit after p₁'s next transaction
  has begun. With this strategy p₁ can never commit, under *any* schedule. In a crash-free system
  the analysis is then short: if p₁ is parasitic, p₂ is correct but makes no progress, so it does
  not run alone; otherwise p₁ is correct and never commits. (`lemma1_crashFree`,
  `stratRun_ne_commit₁`)
* **Degenerate cases.** Theorem 1 says "for every fault-prone system" with no restriction. It fails with
  one process, with no t-variable, or with a single value. In each case a TM that answers every
  operation immediately from a single store and never aborts is opaque and ensures local progress. We assume two processes, a t-variable `x`
  and infinitely many values. The paper's proof writes `v + 1`, so it assumes integer values. Finite
  value sets with at least two elements are not covered by our proof (see Not formalized).
* **Typos and slips.**
  - §2.2 requires `H|p_k ∈ Σ_k^∞` for every history of a TM. Histories are prefix-closed, so this
    forbids accepting any invocation. The chapter allows a final pending invocation
    (`Σ_k^* · Inv_k`).
  - §2.3 defines a crash as a finite *non-empty* projection. Then a process that never takes a step
    is correct and starving, and local progress fails trivially in every history where some process
    does not participate. The chapter drops "non-empty".
  - The proof of Lemma 1 writes `pₙ` for `p₂` twice.
  - Theorem 2 says "serializable safety property". The definition in §5.1 is "strictly serializable",
    while the introduction claims "at least as strong as serializability". Both readings are true
    (`theorem_2`, `theorem_2_serializable`).

**About the chapter** (not the paper judged here). The chapter changes the definition of "runs alone"
to "all other processes crash" but keeps the PODC proof of Lemma 1. In the parasitic-prone case that
proof concludes "p₂ runs alone" while p₁ is parasitic, not crashed. With the chapter's definition,
Lemma 1 and Theorem 2 appear to be false in a crash-free, parasitic-prone system with two processes
(sketch below, not checked in Lean). There,
solo progress is vacuous, and a lock-based TM ensures strict serializability together with "if both
processes are correct, both make progress". In that TM a transaction's first operation takes a global
lock, operations of other processes are aborted, and an aborted process reserves the lock next. We did
not formalize this counterexample. The chapter's crash-prone/parasitic-prone proofs also have the
admissibility gap of the second item.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory with finitely many processes and read/write t-variables. Each step
  belongs to one process: an invocation by an idle process (the environment chooses it), or a step of
  the TM implementation for a process with a pending invocation. In such a step the implementation
  either returns a response or takes an internal step (`tau`). This is the chapter's step-based model.
* The TM is an arbitrary nondeterministic agent. It sees the whole execution so far and chooses each
  step's outcome; its responses must fit the invocation. Every implementation from base objects
  induces such an agent, so the impossibility covers all implementations. The adversary is the
  environment, which picks the invocations and the schedule. There is no randomness.
* Failures (PODC §2.3 with the chapter's crash notion). A process crashes iff it takes finitely many
  steps. It is parasitic iff it invokes infinitely often but is aborted and invokes `tryC` only
  finitely often. It is correct iff neither. It makes progress iff it commits infinitely often. The
  fault-prone systems are those of PODC: crashes and parasitic processes allowed, parasitic-free, or
  crash-free; a system constrains which executions the liveness property must hold for.
* Liveness properties are predicates on executions. This is more general than the paper's sets of
  fair histories, which induce such predicates. "Runs alone" follows PODC: the process is the only
  correct one. Safety (strict serializability, serializability, opacity) is checked on the history of
  every finite execution, using sequences of transactions and the usual read/write semantics.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (§4) | `theorem_1` (also with strict serializability: `theorem_1_ss`) | `Main.lean` |
| Lemma 1 (§5.2) | `lemma_1`; with serializability `lemma_1_serializable` | `Main.lean` |
| Theorem 2 (§5.2) | `theorem_2`; with serializability (introduction's claim) `theorem_2_serializable` | `Main.lean` |
| Local progress is nonblocking and biprogressing (§5.1) | `nonBlocking_localProgress`, `biprogressing_localProgress` | `Main.lean` |
| Opacity and strict serializability are strictly serializable (§5.1) | `EnsuresSafety.ss_of_opaque`, `EnsuresSafety.serializable_of_ss` | `Safety.lean` |
| "Algorithm 1/2 never terminates" (p₁ never commits) | `stratRun_ne_commit₁` | `Strategy.lean` |
| Lemma 1, parasitic-free case (Algorithm 1) | `lemma1_parasiticFree` | `Schedulers.lean` |
| Lemma 1, crash-free case (repaired) | `lemma1_crashFree` | `Schedulers.lean` |
| Literal PODC framework: the silent TM | `PodcModel.silent_ensures` | `PodcModel.lean` |

Sources of the proofs. Definitions and statements follow the PODC version: the three fault-prone
systems, "runs alone", Definitions 4 and 5, strictly serializable safety properties. The execution
model and the crash notion follow the chapter. The opacity conflict that stops p₁ from committing
(PODC Figure 8, chapter Figure 6) is in both versions; we generalize it to stale commits and to
serializability (`conflict_seq`). The parasitic-free case is the chapter's Strategy 1 (PODC
Algorithm 1) with the chapter's argument that operations return. The crash-free case is new. The
derivation of Theorem 2 from Lemma 1, and of Theorem 1 from Theorem 2, is the papers'.

**Not formalized.** Theorem 3 (§6: the automaton `F_gp` ensures opacity and global progress). Finite
value sets with at least two elements. The counterexample to the chapter's version of Lemma 1. The
examples (Figures 1–7, 14–16).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: TMs exist, and the TM that never answers ensures opacity
(`silentTM_opaque`); so `theorem_1` does not hold merely because its hypotheses are unsatisfiable. Only
Mathlib and CSLib's `Nat.eventually_const_of_le_succ` / `Nat.exists_last_of_le` are used; the model
is paper-local. CSLib candidates (marked `-- CSLib candidate`): the TM history/transaction model
(`Model.lean`) and the safety properties with the conflict lemma (`Safety.lean`).
