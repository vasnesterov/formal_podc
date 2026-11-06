# The Recoverable Consensus Hierarchy — PODC 2019

Wojciech Golab. *Brief Announcement: The Recoverable Consensus Hierarchy.* PODC 2019. DOI
[10.1145/3293611.3331574](https://doi.org/10.1145/3293611.3331574). Formalized version: the full version
*Recoverable Consensus in Shared Memory*, arXiv [1804.10597](https://arxiv.org/abs/1804.10597) v2 (May 2018);
numbering follows it.

**Verdict: 🔧 Easy fix.** All four results hold: the two transformations (Figure 1 under simultaneous
failures, Theorem 1; Figure 2 with `f + 1` consensus instances under at most `f` independent failures, Theorem 2)
and the two lower bounds (`f` readable test-and-set objects do not suffice, Theorem 3; `f` consensus objects do
not suffice for generic constructions, Theorem 6). The proof of Theorem 3 rests on a restricted failure model
(Assumption 1) in which its Case C is false for *readable* TAS, and changing one condition of that model repairs
it; the multi-register reads of Figures 1–2 need only a local argument. The Θ(`f`) tightness for TAS was not checked.

## Mistakes in the paper

### ✏️ Slips
- Section 5, after Corollary 4: "2-process conventional consensus implemented using a single TAS object and no
  additional read/write registers" is impossible (the loser must learn the winner's input); with `O(1)` registers
  per instance, as the abstract says, the intended `O(f)` space bound holds.
- Theorem 2 sketch and Lemma 15, Case 2: "`R[z] > R[j] = x`" should be `R[j] = x + 1`.
- Lemma 14, Case B: "line 17 in its own iteration `k_i` or higher" should be `k_i + 1`.

### Typos
- Lemma 13: there is no condition `k > 0` at line 19; the loop is simply empty.
- Theorem 2 sketch, validity: "at line 4" should be line 21.
- Lemma 9: Case 3 "reads `P[j] = ⊥` at line 10" should be line 9; Cases 4–5 say `p_j` for `p_i`.

## Proof gaps (statements true)

### 🔧 Theorem 3 (Assumption 1 and Case C)
With Assumption 1 as written — `p₁` crashes right after its first *access* to a TAS object — Case C ("`p₁` has
accessed `T` already, so `T` holds 1") is false when that access was a read of the readable TAS, and the
restricted-model statement the proof establishes is then false (`literal_assumption1_rcorrect`).

**Impact.** Statement true; repaired by counting only `tas` operations in Assumption 1 (`theorem3`,
`corollary4`).

**Details.** In the critical state both processes may be poised to apply `tas` to an object `T` that still holds
`0` but that `p₁` has already read. Then `p₁`'s `tas` is not its first access, so no crash follows (Case B does
not apply), and the two `tas` operations do not commute (Case C's premise fails). This is not just a missing case:
the algorithm `A₀` (`P[i] := v`; read `T`; `tas T`; the winner returns `v`, the loser returns the other's `P`),
with one rTAS object and two registers, satisfies agreement, validity and recoverable wait-freedom on **every**
execution obeying the literal Assumption 1 (`p₁` crashes once, after its dummy read, before any `tas`), so no
argument confined to those executions can derive a contradiction. `A₀` is of course incorrect in the real model
(`A₀_not_solvesP`, from Theorem 3).

**Repair.** `p₁` crashes right after its first `tas` on each rTAS object (reads do not count). An rTAS object on
which `p₁` has applied `tas` holds `1` (`Theorem3.tasInv`), so Case B applies whenever the object holds `0` and Case
C whenever it holds `1`; there are still at most as many crashes as rTAS objects. We also supply the steps the
proof omits: an initial bivalent state (`biv_init`), termination of the critical-state construction
(`exists_crit`: finitely many crashes, so some process steps crash-free forever and must decide), agreement of all
outputs in restricted executions although the paper's agreement is only between distinct processes (`agree'`), and
the non-symmetric Case D in which `p₂` reads and `p₁` runs solo with its forced crashes (`contra_a`).

### 🔧 Lemmas 9, 10, 14 (non-atomic multi-register reads)
The proofs for Figures 1 and 2 treat the two-register tests of Figure 1 (lines 2, 9, 11) and the scan of
`R[1..n]` in Figure 2 (lines 24–25) as atomic snapshots.

**Impact.** Statements true; the Lean proofs handle the reads one at a time (`Fig1.theorem1`, `Fig2.lemma14`).

**Details.** Figure 1: `P[i]` changes only when `p_i` writes it and never returns to `⊥`, and an idle process
whose proposal is recorded implies that nobody is in lines 3–5 (used implicitly in Lemmas 9–10). Figure 2: the
argument "when `p_i` reached line 26 no process had reached line 17 of a later iteration" holds per checked process;
the invariant is "the commitment holds, or some not-yet-checked process has `R ≥ k_i + 2`".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- CSLib's crash-recovery shared-memory model (`Cslib.SharedMemory.Recoverable`): asynchronous, deterministic
  processes, one atomic operation per step, objects with deterministic sequential specifications. A crash resets
  the crashed process's local state to its initial state (holding its input); shared objects are non-volatile.
  No randomization; the adversary chooses the schedule and the crashes.
- *Independent failures*: `Ev.crash p`; `AtMost f` = at most `f` crashes in total. *Simultaneous failures*: our
  event type `SEv` with `crashAll` (resets every process), arbitrarily many crashes.
- Binary consensus (CSLib's inputs/outputs are `Bool`): impossibility results are slightly stronger, algorithms
  slightly weaker than the paper's multi-valued ones.
- Specification: the paper's recoverable consensus `SolvesP` (agreement between distinct processes, validity,
  recoverable wait-freedom: a process that steps forever without crashing after time `N` outputs after `N`) for
  the lower bounds; the algorithms satisfy the stronger CSLib `Solves` (all outputs agree, also those of one process
  in different incarnations) resp. `SolvesS`.
- The conventional consensus algorithms `C`, `C[k]` of Figures 1–2 are atomic sticky consensus objects
  (`consObj`); each process accesses each of them at most once (Lemmas 8, 12), so they are used within their
  contract. Theorem 6's `n`-consensus objects are the same atomic objects over any value type.
- Lower bounds: registers generalized to read/write-like objects (`ObjSpec.RWLike`); the bounds hold for every `f`
  (the paper: `f > 0`) and any number of processes of which two participate.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 = Theorem 11 (Figure 1, simultaneous failures) | `Fig1.theorem1` | `Fig1.lean` |
| Lemma 8 (`C` accessed at most once) | `Fig1.lemma8` | `Fig1.lean` |
| Theorem 2 = Theorem 16 (Figure 2, ≤ `f` independent failures) | `Fig2.theorem16`, `Fig2.theorem16P` | `Fig2Prog.lean` |
| Lemma 12 (each `C[k]` accessed at most once) | `Fig2.lemma12` | `Fig2Safe.lean` |
| Lemma 13 (validity, every execution) | `Fig2.lemma13` | `Fig2Safe.lean` |
| Lemma 14 (agreement, every execution) | `Fig2.lemma14` | `Fig2Safe.lean` |
| Lemma 15 (recoverable wait-freedom, ≤ `f` failures) | `Fig2.lemma15` | `Fig2Prog.lean` |
| Figure 2 is generic (remark after Definition 5) | `Fig2.fig2_generic` | `Fig2Generic.lean` |
| Theorem 3 | `theorem3`, `theorem3_gen` | `Theorem3.lean` |
| Corollary 4 | `corollary4`, `corollary4'` | `Theorem3.lean` |
| Definition 5 | `Generic` | `Theorem6.lean` |
| Theorem 6 | `theorem6`, `theorem6_gen` | `Theorem6.lean` |
| Corollary 7 | `corollary7` | `Theorem6.lean` |
| Theorem 6 + Theorem 16: exactly `f + 1` objects for generic constructions | `generic_consensus_objects_tight` | `Tightness.lean` |
| Proof gap of Theorem 3: literal Assumption 1 admits a correct algorithm | `Assumption1Gap.literal_assumption1_rcorrect`, `Assumption1Gap.A₀_not_solvesP` | `Assumption1Gap.lean` |

The restricted failure model of Assumptions 1–2 is a reusable framework (`Restricted.lean`: schedules, the crash
bookkeeping, `RCorrect`, `SolvesP.rcorrect`; `Valency.lean`: valency, `exists_crit`, `contra_a`/`contra_b`;
`Critical.lean`: initial bivalence and the per-case lemmas). Proof remark: for consensus objects (Theorem 6) the
paper's Case C is correct, since a consensus object has no read. In Lemma 15, Case 1, a process can also reach
iteration `k` by skipping at line 16 after a crash; the invariant `PInv` covers it.

**Not formalized.** Θ(`f`) tightness for TAS (needs composing Figure 2 with a TAS-based 2-process consensus
implementation), the composition theorem replacing the atomic consensus objects `C`, `C[k]` by conventional
implementations, the universality claims of Section 6, the consensus-number corollaries ("level two remains level
two"), and the broad reading of abstract claim (iv) (arbitrary types `T` with consensus number `n`, see
differencies.md).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: the specification is satisfiable — Figure 2 solves it with `f + 1` consensus objects
(`generic_consensus_objects_tight`), Figure 1 under simultaneous failures. `Assumption1Gap.lean` uses a file-local
`attribute [local reducible] Sum.elim` (tactic convenience only). CSLib candidates: `consObj` (`Defs.lean`),
`Fig1.saccCount` (access counts in the simultaneous model), `Fig2.prog_of_rank_from` (progress from a rank that
decreases from time `N` on).
