# Asymmetric Progress Conditions — PODC 2010

Damien Imbs, Michel Raynal, Gadi Taubenfeld. *On Asymmetric Progress Conditions.* PODC 2010. DOI
[10.1145/1835698.1835709](https://doi.org/10.1145/1835698.1835709). Formalized version: the extended
IRISA research report PI-1952 (May 2010, HAL inria-00486977), whose numbering matches the PODC paper and adds
the proofs of Appendix A. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** All results hold for `n ≥ 2` processes. These are the
impossibility of `(n,1)`-liveness from `(n−1)`-port objects (Theorem 1), the `(n,x)`-liveness hierarchy
(Theorems 2, 3, Corollary 1) and the fault-freedom variant (Theorem 4). Theorems 1 and 4 and Lemmas 3–9
are false only in the degenerate one-process case. The proofs of Lemma 6 and Theorem 2 needed repairs.
The arbiter (Theorem 5) and the group-based consensus algorithm (Theorem 6) are correct.

## Mistakes in the paper

### ⚠️ Theorems 1 and 4, Lemmas 3–9 (one process)
With `n = 1` these statements are false: one process that decides its own input is a wait-free consensus
algorithm without any shared object, and it has no bivalent run (`theorem1_false_one_process`,
`lemma3_false_one_process`).

**Impact.** Degenerate case only. The paper never states `n ≥ 2`, but every proof needs two processes
(Lemma 3 picks two processes with different inputs). With `n ≥ 2` all of them are proved.

### Typos and slips
- Lemma 10 says "`y ∈ [1..n]`"; it should be `[1..m]` (groups). Its end marker reads "Lemma 11".

## Proof gaps (statements true)

### 🛠️ Lemma 6 (induction step)
The proof applies Lemma 1 to `x` and `z` (and `xq`, `zq`, `y`), claiming that all objects `p` can access have
the same state there, although the steps of `s` in `z − x` may write registers that `p` can access.

**Impact.** Statement true; repaired (`lemma6`, `CritK.extend`). Lemma 9 has the same proof and the same
repair.

**Details.** Lemma 1 needs equal states of every object `p` may touch in its solo run, not only of the object
of its next step. So the hypothesis of Lemma 1 fails as soon as `s` writes a register before reaching `o`.

**Repair.** The step of `p` on `o` commutes with the steps of `s`, which avoid `o`. So `z p = x p (z − x)` is
an extension of `x p`, and `z q p = x q p (z − x)` one of `x q p`. Compatibility follows without Lemma 1
(`run_comm_of_avoids`, `Avoids.step_of_poised`).

### 🛠️ Theorem 2 (blocking base objects)
The proof applies Lemma 6 (developed only for atomic events) to implementations from non-wait-free
`(n,x)`-live base objects and lets processes "access `o` simultaneously" forever, without saying what a step on
such an object is.

**Impact.** Statement true (for every `0 ≤ x < n − 1`); repaired (`theorem2`).

**Repair.** Base objects are deterministic, caller-aware objects that may withhold a response (`BObj`).
Lemmas 1–6 are proved in this model. The adversary lets every `(n,x)`-live base object behave as `advCons`:
wait-free ports are answered at once, any other process only at a step that directly follows its own previous
step on the object. This is a legal `(n,x)`-live consensus object (`advCons_isLive`). At the configuration of
Lemma 6 take a process `w` wait-free for the implementation but not for `o` (it exists since `x + 1 > x`) and
another process `r ∉ X_o` (it exists since `x + 1 < n`). Alternating `w` and `r` keeps both blocked forever,
so `w` violates wait-freedom.

### 🛠️ Theorem 6 (use of the arbiter's validity)
The proofs of Lemma 10 (Case 2) and Lemma 11 (Case 2) need "a guest (owner) invoked `arbitrate()` *before*
the return", but the arbiter specification of Section 6.1 only says "if no guest (owner) invokes
`arbitrate()`, the value guest (owner) cannot be returned".

**Impact.** Statement true; repaired. The Figure 4 implementation satisfies the real-time version
(`arbiter_validity_owner`, `arbiter_validity_guest`), and Theorem 6 is proved for the inlined algorithm
(`group_agreement`, `group_termination`).

**Details.** The non-⊥ argument for `ARB_VAL[y+1]` (and `VAL[y]`) needs an invocation that happened
before the read. An invocation later in the run would have written the register too late.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory, `n` deterministic processes, crash-stop. Infinite executions are schedules
  `ℕ → Fin n`; a process is correct iff it is scheduled infinitely often. No randomness; the adversary
  chooses the schedule and, for non-wait-free base objects, a legal behaviour.
* Theorems 1–4: every process proposes a binary input at time 0. This only restricts the executions, so the
  impossibility results transfer to the paper's setting. Valency is on configurations, since the system is
  deterministic and outputs persist.
* Base objects (`BObj`): deterministic, possibly caller-dependent, possibly withholding the response.
  Atomic objects always respond. "Atomic register" is generalized to *read/write-like* objects (every
  operation is read-only or a blind overwrite). Ports are a property of the algorithm (`RespectsPorts`).
* `(n,X)`-live consensus (`Live A X`): agreement and validity in all finite executions,
  obstruction-freedom of every process (solo runs from reachable configurations decide), wait-freedom of the
  processes in `X`. Fault-freedom (`FFree`): a process decides in every execution where all processes are
  correct.
* Section 6 (`Arbiter.lean`, `GroupConsensus.lean`): a separate concrete model with proposals of an
  arbitrary type `V`. A process participates iff it takes a step. Registers are atomic, and `GXCONS[g]`
  and the arbiters' `XCONS` (wait-free `(x,x)`-live objects accessed only by group `g`) are atomic
  consensus objects. Figure 4 is inlined for every `ARBITER[g]`. The two tasks of a process alternate
  (T1, T2, T1, …). Deciding does not stop T1, which only adds executions.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 | `lemma1` | `Valency.lean` |
| Lemma 2 | `lemma2` | `Valency.lean` |
| Lemma 3 (`n ≥ 2`) | `lemma3` | `Valency.lean` |
| Lemma 4 | `lemma4` | `Critical.lean` |
| Lemmas 5 and 8 | `lemma5` | `Critical.lean` |
| Lemmas 6 and 9 | `lemma6` | `Critical.lean` |
| Lemma 7 | `lemma7` | `Critical.lean` |
| Theorem 1 | `theorem1`, `theorem1_single` | `Theorems.lean` |
| Theorem 2 | `theorem2` | `Theorems.lean` |
| Theorem 3 | `theorem3_lower`, `theorem3_upper` | `Theorems.lean` |
| Corollary 1 | `Live.mono`, `theorem2`, `corollary1_top` | `Theorems.lean` |
| Theorem 4 | `theorem4` | `Theorems.lean` |
| `(n,x)`-live base objects (adversarial behaviour is legal) | `advCons_isLive` | `LiveCons.lean` |
| `n = 1` counterexamples | `theorem1_false_one_process`, `lemma3_false_one_process` | `NonVacuity.lean` |
| Theorem 5 (arbiter; Lemmas 12–16) | `arbiter_agreement`, `arbiter_validity_owner`, `arbiter_validity_guest`, `arbiter_termination` | `Arbiter.lean` |
| Theorem 6 (Lemma 10, Lemma 11, validity) | `group_termination`, `group_agreement`, `group_validity` | `GroupConsensus.lean` |

Theorems 1 and 4 are proved in a more general form than stated. The objects with at most `n − 1` ports may
be arbitrary, not only `(n−1, n−1)`-live consensus objects; this covers the abstract's "any wait-free objects
with `n − 1` ports". Theorem 1 allows wait-freedom of any nonempty set of processes. Theorem 2 allows
different wait-free sets for different base objects and also `x = 0`. Lemmas 4–6 are proved once from "a
bivalent configuration with a decider", which Lemma 4 (wait-freedom) or Lemma 7 (fault-freedom) supplies, so
Lemmas 8 and 9 come for free. `corollary1_top` rests on a general lemma (`wFree_of_wFree_others`): if every
process but `r` is wait-free and `r` is obstruction-free, then `r` is wait-free. This lemma is also the lower
bound of Theorem 3.

Theorem 5 validity and Theorem 6 validity are proved in the real-time form ("invoked before the return",
"proposed by a process that took a step before the decision").

**Not formalized.** Section 3.5 (Common2 objects; relies on external results) and the remarks of Sections
1.2 and 6.3.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `advCons_isLive` shows that the adversarial base objects are legal `(n,X)`-live consensus objects.
`atomicCons_live` shows that one `n`-port atomic consensus object solves wait-free consensus, so `Live` is
satisfiable and the `n − 1` port bound of Theorem 1 is needed. The model is paper-local (CSLib candidate:
caller-aware blocking objects and the valency toolkit); registers come from CSLib's `ObjSpec` and `RWLike`
(`Cslib/Computability/Distributed/SharedMemory/{Spec,ObjClasses}.lean`).
