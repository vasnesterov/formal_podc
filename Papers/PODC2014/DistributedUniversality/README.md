# Distributed Universality — PODC 2014

Michel Raynal, Julien Stainer, Gadi Taubenfeld. *Brief Announcement: Distributed Universality:
Contention-Awareness; Wait-Freedom; Object Progress, and Other Properties.* PODC 2014. DOI
[10.1145/2611462.2611503](https://doi.org/10.1145/2611462.2611503). Formalized version: the full
version, IRISA research report PI-2014 (HAL hal-00947657v2, May 2014), with all proofs in the
appendices; numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Weakened.** The construction is **not contention-aware**, contrary to the title, Theorem 2 and
property (4) of the abstract: a process that runs alone, after the other processes have completed their operations
and stopped, can still be forced to use the `k`-SC object, because an `adopt` tag at line N1 does not mean
contention, and no repaired construction is proved. Everything else we checked holds: the constructions of Figures 1
and 2 and of Section 4.3 are linearizable (Lemmas 1–4) and non-blocking (Lemmas 5, 6, Corollary 1, Theorem 1); with
helping they are wait-free (Theorem 3); at least `ℓ` objects progress with `(k, ℓ)`-SC objects (Theorem 4(a)); and
`(k, ℓ)`-SC can be built from a `(k, ℓ)`-universal construction (Theorem 4(b)). Several proofs needed genuine repairs
(Lemma 3, Lemma 6, Theorem 3 and Theorem 4(b)), and properties (3) and (5) of the abstract were not checked.

## Mistakes in the paper

### ❌ Theorem 2 and abstract property (4) (contention-awareness of Figure 2)
With `n = 3` processes and `k = 1` object, processes 1 and 2 run round 1 concurrently, complete their
first operations and stop, and then process 0, running its first operation completely alone, gets
`adopt` at line N1 of round 1 and invokes `kSC[1]` (`theorem_2_not_contention_aware`).

**Impact.** The contention-awareness claim of Figure 2, and of the final construction of Section 4.3,
is false in the paper's own terms. Non-blocking, linearizability and wait-freedom are unaffected. A
weak version holds (`fig2_solo_from_init_no_sc`): in an execution where a single process takes all
the steps from the initial state, no SC object is ever used.

**Details.** Section 4.1 defines a contention-aware construction as one in which "a process … must be
able to complete its operation by accessing only read/write registers in the absence of contention".
The introduction makes this precise as "no contention during the execution of an operation (i.e.,
interval contention)". Section 3.4 defines the execution of an operation: it starts when its issuer
first proposes it (makes it public) and ends when it is returned.

The proof of Theorem 2 (and the text of Section 4.1: "there is at least one object for which `p_i`
has received the tag adopt. This means that there is contention") assumes that an `adopt` at
`AC[2r−1]` reveals contention. But rounds are numbered per process, and the adopt-commit objects of
a round keep the proposals of processes that went through that round earlier. Here is the run:

1. Processes 1 and 2 invoke `AC[1][0]` (line N1) concurrently with their own operations. Both adopt.
2. They go through `kSC[1]`. Process 1 completes its operation in round 1, process 2 in round 2.
3. Both stop. Their next operations were fetched by `next()` but never proposed, so under the paper's
   definition no operation of theirs is in progress.
4. Process 0 starts its first operation and takes every remaining step alone. At `AC[1][0]` it sees
   the stale conflicting proposals, receives `adopt`, and invokes `kSC[1]`.

Every adopt-commit response in the run satisfies even the strong reading of the no-conflict property.
They are exactly the responses of the standard two-phase register implementation cited by the paper,
[13, 28] (`ACImpl.adopt_on_stale`). With the weak reading, which the standard implementation
satisfies, even a fully sequential run fails: process 1 completes an operation alone, then process 0
runs alone, adopts process 1's stale value at `AC[1][0]` and invokes `kSC[1]`
(`theorem_2_not_contention_aware_sequential`, `ACImpl.adopt_after_solo_commit`). The theorem records invocation and return times. Every action
from process 0's invocation on is by process 0. Every operation of processes 1 and 2 that was ever
proposed was returned before that invocation. And `kSC[1]` was untouched by process 0 at that
moment and invoked by it afterwards.

The claim survives only under the reading "a single process has taken steps since the initial state"
(`fig2_solo_from_init_no_sc`). That reading contradicts the paper's explicit "interval contention".
If instead an operation counted as pending from its `next()`, every process that ever started would
be in contention forever, since its next operation is fetched before the previous one returns. The
property would then mean the same weak thing.

**Repair.** No repaired construction is proved. A plausible fix is to let a process skip to rounds
that no one has started yet: publish round numbers and start each operation at the largest
published round plus one.

### ✏️ Slips
- Section 4.3, line 4M of the `(k, ℓ)`-construction: the text has line 4M propose `oper_i[m]` instead of Figure 2's
  `ac_op_i[m]`, and with this version two processes can commit different operations on the same object in the
  same round (`Typo4M.section_4_3_line_4M_unsafe`: `n = 2`, `k = 2`, `ℓ = 1`). The intent is evident: Section 4.3
  says the algorithm is Figure 2 with only `(k, ℓ)`-SC substituted, and all our results use Figure 2's line 4M
  (`Mode.Good`). The run: process A commits at line N1 on both objects and skips lines 2M–4M. Process B adopts A's
  value on object 0 at N1, gets object 1 from SC, and at 4M proposes its own operation to the fresh `AC[2r][0]`,
  where it commits. A and B each return their own operation as the first operation on object 0. Their histories are
  not prefix-comparable, so the run is not linearizable. Both readings of the adopt-commit specification allow
  this run, and with Figure 2's line 4M the same schedule is not executable (`Typo4M.sched_not_executable_fig2`).
- Lemma 5 is stated "∀ r ≥ 1" but needs some process to complete the adopt-commit part of round `r`
  (true in every infinite execution); we state it so.

### Typos
- Line 30 of Figure 1 writes `GSTATE`; the proof of Lemma 2 refers to it as "line 31".
- Corollary 1 is numbered Corollary 2 in Appendix B.

## Proof gaps (statements true)

### 🛠️ Lemma 3 (valid histories)
The definition of "valid" and its "consequence (i)" (`R` determines `VH(R)`) silently assume that an
operation is never committed in two non-consecutive rounds, which the paper argues only inside the
proof of Lemma 3, by a timing case analysis that overlooks some proposers.

**Impact.** Statement true; repaired by an inductive invariant proof (`lemma_3`, `InvB`, `chain_next`).

**Details.** Case (a) of that analysis concludes that `p_j` commits `op_{r1}` in round `r1 + 1`, but it
overlooks processes that adopted `op_{r1}` while already having it in their history: they propose
other operations in round `r1 + 1`. (They wrote `GSTATE` first, so `p_j` still learns `op_{r1}`; this
is our invariant `PIa`.) We replace the paper's "first invalid write" timing argument by state
invariants: the
ghost sequence `G m` and the round in which each element was appended; the knowledge invariant
(`know`: after round `ρ + 1`, a process knows the value of a uniform round `ρ`); and two
proposal/collect invariants (`PIa`, `CI`). The proof also needs the adopt-commit validity in the
form "the returned value was proposed *before* the response". This is standard but not written in
Section 2.1.

### 🛠️ Theorem 3 (wait-freedom with lines L1–L5)
The proof leaves its last case open ("`ℓ_hist_i[m]` is a strict prefix of `ℓ_hist_h[m]` … It perceived
it from an indirect increase") and never explains why the helping index stays aligned among the
processes.

**Impact.** Statement true; repaired with a different argument (`theorem_3`, `Wst`).

**Details.** Fix a correct process `p_j` whose operation `X` on `x` would stay pending forever. Take
the first moment the global sequence of `x` reaches a length `L ≡ j (mod n)`, by the commit of `e` in
round `ρ`. Until the sequence grows again, every proposal for `x` of a round `> ρ` is `e` or `X`, and
from round `ρ + 2` on it is `X` (`Wst.start`, `Wst.step`). Every process with a history of length `L`
helps `p_j`, adopters of `e` learn `e`, and no other operation can be proposed. So the next operation
appended is `X` (`Wst.close`), a contradiction.

### 🔧 Lemma 6 (an object progresses forever)
The proof counts commits, not operations (a round's commit may repeat an operation committed
earlier), and claims that every committed operation becomes visible in `GSTATE`, which fails if the
committer crashes first.

**Impact.** Statement true; repaired (`lemma_6`, with `Exec.G_unbounded` and `NoRepeat`).

**Details.** Repair: an operation committed in round `ρ` is never proposed from round `ρ + 2` on
(`NoRepeat`). So commits in infinitely many rounds give infinitely many distinct operations. Each of
them reaches every process that completes round `ρ + 1` (the knowledge invariant `InvB.know`),
whether or not the committer survives.

### 🔧 Section 3.4 and Lemma 4 with lines L1–L5 (start of an operation)
Theorem 3's lemmas show that with helping an operation can be linearized before its owner proposes it, so the
paper's start of an operation (its first proposal by its issuer) does not contain the linearization point.

**Impact.** Statement true: in Lemma 4, the start of an operation must be its invocation (`next()`), not its first
proposal; we use invocation times (`lemma_4_realtime`).

### 🔧 Theorem 4(b) (`(k, ℓ)`-SC from a `(k, ℓ)`-UC)
The proof instantiates the construction with `k` registers and returns "the values written in these
objects", but with the universal construction used as a black box a read returns the *last* write,
so two processes can return different values for the same entry.

**Impact.** Statement true; repaired with "sticky" first-value objects (`Abstract.scFromUC`). The
paper's register version fails (`Abstract.register_counterexample`).

Full list of differences (including modelling choices and minor imprecisions):
[differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory, `n` processes `Fin n`, `k` objects `Fin k`, crash failures: a crashed
  process stops taking steps, a correct process takes infinitely many (`Exec.Correct`). The scheduler
  and all base-object responses are adversarial.
- One parametrized algorithm (`Model.lean`, `stepFn`) covers Figure 1, Figure 2 (`ca`), lines L1–L5
  (`help`) and `(k, ℓ)`-SC objects (`ℓ`). Theorems hold for every mode with `Mode.Good` (line 4M as
  in Figure 2).
- Adopt-commit and `(k, ℓ)`-SC objects are black boxes with separate invocation and response steps.
  The adversary picks any response allowed by the specification (`acOK`, `scOK`): validity (the value
  was proposed before the response), agreement, no-conflicting-values (weak reading; strong reading
  optional). The specifications are always satisfiable (`NonVacuity.enabled`), and executions where
  every process is correct exist (`NonVacuity.exists_exec`).
- Each step does at most one access to a base object or one register read. A process's writes to its
  own `LAST_OP` registers are merged with the adjacent local step. Loops run in increasing object
  order, and lines 3M/4M handle decided objects first. Line 7's "longest history containing
  `ℓ_hist`" is a deterministic fold, which matters only if histories were not prefix-comparable,
  and they are.
- Operation `c` of process `i` on object `m` is `(i, c)`: static `my_list`s. Outputs are abstracted
  by the history they are computed from (`retH`), which is a prefix of the common sequence.
- Ghost variables record time, the global sequence `G`, invocation/return times and linearization
  points; they do not influence the algorithm.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 | `lemma_1` | `Safety.lean` |
| Lemma 2 | `lemma_2` | `Safety.lean` |
| Lemma 3 | `lemma_3` | `Safety.lean` |
| Lemma 4 (linearizability) | `lemma_4`, `lemma_4_realtime` | `Safety.lean` |
| Lemma 5 (generalized to `ℓ`, Figure 2) | `Lemma5.lemma5_general`, `Lemma5.lemma5` | `Lemma5.lean` |
| Lemma 6, progress part of Theorem 4(a) | `lemma_6` | `Progress2.lean` |
| Corollary 1 (non-blocking, `ℓ`-non-blocking) | `corollary_1` | `Progress2.lean` |
| Theorem 1 | `theorem_1` | `Main.lean` |
| Theorem 2, safety and non-blocking | `lemma_4`, `corollary_1` (mode `ca = true`) | `Safety.lean`, `Progress2.lean` |
| Theorem 2, contention-awareness (false) | `theorem_2_not_contention_aware`, `theorem_2_not_contention_aware_sequential`, `fig2_solo_from_init_no_sc`, `ACImpl.adopt_on_stale` | `ContentionCex.lean`, `ACImpl.lean` |
| Theorem 3 | `theorem_3` | `WaitFree3.lean` |
| Theorem 4(a) | `theorem_4a` (with `lemma_4`) | `Main.lean` |
| Theorem 4(b) | `Abstract.scFromUC`, `Abstract.register_counterexample` | `SCfromUC.lean` |
| Section 4.3, line 4M (typo) | `Typo4M.section_4_3_line_4M_unsafe` | `Typo4M.lean` |
| Section 4.4 (`(k, k−p)`-SC → `(p+1)`-SA; `(k,k)`-SC ≡ consensus) | `Abstract.setAgreement_of_SC`, `Abstract.consensus_of_SC_kk`, `Abstract.SC_kk_of_consensus` | `Hierarchy.lean` |

**Not formalized.**
- Theorem 5 (characterization by `CN_{k,ℓ}`) needs a general theory of implementations and their
  composition, which our abstraction lacks.
- Theorems 6 and 7 (Appendix G.2). Not checked, and not counted as errors. Their proofs seem to use
  `(k, ℓ)`-universality as if it gave wait-free implementations of single objects, which is doubtful
  for `ℓ < k`. A possible counterexample from the set-consensus hierarchy (2-process consensus versus
  `(4,2)`-set agreement, both apparently with `CN_{2,1} = 4`) relies on topological impossibility
  results and is only a lead.
- The obstruction-freedom "generosity" remarks, property (3) of the abstract (stopped objects end in
  the same state at all processes), Appendices A, C, E, F.

**Trust.** No `sorry`, `axiom` or `native_decide`. The listed theorems use only `propext`,
`Classical.choice` and `Quot.sound`. Safety rests on four inductive invariants (`InvA`–`InvD`,
`Reachable.invAll`); counterexamples are checked by `decide` on the executable step function. The
abstract Theorem 4(b) uses CSLib's `ObjSpec`. CSLib candidates: none; the black-box object model is
paper-specific.
