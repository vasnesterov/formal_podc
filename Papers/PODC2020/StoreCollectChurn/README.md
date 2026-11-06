# Store-Collect in the Presence of Continuous Churn — PODC 2020

Hagit Attiya, Sweta Kumari, Archit Somani, Jennifer L. Welch. *Brief Announcement: Collect in the
Presence of Continuous Churn with Application to Snapshots and Lattice Agreement.* PODC 2020. DOI
[10.1145/3382734.3405709](https://doi.org/10.1145/3382734.3405709). Formalized version: the full
version *Store-Collect in the Presence of Continuous Churn with Application to Snapshots and
Lattice Agreement*, arXiv [2003.07787](https://arxiv.org/abs/2003.07787) v3; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ Intent lost.** The churn-tolerant store-collect algorithm CCC (Algorithms 1–3)
is **not regular** as written: a collect returns its node's current local view, which may contain a
value it never wrote back, and a later collect can miss that value — already in a 5-node system
without churn or crashes, with parameters satisfying all of the paper's constraints — and no repair is proved. So
Theorem 6, Corollary 7, Lemma 10 and Observation 5 are false. The other main contribution stands: the atomic
snapshot built on any regular store-collect object (Algorithm 7) is linearizable (Theorem 8, with
the paper's proof idea), and the churn arithmetic (Lemmas 1–3, Corollary 1) is correct up to a
sign slip in Constraint (A).

## Mistakes in the paper

### ❌ Theorem 6, Corollary 7, Lemma 10, Observation 5 (CCC is a correct store-collect implementation)
A `COLLECT` returns `LView` at Line 47, but during its store-back phase the node's own server thread
(Line 48) may have merged a concurrent `STORE` into `LView`; that value was never written back, so a
later `COLLECT` can miss it: with 5 nodes, no churn and no crash, `COLLECT_{p₁}` returns `{⟨r, 1⟩}`
and the subsequent `COLLECT_{p₂}` returns `∅`, violating regularity part (2) (`theorem6_false`).

**Impact.** The paper's main algorithm does not implement a store-collect object, so every
application built on CCC (Section 6 under churn) inherits a broken base object. The snapshot and
lattice-agreement constructions themselves are fine on top of any correct store-collect object.

**Details.** Parameters `α = Δ = 1/100`, `γ = 3/4`, `β = 3/5` (threshold 3), `N_min = 2`, `D = 20`,
satisfying Constraints A–D; nodes `r, p₁, p₂, a, b`, all in `S₀`, always active.
- t = 1: `p₁` starts `COLLECT`; replies from `p₁, a, b` (empty views); store-back of `∅` at t = 3.
- t = 4: `r` invokes `STORE(1)`; its store message reaches `p₁` at t = 6, which merges `r ↦ 1`
  into `LView` (Line 48).
- t = 7: three store-acks arrive; `p₁` returns `LView = {r ↦ 1}`.
- t = 8–12: `p₂` runs `COLLECT` with quorum `p₂, a, b`, none of which has heard of `r`'s value yet,
  and returns `∅`.
- Every message carrying `r ↦ 1` reaches `p₂, a, b` at t = 24 (delay ≤ D). Afterwards all messages
  are delivered, FIFO per sender; the execution is complete and admissible (`ex_admissible`).

The counterexample works for the code with the slips of Algorithms 1–2 repaired (see Slips). With the literal
stray-message handling (but `S₀` nodes joined) it reaches the same violation, because no stray reply or ack reaches
`p₁` or `p₂` before `t = 12`.

The proof fails where it identifies `view(s)`, defined (p. 10) as `LView` at the *end* of the store
phase, with the view carried by the phase's store message (Observation 5, Lemma 10 Case II: "Qc
contains a node whose LView is ⪰ view(s)").

Lemma 10 (a store phase that ends before a collect phase starts is seen by it), the key lemma of Theorem 6, is false
in the same execution: the store-back phase of `COLLECT_{p₁}` ends at t = 7, the collect phase of `COLLECT_{p₂}`
starts at t = 8, but `view(s) = {r ↦ 1} ⋠ view(c) = ∅` (`lemma10_false`).

Observation 5 (a node active `D` after a store phase starts knows its view) is false too: for the store-back phase
`s` of `COLLECT_{p₁}` (starting at t = 3), node `a` is active throughout and at t = 3 + D = 23 its `LView` is still
`∅ ⋡ view(s)` (`observation5_false`). `view(s)` includes `r ↦ 1`, which `p₁` received after broadcasting its store
message; nothing obliges it to reach `a` within `D` of the start of `s`. Lemmas 7 and 8 and Case I of Lemma 10 rely
on it with the same `view(s)`.

**Repair.** None proved (see **Not formalized.** below). It is not a typo: the prose ("returning LView"), the
pseudocode and the definition of `view(φ)` agree with each other, Theorem 6(2)'s proof uses `view(s) = V₁`, and the
journal version (Information and Computation 285, 2022) keeps the same code (its Line 51) and definition.

### ✏️ Slips
- Constraint (A): as printed, `N_min ≥ 1/(Z + γ − (1+α)³)` is vacuous when the denominator is `≤ 0`, which
  Constraints (B)–(D) allow (`literal_constraints_not_imply_ZNmin`: `α = 0.04`, `Δ = 0.01`, `γ = 0.1`, `β = 0.8`,
  `N_min = 1`). Lemma 5 needs `N_min·(Z + γ − (1+α)³) ≥ 1`, which we use (`ConstraintA'`). Corollary 1 does not even
  need (A) (`corollary1_of_Z_pos`).
- Algorithm 1: `is_joined` is initialized to `false` also for the initial members `S₀`, so in a system consisting of
  `S₀` no node ever answers a collect or a join. The proofs treat `S₀` nodes as joined; repaired in our model
  (`CCC.lean`).
- Algorithm 2: the client's single `counter` is incremented by late collect-replies during the store-back and by
  store-acks after the return (which would "return" again). The proofs treat phases as separate; repaired in our model
  (`CCC.lean`).
- Proof of Lemma 11, Case 1: "`⟨r, w⟩ ∈ W₂`" should be `W₁`.

### Typos
- Section 5: the example `α = 0, Δ = 0.21, γ = β = 0.79` is outside the model (`α > 0`), though the constraints hold
  at `α = 0` (`example_alpha_zero`); for every `α > 0` these `γ, β` violate (B) and (C) (`not_constraintB_021_079`,
  `not_constraintC_021_079`), `γ = β = 0.78` works at `α = 1/1000` (`example_alpha_small`).
- Lemma 10, Case I: "enter-echo" should be "collect-reply".
- Proof of Lemma 13: "both stores of `uop_p`" is imprecise.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- *Store-collect specification* (Section 2): schedules of `STORE`/`COLLECT` invocations and
  responses; `Regular` is the paper's regularity, with "no other store occurs between" read as the
  usual regular-register condition (weaker reading; Theorem 8 holds under it).
- *CCC counterexample*: asynchronous message passing, reliable FIFO broadcast, message delays in
  `(0, D]`, crash and churn assumptions of Section 3 (here: no churn, no crash, `N = 5`), integer
  times; a complete finite execution (every message delivered to every node, nothing happens
  afterwards) checked by `decide` in the kernel. Algorithm 1 never fires in a static run.
- *Churn arithmetic*: nodes with entry, leave and crash times, `N(t)` the number of present nodes,
  the Churn, Minimum System Size and Failure Fraction assumptions as in Section 3, plus local
  finiteness (finitely many nodes have entered by any time).
- *Algorithm 7*: nodes of an arbitrary (possibly infinite) type run the code of Algorithm 7 as
  deterministic automata on top of an **abstract** store-collect object: the adversary chooses the
  interleaving and the views returned by collects, subject only to `Regular` of the whole schedule.
  Any choice rule at Line 77. Line 71's `STORE_p(⟨−, −, ssqno, −, −⟩)` "with all the other components
  unchanged" is read as keeping the components of the value `p` stored last. Reading `−` as the
  current local variables would store the new `scounts` of Line 79 with the old `sview`, and a scan
  could then borrow a view older than its own start; that reading is not linearizable (scenario in
  `differencies.md`, not in Lean). Linearizability is CSLib's `IsLinearization` for finite executions
  (hence every prefix), w.r.t. the atomic snapshot specification over the nodes.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 6, Corollary 7 (false) | `theorem6_false` | `CCCCounterexample.lean` |
| Lemma 10 (false) | `lemma10_false` | `CCCCounterexample.lean` |
| Observation 5 (false) | `observation5_false` | `CCCCounterexample.lean` |
| Constraints A–D, example values | `AllConstraints`, `example_alpha_004`, `example_alpha_zero`, `literal_constraints_not_imply_ZNmin` | `Constraints.lean` |
| Lemma 1 (a), (b) | `lemma1_a`, `lemma1_b` | `Churn.lean` |
| Lemma 2 | `lemma2` | `Churn.lean` |
| Lemma 3 | `lemma3` | `Churn.lean` |
| Corollary 1 | `corollary1` | `Churn.lean` |
| constraints imply `α < 0.206` | `alpha_lt_0206_of_CD` | `Constraints.lean` |
| Lemma 10, arithmetic of Case II | `lemma10_core` | `Constraints.lean` |
| Theorem 8 (linearizability) | `theorem8_linearizable` | `Snapshot.lean` |
| Theorem 8 (rounds: ≤ n + 2 collects per scan loop) | `theorem8_collects` | `SnapshotRounds.lean` |
| Lemma 11 | `vec_total` | `SnapshotOrder.lean` |
| Lemma 12 | `borrow_cert` | `SnapshotStep.lean` |
| Lemma 13 | `kU_le_vec_of_precedes_upd` | `SnapshotOrder.lean` |

**Proof remarks.** The round bound of Theorem 8 is proved in the paper's form: after its Line-71
store, a scan performs at most `n + 2` collects, `n` = nodes with an `UPDATE` pending when that
store completes. The paper counts the nodes present when the operation *starts*; under churn the
two differ by a constant factor `(1+α)²`. Every completed scan gets a *certificate*: a successful double collect inside it.
For a borrowed scan the certificate is inherited from the stored `sview`; Lemma 12
(`borrow_cert`) shows it lies inside the borrowing scan, because the borrowed `scounts` contains the
scanner's own Line-71 `ssqno`. All scans are then ordered by the update-sequence vectors of their
certificates, a chain by Lemma 11. Ties are broken by completion, and updates are placed before
the first scan that sees them. So the paper's borrowing chains are never needed explicitly. Lemma 2
assumes `α < 0.206`; the proof needs only `α ≤ 1 − 1/√2 ≈ 0.293` (`lemma2_of_sq`). The
churn assumption is stated only for `t > 0`, but Lemmas 1–2 use `t = 0`; this case follows from
local finiteness (`churn_zero`).

**Not formalized.** Lemmas 4–9 and Theorems 3–4 (join and phase termination under churn); Lemmas 7 and 8 rely on
Observation 5 and were not refuted separately. A repaired CCC: the natural repair (Line 47 returns the view broadcast
at Line 36, and `view(φ)` is the view broadcast in `φ`) has had an informal check only and would require re-checking
Lemmas 4–10 under churn. Theorem 8's round bound in the paper's form (the `(1+α)²` relation under churn, and nodes
that left with an `UPDATE` pending). The other reading of Line 71's `−` components: its non-linearizability rests on
a scenario not in Lean. Section 6.1 (max register, abort flag, set) and Section 6.3 (generalized lattice agreement
from the snapshot).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: the counterexample parameters satisfy all constraints (`params_ok`); the
churn assumptions are satisfiable (`static2_assumptions`). Linearizability uses CSLib's
`Cslib.Computability.Distributed.SharedMemory.History` (`IsLinearization`).
