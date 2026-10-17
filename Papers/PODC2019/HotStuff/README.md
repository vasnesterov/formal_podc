# HotStuff — PODC 2019

Maofan Yin, Dahlia Malkhi, Michael K. Reiter, Guy Golan Gueta, Ittai Abraham. *HotStuff: BFT
Consensus with Linearity and Responsiveness.* PODC 2019. DOI
[10.1145/3293611.3331591](https://doi.org/10.1145/3293611.3331591). Formalized version: arXiv
[1803.05069](https://arxiv.org/abs/1803.05069) **v6** (23 Jul 2019, the full version of the PODC paper,
titled "HotStuff: BFT Consensus in the Lens of Blockchain"); numbering follows it. The replica code of
Algorithm 3 is the same in v4 (Apr 2019), v5 (Jun 2019) and v6.

**Verdict: ❌ False claim.** Theorem 5 (safety of Chained HotStuff) is false for Algorithm 3 as
written: with round-robin leaders, one Byzantine replica and a synchronous execution, a correct
replica commits two conflicting nodes; adding the check `b*.height = curView` restores it. Basic
HotStuff (Algorithm 2) is safe and live as claimed (Theorems 2 and 4, proved for a partially
synchronous implementation), although the proof of Theorem 2 has a gap.

## Mistakes in the paper

* **Theorem 5 is false for Algorithm 3 (Chained HotStuff) as written; the standard setting
  suffices.** Take `n = 4`, `f = 1`, round-robin leaders `leader(v) = v mod 4` and Byzantine
  replica `2`, which leads only views 2, 6 and 10. The execution is synchronous: all correct
  replicas process every proposal. Correct leaders build their proposals with `createLeaf`, so
  height equals view.
  - View 1: leader 1 proposes `y` on genesis.
  - View 2: the Byzantine leader proposes `w`, which conflicts with `y`. In views 3–5 the correct
    leaders extend `w` to `w ← w' ← w'' ← w*`, and all correct replicas commit `w`.
  - View 6: the Byzantine leader sends `x`, a direct child of `y` with justify `QC(y)`. This is the
    only proposal whose height differs from its view. Every correct replica rejects it, but Lines
    17–20 still run. Since `y.parent = genesis = y.justify.node`, they reset every lock to the
    genesis QC and every `genericQC` to `QC(y)`.
  - Views 7–10: the correct leader of view 7 extends its `genericQC = QC(y)`, and the chain
    `u ← u₁ ← u₂ ← u₃` commits `u`, which conflicts with `w`.

  Replica `0` commits both. (`HotStuff.Chained.theorem5_false_roundRobin`; the theorem also checks
  that every correct leader's proposal has height equal to its view.) Two simpler variants, with a
  Byzantine leader in every view, isolate the two causes. Both exploit that replicas never check
  `b*.height = curView`; a monotone lock stops the first but not the second.
  1. *Lock downgrade.* Line 20 sets `lockedQC ← b''.justify` unconditionally. Lines 17–22 run whether
     or not `safeNode` accepted `b*`. So a Byzantine leader can reset a correct replica's lock to an
     old QC with a proposal the replica does not even vote for. Counterexample: `n = 4`, `f = 1`,
     replica `3` Byzantine and leading every view. Replicas `0, 1` vote for `y` on genesis (view 1).
     Then they vote for the conflicting `w` and its chain `w ← w' ← w'' ← w*` (views 2–5), which
     commits `w`. In view 6 the leader sends `x` with parent `y` and justify `QC(y)`. The replicas
     reject it, but `y.parent = genesis = y.justify.node`, so their lock becomes the genesis QC. Then
     they vote for `u ← u' ← u''` extending `y` (views 7–9), which commits `y`. Replica `0` alone has
     committed both `w` and `y`. (`HotStuff.Chained.theorem5_false`)
  2. *Views vs. heights.* The proof needs "view numbers = node heights" ("createLeaf … so
     view-numbers are equated with node heights"). Only a correct leader ensures this; replicas never
     check it. Even with a monotone lock update, as in Algorithm 4, safety fails. A QC on a node `c`
     conflicting with `w` is formed in view 3, between the QC on `w` (view 1) and its children
     (views 5, 6). Replica `2` commits `w` in view 7. Replicas `0, 1`, locked on `(1, w)`, accept a
     child of `c` in view 8 by the liveness rule (`3 > 1`) and commit `c` in view 10.
     (`HotStuff.Chained.monoLock_unsafe`) In this execution every proposal passes `safeNode`. So
     reading Lines 17–22 as nested under `if safeNode` does not save Algorithm 3 either.

  *Fix.* Add the guard `b*.height = curView` (and check that `b*.justify` is valid and refers to a
  strict ancestor, which the paper says it "assumes"). With these checks Theorem 5 holds for every
  `n > 3f` (`HotStuff.Chained.theorem5_fixed`); the lock then becomes monotone by itself. The paper's
  proof also has an unjustified step ("by minimality of `qc_s`,
  `m.node.justify.viewNumber ≤ v_{w''}`"; the justification can also be higher but extend `w`).
  Severity: false statement for the pseudocode; the intended protocol is safe.
* **Proof gap in Theorem 2 (Basic HotStuff); the statement is true.** The proof takes the lowest
  view `v_s ∈ (v₁, v₂]` with a `prepareQC` *conflicting* with the committed `w`. View-minimality over
  conflicting QCs does not exclude two things:
  - the lock of `r` moving, in a view in `(v₁, v_s)`, to a QC on a strict ancestor of `w`, which a
    conflicting proposal may extend;
  - `m.justify` being a QC on a common ancestor with a view in `(v₁, v_s)`, or a QC with a view above
    `v_s`. Replicas never check `m.justify.viewNumber < curView`, and before GST views differ.

  So "the disjunct at Line 26/27 is false" is not established. We prove Theorem 2 differently. A QC
  with view `> v₁` whose node does *not extend* `w` is called bad. Take the **first moment** at which
  a bad QC becomes valid: before it, every correct replica that voted `commit` for `w` is locked on a
  node extending `w` and votes only for nodes extending `w`. So at most `f` correct replicas can still
  contribute to the commit QC on `w` once a bad QC exists. This is formalized as a state invariant.
  (`HotStuff.Basic.theorem_2`, `commitQC_safety`, invariant `SInv`)
* **The pacemaker argument of §4.4 does not hold as stated.** "Since the interval is doubled at
  each time, the waiting intervals of all correct replicas will eventually have at least `T_f`
  overlap". Suppose a Byzantine leader sends `decide` only to replica `A` at time `α`. Then `A`
  enters view 2 with interval `α`, while `B` times out at the same moment with interval `2α`. From
  then on the two replicas share every view for exactly `α` time units, forever. With `α < T_f` and
  `n = 4` (one silent Byzantine), no later view decides. This is the view-synchronization gap;
  Algorithm 5 later just *assumes* "synchronized leadership after GST". Severity: informal claim,
  unsupported; Theorem 4 itself is conditional and correct. (`HotStuff.Pacemaker.overlap_constant`,
  timer arithmetic only)
* **Imprecisions in Lemma 3 / Theorem 4 (statements true).**
  - Lemma 3's proof cites the prepare votes (Line 10). What it needs are the pre-commit voters, who
    stored the `prepareQC` (Lines 16–18).
  - Theorem 4's proof says Line 27 (liveness rule) makes every correct replica vote. When `highQC`
    has the *same* view as the replica's lock, Line 27 fails (strict inequality). Line 26 applies
    instead, because two valid QCs of one view are on the same node.
  - The "highest lock among all replicas" must be among *correct* replicas.
  - Messages for a future view must be buffered, which the "wait for" pseudocode leaves implicit.
  (`HotStuff.Basic.lemma_3`, `safeNode_of_correct_leader`, `theorem_4`)
* Minor: Algorithm 2 Line 32 ("wait for message m from leader") duplicates Line 33. Lemma 1 holds
  more generally: two valid QCs of the same view are on the same node, whatever their types
  (`Inv.node_eq`). Theorem 5 leaves `n > 3f`, `|F| ≤ f` implicit.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Abstract asynchronous system** (`Basic/Defs.lean`, `Chained/Model.lean`), used for all safety
  proofs.
  - Correct replicas take their protocol steps in any order and at any time. The pacemaker is
    arbitrary: a replica may jump to any higher view.
  - Leaders may be Byzantine, so a replica may receive *any* proposal. Safety therefore holds for
    every leader schedule and pacemaker.
  - Ideal `(n − f)`-threshold signatures: a QC is the signed tuple, and it is valid iff `n − f`
    replicas signed it. Byzantine replicas sign anything; correct ones sign exactly their votes
    (`signers` = `Cslib.Byzantine.signers`; quorum facts from `Podc/Byzantine/Certificate.lean` and
    `Podc/Foundations/Quorum.lean`).
  - Nodes are branches (lists of commands), with "extends" = suffix. In the chained model, nodes
    carry parent and justify.
  - Results hold for every `n > 3f` with quorums `n − f`; the paper's case is `n = 3f + 1`.
* **Partially synchronous implementation of Algorithm 2** (`Basic/Impl.lean`) in CSLib's PSync
  model (`Cslib.Byzantine.PartialSync`).
  - Discrete time; correct replicas step every time unit, with drift-free clocks. At most `f`
    Byzantine replicas send arbitrary messages subject to unforgeability (`Run.AuthValid`).
  - Messages between correct replicas sent at `τ` are delivered by `max τ GST + δ`.
  - Replicas buffer all received messages and run the leader and replica handlers of Algorithm 2.
    A QC carries its signer set (the partial-signature tokens).
  - The pacemaker (`nextView` interrupts) and the client commands are per-replica *inputs*; views
    increase by one.
  - The implementation refines the abstract system (`abs_reach`). Safety thus holds in every run,
    for any GST, delays and pacemaker.
  - Caveat (CSLib PSync): drift-free, always-awake replicas make this positive result weaker than in
    the textbook DLS model.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (strengthened: same view ⇒ same node) | `HotStuff.Basic.lemma_1`, `Inv.node_eq` | `Basic/Invariants.lean` |
| Theorem 2 (abstract system) | `HotStuff.Basic.theorem_2`, `commitQC_safety` | `Basic/Safety.lean` |
| Theorem 2 (PSync implementation) | `HotStuff.Basic.impl_theorem_2` | `Basic/Main.lean` |
| Lemma 3 | `HotStuff.Basic.lemma_3` | `Basic/Main.lean` |
| Theorem 4, `T_f = 8(δ+1)` | `HotStuff.Basic.theorem_4` | `Basic/Liveness.lean` |
| Correct leader's proposal passes `safeNode` | `safeNode_of_correct_leader` | `Basic/LiveCore.lean` |
| Theorem 5 for Algorithm 3: **false** (round-robin, synchronous) | `HotStuff.Chained.theorem5_false_roundRobin` | `Chained/Counterexample.lean` |
| … with a Byzantine leader in every view | `HotStuff.Chained.theorem5_false` | `Chained/Counterexample.lean` |
| … also with a monotone lock: **false** | `HotStuff.Chained.monoLock_unsafe` | `Chained/Counterexample.lean` |
| Theorem 5 with the height check | `HotStuff.Chained.theorem5_fixed` | `Chained/Safety.lean` |
| §4.4 pacemaker remark: constant overlap | `HotStuff.Pacemaker.overlap_constant` | `Basic/Pacemaker.lean` |

`theorem_4` says the following. Let `R` be a valid, unforgeable run with `3f < n`, and `t₀ ≥ GST`.
Suppose all correct replicas are in view `v` at `t₀`, `leader v` is correct, and no correct replica
is interrupted during `[t₀, t₀ + 8(δ+1))`. Then every correct replica has committed the leader's
proposal `cmd :: highQC.node` by `t₀ + 8(δ+1)`.

**Not formalized.**
- Event-driven HotStuff (Algorithms 4–6, Appendix B, Theorem 8) and the two-phase variant with its
  livelessness scenario.
- Authenticator complexity (`O(n)` per view); Section 7.
- Chained liveness ("omitted for brevity" in the paper).
- An actual pacemaker: Theorem 4 is conditional, as in the paper.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity checks:
- `HotStuff.Basic.nonvacuous` applies Theorem 4 to a concrete run (`n = 4`, a silent Byzantine
  replica, `δ = 1`). The hypotheses are satisfiable, and every correct replica commits `cmd 1`.
- `HotStuff.Chained.heightCheck_nonvacuous`: the repaired chained protocol commits.
- The Chained counterexamples are checked by kernel `decide` on explicit executions; the abstract
  model is executed action by action.
- `hotstuff_unforging` shows the implementation satisfies CSLib's `Algorithm.Unforging`.
