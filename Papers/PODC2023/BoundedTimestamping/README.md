# Bounded Timestamping from Standard Primitives — PODC 2023

Benyamin Bashari, Ali Jamadi, Philipp Woelfel. *Efficient Bounded Timestamping from Standard
Synchronization Primitives.* PODC 2023. DOI
[10.1145/3583668.3594601](https://doi.org/10.1145/3583668.3594601). Formalized version: the
45-page full version with appendices (University of Calgary report). There is no arXiv version.
Numbering follows the full version.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The algorithm of Figures 1–2 is **not linearizable**: Lemma 6 is
false, and so are Lemmas 9 and 8 and Corollary 10 and Theorem 1 is not established by it. Lean checks a sequential
execution with 3 processes in which `isEarlier(1, 0)` gives the wrong answer. The cause is
reusable: a `helpMoveTS()` call spread over several operations shares its LL/SC links with the
rest of the process's code. A simple repair (a separate link for `helpMoveTS`) blocks our attack,
but we did not prove it correct. Section 6 (bounded FAI from bounded FAA) is
correct, with a slightly better bound. The constant step complexity (Lemma 12) holds: every
operation takes at most `2κ + 107` base-object steps, independently of `n`.

## Mistakes in the paper

* **The algorithm is not linearizable: Lemma 6 is false, and hence Lemma 9, Lemma 8,
  Corollary 10 and the proof of Theorem 1 fail** (false statement).
  - Line 23 executes `helpMoveTS()` `κ` steps per `helpActiveCluster()` call, so one call is
    spread over several operations of the same process.
  - Those operations perform their own `LL()`s on `TS` entries: `isEarlier` lines 35/37/44/45/50,
    `helpUpdateTS` line 9, `conditionalReset` line 29.
  - With one link per process and object, which is the paper's LL/SC definition in Section 3, such
    an `LL()` renews the link that the coroutine later checks with `VL()` (line 65) and uses for
    `SC()` (line 73).
  - Lemmas 46 and 51 still hold in our execution; only their use in the proof of Lemma 6 breaks.
    Lemma 6 itself fails: an `SC()` of line 73 changes `TS[0]` from `(1, 63)` to `(1, −1)` while
    `TS[1] = (1, 61)`, which reverses their dominance order (`lemma6_false`). Lemma 9 then fails
    as well.

  Counterexample (`n = 3`, `κ = 4`; every operation runs solo):
  1. Process 0 calls `updateTS()` 371 times and process 1 calls it 62 times. Cluster 1 is now in
     its move phase and `TS[2]` has been moved.
  2. Process 2 calls `isEarlier(0,1)`. Its coroutine reads `TS[0] = (0, 370)` (line 61) and pauses.
  3. Process 0 calls `updateTS()` twice. Now `TS[0] = (1, 63)`, and the flag has its old value
     again.
  4. Process 2 calls `isEarlier(0,2)`. Line 35 renews its link on `TS[0]`. Its coroutine's
     `VL()` succeeds, and line 73 writes `(1, −1)` into `TS[0]`.
  5. `isEarlier(1,0)` returns `false`. The specification says `true`.

  The execution has 438 operations and 6392 steps. Python experiments give analogous violations
  for `n = 4, 5, 6` with `κ = 3` (the smallest admissible `κ`) and for other readings of lines
  70–72. (`alg_not_linearizable`)
* **`isEarlier(x, x)` can return `true`** (false in a degenerate case).
  - For `x = y`, lines 44–46 validate only the second `LL()`. If process `x` completes an update
    between lines 44 and 45, the comparison sees two different values of `TS[x]` and returns
    `true`.
  - Observation 56 tacitly assumes `x ≠ y`. Returning `false` for `x = y` fixes it.

  (`alg_not_linearizable_self`)
* **Observation 13, Lemma 14 and Lemma 2 are false** (false lemmas; proof gap in Lemmas 21 and
  33).
  - `helpSystem()` may call `isEarlier()` (line 18), which runs two `helpUpdateTS()` calls before
    its `helpActiveCluster()`.
  - So an `updateTS()` can increment `Counter` up to 12 times before its first
    `helpActiveCluster()` call, not at most 6.
  - The constants `ζ = 6n + 2` and `μ = 6n³ + 6n² + 2` of Lemmas 21 and 33 rely on the bound 6.
    Larger constants probably repair this; we did not check.

  (`observation13_false`: 7 increments in one `updateTS()`, no `helpActiveCluster()` started)
* **Proof of Lemma 8, Case 2b** (proof gap). The text says "`i ≺ j` at point `t*x1`" where `t*y1`
  is meant. The other subcase needs `t*x1 < t*y2`, which is not argued.
* **The informal specification in Section 1 disagrees with the interpreted value of Section 5**
  (under-specified definition). In Section 1, `isEarlier(p, q)` is false when only `p` updated.
  In `≪` and the interpreted value it is true. We formalize the latter.
* **Section 6 is correct.**
  - Lemma 63, Corollary 64 and Theorem 11 hold, for any overflow behaviour.
  - The counter never exceeds `φn − 1`, so `B ≥ φn` suffices instead of `B > φn`. This is tight
    for `φ ≥ 2`.
* **Smaller points.**
  - Lines 70–72 do not say what to do with `⊥` indices.
  - Process `n − 1` may not call `updateTS()`, so "`n`-process MTS" really means `n − 1`
    updaters.
  - Typos: `T = n(m − 1)` should be `n(φ − 1)`; "mod 3δ-FNI" should be "FAI".

Full list of differences (including modelling choices): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory, using CSLib `Cslib.SharedMemory.Impl`.
  - `n` deterministic processes.
  - Each base-object primitive is one atomic step.
  - Wait-freedom is CSLib's `WaitFree`. Linearizability is CSLib's `Linearizable`, which is
    Herlihy–Wing.
* The implemented object is `mtsObj n`. Its state is the order of the processes' latest
  `updateTS()`, followed by the processes that never updated, by identifier. It is the paper's
  "interpreted value".
  - `updateTS()` of `p` is the operation `upd p`, and only `p` may invoke it.
  - Process `n − 1` never updates.
* Base objects (Corollary 10 level), from `Defs.lean`:
  - bits `A[i]`;
  - LL/SC objects `TS[i]` and `LookupTable[i]`, with one link per process as defined in
    Section 3;
  - one atomic `mod 3δ` FAI object `Counter`, with the paper's constants `ζ, η, μ, γ, δ`.
* `alg n κ` (`Alg.lean`) encodes Figures 1–2 line by line.
  - `helpMoveTS` is a persistent coroutine advanced `κ` steps per `helpActiveCluster()`.
  - Lines 70–72 select the `≪`-dominant / `≪`-minimal entries.
* Section 6 is modelled separately (`BoundedFAI.lean`). It uses a bounded FAA object whose
  overflow behaviour is an arbitrary function parameter.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Corollary 10 / Lemma 8 / Theorem 1 are false for Figs. 1–2 (`n = 3`, `κ = 4`) | `alg_not_linearizable` | `Counterexample.lean` |
| Lemma 6 is false (a line-73 `SC()` reverses `TS[0]`, `TS[1]`) | `lemma6_false` | `Counterexample.lean` |
| `isEarlier(x, x)` can be wrong | `alg_not_linearizable_self` | `Counterexample.lean` |
| Observation 13 and Lemma 2 are false | `observation13_false` | `Observation13.lean` |
| Lemma 12: every operation takes at most `stepBound κ = 2κ + 107` steps; wait-freedom | `lemma12`, `alg_waitFree` | `StepComplexity.lean` |
| Lemma 63, sharper form | `FAI.lemma63`, `FAI.lemma63_sharp` | `BoundedFAI.lean` |
| Corollary 64 (no overflow) | `FAI.corollary64` | `BoundedFAI.lean` |
| Theorem 11 (linearizable, wait-free, ≤ 2 steps) | `FAI.theorem11_linearizable`, `FAI.theorem11_linearizable_paper`, `FAI.theorem11_waitFree`, `FAI.theorem11_steps` | `BoundedFAI.lean` |
| `B ≥ φn` is tight | `FAI.exists_reach_max`, `FAI.exists_overflow` | `BoundedFAI.lean` |

Generic tools (CSLib candidates):
* `Sequential.lean`: a sequential execution with an illegal response sequence, or a response no
  state can produce, refutes linearizability.
* `Machine.lean`: a list-based computable copy of `Impl.step`, proved equal (`step_toCfg`). It
  lets `decide +kernel` evaluate the 7268-label counterexample.

**Not formalized.**
* Linearizability of any repaired algorithm (a separate link context for `helpMoveTS`, and
  `isEarlier(x, x) = false`). In simulation the repair blocks our attacks. Random runs of the
  repaired algorithm found no violation, but random runs also miss the original bug, so this is
  weak evidence.
* The `O(log n)` word-size bound (index range `[−n, δ)`).
* The Jayanti–Petrovic LL/SC construction and the resulting `O(n²)` space.
* Composing Section 6 into the algorithm.
* Section 7.

**Trust.** No `sorry`. The listed theorems use only `propext`, `Classical.choice` and
`Quot.sound`. `decide +kernel` adds no axiom. The model comes from CSLib's
`SharedMemory.{Model, History, LinPoints}`. Python confirms the counterexample independently:
our simulator and an offline linearizability checker agree with the Lean evaluation step for step.
