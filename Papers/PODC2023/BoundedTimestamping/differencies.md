# Differences between the formalization and the paper

Paper: B. Bashari, A. Jamadi, P. Woelfel, *Efficient Bounded Timestamping from Standard
Synchronization Primitives*, PODC 2023 (DOI 10.1145/3583668.3594601). We used the 45-page full
version with appendices (University of Calgary report). No arXiv version exists. A journal version
(Distributed Computing 38(3), 2025) exists; we did not check whether it changes the algorithm.
Numbering follows the full version.

## Errors in the paper

1. **Lemma 6 is false, and hence Lemma 9, Lemma 8 and Corollary 10 are false for the algorithm
   of Figures 1–2. Theorem 1 is therefore not established.** *False statement.*
   - Line 23 runs `helpMoveTS()` as a coroutine, `κ` steps per `helpActiveCluster()` call. Between
     two such slices, the same process runs other code: `isEarlier` lines 35/37/44/45/50,
     `helpUpdateTS` line 9, `conditionalReset` line 29. That code executes `LL()` on the same
     `TS` entries.
   - LL/SC as defined in Section 3 has one link per process and object. So these `LL()`s renew
     the links that the coroutine's `VL()`s (lines 65, 66) and `SC()` (line 73) refer to.
   - The proof of Lemma 6 (through Lemmas 46 and 51) infers from a successful `VL()` in line 65
     that `localTS[q]` (read in line 61) is still current. That inference fails.
   - Lemmas 46 and 51 still hold in our execution. Lemma 6 itself is false: the `SC()` of line 73
     changes `TS[0]` from `(1, 63)` to `(1, −1)` while `TS[1] = (1, 61)`, which reverses their
     dominance order (`lemma6_false`). Lemma 9 then fails too: the order of `TS[0]` and `TS[1]` no
     longer matches the latest `updateTS()` calls.
   - Counterexample (`alg_not_linearizable`, `n = 3`, `κ = 4`): a *sequential* execution of 438
     operations and 6392 steps.
     - Process `0` updates 371 times and process `1` 62 times, reaching the cluster-1 move phase.
     - Process `2` calls `isEarlier(0,1)`. Its coroutine reads `TS[0] = (0, 370)` in line 61.
     - Process `0` updates twice: `TS[0] = (1, 63)`, and the flag is back to its old value.
     - Process `2`'s `isEarlier(0,2)` renews its link on `TS[0]` in line 35. Its coroutine then
       writes `(1, −1)` to `TS[0]` in line 73.
     - `isEarlier(1,0)` returns `false`. The correct answer is `true`.
   - Python experiments found analogous executions for `n = 4, 5, 6` with `κ = 3`, for `n = 3`
     with `κ ∈ {4, 5, 6, 8}`, and for other readings of lines 70–72.
   - Suggested repair (not proved): give `helpMoveTS` its own LL/SC context, e.g. LL/SC objects
     for `2n` identities. This keeps all asymptotic bounds. In our simulator the repair blocks the
     attack. Random runs found no violation, but they do not find the original bug either.
2. **`isEarlier(x, x)` can return `true`.** *False in a degenerate case.*
   - With `x = y`, the "snapshot" of lines 44–46 (`LL x; LL y; VL x`) only validates the second
     `LL`. The two local copies can be different values of the same entry.
   - The specification always answers `false`. Observation 56 tacitly assumes `x ≠ y`.
   - Counterexample (`alg_not_linearizable_self`): a 3-process execution in which process `1`
     completes an `updateTS()` between process `2`'s lines 44 and 45.
   - Repair: return `false` when `x = y`.
3. **Observation 13, Lemma 14 and Lemma 2 are false.** *False lemmas; gap in the proofs of
   Lemmas 21 and 33.*
   - `helpSystem()` (line 5) can call `isEarlier()` (line 18). That `isEarlier()` runs two
     `helpUpdateTS()` calls before its `helpActiveCluster()` (line 39).
   - So an `updateTS()` can increment `Counter` up to 12 times before its first
     `helpActiveCluster()` call, not 6. Lean shows 7 (`observation13_false`, `n = 4`, `κ = 3`).
   - Lemmas 21 and 33 derive `ζ = 6n + 2` and `μ = 6n³ + 6n² + 2` from Lemma 2, so their proofs
     do not go through as written. Probably larger constants (factor 2) repair them. Not
     checked.
4. **Proof of Lemma 8, Case 2b.** *Proof gap.*
   - "If `t*x1 < t*y1` then `i ≺ j` at point `t*x1`" should read "at `t*y1`".
   - The other case ("`i ≺ j` at `t*y2`") needs `t*x1 < t*y2`, which is not shown.
   - This was not analysed formally.
5. **The informal specification in Section 1 is inconsistent with the rest of the paper.**
   *Under-specified definition.*
   - The verbal definition makes `isEarlier(p, q)` false when `p` updated and `q` never did. It
     also is not a total order.
   - The operator `≪` and the "interpreted value" of Section 5 make it true.
   - We formalize the interpreted value (`mtsObj`).
6. **Section 6.** No errors in the claims.
   - Lemma 63, Corollary 64 and Theorem 11 hold. Theorem 11 holds for every overflow behaviour
     (`ovf` is arbitrary).
   - The hypothesis `B > φ·n` can be weakened to `B ≥ φ·n`, because the counter never exceeds
     `φ·n − 1`. This is tight for `φ ≥ 2` (`exists_reach_max`, `exists_overflow`).
   - Section 3 allows `φ ∈ {0, …, ⌊2^w/n⌋}`. `φ = 0` is meaningless. The top value
     `φ = 2^w/n` (when `n ∣ 2^w`) is not covered by Theorem 11's `B > φn`, but it is covered by
     the sharper bound.
   - Typos: "threshold `T = n(m − 1)`" should be `n(φ − 1)`; "mod 3δ-FNI" should be "FAI".

## Under-specified points and our choices

- **Line 23** ("perform `κ` steps from `helpMoveTS()`"). We read it as a persistent coroutine
  (field `mv` of the local state). A finished call is immediately followed by a new one. This is
  the only reading compatible with constant step complexity and with the proof of Lemma 33.
- **Lines 70–72 with `⊥` indices.** We read "`localTS[j].index` maximal" as "the `≪`-dominant
  entry", which is the paper's wording in Lemmas 6 and 51.
  - `⊥` entries come first, the larger identifier first.
  - "`localTS[i].index` minimal" is the `≪`-minimal entry, and `min(⊥, 0)` is read as `0`.
  - If there are no entries, `newIndex = −1`.
  - The Lean counterexample uses this reading. Python finds violations for other readings too,
    with different schedules.
- **Line 65** evaluates `VL()` only for entries whose local copy is in the old cluster
  (short-circuit `∧`).
- **Process `n − 1` never calls `updateTS()`** (Section 4.1.1). This is `allowedOp`. So the object
  is an MTS for `n − 1` updaters. Theorem 1's "`n`-process MTS" needs `n + 1` processes. This is
  harmless asymptotically.
- **`updateTS()` takes the caller as argument** (`upd p`, only `p` may invoke it), because CSLib
  specifications do not see the caller.
- **LL/SC links**: the object state is the value and the list of processes with a valid link,
  exactly as Section 3 defines LL/SC.

## Model differences (do not weaken the results)

- Corollary 10 level. `Counter` is an atomic `mod 3δ` FAI object and the LL/SC objects are
  atomic. This matches the paper's own analysis.
  - We do not compose with the FAI implementation of Section 6 or with the LL/SC implementation of
    Jayanti–Petrovic.
  - The counterexample therefore refutes the claim that Figures 1–2 implement a linearizable MTS
    from these objects (Corollary 10).
- Every primitive is one atomic step. Responses are separate (non-memory) steps, as in CSLib.
- `read()` of the mod-`φ` FAI object in Section 6 is implemented as `Counter.read() mod φ`. The
  paper does not give it.

## Not formalized

- Linearizability of any repaired algorithm.
- Lemmas 3–9 and 15–62 in general.
- The `O(log n)`-bit bound on stored values: the index range `[−n, δ)` of Section 4.1.
- The space bound `O(n²)` via Jayanti–Petrovic.
- Section 7 (snapshots).
- The consensus-number remark of Section 1.
