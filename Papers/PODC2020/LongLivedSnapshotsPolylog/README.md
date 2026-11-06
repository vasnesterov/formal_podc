# Long-Lived Snapshots with Polylogarithmic Amortized Step Complexity — PODC 2020

Mirza Ahad Baig, Danny Hendler, Alessia Milani, Corentin Travers. *Long-Lived Snapshots with
Polylogarithmic Amortized Step Complexity.* PODC 2020. DOI
[10.1145/3382734.3406005](https://doi.org/10.1145/3382734.3406005). Formalized version: the full
version, HAL preprint hal-02860087v1 (June 2020, 19 pp., all proofs); numbering follows it. Copy of
the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** Lemma 3.3 (the linearization given by rules 1–3 respects the max-array semantics) and Lemma 3.4
(counting the `MaxUpdate`s that start during a scan) are false, so the linearizability proof of the new max array
collapses. Algorithm 1 (the unbounded 2-component max array) is still linearizable, by a new proof with certified views;
in bounded-increment executions it is wait-free, given a helping period `≥ 1`, which the pseudo-code's `⌊n/log² m⌋` is not
for realistic `n`; and Algorithm 2, the unlimited-use snapshot, is linearizable and wait-free, with bounded increments
(Lemmas 4.1, 4.2). The polylogarithmic amortized bounds, the paper's main claim, were checked only in their counting
cores, which hold; the black-box costs and the final summation were not checked.

## Mistakes in the paper

### 🛠️ Lemma 3.3 (linearization rules 1–3, with Definition 3.2 and Claim 4)
The order of rules 1–3 can put a `MaxUpdate(right, 3)` before a `MaxScan` that returns right component
`0`, in a `4`-bounded-increment execution with `n = 4` processes and `m = 16 = n²`
(`Counterexample.lemma_3_3_false`).

**Impact.** The linearizability proof of Theorem 3.7 rests on Lemma 3.3 and Claim 4 and is broken: Lemma 3.3 is false, and
so are Claim 4 and the "value of `O`" of Definition 3.2. Theorem 3.7's linearizability still holds; we prove it
differently (`alg1_linearizable`). It holds in every execution with atomic `MR` registers, with no bounded-increment
hypothesis and for every `m`. The history in the counterexample is itself linearizable.

**Details.** Process `A` writes `MR_left = 4, 8, 12`. Then:
1. `Q` scans and reads `r₁ = 0`, `l = 12`.
2. `A` writes `MR_left = 16`.
3. `S` scans and reads `0, 16, 0`, so its index is `h = 1`.
4. `B` writes `MR_right = 3`.
5. `Q` reads `r₂ = 3`. Its index is `h = 0`, and it writes `MA_0 = (12, 3)`. Rule 3 linearizes `B`'s update at `Q`'s write of `MA_0.right`.
6. `S` writes `MA_1 = (0, 0)` and scans it at a later step. Line 18 passes, and `S` returns `(16, 0)`.

Rule 1 linearizes `S` at that scan, after `B`'s update. Definition 3.2 makes the "active" array jump
from `MA_0` to `MA_1`. The right component of `O`'s value then drops from `3` to `0`, which Claim 4
excludes.

**Repair.** A certified view (`Cert`) records the time `t₀` of its line-11 read and the time `t₁` of
its line-17 scan of `MA_h`. On `[t₀, t₁]` the high-order bits are constant, and
`MR(t₀) ≤ view ≤ MR(t₁)`. Its components are actual values of the max registers before `t₁`. Views
are monotone in `t₁` (`cert_le`). Every completed operation has a certificate inside its interval: a
direct view, or by Claim 1 a helper's view. The max-array criterion of the PODC 2012 formalization then
gives a linearization (`exists_isLinearization_maxArr`). The invariant is `Inv` in `LinInv.lean`.

### 🔧 Lemma 3.4 (`MaxUpdate`s that start during a `CompScan`)
After `K = 3` unsuccessful iterations of a `CompScan`, only `3` `MaxUpdate`s have been invoked during it,
not `⌈(K−2)m/b⌉ = 4`, with `n = 4`, `m = 16`, `b = 4` (`Counterexample34.lemma_3_4_false`).

**Impact.** Lemma 3.5 (wait-freedom) still holds. Its proof only needs the number of `WriteMax` steps
during the iterations (`WaitFree.lemma_3_4`, `WaitFree.iterations_le`).

**Details.** The proof counts the `WriteMax` operations that take effect during `S`. It then assumes
that each of them belongs to a `MaxUpdate` that started during `S`. But each of the other processes
may have invoked its `MaxUpdate` before `S` and write during `S`. In the counterexample:
- `A`, `B`, `C` have pending `MaxUpdate(left, 16)`, `MaxUpdate(right, 16)`, `MaxUpdate(left, 20)` when `S` starts;
- `MR_left = MR_right = 15` at that point;
- the three pending writes plus three new `MaxUpdate`s of `C` (`24`, `28`, `32`) make three iterations of `S` fail.

**Repair.** Count `WriteMax` steps inside `I₂`. With `2n+1` of them, some process writes three times
there. Both `CompScan`s between its writes then complete inside `I₂`, which gives Observation 5's
"+2".

### ✏️ Slips
- Algorithm 1, lines 23 and 25 and the text of Section 3 (helping period `⌊n/log² m⌋`): with `m = n²`, the period is `0`
  for every `n < 256`, so line 25 computes `c mod 0`. A floor is printed for a ceiling: the proof of Lemma 3.5 uses
  `⌈n/log² m⌉`. We model the intended version: a period `X ≥ 1`, with further collects at `c = 2X, 3X, …` (`afterFail`,
  `WaitFree.waitFreeOn_BIExec`). With period `0` read as "never collect again", there is no helping.
- Algorithm 1, line 25 also fires at `c = 0`, before `h₀` has been collected. The text says line 25 is "not the first
  collect", which is what we model.
- Lemma 4.1: the induction takes `x` of height `h+1` but uses the bound `2^{h−1}`; this is an index
  slip (`Section4.lemma_4_1`).
- Lemma 4.1, Claim 5: `(L_u, R_u)` is undefined when no `MaxUpdate` of `I` touches `u.MA`; take `(0, 0)`.

## Proof gaps (statements true)

### 🔧 Lemma 3.5 (wait-freedom of Algorithm 1)
The interval `I₁` in the proof is one iteration short, because the first collect happens in iteration `X + 1`; the proof
also uses the false Lemma 3.4.

**Impact.** The statement stands for a period `X ≥ 1`, with the paper's bound `K + 2X` iterations
(`WaitFree.iterations_le`, `WaitFree.steps_le`, `WaitFree.waitFreeOn_BIExec`). Here
`⌈(K−2)m/ℓ⌉ ≥ 2n+1`, i.e. `2nℓ < (K−2)m`.

**Repair.** The off-by-one in `I₁` is absorbed because `I₃` needs only `X − 1` iterations.

### 🔧 Section 3 (the bounded max arrays `MA_j` of [4])
Algorithm 1 uses the `(m × m)`-bounded max arrays of Aspnes, Attiya, Censor-Hillel and Ellen [4]
(the 2015 journal version) as linearizable black boxes, but as published that max array is not
linearizable (its Theorem 3.4 is false, see
[LimitedUseSnapshots](../../PODC2012/LimitedUseSnapshots/README.md)).

**Impact.** The statement stands with the authors' corrected max array (its erratum), which is linearizable.
That correction makes `MaxUpdate₁` cost `O(log² m)`, which eq. (4) already charges per iteration.

### 🔧 Theorem 4.4 (Algorithm 2 is a linearizable snapshot)
The proof only says that the proof of Section 4.1 of [4] "holds also", but that proof's linearization
points are wrong, as found in the PODC 2012 formalization.

**Impact.** The statement stands with the corrected linearization points of
`Snapshot.theorem_4_2` (`Section4.theorem_4_4_linearizable`). No bound on the number of `Update`s is
needed (unlimited use).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory, CSLib `Cslib.SharedMemory.Impl`. Processes are deterministic, `n`
  processes are `Fin n`, and the scheduler is arbitrary. A crash is a process that stops taking steps.
  There is no randomization. Linearizability is CSLib's amended Herlihy–Wing definition.
- Algorithm 1 is `alg1 n m X`. Its base objects are atomic, as the paper uses them as linearizable
  black boxes:
  - `MR_left`, `MR_right`: unbounded max registers;
  - `MA_j`, `j ∈ ℕ`: 2-component max arrays;
  - `H[i]`: registers.

  `X` is the helping period. Every program counter does one access. `Collect` reads `H[0..n−1]` one
  by one. Line 27 picks the least eligible `j`.
- Definition 2.1 (`BoundedIncr`) is stated on the sequence of written values, since writes are atomic
  steps. We show it is equivalent to "each write exceeds the previous maximum by at most `ℓ`"
  (`boundedIncr_iff_stepBounded`). `BIExec` imposes it on `MR_left` and `MR_right`.
- Algorithm 2 is `Snapshot.alg3 T v₀` of the PODC 2012 formalization, for any tree `T` whose leaves
  are the processes. Its max arrays and root max register are atomic and unbounded.
- CSLib has no composition theorem. "Algorithm 2 over Algorithm 1 over [12] and [4]" therefore follows
  only informally, by locality of linearizability. Lemma 4.1 then provides the bounded-increment
  hypothesis that Algorithm 1 and [12] need.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Algorithm 1 | `alg1 n m X` | `Algorithm.lean` |
| Definition 2.1 | `BoundedIncr`, `BIExec`, `boundedIncr_iff_stepBounded` | `BoundedIncrement.lean` |
| Lemma 3.3 is false | `Counterexample.lemma_3_3_false` (rules: `Rule1Point`, `Rule3Point`) | `Counterexample.lean` |
| Theorem 3.7, linearizability (Lemmas 3.1, 3.3 repaired) | `alg1_linearizable`, `cert_le` | `LinMain.lean` |
| Claims 1–3 (as invariants) | `Inv`, `HInv`, `MAInv`, `PFL`, `inv_run` | `LinDefs.lean`, `LinInv.lean` |
| Lemma 3.4 is false | `Counterexample34.lemma_3_4_false` | `Lemma34Counterexample.lean` |
| Lemma 3.4, corrected (`WriteMax` steps) | `WaitFree.lemma_3_4` | `WaitFree.lean` |
| Lemma 3.5 / Theorem 3.7, wait-freedom | `WaitFree.iterations_le`, `WaitFree.steps_le`, `WaitFree.waitFreeOn_BIExec` | `WaitFree.lean` |
| Lemma 3.6, counting core (Obs. 6, eqs. (6)–(7)) | `Amortized.fails_le`, `Amortized.lemma_3_6_unsuccessful`, `Amortized.lemma_3_6_unsuccessful_of_le` | `Amortized.lean` |
| Lemma 4.1 | `Section4.lemma_4_1`, `Section4.lemma_4_1_access` | `Section4.lean` |
| Lemma 4.2 | `Section4.lemma_4_2` | `Section4.lean` |
| Theorem 4.4 | `Section4.theorem_4_4_linearizable`, `theorem_4_4_update_cost`, `theorem_4_4_scan_cost` | `Section4Main.lean` |

**Not formalized.**
- The implementations of the black boxes ([12]'s unbounded max register and [4]'s bounded max array)
  and their amortized costs.
- Hence Lemma 3.6 and Lemma 4.3 are formalized only as their counting cores:
  - at most `|W|` unsuccessful iterations when `nℓ ≤ m`;
  - the per-operation weighted access bounds of Algorithm 2.
- The starvation of the literal algorithm with period `0`: a scanner can starve, because a fast updater crosses a multiple
  of `m` during each of its iterations. We only sketch this.
- The effect of the useless collect at `c = 0` on the amortized bound, under the literal reading of line 25: not analysed.
- Whether Algorithm 1 is also correct over the uncorrected max array of [4]: not checked.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

The concrete executions are checked by `decide +kernel`. `lemma_3_3_false` holds for every `X` and is
checked by a small tactic, `kernel_decide_fvar`: it calls `of_decide_eq_true rfl` and leaves the
evaluation to the kernel.

Non-vacuity: both counterexample executions are valid `4`-bounded-increment executions of the same
`alg1`, so `BIExec` is satisfiable.

The model of Algorithm 2 and the max-array criterion come from `Papers/PODC2012/LimitedUseSnapshots`.
CSLib candidates (marked in the files):
- `boundedIncr_iff_stepBounded`, `wlogFrom`/`writesTo` and `writesTo_stepBounded` (generic write logs
  and Definition 2.1);
- the time-indexed `cfgAt`/monotonicity pattern of `LinBasic.lean`.
