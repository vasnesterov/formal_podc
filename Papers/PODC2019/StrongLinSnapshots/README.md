# Strongly Linearizable Snapshots and ABA-Detecting Registers — PODC 2019

Sean Ovens, Philipp Woelfel. *Strongly Linearizable Implementations of Snapshots and Other Types.* PODC 2019.
DOI [10.1145/3293611.3331632](https://doi.org/10.1145/3293611.3331632). Formalized version: arXiv
[1908.10826](https://arxiv.org/abs/1908.10826) v1 (full version, 51 pp.); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** Theorem 1 holds: Algorithm 2 is a lock-free strongly linearizable
ABA-detecting register from `n + 1` registers of `O(log n + log |D|)` bits. It holds for the natural
specification, but not for the one the paper writes down, which wrongly forces every process's first `DRead`
to report "no write". Observation 4 (Algorithm 1 is not strongly linearizable) holds. Theorem 25 (Algorithm 3,
the snapshot, is strongly linearizable) and its lock-freedom (Theorem 32) are proved with *atomic* `S` and
`R`, not for a merely linearizable `S`. Theorem 3 (simple types) is not formalized.

## Mistakes in the paper

* **The specification of the first `DRead` does not match Algorithms 1 and 2 (mis-stated definition; the intent is evident).**
  Section 3 defines `DRead_q()` to return `a = true` iff "`q` performed an earlier `DRead_q()` and a
  `DWrite` was performed since `q`'s last `DRead_q()`". So a first `DRead` must return `false`. In
  Algorithm 2 a first `DRead` after any `DWrite` reads `A[q] = ⊥ ≠ (p, s)`, sets `changed`, and returns
  `true`. In the sequential execution `DWrite_p(x); DRead_p()` the read returns `(x, true)`, so
  Algorithm 2 is not even linearizable for the literal specification, for every `n ≥ 1`
  (`not_linearizable_literal`); read literally, Theorem 12 is false. The proof misses it because Lemma 8 only compares two consecutive
  `DRead`s and Theorem 10 never treats the first one. The fix is the specification "a `DWrite` since
  `q`'s last `DRead_q()` *or since the beginning*". This is the PODC'15 ABADetection formalization's
  `abaObj`, and Theorem 1 is proved for it. Algorithm 3 is unaffected: it only uses the flag of a `DRead`
  that follows a `DRead` of the same `SLscan`.
* **Observation 6(b) is mistyped (statement true).** It reads "`A[p] = s` throughout `[t, t']`". The
  intended statement, used in Lemma 7, is "`A[q] = (p, s)` throughout `[t, t']`". The paper takes it from
  a thesis without proof; we prove it as an invariant of `GetSeq` (`protBy_getSeq`, `protBy_of_wInv`).
* **Small slips.** Lemma 8 refers to "the loop-guard on line 53" (line 41 is meant). Theorem 12's proof
  cites "Theorem 11" (Lemma 11 is meant). Lemma 11's case (ii) cites Q-2 instead of Q-1. Observation 6(a)
  says "at least `n`" `GetSeq` calls where the queue gives `n + 1`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`): `n` processes `Fin n`,
  deterministic programs, atomic base objects, arbitrary scheduler. Executions are label lists, and a
  response is a separate step after the operation's last access. Strong linearizability is CSLib's
  `Impl.StronglyLinearizable` (a prefix-preserving linearization function). Lock-freedom is
  `Impl.LockFree` (every infinite execution with infinitely many steps has infinitely many responses).
* ABA-detecting register: `abaObj (Fin n) V v₀` (value domain `V` with `⊥ = v₀`; `DRead` carries the
  reader, and only `q` may invoke `dread q`). Algorithm 2 runs on `n + 1` registers over
  `V × Option (Fin n × Fin (2n+2))`. The arbitrary choice on line 11 is any `pick` avoiding the excluded
  values (`PickSpec`); `theorem1` uses `pickMin`.
* Snapshot: CSLib's `snapObj n` over `ℕ` (`0 = ⊥`; `update_p(x)` only on component `p`, `x ≠ 0`).
  Algorithm 3's lock-freedom is proved with a lexicographic potential: pending update work, stale scanner views,
  `R ≠ S`, scanners heading for the line-51 write, and steps left in the current iteration. The paper
  instead derives it from the amortized bound of Section 4.4.
* Algorithm 3 runs on an **atomic** snapshot `S` and an **atomic** ABA-detecting register `R` over
  vectors. The paper's `S` may be any linearizable snapshot (that gives bounded space), and `R` may be
  Algorithm 2 (by composability). Neither substitution is formalized: CSLib has no composition
  theorem. The linearization function R-1/R-2 is the paper's. It does not look at where `S`'s operations
  take effect, so we expect the proof to transfer to a linearizable `S`, but this is not checked.

**Main results in Lean** (namespace `Podc.StrongLinSnapshots`).

| Paper | Lean | File |
|---|---|---|
| Algorithm 2 (+ `GetSeq`, `DWrite` of Algorithm 1) | `impl`, `implG`, `getSeq` | `ABADefs.lean` |
| Observation 6(b), Lemmas 7–9 (as invariants) | `Inv`, `RInv`, `WInv`, `ProtBy`, `protBy_getSeq` | `ABAInv.lean` |
| Theorems 10, 12 (strong linearizability, Q-1/Q-2) | `linSim`, `stronglyLinearizable` | `ABASim.lean` |
| Theorem 14 (lock-freedom part) | `lockFree` | `ABALockFree.lean` |
| **Theorem 1** | `theorem1` | `ABALockFree.lean` |
| Literal spec of the first `DRead` fails | `not_linearizable_literal` | `FirstRead.lean` |
| **Observation 4** (Algorithm 1 not strongly linearizable) | `Alg1.observation4` | `Alg1.lean` |
| Algorithm 3 | `Snap.impl` | `SnapDefs.lean` |
| Lemmas 17–22 (as invariant, atomic `S`) | `Snap.Inv`, `Snap.Good` | `SnapInv.lean` |
| **Theorem 25** (atomic `S`, `R`) | `Snap.stronglyLinearizable` | `SnapSim.lean` |
| Theorem 32 (lock-freedom part; atomic `S`, `R`) | `Snap.lockFree` | `SnapLockFree.lean` |

**Not formalized.** Theorem 3 and Section 5 (simple types, Aspnes–Herlihy's construction). Theorem 2
with a linearizable `S` and with Algorithm 2 for `R`, and the space bound via Attiya–Rachman. The
complexity bounds of Theorems 14 and 32 (amortized `O(n)` and `O(s + n³u)`). Observation 4 is proved
for one instance (`n = 2`, `pick = pickMin`) rather than for all `n` and choice rules.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. `PickSpec` is satisfiable (`pickMin_spec`). The ABA object `abaObj` is imported from
`Papers/PODC2015/ABADetection/Defs.lean`. The rest of the model comes from CSLib
(`SharedMemory/{Model,StrongLin,LinPoints,Potential,Sequential,Objects/Snapshot}`).
