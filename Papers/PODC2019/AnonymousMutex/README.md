# Optimal Memory-Anonymous Symmetric Deadlock-Free Mutual Exclusion

Zahra Aghazadeh, Damien Imbs, Michel Raynal, Gadi Taubenfeld, Philipp Woelfel.
*Optimal Memory-Anonymous Symmetric Deadlock-Free Mutual Exclusion*, PODC 2019,
DOI [10.1145/3293611.3331594](https://doi.org/10.1145/3293611.3331594); full version
arXiv:1810.03723 (v1, the only version; local PDF
`papers/2019/3293611.3331594_Optimal_Memory_Anonymous_Symmetric_Deadlock_Free_Mutual_Exclusion.pdf`).
All numbering below refers to the arXiv version.

## Model

Shared infrastructure (now in CSLib):

* `Cslib/Computability/Distributed/SharedMemory/Mutex.lean`: lock objects on top of CSLib's asynchronous shared-memory
  model (`Cslib.SharedMemory.Impl`): operations `lock`/`unlock`, client regions computed from the
  history (`regionOf`: remainder → trying → CS → exiting), client well-formedness (`ClientWF`),
  `Impl.MutualExclusion`, fairness of infinite executions (`InfExec.Fair`: a process with a pending
  operation eventually takes a step) and `Impl.DeadlockFree` (paper §2.3: if some process has a
  pending `lock()`/`unlock()` and nobody is in the CS, some operation completes later; fair
  client-well-formed executions). Progress lemma `InfExec.exists_good`.
* `Cslib/Computability/Distributed/SharedMemory/Anonymous.lean`: **memory anonymity and symmetry**. The memory is an array
  of `m` registers (values `V`, all initially `bot`), accessed by atomic read-modify-write steps
  `rmw x f` (any function `f`; reads, writes, compare&swap are special cases) and atomic snapshots.
  Each process `p` has a private permutation `π p` of the register names (adversarial);
  local name `x` means physical register `π p x`. A *symmetric algorithm* (`SymAlg`) is one
  program for all processes; process `p` only differs by its identifier `ids p`. *Symmetry with
  equality* is semantic: identifier renamings `Equiv.Perm Id` act on register values and local
  states and the algorithm is equivariant (`SymAlg.Symmetric`), `bot` is not an identifier.
  `SymAlg.impl A ids π` is the resulting CSLib implementation. `SymAlg.ReadWrite`: only reads,
  writes and snapshots; `SymAlg.NoSnapshot`: only single-register read-modify-write accesses.
* Asynchronous, no crashes, deterministic processes; processes may stay forever in the remainder
  section (and, as in the paper, in the CS).

Paper-specific modelling (details in `differencies.md`): registers hold `Option Id` (`none` = `⊥`);
each loop iteration of the pseudo-code is one atomic access, the local bookkeeping between two
accesses is folded into the continuation; Algorithm 1 uses an atomic snapshot primitive (as the
paper assumes) and writes into the *first* `⊥` entry of its view in local order (the paper leaves
the choice open).

## Main results ↔ Lean

| Paper | Lean | File | Status |
|---|---|---|---|
| `M(n) = {m : ∀ ℓ, 1 < ℓ ≤ n → gcd(ℓ,m) = 1}` | `AnonymousMutex.M` | `LowerBound.lean` | def |
| **Thm 5** (RMW lower bound: symmetric DF mutex with `m` anonymous registers ⇒ `m ∈ M(n)`) | `AnonymousMutex.theorem_5` | `LowerBound.lean` | **proved**, generalized (arbitrary RMW *and* atomic snapshots, any value/state types); also covers the RW necessity result of [15] and the model of Alg. 1 |
| Algorithm 1 (RW + snapshot) | `Alg1.alg1`; symmetric `Alg1.alg1_symmetric`, read/write `Alg1.alg1_readWrite` | `Alg1.lean`, `Alg1Sym.lean` | def + proved |
| **Thm 1** (Alg. 1 mutual exclusion) | `Alg1.theorem_1` (needs only `n ≤ m`), `Alg1.theorem_1_of_M` (paper's hypotheses) | `Alg1Safety.lean` | **proved** |
| **Thm 2** (Alg. 1 deadlock-free for `m > 1`, `m ∈ M(n)`) | `AnonymousMutex.theorem_2_false`, `Alg1.Livelock.not_deadlockFree` | `Alg1Livelock.lean` | **FALSE** (`n = 4`, `m = 5`: explicit fair livelock) |
| Algorithm 2 (compare&swap) | `Alg2.alg2`; symmetric `Alg2.alg2_symmetric` | `Alg2.lean`, `Alg2Sym.lean` | def + proved |
| **Thm 3** (Alg. 2 mutual exclusion) | `Alg2.theorem_3` (any `m ≥ 1`) | `Alg2Safety.lean` | **proved** |
| **Thm 4** (Alg. 2 deadlock-free for `m ∈ M(n)`) | `Alg2.theorem_4` | `Alg2DF.lean` (+ `Alg2Live`, `Alg2Inflation`, `Alg2Resign`, `Alg2Holder`, `Alg2Endgame`) | **proved** (new proof; the paper only sketches it) |
| Tight characterization for RMW registers (§6.2, §7) | `AnonymousMutex.rmw_characterization` | `Main.lean` | **proved** |
| RW necessity `m ∈ M(n) \ {1}` (§4.2; `m ≠ 1` cited from Burns–Lynch [3]) | `AnonymousMutex.rw_necessity'` (uses `theorem_5` and `one_register_impossible`) | `Main.lean`, `OneRegister.lean` | **proved** (the `m = 1` case is a new formal proof of the cited fact) |
| Tight characterization for RW registers (§4.2, §7) — sufficiency | Alg. 1 fails for `n = 4`, `m = 5` (`alg1_summary`) | `Main.lean` | **not established** |

The theorems are checked with `lean_verify` (axioms: `propext`, `Classical.choice`, `Quot.sound`;
the livelock uses `decide +kernel`, which adds no axiom).

## Status

* No `sorry`, no axioms (see the table for the status of each claim).
* **Main finding: Theorem 2 is false.** Algorithm 1 (the paper's headline read/write algorithm)
  is not deadlock-free for 4 processes and 5 ∈ M(4) registers; the counterexample relies on
  *stale* writes (a write into a register that was `⊥` in an old snapshot), which the proof of
  Claims 4–5 ignores. Hence the claimed tight characterization `m ∈ M(n) \ {1}` for read/write
  anonymous memory is not established by the paper (its necessity part holds). Exhaustive bounded
  model checking (all register choices and shrink orders) found no livelock for `n = 2`
  (`m ∈ {3, 5, 7}`) and `n = 3` (`m ∈ {5, 7}`); scripts in `modelcheck/` (not part of the Lean development).
* Theorems 1, 3, 4, 5 hold. Theorem 4's proof is new (the paper's argument is a sketch that
  ignores non-atomic views): a no-inflation lemma for non-atomic scans, an eventual-maximum
  argument showing that some process eventually keeps its registers forever, and a final
  counting argument using `m ∈ M(n)`.
* Not formalized: the double-collect implementation of the snapshot (Alg. 1 uses an atomic
  snapshot, as the paper assumes). The cited Burns–Lynch bound is only needed for `m = 1`, which
  is proved directly (`one_register_impossible`, no symmetry needed).

## CSLib candidates

* `Cslib/Computability/Distributed/SharedMemory/Mutex.lean` (lock objects, fairness, deadlock-freedom, `InfExec.exists_good`).
* `Cslib/Computability/Distributed/SharedMemory/Anonymous.lean` (anonymous memory, symmetric algorithms, step inversion).
* Generic helpers in paper files: `runFrom_agree`, `regionOf_filter` (`OneRegister.lean`),
  `last_entry`, `exists_cstar`-style eventual maximum (`Alg2Holder.lean`), `finset_stab`,
  `exists_time_all` (`Alg2Endgame.lean`), `runFrom_range` (`LowerBound.lean`).
