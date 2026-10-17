# Space-Optimal Election in Anonymous Memory (Bezout) — PODC 2020

Emmanuel Godard, Damien Imbs, Michel Raynal, Gadi Taubenfeld. *From Bezout's Identity to
Space-Optimal Election in Anonymous Memory Systems.* PODC 2020. DOI
[10.1145/3382734.3405727](https://doi.org/10.1145/3382734.3405727). Formalized version: the
proceedings text (HAL hal-03148627); there is no arXiv version.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** All results are proved: Theorems 1, 2 and 4, and
Corollaries 1–3 as iff characterizations. The termination proofs of Algorithms 1 and 2 and the
safety proof of Algorithm 2 (Lemma 2) are sketches with genuine gaps, repaired here. The claim in
§4 that `v′` is positive fails for `m = 1`.

## Mistakes in the paper

No main statement is wrong. The proofs have gaps:

* **Theorem 4's proofs (Lemmas 1 and 2) are sketches (proof gap, statement true).** Lemma 2
  reuses Claim 1 of Algorithm 1 for each competition. In Algorithm 2, however, a process decides
  a write from a copy read in an earlier, *non-atomic* collect, and the write can land much
  later. The property really needed is that a write for level `L` never lands after the register
  has reached level `L + 1`. Proving it takes a per-register invariant over every process's
  status for that register. The counting behind "exactly `d` leaders" is also missing. When the
  first process sets `finishing`, every process has already won exactly `v ℓ` competitions: the
  collected sum of levels never exceeds the true sum, because levels are monotone. Lemma 1
  (termination) is one paragraph. Our proof shows that once solved competitions stop increasing,
  the candidate flags, `to_win` and `finishing` stabilize. It then finds an open register with a
  stable candidate, using `d ≤ n`, and replays Algorithm 1's convergence argument there.
  (`theorem_4`, `Alg2.alg2_agreement`, `Alg2.alg2_terminates`)
* **Theorem 2's termination proof is a sketch (proof gap, statement true).** "This pattern is
  repeated until all processes except one are losers" does not explain why two candidates
  cannot overwrite each other forever while losers keep re-announcing their loss. The missing
  step is a "minimal discarded set" argument. Once the candidates and their sets are stable,
  any ⊥-value a candidate `c′` reads was written by a loser `j` who had read another candidate
  `c`'s value without `j` in it, so `D_c ⊊ D_{c′}`. This is impossible for the candidate with
  the smallest set. The committing phase needs "quiet" losers: once the leader knows `j`, `j`
  never writes again. Line 16 copies `REG.discarded` without checking its phase; the paper
  ignores this, and it turns out harmless. (`Alg1.alg1_terminates`, `Alg1.alg1_agreement`)
* **Theorem 1's proof is imprecise (statement true).** It fixes the anonymity permutations
  lazily, through "the k-th *new* register `pᵢ` accesses". This is legitimate without snapshots,
  and the paper explains it. It also says that processes of a group with the same number of
  steps are "in the same state". Literally they differ by their identifiers: they are in the
  same state *up to a renaming of identifiers*. We fix the permutations in advance (process `i`
  of each group sees the memory rotated by `i·m/δ`), which also covers snapshots.
  (`theorem_1_1`, `theorem_1_2`)
* **Smaller slips.** In Section 4, "both `u′` and `v′` are positive" fails for `m = 1`, `n = 2`,
  `(u, v) = (−1, 1)`, where `v′ = 0`; only `v′ ≥ 0` is needed (`v_prime_zero_example`).
  The prose of §3.1 says line 8 "leaves `REG.id = id_ℓ`", but the code writes `⊥`; we follow
  the code. Typos in Algorithm 2
  and Section 5: `reg_i.discarded` should be `reg_i[x].discarded`; there are wrong line
  references (N(2)/N(3) instead of N(5)/N(6), N(3) instead of N(4)); "jumps to the level" where
  the code increments by one. In Claim 1, `loser_i` "false" should be "true".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory (CSLib `Impl`), fault-free, deterministic processes. All `n`
  processes participate: each invokes `elect()` exactly once.
* *Termination*: in every fair infinite execution where all processes invoke, every process
  returns. Fair means a pending process eventually takes a step.
* Anonymous memory of `m` registers, all with the same initial value. Each process has its own
  adversarial permutation of the register names, fixed for the run (CSLib `SymAlg.impl`).
  Lower bounds allow arbitrary read-modify-write accesses and atomic snapshots. The algorithms
  use plain reads and writes only (`ReadWrite`), and Algorithm 2's collect is `m` separate reads.
* *Symmetry* ("identifiers compared only for equality") is semantic. The algorithm commutes with
  every renaming of identifiers, and the initial register value is not an identifier.
* Outputs are bits ("am I elected?") for `DElection d` / `ExactElection d`. This is weaker than
  the paper's leader-set outputs, so the impossibility is stronger. The algorithms are also
  proved to agree on the leader set itself.
* Lower bounds need correctness for every permutation choice but only one injective identifier
  assignment.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (1): no symmetric `d`-election if `gcd(m,n) > d` | `theorem_1_1` | `LowerBound.lean` |
| Theorem 1 (2): no exact `d`-election if `gcd(m,n) ∤ d` | `theorem_1_2` | `LowerBound.lean` |
| Lock-step symmetry argument (`k` groups of `gcd(m,n)`) | `exists_symmetric_outcome`, `exists_elected_mul` | `LockStepExec.lean`, `LowerBound.lean` |
| Theorem 2: Alg. 1, one RW register | `Alg1.alg1_agreement`, `Alg1.alg1_terminates`, `Alg1.alg1_symmetric`, `Alg1.alg1_readWrite`, `one_register_leader_election` | `Alg1Main.lean`, `Alg1Sym.lean`, `Main.lean` |
| Theorem 3 + Section 4 (Bezout rewriting) | `theorem_3`, `paper_rewrite`, `exists_bezout_nat`, `bezout_count` | `Bezout.lean` |
| Lemma 2 (safety of Alg. 2) | `Alg2.alg2_agreement` | `Alg2Main.lean` |
| Lemma 1 (termination of Alg. 2) | `Alg2.alg2_terminates` | `Alg2Main.lean` |
| Theorem 4 (paper's parameters) | `theorem_4` | `Corollaries.lean` |
| Corollaries 1, 2, 3 (iff, RW and RMW) | `corollary_1`, `corollary_2`, `corollary_3` | `Corollaries.lean` |

**Not formalized.** The register-size claims (bits per register) and the remark on electing
without required participation (§1.3, which cites [1]).

**Trust.** No `sorry`; all listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The hypotheses of Theorem 1 are satisfiable: Algorithm 1 meets them for `m = 1`
(`theorem_1_nonvacuous`). Corollaries 1–3 are iff statements whose sufficiency direction
exhibits Algorithm 2. The model (anonymous memory, symmetric algorithms) is CSLib's
`Cslib/Computability/Distributed/SharedMemory/Anonymous.lean`. The symmetric `k`-group lock-step
rounds are the shared library `Cslib/Computability/Distributed/SharedMemory/Anonymous/LockStep.lean` (`SymAlg.LSSetup`,
`SymAlg.SymCfg`, `SymAlg.round_*`; also used by `Papers/PODC2019/AnonymousMutex` with one group);
fairness, prefixes of infinite executions and pending/return lemmas come from
`Cslib/Computability/Distributed/SharedMemory/Potential.lean` (`InfExec.Fair`, `InfExec.pre`, `InfExec.first_act`,
`InfExec.exists_ret_between`; `InfExec.exists_act_of_pending`, `InfExec.false_of_descent` also in
`Cslib/Computability/Distributed/SharedMemory/Potential.lean`), eventual-stabilization lemmas from
`Cslib/Foundations/Data/Nat/Descent.lean`, and the
election object is the interface-only object `ObjSpec.iface Unit R`. Outputs of extended executions:
`outputs_append`, `outputs_concat`, `outputs_ne_none_of_mem` (in
`Cslib/Computability/Distributed/SharedMemory/Task.lean`).

**CSLib candidates.** The generic one-shot progress
definitions in `Defs.lean`, and the lock-step execution of all groups in `LockStepExec.lean`.
