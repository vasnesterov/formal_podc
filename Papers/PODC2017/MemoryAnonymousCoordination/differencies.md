# Differences between the formalization and the paper

Gadi Taubenfeld, *Coordination Without Prior Agreement*, PODC 2017 (author copy, 10 pp.).

Two pseudocode issues (the "arbitrary index" of Fig. 2 line 6 / Fig. 3 line 15 does not exist in the
last iteration; Fig. 2 fails for an input equal to the initial value `0`) and the proof gaps of
Theorems 3.3, 4.1, 5.1, 5.2, 5.3 are listed below; every theorem holds in the intended reading.

## Model (all sections)

* **Unnamed registers.** CSLib's asynchronous shared-memory model (`Impl`, `Config`, labelled
  executions), with read/write registers as separate base objects (`RegFamily ι V v₀`). An
  algorithm is written in local register names; `I.unnamed π`
  (`Podc/Computability/Distributed/SharedMemory/Unnamed.lean`) runs it with an adversarial private
  numbering `π p : Equiv.Perm ι` of each process; all registers start with the same value `v₀`.
  "The algorithm is correct" = correct for **every** `π`. The paper's "initial register + ordering"
  is the special case of cyclic-shift-type numberings; arbitrary permutations are what the paper
  means ("the first register examined and the subsequent order … may be different for each
  process").
* **Granularity.** Every read and every write is one atomic step; collects (`for j … myview[j] :=
  p.i[j]`) are *not* atomic. Local computations are folded into the preceding step.
* **"Arbitrary index"** choices (Fig. 2 line 6, Fig. 3 lines 9 and 15) are parameters of the
  algorithm, and the theorems hold for every admissible choice function.
* **Process code** may depend on the process (`I.act p`), so the impossibility results (Section 6)
  cover non-symmetric algorithms, as the paper claims ("These results also hold for algorithms
  which are not symmetric"). Identifiers are elements of an arbitrary type `P`.
* **Tasks** (consensus, renaming) are CSLib one-shot tasks (`Task`, `Impl.Solves`): safety on every
  finite one-shot execution, inputs = first invocations, outputs = first responses, participants =
  processes that invoked. Obstruction-freedom: `Impl.ObstructionFree` (algorithms) and the weaker
  `Impl.OneShotOF` (assumed in the impossibility results, which makes them stronger).
* **Mutual exclusion**: CSLib `Impl.MutualExclusion` / `Impl.DeadlockFree` (fair, client-well-formed
  infinite executions; participation not required; deadlock-freedom does not require processes to
  leave the critical section — weaker than the paper's assumption that processes always leave it,
  which makes the impossibility stronger).

## Section 6 (impossibility results)

* **Theorem 6.2** (`theorem_6_2`, `ImpMutex.lean`): "number of processes not a priori known" is
  modelled as an infinite set `P` of potential participants; the number of registers `ι` is
  arbitrary (finite or infinite). Deadlock-freedom is assumed only for fair infinite executions in
  which finitely many processes take part (`DeadlockFreeFin`): an algorithm for a finite but
  unknown number of processes need not guarantee anything when infinitely many processes join.
  CSLib's `Impl.DeadlockFree` (all fair executions) is the paper's "unbounded" case, a weaker
  impossibility, obtained as the corollary `theorem_6_2_unbounded`. (Consensus and renaming,
  Theorems 6.3/6.5, need no such restriction: safety and obstruction-freedom only concern finite
  executions.) Hypothesis added: every invocation is
  allowed (`I.allowed`), otherwise an algorithm could forbid all invocations and be vacuously correct.
  Extra result not in the paper: the same argument for `n ≥ 2` known processes and `≤ n − 1`
  registers (`mutex_card_lt`).
* **Theorems 6.3 and 6.5** (`theorem_6_3_1/2`, `theorem_6_5_1/2`): part (2) is proved for
  `Fintype.card ι ≤ Fintype.card P − 1` (the paper: exactly `n − 1` registers). Consensus is stated
  for any value type with two distinct inputs (the paper uses binary inputs). Adaptive perfect
  renaming is `adaptiveRenaming P`: distinct names, and every name in `{1, …, k}` for `k`
  participants (perfect renaming `{1..n}` follows when `|P| = n`).
* **Proofs.** The paper's covering argument is followed (`covering_construction`,
  `Podc/Computability/Distributed/SharedMemory/UnnamedCovering.lean`). Two points the paper leaves
  implicit are made explicit: (a) the register a process first writes when running alone does not
  depend on its numbering, because until then it only reads the common initial value (`blindStep`);
  this is what allows "letting each process scan the registers in an order which ensures" that it
  covers a prescribed register; (b) the "must write" step is used for every process of `P`, not only
  for `q` (each process of `P` must reach a write before returning in its solo run). For mutual
  exclusion, deadlock-freedom is used through a round-robin run of the covering processes
  (`df_progress`, `df_enter`): a solo run of one of them would not be fair. These are routine
  details.
* Typo: in the proof of Theorem 6.5, "By construction, in y the processes in P together cover
  …" should be "in x".
* **Not formalized:** Theorem 6.1 and Corollary 6.4 (they combine Theorems 6.2/6.3 with results of
  [17] and the unpublished manuscript [25]); the remark on k-set consensus; Theorems 3.1/3.4
  (necessity part) are covered, more generally, by `theorem_5` of
  `Papers/PODC2019/AnonymousMutex/LowerBound.lean`.

## Section 4 (Figure 2, obstruction-free consensus with 2n − 1 registers)

* Registers hold `Option (P × V)`; `none` is the initial record `(0, 0)`. Inputs range over `V`,
  hence can never be the initial `val` value `0`. **Paper issue (🔧):** the input domain is not
  restricted, but line 4 ignores the value `0`; if a process may have input `0`, agreement fails:
  with `n = 2`, a process with input `0` runs alone, fills the 3 registers with `(i, 0)` and decides
  `0`; then a process with input `1` ignores the `0` entries, keeps `1`, overwrites all registers
  and decides `1` (found by `modelcheck/cons.py 2 0,1 any skip`). `0` is plainly used as the
  "empty" value, so a reader would assume inputs are non-zero. But the paper never restricts the
  inputs, and Section 6.3 states binary consensus with inputs `{0, 1}` while referring back to
  Figure 2 ("In Section 4, we have presented an obstruction-free consensus for n processes"). The
  intended version is recoverable from the paper (identifiers are positive integers, so `id = 0`
  marks an unwritten register; the proof of Theorem 4.2 speaks of "a value (different from 0)" read
  from a register), the fix is local (line 4 counts only entries with `id ≠ 0`, or the registers
  start at `⊥`), and no proof step uses the wrong version.
* **Line 6 (✏️, pseudocode missing case):** "Clearly, such an arbitrary entry exists" is false
  in the deciding iteration, where every entry equals `(i, mypref)` (the until-test of line 8 is
  evaluated after the write of line 7). We write `(i, mypref)` to the selected register anyway
  (harmless). Correctness is proved for every `sel` (safety) and every `sel` choosing a differing
  entry when one exists (termination).
* **Proof gap (🔧):** the proof of Theorem 4.1 says that after the first decider `i` saw all
  registers equal to `(i, v)`, "all the other processes, when executing line 4, will find that `v`
  appears in at least `n`" entries. This is false for a process whose (non-atomic) collect started
  before that point: its partly stale view need not contain `n` copies of `v`, and it then writes
  a non-`v` value. The theorem survives because each process can do this at most once. Repaired
  proof: the invariant `Lock` (`ConsensusLock.lean`): there is a set `T` of "token holders" (each
  may still write one non-`v` value) with `#{registers with val ≠ v} + |T| ≤ n − 1`, plus a bound for
  every collecting process outside `T`; it is preserved by all steps, it is established at the start
  of the deciding collect (ghost invariant on collects, `ConsensusSafety.lean`: a collect that reads
  only `(i, ·)` entries started when all registers held them), and two locks for different values
  are incompatible (`2n > 2n − 1`). The paper's "let `i` be the first process to decide" must be
  replaced by "the process whose deciding collect starts first" (decisions and collect starts may
  be ordered differently); the lock argument makes this immaterial.
* Termination (`ConsensusOF.lean`): the preference is fixed after one solo collect and each further
  iteration increases the number of registers holding `(i, mypref)`; this is the paper's argument
  with the stabilization step made explicit.
* Theorem 4.1's statement mixes termination and agreement; we prove `ObstructionFree` (from every
  reachable configuration) and `Solves (consensus P V)` separately; `Fintype.card P ≤ n` processes
  (at most `n` participate), `n ≥ 1`.
* Not formalized: the note on obstruction-free election (immediate from consensus with ids as
  inputs).

## Section 3 (Figure 1, two-process mutual exclusion)

* Registers hold `Option P` (`none` = `0`). Line 2 and line 5 ("`if p.i[j] = 0 then p.i[j] := i`",
  "`if p.i[j] = i then p.i[j] := 0`") are a read followed by a *separate* write step (the paper does
  not say they are atomic; non-atomic is the weaker assumption). `lock()` returns when line 10
  succeeds; `unlock()` is line 12. Processes: `Fintype.card P ≤ 2` (ME), `= 2` (DF). Symmetry is
  not stated as a Lean theorem (the code only uses `some p`; noted in `MutexAlg.lean`).
* **Theorem 3.2** (`theorem_3_2`) is proved for every `m ≥ 2`: the threshold `⌈m/2⌉` and oddness play
  no role in mutual exclusion (for `m = 1` it fails). The paper's proof is essentially right; it omits
  that the other process may still have one pending write from its exit section (line 12) and its
  "less than `⌈m/2⌉`, resets" step is not needed. Routine.
* **Theorem 3.3** (`theorem_3_3`) is proved for every odd `m` (also `m = 1`); parity is needed
  (livelocks for `m = 2, 4` in the model checker). **Proof gap (🛠️):** the proof's claim "When there
  is contention … exactly one of the two processes must find that less than `⌈m/2⌉` of the registers
  are set to its identifier, will give up, wait …, enabling the other process to write all the `m`
  registers and to enter its critical section" is false. Counterexample (`m = 3`, both processes scan
  in the same order; `modelcheck/mutex_scenario.py 3 0,1,2`): `p` enters the CS alone and starts its
  exit; `q` scans during `p`'s line-12 writes, reads all three registers as `p` and writes nothing;
  `p` finishes zeroing, `q` collects three `0`s and gives up; `p` calls `lock` again; `q` finishes
  its wait pass on an all-zero memory and leaves the wait loop; `q` writes registers 1 and 2, `p`
  writes register 3 and also gives up. Both gave up with no CS entry in between, and the first
  loser was not blocked. Repaired proof (`MutexDF.lean`, `MutexDFInv.lean`, `MutexRegion.lean`): while
  no operation completes, at most two give-ups can happen (invariants `DFInv`, `GInv`, `DInv`);
  without give-ups the zeros and then the whole memory stabilize, and since `m` is odd one process
  either gives up or enters the CS.
* Theorem 3.1 ("iff `m` odd"): the "if" direction is Theorems 3.2 + 3.3; the "only if" direction is
  the case `n = 2` of Theorem 3.4, covered by `theorem_5` of `Papers/PODC2019/AnonymousMutex`
  (not re-proved here).

## Section 5 (Figure 3, adaptive perfect renaming)

* Registers hold `Option (P × St P)` with `St = (val, round, history)`; `none` is the initial
  `(0, 0, 0, ∅)`. Identifiers are arbitrary (`P`), `Fintype.card P ≤ n`, `n ≥ 1`. Line 5 chooses `v`
  classically (it is unique in every execution, as a consequence of the proof). Lines 9 and 15 are
  parameters (`Sel`); proofs assume `Sel.OK`: line 9 copies an entry of maximal round, line 15
  picks an entry different from the own record when one exists. As in Fig. 2, in the iteration
  that leaves the inner loop no such entry exists (✏️, same pseudocode missing case); the write
  is still performed. Line 21 keeps the paper's test `myround = n`.
* Specification: `adaptiveRenaming P` (distinct names; every name in `{1..k}` for `k`
  participants), the same object as in Theorem 6.5. Theorem 5.2 (names in `{1..n}`) follows from
  adaptivity with `k ≤ |P| ≤ n`.
* **Proof gap in Theorem 5.2 (🛠️):** the argument "each of the other `n − 1` processes might write
  into one of the registers during round `r` … thus all the other processes, when executing line 13
  during round `r`, will find that `v` appears in at least `n` entries" has the same flaw as in
  Theorem 4.1 (non-atomic collects, stale pending writes) and in addition ignores writes of other
  rounds and catch-up (lines 8–12): processes that already left round `r` keep writing records of
  later rounds, so the number of `(v, r)` records does drop below `n`. Repaired by a per-round lock
  `Lock v t` (`RenamingLock.lean`): a record is "bad" if its round is `≤ t` and it is not `(v, t)`;
  records of later rounds are harmless because a collect that sees one catches up beyond `t`, and the
  lock also requires every record of a later round to contain `(v, t)` in its history. Together with
  a ghost invariant for collects and the well-formedness of histories (one winner per earlier round,
  distinct winners, each locked, never the record's owner) this gives agreement per round and that
  a process is elected at most once (`RenamingSafety.lean`).
* **Proof gap in Theorem 5.3 (🔧):** "the algorithm will terminate after `k` rounds" does not by
  itself bound the names. The repaired argument: a process that gets name `a` sees a history naming
  `a − 1` other, distinct participants, so `a ≤ k`; that two processes cannot both get the name `n`
  (line 22) needs a counting argument (otherwise there would be `n + 1` distinct processes).
* **Proof errors in Theorem 5.1 (🔧):** (a) item (4) claims that a process continuing alone into the
  next round wins it ("since mypref = i, it returns the current round number"); false — records of
  that round written earlier by other processes may contain another value at least `n` times, which
  the solo process adopts at line 14, so it loses that round too. Termination is instead proved by
  induction on `n − myround` (`RenamingOF.lean`). (b) The proof never shows that `myround` stays
  below `n` (needed for the test `myround = n` of line 21 to stop the loop); we derive `round + 1 ≤
  |P|` from the invariant. (c) Typo: item (3) says "Process i increments mypref by 1 (line
  20)"; it is `myround`. Also "updates its history (line 19) and round number (line 19)" — line 20.
* Theorem 5.1 is proved as `ObstructionFree` from every reachable configuration.
