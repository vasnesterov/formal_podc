# Coordination Without Prior Agreement — PODC 2017

Gadi Taubenfeld. *Coordination Without Prior Agreement.* PODC 2017. DOI
[10.1145/3087801.3087807](https://doi.org/10.1145/3087801.3087807). Formalized version: the author's
copy (10 pages, proofs included; no arXiv version). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** All checked results hold: the impossibility results of
Section 6 (Theorems 6.2, 6.3, 6.5), and correctness of the three algorithms (Figure 1 mutex,
Theorems 3.2–3.3; Figure 2 consensus, Theorems 4.1–4.2; Figure 3 renaming, Theorems 5.1–5.3) for
every adversarial numbering of the registers. The label comes from two small pseudocode issues
(an "arbitrary index" that does not exist in the last iteration, and an input equal to the initial
value `0`). The correctness proofs of all three algorithms are sketches with false intermediate
claims and had to be repaired.

## Mistakes in the paper

* **The algorithm proofs reason as if collects were atomic (Theorems 4.1, 5.2; proofs repaired).**
  For Figure 2 the paper argues that once the first decider `i` has seen all registers equal to
  `(i, v)`, every other process will find `v` in at least `n` entries at line 4. A process whose
  collect started earlier sees a partly stale view, may keep another value and write it once more.
  For Figure 3 there is a second problem: processes that already left round `r` keep writing records
  of later rounds, so the number of `(v, r)` records does drop below `n`, and the catch-up of lines
  8–12 is ignored. Both theorems are true. We prove them with a counting invariant: "registers not
  carrying `v` plus processes that may still write one stale value ≤ `n − 1`", per round for Figure 3
  (records of later rounds force catch-up and carry `(v, r)` in their history). A ghost invariant on
  collects shows the invariant holds when the deciding collect starts.
  (`Consensus.consensus_solves`, `Renaming.renaming_solves`)
* **Theorem 3.3's proof states a false claim (proof repaired).** "Exactly one of the two processes
  must find that less than `⌈m/2⌉` registers are set to its identifier, will give up, …, enabling
  the other … to enter its critical section." With `m = 3`, both processes can give up with no CS
  entry in between, and the first loser is not blocked. The schedule: `q` scans while `p` is exiting
  and writes nothing; it then collects three `0`s and gives up. Meanwhile `p` calls `lock` again,
  `q` leaves its wait loop on the empty memory, `q` writes two registers, `p` writes one, and `p`
  gives up too. Deadlock-freedom still holds for every odd `m`. Our proof shows that at most
  two give-ups occur while no operation completes. Without give-ups the memory stabilizes, and
  oddness of `m` forces a decision. (`Mutex.theorem_3_3`; schedule in
  `modelcheck/mutex_scenario.py`)
* **Theorem 5.1's proof (proof repaired).** Item (4) claims that a process continuing alone into the
  next round wins it. But records of that round written earlier by others may hold another value at
  least `n` times; the solo process adopts it and loses that round too. Also, the proof never shows
  that `myround` stays below `n`. Termination is proved by induction on `n − myround`, using the
  invariant `myround + 1 ≤ |P|`. (`Renaming.renaming_obstructionFree`)
* **Theorem 5.3's proof (proof repaired).** "The algorithm will terminate after `k` rounds" does not
  bound the names. The repaired argument: a process acquiring name `a` sees a history naming `a − 1`
  other distinct participants. Two processes cannot both get the name `n` by a counting argument.
* **Pseudocode issues (⚠️).** Figure 2 line 6 and Figure 3 line 15 ("an arbitrary index `k` such that
  `myview[k] ≠` own record; clearly, such an entry exists") have no such index in the deciding
  iteration, because the until-test comes after the write. We let the write go anywhere (harmless).
  Figure 2 ignores the value `0` at line 4 but does not exclude `0` as an input. With an input `0`
  agreement fails (`n = 2`): process 1 with input `0` fills the registers and decides `0`, then
  process 2 with input `1` decides `1`. We type inputs apart from the empty value.
* **Minor.** The Section 6 proofs are correct. They leave implicit why the adversary may steer each
  process's first write: until then it reads only initial values, so its run does not depend on its
  numbering. For mutual exclusion, the covering processes must run round-robin, not solo, for
  deadlock-freedom to apply. Theorem 3.2 holds for every `m ≥ 2`. Typos: Theorem 6.5's proof says
  "in y" for "in x"; Theorem 5.1's item (3) says "increments mypref" for `myround`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory (CSLib `Impl`), atomic read/write registers, deterministic processes
  with arbitrary identifiers (any type `P`); process code may depend on the process, so the
  impossibility results also cover non-symmetric algorithms. No randomness.
* **Unnamed registers:** each register is a separate base object; every process `p` uses its own
  adversarial numbering `π p : Equiv.Perm ι` of the registers, and all registers start with the same
  value (`Impl.unnamed`, `Podc/Computability/Distributed/SharedMemory/Unnamed.lean`). An algorithm
  is correct iff it is correct for every `π`.
* Collects are not atomic: every read and every write is one step. "Arbitrary index" choices in
  the pseudocode are parameters, and the theorems hold for all admissible choices.
* Failures: crash-stop is implicit (a process may stop taking steps); progress conditions are
  obstruction-freedom (consensus, renaming) and deadlock-freedom (mutex, CSLib's definition with
  fair client-well-formed infinite executions; participation not required). Tasks are CSLib one-shot
  tasks (`consensus P V`; `adaptiveRenaming P` = distinct names in `{1..k}` for `k` participants).
* "Number of processes not a priori known" = an infinite set `P` of potential participants. Safety
  and obstruction-freedom only involve finite executions; for Theorem 6.2, deadlock-freedom is
  required only of infinite executions with finitely many participants (`DeadlockFreeFin`); with
  CSLib's `DeadlockFree` (also executions with infinitely many participants) it is the paper's
  "unbounded" case. "n processes" = `Fintype.card P = n` (or `≤ n` for the algorithms).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 6.2 (no deadlock-free mutex, unknown `n`; unbounded `n`) | `theorem_6_2`, `theorem_6_2_unbounded` | `ImpMutex.lean` |
| (extra) mutex needs `≥ n` unnamed registers | `mutex_card_lt` | `ImpMutex.lean` |
| Thm 6.3 (1)/(2) (no OF consensus: unknown `n` / `n − 1` registers) | `theorem_6_3_1`, `theorem_6_3_2` | `ImpConsensus.lean` |
| Thm 6.5 (1)/(2) (no OF adaptive perfect renaming) | `theorem_6_5_1`, `theorem_6_5_2` | `ImpRenaming.lean` |
| Thm 4.1 (agreement) + Thm 4.2 (validity), Fig. 2 | `Consensus.consensus_solves` | `Consensus.lean` |
| Thm 4.1 (termination under obstruction-freedom) | `Consensus.consensus_obstructionFree` | `Consensus.lean` |
| Fig. 2 correct with a concrete line-6 choice | `Consensus.figure2_correct'` | `Consensus.lean` |
| Thm 3.2 (Fig. 1 mutual exclusion; any `m ≥ 2`) | `Mutex.theorem_3_2` | `MutexME.lean` |
| Thm 3.3 (Fig. 1 deadlock-free; any odd `m`) | `Mutex.theorem_3_3` | `MutexDF.lean` |
| Thm 5.2 + 5.3 (Fig. 3 uniqueness, adaptivity) | `Renaming.renaming_solves` | `Renaming.lean` |
| Thm 5.1 (Fig. 3 termination under obstruction-freedom) | `Renaming.renaming_obstructionFree` | `Renaming.lean` |
| Fig. 3 correct with concrete choices | `Renaming.figure3_correct'` | `Renaming.lean` |

The covering construction shared by Theorems 6.2, 6.3 and 6.5 is `Impl.covering_construction`
(`Podc/Computability/Distributed/SharedMemory/UnnamedCovering.lean`): since a process running alone
from the initial memory reads only the common initial value until its first write, the adversary
can choose its numbering so that this write goes to any prescribed register.

**Not formalized.** Theorem 6.1 and Corollary 6.4 (they rely on results of [17] and the unpublished
[25]); the k-set consensus remark; the election note. Theorems 3.1/3.4 (necessity of `m` odd,
resp. `gcd(m, ℓ) = 1`) are covered, more generally, by `theorem_5` of
[`Papers/PODC2019/AnonymousMutex`](../../PODC2019/AnonymousMutex/README.md).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The algorithms are concrete, and admissible choice functions are exhibited
(`figure2_correct'`, `figure3_correct'`), so the correctness theorems are not vacuous. The
algorithms also show that the hypotheses of the impossibility results are not trivially
unsatisfiable: for example, Figure 1 gives deadlock-free mutual exclusion for 2 processes with
3 registers, consistent with `mutex_card_lt`. Bounded model checkers used
for exploration are in [`modelcheck/`](modelcheck/) and are not part of the Lean development.
CSLib candidates: `Podc/Computability/Distributed/SharedMemory/{Unnamed,UnnamedCovering}.lean`;
`df_progress`/`df_enter` in `ImpMutex.lean` (deadlock-freedom as a round-robin progress guarantee).
