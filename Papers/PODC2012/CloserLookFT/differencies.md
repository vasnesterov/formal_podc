# Differences between the formalization and the paper

Paper: G. Taubenfeld, *A closer look at fault tolerance*, PODC 2012. Formalized version: the
author's full version dated 22 February 2017 (22 pp.; journal version Theory Comput. Syst. 62(5),
2018). Numbering follows the full version.

## Model (all sections)

- Asynchronous shared memory = CSLib's `Cslib.SharedMemory.Impl` (deterministic processes,
  atomic base objects, executions as label lists, infinite executions `InfExec`). Every step of a
  process accesses one register; local computation is folded into the access before it; a `return`
  is a separate step (CSLib convention).
- Crash failures (new, staged in `Podc/Computability/Distributed/SharedMemory/Resilience.lean`):
  in an infinite execution a process *crashes* if from some time on it has a pending operation and
  takes no further step; a process that stops after returning has not failed (it is
  indistinguishable from a correct one). *Participating* = has a pending operation at some time;
  *starved* = pending forever without crashing (a correct participating process that does not
  terminate). `(t, f)`-resilience (§1.3) quantifies over infinite executions with `t' ≤ t` crashed
  processes and bounds the number of starved ones by `f t'`; almost-, partially- and weakly-resilient
  and the wait-free variants are defined literally from §1.3. Infinite executions must contain
  infinitely many labels; executions in which every process eventually stops are not considered
  (they are irrelevant for liveness).
- Participation is not required in §2–§3 (any process may never be invoked); §6 uses
  `AllParticipate`.
- Identifiers: an arbitrary type `P` with decidable equality (symmetric algorithms only compare
  identifiers); `0`/`⊥` is `none`. Number of processes `n = Fintype.card P`.
- One-shot objects: a process invoked again after returning returns its first answer again
  (keeps `Impl` total; one-shot specifications only constrain one-shot executions).

- The comparisons of the resilience notions in §1.3 ("for `n ≥ 3` and `t < n − 2`,
  weakly-`t`-resiliency is strictly weaker than partially-`t`-resiliency", …) are not formalized;
  only the easy implications (`Resilient.almostResilient`, `AlmostResilient.partiallyResilient`,
  `Resilient.weaklyResilient`) are proved.

## Section 2 (election)

- Levels are 0-based (`V[k+1]` of the paper is `V k`); the number of levels is a parameter `L`.
  Safety holds whenever `n ≤ 2^L`; Theorem 2.1 instantiates `L = Nat.clog 2 n = ⌈log₂ n⌉`. For
  `n = 1` the loop is empty (`L = 0`) and the process writes `turn`, then `done`.
- The clearing loops (lines 6, 11) are modelled as one read state and one write state per index;
  the final `return(0)` is folded into the last step. Ghost data (levels passed, registers written,
  registers below which the process has cleared) is recorded in the returned local state; the
  algorithm never reads it.
- **Theorem 2.2** ("in the absence of faults, at least one leader is elected") needs some process to
  participate (`exists_ret_true_of_no_crash` assumes it). ✏️ (degenerate case).
- **Theorem 2.4 (safety), proof**: the paper's credit system is replaced by a precise ghost-state
  accounting (`ElectionSafety.lean`): credits are owned by processes and registers, the transfer of
  Rules 3/4 ("from `q` to `p`") becomes "from the owner of `V[k]`'s credits to a *younger*
  overwriter" (age = order of `turn` writes), owners keep a *reserve* while a younger process is
  about to overwrite, and Lemma 2.3 is replaced by two invariants `c1`/`c2` (a younger process
  cannot have passed a level whose register still holds an older passed process's id). 🛠️ (proof
  gap; statement true). Lemma 2.3 itself is not stated in Lean (its role is played by `c1`/`c2`).
- Rule 3 of the credit system says "the last process to change `V[k]`'s value back to 0" where
  "from 0 to its id" is meant (typo).
- Theorem 2.5 is proved in a stronger form: at most one correct participating process is starved
  for *any* number of crashes (`starved_unique`), and none without crashes, for any `L` (safety
  needs `n ≤ 2^L`, liveness does not).
- Register count (Theorem 2.1): `electionImpl_accessed` shows that every access is to `turn`,
  `done` or `V[k]` with `k < L` (the base-object type also contains unused `V[k]`, `k ≥ L`).
- Symmetry is by construction (identifiers of an arbitrary type, only compared); no separate
  symmetry theorem.
- Theorem 2.6 (message passing) is not formalized.

## Section 3 (test-and-set)

- The sequential specification (§3, first paragraph) and the definition of *winner* before
  Theorem 3.2 use the convention "a winning test-and-set returns 0" (the previous value of the bit),
  while the algorithm returns 1 to the winner (line 14) and 0 to losers. We follow the algorithm.
  Typo.
- §3.1 says the algorithm "makes use of exactly `n` registers"; it uses `n + 1` (`turn`, `winner`,
  `n − 1` locks), as Theorem 3.1 says. Typo.
- The proof of Theorem 3.4 mentions `done = 1`; the test-and-set algorithm has no `done` register
  (`winner` is meant). Typo.
- `tsysStep` ignores schedule entries outside `1..n` (identifier `0` is the empty register value
  and is not a process).
- **Theorem 3.2 is false** for the printed algorithm (🔧; fixed by adding `locked = 0` to the
  losing test at line 10, `TAS.theorem_3_2_fixed` for all `n ≥ 2`) (`TAS.theorem_3_2_false`, `n = 2, 3`).
  See README. Model: `TestAndSet.lean` (custom transition system; a process with no pending
  operation may invoke test-and-set, or reset if it is a winner, so every run is well-structured;
  *winner* = last completed operation is a winning test-and-set and no reset invoked yet).
- The test-and-set model lets a winner invoke only `reset` (from `won`), not a further
  test-and-set, although well-structured runs allow it. This does not affect the counterexample
  (a subset of the paper's runs). For `TAS.theorem_3_2_fixed` it is a restriction: such an extra
  operation only reads `turn` (non-zero while a winner exists) and returns `0`, so it plausibly does
  not create a second winner, but this is not proved.
- The definition of *winner* counts a process whose reset is still pending as a winner (its last
  *completed* operation is a winning test-and-set); with that literal reading even the corrected
  algorithm has two "winners" (one finishing its reset, one that just won). We count winners as
  processes that have not invoked reset. ✏️
- Theorems 3.3, 3.4, Observation 3.5 not formalized. Linearizability of the test-and-set
  implementation (claimed to follow from Theorems 3.2–3.4) is not formalized.

## Section 4 (renaming)

- Theorem 4.1 (composition of `n − 1` election objects) is not formalized as a whole. Its two
  per-object ingredients are proved for the algorithm of Section 2 (`RenamingFacts.lean`):
  `card_outFalse_lt` (fewer processes return 0 from an object than start it; this is what gives
  "at most `n − i + 1` processes participate in object `i`") and `Inv.elected_unique_of_started`
  (safety needs only `#participants ≤ 2^L`).
- The proof of Theorem 4.1 derives "at most `n − i + 1` processes participate in object `i`" from
  the abstract election specification of §2 ("in the absence of faults exactly one … outputs 1").
  Read globally ("no fault anywhere in the run"), this does not suffice: a crash in a later object
  would allow object `i` to elect nobody while all its correct participants move on. The intended
  reading is per object (faults among the object's own participants during its operation), which
  the Section 2 algorithm satisfies (`card_outFalse_lt`). ✏️ (implied assumption).
- Theorem 4.2 relies on the test-and-set bit of Theorem 3.1 with resets (see Section 3) and is
  not formalized.

## Section 5

- Lemma 5.1 / Theorem 5.2 not formalized (they rely on the Common2 constructions of [2, 3] and on
  the test-and-set of Theorem 3.1).

## Section 6

- Lemma 6.1 is formalized for shared memory (`lemma_6_1`): `A'` = `withOutput A`, with one extra
  register `output`; every A-step is preceded by a read of `output`, and a process writes its
  decision to `output` before returning it. Safety (`solves_withOutput`) needs colorlessness only in
  the form `AdoptClosed` (outputs may be copied, including outputs that are written to `output` but
  not yet returned in A). Liveness (`resilient_withOutput`) builds the projected A-execution
  (`exists_infExec_of_chain`) in the branch where nobody ever writes `output`; there nobody adopts,
  so adopters are never extra crashes of A.
- Lemma 6.1 needs only `t ≤ n − 2`; `n ≥ 3` is not used. Theorem 6.3 does not use `1 ≤ k`.
- "Algorithm" (`HasRegAlgorithm`) = uses only registers, accepts every input in every process,
  solves the task, has the progress property. Colorless tasks: `Colorless T` (Δ depends only on the
  sets of input and output values, downward closed in outputs).
- Theorems 6.2/6.3: the external impossibility results (Loui–Abu-Amara; Borowsky–Gafni /
  Herlihy–Shavit / Saks–Zaharoglou) are hypotheses (`LAAImpossibility`,
  `SetConsensusImpossibility`); they need `|V| ≥ 2` (resp. `k + 1`) values, which the non-vacuity
  lemmas illustrate (`not_LAAImpossibility_unit`, `not_setConsensusImpossibility`).
- Message-passing versions of Lemma 6.1 and Theorems 6.2/6.3, and Corollary 6.4, are not formalized.
