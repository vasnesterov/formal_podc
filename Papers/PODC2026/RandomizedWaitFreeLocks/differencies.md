# Differences between the formalization and the paper

Paper: Aeini, Bencivenga, Giakkoupis, Woelfel, *Simple and Efficient Randomized Wait-Free Locks*,
PODC 2026; full version HAL hal-05628351v1 (numbering of the full version).

## Mistakes and proof gaps (see README)

1. ✏️ (S1)/(S2) literally cover the dummy descriptor's thunk, which helpers execute although there
   is no `TryLock(dummy)`/`Lock(dummy)` call, so the first half of (S2) fails for it ((S1) does not:
   a call of `dummy.execute()` responds before the first promotion). Formalization: the dummy is
   `none`, done from the start, and its `execute()` steps emit no events, so (S1)/(S2) speak about
   real descriptors only.
2. ✏️ Algorithm 2, line 16: `⌊log C⌋` with `C = 0` (calls of line 22) is undefined; the Lean model
   uses `Nat.log 2 0 = 0` (any index is fine for safety).
3. Typo: Algorithm 2 declares `R[0..⌊log n⌋+1]` but initializes `R[0..log n]`; the extra register is
   never read. Our `R` is an unbounded array initialized to the dummy.
4. Typo: proof of Lemma 4.8, "pending `HelpAndPromote()` call … not yet executed line 9" should be a
   `TryLock()` call.
5. 🔧 Proof gap, Lemma 4.8: the coupling indexes coins by an order that depends on the future
   (invocation order among processes that will execute line 6 after `t`), so claim (1) is not
   well-defined. Replaced by a supermartingale/potential argument (`V`, `V_super`,
   `prob_le_of_super`); the pathwise rank bound (Corollary 4.7 + Lemma 4.5) is the invariant clause
   `k1`/`k2` plus `Sig_le`.
6. 🔧 Proof gap, (S2) for Algorithms 2 and 3: "the execution interval lies within the single
   `Lock(ω)` call" is not argued (only the response half is); Lemma 4.15's "abort_sig = True" is not
   justified. Proved by invariants in `Alg2*.lean`, `Alg3.lean`.

## Modelling choices (all algorithms)

- Execution interval: Section 2.2 says it "ends with the response of the first `ω.execute()` call";
  read as the call invoked first, (S1) would fail for every algorithm (a helper that invoked
  `ω.execute()` first may stall inside it while another helper finishes `ω`'s thunk and the next
  descriptor is promoted and executed). We use the reading stated in Sections 4.2.1 and 4.3.1: it ends
  at the first response of any `ω.execute()` call.
- (S1), (S2) are stated on the event list of an execution (`Trace.lean`): `InInterval es d t`
  (first `exS d` ≤ `t`, no `exE d` before `t`), `S1`, `S2`. (S2)'s "within a single call" is: an
  invocation `inv p d` at index `i` before the interval and no response of `p` in `(i, t]` for every
  `t` of the interval.
- `execute()` = two steps (invocation `exS`, response `exE` which sets `isDone`); the thunk's own
  steps act on other memory and are omitted (any interleaving is allowed between the two steps).
  A thunk whose `execute()` is a single step is the special case where nothing is scheduled in
  between.
- Idempotence of thunks is not modelled (not needed: only the first invocation/response matter).
- Every step advances a ghost clock; invalid adversary actions are `tau` steps.
- Processes: arbitrary type `P` (any number, possibly infinite); descriptors `D`; finitely many
  steps in any execution.
- Ghost variables (times of writes/changes/reads, `act`, `started`, `retT`, `failed`, call
  counters) do not influence the algorithm.

## Algorithm 1

- Owners: a fixed function `own : D → P`; `TryLock(δ)` may be invoked by `own δ` only, and only if
  no earlier `TryLock(δ)` returned `True` (ghost `retT`). This is the paper's requirement.
- Invocation = the step of line 5 (`C.FAI()`); response = line 10 (`isDone`); the event carries the
  return value.
- Line 6 with coin `false` is a separate local step instead of being fused with the read of line 1
  (strictly more interleavings for the adversary: the safety theorems and the probability bounds
  transfer to the paper's model).
- Lemma 4.3 is not proved by the paper's induction over promotions but by one inductive invariant
  (`Alg1Inv.lean`, 37 clauses, `inv_step`); its clauses `f4` (promotions install never-promoted
  descriptors whose owner is between lines 6 and 8), `o1`–`o4`, `g1`–`g3` (Lemma 4.5) and `ij`/`ik`
  (stale helpers) are the state forms of Lemmas 4.3 and 4.5. Lemma 4.5 is proved for the processes
  it is used for (those whose line 6 is not older than the last write), not for arbitrary pairs of
  `HelpAndPromote()` calls.
- Probability: the adversary is a deterministic function of the whole history of configurations
  (randomized adversaries cannot do better for an upper bound on a failure probability). The value
  `prob … n` is the probability that the event holds after `n` steps; `Bad` ("the `k`-th call of `p`
  returned `False`") is monotone, so this is "fails within `n` steps". We bound the failure
  probability for every horizon (equivalent to the infinite-horizon bound); we do not state the
  success probability of a call that never terminates.
- Theorem 4.9 is stated with an explicit constant: failure probability `≤ 1 − 1/(14 κ log₂²(κ+1))`,
  `κ = |S|` for any finite `S` containing the processes with a pending call right after the
  invocation (the paper: `Ω(1/(k log²(k+1)))`, `k` the contention at invocation). The proof uses the
  observed contention `b ≤ |act| ≤ κ`.
- `log` is base 2 (as everywhere in the paper). With the natural logarithm the series is ≈ 0.484,
  still `≤ 1/2`, but our proof uses base 2 (bound `3/7`).
- Theorem 4.4's (S1) and (S2) hold for every adversary and every sequence of coin outcomes.

## Algorithms 2 and 3 (safety only)

- Random choices (line 30's index; line 51's write decision, line 50's level and lines 42–46's new
  level in Algorithm 3) are made by the adversary: an over-approximation, sound for safety.
- Algorithm 2: invocation = the first read of line 11 in the first `HelpAndPromote()` of line 22;
  the `while` test of line 25 is two steps; the abort test of line 26 is evaluated in the next
  shared-memory step; `abort p` is an adversary action allowed during a call; line 17 reads
  `R[Nat.log 2 C]`.
- Algorithm 3: invocation = line 48 (`C.FAI()`), response = line 54 (`C.FAD()`), whose event value
  is `isDone`, proved always `true` (Lemma 4.34). The safety proof does not use the assumption that
  `Lock` calls use distinct descriptors (the model still enforces it).

## Not formalized

- Theorems 4.18 and 4.37 (expected step complexity of Algorithms 2 and 3) and their lemmas
  (4.16–4.30, 4.35–4.58); the oblivious-adversary analysis of Algorithm 2.
- The derived expected number of steps of repeated `TryLock` calls (`O(1 + κ log² κ)`).
