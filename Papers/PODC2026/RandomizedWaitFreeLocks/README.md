# Simple and Efficient Randomized Wait-Free Locks — PODC 2026

Kahbod Aeini, Dante Bencivenga, George Giakkoupis, Philipp Woelfel. *Simple and Efficient Randomized
Wait-Free Locks.* PODC 2026. DOI [10.1145/3796701.3815952](https://doi.org/10.1145/3796701.3815952).
Formalized version: the full version, Inria HAL report hal-05628351v1 (32 pp., May 2026). The PODC
paper proves only Algorithm 1; the full version also has the proofs for Algorithms 2 and 3.
Numbering follows the full version.

**Verdict: 🔧 Easy fix.** All checked results hold. These are the safety properties (S1), (S2) of all
three locks and Theorem 4.9, the `Ω(1/(k log²(k+1)))` success probability of Algorithm 1's `TryLock`
against a weak adaptive adversary. The proof of Lemma 4.8, the probabilistic core of Theorem 4.9,
has a gap: its coupling indexes the coins by a future-dependent order. We repaired it with a
potential-function argument. The expected step complexity theorems of Algorithms 2 and 3
(Theorems 4.18 and 4.37) were not checked.

## Mistakes in the paper

### ✏️ Slips
- (S1) and (S2) are stated for every thunk that is executed, which literally includes the dummy
  descriptor's no-op thunk. Its `execute()` is called by every `HelpAndPromote()` that reads it from
  `L`, but there is no `TryLock(dummy)` or `Lock(dummy)` call, so the first half of (S2) fails for it.
  ((S1) is fine for the dummy: some call of its `execute()` responds before the first promotion.)
  We treat the dummy as done from the start and give its `execute()` calls no events.
- Algorithm 2, line 16 computes `⌊log C.Read()⌋`, but in the `HelpAndPromote()` calls of line 22
  (before the caller's `C.FAI()`) `C` can be `0`. The Lean model reads index `0` there. This does not
  matter for safety.

### Typos
- Algorithm 2 declares registers `R[0..⌊log n⌋+1]` but initializes only `R[0..log n]`. This is harmless:
  line 17 reads `R[⌊log C⌋]` with `C ≤ n`, so the last register is never read.
- Proof of Lemma 4.8: "each such process has a pending `HelpAndPromote()` call at point `t*` which has
  not yet executed line 9" should say `TryLock()` call.

## Proof gaps (statements true)

### 🔧 Lemma 4.8 (Algorithm 1, the coupling)
The coupling's coins `c_i` belong to the `i`-th process "in the order in which they invoke their
`TryLock()` calls" among those that execute line 6 after `t`. That index depends on the future, so
claim (1), "given the execution up to just before `t_i`, `p_i` writes with probability ≤ `ε_i`", is not
well-defined.

**Impact.** Lemma 4.8 and Theorem 4.9 are true. Repaired (`lemma_4_8`, `theorem_4_9`).

<details><summary><b>Details.</b></summary>

When `p_i` flips its coin, it is not yet known which processes invoked earlier will still execute
line 6 after `t`, so its index `i` is not determined. Indexing by the order of the line-6 steps instead
would be adapted, but then the `j`-th such process can observe contention `1`. So "wlog `p_i` uses `c_i`"
is not a valid coupling as written. The conclusion survives because the bound holds pathwise. At any
time, the processes that executed line 6 after `t` are all still before line 9 (Lemma 4.5). Sorted by
invocation, the `j`-th observed contention `≥ j` (Corollary 4.7). So the sum of their conditional write
probabilities is `≤ Σ_j ε_j ≤ 3/7 < 1/2`, and a sum of predictable probabilities bounds the probability
that any trial succeeds.

</details>

**Repair.** The potential `V = 1/2 − Σ_{x∈W} ε(b_x)` while `p`'s descriptor is in `R` and not
promoted, `0` once it is promoted, and `1 − ε(b_p)/2` before `p`'s line 6. No adversary action
increases its expectation (`V_super`), so it bounds the failure probability for every adversary and
horizon (`prob_le_of_super`).

### 🔧 (S2) for Algorithms 2 and 3, and Lemma 4.15
The first half of (S2) is never argued for Algorithms 2 and 3: the execution interval of `ω.T` lies
inside the `Lock(ω)` call. Lemmas 4.15 and 4.34 only handle the response. Lemma 4.15 also asserts
without proof that a `False` return implies the caller saw `abort_sig`.

**Impact.** Statements true. Proved with short invariants (`alg2_safety`, `lemma_4_15`, `alg3_safety`).

<details><summary><b>Details.</b></summary>

`ω` can reach `L` only through `R`, which only `ω`'s caller writes during its call, or as the caller's
own argument of `HelpAndPromote(D)`. Only the caller sets `ω.stat = susp`, in line 27, after seeing
the signal.

</details>

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory, one atomic step per time point, any number of processes (`P` arbitrary),
  descriptors `D` with the dummy as `none : Option D`. Executions are lists of adversary actions; a
  step emits an event (`inv`, `resp`, `exS`/`exE` for the invocation/response of `execute()`, `tau`).
  (S1), (S2) are stated on these event lists (`Trace.lean`). A generic bridge, `s1_s2_of_invariants`,
  derives them from three state invariants.
- `execute()` is two steps. Its invocation and response are separate events, and the thunk's own steps
  (on other memory) are omitted. The `isDone` register is set by the response.
- Algorithm 1: each descriptor has a unique owner `own : D → P`. `TryLock(δ)` may be repeated only while
  no earlier call returned `True`. Invocation = the `C.FAI()` step, response = the `isDone` read.
  Line 6 with coin `false` is a step without memory access, separate from line 1. This gives the
  adversary strictly more power, so our bounds apply to the paper's model.
- Randomness of Algorithm 1: `coinP` gives probability `ε(b) = 1/(7 b log₂²(b+1))` to write. The
  adversary is weak adaptive: `σ : List Cfg → Act` sees the whole history, including all past coins
  and local states, but not the coin of the step it schedules. Probabilities are finite-horizon values
  (`prob`, `AdaptiveProb.lean`). "Fails within `n` steps" is bounded for every `n` and every `σ`,
  which bounds the infinite execution.
- Algorithms 2 and 3 (safety only): random indices, levels and write decisions are adversarial, a
  sound over-approximation for safety. `abort` is an adversary action (Algorithm 2).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| (S1), (S2) as properties of executions | `S1`, `S2`, `s1_s2_of_invariants` | `Trace.lean` |
| Observation 4.1, Observation 4.2 | `obs_4_1`, `obs_4_2` | `Alg1Safety.lean` |
| Lemma 4.3 (state form) | `lemma_4_3`, invariant `Inv` (`f4`, `o1`–`o4`) | `Alg1Safety.lean`, `Alg1Inv.lean` |
| Lemma 4.5 (state form) | `lemma_4_5` (`Inv.g1`–`g3`) | `Alg1Safety.lean` |
| Theorem 4.4 (Algorithm 1 satisfies (S1), (S2)) | `theorem_4_4` | `Alg1Safety.lean` |
| Observation 4.6, Corollary 4.7 | `Inv.k1`, `Inv.k2`, `Sig_le` | `Alg1Inv.lean`, `Alg1Prob.lean` |
| `Σ_i 1/(7 i log²(i+1)) ≤ 1/2` | `sum_eps_le_half`, `sum_eps_le_half_of_rank` | `Series.lean` |
| Lemma 4.8 | `lemma_4_8` | `Alg1Prob.lean` |
| Theorem 4.9 | `theorem_4_9` | `Alg1Prob.lean` |
| Observation 4.10, Lemmas 4.11–4.13 | `obs_4_10`, `lemma_4_11`, `lemma_4_12`, `lemma_4_13` | `Alg2.lean` |
| Lemmas 4.14, 4.15 ((S1), (S2) for Algorithm 2) | `alg2_safety`, `lemma_4_15` | `Alg2.lean` |
| Lemmas 4.31, 4.32, Corollary 4.33, Lemma 4.34 | `lemma_4_31`, `lemma_4_32`, `alg3_safety`, `lemma_4_34`, `alg3_resp_true` | `Alg3.lean` |

`theorem_4_9` holds for any finite set `S` containing all processes with a pending call right after
the invocation, so `|S|` can be the point contention `k`. For every adversary and horizon, the call
returns `False` with probability `≤ 1 − 1/(14 |S| log₂²(|S|+1))`. Lemma 4.3 is not proved by the
paper's induction over promotions but by one inductive invariant (`Inv`, 37 clauses, preserved by every
step: `inv_step`). The invariant also records the "stale helper" facts (`ij`, `ik`) needed when a
process promotes a descriptor it read long ago.

**Not formalized.** Theorems 4.18 and 4.37 (expected step complexity of Algorithms 2 and 3, with
Lemmas 4.16–4.30, 4.35–4.58). Also not formalized: the derived `O(κ log² κ)` expected steps of repeated
`TryLock` calls, and the probability of success itself, as opposed to the bound on the failure
probability.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity is checked by `decide` on concrete executions. For Algorithm 1 (one process),
a write gets the thunk executed and `TryLock` returns `True`, and no write makes it return `False`
(`Alg1Examples.lean`). Algorithms 2 and 3 each have a solo `Lock` that executes its thunk. The model
is self-contained: no CSLib shared-memory module fits thunks executed by helpers.
`AdaptiveProb.lean` (`prob`, `prob_le_of_super`) is a CSLib candidate.
