# Group Mutual Exclusion in O(log n) RMR — PODC 2010

Vibhor Bhatt, Chien-Chung Huang. *Group Mutual Exclusion in O(log n) RMR.* PODC 2010. DOI
[10.1145/1835698.1835708](https://doi.org/10.1145/1835698.1835708). Formalized version: the authors' copy of the
PODC'10 paper (10 pages, https://www.di.ens.fr/~cchuang/work/gmx.pdf); no full version exists (the paper defers the
proof of P5' "to the full version" and gives its Invariants 1–8 "without their formal proofs"). Numbering follows
it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ Intent lost.** The final algorithm (Figure 3) is not a correct GME algorithm in the claimed sense:
it **deadlocks** — two processes and two sessions suffice for a fair execution in which a process waits at line 8
forever although nobody else is active — and its RMR cost per attempt is **unbounded** (four processes), so
Theorem 1's starvation freedom (P2) and its O(min(log n, k)) RMR bound both fail. Mutual exclusion (P1) and
bounded exit (P3) do hold; P1 needed a new inductive invariant of about thirty clauses, since the paper's
Invariants 1–8 are unproved and partly false.

## Mistakes in the paper

### ❌ Theorem 1 / Lemma 3 (starvation freedom, P2)
The algorithm deadlocks: with two processes and two sessions there is a fair execution in which `p₁` waits at
line 8 forever while `p₀` stays in the remainder section and nobody is in the CS (`starvationFree_false`).

**Impact.** P2, the basic liveness property of every exclusion algorithm, fails for the paper's final algorithm;
with it fall Lemma 3, Claim 3 (`claim3_false`), concurrent entering in the paper's own formulation (Lemma 2,
`concurrentEnteringPaper_false`) and Invariant 8 (`invariant8_false`), on which the proofs of Lemmas 2 and 3
rest. We did not find (or prove) a repaired algorithm.

**Details.** Sessions 0 and 1, `S = (0,0,0)` initially (`deadSched`, `deadCfg` in `Deadlock.lean`):
1. `p₀` (session 0) joins side 0, enters and leaves the CS and stops in Promote-Exit after line 16.5 (after its
   `LL(Ex)` at line 16.3), still counted in `C[0,0]`.
2. `p₁` (session 0) also joins side 0, passes line 8 (`Out[0] = 0`), finds `Ex = false` at line 9 and performs a
   *successful* `SC(Ex, false)` at line 10 — which kills `p₀`'s link on `Ex`. In its exit it sees
   `C[0,0] = 1` (because of `p₀`) at line 16.8 and leaves without promoting anybody.
3. `p₁` starts a new attempt with session 1 (side 1). Promote-Try sees `C[0,0] = 1` and does nothing; `p₁`
   waits at line 8 for `Out[1] = 1`.
4. `p₀` finishes: `C[0,0] = 0`, `Min(Q) = (1,1)`, but its `SC(Ex, 0)` at line 16.9 fails (step 2), so it returns
   to the remainder section without switching `S`.

Now `S = (0,0,0)`, `Out[1] = 0`, and nobody will ever write `Out[1]`. The proof of Claim 4 treats the case "the
successful SC [on `Ex`] was performed by some process at Line 10" as happening after `q[16.6]`; here it happens
between `q[16.3]` and `q[16.6]`, by a fellow process of `q` that is the actual reason why `q` is the last of its
side. The mechanism of lines 9–10 (invalidating lingering exiters) thus also disables the exiter that is
responsible for the next switch. Line 10 is not essential: `p₁`'s own *successful* `SC(Ex, false)` at line 16.2
(after its `LL(Ex)` at 16.1) also falls between `q[16.3]` and `q[16.9]` and would kill `p₀`'s link just as well;
the paper's sentence "If q fails at Line 16.9 then … some process performed a successful SC on `Ex` since `q[16.6]`"
should read "since `q[16.3]`", and the window `(q[16.3], q[16.6])` is not covered. (Under the stricter, Hadzilacos-style reading of concurrent entering — no
conflicting process during the whole attempt — our model checker found no violation; the paper's Lemma 2 and
Claim 3 use the weaker "no conflicting process active at time `t`".)

### ❌ Theorem 1 / Lemma 5 (RMR complexity O(min(log n, k)))
With `n = 4` processes and two sessions, a single attempt can incur any number of remote memory references at
line 8 (`rmr_unbounded`, `not_bounded_rmr`).

**Impact.** The headline complexity claim of the paper (and of its title) fails for the printed algorithm: no
bound in terms of `n` holds at all. A plausible repair (writing `Out[s]` at line 7 only when it differs) was not
checked.

**Details.** Lemma 5 argues that the busy-waiting loops cost 2 RMRs "by Claims 6 and 8", i.e. because `Out[s]`
does not change once it equals `p`'s side. But line 7 rewrites `Out[s]` (with the *other* side) every time a
fellow process finds `S = (s, d̄, s)`, and in the CC model every such write invalidates the waiting process's
cached copy. Execution (`RMR.lean`): `r` (session 0) takes time-stamp 1 and pauses before enqueuing; `q`
(session 1, time-stamp 2) and `p` (session 0, side 1, time-stamp 3) wait at line 8; `r` enqueues, writes
`Out[0] ← 0` at line 7 and stays in the CS. Then, round after round, `f` (session 0) joins side 0 via lines 1.4–1.6
(`Min(Q)` is `r`'s element), writes `Out[0] ← 0` at line 7, passes the CS and leaves without flipping `In[0]` or
promoting; after each round `p`'s re-read of `Out[0]` is remote. The rounds leave the configuration unchanged
except for `G`, so `K` rounds give `K` remote reads in one attempt of `p`; `rmr_completes` checks for `K = 3` that
the attempt then completes (`r` leaves, `q` runs, `p` enters the CS).

### ❌ Invariant 8 and Claim 3
Both are false (`invariant8_false`, `claim3_false`): in the deadlocked configuration of the first item, `p₁` is at
line 8 with `Min(Q) = (1,1)`, `S = (0,0,0)`, `C[0,0] = 0`, no process of session 0 active, and `Out[1] ≠ 1`.

**Impact.** These are the steps of the proofs of Lemmas 2 and 3 that fail; see the first item.

### ✏️ Slips
- Invariant 1 ("no process of session `s` and side `d` active ⇒ `C[s,d] = 0`") is false for processes at lines
  1.2–1.3, which are counted but have no side yet. We use the exact count (`Inv.gC`).
- Invariant 6 requires the exiting winner to be at lines 16.10–16.13; it may be at 16.14 (with `Exclear[s]` still
  `false`). Our clause `win` uses 16.10–16.14.
- Invariant 7 is false as stated (a process in `LE` at line 16.9 may find `S` already switched by Promote-Try); it
  holds when the process is also in `LS` (`LI.e1`, `LI.e2`).

## Proof gaps (statements true)

### 🛠️ Theorem 1 (mutual exclusion, P1)
"Mutual exclusion (P1) follows easily from Invariant 5", but Invariant 5 is not proved and is far from inductive:
it depends on the time-stamp order (it fails if `Min(Q)` may return any element of `Q`, as our model checker
shows), on the `Ex`/`Exclear` protocol of Promote-Exit, and on Invariants 2–4.

**Impact.** Statement true for every number of processes and sessions; proved with a new inductive invariant
(`mutual_exclusion`, with Invariant 5 `invariant5` and Invariant 3 `invariant3` as by-products).

**Details.** `Inv` (`Inv.lean`) has 7 global and 26 per-process clauses: exact counters, the queue, the relation
`In[s] ≠ Out[s]` unless `S` is of session `s` with side `Out[s]` (`g4`), who may hold `In[s] = S.2.1` (`g5`), all
waiting processes of a session not in `S` are on side `In[s]` (`g7`), Lemma 1 with time-stamps (`l1`), the facts
remembered by a process holding a valid `LL` on `S` or `Ex` (`a1`–`a3`, `e1`–`e3`, `x1`–`x3`), the pending writes
of `Out` (`p5`, `p11`, `p13`, `g8`), and the `Ex` "winner" protocol (`w1`–`w5`, `win`, `winS`). It was found and
checked with an explicit-state model checker before the Lean proof.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** Asynchronous shared memory, `n` processes (`Fin n`), sessions of an arbitrary type `J` (finite or not);
no crashes outside the remainder section. Each numbered line of Figure 3 is one atomic step (line 1.8 is merged
with 1.7, the CS is one step). `G`, `C[s,d]` and the priority process-queue `Q` are atomic objects (the paper's
Theorems 2–3 provide linearizable implementations); `Q` is one slot per process and `Min(Q)` returns the element
with least `(tm, p)`. LL/SC on `S` and `Ex`: per-process link bits, cleared by every successful SC. A process in
the remainder section starting an attempt chooses its session (adversary). Fairness for P2: every process takes
infinitely many steps or stays in the remainder section from some time on. RMRs: the write-invalidate CC model,
restricted to the reads of `Out` at line 8 (a lower bound).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Figure 3 | `Cfg.step`, `run`, `Reachable` | `Model.lean` |
| Theorem 1 (P1) | `mutual_exclusion` | `Safety.lean` |
| Invariant 5, Invariant 3 | `invariant5`, `invariant3` | `Safety.lean` |
| Theorem 1 (P3) | `bounded_exit` | `BoundedExit.lean` |
| Theorem 1 (P2), Lemma 3 — false | `starvationFree_false` | `Deadlock.lean` |
| Lemma 2 (P4, paper's form), Claim 3 — false | `concurrentEnteringPaper_false`, `claim3_false` | `Deadlock.lean` |
| Invariant 8 — false | `invariant8_false` | `Deadlock.lean` |
| Theorem 1 / Lemma 5 (RMR) — false | `rmr_unbounded`, `not_bounded_rmr` | `RMR.lean` |
| the invariant for P1 | `Inv`, `Inv.step`, `Reachable.inv` | `Inv.lean`, `Safety.lean` |

**Not formalized.** P5' (relaxed FCFS; no proof in the paper), P6 (pulling, Lemma 4), concurrent entering in the
strict sense, and the f-array constructions of Theorems 2–3. Our model checker found no violation of P6 (random
runs, 3–4 processes) or of strict concurrent entering (exhaustive, 2 processes).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
counterexamples are concrete executions evaluated by `decide +kernel`. The model is paper-local.
