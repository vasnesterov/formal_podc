# The k-Bakery — PODC 2010

Robert Danek. *The k-Bakery: Local-Spin k-Exclusion Using Non-atomic Reads and Writes.* PODC 2010.
DOI [10.1145/1835698.1835707](https://doi.org/10.1145/1835698.1835707). Formalized version: the author's
9-page copy (no arXiv version); the proofs the paper omits (Theorem 9, the CC part of Lemma 7, Theorem 10)
are taken from Danek's PhD thesis (Toronto, 2010, Chapter 5: Figures 5.3, 5.5, 5.6, Theorems 5.9, 5.20,
5.33). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ Intent lost.** The non-atomic algorithm of Figure 3 — the variant named in the
title — violates k-exclusion: with safe registers, 3 processes and `k = 1`, two processes end up in the
critical section together (`NonAtomic.counterexample`), and no repair is proved. The two algorithms for
atomic reads and writes are correct: Theorems 8 and 9 (k-exclusion, starvation freedom with up to `k − 1`
crashes, k-FCFS, FIFE, `Θ(N)` RMRs per passage in the DSM and CC models) are fully proved.

## Mistakes in the paper

### ❌ Theorem 10 (Figure 3, non-atomic reads and writes)
Figure 3 does not satisfy k-exclusion: for `N = 3` processes `y, p, r` and `k = 1` there is a legal
execution with safe registers after which `y` and `p` are both in the CS (`NonAtomic.counterexample`).

**Impact.** The title's claim of a k-exclusion algorithm with non-atomic reads and writes is refuted
for the paper's algorithm. The atomic results (Theorems 8 and 9) are unaffected. The thesis' Theorem 5.33 (same algorithm, Figure 5.6)
is false for the same reason.

**Details.** `Ticket` is a safe register too (the paper duplicates `Want` and `Capture`, but not
`Ticket`), so a read of `Ticket[r]` that overlaps a write of `r` may return any value, even `0`.
Line 44 keeps an old capture value `Capture[r][p]`, written in an earlier passage of `r`, until `p`'s
ticket catches up with it. The execution (246 steps):
1. `y` starts its first passage and begins writing `Ticket[y] := 1`; meanwhile `r` chooses its ticket,
   its read of `Ticket[y]` returns `100`, so `r` gets ticket `101`.
2. `y` (ticket 1) goes through the CS and leaves. Then `r` goes through the CS; at line 45 it
   captures `y` and `p` with `Capture[r][·] := 101`.
3. `r` starts a second passage and stops in the middle of writing `Ticket[r] := 102`.
4. `y` starts its second passage; its read of `Ticket[r]` returns `0`, so `y` gets ticket `2` and
   enters the CS (all announcements it sees are larger).
5. `p` starts its first passage; its read of `Ticket[r]` returns `0`, so `p` gets ticket `3`. `p`
   cannot remove `y` (whose pair `(2, y)` is smaller), but it reads the stale `Capture[r][p] = 101 > 3`,
   leaves the loop as captured, and enters the CS too.

The thesis' proof breaks at Lemma 5.21 ("if `Cp → Cq` then `tp < tq`"): "the value that `q` reads
from `Ticket[p]` is no smaller than `tp`" fails when `p` is rewriting `Ticket[p]` in a later passage
(step 4–5: `C_r → C_p` but `t_p = 3 < t_r = 101`). Lemma 5.24 then allows a capture by a stale value,
and the induction of Lemma 5.25 ("`r` was CS-qualified earlier, so `r` violates the lemma earlier")
no longer applies, because the processes that block `p` started their passages after `r`'s passage.

*Scope.* The counterexample uses one particular legal schedule, `foreach` loops in increasing index
order (the paper leaves the order open), and the safe-register semantics the paper states ("if a
non-atomic read and write access the same variable concurrently, then the read returns an arbitrary
value"). It does not depend on crashes.

**Repair.** Not formalized. Making `Ticket` an atomic or at least a regular register (a read
overlapping a write returns the old or the new value) restores Lemma 5.21, since tickets only grow;
whether the rest of the thesis' proof then goes through was not checked.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory, `N` processes of a finite linearly ordered type `P` (ids break ticket
  ties). Figure 2 is one transition system with a flag `fife`: `false` is the unshaded algorithm
  (Theorem 8), `true` the full algorithm (Theorem 9). One shared access per step; the program counter
  carries the local variables. The adversary schedules processes and picks the next index of every
  `foreach` (any order).
- Crash failures: a process crashes iff it takes finitely many steps and stops outside the NCS; a
  process resting in the NCS forever is not faulty; a scheduled process in the CS leaves it (so "the
  CS is finite" for non-faulty processes). No fairness assumption beyond this.
- Executions are infinite schedules (every process always has an enabled step); safety is also proved
  for all reachable configurations. Deterministic algorithm, no randomness.
- RMRs: DSM with `Ticket[p]`, `Want[i][p]`, `Capture[i][p]` in `p`'s module; CC write-through /
  write-invalidate caches (`cached`), reads miss iff no valid copy, every write is an RMR and
  invalidates the other copies.
- Figure 3: separate model (`NonAtomic.lean`) with safe registers: writes take two steps (begin,
  end), a read overlapping a write returns an adversary-chosen value. This is a sub-model of the
  paper's interval semantics, so its executions are legal executions of the paper's model.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1, Corollary 2, Lemma 3 (as invariants) | `Inv`, `inv_step`, `safe_of_wantGood`, `s1_step` | `Defs.lean`, `Invariant.lean` |
| Lemma 4 (k-exclusion; thesis Lemma 5.15 for FIFE) | `k_exclusion`, `card_qual_le_of_inv` | `Exclusion.lean` |
| Lemma 5 (starvation freedom) | `starvation_freedom` | `Liveness.lean` |
| Lemma 6 (k-FCFS) | `k_fcfs` | `FCFS.lean` |
| Lemma 7, DSM | `rmr_dsm_eq`, `rmr_dsm_le`, `rmr_dsm_complete` | `RMRDSM.lean` |
| Lemma 7, CC (thesis Lemmas 5.7, 5.8, 5.17–5.19) | `rmr_cc_le`, `rmr_cc_complete_ge` | `RMRCC.lean` |
| Theorem 8 | `theorem_8` | `Main.lean` |
| FIFE (thesis Lemma 5.16) | `fife` | `Fife.lean` |
| Theorem 9 | `theorem_9` | `Main.lean` |
| Theorem 10 (refuted) | `NonAtomic.counterexample` | `NonAtomic.lean` |
| non-vacuity | `rrRun_enters_cs` | `NonVacuity.lean` |

**Proof remarks.** The proofs replace the paper's interval reasoning (`→`, `⇢`) by inductive
invariants. `Safe s q v r` says that `q` cannot get priority over the pair `(v, r)` before its next
ticket; the set `U s v r` of unsafe processes only shrinks while `v ≤ Ticket[r]`. A process past its
loop has fewer than `k` unsafe processes: either its predecessor set is small, or it was captured with
a pair `(v, r)` whose own unsafe set is small (`card_U_le_of_capture`). This also replaces the thesis'
induction on qualification times (Lemmas 5.13–5.14). Starvation freedom follows the paper's
minimal-ticket argument. The paper's sketch skips processes that leave and re-enter; these are
handled by a measure argument (`reach_good`). The CC bound is an amortized potential argument. While
`p` waits, `q` has at most 4 more writes to `Want[q][p]` and at most 2 more to `Capture[q][p]` before
these are good for `p` forever (`Bw`, `Bc`). This gives the thesis' "5 RMRs per `Want[q][p]`, 3 per
`Capture[q][p]`".

Explicit constants: per passage, DSM exactly `4(N − 1)` / `5(N − 1)` RMRs (unshaded / full algorithm),
CC at most `9N − 6` / `13N − 6` and at least `3N − 1`; FIFE within `4N + 7` own steps after `q` is in
the CS.

**Not formalized.** The rest of Theorem 10 (starvation freedom, FIFE, `Θ(N)` RMRs for Figure 3) was not
examined, as k-exclusion already fails. The scenarios of Section 5 (Figure 2 unshaded violates FIFE) and
Section 6 (Figure 2 is incorrect with non-atomic registers); Table 1; the CC write-back variant; the
ticket-resetting algorithms of the thesis.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The counterexample is checked by kernel evaluation (`decide +kernel`, no
`native_decide`). Non-vacuity: in the round-robin execution every process enters the CS
(`rrRun_enters_cs`). The model is paper-local (no CSLib model of RMRs or crash-prone mutual
exclusion fits); it imports only Mathlib. CSLib candidates: `exists_good_of_measure` (`Progress.lean`),
`sum_cost_le` (`RMRCC.lean`).
