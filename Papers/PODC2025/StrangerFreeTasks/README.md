# Stranger-Free Tasks — PODC 2025

Eli Gafni, Giuliano Losa, Michel Raynal, Gadi Taubenfeld. *Brief Announcement: Stranger-Free Tasks.* PODC 2025.
DOI [10.1145/3732772.3733545](https://doi.org/10.1145/3732772.3733545). Formalized version: the brief announcement
(no full version used).

**Verdict: ❌ False claim.** Theorem 2.1 (a stranger-free task for `n` processes needs `n` registers) and the lower
bound of Theorem 3.1 (`k`-bounded lattice agreement needs `k + 1` registers) are proved. **The upper bound of
Theorem 3.1 fails: Algorithm 1 is not wait-free for any `k ≥ 2`**, already with two processes. It is safe and
obstruction-free for every `k`, and wait-free for `k = 1`. So the claimed wait-free hierarchy is established only
in the obstruction-free sense (and for `k = 1`).

## Mistakes in the paper

1. **Algorithm 1 is not wait-free for `k ≥ 2` (false claim).** §3.1 argues that "processes that keep
   interfering have seen sets that converge to the same value or eventually grow in cardinality past `k`".
   Counterexample with two processes `a`, `b` and `k = 2`, so `|seen| = 2 ≤ k` never triggers the early exit at
   line 23. Once both have `seen = {a, b}`, repeat forever: `a` does its first collect; `b` writes; `a`'s second
   collect fails because `b`'s triple changed; `b` does its first collect; `a` writes; `b`'s second collect
   fails. Both processes take infinitely many steps in a one-shot execution and never output. Converging `seen`
   sets do not help: without helping, the double collects keep invalidating each other, as in the double-collect
   scan of Afek et al., which is only obstruction-free. The livelock does not depend on how line 21 is read.
   Replacing `> k` by `≥ k` in line 23 would only repair `k = 2`. Consequently the wait-free upper bound of
   Theorem 3.1 (`k + 1` registers, unboundedly many processes) and the wait-free "infinite hierarchy" of the
   abstract are **not established for `k ≥ 2`**; whether they hold remains open
   (`exists_livelock`, `theorem_3_1_alg1_not_waitFree`).
   For `k = 1` the claim is true, but the paper's sketch does not apply. Our argument: a process other than `p`
   can write `A[2]` (the second register; `A[1]` in the 0-based Lean code) only as its second write, and only if
   it read `⊥` there before anybody wrote it. So only finitely many interfering writes on `A[2]` exist, while
   every two failed iterations of `p` need one
   (`theorem_3_1_k1`).
2. **Safety argument of §3.1: gap, true claim.** The argument ("unless at least `k + 1` processes participate,
   the set will always be a subset of at least one register … `k` processes are not enough to obliterate all
   `k + 1` registers") covers only runs with few participants. With more than `k + 1` participants, `k + 1`
   processes poised on distinct registers can overwrite everything after a successful snapshot, and the paper
   does not say why containment then still holds. It does hold, by a counting argument over "clean" writes. A clean write by a process that has completed a
   collect since all registers became dirty carries a seen-set of size `≥ k + 1`, and each process makes at most
   one write without such a collect. So if all registers become clean, the union of their seen-sets is too large for a
   later output of size `≤ k` (`card_union_of_obliterate`, `alg1_solves`).
3. **§3.2, step omitted as routine.** The claim that `k`-bounded lattice agreement for `k + 1` processes is
   stranger-free needs "`j` in `i`'s output ⇒ `j` appears in `i`'s view". This takes a causal-erasure argument:
   erase `j`'s causal future to obtain an execution without `j` in which `i` outputs the same set. The claim
   holds (`boundedLA_strangerFree`).
4. **Unstated hypothesis.** The obstruction-free variant of Theorem 2.1 (remark after its proof) needs
   stranger-freedom with respect to *obstruction-free* algorithms, a stronger hypothesis. It holds for
   `k`-bounded lattice agreement. Line 21 of Algorithm 1 (`seen ∪ collect[j][3]`) is a no-op as written,
   probably a typo for `A[j][3]`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (CSLib `Cslib.SharedMemory`).
- Asynchronous shared memory, deterministic processes, arbitrary interleavings. Atomic multi-writer multi-reader
  registers (any value type), one register access per step. No crashes: a process may simply stop taking steps.
  Wait-freedom and obstruction-freedom as usual, on infinite executions and solo runs.
- Process type: finite with `|P| = n` for Theorem 2.1 and the lower bound; arbitrary (possibly infinite) for
  Algorithm 1.
- One-shot tasks: the input/output relation must hold on every finite one-shot execution (participating = has
  invoked). Every process may invoke with every input.
- Full-information versions store (value, writer's view) in registers. The paper's remark that an algorithm and
  its full-information version solve the same tasks with the same registers is proved. Stranger-freedom
  quantifies over the full-information versions of all algorithms solving the task.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 2.1 (`n ≤ #registers`); covering form | `theorem_2_1`, `covering_of_strangerFree` | `StrangerFree.lean` |
| Remark after Theorem 2.1 (obstruction-free) | `theorem_2_1_obstructionFree` | `StrangerFree.lean` |
| §3.2: `k`-bounded LA for `k+1` processes is stranger-free | `boundedLA_strangerFree` | `LowerBound.lean` |
| Theorem 3.1, lower bound | `theorem_3_1_lowerBound`, `boundedLA_lowerBound` | `Main.lean`, `LowerBound.lean` |
| Algorithm 1 is safe / obstruction-free (all `k`) | `alg1_solves`, `alg1_obstructionFree` | `Alg1Safety.lean`, `Alg1OF.lean` |
| Algorithm 1 is **not** wait-free (`k ≥ 2`) | `alg1_not_waitFree`, `theorem_3_1_alg1_not_waitFree` | `Alg1Livelock.lean`, `Main.lean` |
| Theorem 3.1, obstruction-free hierarchy; `k = 1` wait-free | `theorem_3_1_obstructionFree`; `theorem_3_1_k1` | `Main.lean` |
| Tightness of Theorem 2.1 for `n = 2` | `theorem_2_1_tight` | `TwoProcess.lean` |

**Not formalized.** The anonymous-memory/anonymous-process remarks at the end of §3.1 and the introduction's
discussion of related work (splitters, adopt-commit, renaming).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `theorem_2_1_tight` exhibits a stranger-free task (1-bounded LA for two processes) solved wait-free
with exactly 2 registers. The model, full-information versions and covering lemmas come from CSLib
(`Cslib/Computability/Distributed/SharedMemory/`).
