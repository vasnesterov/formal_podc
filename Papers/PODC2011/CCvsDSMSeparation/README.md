# CC vs. DSM complexity separation — PODC 2011

Wojciech Golab. *A complexity separation between the cache-coherent and distributed shared memory
models.* PODC 2011. DOI [10.1145/1993806.1993822](https://doi.org/10.1145/1993806.1993822).
Formalized version: arXiv [1109.5153](https://arxiv.org/abs/1109.5153) v1 (full version; numbering
follows it).

**Verdict: ⚠️ Minor statement issues.** The main result holds: the signaling problem has an
`O(1)` RMR solution in the CC model (Section 5), but no deterministic terminating read/write
solution with `O(1)` *amortized* RMR complexity in the DSM model (Theorem 6.2). We proved both,
and the separation, in Lean. Corollary 6.14 is false as literally stated, because it drops the word
"terminating"; its own proof assumes it. The proof of Lemma 6.10 has a genuine gap: the regularity
invariant is not preserved. We repaired it with a weaker invariant.

## Mistakes in the paper

### ⚠️ Corollary 6.14 (omits "terminating")
Corollary 6.14 claims the DSM lower bound for "any deterministic algorithm", but without
termination it fails: an algorithm whose `Poll()` busy-waits forever on the caller's own module
solves the problem with no RMRs at all (`corollary_6_14_needs_terminating`).

**Impact.** Typo-level with evident intent: the corollary's own proof starts from "some
deterministic *terminating* algorithm", and the fix is one word. Theorem 6.2 is unaffected.

**Details.** The corollary covers "any deterministic algorithm" using reads, writes and CAS or
LL/SC. In the counterexample `Poll()` busy-waits forever on a variable in the caller's own module
and `Signal()` returns at once. Specification 4.1 only constrains calls that return, so this
algorithm solves the problem, yet no execution has an RMR in the DSM model. The algorithm uses only
reads, so it is also a "reads, writes, and CAS" algorithm.

### ⚠️ Lemma 6.10 (regularity invariant, Definition 6.6 condition 3)
The construction in the proof of Lemma 6.10 does not preserve condition 3 of regularity (the last
of several writers of a variable is finished), so Lemma 6.10 as stated is unestablished: neither
proved nor refuted here.

**Impact.** Theorem 6.2 is unaffected: a variant of Lemma 6.10 with a weaker invariant (`SoleW`) is
proved and is all that Theorem 6.2 needs (`Algorithm.lemma_6_10`).

**Details.** Condition 3 requires: if a variable `v` has several writers and the last one is `p`,
then `p` is finished. In the erasing case, the paper removes conflicts only with variables "already
written by *active* processes". A kept unstable process may still write a variable previously
written by a *finished* process. Example: a rolled-forward process `r` wrote a shared flag `G`, and
in a later round an unstable process writes `G` as its next RMR. The result violates condition 3.
Finished processes cannot be erased, and such writers need not be a constant fraction, so erasing
them is not an option either. Under condition 3 the claim "for each process we add at most one
edge" is also wrong. A variable whose last writer is finished may have many active earlier writers
(the processes left behind by a roll-forward), and a new write to it conflicts with all of them.

**Repair.** We replace condition 3 by a weaker one: after erasing the (active) last writer of `v`,
the last writer of `v` is not active (`SoleW`). This condition is preserved by every step of the
construction. It gives out-degree ≤ 1 for the write conflicts (≤ 2 together with touching). It is
all that Lemma 6.13 and the roll-forward need: erasing active processes reverts every variable to a
value written by a finished process (`SoleW.erase_writer_not_mem`, `Algorithm.round`).

### Typos and slips
- Proof of Lemma 6.10: "`|Fin(H_{i+1})| ≤ |Fin(H_i)| + 1 ≤ i`" should end with `i + 1`.
- Proof of Lemma 6.12: "erase all active processes except `⌊N^{1/3^c}/2⌋` unstable ones" should
  say *stable*.
- Lemma 6.13: "at most `k` processes participate in `H`" should be `H′` (twice).

## Proof gaps (statements true)

### 🛠️ Lemma 6.13 (termination and disjointness)
Two steps lack a justification: termination is applied to histories that are not fair, and "`s`
performs one such RMR for each stable process" needs an unstated disjointness.

**Impact.** Statement true; repaired (`Algorithm.final_stable`).

**Details.**
- (a) Stable processes "complete any pending call to `Poll()`", and `s`'s `Signal()` "must
  eventually terminate". The histories in question are not fair, because the other active
  processes are stopped in mid-call, so termination does not apply directly.
- (b) "`s` performs one such RMR for each stable process" needs the sets "`p`'s module ∪ variables
  last written by `p`" to be pairwise disjoint over the stable processes `p`. This follows from
  conditions 2 and 3 of regularity, but the paper does not say so. Also, `s` must be chosen outside
  `Par(H)`, which the paper's choice "a process whose module is not written" does not guarantee.

**Repair.** Our proof runs `s` solo in the history where *all* stable processes are erased: there
every other participant has terminated. It never needs the pending polls. We prove: for each stable
`p`, `s`'s solo `Signal()` accesses `p`'s module or a variable last written by `p`. Otherwise `p`'s
next `Poll()` would return `true` after a run without any signal (`Algorithm.final_stable`).

### 🛠️ Theorem 6.2 (the constant `k`)
The theorem promises a *constant* `k`, but in the branch of the proof that goes through Lemma 6.11
the paper's `k = c + ⌊N^{1/3^c}/2⌋` is not constant.

**Impact.** Statement true; using only `c² + 1` unstable processes there gives `k ≤ c² + c + 1` in
every branch (`theorem_6_2`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory with `N` processes `Fin N`, deterministic programs and atomic reads
  and writes of variables `V`. `Algorithm` has the shape of `Cslib.SharedMemory.Impl` specialised
  to registers. Each variable lives in one process' module (`home`, the DSM placement chosen by
  the algorithm).
* An execution is a list of events that record what each step did: invocation, read with the
  value read, write, or return. `Valid` means every event is a legal step of its process and every
  read returns the last written value. Recording the accessed variables and values makes the
  erasing argument (Lemma 6.7) a statement about filtering a list (`Algorithm.valid_erase`).
* There are no crashes. A process that stops in mid-call is a prefix; a process that terminates
  stays idle forever. Which call an idle process makes next is chosen by the environment.
* DSM RMR: an access to a variable outside the process' own module (`rmr`). CC RMR: the paper's
  loose definition (`ccRMR`). A read is free if the process read the variable before and no other
  process has written it since; every other access costs one.
* Specification 4.1 is required only in executions with at most one call to `Signal()` (one
  signaler). Waiters may stop after any number of polls. Participants are processes with at least
  one event, invocations included. Both choices make the lower bound stronger.
* Termination follows Section 2: in every fair infinite history every call completes
  (`Algorithm.Terminating`). The proof uses only a weaker solo form (`SoloTerminating`), which we
  derive from it.
* The lower bound is existential over executions: the adversary chooses the schedule and which
  procedures are called.
* Theorem 6.2's quantifiers are implicit (standard asymptotic convention; not counted as a
  mistake). The statement fixes `A` (hence `N`) and quantifies "for any constant `c`". For a fixed
  `N` the claim is false: a signaler that writes all `N` per-process flags makes at most `N − 1`
  RMRs per history, so `c = N` violates it (easy example, not formalized). The intended reading is
  the standard one: `c` is independent of `N`, and the claim holds for all `N ≥ N₀(c)`. The proof
  says "if `N` is large enough", and we formalize exactly that.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Section 5 (CC algorithm: correct, terminating, `O(1)` RMRs per process) | `section_5` (`ccAlg_solves`, `ccAlg_terminating`, `ccAlg_ccRMROf_le`) | `Main.lean`, `UpperBoundCC.lean`, `CCTerminating.lean` |
| Theorem 6.2 (no `O(1)` amortized DSM solution; `k ≤ c² + c + 1`) | `theorem_6_2_terminating` (from `theorem_6_2`) | `Main.lean`, `LowerBound.lean` |
| Separation CC vs. DSM (abstract, §1) | `separation` | `Main.lean` |
| Lemma 6.7 (erasing) | `Algorithm.valid_erase` | `Trace.lean` |
| Lemma 6.10 (variant: weaker regularity `SoleW`, our constants) | `Algorithm.lemma_6_10`, one round: `Algorithm.round` | `LowerBound.lean`, `Round.lean` |
| Lemma 6.11 (variant: < `5(c²+1)` unstable processes) | `Algorithm.final_unstable` | `LowerBound.lean` |
| Lemmas 6.12–6.13 (variant: < `c(c+1)+1` stable processes) | `Algorithm.final_stable` | `LowerBound.lean` |
| Corollary 6.14 as stated (without "terminating"): **false** | `corollary_6_14_needs_terminating` | `NonTerminating.lean` |
| "terminating" (Section 2) ⇒ solo termination | `Algorithm.Terminating.soloTerminating` | `Terminating.lean` |

**Not formalized.** Corollary 6.14 with "terminating" restored: it reduces CAS and LL/SC to reads
and writes through the locally-accessible implementations of [11, 12]. Also not formalized: the
variants of Section 7, blocking semantics, and the discussion of Section 8.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: the Section 5 algorithm satisfies both hypotheses of Theorem 6.2
(`Terminating` and `Solves`; `example` in `Main.lean`). The model is paper-local
(`Model.lean`, `Trace.lean`, `Regular.lean`). The counting lemmas (an independent set in a digraph
of bounded out-degree; fiber vs. image) are staged as a CSLib candidate in
`Podc/Foundations/Combinatorics/OutDegreeIndep.lean`.
