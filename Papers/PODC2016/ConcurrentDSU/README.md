# A Randomized Concurrent Algorithm for Disjoint Set Union — PODC 2016

Siddhartha V. Jayanti, Robert E. Tarjan. *A Randomized Concurrent Algorithm for Disjoint Set Union.*
PODC 2016. DOI [10.1145/2933057.2933108](https://doi.org/10.1145/2933057.2933108). Formalized version:
arXiv [1612.01514](https://arxiv.org/abs/1612.01514) v1 (the only version; a revised version of the
conference paper). Numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Proof repaired (correctness part only; work bounds not checked).** We verified
the correctness theorem, Theorem 3.4: `SameSet`/`Unite` with CAS-based linking by node id is
linearizable and wait-free with each of the three versions of `Find` (no compaction, one-try and
two-try splitting), for every fixed order of the ids, and so are the early-termination variants of
Section 6. The proofs in Section 3 have small gaps, all easy to fill. The work bounds (Sections 4–5),
the paper's headline efficiency result, are not formalized. For one-try splitting the PODC version
claims the work bound of Theorem 5.1 with a proof that the authors themselves later called incorrect;
the claim is open. We found a proof gap in Lemma 4.2, which the proof of Theorem 5.1 inherits; it
can be fixed on paper by changing constants, but this repair is not checked in Lean.

## Mistakes in the paper

No mistakes in the statements we checked (correctness, Sections 3 and 6).

Not checked by us: the PODC version claims the expected work bound `O(m(α(n, m/(np)) + log(np/m + 1)))` (Theorem
5.1 of the arXiv version, stated in the PODC abstract) also for one-try splitting, and the authors later
acknowledged that its proof is incorrect. The arXiv version says: "In the conference version of our paper [JT16],
we claimed that Theorem 5.1 holds for one-try splitting, but our proof, essentially the proof of Theorem 5.1, is
not correct for this algorithm." It proves only a weaker bound (Theorem 5.2, `m/(np²)` in place of `m/(np)`) and
calls the original claim "an open problem" (Section 7). We could not consult the proceedings text and do not
formalize Sections 4–5, so we neither confirm nor refute the claim.

### Typos and slips
- Algorithm 4, line 7: `u.p` should be `u.parent`.
- Proof of Lemma 4.1: "rank … never less than the rank of its parent" should be "never more".
- Proof of Lemma 4.2: "fewer than h bad links" should be "good links".
- Proof of Theorem 5.1: the two exponents `h²/16` and `h²/4` are inconsistent.
- Proof of Lemma 5.3: "depth 1 before the Find" should be "depth 2".

## Proof gaps (statements true)

### 🛠️ Lemma 4.2 (exponent `h²`, checked in the arXiv text)
The proof claims the bound `exp(−(c/2−1)²h²/c)` "by a Chernoff bound", but Chernoff gives only `exp(−(c/2−1)²h/c)`,
linear in `h`, and the quadratic bound already fails for fair coins with `c = 4`, `h = 6` (`chernoff_step_fails`).

**Impact.** We do not know whether the stated lemma is false; only its proof is broken. Corollary 4.2.1 and
Theorem 4.3 survive with a larger constant `c`, and Theorem 5.1 (which inherits the gap) can be repaired on paper
with another threshold; not checked in Lean.

**Details.** The proof bounds the probability that fewer than `h` of `c·h` independent links are "good", each good
with probability ≥ 1/2. Fair coins are allowed by Lemma 4.1: with `c = 4`, `h = 6`, fewer than 6 heads among 24
coins has probability `55455/2²⁴ ≈ 3.3·10⁻³ > e⁻⁹`. The case `d < 1` of the proof of Theorem 5.1 uses the
quadratic form to show that there are very few "middle" nodes. With the paper's threshold `4h` and the linear
exponent, its charge is not `O(m)`.

**Repair.** A threshold `7h` repairs the proof of Theorem 5.1 (on paper; not formalized).

### 🛠️ Lemma 3.1 ("u, v and w are distinct")
The proof's claim that `u`, `v` and `w` are distinct is false: a splitting `Find` can read `v ← u.parent = u` while
`u` is a root, and if `u` is linked before the next read, it executes `Cas(u.parent, u, w)` with `u = v`
(`cas_same_node`, a concrete 2-process execution).

**Impact.** Lemma true: this `Cas` always fails. The same execution gives a `Find` iteration in which `u` does not
advance, contrary to a sentence in the proof of Lemma 3.3; this happens at most once per `Find`.

### 🛠️ Lemma 3.2 (linearizability: two implicit facts)
The proof leaves implicit that `u` is already a root at the linearization point of a `SameSet` that returns false,
and that in the link case the larger node is not in the smaller root's tree.

**Impact.** Statement true; both facts are easy (`linearizable`).

**Details.**
- When `SameSet` returns false, the answer is decided at the later test `u = u.parent`, but the operation is
  linearized earlier, at the last read of `Find(v)`. One needs that `u` was a root already at that read: it was a
  root when `Find(u)` returned and is one at the test, and non-roots never become roots again. Linearizing at the
  test instead would be wrong, because `v` may have been linked into `u`'s tree in between.
- The link case needs that the larger node is not in the smaller root's tree. This holds because ids increase
  along parent pointers.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's asynchronous shared-memory model: any set of processes, deterministic programs, no
  crashes, an arbitrary (adversarial) scheduler. Each process runs one operation at a time, and every
  invocation is allowed.
* Each atomic step is one `read` or one `Cas` on one parent pointer (`casObject E a`, initially
  `a`). Local computation is folded into the preceding access.
* No randomness. The node ids are an arbitrary injective `key : E → ℕ`, so the random order of the
  paper is a special case. `E` is finite.
* The object is DSU over `E`. Its state is the same-set relation, initially equality. `sameSet`
  answers membership; `unite` merges the two classes and returns a dummy `true`.
* `Find` comes in three versions: Algorithm 1, two reads per iteration as written; and splitting
  with `k + 1` tries (`k = 0`: Algorithm 4, `k = 1`: Algorithm 5).
* Linearizability is CSLib's `IsLinearization`, and wait-freedom is CSLib's `Impl.WaitFree`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 3.1 (union forest: links attach a root below a node of another tree; `Find` replaces a parent by a proper ancestor of it in the union forest; ids increase along parents) | `lemma_3_1_union` (variant without union forest: `lemma_3_1`) | `UnionForest.lean`, `Main.lean` |
| Lemma 3.2 (linearizability; the statement is existence of a linearization, the proof uses the paper's linearization points; abstract state = trees) | `linearizable`, `linearizable_with_state` | `Lin.lean` |
| Lemma 3.3 (wait-freedom) | `waitFree` | `WaitFree.lean` |
| Theorem 3.4 | `theorem_3_4` | `Main.lean` |
| Section 6, Algorithms 6–7 (and the one-try variant) | `et_linearizable`, `et_waitFree` | `EarlyTerm.lean` |
| Lemma 3.1 proof, `u = v` case | `cas_same_node` | `Examples.lean` |
| Lemma 4.2 proof gap (numeric witness) | `chernoff_step_fails`, `chernoff_linear_ok` | `Lemma42.lean` |

**Proof structure.**
* *Linearizability.* An invariant over (history, configuration, linearization) says that the
  abstract state of the linearization is the partition into trees of the current memory. Responses
  of `SameSet = false` are inserted retroactively, at a cut of the linearization recorded when
  `Find(v)` found its root; this uses `IsLinearization.insert` from
  `Cslib/Computability/Distributed/SharedMemory/LinPoints.lean`.
* *Wait-freedom.* The potential is `bound · Σₐ #{ids above a.parent} + Φ`. The first term
  decreases at every successful `Cas`. `Φ` is a lexicographic local potential: positions of `u`,
  `v` (taken at their roots while a `Find` runs), then the phase, then the `Find`'s progress. It
  decreases at every own step that leaves memory unchanged (`Impl.waitFree_of_cfgPotential`,
  `Cslib/Computability/Distributed/SharedMemory/Potential.lean`).

**Not formalized.** The randomized analysis of Sections 4–5 (Lemma 4.1 relies on Goel et al.,
SODA 2014), the `O(h+1)` step bound of Lemma 3.3, and the `MakeSet` remark.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: concrete valid executions (`seqDemo_valid`: `Unite(0,1)` then
`SameSet(1,0)` returns `true`; `seqDemo_false`: `SameSet(1,0)` alone returns `false`) and
`cas_same_node`, all evaluated by `simp`. The model comes from CSLib
`Cslib/Computability/Distributed/SharedMemory/{Model,History,LinPoints}.lean`; the shared library
`Cslib/Computability/Distributed/SharedMemory/{History,Model,LinPoints,Potential}.lean` provides the current operation instance
`curOp`, `Impl.run_pend_curOp`, `Impl.linearizable_of_run`, `IsLinearization.insert` and
`Impl.waitFree_of_cfgPotential`.

**CSLib candidates.** The forest lemmas of `Forest.lean` (`rootOf`, `rootOf_update_split`,
`rootOf_update_link`).
