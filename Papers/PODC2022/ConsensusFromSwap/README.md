# The Space Complexity of Consensus from Swap — PODC 2022

Sean Ovens. *The Space Complexity of Consensus from Swap.* PODC 2022. DOI
[10.1145/3519270.3538420](https://doi.org/10.1145/3519270.3538420). Formalized version: arXiv
[2305.06507](https://arxiv.org/abs/2305.06507) v2 (Aug 2023), which also covers k-set agreement.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** Every formalized result holds as stated, for obstruction-free
algorithms:
* Algorithm 1 is an obstruction-free k-set agreement algorithm from `n − k` swap objects;
* `⌈n/k⌉ − 1` swap objects are needed, so `n − 1` is tight for consensus;
* `n − 2` readable binary swap objects are needed;
* `(n−2)/(3b+1)` readable swap objects with domain size `b` are needed.

Repairs were needed in a few places. One step of the proof of Lemma 16 does not follow as written. The valency
definitions are ambiguous, and Lemma 13's proof relies on one reading of them. The proof of Lemma 14 picks `j`
over the wrong set of executions. A few statements fail in degenerate cases.

## Mistakes in the paper

### ⚠️ Observation 4 for `m = 1` (Algorithm 1)
Observation 4 ("`V[x] ≥ 2` when `x` is decided") is false for `m = 1`: the only value is decided with `V[0] = 1` (`example` in `Alg1Agree.lean`).

**Impact.** Degenerate case: Lemma 6 uses Observation 4 only when two values are decided, so nothing breaks
(`lemma6_agreement`).

### Typos and slips
- Lemma 16, Case 2: "then `P` is univalent" should be `Q`.
- Section 5.2: "`S_1 = {p_1}` covers" should be `{p_0}`.
- Lemma 6, Step 1: "`V_j[v_j] = ℓ_j > V_{k+1}[v_j] + 2`" should read `x_j` for `v_j`.

## Proof gaps (statements true)

### 🛠️ Lemma 16, Case 2, property (d) for `i+1`
The proof shows only that `Q` is univalent in `C_{i+1}λ'd` (via Lemma 14(b)) and then says "therefore" `Q` is univalent in `C_{i+1}λ'dβ_i`, but univalence of `Q` is not preserved by steps of processes outside `Q`, and the block `β_i` is such a step sequence.

**Impact.** Statement true; repaired by a case split (`lemma16_step`).

**Details.** What is needed: if the block swap `dβ_i` changes an object of `Y_i ∪ {B}` when applied in
`C_{i+1}λ'`, then `Q` is univalent in `C_{i+1}λ'dβ_i`.

**Repair.**
* If `β_i` changes an object of `Y_i` in `C_{i+1}λ'd`, the induction hypothesis (d), with `λ = γα_jλ'd`,
  applies directly.
* Otherwise `β_i` leaves the memory unchanged. Observation 15 then transfers univalence from `C_{i+1}λ'd` to
  `C_{i+1}λ'dβ_i`.

### 🛠️ Lemma 13 (ambiguous valency definitions)
"`P` is bivalent in `C` if … there is an execution from `C` … in which some process in `P` decides `v`" does not say whether decisions taken before `C` count, and Lemma 13's proof works only if they do.

**Impact.** Statement true under the inclusive reading; with agreement, nothing else in the paper changes
(`CanDec`, `lemma13`).

**Details.** Lemma 13's proof uses "`Q` is `v̄`-univalent in `Cαβ`", where `α` contains a decision of `v̄`. If
decisions must happen inside the extension, and both processes of `Q` have already decided in `α`, then `Q`
is vacuously `v`-univalent in `Cαβ` as well. The prefix `α'` used by the proof need not exist.

**Repair.** Count earlier decisions (`CanDec`), or cut `α` after its first decision. We do the former.

### 🛠️ Lemma 14 (choice of `j`)
The proof picks `j` as the least index such that `Q` is univalent after *every* execution `α ∼_{p_i} δ_{j+1}` from `C`, but then minimality only yields some bivalent execution `α_{j'}`, while part (a) needs a `(Q ∪ P_i)`-only one.

**Impact.** Statement true; the minimum must range over `(Q ∪ P_i)`-only executions. Parts (b) and (c) only
use such executions, so the fix is harmless (`lemma14`).

### 🛠️ Lemma 6, Step 2 (missing case)
The proof splits into "`C` before `C_t`" and "`C` after `C_t`" and omits `C = C_t`.

**Impact.** Statement true; the case is trivial, since it would force `q = p_t` (`lemma6_agreement`).

### 🛠️ Theorem 10, induction step (restricted algorithm)
The claim "the algorithm solves `k`-valued `(k−1)`-set agreement among the processes in `R`" does not obviously hold, because in an `R`-only execution a decided value could be the input of a process outside `R`, so validity may fail.

**Impact.** Statement true; repaired (`theorem10_gen`).

**Repair.** Reset the inputs outside `R`, which is invisible to `R`. We use a different split of `R` (peel off
`#objects + 1` processes), which gives the same bound with no base case and no hypothesis `n > k`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Model.lean`, self-contained, built on CSLib's `ObjSpec`).
* Asynchronous shared memory with deterministic processes.
* Processes start with their inputs; `A.init p x` is the initial state of `p` with input `x`.
* A local state either outputs a value (a final state; its steps are no-ops) or is poised on one operation of one
  object. The scheduler is arbitrary.
* Executions are lists of process ids; `run C α` is the configuration they reach from `C`.
* `SolvesSetAgreement A k S`: at most `k` decided values (`k`-agreement) and every decided value is some
  process's input (validity), for all initial configurations with inputs in `S`.
* `ObstructionFree A S`: from every reachable configuration, each process decides when it runs solo.
* **Scope (weaker than the paper for Theorem 10).** Only deterministic, obstruction-free algorithms are covered.
  * Theorem 10 / Corollary 11 are proved only for this class. It is a strict special case of the paper's
    nondeterministic solo-terminating algorithms (which include randomized wait-free ones), so our statement is
    weaker than the paper's.
  * Theorems 18 and 22 lose nothing: the paper states them for obstruction-free algorithms too, and extends them
    to other algorithms only through cited results.
* Object types:
  * Section 4: any objects all of whose operations are nontrivial historyless
    (`ObjSpec.OverwritesState`, CSLib), in particular swap objects (`swapObj`). This covers the paper's remark on historyless objects without trivial operations.
  * Section 5: readable swap objects `rswapObj D` with one value set `D`, `|D| = b` (the paper's "WLOG").
  * Initial values are arbitrary.
* Lemmas 13 and 14 are proved for arbitrary objects. A covering process must be poised on an operation that
  overwrites the object.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Algorithm 1, Lemmas 6–8 | `algorithm1_correct` (`lemma6_agreement`, `lemma7_validity_strong`, `lemma8_bound`) | `Main.lean`, `Alg1*.lean` |
| Lemma 5 | `Alg1.Agree.Sched.lemma5` | `Alg1AgreeLemma5.lean` |
| Lemma 9 | `lemma9` | `SetAgreementLB.lean` |
| Theorem 10, Corollary 11 (OF) | `theorem10`, `theorem10_swap`, `consensus_swap_lowerBound` | `SetAgreementLB.lean` |
| Table 1, consensus from swap: `n − 1` tight | `consensus_swap_tight` | `Main.lean` |
| Observation 12, Lemmas 13, 14, Observation 15 | `obs12`, `lemma13`, `lemma14`, `obs15` | `Valency.lean` |
| Lemma 16 (with Claim 17), Theorem 18 | `lemma16`, `theorem18` | `BinarySwap.lean` |
| Lemma 20 (with Claim 21), Theorem 22 | `lemma20`, `theorem22` | `BoundedSwap.lean` |

Further result: validity of Algorithm 1 holds in the stronger form "the decided value is the input of a process
that took a step".

**Not formalized.**
* Nondeterministic solo-termination and randomized wait-freedom.
* The transformation of Ellen–Gelashvili–Zhu (needed for Corollaries 19 and 23).
* The simulations of historyless objects by (readable) swap objects.
* Table 1 entries cited from other papers.

**Trust.**
* No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
* Non-vacuity for Sections 3–4: Algorithm 1 satisfies the hypotheses of Theorem 10 and attains its bound for
  `k = 1` (`consensus_swap_tight`).
* Non-vacuity for Section 5 is not established: no algorithm from readable *bounded* swap objects is formalized.
* Before the proof, a bounded breadth-first model check of Algorithm 1 found no agreement or validity violation.
  It ran a small script (not in the repository) on all input vectors for `(n, k, m) = (2,1,2)`,
  `(3,1,2)`, `(3,2,3)` and `(3,1,3)`, with lap counters bounded by 3–5.
