# Disjoint-Access Parallelism and Real-Time Order in TM — PODC 2015

Sebastiano Peluso, Roberto Palmieri, Paolo Romano, Binoy Ravindran, Francesco Quaglia. *Disjoint-Access
Parallelism: Impossibility, Possibility, and Cost of Transactional Memory Implementations.* PODC 2015. DOI
[10.1145/2767386.2767438](https://doi.org/10.1145/2767386.2767438). Formalized version: the Virginia Tech
technical report of May 2015 (14 pp., with the proofs of Section 3); no arXiv version. Numbering is the same in
both versions.

**Verdict: ❌ False claim.** The two impossibility theorems (Theorems 1 and 2: no weakly disjoint-access-parallel
TM with wait-free read-only transactions and obstruction-free, resp. weakly progressive write transactions with
invisible reads, ensures real-time order) are true, and the claims about the histories of Figure 1 hold. But
Lemma 1, on which their proofs rest, is false as soon as a third process takes steps; we re-prove both theorems
without it. The lower bounds (Theorems 3 and 4) and the algorithm of Section 4 are not formalized.

## Mistakes in the paper

### ❌ Lemma 1 (disjoint-access transactions never contend)
"In a WDAP TM two concurrent disjoint-access transactions cannot contend on a common base object" is false:
there is a WDAP TM with three processes in which a transaction `Tⱼ` reads a base object written by a
concurrent, disjoint-access transaction `Tᵢ` (`Lemma1.lemma_1_false`).

**Impact.** Lemma 1 is the basis of Lemmas 2 and 3, so the paper's proofs of Theorems 1 and 2 (and the uses of
Lemma 1 in the proof of Theorem 3) are not valid as written. Theorems 1 and 2 themselves are true (see the proof
gap below).

**Details.** The proof only considers executions in which `Tᵢ` and `Tⱼ` are the only transactions taking steps:
it delays the first contending event of `Tⱼ` until it is concurrent with that of `Tᵢ`. With a third process,
information can flow from `Tᵢ` to `Tⱼ` through two *different* transactions of that process. The counterexample
TM `Lemma1.chainTM` has base objects `o(y,q)` (written once, by the first write of process `q` to `y`) and a
board `f(x)` per transactional object `x`. A write to `x` writes `o(x, self)` the first time, then publishes on
`f(x)` all pairs `(y,q)` it knows to be written. A read of `x` reads `f(x)`, then the published `o(y,q)` and all
`o(x,q)`. The execution `Lemma1.exec`:
1. `Tᵢ` (process 0) writes `x₀` and stays live;
2. `T_k1` (process 1) reads `x₀`, sees `o(x₀, 0)` written, commits;
3. `T_k2` (process 1) writes `x₁`, publishing `(x₀, 0)` on `f(x₁)`, commits;
4. `Tⱼ` (process 2) reads `x₁`, finds `(x₀, 0)` on the board and reads `o(x₀, 0)`.

`Tᵢ` and `Tⱼ` are live, hence concurrent. Their only conflict edges are `Tᵢ — T_k1` (object `x₀`) and
`T_k2 — Tⱼ` (object `x₁`), so they are disjoint-access. Yet `Tⱼ` reads the base object `Tᵢ` wrote. They never
contend *concurrently*: `Tⱼ` reads `o(x₀,0)` only after learning that it is written for good. In every reachable
configuration, two processes poised to contend on a base object run transactions with intersecting data sets
(`Lemma1.chainTM_strongWDAP`). So `chainTM` is WDAP for the data-set/conflict-graph definition of Attiya,
Hillel and Milani [4], which the paper says it uses. It is not WDAP if "disjoint-access" is read literally as "no
path in the DSG" of the current history: then two transactions with pending operations on the same object are
"disjoint" until one of them commits, which rules out even a reader and a writer of the same object touching a
common base object concurrently.

The same pattern breaks the non-concurrent case of Lemma 2's proof, which cites Lemma 2 of [4] for two
"consecutive" transactions although other transactions may run in between; we did not formalize Lemma 2.

### ⚠️ Theorems 1 and 2 (progress conditions without termination)
As defined in Section 2, obstruction-freedom and weak progressiveness only forbid aborts, so a TM whose write
transactions never return satisfies them and trivially preserves RTO.

**Impact.** The intended (standard) definitions include termination of operations that run solo, as in the
cited [15, 17]; with it both theorems hold.

**Details.** The proofs need `T₃` and `T₂` to commit ("they cannot be aborted"). We assume that a write
transaction running solo completes its operations (`ObstructionFreeWrites`), resp. that a write transaction
running with no concurrent transaction completes and commits (`IsolatedWritesCommit`).

## Proof gaps (statements true)

### 🛠️ Theorems 1 and 2 (the indistinguishability argument)
The proofs apply Lemma 3 (via the false Lemma 1) to `T₄` and `T₂` in `H_WRTO`, and the proof of Lemma 3 only
reorders the steps of these two transactions, ignoring `T₃`.

**Impact.** Statements true; re-proved without Lemmas 1–3 (`theorem_1`, `theorem_2`).

**Details.** To move `T₂` before `T₄`'s first read one must also move it before `T₃`. In `H_WRTO`, `T₂` and `T₃`
are connected through `T₄`, so WDAP does not directly say that they do not contend.

**Repair.** We use WDAP only at the moments where it applies. At every configuration reached by interleaving
the steps of `T₂` with those of `T₃` after `R₄(y)` (or with those of `R₄(y)`), `T₂` has accessed only `x` and
the others only `y`: transactions are not known a priori, so `T₄` has not yet read `x`. Hence the two sides
never contend, and their steps commute (`commute`, `noContendFrom_of_wdap`, `commute_scenario`). So
`E = R₄(y) · T₃ · T₂ · R₄(x) c₄` and `E' = T₂ · R₄(y) · T₃ · R₄(x) c₄` are executions in which `R₄(x)`
returns the same value. If it is `T₂`'s value, `E`'s history is `H_WRTO` and violates RTO
(`T₃ ≺RTO T₂ →wr T₄ →rw T₃`). If it is the initial value, `E'` violates WRTO (`T₂ ≺WRTO T₄ →rw T₂`). In
particular, under WRTO the TM produces `H_WRTO` (`theorem_1_wrto`, `theorem_2_wrto`; this contains the instance
of Lemma 3 used by the paper).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory from CSLib (`Cslib.SharedMemory.Impl`): deterministic processes, arbitrary
  atomic base objects, arbitrary scheduler, environment choosing the invocations; crashes are processes that
  stop taking steps (only finite executions are used). A TM is an implementation of the interface `read x`,
  `write x v`, `tryC`; a transaction begins with its first invocation (no separate `begin` step) and ends with
  an abort or a successful `tryC`.
* Histories, versions (initial version and committed writers in commit order), the DSG edges `wr`, `ww`, `rw`,
  real-time order and the paper's "`H` preserves RTO / WRTO" (no cycle through `Tq`, `Tk` after adding an edge
  for every `Tq ≺ Tk`) are defined on arbitrary histories (`Model.lean`). Read-from is determined by values, so
  "the TM ensures RTO / WRTO" quantifies over histories with unique written values (`UniqueWrites`: every write
  to `x` writes a value different from `x`'s initial value and from the other writes to `x`), the usual
  convention that makes the paper's `Rᵢ(xⱼ)` well defined; accordingly, Theorems 1 and 2 assume that the value
  domain has a value other than the initial values of `x` and `y`.
* WDAP: whenever two processes are poised to contend on a base object (at least one non-trivial primitive),
  their transactions are joined by a path in the conflict graph of the history so far (vertices: begun
  transactions; edges: intersecting data sets). This is weaker than the definition of [4] and than the paper's
  DSG-based wording, so the theorems cover more TMs.
* Progress, as hypotheses only for the operations the proofs use (each implied by the paper's notions plus
  termination): a write transaction without step contention completes its operations solo without abort;
  a write transaction running with no concurrent transaction commits; an operation of a transaction that has
  not written completes solo without abort (WFRO); the steps of its reads are trivial (IRO); a read returns
  the initial value or a value some invoked write writes (implicit in the paper's histories).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 | `theorem_1`, `theorem_1_explicit`, `theorem_1_wrto` | `Impossibility.lean` |
| Theorem 2 | `theorem_2`, `theorem_2_explicit`, `theorem_2_wrto` | `Impossibility.lean` |
| Lemmas 1–2 as used (commutation under WDAP) | `commute`, `noContendFrom_of_wdap`, `commute_scenario` | `Commute.lean`, `Impossibility.lean` |
| Lemma 1: **false** | `Lemma1.lemma_1_false` | `Lemma1.lean` |
| Lemma 3, instance in `H_WRTO` | `hWRTO_of_run` | `Impossibility.lean` |
| Figure 1: `H_WRTO` preserves WRTO, not RTO | `Figure1.hWRTO_preservesWRTO`, `Figure1.hWRTO_not_preservesRTO` | `Figure1.lean` |
| Figure 1: `H_NO-RTO` preserves neither | `Figure1.hNoRTO_not_preservesWRTO` | `Figure1.lean` |
| "WRTO is strictly weaker than RTO" | `PreservesRTO.preservesWRTO`, `Figure1.wrto_strictly_weaker` | `Model.lean`, `Figure1.lean` |

`theorem_1` / `theorem_2` state the paper's form (`¬ EnsuresRTO`: some history of the TM with unique written
values violates RTO); the `_explicit` versions name the violating execution (`E` or `E'`, for any value `v₁`
written by `T₂` and `T₃`; with unique values when `v₁` differs from the initial values); the `_wrto` versions
show that a TM ensuring WRTO produces `H_WRTO` itself.

**Not formalized.** Lemma 2 and Lemma 3 in general; Theorems 3 and 4; the algorithm of Section 4 and its
correctness arguments; Consistent View and EUS. Theorems 3 and 4 are argued informally and do not fix what is
counted. For Theorem 3, the proof argues `Ω(Nₒ)` for a single version check and then multiplies by `k` without
justification. It also applies Lemma 1 to `Ti*` and `Ti+`, which are not disjoint-access since both are
connected to `Tro`. For Theorem 4, "space per version" is undefined: an unbounded register can hold a whole
vector clock.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The hypotheses of Theorems 1 and 2 are satisfiable together: the trivial TM that answers every operation at once
satisfies all of them (`trivTM_hyps`, `NonVacuity.lean`). Whether the hypotheses of `theorem_1_wrto` (with
WRTO) can be met is not checked; for `theorem_2_wrto`, Section 4 of the paper claims such a TM. The counterexample
to Lemma 1 is checked by kernel computation on a concrete execution. The TM layer (`Model.lean`,
`Commute.lean`) is built on CSLib's `Cslib.Computability.Distributed.SharedMemory` model and is a CSLib
candidate.
