# Eventually Linearizable Shared Objects — PODC 2010

Marco Serafini, Dan Dobre, Matthias Majuntke, Péter Bokor, Neeraj Suri. *Eventually Linearizable Shared
Objects.* PODC 2010. DOI [10.1145/1835698.1835723](https://doi.org/10.1145/1835698.1835723). Formalized
version: the authors' copy with the appendix (full proofs of Theorems 1–3); no arXiv version. Copy of the
paper: [paper.pdf](paper.pdf).

**Verdict: ❌ Intent lost.** Eventual Consensus is not shown to suffice for Eventual Linearizability:
Algorithm 1 is not even weakly consistent over an Eventual Consensus layer, and with Eventual Stability
read per run (as the rest of the layer specification) no implementation over such a layer is eventually
linearizable. The nonblocking part of Theorem 1 and Lemma 5 are false as well, while locality (Theorem 1,
Lemmas 1–2) and Theorem 2 hold. The tradeoff (Theorem 4) and Aurora were not checked.

## Mistakes in the paper

### ❌ Theorem 3, sufficiency (Lemma 6, Algorithm 1)
Algorithm 1 over a layer satisfying Eventual Consensus can return `0` to a read of `p0` after an
earlier read of `p0` returned `1` written by `swap(1)`, so its history is not weakly consistent
(`algorithm1_not_weaklyConsistent`).

**Impact.** The proof of "Eventual Consensus is sufficient" fails at its first step, under every
reading of Eventual Stability. Theorem 2 and the definition of Eventual Consensus as a target are
unaffected.

**Details.** In the counterexample (`tr₁`), `p1` submits `x = swap(1)`, `p0` submits `o' = read`
and gets `[x, o']`, so `o'` returns `1`. Then `p0` submits `o = read` and gets `[o, x, o']`, which set
stability allows (it only requires the old operations to be present). Algorithm 1 executes the sequence
up to `o` and returns `0`. Weak consistency is violated: `τ(p0, o')` must contain `x` (the only
`swap(1)`), condition (iii) puts `x` into `τ(p0, o)` before `o`, so `o` must return `1`. The layer is
stable from time 7 on and converges to `[o, x, o']`; all processes are correct. The paper's claim
"weak consistency directly derives from the set stability and nontriviality properties" overlooks
that set stability allows observed operations to move after the new one.

**Repair.** None formalized. With a uniform stability time, completing `o` after the operations
observed earlier (rather than at its position in the delivered sequence) restores weak consistency;
whether the rest of Lemma 6 then goes through is not checked.

### ❌ Theorem 3 and Eventual Stability (the stability time, Lemmas 6–7)
The definitions do not say whether the stability time of Eventual Stability may depend on the run, and
no reading gives both halves of Theorem 3: read per run, no implementation over such a layer is
eventually linearizable, even for a single-writer single-reader binary register
(`not_eventuallyLinearizable_eCons`).

**Impact.** With Eventual Stability read per run, sufficiency is false for every implementation. This
uses one `t_l` for all runs, which the paper requires and its proof of Theorem 2 uses. Read uniformly
over runs, sufficiency may hold with a repaired algorithm, but then the necessity proof (Lemma 7)
yields only a per-run stability time. If both `t_l` and the stability time are read per run,
sufficiency is not refuted; only Algorithm 1 and the proof of Lemma 6 fail.

**Details.** Every other layer property is a property of a run, and Lemma 7 constructs a run-dependent
time (`t_s > max(t_l, t_d)`, where `t_d` depends on the run). With that reading the proof of Theorem 2
applies verbatim to Eventual Consensus: its layer behaviour becomes stable at the final delivery.
So no implementation over such a layer has one `t_l` for all runs, which Eventual Linearizability
requires (`not_eventuallyLinearizable_eCons`). The proof of Lemma 6 is also built on the false
Lemma 5, and its `t_l = max(t_s, t_p, t_c)` depends on the run through `t_p` and the crash time `t_c`.

### ❌ Theorem 1, nonblocking part
"Eventual Linearizability is nonblocking" is false: in a weakly consistent, `3`-linearizable history
with a pending `swap(2)`, every response breaks one of the two properties
(`theorem1_nonblocking_false`).

**Impact.** Only locality survives from Theorem 1. Weak consistency alone and `t`-linearizability
alone are nonblocking (Lemmas 3 and 4 hold), but not their conjunction, which is what Eventual
Linearizability requires.

**Details.** One swap register (initially `0`), time = event position, `t = 3`:
`p1` invokes `i1 = swap(1)` (pending forever); `p0` runs `o' = read → 1`; `p0` invokes `o = swap(2)`
(pending); `p2` runs `r2 = read → 2`, then `r3 = read → 1`. This history is weakly consistent and
`3`-linearizable (`o', o, r2, i1, r3`). `t`-linearizability forces `o` to return `0`: `r2` (late)
needs `o` as the last swap before it, and `r3` needs `i1` after `r2`, so no swap precedes `o`. Weak
consistency forces `1`: `τ(p0, o')` contains `i1`, hence so does `τ(p0, o)`, and `i1` is the only
other swap. The proof "directly follows from Lemmas 1, 2, 3 and 4" combines the response chosen by
Lemma 3 with the one chosen by Lemma 4. Reading Eventual Linearizability of one history as "for some
`t`" would make the claim true but empty, since every finite history is `t`-linearizable for a late
`t`, as the paper notes.

### ❌ Lemma 5 (`t`-stability implies `t`-consistency)
False: two correct processes can hold `[c, a]` and `[c, b]` forever in a run satisfying Eventual
Consensus, stable from time `0` (`lemma5_false`).

**Impact.** Lemma 6 uses it. It holds if all processes are correct.

**Details.** The proof applies (C3) to the operations at the first position where the two
sequences differ, but (C3) covers only operations submitted by correct processes. In the
counterexample a faulty process submits `a` and `b`; the common prefix `[c]` contains the only
operation of a correct process.

### ✏️ Slips
- Definition of Eventual Linearizability and Theorem 2: the definition has no liveness requirement, so
  literally an implementation that never responds is eventually linearizable and Theorem 2 fails. The
  proofs use termination ("Let `t_w` be the time when the write operation completes"); with it Theorem 2
  is proved (`theorem2`).
- Lemma 4's proof says "`L` only contains completed operations", contradicting (P1); under (P1)
  the pending operation is always in `L`, and totality is not needed.
- Section 3.2: "every well-formed history has a `t`-permutation for each `t`" needs total operations.
- Theorem 4's proof puts all messages sent after `σ_{k-1}` into `M_k`, "not received in `σ_k`", but
  messages inside `Π_m` before `t_k` must be received, or `p_i` could tell `σ_k` from `σ_E1` up to `t_k`.
- Theorem 4's proof says "Runs `σ_E21` and `σ_E22` are indistinguishable"; it should read `σ_E22` and
  `σ_E23`.

### Typos
- Lemma 3's proof writes `p_j` for `p_i`.

## Proof gaps (statements true)

### 🛠️ Lemma 2, "if" direction (`t`-linearizability is local)
The minimal-cycle argument asserts `o_k <_{H,tmax} o_i <_{H,tmax} o_j`, which does not follow.

**Impact.** Statement true; repaired (`tLinearizable_of_restrictX`).

**Repair.** Merge the `L_x` by a key: the latest invocation time of a late operation at or before
the operation in its `L_x`. Keys are monotone along each `L_x` and strictly increase along `<_{H,t}`.

### 🔧 Lemma 1, "if" direction (weak consistency is local)
Reusing `τ_x(i, o)` from `H|x` for `H` violates condition (iii) across objects: `τ(i, o')` of an
earlier operation on another object is not contained in `τ_x(i, o)`.

**Impact.** Statement true; repaired (`weaklyConsistent_of_restrictX`).

**Repair.** For each object `y`, glue `τ_y` of the last operation of `p_i` on `y` before `o`, and put
`τ_x(i, o)` last.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- *Histories* (Section 3): CSLib Herlihy–Wing histories (`inv p x o` / `res p x r`, operations
  identified by `(p, x, k)`). Weak consistency (`WeaklyConsistent`), `t`-permutations (`IsTPerm`) and
  `t`-linearizations (`IsTLin`) are transcribed literally; the operations "invoked after `t`" are an
  arbitrary set `A` (`after invTime t` for a global clock), so locality is proved for any
  `A ⊆ A_x`. Nonblocking is the Herlihy–Wing notion used by Lemmas 3–4, for a fixed `t`.
- *Consistency layers* (Section 4): runs `S(i, t)` with submissions and correct processes;
  Eventual Consistency, Eventual Stability (per run), Eventual Consensus, `t`-consistency.
- *Implementations* (Theorems 2–3): asynchronous, crash failures, no failure detector, deterministic
  processes that communicate only through the layer. An adversary chooses one action per time unit:
  an invocation, a delivery, a local tick, or nothing. Admissible runs: crashed processes stop,
  correct processes tick infinitely often, single-writer/single-reader environment, and the layer run
  meets its specification. We require termination for correct processes (implied by the paper). Our
  Eventual Linearizability uses one `t_l` for all runs; prefixes must be weakly consistent and, in
  crash-free runs, `t_l`-linearizable. This is weaker than the paper's uniform and non-uniform
  notions, so the impossibility results are stronger.
- *Algorithm 1*: deterministic object, runs given as lists of invocations and deliveries.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (weak consistency is local) | `weaklyConsistent_iff_restrictX` | `Locality.lean` |
| Lemma 2 (`t`-linearizability is local) | `tLinearizable_iff_restrictX`, `tLinearizable_of_restrictX_after` | `Locality.lean` |
| Theorem 1, locality | `weaklyConsistent_and_tLinearizable_of_restrictX` | `Locality.lean` |
| Lemma 3 (weak consistency nonblocking) | `weaklyConsistent_nonblocking` | `Nonblocking.lean` |
| Lemma 4 (`t`-linearizability nonblocking) | `tLinearizable_nonblocking` | `Nonblocking.lean` |
| Theorem 1, nonblocking (false) | `theorem1_nonblocking_false`, `not_eventuallyLinearizable_nonblocking` | `Theorem1.lean` |
| Theorem 2 | `theorem2` | `Theorem2.lean` |
| Lemma 5 (false) | `lemma5_false`, `not_lemma5` | `Layer.lean` |
| Theorem 3 sufficiency / Algorithm 1 (false) | `algorithm1_not_weaklyConsistent` | `Algorithm1.lean` |
| Theorem 3 sufficiency, per-run Eventual Stability (false) | `not_eventuallyLinearizable_eCons` | `Theorem2.lean` |

**Not formalized.** Theorem 4 (its proof needs one stability time for all runs), Lemma 7 (necessity
in Theorem 3) beyond the run-dependence of `t_s`, Aurora (Section 5.2, Lemmas 8–13) and its use of
Theorem 3, the remarks of Section 2.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Counterexamples are checked by `decide +kernel` (no `native_decide`). The history layer
builds on CSLib's Herlihy–Wing framework (`Cslib.Computability.Distributed.SharedMemory.HerlihyWing`).
`Defs.lean` and `Locality.lean` are CSLib candidates.
