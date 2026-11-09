# Gracefully Degrading Consensus and k-Set Agreement under Dynamic Link Failures — PODC 2014

Manfred Schwarz, Kyrill Winkler, Ulrich Schmid, Martin Biely, Peter Robinson. *Brief announcement: Gracefully
degrading consensus and k-set agreement under dynamic link failures.* PODC 2014. DOI
[10.1145/2611462.2611506](https://doi.org/10.1145/2611462.2611506). Formalized version: the full version, Biely,
Robinson, Schmid, Schwarz, Winkler, *Gracefully Degrading Consensus and k-Set Agreement in Directed Dynamic
Networks*, arXiv [1501.02716](https://arxiv.org/abs/1501.02716) v1; numbering follows it. Its Sections 6–7 are the
PODC'14 announcement, Sections 4–5 the SIROCCO'12 consensus part. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ Intent lost.** The paper's central algorithm is wrong. Algorithm 4, the "first gracefully degrading
consensus algorithm", violates agreement: with `k = 1` (consensus) there are runs under `VSRC(n, 3D + H) + MAJINF(1)` in
which two values are decided, so Theorem 11 is false. The impossibility results hold: Theorems 7, 8 and 9, and the
consensus lower bound Theorem 4 they rest on. Proving Theorems 4 and 7 needed new arguments. Theorem 10 (set agreement)
is correct.

## Mistakes in the paper

### ❌ Theorem 11 (Algorithm 4, k-agreement)
Algorithm 4 does not solve `k`-set agreement under `VSRC(n, 3D + H) + MAJINF(k)`. Two runs with `k = 1` decide two
different values:
- `n = 5`, `D = H = 1` (`theorem11_false`);
- `n = 8`, `D = 2`, `H = 1` (`theorem11_false'`); the same run with `H = D = 2` (`theorem11_false'_H2`), as the
  paper assumes `H ≥ D`.

**Impact.** The paper's main positive result, the `k`-uniform, gracefully degrading `k`-set agreement algorithm,
is refuted, already for consensus. The impossibility results of Section 6 and Theorem 10 are not affected.

**Details.** The proof breaks in Lemma 26. It claims that, by majority influence, no lock is known to more members
of `R_suc` than the lock `L` of the majority-influencing `R_cur`. It also claims that equally frequent locks are
older than `L`. But Definition 19 counts only causal chains that start *after* a VSRC's stability interval. It
constrains neither locks spread *during* the interval nor virtual locks (initial values).
- *First run* (`theorem11_false`, processes `a, b, c, y, s`, inputs `1..5`).
  - `{a}` is a root in rounds 1–3. `{b}` and `{c}` are roots in rounds 5–7 and 5–8. From round 10 on the graph
    is the static star from `s`. Every other root lasts one round.
  - `K = {{a}}`, `{a} ↪m {b}`, `{a} ↪m {c}`, `{b} ↪m {s}`.
  - `a` decides 1. `b` and `c` lock `({b}, 1, 7)` and `({c}, 1, 7)`.
  - `c`'s lock reaches `s` through `y` in round 8, inside `c`'s interval, so `IS({c}, {s}) = ∅`.
  - In `s`'s `GetLock` the two locks tie in multiplicity and creation round. The fallback of line 32 takes the
    largest value of *all* known locks, and `s` decides its own input 5.
- *Second run* (`theorem11_false'`): no tie and no fallback.
  - `{a}` is a root in rounds 1–5, then `R_suc = {1, 2, 3}` from round 7 on, with `{a} ↪m R_suc`.
  - The virtual lock of process `h` is known to all three members of `R_suc`, and `a`'s lock only to two.
  - `R_suc` locks and decides `h`'s input 2, while `a` decided 1.

Both runs are verified against the formal adversary (`Scenario1.mem_VSRCkAll`, `Scenario1.mem_MAJINF`, and the
same for `Scenario2`). The decisions are computed by evaluating the algorithm in the kernel. Definition 19 is
taken in its charitable reading (next item), and Algorithm 1's `InStableRoot` in its sound reading (see
[differencies.md](differencies.md)).

Further problems, found by simulation only (not in Lean):
- A run with `D = 2` breaks agreement in another way. A member of `R_cur` releases and re-locks with a newer lock
  of another value, which a successor VSRC adopts.
- Lemma 22 (termination) is off by one. A VSRC decides only in round `a + 3D`, so its decision can miss the
  `3D + H` window.

### ✏️ Definition 19 (majority influence)
Read literally, `R` ranges over all of `V_{D+1}`, including `R_cur` itself, where `IS(R_cur, R_cur) = ∅` requires
`|IS(R_cur, R_suc)| > |IS(R_cur, R_suc)|`. So `↪m` never holds (`majInfLit_false`), and `MAJINF(k)` degenerates to
"at most `k` VSRCs in `V_{2D+1}`" (`mem_MAJINFLit_iff`).

**Impact.** `R ≠ R_cur` is clearly meant. Without the requirement that `R_cur` precedes `R_suc`, which the text
implies ("by some earlier VSRC"), the antisymmetry claimed in Lemma 18 fails. We use the reading with both
(`MajInf`); Theorem 11 fails under it.

### ❌ Theorem 4, first claim, Definition 13 and Lemma 8 (`VSRC'(H − 1)`)
The sharper impossibility under `VSRC'(H − 1)` fails as stated and its proof does not work for the reading the
text describes.

**Impact.** The sharper impossibility under `VSRC'(H − 1)` is not established. The claim used later, Theorem 4
for `VSRC(H − 1)`, holds (proof-gap item below, `theorem4`).

**Details.**
- *Literally* (a slip on its own): Definition 13 asks for a *unique* process `q` with `cd_x(p, q) ≤ H` while
  every other process has `cd_x(p, q') ≤ H − 1 ≤ H`, so it is unsatisfiable with two processes. Hence
  `VSRC'(H − 1) = ∅`, every algorithm solves consensus under it, and Theorem 4's first claim and Lemma 8's
  `VSRC'(H − 1) ⩾ VSRC(H)` are false (`vsrcPrime_eq_empty`, `theorem4_prime_false`, `lemma8_false`).
- *Reading of the text* ("guarantees one process to be reached from the processes in `R` within `H` rounds"):
  all but one process are reached within `H − 1` rounds, the last one within `H`. The proof fails: Lemma 9's
  cases (ii) and (iii) make the distant process `q` the single root right after the window `J`, so `q` is
  never reached from `R`. In fact, if `p ∈ R` changes state at the start of `J`, the change reaches every
  process within `H` rounds, so no process can serve as Lemma 9's witness. Lemma 8 also fails under this
  reading: Definition 13 quantifies "for all `p ∈ R`" where Definition 10 has "for some `p`".
- *Weakest reading* (the condition on `q` is void: all but at most one process are reached within `H − 1`
  rounds): Lemma 9 (ii) goes through, but the induction of Theorem 4 has the gaps of the item below, and our
  re-proof does not cover it (its window graphs need not reach anybody within `H − 1` rounds). Not proved
  either way.

### ✏️ Slips
- Theorem 4 needs `2 ≤ H ≤ n − 1`. For `H = 1` the window `d = H − 1 = 0` is meaningless, and the distant
  process needs `H + 1` processes. For large `H` the claim would contradict the paper's own Theorem 5 with
  `H' = n − 1`. The paper's `H` is a causal diameter, at most `n − 1` by Lemma 4.
- Lemma 17 as stated ("some round `r' > 0`") is trivial: `r' = 1` gives two processes that never communicate
  (`lemma17`). The proofs of Theorems 8 and 9 need the version for every fixed `r'` (`lemma17_fixed`).

### Typos
- Proof of Theorem 8: "`Di (i < 0 < k)`" should read `0 < i < k`.

## Proof gaps (statements true)

### 🛠️ Theorem 4 (no consensus under `VSRC(H − 1)`)
The bivalence induction never checks that the forever-bivalent run is feasible. Lemma 10's intermediate graphs
are arbitrary single-root graphs, so item (ii) of Definition 12 (every VSRC `H`-network-bounded) may fail. A VSRC
of the prefix may also run into the window `J` and force the distant process to be reached.

**Impact.** Statement true for `2 ≤ H ≤ n − 1`; re-proved (`theorem4`).

**Repair.** A product sub-adversary `famT4` (`prodAdv_famT4_subset`):
- the window `J` is the first `H − 1` rounds, and every graph there has root `{a}`;
- after `J` the adversary uses only "fast" graphs, with a root of at most two processes that every other process
  hears directly.

The rest of the argument:
- Lemma 10 is proved inside these families via stars (`chain_rootedAt`, `chain_famF`).
- Lemma 9's strategy (`iso_famT4`): during `J`, `a`'s information goes down a line `a → c₁ → ⋯ → q` of length
  `H`, and then `q` is the eternal root.
- The bivalence skeleton is generic (`not_solvesConsensus_of_chain_isolation`).

### 🔧 Theorem 7 (case `k = 1` and use of Theorem 6)
For `k = 1` the paper appeals to Theorem 4 "with item (ii) dropped". That is a larger adversary than
`VSRC(1, H − 1)`, so it does not give the claimed impossibility. For `k > 1` it uses the generic Theorem 6, whose
literal statement is false (see `Papers/PODC2011/KSetAgreement`).

**Impact.** Statement true for every `D ≥ 1`, `H ≥ 2`, `|V| > k`, even with `k − 1` roots stable forever
(`theorem7`). It also holds for the literal reading of Definition 15 (iii) (`theorem7_weak`).

**Repair.** All runs of `famT4` have only roots that are cliques of at most two processes, so item (ii) holds for
every `D ≥ 1` (`dBounded_of_clique`). The reduction to consensus among `D̄` is proved directly
(`restrict_solvesConsensus`):
- the processes of `D` decide their own inputs, chosen to avoid the two values on which `D̄` disagrees;
- validity of `A|D̄` follows by giving `D` an input of `D̄`. This is the condition (E) that the repaired Theorem 6
  needs.

### 🔧 Theorem 9 (finite-horizon lossy link)
The proof uses Lemma 17 ("`A|Dᵢ` cannot have solved consensus") to get a bad link pattern for each pair. But the
pattern must have a prescribed length: the pair's lossy period ends when the earlier phases end.

**Impact.** Statement true (`theorem9`); Theorem 8 follows from it (`theorem8`).

**Repair.** The chain argument for a fixed horizon `L` (`exists_lossy_disagree`): if the two processes agree after
every lossy pattern of length `L`, the decision does not depend on the pattern, and the two one-directional
patterns force their two inputs. Each pair's pattern is chosen after the length of its lossy period is known.

### 🔧 Theorem 10 (Algorithm 3, the process with the largest input)
The inductive proof does not justify why `pᵢ` decides `xᵢ`. It also leaves implicit why a process deciding by
line 11 in round `n` was deaf.

**Impact.** Statement true (`theorem10`).

**Repair.** If `n` values are decided, the decision map is a permutation of the inputs, and each decision is at
least the decider's input. Induction on the rank then forces every process to decide its own input in a deaf
round. A causal chain from one such round to a later one would make the later process adopt a decision first.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Synchronous lock-step rounds, `n` processes with unique identifiers, no process failures.
- An omniscient message adversary chooses the directed graph of every round. Message adversaries are arbitrary
  sets of graph sequences (`Model.lean`, CSLib `Cslib.HeardOf.Graph`).
- Deterministic full-information algorithms (`Alg`) with irrevocable decisions. These cover all algorithms of the
  paper, which may know `n`, `D`, `H`, `k`. No randomness.
- Inputs are arbitrary and independent of the graphs. `k`-agreement, validity and termination are required in
  every run.
- Root components are CSLib's `Digraph.IsSourceComponent`. Causal-distance bounds are CSLib journeys
  (`Cslib.DynNet.Journey`).
- Definitions 9, 10, 12, 15 and 16 are in `Model.lean`. Definition 15 (iii) is ambiguous: `VSRCk` is the literal
  reading and `VSRCkAll`/`VSRCkInf` the strong one (all roots of the window are stable). Impossibilities are proved
  for the strong reading, which is the smaller adversary.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 9/10 + induction (generic) | `not_solvesConsensus_of_chain_isolation` | `Bivalence.lean` |
| Theorem 4 (`VSRC(H − 1)`, `2 ≤ H ≤ n − 1`) | `theorem4` | `Consensus.lean` |
| Def. 13 unsatisfiable, Theorem 4 (first claim) and Lemma 8 false | `not_almostBounded`, `vsrcPrime_eq_empty`, `theorem4_prime_false`, `lemma8_false` | `Consensus.lean` |
| Theorem 7 | `theorem7`, `theorem7_weak` | `KSetShort.lean` |
| Lemma 17 (fixed `r'`; literal) | `lemma17_fixed`, `lemma17`; core `exists_lossy_disagree` | `LossyLink.lean` |
| Theorem 9 | `theorem9` | `KSetUnstable.lean` |
| Theorem 8 | `theorem8` | `KSetUnstable.lean` |
| Theorem 10 (Algorithm 3) | `theorem10`, `alg3_decided_at_n` | `SetAgreement.lean` |
| Algorithms 1 + 4 | `alg4` | `Alg4.lean` |
| Definitions 17–21 (`IS`, `↪m`, `MAJINF(k)`) | `IS`, `MajInf`, `MAJINF`; literal Def. 19: `MajInfLit`, `majInfLit_false`, `mem_MAJINFLit_iff` | `MajInf.lean` |
| Theorem 11 is false (`k = 1`) | `theorem11_false`, `theorem11_false'`, `theorem11_false'_H2` | `Theorem11.lean` |

**Not formalized.** Theorems 1–3 and 5, Algorithm 2, Lemmas 1–7 and 11–16, the expander example (Lemma 5),
Theorem 6 as a black box (its instance is proved directly), and Lemmas 18–26 beyond the counterexamples.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The impossibility proofs construct explicit feasible runs, so the adversaries are non-empty. `const_star_mem_VSRCd`
shows that the constant star is in `VSRC(d)`. `complete_mem_sigmaMaj` shows that `Σ_{n−1}-MAJ` is non-empty, but
only trivially: the complete graph has no singleton roots.

Reusable pieces (CSLib candidates):
- the generic bivalence theorem for product message adversaries (`Bivalence.lean`);
- `conf_eq_of_not_journey`;
- the root-counting lemma `isRootComp_mem_of_reach`;
- `dBounded_of_clique`;
- the finite-horizon lossy-link lemma `exists_lossy_disagree`;
- deciding journeys, reachability and root components of Boolean patterns (`Decide.lean`);
- adversary membership of eventually constant patterns (`Concrete.lean`).

The adversary definitions follow the stated reading choices: the strong reading of Definition 15 (iii) and the
charitable reading of Definition 19. The counterexamples satisfy both, and the literal Definition 15 (iii) is
implied.
