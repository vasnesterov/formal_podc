# Byzantine Vector Consensus in Complete Graphs — PODC 2013

Nitin H. Vaidya, Vijay K. Garg. *Byzantine Vector Consensus in Complete Graphs.* PODC 2013. DOI
[10.1145/2484239.2484256](https://doi.org/10.1145/2484239.2484256). Formalized version: arXiv
[1302.2543](https://arxiv.org/abs/1302.2543) v1 (full version with appendices); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The main results (Theorems 1–5 and Lemma 1) hold. Exact BVC
in synchrony is solvable iff `n ≥ max(3f+1, (d+1)f+1)`, and approximate asynchronous BVC needs
`n ≥ (d+2)f+1` and is achieved by the paper's algorithm, given the AAD exchange primitive. In the
secondary Section 4 (Theorem 6, stated without proof), the synchronous necessity claim is false as
literally stated (likely true for the intended hull-preserving iterative class), and the
asynchronous algorithm is under-specified.

## Mistakes in the paper

* **Theorem 6, synchronous necessity, is false as stated.** Section 4 defines the restricted
  synchronous structure only as "send your vector state to everybody, then compute the new state
  as a function of the old one and the received vectors". It claims `n ≥ (d+2)f+1` is necessary
  for such algorithms. But the update function is unrestricted, and one vector of reals can encode
  any finite amount of real data. So the state can carry a full-information history. For `n = 4`,
  `d = 2`, `f = 1` (where `(d+2)f+1 = 5`), take this algorithm. In round 1, store the encoded vector
  of received inputs. In round 2, for each `k`, take the majority of the values for `k` relayed by
  the three other processes (OM(1)), then output the chosen point of `Γ`. It is a restricted
  algorithm, and it solves even *exact* BVC in two rounds. The claim presumably needs an extra
  restriction that the paper does not state, e.g. that the new state lies in the hull of the
  received states. The claim is likely true for that intended hull-preserving iterative class,
  but we formalized nothing under such a reading. Classification: under-specified definition;
  false as literally stated. Our restricted class lets the update depend on the round number `t`.
  This is harmless: in synchrony processes know `t`, and the paper's own algorithm stops after a
  fixed round. A second counterexample does not use `t` at all: inputs lie in the box `[0,1]²`,
  encodings lie outside it, so the own state tells the rounds apart.
  (`theorem_6_sync_necessity_false`, round-independent: `theorem_6_sync_necessity_false'`)
* **Theorem 6, asynchronous case: the algorithm is under-specified, and necessity is unproved.**
  The paper says Step 2 is "analogous to Section 3.2", i.e. it averages over the subsets of `B_i`
  of size `n − f`. In the restricted asynchronous structure `|B_i| = n − f`, so `Z_i` is a single
  point. Two correct processes then need not share a point of `Z`, and the paper's argument (a
  common point `z_ij`) breaks. With subsets of size `n − 3f`, or any `s` with
  `(d+1)f < s ≤ n − 3f`, the argument goes through and gives sufficiency for `n ≥ (d+4)f+1`
  (`theorem_6_async`). The paper gives no argument for the necessity of `(d+4)f+1`, and the
  objection of the previous item applies to it as well. Not formalized.
* **Theorem 4: a minor presentational gap.** In the scenario "`p_j` faulty, `p_{d+2}` correct but
  slow", validity gives the hull of `X_i^j ∪ {x_{d+2}}`, not `H(X_i^j)`. The paper's own remark
  that "`p_i` has no information about `x_{d+2}`" already implies the fix: choose `x_{d+2}` per
  scenario inside `H(X_i^j)`. Only the later sentence fixing `x_{d+2} = 0` for all scenarios is
  inconsistent with that remark: with that fixed choice and `j = d+1`, the argument gives no
  contradiction. We pick the slow group's input per scenario (`theorem_4`).
* **Degenerate cases and imprecise reductions (all minor).**
  - Theorems 1 and 4 need `n ≥ 2` (the paper assumes `n > 1`) and `d ≥ 1`. With one process, BVC is
    trivially solvable for every `f` (`ownInput_solves_of_card_one`).
  - Theorem 4 needs inputs of width `> ε`. Theorem 5 assumes known bounds `[ν, U]^d`, and with
    `U − ν ≤ ε` approximate BVC is trivial for every `n` (`ownInput_solves_of_narrow`). So the
    "necessary and sufficient" pair (Theorems 4/5) is tight only when `U − ν > ε`.
  - "`n ≤ d+1` (resp. `n ≤ d+2`) is also not sufficient — easy to see" needs a different argument
    for `n = 2`. The simulation step "f simulated processes per process" is only sketched. We use a
    direct partition of the processes into `d+1` (resp. `d+2`) groups of size `≤ f`, which covers all
    cases.
  - The `3f+1` part of Theorem 1 cites scalar consensus. The reduction (diagonal inputs) is correct.
    The classical bound needs `n ≥ 3`, and `n = 2` follows from the `(d+1)f+1` part.
  - The round count `1 + ⌈log_{1/(1−γ)}((U−ν)/ε)⌉` is meaningless for `U = ν` and negative for
    `U − ν < ε`. Read it as `1 + ⌈·⌉₊`, which works (`rounds_spec`).
* **Typos.** Section 4: "the proof of correctness … is similar to the proof of Theorem 4" should
  say Theorem 5. Section 4 says the proof relies on `|B_i ∩ B_j| ≥ (d+1)f+1`; it needs a common
  `C ⊆ B_i ∩ B_j` of the subset size used in Step 2.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Exact BVC and the lower bounds use CSLib's Byzantine message-passing model
  `Cslib.Byzantine.PartialSync`. It has a complete network of `n = |P|` deterministic state
  machines and at most `t` Byzantine processes. The adversary chooses the faulty set, the inputs,
  the Byzantine messages (which may differ per receiver) and the delivery times. Synchronous runs
  are runs with `gst = 0`; the bounded delay `δ` is arbitrary.
- "Asynchronous" lower bounds are proved in the partially synchronous model (any finite `gst`). It
  has fewer runs than the asynchronous model, and its processes have synchronized clocks, so the
  impossibility is stronger than the paper's.
- Specifications. Exact BVC uses CSLib's `SolvesConsensusSync` with
  `bvcValidity` (decision in the convex hull of the correct inputs). Approximate BVC is
  `SolvesApproxBVC`/`SolvesApproxBVCSync`: termination, `ε`-agreement in every coordinate, and
  validity, for correct inputs in a domain `K`.
- Theorem 5's algorithm is modelled on the level of round exchanges (`RoundExec`), exactly as the
  paper's proof uses them. In each round, every correct process obtains a set `B_i` of senders and
  tuple values. Byzantine values may differ per receiver. Correct senders carry their current state
  (Property 3), and at most one tuple per sender is built in (Property 2). Properties 1 and
  `|B_i| ≥ n − f` are hypotheses (`RoundExec.Valid`). **AAD's Component #1 itself (reliable
  broadcast + witnesses, from [AAD04]) is not implemented**: Theorem 5 is proved for every
  execution in which Component #1 delivers sets with Properties 1–3, as in the paper.
- The Section 4 synchronous structure is modelled directly (`RestrictedAlg`, `SyncExec`): the state
  is a vector, the update is arbitrary and may depend on the round number, and Byzantine processes
  send arbitrary vectors to each receiver.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorems 1 + 3 (characterization) | `exactBVC_sync_iff` | `Main.lean` |
| Theorem 1 | `theorem_1` (+ `approxSync_lower_bound`: `(d+1)f+1` even for approximate BVC in synchrony) | `LowerBounds.lean` |
| Theorem 2 (Tverberg) | `tverberg` (= shared `Convex.tverberg_partition`, via colorful Carathéodory `exists_colorful_mem_convexHull`, Sarkaria lifting) | `Tverberg.lean`, `Cslib/Foundations/Combinatorics/Convex/Tverberg.lean` |
| Lemma 1 | `GammaOn_nonempty` (via Helly), `GammaOn_nonempty_of_tverberg` (paper's route); tightness `gamma_empty_of_card_eq` | `Gamma.lean`, `Tverberg.lean` |
| Theorem 3 (IC + choice of a point of `Γ`) | `theorem_3`, `withGamma_solves` | `ExactAlgorithm.lean` |
| Theorem 4 | `theorem_4` | `LowerBounds.lean` |
| Theorem 5 (validity, (12), (13), rounds) | `theorem_5`, `RoundExec.state_mem_convexHull`, `RoundExec.contraction`, `RoundExec.spread`, `rounds_spec` | `Iterative.lean` |
| Theorem 6, sufficiency | `theorem_6_sync`, `theorem_6_sync_restricted`, `theorem_6_async` (subset size `n − 3f`) | `Iterative.lean`, `RestrictedSync.lean` |
| Theorem 6, sync necessity | `theorem_6_sync_necessity_false`, `theorem_6_sync_necessity_false'` (counterexamples; the second ignores the round number) | `RestrictedSync.lean` |
| Intro example | `intro_example` | `Main.lean` |

**Not formalized.**
- AAD Component #1 (Properties 1–3 are hypotheses).
- The AAD-style termination variant, the LP implementation of Step 2, and the Appendix F
  optimization (`γ = 1/n²`).
- Theorem 6 asynchronous necessity, and any repaired version of the synchronous necessity.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity checks:
- Step 1 of Theorem 3 is CSLib's verified interactive-consistency protocol
  (`icSolvableSync_of_three_t_lt`).
- `theorem_6_sync` derives `RoundExec.Valid` for synchronous exchanges, so the hypotheses of
  Theorem 5 are satisfiable.
- "Decide your own input" satisfies the approximate spec for narrow input domains
  (`ownInput_solves_of_narrow`).

The model comes from CSLib `Cslib/Computability/Distributed/Byzantine/PartialSync/` (`Model`,
`Consensus`, `Sync` with `Run.enlarge`, `Constructions` with `Run.extend`, `FLM`, `ICSync`); `withGamma` is the
decision post-processing `Algorithm.mapDecide` of the shared library `Cslib/Computability/Distributed/Byzantine/PartialSync/Map.lean`.
CSLib candidates (marked `-- CSLib candidate`):
- Tverberg's theorem and colorful Carathéodory — moved to `Cslib/Foundations/Combinatorics/Convex/Tverberg.lean`;
- `GammaOn` with Lemma 1 via Helly (`Gamma.lean`).
