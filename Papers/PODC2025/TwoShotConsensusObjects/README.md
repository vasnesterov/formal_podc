# Two-shot objects solving two-process consensus — PODC 2025

Minh Tung Nguyen, Pierre Sutra. *An Exact Characterization of the Two-shot Deterministic Objects
Solving Two-process Consensus.* PODC 2025. DOI
[10.1145/3732772.3733534](https://doi.org/10.1145/3732772.3733534). Formalized version: the PODC
proceedings version (no arXiv version found); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The main result is fully formalized. A deterministic two-shot
type `(T, m)`, together with registers, solves wait-free two-process consensus iff it lies in
`C₁ ∪ C₁.₅ ∪ C₂`. Both directions hold, and all three algorithms are correct, after fixing a
typo in Algorithm 3. The necessity proof has gaps, which we filled. The illustrating example
"the asymmetric queue AQ is in `C₁.₅`" is false: AQ is in `C₂`.

## Mistakes in the paper

* **The AQ example (§4.2.5) is false (illustration only).** The paper claims the asymmetric
  queue, where only `p₀` may dequeue, is in `C₁.₅`, with witness queue `[0]`, `f = dequeue`,
  `f' = read`, `g = enqueue(1)`, `g' = read`.
  - That witness already violates property (1): `dequeue` returns `0` whether or not
    `enqueue(1)` went first. Properties (3), (4) and (5) fail too; only (2) holds.
  - No witness exists, in any state and in either role orientation. Property (1) forces
    `g = enqueue(y)`. Properties (1) and (3) then force `g' = read`, `f = dequeue` and an empty
    queue. But then `p₁` reads `[y]` both in `gg'ff'` and in `fgg'f'`, so property (4) fails.
  - AQ is in `C₂` (with the WQ witness), so it still solves consensus. The characterization
    itself is unaffected. (`paper_AQ_witness_fails`, `aq_not_C15`, `aq_C2`)
* **Necessity proof (§6): implicit assumption that `f` and `g` are first accesses (proof gap,
  statement true).** At the critical configuration the paper treats `f` and `g` as each process's
  first call to `O`, and Lemma 5 / Proposition 1 use "the second call `f'`".
  - If `f` is `p₀`'s second call, `p₀` can never touch `O` again, so it must distinguish `fg`
    from `gf`.
  - The object is then in `C₁`, or in `C₁.₅` with alternative (5a) and an arbitrary `f'`.
  - Likewise, `p₀` may decide without calling `O` again after `fgσg'`; then (5a) holds.
  (`KSetup.dist_of_last`, `KSetup.c15`)
* **Proposition 2: the graph `G` must be bipartite (proof gap, statement true).**
  - With *operations* as nodes, an operation allowed to both processes merges a `p₀`-node with
    a `p₁`-node. A path can then switch sides there, and "`cᵢ ∈ m(p₀)` for even `i`" fails.
  - Using `(process, operation)` nodes repairs this; the reduction to fewer objects works
    unchanged.
  - The paper also writes "`n ≥ 2` even" where `n` must be odd.
  - The "minimal number of objects" argument becomes an induction on the number of copies, which
    needs finitely many copies. We prove the reduced algorithm correct and wait-free.
  (`KSetup.Adj`, `KSetup.c2_or_smaller`, `reduction`, `necessity`)
* **Lemma 4 (Algorithm 3) omits some histories (proof gap, statement true).** Its case
  analysis ignores histories where the other process applies its operations on `O` after the
  decider's reads. The Lean proof enumerates all interleavings. `k ≥ 1` is genuinely needed:
  with `N = 1`, line 23 would fire wrongly in the run `g c_N f c_{N−1}`.
  (`decide0_ok`, `decide1_ok`)
* **Typos.**
  - Algorithm 3, line 30: `v[1][1]` must be `v[0][1]`. Only `p₀` executes the line, and its
    `v[1][1]` is `⊥`. Taken literally, agreement fails in the run where `p₁` runs solo first.
    A brute-force search (Python, not in Lean) found a 4-state object in `C₂` exhibiting this.
  - Corollary 1's "`op ∈ [0, k]`" should be `[0, 3^k]`.
  - The proof of Lemma 2 is imprecise (its case `a = 0` gives `n = 3^{k-1}`, which for `n = 1`
    violates `k > 0`; it cites the "third" property of `C₂` for the pairs of property (2)); the
    padding argument is formalized.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Two deterministic processes with binary inputs; asynchronous; wait-freedom (every process
  taking infinitely many steps in an infinite schedule outputs).
* Crashes are modelled by processes that stop taking steps: CSLib
  `Cslib.SharedMemory.Recoverable` without crash events, `WFConsensus`.
* Shared objects:
  - Read/write-like objects (`ObjSpec.RWLike`, which includes registers of any value type).
  - Finitely many copies of the deterministic type `O` (the paper's "minimal number of
    objects" argument presupposes this; necessity is proved for such algorithms). Each process applies at most two
    operations to each copy in every execution (`TwoShot`), and only operations allowed by
    `m` (`Allowed`).
  - Initial states are chosen by the algorithm.
* `Solvable O m` existentially quantifies over all such algorithms (`Model.lean`). Generalizing
  registers to read/write-like objects only strengthens necessity. The algorithms use one copy of `O` and
  plain registers.
* Distinguishability (`Dist`, `DistBoth`) compares the lists of a process's responses along an
  interleaving (`view`). The classes are `C1`, `C15` (incl. role swap) and `C2`, with the paper's
  exclusions (`Defs.lean`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Characterization (Thms 1–3) | `characterization` | `Main.lean` |
| Theorem 3 (necessity) | `necessity` | `Necessity.lean` |
| Proposition 1 + Lemma 5 | `KSetup.c15` | `NecC15.lean` |
| Lemma 5 (roles of Prop. 2) | `KSetup.c34` | `NecC2Lemmas.lean` |
| Proposition 2 (edges, path) | `KSetup.edge_dist`, `KSetup.c2_of_conn`, `KSetup.c2_or_smaller` | `NecC2Lemmas.lean`, `NecC2.lean`, `Necessity.lean` |
| Prop. 2's construction (fewer objects) | `reduction` | `NecReduction.lean`, `NecReductionSim.lean` |
| §5.1 (class `C₁`) | `solvable_of_C1` | `AlgC1.lean` |
| Thm 1, Lemma 1 (Algs 1–2, class `C₁.₅`) | `solvable_of_C15Cond` | `AlgC15.lean`, `AlgC15Core.lean` |
| Thm 2, Lemmas 2–4, Cor. 1 (Alg 3, class `C₂`) | `solvable_of_C2Cond` | `AlgC2*.lean` |
| §4.2.5 examples (RQ ∈ C₁, WQ ∈ C₂, AQ ∉ C₁.₅, AQ ∈ C₂) | `rq_C1`, `wq_C2`, `aq_not_C15`, `aq_C2`, `queues_solvable` | `Examples.lean`, `Main.lean` |

**Not formalized.** Everything in the paper is formalized. Section 2's comparison with
Herlihy–Ruppert and Ruppert's classes is not, since it is discussion only.

**CSLib candidates** (generic over CSLib's `Recoverable.Alg`):
- `TwoShot`/`Allowed`, `twoShot_of_budget`, `allowed_of_inv` (`Model.lean`);
- `AgreeExcept`/`AgreeAll`, `agreeOn_two_steps` (`NecBasic.lean`);
- the object-removal `reduction` (`NecReductionSim.lean`);
- the `view`/`resps` append lemmas (`AlgC2Pad.lean`).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Sanity checks:
- The characterization is non-vacuous on both sides: the queues are solvable
  (`queues_solvable`), and objects whose operations return no information are not
  (`not_solvable_of_trivial_resp`).
- Before formalizing, Algorithms 1–2 were checked by exhaustive scheduling on random small
  objects satisfying `C₁.₅`.
- The model and the critical-configuration machinery (`exists_crit`, `Crit.poised`,
  `team_contra`) come from CSLib `Cslib/Computability/Distributed/SharedMemory/Recoverable.lean`;
  the object families `withRW`, access counts `accCount` and the generic tools `prog_of_rank`,
  `wfConsensus_of_inv` from the shared library `Podc/SharedMemory/Recoverable.lean`, and
  `ObjSpec.RWLike` from `Podc/SharedMemory/ObjClasses.lean`.
