# Self-stabilizing Leader Election in Directed Networks — PODC 2024

Karine Altisen, Alain Cournier, Geoffrey Defalque, Stéphane Devismes. *On Self-stabilizing Leader
Election in Directed Networks.* PODC 2024. DOI
[10.1145/3662158.3662778](https://doi.org/10.1145/3662158.3662778). Formalized version: the full
version on HAL, [hal-04434345v4](https://hal.science/hal-04434345v4) (4 March 2024); numbering
follows it (v1 has the same statements and algorithms).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** **Theorem 5 is false**: the synchronous unison algorithm `U(K)` is not
self-stabilizing on *any* network with `n ≥ 2` once the smallest identifier lies in the source
component. It also fails for every identifier assignment once the source component has two
processes, e.g. on every strongly connected network with `n ≥ 2`. The dipath `0 → 1` is a concrete
case. The bug is in the input of the third instance `E` of PEL. A one-line change
(`I_E(p) = (¬p.A.M, p.Id)` instead of `(¬p.A.M, p.MI.M)`) repairs it, and with that change the
paper's proof of Theorem 5 goes through. Everything else holds. This covers C-MAI (Theorems 1 and 2,
with the bound `α + MAD + 2`), PEL (Theorem 3, with `3α + 3MAD + 6` rounds under the distributed
unfair daemon) and the impossibility (Lemma 13, Corollary 2). Both characterizations hold: leader
election (Corollary 3) and, with the repaired algorithm, synchronous unison (Corollary 5).

## Mistakes in the paper

* **Theorem 5 is false; `U(K)` (Algorithm 2 on top of PEL) does not stabilize.** Section 5.3 and the
  proofs of Lemmas 16 and 19 use that in a terminal configuration of PEL, `p.E.d = ‖ℓ, p‖`, so
  the leader `ℓ` is "the only process satisfying `E.d = 0`". The paper cites Theorem 1 for this.
  But Theorem 1 gives `p.E.d = Mind(p)`: the distance to the closest ancestor whose `E`-input
  equals the minimum `(0, mid)`. That input `I_E(q) = (¬q.A.M, q.MI.M)` equals `(0, mid)` for
  *every* `q` with `q.MI.M = mid`. This includes the whole source component (Corollary 4 and
  Lemma 14). So all these processes have `E.d = 0`, and `U-DAG` makes each of them increment its
  own clock independently. Counterexample: the 2-cycle `0 ⇄ 1` with identifiers `0, 1`, `α = 1`
  and `K = 2`. Start from a terminal configuration of PEL with clocks `(0, 1)`. Under the
  synchronous daemon the clocks alternate `(1, 0), (0, 1), …` forever. They are never equal, so
  no choice of legitimate configurations makes `U(K)` self-stabilizing. The paper's own example
  is inconsistent in the same way. In Figure 5(c), the six processes of the two triangular components have
  `E`-input `(0,4)`, yet Figure 6 shows `E.d = 0, 1, 2, 3, 4, 5` for them. We prove the failure
  for every network whose source component has two distinct processes, every `K ≥ 2`, every
  identifier assignment and every `α ≥ MAD` (`U.paper_unison_not_selfStab`; concrete instance
  `twoCycle_paper_unison_fails`). More generally, it fails as soon as two processes have only
  ancestors with identifiers `≥ mid` (`U.paper_unison_not_selfStab_gen`). So if the smallest
  identifier lies in the source component, *every* process has `E.d = 0`, and `U(K)` fails on
  every network with `n ≥ 2` (`U.paper_unison_not_selfStab_of_min`). An example is the dipath
  `0 → 1`, whose source component is a single process (`dipath_paper_unison_fails`). Severity: false statement, and an algorithm that does not work. The
  characterization of Corollary 5 survives with the fix. With `I_E(p) = (¬p.A.M, p.Id)`, PEL still
  elects `mid`: Lemma 15 holds for both inputs (`PEL.lemma15`). Moreover the leader is now the
  only process with `E.d = 0`, and `E.d` is a BFS distance from it (`U.fixed_ed`). The paper's
  Lemmas 16 and 19 then go through. We prove Theorem 5 for the repaired algorithm, with the
  claimed bound of `3α + 4MAD + 6` synchronous steps (`U.theorem5`, `U.theorem5_time`), and
  Corollary 5 (`corollary5`).
* **Theorem 4 is only cited.** The paper refers to [ACDD23] for it; we prove it directly
  (`theorem4`). Shift the configuration of one source component by one synchronous step. The two
  components never hear from each other, so their clocks stay one apart forever.
* **Small slips (statements unaffected).**
  * Lemma 10's induction claim reads "If `MinI(p) < i`"; it should be "`Mind(p) < i`".
  * Lemma 5's proof writes `q ∈ F_{i+1}(q)` for `q ∈ F_{i+1}(p)`, and Lemma 8 has `F_j(q)` for
    `F_j(p)`.
  * Lemma 9 has a stray `q` in "`Mdf_{R(α+1)} q(p)`".
  * Lemma 9 and Lemma 10 index rounds by `R(i)`, which is undefined once the (finite) execution
    has ended. This is harmless: terminal configurations are legitimate.
  * Lemma 4's limit-inferior argument is correct. We replace it by an elementary
    "freeze keys from the smallest up" induction.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Podc/AtomicState/`, reusable).
* Atomic-state model on a finite `Digraph V`. `G.Adj q p` means `p` reads `q`, i.e. `q` is a
  predecessor of `p`.
* Deterministic algorithms `next : (V → Q) → V → Q`. A process is enabled iff its action changes
  its state. The hierarchical collateral compositions `E ∘ A ∘ MI` and `U-DAG ∘ PEL` are written
  as one such function.
* **Distributed unfair daemon**: `IsRun next e S`, where each step activates a nonempty set of
  enabled processes. Executions are in the paper's `Ext∞` form: a terminal configuration repeats
  forever, so "finite" means "eventually terminal".
* **Synchronous daemon**: `e (t+1) = next (e t)`.
* Rounds follow the paper's neutralization definition. `RoundDone e S s s'` says that every
  process enabled at `s` executes or becomes disabled in `[s, s']`. Time bounds hold for every
  sequence `RoundBounds e S r` of such boundaries, a family that contains the paper's minimal
  rounds (`PaperRounds`).
* Self-stabilization (Definition 1, `SelfStab`) and silent self-stabilization (Definition 2,
  `SilentSelfStab`) are as in the paper.
* Identifiers are a separate input `ι : V → ID`, and algorithms are families indexed by `ι`. They
  are local: `IsLocal` lets a process use only the inputs and states of itself and its
  predecessors. So an algorithm must work for every assignment of unique identifiers ("insensitive
  to its inputs").
* `α` is a fixed parameter with `MADLe G α` (`α ≥ MAD`). `|IDSET| > |V|` is an injection
  `Option V ↪ ID`. Source components follow the paper's definition (maximal strongly connected
  induced subgraphs without outside predecessors).
* The impossibilities (Lemma 13, Corollaries 2 and 3) quantify over *all* deterministic local
  algorithms, with an arbitrary state type, as in the paper.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2, Lemma 3 (terminal ⇒ `MinOk`) | `CMAI.target_le_of_terminal`, `CMAI.eq_target_of_terminal` | `Correctness.lean` |
| Lemma 4 (termination, unfair daemon; generalised to eventually constant inputs) | `CMAI.Run.eventually_const` | `Termination.lean` |
| Theorem 1 (C-MAI silent self-stabilizing) | `CMAI.theorem1` | `Correctness.lean` |
| Lemmas 5–9 (fake values vanish in `α + 1` rounds) | `CMAI.fake_d_moved`, `CMAI.enabled_of_bad`, `CMAI.noFake_within` | `Rounds.lean` |
| Lemma 10, Theorem 2 (`α + MAD + 2` rounds) | `CMAI.claim_within`, `CMAI.Run.target_within`, `CMAI.theorem2` | `Rounds.lean` |
| Lemma 12 (synchronous executions agree on a source component) | `syncExec_agree` | `Podc/AtomicState/Model.lean` |
| Lemma 13, Corollary 2 (necessity for leader election) | `lemma13`, `corollary2` | `Necessity.lean` |
| Corollary 4, Lemmas 14, 15 | `PEL.corollary4`, `PEL.lemma14`, `PEL.lemma15` | `PELCorrect.lean` |
| Theorem 3 (PEL silent self-stabilizing; `3α + 3MAD + 6` rounds) | `PEL.theorem3`, `PEL.silent`, `PEL.theorem3_time` | `PELCorrect.lean`, `PEL.lean` |
| Corollary 3 (unfair / synchronous daemon) | `corollary3`, `corollary3_sync` | `Necessity.lean` |
| Theorem 4 (necessity for unison) | `theorem4` | `Unison.lean` |
| Theorem 5: **false** for the paper's `U(K)` | `U.paper_unison_not_selfStab_gen`, `U.paper_unison_not_selfStab`, `U.paper_unison_not_selfStab_of_min`, `twoCycle_paper_unison_fails`, `dipath_paper_unison_fails` | `Unison.lean`, `Examples.lean` |
| Theorem 5, Lemmas 16, 19, Corollary 6 (repaired `U(K)`, `3α + 4MAD + 6` steps) | `U.theorem5`, `U.legit_step`, `U.theorem5_time` | `Unison.lean` |
| Corollary 5 (unison iff unique source component) | `corollary5` | `Unison.lean` |

**Not formalized.**
* The generic composition results (Lemma 1, Corollary 1). We prove their instances for PEL
  directly: each layer is a C-MAI run whose inputs become constant once the lower layers have
  frozen.
* Lemma 17 (no configuration of `U(K)` is terminal).
* The space bound `O(log α + B)`. It can be read off the state types: `CState` holds a key with
  `d ≤ α`, `PState` holds three of them, and `UState` adds a clock.

**Trust.**
* No `sorry`. All listed theorems use only `propext`, `Classical.choice` and `Quot.sound`.
* Non-vacuity on the 2-cycle (`Examples.lean`): PEL and the repaired `U(K)` are proved correct
  there (`twoCycle_PEL`, `twoCycle_fixed_unison`).
* `idset_card_needed` shows that Corollary 2 needs `|IDSET| > |V|`. With exactly `|V|`
  identifiers, leader election is trivially solvable on two isolated nodes.
* The model and the digraph vocabulary (ancestors, `MAD`, source components) are in
  `Podc/AtomicState/{Digraph,Model}.lean` (CSLib candidates).
