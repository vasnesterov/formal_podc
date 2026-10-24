# Unbeatable Set Consensus — PODC 2016

Armando Castañeda, Yannai A. Gonczarowski, Yoram Moses. *Unbeatable Set Consensus via Topological and
Combinatorial Reasoning.* PODC 2016. DOI [10.1145/2933057.2933120](https://doi.org/10.1145/2933057.2933120).
Formalized version: arXiv [1605.07354](https://arxiv.org/abs/1605.07354) v1 (full version with appendices);
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The main results hold: `Optmin[k]` solves nonuniform `k`-set consensus
with decisions by `⌊f/k⌋ + 1` (Prop. 1), it is unbeatable (Thm. 1) and last-decider unbeatable (Thm. 2), and
`u-Pmin[k]` solves uniform `k`-set consensus by `min(⌊t/k⌋+1, ⌊f/k⌋+2)` (Thm. 3). But **Lemma 1, the core of
the combinatorial unbeatability proof, is false as stated.** We prove it under an extra hypothesis that holds
wherever the paper uses it, so the proof of Theorem 1 goes through.

## Mistakes in the paper

* **Lemma 1 is false as stated (false statement; Theorem 1 survives).** Lemma 1 says: in any solution in
  which low processes decide at once, a process `i` that becomes low at `m` with a single low value `v`,
  hidden capacity `≥ k − 1`, and `k` hidden processes `j_b` that are high at `m − 1` must decide `v` at
  `m`. Counterexample with `n = 6`, `k = 2`, `t = 1`, `m = 1`: `i` has input 2, two processes `x`, `y`
  have input 0, a process `z` crashes in round 1 sending nothing, and `j₁`, `j₂` have input 2. All four
  hypotheses hold for `i` at time 1 with `v = 0` (`⟨z, 0⟩` and `⟨j₁, 1⟩` witness `HC ≥ 1`). Now take
  this protocol: a low process decides its input at time 0; at time 1, a high process that missed a
  round-1 message and whose only low value is `0` decides its smallest high value, and every other
  process decides its minimum. It solves 2-set consensus for `t = 1`: whoever misses a message knows the
  unique faulty process, so `0` is held by correct processes and only one more value can be decided.
  Here `i` decides `2`. The proof fails in the "changes": when `j_{b'}` (`b' > b`) has decided `v`,
  process `j_b` must get *no* message carrying `v` in round `m`. That needs every process that told `i`
  about `v` to crash in round `m`, which can exceed `t` (here `x` and `y` would both have to crash). The
  topological proof has the same gap: it assumes that `j_y` gets low values only from the `i_x`. The
  failure does not depend on `t < k`: with `t + 1` carriers of `0`, a variant of `Optmin[k]` breaks the
  lemma for every `t ≥ 1`, `k ≥ 2` (sketch in [differencies.md](differencies.md), item 1). We
  prove Lemma 1 with an extra hypothesis 5: *every process alive and low at `m − 1` crashes in round
  `m`*. In the proof of Lemma 3, hypothesis 5 holds because `i` is still high at `m`. Inside Lemma 1's own
  induction it holds because `i` is high at `m − 1`. So Lemma 3 and Theorems 1–2 are unaffected.
  (`lemma1_paper_false`; repaired: `lemma1` with `Lemma1Hyp.lowCrash`)
* **Lemma 1, the induction step: unchecked hypotheses (proof gap, true statement).** The induction
  hypothesis is applied to the processes `i_w` "to decide `w` by time `m − 1`". Only hypothesis 3
  (`HC ≥ k − 1`) is checked. The lemma must be applied at the first time `i_w` is low, and hypothesis 4
  must be checked too. It holds: `j_1, …, j_k`, made correct, are hidden from `⟨i_w, m''⟩` and high
  before. (`lemma1_step`)
* **Lemma 5 (Appendix D), case `m = 0`: slip.** The run `r'` "with all initial values `0`" contradicts
  `r'_i(0) = r_i(0)` when `i`'s low input is not `0`. All inputs equal to `i`'s input works. (`lemma5`)
* **Theorem 3's proof writes `K_j ∃correct(w)` for "j knows that w will persist" (imprecise).** It then
  uses it as "some correct process knows `w`". That consequence needs its own argument. We prove the
  persistence claim stated after Definition 3 directly: everyone alive at `m + 1` has seen `w`. The count
  `t − d` there also needs `d` to count processes disjoint from the `t − d` carriers; we show this.
  (`persist`)
* **Small slips.** Proof of Theorem 3: "`v = Min⟨i, m′_i⟩ < k − 1`" should be `≤ k − 1`. Prop. 1 and
  Thm. 3 say "all processes decide by …"; this holds for processes alive at that time. Lemma 2 assumes `i`
  active at `m − 1`; we use `i` alive at `m`, which is all that is needed.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous message passing, `n` processes (any `Fintype`), crash failures with at most `t` crashes
  (no constraint `t < n` is needed). An adversary is CSLib's `SyncCrash.Run`: input vector, crash round,
  and the set reached in the crashing round. Inputs are naturals in a set `D ⊇ {0, …, k}`; the paper's
  `{0, …, k}` and its footnote-4 generalization are special cases.
* Full-information protocols. The communication graph `comm r` depends only on the adversary. A view is
  CSLib's full-information indistinguishability `FIIndist` on that graph (`SameView`). A protocol is a
  decision rule `dec r i m : Option ℕ` invariant under `SameView`. A process decides when the rule first
  fires while it is alive. `LockStep.lean` shows that every deterministic CSLib protocol, with arbitrary
  messages, gives such a rule with the same decision times (Coan's reduction), so Theorem 1 holds against
  all of them (`theorem1_lockStep`).
* Seen = message chain (`DynNet.Journey`). Guaranteed crashed = `⟨i, m⟩` has seen a node `⟨h, s + 1⟩`,
  `s + 1 ≤ ℓ`, that missed `j`'s round-`s + 1` message. Hidden, `HC`, `Vals`, `Min` and low follow
  Definitions 2 and 5.
* Unbeatability (Def. 1) quantifies over all solutions `Q`: `Q ⪰ Optmin ⇒ Optmin ⪰ Q`, comparing
  per-process decision times on the same adversary. Last-decider domination (Def. 6) compares the times
  by which all correct processes have decided.

**Main results in Lean.** Namespace `Podc.UnbeatableSetConsensus`.

| Paper | Lean | File |
|---|---|---|
| Protocol `Optmin[k]` | `optmin` | `Optmin.lean` |
| Prop. 1 (solves; decisions by `⌊f/k⌋+1`) | `optmin_solves`, `optmin_decidesBy` | `Optmin.lean` |
| Lemma 2 (the chain run) | `chainRun`, `ChainHyp.sameView`, `.mem_vals`, `.vals_subset`, `.hidden_col` | `Runs.lean` |
| Lemma 1, as stated: **false** | `lemma1_paper_false` | `Counterexample.lean` |
| Lemma 1, with hypothesis 5 | `lemma1` (`Lemma1Hyp`) | `Lemma1.lean` |
| Lemma 3 | `lemma3` | `Unbeatable.lean` |
| Theorem 1 (`Optmin[k]` unbeatable) | `theorem1`, `theorem1_lockStep` | `Unbeatable.lean`, `LockStep.lean` |
| Lemma 5 | `lemma5` | `Unbeatable.lean` |
| Theorem 2 (last-decider unbeatable) | `theorem2` | `Unbeatable.lean` |
| Theorem 4 (KoP), for Validity | `decided_mem_vals` | `Runs.lean` |
| Def. 3, protocol `u-Pmin[k]` | `KnowsPersist`, `uPmin` | `UPmin.lean` |
| Persistence claim after Def. 3 | `persist` | `UPmin.lean` |
| Theorem 3 (uniform; by `min(⌊t/k⌋+1, ⌊f/k⌋+2)`) | `theorem3` | `UPmin.lean` |

Other files: `Model.lean` (definitions), `Views.lean` (basic facts about views, hidden nodes and the
locality lemma `sameView_of_agree`), `LastRound.lean` (the "changes" of round `m` in Lemma 1's proof).

**Not formalized.** The topological proof of Lemma 1 (§B.1, Sperner) and Proposition 2. Conjecture 1. The
`O(n log n)`-bit implementation (Lemma 6). The comparison of `u-Pmin[k]` with earlier protocols (Fig. 4).
Remark 2, except that domination implies last-decider domination.

**Trust.** No `sorry`. `theorem1`, `theorem2`, `theorem3`, `lemma1`, `lemma1_paper_false` and
`theorem1_lockStep` use only `propext`, `Classical.choice`, `Quot.sound`. The hypotheses of the main
theorems (`1 ≤ k`, `{0, …, k} ⊆ D`) are trivially satisfiable. The counterexample protocol is proved
correct (`cexProtocol_solves`, `cexProtocol_lowDecides`). The hypotheses of the corrected Lemma 1 are
established in the proof of Lemma 3 for every high node of hidden capacity `≥ k`. Model from CSLib:
`SyncCrash.Run` (crash patterns), `DynNet.Journey`, `HeardOf.FIIndist` (views), `Byzantine.LockStep`
(general protocols).

**CSLib candidates.** The generic parts of `Views.lean` (seen nodes, the view of a `SyncCrash` run as
`FIIndist`, `sameView_of_agree`, hidden nodes and their soundness lemmas), `modify` (making processes
correct / changing last-round reach sets) and `hist_eq_of_sameView` (every `SyncCrash` protocol is a
function of the full-information view). They are marked `-- CSLib candidate` in the files.
