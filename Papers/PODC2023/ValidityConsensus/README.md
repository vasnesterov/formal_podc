# On the Validity of Consensus (PODC 2023)

Pierre Civit, Seth Gilbert, Rachid Guerraoui, Jovan Komatovic, Manuel Vidigueira.
*On the Validity of Consensus.* PODC 2023, DOI 10.1145/3583668.3594567; extended version arXiv:2301.04920v3
(the version formalized; numbering below follows it).

## Status

**Complete, no `sorry`, no axioms** (all main theorems checked with `lean_verify`: only `propext`,
`Classical.choice`, `Quot.sound`). Vector consensus (used by the sufficiency direction) is a hypothesis, as
now **discharged**: `Cslib/Computability/Distributed/Byzantine/PartialSync/VC/` is a verified vector-consensus protocol for every `n > 3t`, so
the classification (`solvable_iff`) is unconditional and Theorems 3/4 are non-vacuous at optimal resilience
(`Optimal.lean`). See `differencies.md` for every deviation; the paper is
correct up to one minor proof gap (Lemma 3 for `n < 2t`, fixed) and implicit assumptions.

## Model (explicit)

Shared model `Cslib/Computability/Distributed/Byzantine/PartialSync/` (owned by this paper):

- `n = Fintype.card P` processes, at most `t` Byzantine (static, arbitrary behaviour), deterministic
  algorithms (state machines), authenticated point-to-point links, no randomness.
- **Partial synchrony**: per run, an unknown `gst`; correct-to-correct messages sent at `τ` are delivered
  in `[τ, max τ gst + δ]` (`δ` known). Discrete time; correct processes step every time unit from time 0.
- Message complexity: number of messages sent by correct processes to other processes during `[GST, ∞)`.
- Solvability (`Solvable`, `VectorConsensusSolvable`) quantifies over algorithms with message/state types
  in `Type` (universe 0); see `differencies.md`.
- Optional **ideal signatures** (`Auth`, unforgeable tokens, eavesdropping rushing adversary); every
  impossibility result is proved in the authenticated model (`*_auth`) and specialised to the plain model.

## Main results ↔ Lean

| Paper | Lean (namespace `ValidityConsensus`) | File |
|---|---|---|
| §3 model, consensus, validity property, `π(c)`, `I`, similarity `∼`, compatibility `⋄`, trivial | `Cslib.Byzantine.PartialSync.{Algorithm, Run, Run.Valid, Config, IsInputConfig, Similar, Compatible, ValidityProperty, ValidityProperty.Trivial, SolvesConsensus, ValidityProperty.Solvable}` | `Cslib/Computability/Distributed/Byzantine/PartialSync/*.lean` |
| Lemma 1 (canonical similarity) | `canonical_similarity`, `canonical_similarity_auth` | `Triviality.lean` |
| Lemma 2 (merge of compatible executions) | `eq_of_compatible`, `eq_of_compatible_auth` | `Triviality.lean` |
| Lemmas 3, 4, **Theorem 1** (`n ≤ 3t` ⇒ solvable ⇒ trivial) | `trivial_of_solvable`, `trivial_of_solvableAuth`, `trivial_of_solvesConsensus(_auth)` | `Triviality.lean` |
| **Theorem 2** | `alwaysAdmissible_computable` (see `differencies.md` §1.2) | `SimilarityComputable.lean` |
| Definition 2 (`C_S`) | `SimilarityCondition` (+ `CommonAdmissible`, `IsInputConfigExact`) | `Similarity.lean` |
| **Theorem 3** (`C_S` necessary) | `similarityCondition_of_solvable`, `similarityCondition_of_solvableAuth`; computable `Λ`: `similarityCondition_computable(_auth)` | `Similarity.lean`, `SimilarityComputable.lean` |
| Lemma 5 (pigeonhole + isolated decision), Lemma 6, Lemma 7 | `pigeonhole`, (inside) `message_lower_bound_auth`, `exists_run_decides_ne`, `eq_of_isoRun_decides` | `LowerBound.lean` |
| **Theorem 4** (`Ω(t²)`, `> ⌈t/2⌉²` messages) | `message_lower_bound(_auth)` (`≥ ⌈t/2⌉(⌈t/2⌉+1)` within finite time), `message_complexity_lower_bound(_auth)` | `LowerBound.lean` |
| Vector consensus (§5.2.1) | `SolvesVectorConsensus(Auth)`, `VectorConsensusSolvable(Auth)` (hypotheses) | `Universal.lean` |
| Algorithm 2 `Universal`, Lemma 8, **Theorem 5** | `universal`, `solvesConsensus_universal(_auth)`, `msgComplexity_universal`, `solvable_of_similarityCondition`, `solvableAuth_of_similarityCondition` | `Universal.lean` |
| Non-vacuity for `t ≥ 1` (not in the paper) | `exists_nontrivial_solvable`, `binary_message_lower_bound`, `strongValidity_similarityCondition`; protocol `Cslib.Byzantine.PartialSync.Binary.solvesConsensus` (`n ≥ 7t+1`) | `NonVacuity.lean`, `Cslib/Computability/Distributed/Byzantine/PartialSync/BinaryConsensus.lean` |
| Vector consensus at `n > 3t` (black box of §5.2, discharged) | `vectorConsensusSolvable(Auth)`; protocol `Cslib.Byzantine.PartialSync.VC.solvesVectorConsensus` | `Optimal.lean`, `Cslib/Computability/Distributed/Byzantine/PartialSync/VC/` |
| **Unconditional classification** | `solvable_iff` (all `0 < t < n`), `solvable_iff_similarityCondition'`, `solvableAuth_iff_similarityCondition'` | `Optimal.lean` |
| Binary strong-validity BA at `n > 3t`, Thm 4 instance | `universal_vc_solves`, `strongValidity_solvable_optimal`, `optimal_message_lower_bound` | `Optimal.lean` |
| Classification (Fig. 1; remark after Thm 2) | `solvable_iff_trivial`, `solvable_iff_similarityCondition`, `solvableAuth_iff_trivial`, `solvableAuth_iff_similarityCondition` | `Universal.lean` |

Generic infrastructure built for this paper (in `Cslib/Computability/Distributed/Byzantine/PartialSync/`): `Run.st_eq_of_inbox_eq`
(indistinguishability), `Run.inbox_eq_of_dlv_eq`, `canonRun`, `isoRun`, `Run.extend` (+ `extend_st`,
`extend_valid`, `extend_authValid`), `Run.tokens_replay`, `isoRun_tokens`, `Run.msgsUpTo`,
`Run.msgComplexity` (self-messages not counted), sanity example `Examples.leaderEcho_solves`, the
round layer `Rounds.lean` (`RoundAlgorithm.compile`, `Run.toRoundRun`, `toRoundRun_syncFrom`,
`decides_compile_iff`), and the verified binary BA protocol `BinaryConsensus.lean`.

## CSLib candidates

- Done: the partially synchronous model (`Model`, `Consensus`, `Constructions`, `Auth`, `Examples`), the round
  layer, `BinaryConsensus` and `VC/` moved to CSLib (`Cslib/Computability/Distributed/Byzantine/PartialSync/`,
  namespace `Cslib.Byzantine.PartialSync`, same declaration names; vasnesterov/cslib PRs #26–#29). The module
  docs there state the drift-free/awake-from-0 caveat and relate the model to CSLib's FLP model.
- `pigeonhole` (`LowerBound.lean`) is generic counting but too specialised to upstream as is.

## Token spend

Rough estimate: first pass ~0.45M (main) + ~0.11M (subagent, `SimilarityComputable.lean`); follow-up
(review fixes, signature-model computable Thm 3, round layer, binary BA protocol, non-vacuity) ~0.25M (main)
+ ~0.09M (two subagent runs). Total ≈ 0.9M of the 10M budget.

Additional CSLib candidates in `SimilarityComputable.lean`: `Algorithm.lockStep`,
`canonRun_st_eq_lockStep`, `Algorithm.IsComputable`, `Computable.finArrow_of` (generic Mathlib-level lemma).

Third pass (VC protocol at optimal resilience + unconditional classification): ~0.2M (main) + ~0.09M
(one subagent, liveness). Overall ≈ 1.25M tokens.
