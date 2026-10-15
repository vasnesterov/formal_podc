# All Byzantine Agreement Problems Are Expensive (PODC 2024)

Pierre Civit, Seth Gilbert, Rachid Guerraoui, Jovan Komatovic, Anton Paramonov, Manuel Vidigueira.
*All Byzantine Agreement Problems Are Expensive.* PODC 2024, DOI 10.1145/3662158.3662780.
Formalized version: **arXiv:2311.08060v2** (15 Nov 2023; title checked), local copy
`papers/2024/3662158.3662780_All_Byzantine_Agreement_Problems_Are_Expensive.pdf` (from arXiv, see
`papers/2024/index.json`). Numbering below follows the arXiv version. Companion of *On the Validity of
Consensus* (PODC 2023, `Papers/PODC2023/ValidityConsensus/`).

## Status

**Complete. No `sorry`, no axioms.** All main theorems were checked with `lean_verify`; the only
axioms are `propext`, `Classical.choice` and `Quot.sound`. The modules build with
`lake build Papers.PODC2024.AllBAExpensive.Theorem4 Papers.PODC2024.AllBAExpensive.LowerBound`.

The paper's main result is correct. We prove it for every `t < n` (`t² ≤ 32 · #messages`), in the
Byzantine model with or without signatures, and also in the omission model.

**Error found.** Lemma 10 is false for `n = 2, t = 1`, and so is the unauthenticated part of
Theorem 4. The paper says: unauthenticated-solvable with `n ≤ 3t` ⇒ trivial. But for `n = 2, t = 1`,
weak consensus is non-trivial and unauthenticated-solvable. The cited FLM impossibility needs
`n ≥ 3`. The Lean counterexample is `lemma10_counterexample`, and the corrected Theorem 4 is
`theorem4_unauth'`. See `differencies.md`.

The interactive-consistency black boxes the paper cites are discharged by verified protocols.
The FLM impossibility it cites is proved. So Theorem 4 (corrected) is **unconditional**.

## Model (explicit)

Shared model `Cslib/Computability/Distributed/Byzantine/PartialSync/`, restricted to **synchrony**:

- `n = |P|` processes, at most `t < n` Byzantine (static adversary, arbitrary behaviour), deterministic
  state machines, authenticated point-to-point links.
- **Synchronous runs** are the runs with `gst = 0`. Messages between correct processes are delivered
  within `[τ, τ + δ]`, and `δ = 0` is the paper's lock-step round model.
  - `SolvesConsensusAuthSync Au t δ A val` (`Cslib/Computability/Distributed/Byzantine/PartialSync/Sync.lean`) is the spec:
    Termination, Agreement and Validity in every valid run with `gst = 0`.
  - The lower bounds hold for every `δ`. Their witnesses have zero delays.
  - The reduction algorithm (Algorithm 1) is stated for `δ = 0`.
- **Message complexity**: messages sent by correct processes to other processes during the whole
  execution. Formally this is `Run.msgsUpTo` from time `gst = 0`, with `Run.msgComplexity` the
  supremum in `ℕ∞`.
- **Omission model** (`Cslib/Computability/Distributed/Byzantine/PartialSync/Omission.lean`, `OmExec`): a lock-step synchronous
  execution in which some batches are omitted. A set `F` is admissible if every omitted non-empty
  batch has an endpoint in `F`. Omission executions are simulated by Byzantine runs (`toRun`), so
  omission lower bounds transfer.
- **Signatures**: ideal unforgeable tokens (`Auth`, `Algorithm.Unforging`, `Run.AuthValid`). Every
  lower bound is proved with signatures. The unauthenticated case is `Auth.none`.

## Main results ↔ Lean

The namespace is `AllBAExpensive` unless noted; files are in this folder unless noted.

| Paper | Lean | File |
|---|---|---|
| §2 model, synchronous solvability | `Cslib.Byzantine.PartialSync.{SolvesConsensusAuthSync, SolvesConsensusSync, ValidityProperty.SolvableSync, SolvableAuthSync}` | `…/PartialSync/Sync.lean` |
| §3 omission model, indistinguishability | `Cslib.Byzantine.PartialSync.{OmExec, OmExec.Admits, OmSolves, OmExec.st_eq_of_inbox_eq}`; Byzantine solutions are omission solutions: `SolvesConsensusAuthSync.omSolves` | `…/PartialSync/Omission.lean` |
| Definition 1 (isolation) | `isoExec x G k H k'` (two groups isolated from times `k`, `k'`), `ffExec` | `WeakLowerBound.lean` |
| Lemma 15 (`swap_omission`) | `Cslib.Byzantine.PartialSync.OmExec.Admits.swap` | `…/PartialSync/Omission.lean` |
| Lemma 16 (`merge`) | `merge_st`, `merge_decides` | `WeakLowerBound.lean` |
| Lemma 2 | `lemma2` | `WeakLowerBound.lean` |
| Definition 2 + Lemma 3 | `lemma3` (generalized mergeability) | `WeakLowerBound.lean` |
| Lemmas 4, 5 | `chain` | `WeakLowerBound.lean` |
| **Lemma 1** | `omission_lower_bound` (parametric: `⌈β/2⌉·σ` messages), `omission_lower_bound_sq` (`t² ≤ 32·msgs`, all `t < n`), `weak_consensus_lower_bound_om` | `WeakLowerBound.lean`, `LowerBound.lean` |
| **Theorem 2** (weak consensus) | `weak_consensus_lower_bound(_auth)` | `LowerBound.lean` |
| Lemma 7 (containment) | `containment(_auth)` (any execution; uses `Run.enlarge`), `ff_mem_val` (omission model) | `Containment.lean`, `LowerBound.lean` |
| Algorithm 1, Table 2, Lemmas 17, 18, **Lemma 6** | `weakReduction`, `exists_reduction_data`, `weakReduction_solves`, `msgsUpTo_weakReduction`, `weakConsensus_solvable(Auth)Sync_of` | `Reduction.lean` |
| **Theorems 1 and 3** | `message_lower_bound(_auth)`, `message_complexity_lower_bound_auth`, omission version `message_lower_bound_om` | `LowerBound.lean` |
| **Corollary 1** (External Validity) | `external_validity_lower_bound(_auth)` | `LowerBound.lean` |
| Definition 3 (CC) | `ContainmentCondition`, computable: `ContainmentConditionComputable` | `Solvability.lean` |
| Lemma 8 | `containmentCondition_of_solvesConsensusAuthSync`, `…_of_solvable(Auth)Sync`, computable: `containmentConditionComputable_of_solvesConsensus(Auth)Sync` | `Solvability.lean` |
| IC, IC-Validity | `Cslib.Byzantine.PartialSync.icValidity`, `ICSolvableSync`, `ICSolvableAuthSync` | `…/PartialSync/Sync.lean`, `Solvability.lean` |
| Algorithm 2, **Lemma 9** | `reduction`, `solvesConsensusAuthSync_reduction`, `solvable(Auth)Sync_of_containmentCondition` | `Solvability.lean` |
| [52] Dolev–Strong (cited) | `Cslib.Byzantine.PartialSync.icSolvableAuthSync_dolevStrong` (verified, any `t`) | `…/PartialSync/DolevStrong.lean`, `RoundAuth.lean` |
| [55, 78] IC for `n > 3t` (cited) | `Cslib.Byzantine.PartialSync.icSolvableSync_of_three_t_lt` (verified: exchange round + the verified VC protocol + majority) | `…/PartialSync/ICSync.lean`, `RoundSeq.lean` |
| [55] FLM weak consensus impossibility (cited) | `Cslib.Byzantine.PartialSync.weakValidity_not_solvableSync` (**needs `3 ≤ n`**) | `…/PartialSync/FLM.lean` |
| **Lemma 10** | corrected: `trivial_of_solvableSync` (`3 ≤ n ≤ 3t`); counterexample: `lemma10_counterexample`, `not_lemma10`, protocol `ic2`, `ic2_solves` | `Theorem4.lean`, `Solvability.lean` |
| **Theorem 4** | `theorem4_auth'` (auth: solvable ⇔ CC); `theorem4_unauth'` (corrected: ⇔ CC ∧ (`n > 3t` ∨ `n ≤ 2`)); paper's version false: `theorem4_unauth_as_stated_false`; conditional versions `theorem4_auth`, `theorem4_unauth` | `Theorem4.lean` |
| **Theorem 5** (strong consensus, `n ≤ 2t`) | `strongValidity_not_containmentCondition`, `strongValidity_not_solvableAuthSync` | `Solvability.lean` |
| Relation to PODC 2023 Thm 4 | `message_lower_bound_psync(_auth)` | `Theorem4.lean` |

## Relation to *On the Validity of Consensus* (PODC 2023), Theorem 4

- **2023, Thm 4** (`ValidityConsensus.message_lower_bound(_auth)`): an algorithm solving a
  non-trivial `val` in **partial synchrony** has a run with `gst = 0` and at least
  `⌈t/2⌉(⌈t/2⌉+1) > t²/4` messages. The proof is Dolev–Reischuk style. It uses asynchrony in two
  places:
  - Theorem 1 of that paper (`n ≤ 3t` ⇒ trivial, which fails in synchrony with signatures);
  - delaying processes past `gst` (Lemma 6 there, with `Run.extend`).
- **2024, Thm 3** (`message_lower_bound(_auth)`) assumes only that `A` solves `val` **in synchrony**,
  a strictly weaker hypothesis (`SolvesConsensusAuth.sync`). It covers e.g. authenticated
  algorithms with `n ≤ 3t`, which do not exist in partial synchrony for non-trivial problems. It
  also holds for omission-only adversaries. The price is the constant: `t²/32` (paper), about
  `t²/16` with our parameters (`omission_lower_bound`), against `t²/4`.
- So 2024 ⇒ 2023 up to the constant: see `message_lower_bound_psync(_auth)`. Both conclusions count
  messages from time 0 with `gst = 0`.
- Validity side: in partial synchrony a decision must be admissible for all *similar* configurations
  (2023 Lemma 1, condition `C_S`). In synchrony it must be admissible only for all *contained*
  configurations (Lemma 7, condition CC). Containment between input configurations implies
  similarity, which is why synchrony admits more solvable problems. We did not formalize a direct
  implication between `C_S` and CC.

## Infrastructure built (shared, `Cslib/Computability/Distributed/Byzantine/PartialSync/`)

- `Sync.lean` (by us):
  - synchronous specifications and solvability;
  - `Contains`, `weakValidity`, `icValidity`;
  - `Run.enlarge` (replay with more Byzantine processes) with `enlarge_authValid` (unforgeability
    is preserved);
  - `Run.inbox_of_dl_eq`;
  - monotonicity in `δ`.
- `Omission.lean` (by us):
  - synchronous omission executions, admissible fault sets, swapping omissions;
  - the counting lemma `count_pairs`;
  - simulation by Byzantine runs (`toRun_st`, `toRun_valid`, `toRun_authValid`, `toRun_msgsUpTo`);
  - `OmSolves`.
- `FLM.lean` (subagent):
  - covering systems `CoverSystem` with the covering lemma `st_run` and locality `st_map`;
  - the line construction;
  - FLM for weak consensus.
- `RoundSeq.lean` (subagent): sequential composition of round algorithms, `RoundAlgorithm.seq`.
- `ICSync.lean` (subagent): IC for `n > 3t`.
- `RoundAuth.lean` (subagent): signatures in the round layer; `compile_unforging`,
  `toRoundRun_authValid`, `tokens_origin`.
- `DolevStrong.lean` (subagent): `n` parallel Dolev–Strong broadcasts, giving IC with signatures
  for every `t`.

## CSLib candidates

- Done: `Sync`, `Omission`, `FLM`, `RoundSeq`, `RoundAuth`, `DolevStrong`, `ICSync` moved to CSLib
  (`Cslib/Computability/Distributed/Byzantine/PartialSync/`, namespace `Cslib.Byzantine.PartialSync`, same
  declaration names; vasnesterov/cslib PRs #27, #30, #33, #34, #35).

## Token spend (rough)

- Main agent: about 0.5M.
- Subagents: FLM about 0.1M, Section 5 about 0.15M, Dolev–Strong about 0.13M, IC for `n > 3t` about
  0.12M.
- Total: about **1.0M** of the 10M budget.
