# Differences between the formalization and the paper

Paper: Civit, Gilbert, Guerraoui, Komatovic, Paramonov, Vidigueira, *All Byzantine Agreement
Problems Are Expensive*, PODC 2024 (arXiv:2311.08060v2). Numbering follows the arXiv version.

**Summary.**
- The main result (Theorems 1–3: `Ω(t²)` messages for every non-trivial problem, even in
  synchrony) is **correct**. We prove it for all `t < n` with an explicit `t²/32`.
- **Lemma 10 and the unauthenticated part of Theorem 4 are false for `n = 2, t = 1`.** This is
  proved in Lean and corrected.
- The rest are imprecisions, implicit assumptions and generalizations.

## 1. Errors in the paper

1. **Lemma 10 / Theorem 4 (unauthenticated) fail for `n = 2`, `t = 1`.**
   - **The claims.** Lemma 10: "if `P` is unauthenticated-solvable with `n ≤ 3t`, then `P` is
     trivial". Theorem 4: "a non-trivial `P` is unauthenticated-solvable iff CC and `n > 3t`". Both
     rely on the citation "[55]: weak consensus is unauthenticated-solvable only if `n > 3t`".
   - **The counterexample.** For `n = 2, t = 1`, every execution with a fault has a single correct
     process, so Agreement only constrains fault-free executions. Weak consensus is therefore
     solvable: exchange proposals and decide the common one if both are equal, a default otherwise.
     Interactive consistency is solvable in the same way.
   - **In Lean.**
     - The protocol is `ic2`, with `ic2_solves`: IC in synchrony whenever `t = 0 ∨ n ≤ 2`.
     - `lemma10_counterexample`: weak validity on `Fin 2` is non-trivial and
       unauthenticated-solvable with `t = 1`.
     - `not_lemma10`.
     - `theorem4_unauth_as_stated_false`.
   - **Why the citation fails.** The FLM argument needs three non-empty groups of size `≤ t`, i.e.
     `n ≥ 3`. Our FLM theorem `weakValidity_not_solvableSync` assumes `3 ≤ n ≤ 3t`.
   - **Corrected statements.**
     - `trivial_of_solvableSync`: Lemma 10 under `3 ≤ n`.
     - `theorem4_unauth'`: a non-trivial problem is unauthenticated-solvable iff CC ∧
       (`n > 3t` ∨ `n ≤ 2`).
   - **Scope.** The error does not affect the lower bound or the authenticated part of Theorem 4.
2. **Lemma 1 is only proved for `t ≥ 8` divisible by 8** ("without loss of generality").
   - For other `t` the group sizes `t/4`, `t/2` must be rounded.
   - We prove the bound for every `t < n` with explicit parameters. Under `2β ≤ t`,
     `2β + σ ≤ t + 2` and `2β + σ ≤ n`, the bound is `⌈β/2⌉·σ` messages (`omission_lower_bound`).
     With `β = 2⌊t/8⌋` and `σ = t + 1 − 2β` this gives `t² ≤ 32·msgs` for `t ≥ 8`
     (`exists_params`). For `2 ≤ t < 8` we take `β = 1`.
   - For `t = 1`, `β ≥ 1` is impossible. We add a separate zero-message argument (`one_message`):
     if no messages are ever exchanged, each process decides as in isolation, which contradicts
     Agreement in a mixed fault-free execution.
   - The paper's pigeonhole loses a factor 2: `|Y|/2 · t/2 = t²/16`. Our parametric bound is about
     `t²/16`.

## 2. Model

1. **Synchrony** is the shared partially synchronous model restricted to `gst = 0`
   (`SolvesConsensusAuthSync`).
   - Delays are bounded by `δ`, and `δ = 0` is exactly the paper's lock-step round model.
   - The lower bounds, Lemma 7, Lemma 8, Lemma 9, FLM and IC hold for every `δ`.
   - **Algorithm 1 (Lemma 6, Lemma 18) is proved for `δ = 0` only.** It needs the fault-free
     execution to be determined by the proposals ("every fully correct execution is completely
     determined by the proposal of processes", App. C). This is false when the adversary can choose
     delays in `[0, δ]`. It does not matter for the lower bound: we prove Theorem 3 directly in the
     omission model, for all `δ`.
   - Lemma 10 is reduced to `δ = 0` by monotonicity (`SolvableSync.mono_delta`).
2. **Discrete time, batches.** Messages are lists, delivered in batches (one per sender, receiver
   and time).
   - A message in the paper is one list element. We do not need the paper's "at most one message per
     receiver per round".
   - Messages to oneself exist but are not counted, and they are never omitted.
3. **Omission model** (`OmExec`).
   - An execution consists of the inputs and the predicate "batch delivered". The faulty set `F` is
     not part of the execution: it is admissible if every omitted non-empty batch has an endpoint
     in `F`.
   - The paper's distinction between send- and receive-omissions disappears. Its `swap_omission`
     (Lemma 15) becomes "the same execution with another admissible faulty set"
     (`OmExec.Admits.swap`), and indistinguishability is then literally equality of executions.
   - Faulty processes are "unaware of being faulty" by construction.
4. **Message complexity** is defined as in the paper: messages sent by correct processes from
   time 0.
   - Results have the form "∃ valid run with `gst = 0` and a finite `N` with
     `t² ≤ 32 · msgsUpTo N`". There is also an `ℕ∞` form, `message_complexity_lower_bound_auth`.
   - Omitted batches sent by correct processes count, as in the paper.
5. **Signatures** are ideal tokens (as in the 2023 formalization).
   - All lower bounds are proved in the authenticated model and specialized with `Auth.none`.
   - The omission simulation respects unforgeability (`toRun_authValid`).
   - Lemma 7's construction ("same execution, fewer correct processes") respects unforgeability
     (`Run.enlarge_authValid`).
6. **Universes.** `Solvable(Auth)Sync` quantifies over message, state and token types in `Type`.
   The positive results (IC protocols, Theorem 4) are stated for `P VI : Type`.

## 3. Statements that differ from the paper (generalizations or precisions)

- **Lemma 1 / Theorem 2.** Weak validity is formalized for any value type (`weakValidity P V`).
  The binary case is used for Theorem 2.
  - The core theorem (`omission_lower_bound`) needs only Termination and Agreement, plus two input
    vectors whose fault-free executions decide differently.
  - This directly gives Corollary 1, and Theorem 3 without going through Algorithm 1.
- **Lemma 2.**
  - The hypotheses are generalized: `|F| + σ ≤ t + 2` and `σ ≤ n − |F|`, instead of
    `|Y| = t/4`, `|Z| ≤ t/4`, `σ = t/2`.
  - The isolation hypothesis is replaced by "members of `Y` only omit batches to `F`".
  - The conclusion is strengthened: the majority decides `b_X` and nothing else. Faulty processes
    could otherwise "change their mind", since decisions are read off states.
- **Definition 2 / Lemma 3 (mergeable).** Mergeability is one-sided: `k₁ = 0` or (same inputs and
  `k₁ ≤ k₂ + 1`) for the first group, and symmetrically for the second. This covers both cases of
  the paper. Time `k` here is the paper's round `k + 1`.
- **The "without loss of generality, the default is 1"** before Lemma 4 is made explicit. If the
  default equals the fault-free decision for inputs `x₀`, the same chain argument is run with
  inputs `x₁` and the roles of `B` and `C` swapped.
- **Lemma 7** is proved for arbitrary synchronous executions, authenticated, via
  `Run.enlarge_authValid`. In the omission model it is immediate, because admissibility is monotone
  in `F`.
- **Corollary 1** is stated for any validity property, not only External Validity. The hypothesis
  is two lock-step fault-free executions (`ffRun`) deciding differently. The formalism cannot
  express the "learning a transaction" aspect of External Validity, and it is not needed.
- **Definition 3 (CC)** is defined for all problems; the paper defines it for non-trivial ones only.
  The paper requires `Γ` Turing-computable.
  - The general Lemma 8 gives some `Γ`.
  - `Γ` is computable if the algorithm is computable (`containmentConditionComputable_of_…`,
    processes `Fin n`, `Primcodable` types).
  - As in the 2023 paper, "A computes it" only makes sense for computable algorithms.
  - Theorem 4 uses the non-computable CC (sufficiency also works with non-computable `Γ`).
- **Lemma 8 and Theorem 5** need `t < n` (the paper assumes `t ∈ [1, n−1]`), and `[Nonempty VI]`.
- **Theorem 5.** The paper says "without loss of generality `n = 2t`". We split `P` explicitly into
  `n − t` and `t` processes, so the proof works for every `n ≤ 2t`. It is binary strong validity.
- **Lemma 9.** Interactive consistency is not a black box: it is discharged by verified protocols.
  These are not the cited algorithms.
  - Authenticated, any `t`: `n` parallel Dolev–Strong broadcasts that relay every new valid chain,
    with no "at most 2 values" optimization, and decide `Classical.epsilon` of the accepted set
    (`DolevStrong.lean`).
  - Unauthenticated, `n > 3t`: one exchange round, then the verified PBFT-style vector consensus
    `VC` of the 2023 formalization, then a per-index majority (`ICSync.lean`).
  - Their message complexity is not analysed.
- **FLM [55]** is proved via an infinite line of copies instead of a ring (`FLM.lean`).
- **Weak validity CC** (`weakValidity_containmentCondition`) needs `P` nonempty.

## 4. Not formalized

- Figures, §6 (related work) and §7 (conclusion).
- The randomized-setting remarks.
- Complexity bounds of the cited protocols.
