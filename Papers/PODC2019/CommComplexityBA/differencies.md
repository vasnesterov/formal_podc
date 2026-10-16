# Differences between the formalization and the paper

Paper: Abraham, Chan, Dolev, Nayak, Pass, Ren, Shi, *Communication Complexity of Byzantine
Agreement, Revisited*, PODC 2019, arXiv 1805.03391v4.

## Errors and gaps in the paper

1. **Theorem 4, proof: unjustified conditioning** (proof gap; statement true, proved with a better
   constant).
   - The claim `Pr[Y₁ | X₁ ∩ X₂] ≥ 1/2` does not follow from the definition of `V`, which bounds
     only the unconditional probability of `p`'s silent output.
   - `X₁ ∩ X₂` depends on `p`'s coins through `p`'s messages to `U`.
   - A union bound with the paper's constants yields only `1/4 − 3ε`, which is no contradiction.
   - Repaired in `LowerBound.lean`: we use a union bound per `p ∈ V` together with Markov's
     inequality per node. The averaging over `p` and the event `X₁` are no longer needed.
   - Result: `E ≥ 2ε·|V|·(k+1)` with `|V| = ⌈f/2⌉`, `k = ⌊f/2⌋`, hence `≥ εf²/2 ≥ (εf)²`.
2. **Theorem 13 (BB version): false for `n = 2`** (false only in a degenerate case).
   - Theorem 3 (BA) is true at `n = 2` by the classical `n ≤ 2t` argument. The BA ⇒ BB transfer
     is not formalized.
   - Lean counterexample: `theorem_13_false_n2` (`C = 1`, probability 1). It is checked against
     the restricted injecting adversary. It is also valid against the full Byzantine adversary,
     but that is argued informally only.
   - The proof needs a forever-honest node other than `S` in `W_{h,b}`, i.e. `n ≥ C + 2`.
   - We prove the theorem under `1 ≤ C` and `C + 2 ≤ n`. `C ≥ 1` is needed because `W_{c,b}`
     corrupts `S`. `C = 0` is trivial but is not covered.
   - For `3 ≤ n ≤ C + 1` the statement is presumably true by the classical `n ≤ 3t` impossibility
     for broadcast without setup, but this is not proved here.
3. **Theorem 13, proof: `Pr[A_s] ≥ p` and the speaker count of `A_r`** (proof gap; statement true).
   - The simulated copy is not an execution against any adversary.
   - In `W_{h,b}` the honest-message guarantee does not bound the real copy's speakers that the
     adversary corrupted.
   - Replaced by a first-crossing argument through the `W_c` worlds (`Protocol.not_E`), giving
     `μ(E) ≥ 1 − 2(1 − q₂)`.
4. **Theorem 13, proof: "without loss of generality `Pr[X | A_r ∩ A_s] ≥ 1/2`"** (imprecise).
   - Replaced by an explicit symmetry: the measure-preserving exchange `σ` of the two copies'
     tapes (`swapE_mp`) and `Protocol.output_S_symm`.
   - The resulting bound `E ⊆ X₀ ∪ σ⁻¹X₁` gives `μ(E) ≤ 4(1 − q₁)`.
   - General form (`theorem_13_general`): `1 ≤ 4(1 − q₁) + 2(1 − q₂)`. With `q₁ = q₂ = p` this
     reads `p ≤ 5/6`, the paper's threshold.
5. **Lemma 1 (Section 5.3) is false as stated** (false statement; not formalized).
   - The adversary can corrupt, after the fact, the `≈ (1/2+ε)λ` honest nodes that sent
     `(Vote, 1, b)`. More than `λ/2` eventually-corrupt nodes are then eligible, with probability
     close to 1.
   - The correct statement counts nodes corrupt *at mining time*. Theorems 5, 6 and 9 should use
     "honest when sending" instead of "forever-honest" / "eventually-corrupt". With that they go
     through.
6. **Theorem 7 (Section 5.3): threshold `n/2`** (proof gap; not formalized, not Lean-checked).
   - Lemma 2's statement is true. Its proof's `n_h > n/2` should be `n_h > εn`, which still
     gives `Θ(1)`.
   - The real error is Theorem 7's claim that `(1/2+ε/2)n` so-far-honest nodes have not
     terminated. The case split should be at `εn/2`.
7. **Typos.**
   - Theorem 8 and Theorem 12 say "messages" where they mean multicasts.
   - References to "Section 8" for the model should be to Section 2.

## Modelling choices (Theorems 4 and 1)

- **Randomness.** One probability space `(Ω, μ)`. Nodes may depend on all of `ω` (shared
  randomness, any setup). This is more general than the paper's private coins, so the lower bound
  is stronger.
- **Synchrony.** Lock-step rounds, infinite executions. The output is the first decision, and
  "no output" = termination failure.
- **No self-messages.** Self-messages are local computation and are not modelled.
- **Messages.** At most one message per ordered pair and round; `M` countable.
- **Regularity.** `Protocol.IsMeasurable`: `send` and `decide` are measurable in `ω` for each
  fixed history. The paper's model has no such regularity issues because executions are discrete
  ITMs. Only Markov's inequality (`cntTo` measurable) and the classification of silent outputs
  (disjoint events adding up to `≤ 1`) use it. Failure probabilities are outer measures, so the
  hypothesis "error `≤ 1 − q`" needs no measurability.
- **Adversary.**
  - Deterministic, adaptive, strongly adaptive (after-the-fact removal) *omission* adversary.
  - It observes only the communication pattern (who sends to whom), including the current round.
  - It can omit messages from or to corrupted nodes and cannot forge.
  - This is the class the paper mentions ("even under a more constrained omission adversary").
    The hypothesis is required only against it, which makes the theorem stronger.
  - The paper's adversaries are p.p.t.; ours are explicit strategies that are as efficient as the
    protocol. Computational bounds are not modelled.
- **Adversary `A`** (`deafAdv`). Nodes of `V` ignore *all* incoming messages. The paper has them
  ignore the first `f/2` messages from `U` plus all messages from `V`. The proof uses only the
  event "at most `f/2` messages reach `p`", on which both versions coincide.
- **Adversary `A'`** (`blockAdv`).
  - It blocks all `U → p` messages of a round as long as the cumulative count (including this
    round) is `≤ k`. The paper blocks "the first `f/2` attempts".
  - Our rule avoids ordering messages inside a round and corrupts at most `k` senders.
  - `p` is fixed. The paper picks `p` at random; averaging is replaced by per-node Markov.
- **Parameters.** `|V| = ⌈f/2⌉`, `k = ⌊f/2⌋`, so `|V| − 1 + k ≤ f` and `|V| + k = f < n`.
- **Statement.** There exist a sender input (for BA, an input configuration) and an adversary
  (static, corrupting `⌈f/2⌉` nodes) with `E[messages by forever-honest nodes] ≥ εf²/2`.
  Hypotheses: `f < n` and `ε ≤ 1/4`.
- **`ε ≤ 1/4`.** This hypothesis is a Lean artifact: `ENNReal.ofReal` truncates `1 − (3/4 + ε)` at
  0. In the paper, `ε > 1/4` makes the hypothesis unsatisfiable, so the statement is vacuous
  there.
- **Non-vacuity.** `SolvesBB` has a witness (`relay_solvesBB`); `SolvesBA` has none.
- **Theorem 1 (BA).** Proved directly with the same core, not via the BB reduction. Inputs:
  `V` gets `false`, `U` gets `v`, where `v` is the value that the silent `V`-nodes (input
  `false`) output with probability `≤ 1/2`.

## Modelling choices (Theorem 13)

- **No setup.** Independent private tapes `ω p ~ ν p`; the adversary has an independent fresh
  copy `ρ : P → T` with the same law. The adversary's randomness is fixed to this form, a
  restriction that strengthens the impossibility.
- **Channels.** Plain authenticated channels with *multisets* of messages per channel and round,
  so a corrupted node can deliver both its real and its simulated message to `S`.
- **Adversary.**
  - It *injects* messages on channels with a corrupted endpoint; corrupted nodes keep running the
    protocol.
  - It sees all messages of previous rounds and is non-rushing.
  - This is a restriction of the paper's Byzantine adversary.
- **Complexity.**
  - `FewSpeakers`: at most `C` forever-honest nodes ever send. This is implied by multicast
    complexity `≤ C` and covers the paper's remark on "at most `C` nodes send".
  - The BB guarantee and the complexity guarantee are separate hypotheses (each with probability
    `p`), which is weaker than a joint one.
- **Truncation rule.**
  - The adversary delivers simulated messages to `S` in round `r` iff at most `C` simulated nodes
    have spoken in rounds `≤ r`. It corrupts exactly those speakers.
  - The paper corrupts "the first `C`" speakers. Ours may stop earlier within a round, which
    needs no intra-round order and is equivalent on the event used.

## Not formalized

- Sections 4–6: the warm-up protocols, the subquadratic protocols in the `F_mine` model, and
  their Chernoff-bound analyses (Lemmas 1–4, Theorems 5–12, Corollaries 1–2).
- Section 9: cryptographic instantiation (adaptively secure VRF from NIZK and commitments).
- The BA ⇒ BB reduction of Section 2. Theorem 1 is proved directly instead.
