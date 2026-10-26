# Communication Complexity of Byzantine Agreement, Revisited — PODC 2019

Ittai Abraham, T-H. Hubert Chan, Danny Dolev, Kartik Nayak, Rafael Pass, Ling Ren, Elaine Shi.
*Communication Complexity of Byzantine Agreement, Revisited.* PODC 2019. DOI
[10.1145/3293611.3331629](https://doi.org/10.1145/3293611.3331629). Formalized version: arXiv
[1805.03391](https://arxiv.org/abs/1805.03391) v4 (15 Feb 2020); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** Both lower bounds hold. **Theorem 4 / Theorem 1** (strongly
adaptive adversary ⇒ Ω(f²) expected messages) is true, but its proof has a probabilistic gap. We
prove it with a repaired argument and get a *better* constant, `εf²/2` instead of `(εf)²`.
**Theorem 13** (no setup ⇒ no sublinear-multicast Byzantine *broadcast*) is false for `n = 2`. It
holds when `n ≥ C + 2`, which we prove. Its BA restatement, Theorem 3, is true at `n = 2` (classical
`n ≤ 2t` argument); the BA ⇒ BB transfer is not formalized. The upper-bound sections (4–6, 9) are not formalized. In them,
Lemma 1 is false as stated, but the consistency proof survives once Lemma 1 is restated correctly.

## Mistakes in the paper

* **Theorem 4: the key conditional-probability step is unjustified (proof gap; statement
  true).** The proof conditions on `X₁ ∩ X₂`: under adversary `A`, the randomly chosen `p ∈ V`
  receives at most `f/2` messages. It then claims `Pr[Y₁ | X₁ ∩ X₂] ≥ 1/2`, "by the definition of
  `V`". But `V` only bounds the *unconditional* probability that `p`, receiving nothing, outputs
  `0`. Both that silent output and `X₁ ∩ X₂` depend on `p`'s own coins. Under `A`, `p` behaves
  honestly towards `U`, so it can reveal its coin, and `U` can then contact `p` exactly when `p`'s
  silent output would be `1`. With a plain union bound the paper's constants only give
  `Pr[Y₁ ∩ Y₂] > 1/4 - 3ε`, which is no contradiction. Our repair has two steps.
  1. For every `p ∈ V`, the event "`p` does not output `0` when silent" is covered by three
     events: failure under `A`, failure under `A'_p`, and "`U` sends `p` more than `f/2`
     messages".
  2. Markov's inequality is applied to each `p` separately, instead of the paper's
     Markov-plus-averaging step.

  This gives `E[#messages] ≥ 2ε·⌈f/2⌉·(⌊f/2⌋+1) ≥ εf²/2`. Since `ε ≤ 1/4`, this is at least the
  paper's `(εf)²`. (`theorem_4`, `theorem_4_paper`, `Protocol.core_bound`)
* **Theorem 13 (BB version) is false for `n = 2` (false only in a degenerate case).** Theorem 3,
  the BA version, is not affected: BA with `n = 2`, `t = 1` is impossible by the classical
  `n ≤ 2t` argument. Take nodes
  `{sender, S}` and `C = 1`. The sender sends its bit once, and `S` outputs what it received.
  This solves Byzantine broadcast with probability 1 against one adaptive corruption, and at most
  one node speaks. The proof needs a forever-honest node other than `S` in world `W_{h,b}`, so it
  needs `n ≥ C + 2`. We prove the theorem under `1 ≤ C`, `C + 2 ≤ n`. The counterexample is
  Lean-checked against our restricted (injecting) adversary. It is also valid against the full
  Byzantine adversary: an honest `S` can only be fooled by a corrupt sender, and then validity is
  vacuous. That part is argued informally only. (`theorem_13_false_n2`, `theorem_13`)
* **Theorem 13: "Pr[A_s] ≥ p" is unjustified, and A_r is measured wrongly (proof gap; statement
  true).** The protocol's complexity guarantee counts only messages of *honest* nodes. In
  `W_{h,b}` the adversary has corrupted the simulated speakers, so the guarantee does not bound
  the number of speakers of the whole real copy, which is what the symmetry argument needs. The
  simulated execution `A_s` is not an execution against any adversary, so no guarantee applies to
  it directly. The bound `Pr[A_r ∩ A_s] ≥ 2p − 1` is still true. We prove it with a first-crossing
  argument that uses only the worlds `W_{c,b}` and `W_{c,1−b}` (there only `S` is corrupted):
  whichever copy exceeds `C` speakers first does so identically in the corresponding `W_c` world.
  The paper's "without loss of generality `Pr[X | A_r ∩ A_s] ≥ 1/2`" is also replaced by an
  explicit symmetry. A measure-preserving exchange of the two copies' tapes maps `W_{h,0}` to
  `W_{h,1}`. Measurability is never needed. (`theorem_13_general`, `Protocol.not_E`,
  `Protocol.output_S_symm`)
* **Lemma 1 (Section 5.3) is false as stated (not formalized).** It says that, except with
  probability `exp(−Ω(λ))`, fewer than `λ/2` *eventually-corrupt* nodes are eligible for any given
  message. Counterexample: in iteration 1 all honest nodes vote for their common input `b`, and
  about `(1/2+ε)λ` eligible honest nodes send `(Vote, 1, b)`. The adaptive adversary then corrupts
  them all; its budget `f ≈ n/2 ≫ λ` allows this. These nodes become eventually-corrupt and are
  eligible, so the claim fails with probability close to 1. The proof ("each so-far-honest node
  independently has a `λ/n` probability") ignores that corruption can depend on revealed
  eligibility. The correct statement counts nodes that were *already corrupt when they mined* the
  message, which is the distinction the paper itself makes in Section 4.3. With it, Theorems 5 and
  6 go through: the node `i*` only needs to be honest when it sends `Commit`, not forever-honest.
  The same imprecision ("forever-honest" / "eventually-corrupt") appears in Theorems 5, 6 and 9.
* **Theorem 7 (Section 5.3) uses the wrong threshold (proof gap; not formalized, not
  Lean-checked).** Lemma 2's statement is true, but its proof's `n_h > n/2` is wrong: fewer than
  `n/2` terminated forever-honest nodes only gives `n_h > εn`, because there are only about
  `(1/2+ε)n` honest nodes. This still gives a `Θ(1)` probability, so Lemma 2 survives. The real
  error is in Theorem 7, which claims that
  `(1/2+ε/2)n` so-far-honest nodes have not terminated. That needs fewer than `εn/2` terminated
  honest nodes, not fewer than `n/2`. The case split should be at `εn/2`. Lemma 3 then still holds
  with probability `1 − (1−λ/n)^{εn/2} ≥ 1 − e^{−ελ/2}`.
* **Typos and small slips.**
  - Theorem 8 says "`O(λ)` messages" and Theorem 12 says "`O(λ² log Δ)` messages". Both mean
    multicasts; Theorems 7 and 11 say `O(nλ)` / `O(nλ² log Δ)` messages.
  - "Section 8 presents the model" / "for the reasons mentioned in Section 8" should refer to
    Section 2.
  - `V` must avoid the designated sender, so one needs `f/2 ≤ ⌈n/2⌉ − 1` rather than
    `f/2 < ⌈n/2⌉`. With `f < n` and `|V| = ⌈f/2⌉` it is fine.

Full list of differences (including modelling choices and minor imprecisions):
[differencies.md](differencies.md).

## The formalization

**Model for Theorems 4 and 1** (`Model.lean`).
* `n` nodes, lock-step synchronous rounds, infinite executions. Each node's output is its first
  decision.
* Randomness is one probability space `(Ω, μ)`, and nodes may use `ω` arbitrarily. This covers
  private coins, shared coins and any setup (PKI, CRS, random oracle), as the paper claims.
* The protocol is history-based: `send p x ω h q : Option M` and `decide p x ω h : Option Bool`.
* Regularity: messages are countable, and send/decide are measurable in `ω` for each fixed
  history (`Protocol.IsMeasurable`). This is needed only for Markov's inequality and for the
  classification of silent outputs.
* The adversary is a deterministic **strongly adaptive omission adversary** with budget `f`. It
  sees the communication pattern, including the current round. It then corrupts nodes and removes
  any current-round message whose sender or receiver is now corrupted (**after-the-fact
  removal**). Corrupted nodes otherwise follow the protocol.
* This is the weakest adversary class the proof needs (the paper notes the bound holds even for
  omission adversaries). Against a weaker class, "the protocol is secure" is a weaker hypothesis,
  so the lower bound is stronger.
* Failure events are measured by the outer measure.
* The expected number of messages sent by forever-honest nodes is `∫⁻ honestMsgs`.

**Model for Theorem 13** (`NoSetupModel.lean`).
* No setup: independent private tapes `ω p ~ ν p`.
* Plain authenticated channels with multisets of messages per channel and round.
* The adversary has independent fresh tapes `ρ`. It sees all past messages, corrupts adaptively
  (at most `C` nodes), and **injects** extra messages on channels with a corrupted endpoint.
  Corrupted nodes keep running the protocol.
* This is a restriction of the paper's Byzantine adversary, which makes the impossibility
  stronger.
* Complexity is "at most `C` forever-honest nodes ever speak". Multicast complexity `≤ C`
  implies it.
* We assume the BB guarantee and the complexity guarantee hold separately, each with probability
  `p`. This is weaker than assuming them jointly.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 4 (BB, `ε f²/2 ≥ (εf)²`) | `theorem_4`, `theorem_4_paper` | `Theorem4.lean` |
| Theorem 1 (BA) | `theorem_1` | `Theorem4.lean` |
| Core of the proof of Theorem 4 (any `V`, `k`, `δ`) | `Protocol.core_bound` | `LowerBound.lean` |
| Indistinguishability of `A` and `A'` | `Protocol.deaf_run_eq_block_run` | `Adversaries.lean` |
| Theorem 13 (BB; `n ≥ C+2`) | `NoSetup.theorem_13`, `NoSetup.theorem_13_general` | `Theorem13.lean` |
| Theorem 13 (BB) false for `n = 2` (restricted adversary) | `NoSetup.theorem_13_false_n2` | `NoSetupCounterexample.lean` |
| Non-vacuity of `SolvesBB` (`n = 3`, `f = 1`, probability 1) | `relay_solvesBB` | `NonVacuity.lean` |

**Not formalized.**
* Sections 4–6: the subquadratic protocols with `F_mine`, their Chernoff-bound analysis, and
  Lemmas 1–4 and Theorems 5–12.
* Section 9: VRF/NIZK instantiation.
* Computational aspects (p.p.t. adversaries). Our adversaries are explicit and simulate only the
  protocol itself.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The hypotheses of Theorem 4 are satisfiable non-trivially: a send-and-relay
protocol solves BB with probability 1 for `n = 3`, `f = 1` (`relay_solvesBB`). The `n = 2`
counterexample shows that the Theorem 13 definitions are satisfiable. Not covered:
* There is no non-vacuity witness for `SolvesBA` (Theorem 1's hypothesis).
* `C = 0` is excluded from `theorem_13`; that case is trivial but not proved.

The hypothesis `ε ≤ 1/4` of `theorem_4` / `theorem_1` is not an issue in the paper: for `ε > 1/4`
the paper's hypothesis is unsatisfiable. It is needed in Lean only because `ENNReal.ofReal`
truncates negative numbers at 0. The models are paper-local; inboxes, histories and the first decision
(`firstSome?`) are those of CSLib's lock-step model (`Cslib/Computability/Distributed/Byzantine/LockStep/Parallel.lean`).

**CSLib candidates.**
* `FiberMeas` (measurability of countable-valued functions via fibres) (`Basic.lean`).
* The randomized synchronous protocol / adaptive omission adversary model (`Model.lean`).
* The measure-preserving tape exchange `swapE` (`Theorem13.lean`).
