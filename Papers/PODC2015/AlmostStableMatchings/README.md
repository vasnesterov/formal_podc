# Fast Distributed Almost Stable Matchings — PODC 2015

Rafail Ostrovsky, Will Rosenbaum. *Fast Distributed Almost Stable Matchings.* PODC 2015. DOI
[10.1145/2767386.2767424](https://doi.org/10.1145/2767386.2767424). Formalized version: arXiv
[1408.2782](https://arxiv.org/abs/1408.2782) v2; numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Proof repaired.** Theorem 4.1 is true with the paper's constants: for every maximal-matching
subroutine, the deterministic algorithm ASM outputs a matching with at most `ε|E|` blocking pairs. Theorem 4.7
(`O(ε⁻³ log⁵ n)` rounds given an `O(log⁴ n)`-round subroutine) is also true, as an explicit round count
(no CONGEST message semantics). All lemmas of §§3–4 hold. The proof of
Lemma 4.4 has a real gap: it overlooks men who become bad while inactive. We closed it with a different charging
argument that gives the same bound.

## Mistakes in the paper

* **Proof of Lemma 4.4: men can become bad while inactive (proof gap, statement true).** The proof charges each man
  who is bad at the end to the set `B_i` of men that became bad in outer iteration `i` with `|Q^m| < 2^i`. It then
  bounds these sets with Lemma 4.5, which only counts the men *active* in iteration `i`. But a man can be matched
  when he leaves the active set and be displaced later. An active man proposes to his partner, she accepts the
  better proposal and rejects him. He then never proposes again and stays bad with a nonempty list. The
  application of Lemma 4.5 does not cover such men. The construction of the sets `H_i` and inequality (2) are not
  justified either.
  *Concrete run* (5 men, 5 women, `k = 2`, `ℓ = 1`, iterations 0–2, greedy maximal matching):
  1. In iteration 1, man 3 displaces man 0, who ends the iteration unmatched with `|Q| = 4`.
  2. In iteration 2 only man 0 is active. He proposes to woman 3 and displaces man 2, who is inactive (`|Q| = 3`).
  3. Man 2 ends bad without ever having been bad while active.

  We found no such run with the paper's parameters (`ℓ = 16k/ε`) by random search. Those parameters make bad active
  men rare, but the argument does not rule such runs out.
  *Our repair.* The number of unmatched men never increases. Hence the inactive men displaced in iteration `j` are at
  most the bad active men at the *start* of iteration `j`, i.e. at the end of iteration `j − 1`, and each has
  `|Q| < 2^j`. A per-man potential (`2^j` if matched, `|Q^m|` if not) shows that inactive men gain nothing else. This
  gives `∑_{m bad} |Q^m| ≤ ∑_i 2^{i+1} b_i`, where `b_i` is the number of bad active men at the end of iteration `i`.
  With Lemma 4.5 this yields Lemma 4.4's bound `4δ|E|` for every `δ > 0` (the paper needs `δ ≤ 1/2`).
  (`Example.bad_while_inactive`; repaired: `sum_bad_card_le`, `lemma_4_4`)
* **Proof of Lemma 4.5: a small missing step.** "The number of matched players can only increase, hence the number
  of good players can only increase" is applied to the *active* men. Individual active men can lose their partners,
  so the count needs two facts: inactive men are never newly matched, and the number of matched men equals the number
  of matched women, which is monotone. The statement is true. (`card_bad_act_le`, `lemma_4_5`)
* **Under-specified details** (we fixed natural readings):
  - The rounding of the quantile sizes `deg v / k` is not given. We use `⌈k · rank / deg⌉`.
  - Algorithm 3 has *every* processor test `|Q| ≥ 2^i`. Only the men can be meant: women and inactive men must still
    react to proposals and rejections.
  - `P^v(∅) = deg v + 1` in Definition 2.3 is introduced only inside the proof of Lemma 4.3.
* **Typos.**
  - Display (1) in Lemma 4.3 has the rank differences reversed (it should be `P^m(p(m)) − P^m(w) < 2deg(m)/k`).
  - The proof of Lemma 4.2 ends with "ε-blocking" for "(2/k)-blocking".
  - In §3.1 the men's quantiles are described as sets of "men".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous, deterministic, no failures. Men `M` and women `W` are arbitrary finite types with symmetric
  incomplete preference lists. The communication graph is the set `E` of mutually acceptable pairs.
* The state is updated once per `ProposalRound`, through local rules. A man stores `Q`, `p` and `A`; a woman stores
  her partner. Each node's update depends only on its own state, one-bit `PROPOSE`/`ACCEPT`/`REJECT` messages from
  its neighbours, and its own partner in `M₀`. There is no formal CONGEST message-passing semantics.
* `MaximalMatching` (Theorem 2.7) is a black box `MMOracle`: any function returning a maximal matching of every
  bipartite graph, with a round count. All results hold for every oracle, so for every deterministic subroutine.
* The parameters are the paper's: `k = ⌈8/ε⌉`, `ℓ = ⌈2k/δ⌉` with `δ = ε/8`, and outer iterations
  `0, …, ⌊log₂ n⌋`, where `n` bounds the degrees. A general version holds for any `k`, `ℓ`, `L`.
* Theorem 4.7 is proved for an explicit round count: ASM is run with a round counter that charges `3` one-bit
  rounds per `ProposalRound` plus the subroutine's `T` rounds (local steps are free). The counter ends at
  `(L+1) · ℓ · k · (3 + T)` (`stageC_asm`), which is `O(ε⁻³ log⁵ n)` for `T = O(log⁴ n)`. This is a cost
  accounting, not a CONGEST execution: message sizes and the subroutine's implementation are not modelled.

**Main results in Lean.** Namespace `Papers.PODC2015.AlmostStableMatchings.Prefs` unless stated otherwise.

| Paper | Lean | File |
|---|---|---|
| Definition 2.1, 2.3 (blocking pairs, `(1−ε)`-stability, `ε`-blocking) | `IsBlocking`, `IsAlmostStable`, `IsEpsBlocking` | `Prefs.lean` |
| Algorithms 1–3 (ProposalRound, QuantileMatch, ASM) | `prStep`, `quantileMatch`, `outer`, `asm`, `ASM` | `Algorithm.lean` |
| Lemma 3.1 (monotonicity) | `lemma_3_1` | `Invariants.lean` |
| Lemma 3.2 (QuantileMatch guarantee) | `lemma_3_2` | `Invariants.lean` |
| Lemma 4.2 (good men are in no `(2/k)`-blocking pair) | `lemma_4_2`, `lemma_4_2_4_6` | `Main.lean` |
| Lemma 4.3 (≤ `4|E|/k` non-`(2/k)`-blocking blocking pairs) | `lemma_4_3` | `Prefs.lean` |
| Lemma 4.4 (bad men contribute ≤ `4δ|E|`) | `lemma_4_4` (core: `sum_bad_card_le`) | `Main.lean`, `BadMen.lean` |
| Lemma 4.5 (few bad active men) | `lemma_4_5` | `Counting.lean` |
| Lemma 4.6 (a bad man's `(2/k)`-blocking partners lie in `Q^m`) | `lemma_4_2_4_6`, `card_strongBlocking_le` | `Main.lean` |
| Theorem 4.1 (`(1−ε)`-stable output) | `theorem_4_1` (general: `blocking_le`) | `Main.lean` |
| Theorem 4.7 (`O(ε⁻³ log⁵ n)` rounds) | `theorem_4_7_run` (arithmetic: `theorem_4_7`; call count: `stageC_asm`) | `Main.lean` |
| Gap in the proof of Lemma 4.4 | `Example.bad_while_inactive` | `Example.lean` |

**Not formalized.**
* The randomized variants (Theorems 5.1, 5.2, Appendix A).
* Remarks 2.4 and 4.8.
* A CONGEST implementation of the maximal-matching subroutine and its composition with ASM.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
* Non-vacuity: every bipartite graph has a maximal matching (`exists_maximal`), so oracles exist
  (`exists_mmOracle`).
* The concrete run in `Example.lean` is checked by `decide +kernel`, step by step against literal states.
* The model is new: CSLib's `Cslib.StableMatching` covers only complete preferences and perfect matchings. The
  incomplete-preference definitions in `Prefs.lean` are a CSLib candidate.
