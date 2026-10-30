# State Complexity of Protocols With Leaders — PODC 2022

Jérôme Leroux. *State Complexity of Protocols With Leaders.* PODC 2022. DOI
[10.1145/3519270.3538421](https://doi.org/10.1145/3519270.3538421). Formalized version: arXiv
[2109.15171](https://arxiv.org/abs/2109.15171) **v2** (March 2022); numbering follows it.

**Verdict: 🛠️ Proof repaired.** The main result holds as stated. Theorem 4.3 is proved for every protocol of finite
interaction-width: `n ≤ (4 + 4·width + 2|ρ_L|)^(|P|^((|P|+2)²))`. Corollary 4.4, the `Ω((log log n)^h)` lower bound
for `h < 1/2`, and Examples 4.1 and 4.2 are proved too. Lemmas 5.2–5.4, 6.2, 7.1, 7.2 and Theorem 6.1 are proved as
stated. Two proofs have genuine gaps, in Lemma 6.2 and Lemma 7.3. Lemma 7.3 is proved only with a weaker constant
(the weak Pottier bound instead of Pottier's), but that constant is still enough for Theorem 4.3's bound.

## Mistakes in the paper

* **Proof gap in Lemma 7.3 (Pottier step).** The linear system (1) has one variable `β(a)` per *displacement* `a ∈ A`
  of a simple cycle. The proof then reads `β(e)` for *edges* `e` ("`Σ_H β(e) = #Θ(e)`") and builds `Θ'` with
  "`#Θ' = β'`". That is a type error: different cycles with the same displacement are merged, so the system no longer
  knows which edges a solution uses. The claim "`#Θ'(e) > 0` if `#Θ(e) ≥ k`" is therefore not established. The
  length is also off: `|Θ'|` counts edges, but `‖β'‖₁` counts cycles. Each cycle has up to `|S|` edges, so the
  proof gives `|Θ'| ≤ |S|·(|E|+d)(1+2|S|‖T‖)^(d(d+1))`, not the stated bound without the factor `|S|`.
  We prove Lemma 7.3 with variables indexed by the cycles themselves. This works with the weak Pottier bound
  (`Cslib.exists_small_decomposition`), whose constant does not depend on the number of variables. The constant
  becomes `K = (2|S|M)^(2^d−1)`, with `k > ‖Δ(Θ)|_Q‖₁·|S|·M·K` and `|Θ'| ≤ (|E|+d)·|S|·K`. Section 8 goes through
  with this constant (`ℓ = h^(2^d+2d+4)`, `k = d·h^(2^d+1)`, threshold `h^(2d+5)·ℓ`). The final exponent still fits
  under `|P|^((|P|+2)²)`, so Theorem 4.3 is unaffected. We do not know whether Lemma 7.3 holds with the paper's
  constant. (`lemma_7_3`)
* **Proof gap in Lemma 6.2 (statement true).** In the case where every `β` reachable from `ρ_n` has
  `β(p) < λ_{n+1}` on `R_n`, the proof asserts that the `T|_{Q'}`-reachability set of `ρ_n|_{Q'}` has at most
  `sλ_{n+1}^{d−n}` elements. The case hypothesis is about the full net `T`. In the restricted net `T|_{Q'}` the places
  `p_1, …, p_n` are unconstrained, so it does not apply directly. Repair: suppose an `R_n`-place reaches `λ_{n+1}` in
  `T|_{Q'}`. A shortest such path stays in a set of at most `sλ_{n+1}^{d−n}` configurations, so it is that short. It
  then lifts to `T` by Lemma 5.2, since `ρ_n(p_j) ≥ λ_n ≥ sλ_{n+1}^{d−n}‖T‖`. That contradicts the case hypothesis.
  (`lemma_6_2_step`)
* **Slips in the proof of Theorem 4.3 (Section 8), all harmless.**
  * The decomposition of a path into a multicycle `Θ` and an elementary path `π` gives `#Θ(e) ≥ ℓ − 1` (or
    `≥ ℓ − |S|` for a short path), not `#Θ(e) ≥ ℓ`. There is ample slack.
  * Theorem 6.1 is applied to `P' = P \ {i}`, so it gives `(d−1)‖α‖∞ ≤ b`, not `d‖α‖∞ ≤ b`. The weaker bound
    suffices, because the sum is over `R' ⊆ P'`.
  * "`Δ(Θ)(p) = μ(p) − η'(p) − Δ(π)(p)`" should read `α'(p)` instead of `η'(p)`. The following estimate only works
    with `α'`.
  * "`α'(i) = ρ_L(i) + (n−1) − Δ(σ)(i)`" has the wrong sign; the bound `≥ n − h` holds anyway.
  * Lemma 7.3 is used with its hypothesis `‖T‖∞ > 0` without checking it. We avoid the issue with `M = 1 + ‖T‖∞`.
  * The final estimate claims `r ≤ d^(d²+d+3)`. The factors `2(d−1)^(d−1) ≤ d^d`, `1+(2+(d−1)^(d−1))^d ≤ d^(d²)` and
    `5d²+2d+4 ≤ d^5` only give `d^(d²+d+5)`. That is still `≤ d^((d+2)²)`, so the theorem is unaffected.
* Typos: Section 8 writes "`d = |Q|`" (meaning `|P|`), "the `(n > i)` predicate" (meaning `(i ≥ n)`) and "a cycle
  `θ` on `x|_Q`" (meaning `α|_Q`). The proof of Lemma 7.3 writes `Δ(Δ)` for `Δ(Θ)` and swaps `α'`/`β'` in one
  sentence. Pottier's decomposition is a multiset, not a "set `H`".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Configurations are vectors `P → ℕ`; `ρ|_Q` is modelled inside `ℕ^P` (zero outside `Q`). A protocol (`Protocol`)
  has an arbitrary additive preorder `R` (agents may be created and destroyed), a leader configuration, initial states
  `I` and outputs in `{0, ★, 1}`. `S₀`, `S₁` and "stably computes" are the paper's definitions, word for word. Inputs
  `ρ ∈ ℕ^I` are the configurations vanishing outside `I`, and include `ρ = 0`. No fairness or scheduler is involved:
  stable computation is the paper's reachability definition. Everything is deterministic and there is no randomness.
* Interaction-width: `HasWidthLE R m` means "width `≤ m`", and `width R : ℕ∞` is the paper's `width`. Section 3's
  "finite width ⇒ Petri-net reachability" is `Protocol.reach_iff`, with the finite net `widthNet R m`.
* Theorem 4.3 is stated for every `m` that bounds the width (`theorem_4_3`), and for `width(→*)` itself
  (`theorem_4_3'`). The paper's `n > 0` is not needed.
* Section 6 is proved relative to a set `U` of active places, so that Section 8 can use `P \ {i}`. The paper's
  statement is the case `U = P`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 4.3 | `theorem_4_3`, `theorem_4_3'` | `Main.lean` |
| Section 8 (case `\|P\| ≥ 2`) | `Sec8.main_bound` | `MainBound.lean` |
| Section 8, "`d = 1` ⇒ `n = 1`" | `n_le_one_of_card_le_one` | `Main.lean` |
| Corollary 4.4 | `corollary_4_4` (numeric core `corollary_4_4_numeric`) | `Corollary.lean` |
| Example 4.1 (2 states, leaderless, width `= n`) | `Ex41.stablyComputesGe`, `Ex41.width_eq`, `Ex41.conservative` | `Examples.lean` |
| Example 4.2 (6 states, `n` leaders, width `≤ 2`) | `Ex42.stablyComputesGe`, `Ex42.hasWidthLE`, `Ex42.conservative` | `Examples.lean` |
| Section 3 (width vs. Petri nets) | `Protocol.reach_iff`, `hasWidthLE_reach` | `Protocol.lean` |
| Lemma 5.1 | `lemma_5_1` | `Stabilized.lean` |
| Lemma 5.2 | `lemma_5_2` (per-place form `run_lift`) | `Model.lean` |
| Lemma 5.3 (Rackoff, bound `(‖ρ‖+‖T‖)^(d^d)`) | `lemma_5_3` | `Stabilized.lean` |
| Lemma 5.4 | `lemma_5_4` | `Stabilized.lean` |
| Lemma 6.2 | `lemma_6_2` (gap repaired in `lemma_6_2_step`) | `Bottom.lean` |
| Theorem 6.1 | `theorem_6_1`, relative form `theorem_6_1_rel` | `Bottom.lean` |
| Lemma 7.1 (Euler) | `lemma_7_1` | `ControlStates.lean` |
| Lemma 7.2 | `lemma_7_2` | `ControlStates.lean` |
| Lemma 7.3 (weak Pottier constant) | `lemma_7_3` | `ControlStates.lean` |

**Not formalized.** Lemma 7.3 with Pottier's constant `(1+2|S|‖T‖)^(d(d+1))` (Pottier's theorem itself), and Remark 1
(Presburger characterization with leaders, which the paper leaves open). The cited upper bound of Blondin–Esparza–Jaax
is not formalized.

**Trust.** No `sorry`. All listed theorems use only `propext`, `Classical.choice` and `Quot.sound`. Rackoff's lemma is
proved: `Podc/Computability/PetriNets/Rackoff.lean`, put in the form `(R+M)^(k^k)` by `rackoffBound_lt`. So is the weak
Pottier bound: `Podc/Foundations/Combinatorics/DiophantineDecomposition.lean`. Non-vacuity: Examples 4.1 and 4.2 are
protocols satisfying the hypotheses of Theorem 4.3 for every `n ≥ 1`.

CSLib candidates (marked `-- CSLib candidate`): the Petri-net model on `P → ℕ` with Lemma 5.2 (`Model.lean`), the
generic shortest-path/bottom lemmas (`BottomAux.lean`), the labelled-multigraph library with the Euler lemma and path
decomposition (`ControlStates.lean`), and `rackoffBound_lt`.
