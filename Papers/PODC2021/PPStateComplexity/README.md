# State Complexity of Population Protocols — PODC 2021

Philipp Czerner, Javier Esparza (arXiv v3 adds Jérôme Leroux). *Lower Bounds on the State Complexity of
Population Protocols.* PODC 2021. DOI [10.1145/3465084.3467912](https://doi.org/10.1145/3465084.3467912).
Formalized version: arXiv [2102.11619](https://arxiv.org/abs/2102.11619) **v3** (July 2022); numbering follows
it. v3 has the double-exponential bound for leaderless protocols (Ω(log log η)). The PODC version (= arXiv v2)
claims only a triple-exponential bound and proves it differently (rejection certificates). That proof is not
formalized.

**Verdict: ⚠️ Correct with fixes.** The leaderless main result holds: Theorem 5.9 is proved, so
`η ≤ 2^((2n+2)!)` and `BB(n) ≤ 2^((2n+2)!)`. Theorem 4.5 (protocols with `ℓ` leaders, `η < F_{ℓ,ϑ}(n)`) is
also proved, after repairing a gap in its proof. Definition 1 of `BB_L` forgets to bound the number of leaders:
read literally, `BB_L(4)` does not exist, since 4 states and `η` leaders decide `x ≥ η` for **every** `η`. The
intended reading — a fixed number `ℓ` of leaders, as in Theorem 4.5, in the cited O(log log η) construction of
Blondin et al., and in the follow-up by Leroux (PODC 2022, "with a fixed number of leaders") — makes the
abstract's claim about protocols with leaders true, and that is what Theorem 4.5 proves. Further gaps
(Lemma 5.8, Corollary 5.7) are repaired without changing the final bounds.

## Mistakes in the paper

* **`BB_L` is under-specified: the number of leaders must be fixed.** Definition 1 defines `BB_L(n)` as the
  largest `η` such that some protocol with at most `n` states and *any* leader multiset computes `x ≥ η`.
  Take states `A, B, a, b` with `L = η·A` and input state `B`. The transitions are `AB ↦ ab`, `Ab ↦ Aa`,
  `Ba ↦ Bb`, `ab ↦ bb`, and identity on the other pairs; `B, b` output 1. This protocol decides `#B ≥ #A`,
  i.e. `x ≥ η`. So with 4 states every threshold is computable, and literally read, "a bound on `BB_L(n)`"
  (§4), "the inverse of a non-elementary function for protocols with leaders" (abstract) and "Ω(α(η)) for
  protocols with leaders" (§6) are false. The paper's own Theorem 4.5 has a bound `F_{ℓ,ϑ}(n)` that depends
  on `ℓ`, so the evident intent is a fixed number of leaders (or leaders counted in the size); with that
  reading the claims hold and follow from Theorem 4.5. (`not_bddAbove_BBLSet`, `majority4_computesGe`)
* **Proof gap in Theorem 4.5 (statement true).** From two configurations `C_k ≤ C_ℓ` in the same basis element
  `B + ℕ^S`, the proof applies Lemma 4.1 with `D_b := C_ℓ − C_k`. Condition 2 of Lemma 4.1, `b·x →* D_b`, is never
  established. Lemma 4.2 only gives `C_k + b·x →* C_ℓ`, which is not the same thing: `b` input agents alone,
  without the leaders, need not reach `D_b`. Fix: a variant of Lemma 4.1 with condition 2 replaced by
  `B + D_a + b·x →* B + D_a + D_b`. Pumping still works, because `C_k + λ b·x →* C_k + λ D_b` by induction.
  (`lemma_4_1'`, `theorem_4_5`)
* **Lemmas 4.1 and 5.2 implicitly need `b ≥ 1`.** The paper calls `D_b` a configuration, and configurations
  have at least two agents, so condition 2 already forces `b ≥ 2`. We work with arbitrary multisets
  (see differencies), and then `b = 0` must be excluded: with `b = 0`, `D_b = 0`, `π = 0`, all hypotheses hold
  for `a = 2` and any stable configuration reachable from `IC(2)`, viewed as the basis element `(C, ∅)`, while
  `η ≤ 2` fails for any protocol deciding `x ≥ 3`. Both applications in the paper have `b ≥ 1`; we add that
  hypothesis. (`lemma_4_1_b_zero_false`, `lemma_5_2_b_zero_false`: counterexamples to the relaxed reading)
* **Lemma 5.8 needs a strict inequality, and its proof swaps `S` and `Q \ S`.** The hypothesis "`C` is
  `1/ξ`-concentrated in `S`" means `ξ·C(Q\S) ≤ i`. The proof needs `ξ·C(Q\S) < i`; with equality the
  pigeonhole step "`|J| > C(S)`" fails. The proof also writes `C(S)` where it means `C(Q\S)`. The case
  "if `x ∉ S` take θ empty" should read "if `x ∈ S`, take `j = 1`, `θ = 0`, `C' = x`": an empty `θ` gives
  `j = 0`, which is useless for Lemma 5.2. In Theorem 5.9 the configuration is in fact
  `1/(ξ3^n)`-concentrated, which gives the strict inequality. So the main theorem is unaffected.
  (`lemma_5_8`)
* **Hidden assumption in §5.3.** The text says "Recall our assumption that for every state `q` there is an input
  `i_q` with `IC(i_q) →* C_q ∋ q`", but this assumption is never stated. It is not WLOG for Lemma 5.1(ii) as
  used: `π` may contain transitions whose pre-states are not coverable. We avoid the assumption. We work with
  the set of coverable states (Lemmas 5.3 and 5.4) and strengthen Lemma 5.1(ii) to require saturation only on
  the pre-states of transitions in the support of `π`. In Theorem 5.9 these pre-states are coverable, because
  `π` is the Parikh vector of a real execution. (`lemma_5_1_ii`, `lemma_5_3`, `lemma_5_4`)
* **Corollary 5.7 is inconsistent.** It sets up "`|Q|−1` equations on `|T|` variables" but needs to decompose
  `i` and `C` together with `π`. That requires the `|Q|` inequalities `Σ_t π(t)Δ_t(q) + [q = x]·i ≥ 0` on
  `|T|+1` variables, which is also what the exponent of `ξ = 2(2|T|+1)^{|Q|}` suggests. We use that system.
* Typos and slips: P'_k in Example 2.1 has `k+2` states, not `k+1`. Lemma 4.4 writes `v_{g(n)}` for
  `v_{i_{g(n)}}`. Lemma 4.2's proof says "for every `2 ≤ i ≤ k`". Theorem 4.5 states `η < F` but its proof
  ends with `η ≤ i_k ≤ F`. In Theorem 4.5 the sequence starts at `C_2`, so Lemma 4.4 must be applied with
  either `δ = ℓ + 2` or a chain two elements longer; we use `g = ϑ + 2`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Population protocols in the multiset (Petri-net) style of the Esparza group (`Podc` multiset model,
  `Cslib.PopulationProtocol.Transition`, `MStep`, `MReach`, `FiresSeq`, `FlowEq`). A `Protocol Q` has a
  transition relation `T ⊆ Q²×Q²` that is total on pairs, a leader multiset `L`, one input state `x`, and an
  output map `O`. `IC(i) = L + i·x`, and inputs satisfy `i ≥ 2`.
* The scheduler is the paper's fairness: if a configuration is reachable infinitely often, it is visited
  infinitely often. This is CSLib's `Run.GloballyFair`; no randomness.
* `ComputesGe η` says that every fair execution from `IC(i)`, `i ≥ 2`, eventually has consensus output
  `[η ≤ i]`. `computesGe_iff` proves the paper's reachability characterization ("every reachable configuration
  can reach `SC_{[η≤i]}`"), and all later proofs use it.
* Cited results. Rackoff's bound is proved: `g(n) ≤ 2^{2(2n+1)!}` for covering sequences. Pottier's theorem is
  replaced by a proved, weaker Hilbert-basis bound `(2M)^(2^e−1)`. This changes the intermediate constant `ξ`
  but not the final bound `2^((2n+2)!)`. Lemma 4.4 (Figueira et al.) is used as a hypothesis property
  `CtrlChainProp`. We prove that admissible functions exist (by compactness and Dickson's lemma), but not that
  they lie at level `F_ω`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Characterization after Def. 2 | `Protocol.computesGe_iff` | `Model.lean` |
| Lemma 3.1 | `Protocol.Stable.of_le`, `Protocol.SC.of_le` | `SmallBasis.lean` |
| Lemma 3.2 | `Protocol.exists_small_basis_stable`, `Protocol.exists_small_basis_SC` | `SmallBasis.lean` |
| Lemma 4.1 (+`b ≥ 1`), repaired variant | `Protocol.lemma_4_1`, `Protocol.lemma_4_1'` | `Leaders.lean` |
| Lemma 4.2 | `Protocol.exists_seq` | `Leaders.lean` |
| Lemma 4.4 (property; existence) | `CtrlChainProp`, `ctrlChainProp_ctrlChainBound` | `Leaders.lean` |
| Theorem 4.5 | `Protocol.theorem_4_5`, `Protocol.theorem_4_5_ctrlChainBound` | `Leaders.lean` |
| Lemma 5.1(ii) (strengthened) | `lemma_5_1_ii` | `Leaderless.lean` |
| Lemma 5.2 (+`b ≥ 1`) | `Protocol.lemma_5_2` | `Leaderless.lean` |
| Lemmas 5.3, 5.4 (coverable states) | `Protocol.lemma_5_3`, `Protocol.lemma_5_4` | `Leaderless.lean` |
| Cor. 5.7 + Lemma 5.8 (our `ξ`) | `Protocol.lemma_5_8` | `Leaderless.lean` |
| Theorem 5.9 | `Protocol.theorem_5_9_le` (`η ≤ ξnβ3^n`), `Protocol.theorem_5_9` (`η ≤ 2^((2n+2)!)`) | `Leaderless.lean` |
| Definition 1, `BB(n) ≤ 2^((2n+2)!)` | `BB`, `BB_le` | `BusyBeaver.lean` |
| `BB_L` unbounded without a leader bound | `not_bddAbove_BBLSet` | `BusyBeaver.lean` |
| Lemmas 4.1/5.2 need `b ≥ 1` (multiset reading) | `lemma_4_1_b_zero_false`, `lemma_5_2_b_zero_false` | `BusyBeaver.lean` |
| Example 2.1 (`P'_k` computes `x ≥ 2^k`) | `exampleP'_computesGe`, `le_BB` (`2^k ≤ BB(k+2)`) | `Examples.lean`, `BusyBeaver.lean` |
| 4-state protocol with `η` leaders | `majority4_computesGe` | `Examples.lean` |

Shared infrastructure, staged in `Podc/` (CSLib candidates):
* `Podc/Computability/PetriNets/Rackoff.lean`: Rackoff's covering-length bound for Petri nets (`Cslib.PetriNet.exists_short_cover`, `rackoffBound_two_two_le`).
* `Podc/Computability/Distributed/PopulationProtocols/Multiset/Rackoff.lean`: the same bound for the multiset model (`MReach.exists_short_cover`).
* `Podc/Foundations/Combinatorics/DiophantineDecomposition.lean`: weak Pottier theorem (`Cslib.exists_small_decomposition`) and zero-sum partitions.
* `Podc/Foundations/Order/ControlledDickson.lean`: chain bounds for controlled sequences (`Cslib.exists_controlled_chain_bound`, `ctrlChainBound`).

Monotonicity of reachability (`MReach.add_right`, `MReach.add`, `MReach.nsmul`) and the fair-run lemmas in
`Model.lean` are further CSLib candidates.

**Not formalized.** The two remaining cited results are not formalized: the fast-growing-hierarchy part of
Lemma 4.4 and Pottier's sharper constant. Also not formalized: the length bound `|σ| ≤ 3^n` in Lemma 5.4
(unused), Section 4.1 (discussion), Theorem 2.2 (cited lower bounds; we only derive `2^k ≤ BB(k+2)`), and the
triple-exponential proof of the PODC version.

**Trust.** No `sorry`. All listed theorems use only `propext`, `Classical.choice` and `Quot.sound`.
Non-vacuity: Example 2.1's leaderless protocols compute `x ≥ 2^k` for every `k`, so the hypotheses of
Theorem 5.9 are satisfiable for unboundedly large `η`. The 4-state protocol with leaders does the same for
Theorem 4.5. Functions with the Lemma 4.4 property exist (`ctrlChainProp_ctrlChainBound`).
