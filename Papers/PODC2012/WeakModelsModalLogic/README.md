# Weak Models of Distributed Computing, with Connections to Modal Logic — PODC 2012

Lauri Hella, Matti Järvisalo, Antti Kuusisto, Juhana Laurinharju, Tuomo Lempiäinen, Kerkko Luosto, Jukka Suomela,
Jonni Virtema. *Weak models of distributed computing, with connections to modal logic.* PODC 2012. DOI
[10.1145/2332432.2332466](https://doi.org/10.1145/2332432.2332466). Formalized version: the full journal version,
arXiv [1205.2051](https://arxiv.org/abs/1205.2051) v3 (Dec 2013); numbering follows it.

**Verdict: 🛠️ Proof repaired.** Both linear orders hold as stated:
`SB ⊊ MB = VB ⊊ SV = MV = VV ⊊ VVc` (1) and the same for the constant-time classes (2), together with every
numbered result on the way (Theorems 4, 8, 9, 11, 13, 17, Lemmas 5, 6, 15, 16, Corollaries 3, 7, 10, 12, 14, 18).
The two simulation proofs (Theorems 4 and 8/9) ignore nodes that have already stopped. A stopped node sends the
empty message `m0`, and so the simulating node cannot receive the extra information it needs from it. For Theorem 8
this needs a real (if small) extra mechanism.

## Mistakes in the paper

* **Theorems 8 and 9: proof gap (stopped neighbours); statements true.** The simulating `Multiset` algorithm `B`
  "augments each outgoing message with the full message history" and sorts the received histories
  lexicographically. But once a neighbour `w` of `u` has stopped in `A`, its copy in `B` has stopped too and sends
  `m0`. Then `u` no longer receives `w`'s history and cannot place `w`'s `m0` in the sorted order. We repair it as
  follows. `B` stores at each node the multiset `H` of the full histories received so far. In each round it sets
  `H' = R + (H − R.map dropLast).map (· ++ [m0])`, where `R` is the multiset of histories actually received.
  So the stopped neighbours' histories are extended by `m0`; this update is exact for multisets. The paper's
  refinement `P₀ ⊇ P₁ ⊇ …` of compatible port numberings is replaced by a single port numbering `p*`: it copies the
  out-ports of `p₀` and sorts the in-ports by the time-`T` histories of `B`'s own run, so it is not circular. We
  show by induction that `A` on `p*` follows `B` on `p₀` exactly, using that truncation is monotone for the
  lexicographic order. Time `T` is kept, as claimed. (`theorem8`, `theorem9`)
* **Theorem 4: small gap of the same kind; statement true.** "Now all messages received by a node are distinct" is
  false: stopped neighbours and padding all deliver `m0`. It is harmless. The non-`m0` messages are pairwise
  distinct by Lemma 6, so the number of `m0`s is `Δ − #(distinct non-m0 messages)`, and the multiset of `A`'s
  messages can be rebuilt from the set. Our `Set` algorithm runs `C_Δ` for `2Δ + 1` rounds and then simulates `A`.
  Its running time is `T + 2Δ + 1 = T + O(Δ)`. (`theorem4`)
* **Theorem 17: loose step.** "There are nodes `u, v` with `t(u) < t(v)` and `t(v)` maximal. This means
  `S(u) = 0`." `S(u) = 0` needs a *neighbour* of larger type. Connectivity, which the paper invokes, gives an edge
  whose endpoints have different types, and its smaller endpoint outputs `0`. (`thm17_mem`)
* Minor imprecisions, none affecting a result:
  - Lemma 5 is stated for rounds `t ≥ 4`; it holds for `t ≥ 3`. Lemma 6's consequence silently uses order `k = 2`
    (the pair `u, w` itself).
  - In Theorem 11, `Π(G)` is undefined for stars with `k ≤ 1`: they are stars, but not `k`-stars with `k > 1`. We
    leave the output unrestricted there.
  - In Theorem 17 the local type is defined through out-ports (`p((v, i))`), but a node can only learn the in-port
    version (`p⁻¹((v, i))`). Under consistency the two agree, which is all the proof uses.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** (`Model.lean`)
* Deterministic synchronous anonymous networks. There are no identifiers, no randomness and no failures; each node
  initially knows only its degree.
* Graphs are finite simple graphs `G : SimpleGraph V`, `[Finite V]`; `deg v` is `Nat.card` of the neighbour set.
* A port numbering is literally the paper's `p : P(G) ≃ P(G)` with `A(p) = A(G)`, where `Port G = Σ v, Fin (deg v)`
  (ports are 0-based). It is *not* required to be an involution; `Consistent` means `p ∘ p = id`.
* A state machine `Machine Δ Y` has stopping states `Y` and arbitrary intermediate states and messages, with `m0`,
  `z0 : ℕ → Y ⊕ Z`, `μ` and `δ : Z → (Fin Δ → M) → Y ⊕ Z`. The execution is the paper's §1.3 verbatim: the
  received vector is ordered by in-port and padded with `m0`, and stopped nodes send `m0` and keep their state.
* `Multiset`/`Set`/`Broadcast` are the paper's conditions on `δ`/`μ`. An algorithm is a sequence `(A_Δ)`. "Solves
  `Π` in time `T`" quantifies over all `Δ`, all finite `G ∈ F(Δ)` and all (resp. all consistent) port numberings.
  Constant time means `T(Δ, n) = T'(Δ)`. The 14 classes `VVc … SB`, `VVc1 … SB1` are defined from these.
* Output sets `Y` are arbitrary types: the equalities hold for every `Y`, and the separating problems use `Bool`.
* Bisimulation (`Bisimulation.lean`) is defined on the paper's relations `R(i,j)`, `R(i,*)` and `R(*,*) = E`.
  Instead of Theorem 2 (modal-logic characterisation, not formalized), we prove directly that bisimilar nodes run
  through identical states for every algorithm of the matching class; Corollary 3 follows.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| (1) `SB ⊊ MB = VB ⊊ SV = MV = VV ⊊ VVc` | `linearOrder` (equalities for any `Y`: `collapse`) | `Main.lean` |
| (2) the same for `·(1)` | `linearOrder1` (`collapse1`) | `Main.lean` |
| Corollary 3 (a), (b), (c) | `cor3a`, `cor3b`, `cor3c` | `Bisimulation.lean` |
| Theorem 4 | `theorem4` (time `T + 2Δ + 1`) | `SetSim.lean` |
| Lemma 5 | `PortNumbering.lemma5` (also `lemma5'` for `t ≥ 3`) | `SetSim.lean` |
| Lemma 6 | `PortNumbering.lemma6`, `PortNumbering.lemma6_consequence` | `SetSim.lean` |
| Corollary 7 | `cor7` | `SetSim.lean` |
| Theorems 8, 9 | `theorem8`, `theorem9` | `MultisetSim.lean` |
| Corollary 10 | `cor10` | `MultisetSim.lean` |
| Theorem 11, Corollary 12 | `theorem11`, `cor12` | `Separations.lean` |
| Theorem 13, Corollary 14 | `theorem13` (the paper's 23-node graph `g13`), `cor14` | `Separations.lean` |
| Lemma 15 | `lemma15` | `Lemma15.lean` |
| Lemma 16 | `lemma16` | `Lemma16.lean` |
| Theorem 17, Corollary 18 | `theorem17`, `corollary18` (Figure 9a graph: `fig9a_inClassG`) | `Theorem17.lean`, `Fig9a.lean` |

**Not formalized.** Theorem 2 and the modal-logic part of §4 and §5.4 (a)–(d). Also not formalized: Remark 2
(`SB_o`), §3.4 (local inputs), the claim that `𝒢` has `k`-regular members for every odd `k ≥ 3` (we use the
3-regular graph of Figure 9a), and the concrete numbering of Figure 9b (Lemma 15 constructs one).

**Trust.** No `sorry`; `linearOrder`, `linearOrder1` and the listed theorems use only the axioms `propext`,
`Classical.choice`, `Quot.sound`. Non-vacuity: every port-numbering quantifier is over a nonempty set
(`exists_portNumbering`, `exists_consistent_portNumbering` in `PortExists.lean`). The separating graphs are
concrete: a 3-star, the paper's 23-node graph and the 16-node graph of Figure 9a. Their properties (regularity,
connectivity, no perfect matching, the bisimulation classes) are checked by `decide` or by explicit proofs. Lemma 15
uses CSLib's `Matrix.exists_perm_decomposition` (Birkhoff–König for `ℕ`-matrices).

CSLib candidates (marked `-- CSLib candidate` or listed here): `Involutive.exists_fixed_of_odd_card`,
`exists_perfectMatching_of_involutive` (`Lemma16.lean`), `exists_mem_not_mem_of_odd_card` (`Fig9a.lean`),
`take_le_take` (lexicographic truncation), `sort_map_univ` (`MultisetSim.lean`). The general (possibly inconsistent)
port-numbering model in `Model.lean`/`Bisimulation.lean` could complement CSLib's `PortNumbering` (consistent only).
