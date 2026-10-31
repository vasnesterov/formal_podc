# Know Your Audience — PODC 2024

Bernadette Charron-Bost, Patrick Lambein-Monette. *Brief Announcement: Know Your Audience.* PODC 2024. DOI
[10.1145/3662158.3662784](https://doi.org/10.1145/3662158.3662784). Formalized version: the full version *Know your
audience: Communication model and computability in anonymous networks*, arXiv
[2311.17728](https://arxiv.org/abs/2311.17728) v1 (23 pp.); numbering follows it. Copy of the paper:
[paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** Theorem 4.1 says that, with output port awareness, symmetric communications
or outdegree awareness, a function is computable in static strongly connected anonymous networks iff it is
frequency-based. The direction "frequency-based ⇒ computable" is true, and so are Corollaries 4.3 (size known) and
4.4 (one leader). The direction "computable ⇒ frequency-based" (and Corollary 4.2) is false, but only because of
networks with at most two agents. In the paper's model an agent can recognise from its received messages that it is
alone, and with symmetric links that the network is `K₂`; these are exactly the sizes where the network is unique and
self-identifying, so every symmetric function is computable there. We prove the exact corrected characterisation:
"frequency-based on vectors of length ≥ 2" (outdegree and output port awareness), and "symmetric and frequency-based
on vectors of length ≥ 3" (symmetric communications). All the paper's examples (average computable, sum not) and
its proof idea survive.

## Mistakes in the paper

* **Theorem 4.1, (ii) ⇒ (i), is false (all three models; also Corollary 4.2).** The paper's model (§2.1–2.2) puts a
  self-loop at every agent, and the transition function receives the *multiset* of received messages. So after
  round 1 an agent knows its indegree. In a strongly connected network the indegree is 1 iff the agent is alone.
  Hence `isSingleton(v) = [|v| = 1]` is computable in every model, even simple broadcast, from every initial
  configuration, but it is not frequency-based: `isSingleton(a) = 1 ≠ 0 = isSingleton(a, a)`
  (`theorem_4_1_ii_imp_i_false`, `theorem_4_1_false`). Taken alone this is the degenerate case `n = 1`.
* **With symmetric communications `K₂` is recognisable too.** In a connected bidirectional
  network, an agent with a single neighbour whose neighbour also has a single neighbour lives in `K₂`. Agents learn
  their degree in round 1 and their neighbours' degrees in round 2. So `isPair(v) = [|v| = 2]` is computable with
  symmetric communications, and it is not frequency-based even on vectors of length ≥ 2:
  `isPair(a, b) = 1 ≠ 0 = isPair(a, b, a, b)` (`theorem_4_1_false_symmetric_K2`). Theorem 4.1 and Corollary 4.2 are
  therefore false for symmetric communications on 2-agent networks. We grade this as degenerate: with symmetric links
  `K₂` is the only 2-agent network and its agents know it after two rounds, so function computation on 2 agents is
  trivial there (in the directed models, where `K₂` is not recognisable, the theorem holds at `n = 2`). This is a
  borderline call; see [differencies.md](differencies.md), item 2.
* **Where the proof breaks.** The proof of (ii) ⇒ (i) (§4.1) lifts both input vectors along the rings
  `R_n → R_p ← R_m`, where `p` is the lcm of the denominators of the frequencies. A bidirectional ring of size ≤ 2
  is a multigraph (`R_2` has a double edge and `R_1` three loops), not a network of the class (§2.1 networks are simple
  digraphs `([n], E_t)` with self-loops). So for `p ≤ 2` (or `n, m ≤ 2`) Lemma 3.2 does not apply: the proof
  silently needs sizes ≥ 3.
  For outdegree and output port awareness this matters only for `n = 1`. We use directed cycles instead and lift along
  `C_{n'n} → C_n` and `C_{nn'} → C_{n'}` (`n, n' ≥ 2`), together with Lemma 3.3 at length `nn'`
  (`frequencyBasedFrom_two_of_computable`). For symmetric communications we use bidirectional rings, which needs
  `n, n' ≥ 3` (`frequencyBasedFrom_three_of_computable_symmetric`). These bounds are optimal, by the two functions
  above. The positive algorithm then has to treat `n = 1` (and `n = 2` for symmetric communications) separately
  (`theorem_4_1_corrected`, `theorem_4_1_corrected_symmetric`, `corollary_4_2_corrected*`).
* **Lemma 3.3 is imprecise.** "If `f` is computed in an anonymous network class then `f` is multiset-based" holds only
  on the vector lengths of the networks in the class: computability in `C_k` says nothing about other lengths. Every
  use in the paper involves classes with networks of all sizes, so the uses are fine (`Computes.perm_eq`).
* **§4.3, symmetric variant (not formalized).** "Up to some permutation of the vertices in `B`, we may assume that
  none of the degrees `d_{1,2}, …, d_{m−1,m}` is zero, since `B` is strongly connected" assumes a Hamiltonian path in
  the minimum base. This fails, e.g., for a star with four distinct input values, which is its own minimum base.
  Propagating eq. (4) along a spanning tree repairs the formula. Our symmetric algorithm does not use this variant.
* **Side remark (cited result).** Table 1 and §6 state, citing [20], that only set-based functions are computable with
  simple broadcast. In this paper's model that also fails at `n = 1` (`isSingleton_computable .broadcast`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Static network = simple directed graph on `Fin n` (`n ≥ 1`) with a self-loop at every agent and a local output port
  numbering. Synchronous lock-step rounds with synchronous starts; no failures; deterministic anonymous algorithms.
  An agent sends `send(state, outdegree, port)`, and its transition gets the multiset of received messages. The
  models restrict `send` (`CommModel.Allowed`): simple broadcast and symmetric communications see only the state,
  outdegree awareness the state and the outdegree, output port awareness everything. Symmetric communications also
  restrict to bidirectional networks.
* `f : List Ω → X`, where `X` is any metric space (main statements) or topological space. `A` computes `f` in a class
  if in every network of the class, for every input vector, every agent's output converges to `f` of the inputs.
* Initial state = function of the input (the paper allows a set `Q₀` of initial states). The counterexample
  algorithms are correct from every initial configuration, so they also compute in the paper's sense
  (`detectOne_out`, `detectTwo_out`).
* Leaders (Cor. 4.4): inputs `(value, isLeader)` with exactly one leader (`OneLeader`). Known size / bound:
  classes `sizeEq k`, `sizeLE B`.

**Main results in Lean.** Namespace `Podc.KnowYourAudience` unless stated otherwise.

| Paper | Lean | File |
|---|---|---|
| Lemma 3.1 (Lifting lemma) | `Cslib.AnonNet.Fibration.runFrom_comp` | `Podc/.../AnonymousNetworks/Lifting.lean` |
| Lemma 3.2 | `Cslib.AnonNet.Fibration.eq_of_computesOn` | `Podc/.../AnonymousNetworks/Lifting.lean` |
| Lemma 3.3 (on the lengths present) | `Cslib.AnonNet.Computes.perm_eq`, `multisetBased_of_computable` | `Lifting.lean`, `Impossibility.lean` |
| Thm 4.1 (i) ⇒ (ii) | `theorem_4_1_i_imp_ii` | `Main.lean` |
| Thm 4.1 (ii) ⇒ (i): **false** | `theorem_4_1_ii_imp_i_false`, `theorem_4_1_false`, `theorem_4_1_false_symmetric_K2` | `Main.lean` |
| Thm 4.1 corrected | `theorem_4_1_corrected`, `theorem_4_1_corrected_symmetric` | `Main.lean` |
| Cor 4.2: **false**; (i) ⇒ (ii); corrected | `corollary_4_2_false`, `corollary_4_2_i_imp_ii`, `corollary_4_2_corrected(_symmetric)` | `Main.lean` |
| Cor 4.3 | `corollary_4_3` | `Main.lean` |
| Cor 4.4 | `corollary_4_4` | `Main.lean` |
| Eq. (1) and rank one of `ker M` (§4.2) | `isSol_card`, `exists_eq_mul_of_irreducible`, `solve_correct` | `Decode.lean`, `Kernel.lean` |

The positive direction uses an infinite-state view algorithm (`viewAlg`). At round `t` it reads, at depth `⌊t/2⌋`,
the colour-refinement classes of all agents (= the minimum base, once refinement has stabilised). It then reads the
edge multiplicities and outdegrees between classes, and outputs `f` of the multiset given by any positive integer
solution of eq. (1). The rank-one property of eq. (1) is proved by a maximum principle (if `z > 0` solves it and the
class graph is strongly connected, every solution is a multiple of `z`) instead of the paper's Perron–Frobenius
argument. With symmetric communications the outdegree of a class is read off as its indegree, so no
outdegree-learning phase is needed.

**Not formalized.** Section 5 (dynamic networks, Push-Sum). The finite-state, self-stabilizing version of the
minimum-base algorithm and the `n + D` time bound. The covering-based variants of §4.3. The extension to `ℓ` known
leaders.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The model
(networks, algorithms, models, computability, fibrations, Lifting lemma, Lemma 3.3) is staged for CSLib in
`Podc/Computability/Distributed/AnonymousNetworks/{Basic,Lifting}.lean`. The paper-local `Rings.lean`, `Views.lean`
and `Kernel.lean` are also CSLib candidates.
