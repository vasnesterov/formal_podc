# How to Meet Asynchronously at Polynomial Cost — PODC 2013

Yoann Dieudonné, Andrzej Pelc, Vincent Villain. *How to meet asynchronously at polynomial cost.* PODC 2013. DOI
[10.1145/2484239.2484245](https://doi.org/10.1145/2484239.2484245). Formalized version: arXiv
[1301.7119](https://arxiv.org/abs/1301.7119) v2 (full version, 2015); numbering follows it.

**Verdict: 🛠️ Proof repaired.** Lemma 2.1, Lemma 3.1, the synchronization Lemmas 3.2–3.6 and the main
Theorem 3.1 are all true as stated, for the paper's fully adversarial continuous asynchronous model and any
exploration procedure with a non-decreasing polynomial step count. Reingold's theorem (UXS) is a hypothesis. Two
proof steps need repair. The case analysis of Lemma 3.3 misses a case. The length estimates that define the
polynomial `Π` are wrong for slowly growing `P`. Neither changes a statement.

## Mistakes in the paper

* **Lemma 3.3: a case is missing in the proof; the statement is true.** The proof says: "if during this time
  interval agent `a` has not started any fence, it would have to follow a trajectory included in a piece
  `T_a(k)`". But `a` may spend the whole fence `Ω_b(2(n+l))` of `b` inside one of its own fences, started
  before `b`'s. That case satisfies the lemma's conclusion anyway, but the proof then derives that `a` *must*
  start a fence during the interval, which is not shown. We prove the lemma differently. Let `j` be the last
  piece of `a` completed by the end of the interval. Then the last atom of piece `j` cannot have been followed
  entirely during the interval (catching, Lemma 3.1). Neither can the first atom of piece `j + 1`. Nor can
  `a` stay inside the single piece `j + 1` (counting); here `j + 1 ≤ 2(n+l)` because `b` finished first.
  (`lemma_3_3`)
* **The length estimates in the proof of Theorem 3.1 are wrong; the theorem is true.** The paper bounds
  `|Y(k, v)| ≤ Y*_k = 2P(k)·Q*_k` and `|A(k, v)| ≤ A*_k = 2P(k)·Z*_k`. But `Y'(k, v₁)` inserts `Q(k, ·)` at
  each of the `P(k) + 1` nodes of `R(k, v₁)` and adds `P(k)` edges, so `|Y(k)| = 2(P(k)+1)|Q(k)| + 2P(k)`.
  Similarly for `A`. For `P ≡ 1`, `|Y(1)| = 10 > 6 = Y*_1` and `|A(1)| = 42 > 12 = A*_1`. The same values arise
  for `P(k) = k`. At `k = 1` the bound fails for every `P`: `|Y(1)| = 4P(1)² + 6P(1) > 4P(1)² + 2P(1) = Y*_1`.
  As a result the paper's
  `Π(n, m)` is not justified. A numerical check (`P ≡ 1`, `n = 2`, labels `1` and `3`) shows that it is even
  smaller than the length of the first `2(n+l)+1` pieces of the agent with the longer label (2.92·10¹¹ vs
  2.77·10¹¹). Theorem 3.1 only claims that *some* polynomial `Π` exists. We define `Π` from the exact lengths
  (`piBound`) and prove that it is polynomially bounded. (`paper_Ystar_wrong`, `paper_Astar_wrong`,
  `theorem_3_1`)
* **Typos and small slips.**
  - Definition 3.8: the pseudocode loop body should be "Follow trajectory `X(k, v)`", not `Ω(k, v)`.
  - Lemma 3.6, Case 2, `µ = 1`: the contradiction comes from Lemma 3.3 (`a` has not completed the first atom
    `N` of piece `j+1` when `b` ends its fence), not from Lemma 3.4.
  - Proof of Lemma 3.3: `Ω_b(2(n+l))` contains `(4(n+l)−1)|K(2(n+l))|` copies of `X(2(n+l))`, not
    `2(2(n+l)−1)|K(2(n+l))|`. This is harmless, since the latter is smaller.
  - §2: `|x| = ⌈log x⌉` should be `⌊log x⌋ + 1`, the length of the binary representation, which is what is used.
  - The proof of Theorem 3.1 says "since the polynomial `P(k)` is non-decreasing". Monotonicity of `P` (and
    `P ≥ 1`) is used already in the correctness proof (Lemmas 3.2–3.6 compare `|A(·)|`, `|B(·)|` at different
    parameters), but it is stated only there. It is harmless: the step count can always be padded.
  - Lemma 2.1: `H` must keep `G`'s port numbers on the copied trajectory edges. The proof never says why the
    procedure follows the same trajectory in `H` (it sees the same degrees and entry ports). That a free port
    exists also uses connectivity.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Graph: finite, simple, connected, nodes anonymous. For Lemma 2.1 and `theorem_3_1_ports`, a CSLib port-labelled
  graph (`PNGraph`, `IsSimple`). For the rendezvous analysis, any `SimpleGraph` with an exploration family.
* Exploration procedure (UXS "axiom"): `Explorer G P` is a family of trajectories `R(k, v)`. Each is a walk
  from `v` of exactly `P(k) ≥ 1` edges. It traverses every edge whenever `G` has at most `k` nodes (the
  paper's "integral"). `P` is non-decreasing, and polynomially bounded for the polynomial claim. The family may
  depend on `G` arbitrarily, so this is more general than Reingold's port-local procedure. `Explorer.ofProc`
  instantiates it with deterministic port-local procedures (`Proc`: history of (degree, entry port) ↦ exit
  port).
* Agents: deterministic, distinct positive labels, modified labels `M(x)`. Before the meeting, the route of an
  agent is a fixed node sequence `E.route (modLabel L) v` (the infinite concatenation of the iterations of the
  `repeat` loop).
* Asynchrony and adversary: exactly the paper's walks. A walk is an increasing time sequence `τ 0 = 0 < τ 1 < …`
  (accumulation allowed) and a progress function `p`. On each `[τ i, τ (i+1)]`, `p` is continuous with values
  in `[i, i+1]` and `p (τ i) = i`. The adversary may stop agents and move them back and forth inside edges.
  Positions live in the embedding `v ↦ e_v ∈ ℝ^V` (edges = segments, pairwise disjoint except at endpoints).
  A meeting is equality of positions, at a node or inside an edge. No randomness.
* Cost: "meeting by the time one of them performs `Π` traversals" is `t ≤ τ_a(Π) ∧ t ≤ τ_b(Π)`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2.1 | `lemma_2_1` | `Lemma21.lean` |
| Lemma 3.1 (for `X` / for `Y`) | `lemma_3_1`, `lemma_3_1_Y` (core: `meet_of_rep`) | `Main.lean`, `Meet.lean` |
| "integral trajectories force progress" (counting) | `meet_of_count` | `Meet.lean` |
| Lemma 3.2 | `lemma_3_2` | `Sync.lean` |
| Lemmas 3.3, 3.4, 3.5, 3.6 | `lemma_3_3`, `lemma_3_4`, `lemma_3_5`, `lemma_3_6` | `Sync2.lean` |
| Theorem 3.1 (meeting on the differing bit) | `meet_of_diff_bits`, `core` | `Sync2.lean`, `Main.lean` |
| Theorem 3.1 (explicit bound / polynomial) | `theorem_3_1_explicit`, `theorem_3_1` | `Main.lean` |
| Theorem 3.1 in the port-labelled model | `theorem_3_1_ports` | `Bridge.lean` |
| `M(x)` prefix-free | `exists_bit_ne` | `Labels.lean` |
| `Π` polynomial | `piBound_poly` | `Poly.lean` |
| wrong estimates `Y*`, `A*` | `paper_Ystar_wrong`, `paper_Astar_wrong` | `Examples.lean` |

Lemmas 3.2–3.6 are stated for any `N0 ≥ n` in place of `n + l`, and with the hypothesis "the agents have not met
before" as `NoMeet` (no meeting at a time when neither agent has passed a given index). Segments are 0-indexed.
`lemma_3_6` gives Properties 1–4 for the segment indices where both agents still have a border after segment `i`
(`i + 1 < min(k, s)` for both); Properties 1 and 2 for the last segment of the agent with the shorter modified
label are not stated (they are not used).

**Not formalized.** Theorem 2.1 (procedure ESST) and Section 4 (team size, leader election, renaming,
gossiping via SGL). Reingold's theorem is a hypothesis.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `k2Explorer` (an exploration family on `K₂`) and `idWalk` satisfy all hypotheses, and `k2_meet`
applies Theorem 3.1 to them. The model uses Mathlib (IVT, `arccos ∘ cos` as a continuous triangle wave) and
CSLib's `PNGraph`.

CSLib candidates (`Model.lean`, `Meet.lean`, `Traj.lean`): the continuous asynchronous mobile-agent model
(`Walk`, `Meet`) with the two meeting lemmas `meet_of_rep` and `meet_of_count`, and the trajectory algebra
(`Traj`, `OccIn`, `RepOcc`).
