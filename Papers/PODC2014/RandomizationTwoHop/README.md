# Anonymous Networks: Randomization = 2-Hop Coloring — PODC 2014

Yuval Emek, Christoph Pfister, Jochen Seidel, Roger Wattenhofer. *Anonymous Networks: Randomization =
2-Hop Coloring.* PODC 2014. DOI [10.1145/2611462.2611478](https://doi.org/10.1145/2611462.2611478).
Formalized version: the authors' 10-page copy from the ETH DISCO publication page (with proofs); there
is no arXiv version.

**Verdict: 🔧 Easy fix.** Both main theorems hold: Theorem 1 (`Π ∈ GRAN` ⇒ `Πᶜ` is solvable by a deterministic
anonymous algorithm) and Theorem 2 (the same in the infinity model), and so do the graph-theoretic results (Lemmas 2–4,
Norris' Theorem 3 and Corollaries 1–2). The proof of Lemma 9, the correctness of the paper's algorithm `A*`, has an
off-by-one in the view depth that port numbers make essential, so Lemma 9 is unestablished for `A*` as written. With
one more level of view (at the same round cost) `A*` is correct, and that is how we prove Theorem 1.

## Mistakes in the paper

### 🔧 Lemma 9 (correctness of algorithm `A*`, §3.2)
The proof says that "the first `k` rounds … are fully determined by `L_k(v, I)`" and the random bits, but they need
`L_{k+1}(v)` even without ports and `L_{k+2}(v)` with port numbers (`locality_gap`), while `A*` matches views `L_p` and
simulates up to `p − 1` rounds.

**Impact.** Theorem 1 is not affected. Lemma 9, and with it the claim that the paper's `A*` (as
written) solves `Πᶜ`, is neither proved nor refuted. If Update-Graph uses the view `L_{p+1}(v, I^p)`
instead of `L_p(v, I^p)`, all lemmas of §3.2 go through and Theorem 1 follows (`theorem_1`). Computing
`L_{p+1}` takes `p` rounds, which is the round count the paper states for this step. The repair changes
the algorithm (one view level), not only the argument; it is a local fix that the paper's own round
count points to.

**Details.** `L_1(v)` is the root alone, so `L_k(v)` has tree depth `k − 1`. Even without ports, `k` rounds depend
on tree depth `k`, i.e. `L_{k+1}`. That alone does no harm here: the simulation of phase `p` lasts
`l ≤ p − 1` rounds and `L_p` has tree depth `p − 1`. Port numbers add one more level. The simulated
algorithm `A_R` may send different messages on different ports. The port number at the far end of an
edge depends on the far node's *other* neighbours. The paper never fixes the port numbering used in
the simulations of `A*`; any numbering that is a local function of the colours (for instance sorting
neighbours by colour) has this problem.

`locality_gap` is a concrete instance. Take the 2-hop coloured paths `1–2–3` and `1–2–0` (labels:
degree and colour). Their endpoints have equal views `L_2`. Under colour-sorted ports, a one-round
deterministic algorithm (every node sends its port number) puts the two endpoints in different
states. Lemma 9 needs exactly this case: `l = p − 1`, all candidate nodes carry `p − 1` bits, and the
selected candidate agrees with the real graph only up to `L_p`. Then the output of `v*` in the
simulation may differ from the output of `v` in the lifted execution `η`, which is what Lemma 9
asserts they share. We did not construct a full counterexample to `A*`: that needs a problem in GRAN,
an adversarial `A_R`, and an analysis of `A*`'s candidate selection over all small graphs.

**Repair.** `AStar.Lv` is `trunc p (relabel (bL p) W)`, the view of tree depth `p`, i.e. `L_{p+1}(v, I^p)`. With
it, Lemma 9 is `AStar.outPhase_eq`, proved with the locality lemma `decided_local`.

### ✏️ Slips
- Corollary 3 is said to follow "from Corollary 1 as `|V̂*| ≤ p`". It follows from Fact 1 and Lemma 2
  (the finite view graph is a factor of the candidate).

### Typos
- §3.1: "node `v` computes `L_p(v, I^p)` (requires `p` rounds)". `p − 1` rounds suffice for `L_p`;
  `p` rounds give `L_{p+1}`, the view the repaired algorithm uses.

## Proof gaps (statements true)

### 🔧 Lemma 3 (`G∞` is the unique prime factor)
The proof shows that every prime factor of `G` is isomorphic to `G∞` but not that `G∞` itself is prime,
which Lemma 7 later uses for `I*^p`.

**Impact.** Statement true; repaired (`lemma_3`).

**Repair.** In `G∞` distinct nodes have distinct views (Fact 1). So every factorizing map out of
`G∞` is injective, hence bijective.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Labelled graphs are finite, connected and simple (`LGraph`). Problems are arbitrary sets of
  instances with arbitrary sets of valid output labellings (`Problem`). Inputs need not contain the
  degree; nodes know their degree from the port numbering.
- Algorithms run synchronously in the anonymous port-numbering model of CSLib (`PNGraph`, ports
  `0, …, deg − 1`). Messages may depend on the port, and the receiver learns the port number at the
  sender's end. There are no failures and states and messages are unbounded. Local computation is
  unrestricted (computability is not modelled).
- Randomness: one random bit per node and round (`RAlg.recv` receives it). Outputs are irrevocable:
  a node's output is its first output (`RAlg.decided`). Deterministic means the transition ignores
  the bit.
- Solvability (Las Vegas) must hold for every simple port numbering of every instance. The paper's
  probabilistic definition, with independent fair coins (product measure `bitMeasure`), is
  `SolvesAS`. The proofs use the combinatorial `Solves`: every finite bit prefix extends to a
  terminating run, and every terminated run is valid. `SolvesAS.solves` shows the paper's definition
  implies ours, so `theorem_1_AS` and `theorem_2_AS` hold for the paper's GRAN (`GRAN_AS`).
- Local views: `TEq … k` is equality of view trees of depth `k`, i.e. of `L_{k+1}`; `ViewEq … d` is
  the paper's `L_d`. `L_∞(u) = L_∞(v)` (`ViewEqInf`) means equality at all depths. In 2-hop coloured
  graphs siblings have distinct marks, so the infinite view is represented canonically by the set of
  label words of walks (`⟪X⟫ v`, `forall_teq_iff_lang`). The infinite view graph `G∞` (`viewLGraph`)
  has these languages as nodes.
- Infinity model: an algorithm is a function `A∞` of `⟪X⟫ v`. This language is determined by the view
  tree `L_∞(v)` (`lang_eq_of_forall_teq`), so `A∞` is a function of `L_∞(v)`.
- Simulations of `A_R` (in `A∞` and `A*`) use the colour-sorted port numbering (`colorPN`). Colours
  are taken from a linear order (the paper's colours are bit strings). The canonical choices of the
  paper (the total orders on `V∞`, on bit assignments and on finite view graphs) are replaced by
  choice functions of the canonical data. The analysis only needs that every node computes the same
  function of the same data.
- `A*` (`AStar.lean`) is written as functions of views: `bL p W` is `b^p(v)` for a node with
  infinite view `W`. The simulation runs on the infinite view graph of a canonically chosen graph
  realizing the selected view set; it is isomorphic to the paper's finite view graph (Corollary 2).
  The message-passing algorithm `astar` floods truncated walk languages and in round `r` evaluates
  phase `⌊√r⌋` (`Flood.lean`). This changes only the timing of outputs, not their values.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Fact 1 (factors preserve views) | `IsLocalIso.teq`, `IsLocalIso.lang_eq` | `Views.lean` |
| Factor of 2-hop coloured is 2-hop coloured | `IsLocalIso.twoHop` | `Graphs.lean` |
| §2.1 (`V∞` from one view) | `reach_lang` | `ViewGraph.lean` |
| Lemma 2 | `lemma_2` | `ViewGraph.lean` |
| Lemma 3 | `lemma_3` | `ViewGraph.lean` |
| Lemma 4 | `lemma_4` | `ViewGraph.lean` |
| Theorem 3 (Norris) | `theorem_3` (and two-graph version `teq_stable_two`) | `Norris.lean` |
| Corollary 1 | `corollary_1` | `Norris.lean` |
| Corollary 2 | `corollary_2` | `Norris.lean` |
| Lifting lemma for the decider (§2.3.2) | `inst_of_isFactorMap` | `Theorem2.lean` |
| Lemma 1, Theorem 2 | `theorem_2`, `theorem_2_AS` | `Theorem2.lean`, `Main.lean` |
| Observation 1 | `AStar.card_S` | `AStarTerm.lean` |
| Lemma 6 | `AStar.mem_Fam` | `AStarTerm.lean` |
| Lemma 7 (and Lemma 5) | `AStar.eq_of_mem_Fam`, `AStar.select_eq`, `AStar.phase_eq` | `AStarTerm.lean` |
| Lemma 8 | `AStar.exists_ext`, `AStar.terminates` | `AStarTerm.lean` |
| Lemma 9 (repaired `A*`) | `AStar.outPhase_eq` | `AStarCorrect.lean` |
| Lemma 9's locality claim fails with ports | `locality_gap` | `LocalityGap.lean` |
| Theorem 1 | `theorem_1`, `theorem_1_AS` | `Theorem1.lean`, `Main.lean` |
| Probabilistic ⇒ combinatorial solvability | `SolvesAS.solves`, `GRAN_AS.gran` | `Measure.lean` |

Lemma 1 holds by construction: `Ainf` makes its choices as functions of `V∞` only.

Lemma 7 (`I*^p` is selected for `p ≥ 2n`) takes another route than the paper. The printed proof, which compares views
in two different graphs (`Ĝ'*` with `n' ≤ n` nodes and `I*^p` with `n` nodes), is terse: it truncates subtrees of equal
depth-`p` views and uses Corollary 1 inside each graph, via "the depth-`n'` truncating function is a factorizing map".
We use colour refinement on the disjoint union (`teq_stable_two`): views of nodes of graphs with `m` and `n` nodes that
agree to tree depth `m + n − 1` agree forever. With `p ≥ 2n ≥ n + n'`, the candidate's view graph has the same views as
`I*^p`, so it is `I*^p` (`AStar.eq_of_mem_Fam`).

**Not formalized.** Section 4 (fibrations), the introduction's remarks (2-hop colouring and MIS are
in GRAN, `k`-hop colouring for `k > 2` is not), and computability of `A*`.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `gran_trivialProblem` gives a problem in GRAN (paper's definition).
`locality_gap` exhibits 2-hop coloured instances. The port-numbering model is CSLib's
`Cslib.PortNumbering.PNGraph`; the product measure is Mathlib's `Measure.infinitePi`.
