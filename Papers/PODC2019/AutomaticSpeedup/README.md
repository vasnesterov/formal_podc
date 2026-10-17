# Automatic speedup (round elimination) — PODC 2019

Sebastian Brandt. *An Automatic Speedup Theorem for Distributed Problems.* PODC 2019. DOI
[10.1145/3293611.3331611](https://doi.org/10.1145/3293611.3331611). Formalized version: arXiv
[1902.09958](https://arxiv.org/abs/1902.09958) v1 (the only version); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The converse of Theorem 1 ("`Π_1` in `t − 1` rounds ⇒ `Π` in `t`
rounds"), and with it Corollary 1 and the "reversible" / "exact complexities `T − 1, T − 2, …`" claims,
is false. It fails for the natural class of input-free `Δ`-regular high-girth graphs with arbitrary port
numbers. It holds once the endpoints of each edge can be told apart (edge symmetry breaking). The
forward direction, Theorem 2, Lemmas 1–4 and the lower bounds (§4.4, Theorem 4) are unaffected.

## Mistakes in the paper

* **Theorem 1, (2) ⇒ (1), and Corollary 1 are false without edge symmetry breaking (false statement).**
  The proof turns a `(t−1)`-round algorithm for `Π_1` into an algorithm for `Π_{1/2}`. Both endpoints
  of an edge `e` look only at `N^t(e)` and must pick a pair `(o, o')` with `{o, o'} ∈ g_{1/2}`; `v`
  takes `o` and `u` takes `o'`. If `N^t(e)` looks the same from both sides, they make the same choice,
  so a pair with `o ≠ o'` cannot be split.
  * *Counterexample.* Take `Π` = edge orientation (labels `0, 1`, edge configuration `{0, 1}` only,
    any node configuration). Outputting the constant `{{0}, {1}}` solves `Π_1` in 0 rounds on every
    graph.
  * On the class `{K_2}` (no inputs, both ports `1`; simple, connected, girth `∞`, `t`-independent for
    every `t`), `Π` is not solvable at all.
  * The same happens on any single `d`-regular graph whose port numbering is a proper edge colouring,
    such as high-girth bipartite graphs.
  * This also refutes the "reversible" / "exactly one round faster" claims of the abstract and §1.1.
  * *Fix.* We prove (2) ⇒ (1) under edge symmetry breaking at radius `t`: the endpoints of every edge
    have different radius-`(t−1)` views or different port numbers for the edge. This direction then
    needs no independence. Input orientations (Theorem 2, §4.4, Lemmas 3–4, Theorem 4), colourings or
    IDs (§4.5) and unique IDs (Theorem 3) all provide such symmetry breaking.
  * (`theorem_1_backward_false`, `theorem_1_backward_false_of_symmetric`; repaired: `theorem_1_backward`,
    `theorem_1`, `corollary_1`)
* **Minor imprecisions (under-specified, statements true).**
  * In the proof of Theorem 3, the new IDs should be spaced by `2Δ^t` *elements of `S`* (ranks), with
    room at both ends. The text asks for a difference of `2Δ^t + 1` in value. Not formalized.
  * In §5.1, the per-colour listing of the maximal `g'_{1/2}` configurations omits the swapped case
    `({⊸}, {→, ⊸, •})`. The trit description that is actually used handles it (`edgeAllMax_superweak`).
  * §4.4's `g_{1/2}` listing omits the configurations containing `∅` (harmless).
  * In the proof of Theorem 4, the edge joining a port to an opposite-orientation port of an identical
    node is "possible due to our choice of `G'`". We make this a hypothesis (`RichFor`).
  * The remark in §4.2 that, with node colourings or IDs, the simplification fails for
    "1-round ⇒ 0-round" is overly cautious: radius-1 edge views already contain both endpoints' inputs.
* **Typos.** In Theorem 4 the bound is `(log*Δ − 7)/5` once and `(log*Δ − 8)/5` later. With CSLib's
  `log*`, `5T + 7 ≤ log*Δ` suffices.

Model checking (not part of the Lean development). The unproved claim of §4.6 is that `h'_1` derived
from weak 2-colouring has only 9 elements. We checked it by exhaustive enumeration for `Δ = 3, 4, 5`:
there are exactly 9 maximal families with nonempty sets, plus one degenerate family containing `∅`.
For `Δ = 2` there are 8 ([`modelcheck/weak2_h1.c`](modelcheck/weak2_h1.c)).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Deterministic synchronous **port-numbering model**: CSLib's `PNGraph` and `Algorithm`. Nodes are
  anonymous and every port carries an input label (the paper's `Σ`-input-labelled graphs). A class is
  a set of such graphs on `Fin n` with all degrees `≤ Δ`. Algorithms may depend on `n`, `Δ` and `t`.
  There is no randomness.
* `N^t(v)` is the information gathered in `t` rounds, i.e. the full-information view `ViewT`.
  `N^t(e)` is the pair of radius-`(t−1)` views of the endpoints together with both port numbers.
  `solvableIn_iff_view` shows that "a `t`-round CSLib algorithm exists" is equivalent to "a function
  of radius-`t` views exists". The paper takes this equivalence as its definition.
* **Girth is not used.** With views defined as information, the proofs need only `t`-independence,
  which we copy verbatim (`IsIndependent`). Girth matters only for making independence true for
  natural classes; that part is not formalized.
* **Problems** (`Problem`): `f`, `g` (2-multisets) and `h` (multisets), as in §3. The operators are
  `edgeStep` (`Π_{1/2}`), `nodeStep`, `speedup` (`Π_1`), and the maximal versions `edgeStepMax`,
  `nodeStepMax`, `speedupMax` (`Π'_1`), with no "compression" of unusable labels.
* The proof itself is done once, for an abstract `ViewSystem` (`Abstract.lean`), and then
  instantiated (`viewSystem`).
* Theorem 4 is proved in the port-numbering model **with input orientations and no IDs**. The paper
  says such a version holds. We take as hypotheses: `t`-independence for all `t ≤ T+1`, and a
  richness condition on the class. The LOCAL-model statement additionally needs Theorem 3
  (order-invariance), Naor–Stockmeyer's Ramsey argument and the existence of high-girth graphs; none of
  these is formalized.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Problems, `Π_{1/2}`, `Π_1`, `Π'_{1/2}`, `Π'_1` (§3, §4.1–4.2) | `Problem`, `edgeStep`, `nodeStep`, `speedup`, `edgeStepMax`, `nodeStepMax`, `speedupMax` | `Problem.lean` |
| Theorem 1 (1) ⇒ (2) | `theorem_1_forward` | `Theorem1.lean` |
| Theorem 1 (2) ⇒ (1): **false** | `theorem_1_backward_false` | `Counterexample.lean` |
| Theorem 1 (2) ⇒ (1) with edge symmetry breaking; equivalence | `theorem_1_backward`, `theorem_1` | `Theorem1.lean` |
| Corollary 1 (corrected) | `corollary_1` | `Theorem1.lean` |
| Theorem 2 | `theorem_2` (orientation), `theorem_2_of_edgeAsym` | `Theorem1.lean` |
| §4.4 sinkless colouring/orientation | `sinkless_edgeAllMax`, `speedupMax_sinkless_relax`, `sinklessColoring_lower_bound`, `sinklessOrientation_lower_bound` | `Sinkless.lean` |
| §4.5 colour reduction on rings | `colorLabel_g`, `colorLabel_h`, `colorReduction_step`, `two_mul_card_reps` | `ColorReduction.lean` |
| §5.1 equivalent (trit) description | `edgeAllMax_superweak`, `toTrit_mem_h`, `ViewSystem.solvesE_toTrit` | `TritEquiv.lean` |
| Lemma 1 (for configurations of exactly `Δ` sets, as in the paper) | `lemma_1` | `Lemmas123.lean`, `Lemma1.lean` |
| Lemma 2 (Hall / matching step) | `lemma_2`, `exists_pairing_cover` | `Lemmas123.lean`, `Lemma2.lean`, `Matching.lean` |
| Lemma 3 | `lemma_3` | `Lemmas123.lean`, `Lemma3.lean` |
| Lemma 4 (port-numbering version) | `lemma_4` | `Theorem4.lean` |
| Weak 2-colouring ⇒ pointer version ⇒ superweak 2-colouring (§4.6, §5.2) | `solvableIn_weakPtr`, `weakPtrToSuperweak` | `WeakColoring.lean` |
| Theorem 4 (port-numbering version) | `theorem_4`, `theorem_4_paper` | `Theorem4.lean` |

**Not formalized.**
* Theorem 3 (order-invariant algorithms with unique IDs), and hence the LOCAL-model form of Lemma 4
  and Theorem 4.
* Existence of `t`-independent high-girth classes, the `Ω(log n)` and `O(log* n)` asymptotics, and
  the claim in §4.6 that `h'_1` has 9 elements (model-checked only).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The hypotheses are satisfiable:
* A simple graph with distinct input lists gives a class that is `t`-independent for all `t` and has
  edge symmetry breaking (`isIndependent_singleton_of_injective`).
* The counterexample class satisfies every hypothesis of the paper's Theorem 1.
* No witness is given for the combined hypotheses of `theorem_4` (`t`-independence for all `t ≤ T + 1`,
  `RichFor`, `log* Δ ≥ 5T + 7`). The paper obtains them from high-girth regular graphs, which are not
  formalized.

The port-numbering model and its algorithms come from CSLib
(`Cslib/Computability/Distributed/PortNumbering/Basic.lean`).

CSLib candidates (marked `-- CSLib candidate`): `Problem.lean` (round-elimination operators), `Abstract.lean`,
`PNModel.lean` (full-information views, `solvableIn_iff_view`, `SolvableIn.post`), `Matching.lean` (Hall-based
pairing lemma). The tower/log* lemmas now live in the shared `Podc/Foundations/Data/Nat/LogStar.lean`.
