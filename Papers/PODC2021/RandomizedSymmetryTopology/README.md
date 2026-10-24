# Topology of Randomized Symmetry Breaking — PODC 2021

Pierre Fraigniaud, Ran Gelles, Zvi Lotker. *The Topology of Randomized Symmetry-Breaking Distributed Computing.*
PODC 2021. DOI [10.1145/3465084.3467936](https://doi.org/10.1145/3465084.3467936). Formalized version: the
conference version (numbering follows it). For the proofs it defers we used the full version
[arXiv:2105.11713](https://arxiv.org/abs/2105.11713) v1. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** All main results hold in the model the paper describes in words (Section 2.1:
every node may send a message to each other node; port numbers "may assist in breaking symmetry"), which is the
standard port-numbering model that the full version's proof uses. But the formal knowledge equation for message
passing, **Eq. (2), mis-models it**: there a receiver never learns the port number at the sender's end. Read
literally with Eq. (2), the **"if" direction of Theorem 4.2 is false** (Lean counterexample `n₁ = 2`, `n₂ = 3`), and
the correct condition becomes the blackboard one, some `nⱼ = 1`. In the standard model we prove **both directions
of Theorem 4.2**. Theorem 4.1 (blackboard), Lemma 3.2, Lemma 3.5, Lemma 4.3 and Corollary 4.4 hold in both models.

## Mistakes in the paper

* **Eq. (2) does not model the paper's message-passing model, and with it Theorem 4.2 ("if") is false.**
  By Eq. (2), the knowledge
  `Kᵢ(t) = (Kᵢ(t-1), Xᵢ(t), K_{πᵢ(1)}(t-1), …, K_{πᵢ(n-1)}(t-1))` only records what lies behind each of *my*
  ports. The paper says that sending the whole history is without loss of generality, but no party ever learns the
  port number at the other end of a channel.

  Counterexample: `n = 5` and two sources, with parties 0, 1 on source 1 (`n₁ = 2`) and parties 2, 3, 4 on
  source 2 (`n₂ = 3`), so `gcd = 1`. Each party numbers its ports in increasing order of the other parties. Then
  parties 0 and 1 see the sources `(1, 2, 2, 2)` behind their ports, and parties 2, 3, 4 see `(1, 1, 2, 2)`. This
  partition by sources is equitable, so by induction parties with the same source have identical knowledge at
  every time, whatever the random bits. Nobody is ever alone, and leader election fails with probability 1.

  More generally, for any configuration in which every source feeds at least 2 parties, some port numbering is
  equitable in this sense. So in the model of Eq. (2) the worst-case characterization is "some `nⱼ = 1`", exactly
  as in the blackboard model.

  The paper's prose model (Section 2.1) lets every node send a message to each other node, and the full version's
  proof of the "if" direction (CreateMatching) sends ACKs back through a chosen port. This is the standard
  port-numbering model. Its full-information knowledge also records the sender's port, so the "without loss of
  generality" step leading to Eq. (2) is wrong. In the standard model Theorem 4.2 is **true**, and we prove the "if"
  direction with a short argument instead of the full version's sketch. Once the sources' bits differ, the knowledge
  partition stabilizes within `n` rounds. In a stable partition, a fixed port `p` with back-port `q` maps each class
  injectively into any other class, so all classes have the same size `m`. Each source is a union of classes, so
  `m ∣ gcd = 1`. (Eq. (2): `theorem_4_2_counterexample_explicit`, `theorem_4_2_if_false`, correct statements
  `worstCase_iff`, `worstCase_algorithm_iff`; standard model: `theorem_4_2_if_twoSided`, `corollary_4_4_standard`)
* **Lemma 3.2: proof gap, the statement is true.** The event `E = ⋃ₛ E_{st}` is not a tail event (it contains
  `E₀`), so Kolmogorov's zero–one law does not apply as stated. The argument is also not needed: disjoint windows
  are independent, so `Pr[no E_{st}, s < m] = (1-p)^m → 0`. Also, "`Kᵢ(t)` is included in `Kᵢ(s+t)`" is not
  literally true. The property actually needed is that knowledge at `s+t` determines the knowledge of the run that
  starts with the same window, which we prove for both models. (`lemma_3_2`, `lemma_3_2'`)
* **Proof of Lemma 4.3 (full version): the explicit construction has a typo, the lemma is true.** As printed,
  "port `j` of party `i` goes to `((i+j) mod g + ⌈i/g⌉g + ⌈j/g⌉g) mod n`" connects a party to itself whenever
  `1 < g < n` (e.g. `n = 4`, `g = 2`: port 2 of party 1). With floors `⌊i/g⌋`, `⌊j/g⌋` it is a valid port numbering
  (checked by script for `n ≤ 12`), and the argument goes through. We use other constructions.
  (`lemma_4_3`, `lemma_4_3_standard`)
* Small slip: in the proof of Lemma 3.2, "independent whenever `|s − s'| > t`" should read `≥ t`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Parties and sources.** `n` anonymous fault-free parties, synchronous rounds, `k` independent uniform bit
  sources. A configuration is `α : Fin n → Fin k` (not required to be surjective), and `nⱼ = load α j`.
- **Probability.** All `2^{kt}` source realizations of length `t` are equiprobable. `Pr[P(t) solves O | α]` is
  the fraction of them whose global state solves `O` (`probSolves`). No measure theory is used.
- **Full-information knowledge** is given by types defined by recursion on time.
  - Blackboard (Eq. (1)): `BBKnow (t+1) = BBKnow t × Bool × Multiset (BBKnow t)`.
  - Message passing (Eq. (2)): `MPKnow (t+1) = MPKnow t × Bool × (Fin (n-1) → MPKnow t)`, for a port numbering
    `π i : Fin (n-1) ≃ {j // j ≠ i}` chosen by the adversary.
  - Both are instances of `FullInfoModel`: knowledge is local, cumulative, and shift-refining.
- **Tasks and solvability.** A task is a set of output vectors. Definition 3.1 says a global state solves `O` if
  some decision map `f` on knowledge values has `f ∘ K ∈ O`. Definition 3.3 (eventually solvable) says
  `probSolves → 1`.
- **Consistency projections** of a single facet are represented by the name sets of their simplices, so a
  name-preserving simplicial map between them is an inclusion.
- **Uniform algorithms.** Since per-facet solvability lets `f` depend on the facet, we also prove that, for leader
  election in both models, one uniform decision rule applied one round later achieves the same probability. The
  positive results are therefore algorithmic.
- **Standard port model.** We additionally state Lemma 4.3 and Corollary 4.4 in CSLib's standard port-numbering
  model (`Cslib.PortNumbering`: port-dependent messages, receivers learn the sender's port). There they hold for
  all deterministic algorithms, even ones that read the whole random stream of their source in advance. For the
  "if" direction of Theorem 4.2 we use the full-information knowledge of this model: Eq. (2) with the sender's
  port added, `TSKnow (t+1) = TSKnow t × Bool × (Fin (n-1) → Fin (n-1) × TSKnow t)` (`tsModel`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 3.2 | `lemma_3_2`, `lemma_3_2'` (generic in the model and the task) | `ZeroOne.lean` |
| Definition 3.4, facets of `π̃(ρ)` | `RSolves`, `isFacet_consistencyComplex_iff` | `Realization.lean` |
| Lemma 3.5 | `lemma_3_5` | `Realization.lean` |
| Blackboard: equal bits ⇔ equal knowledge | `bbK_eq_iff` | `Blackboard.lean` |
| Theorem 4.1 | `theorem_4_1`; with a uniform algorithm `theorem_4_1_algorithm` | `Blackboard.lean`, `Algorithm.lean` |
| Eq. (25) | `theorem_4_1_bound` | `Blackboard.lean` |
| Lemma 4.3 (model of Eq. (2)) | `lemma_4_3` | `MessagePassing.lean` |
| Corollary 4.4 = Thm 4.2 "only if" | `corollary_4_4` | `MessagePassing.lean` |
| Lemma 4.3 / Cor 4.4 (standard port model) | `lemma_4_3_standard`, `corollary_4_4_standard` | `StandardPorts.lean` |
| Theorem 4.2 "if" — **false with Eq. (2)** | `theorem_4_2_if_false`, `theorem_4_2_counterexample_explicit` | `MessagePassing.lean` |
| Theorem 4.2 "if" (standard port model) | `theorem_4_2_if_twoSided` | `TwoSided.lean` |
| Correct worst-case characterization (Eq. (2)) | `worstCase_iff`, `worstCase_algorithm_iff` | `MessagePassing.lean`, `Algorithm.lean` |
| Observation after Def 3.1 (facet ⇒ algorithm) | `exists_algorithm`, `eventuallySolvable_iff_exists_algorithm` | `Algorithm.lean` |

**Not formalized.** Theorem 5.1 (an informal reduction of name-independent tasks with inputs). The
homotopy-level discussion.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity:
- the positive results exhibit explicit realizations of positive probability;
- the counterexample uses an explicit port numbering of `K₅`;
- `theorem_4_2_if_twoSided` is instantiated on the same configuration (`n₁ = 2`, `n₂ = 3`);
- `corollary_4_4_standard` is instantiated for 4 parties on two sources of load 2, and its graph is proved to be
  a clique.

The standard model comes from `Cslib.Computability.Distributed.PortNumbering.Basic` (`Algorithm.state_covering`).
CSLib candidates: the circulant port-numbered clique `StandardPorts.circulant` with its rotations, and
`StandardPorts.comapEquiv` (pulling a port-numbered graph back along a bijection).
