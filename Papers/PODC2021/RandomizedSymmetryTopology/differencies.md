# Differences between the formalization and the paper

Paper: Fraigniaud, Gelles, Lotker, *The Topology of Randomized Symmetry-Breaking Distributed Computing*,
PODC 2021 (DOI 10.1145/3465084.3467936). The proofs deferred in the conference version were read in the full
version arXiv:2105.11713v1.

## Errors found in the paper

1. **Eq. (2) mis-models the message-passing model; with Eq. (2) the "if" direction of Theorem 4.2 is false.**
   Eq. (2) defines `Kᵢ(t) = (Kᵢ(t-1), Xᵢ(t), K_{πᵢ(1)}(t-1), …, K_{πᵢ(n-1)}(t-1))`, justified by "without loss of
   generality each node sends its entire history". A receiver therefore never learns the port number at the
   sender's side. In this model a port numbering in which parties with the same source see the same sequence of
   sources behind their ports makes the partition by sources *equitable*, and it is never refined
   (`mpK_eq_of_equitable`). Hence worst-case leader election is eventually solvable iff some `nⱼ = 1`
   (`worstCase_iff`, `worstCase_algorithm_iff`), the same condition as for the blackboard (Theorem 4.1), not
   `gcd(n₁,…,n_k) = 1`. Counterexample: `n = 5`, `n₁ = 2`, `n₂ = 3`, ports of party `i` numbered in increasing
   order of the other parties; parties 0,1 always see sources `(1,2,2,2)` and parties 2,3,4 always see
   `(1,1,2,2)`, so nobody is ever alone in its knowledge class (`theorem_4_2_counterexample_explicit`,
   `theorem_4_2_counterexample`, `theorem_4_2_if_false`).
   The full version's proof of the "if" direction (Lemmas 4.7–4.8, procedure CreateMatching) sends an ACK "to the
   origin node" through a specific port, i.e. it uses the standard port-numbering model in which messages may
   depend on the outgoing port. Section 2.1 also says "every node can send a message to each other node". That is
   not the model of Eq. (2): the "without loss of generality" step is wrong, because a full-information message
   on port `p` must also carry `p`. In the standard model Theorem 4.2 holds. We prove the "if" direction in
   `TwoSided.lean` (`theorem_4_2_if_twoSided`), with knowledge `Eq. (2)` + back-ports (`tsK`). The proof is not the
   full version's CreateMatching sketch (which is informal: it relies on "full information simulates any
   protocol" and on the parties of `V₁`, which share one source, making "random" picks). Our argument:
   after `k` rounds of a realization separating the sources, the knowledge partition stabilizes within `n` rounds
   (`exists_stable`). In a stable partition, `c ↦ π_c(p)` maps a class injectively into another class
   (`card_class_le`), so all classes have the same size `m`, and `m` divides every `nⱼ`. The "only if" direction
   in the standard model is `corollary_4_4_standard`. Since the theorem holds in the model the paper describes
   and uses in its proof, we count this as a modelling error in Eq. (2), not as a false theorem.
2. **Lemma 3.2, proof.** `E = ⋃ₛ E_{st}` is called a tail event; it is not (it contains `E₀`). The conclusion
   holds anyway because the disjoint windows are independent, so `Pr[no E_{st}, s < m] = (1-p)^m → 0`; we
   formalize this counting argument (`IsGoodEvent.one_sub_pow_le_probEvent`) and no zero–one law is needed. The
   proof also says that `E_s` makes `Kᵢ(t)` "included in" `Kᵢ(s+t)`. Literally this is false (the knowledge
   started at time `s` is a different nested object). What is true and needed is that the knowledge at `s + t`
   *determines* the knowledge of the run that starts with the window, i.e. it is a refinement
   (`FullInfoModel.shift`, proved for both models in `bbK_shift` and `mpK_shift`). "Independent whenever
   `|s - s'| > t`" should read `≥ t`.
3. **Proof of Lemma 4.3 (full version), typo.** The explicit port numbering "port `j` of party `i` goes to
   `((i+j) mod g + ⌈i/g⌉g + ⌈j/g⌉g) mod n`" (ceilings, as printed) is not a port numbering whenever `1 < g < n`.
   For example, for `n = 4` and `g = 2`, party 1 has its port 2 connected to itself. With floors `⌊i/g⌋`, `⌊j/g⌋`
   it is a valid port numbering for all `n ≤ 12` (checked by script), and the rotation `f` is then an automorphism,
   so this is a typo. The lemma is true; we use different constructions: `swapPorts` for Eq. (2), and a relabelled circulant clique with the rotation by
   `n/g` as automorphism for the standard model (`StandardPorts.lean`).

## Modelling choices

- **Parties, sources, configurations.** `α : Fin n → Fin k` is any map. The paper requires the used sources to be
  exactly `1..k` (`α` surjective, `nᵢ ≥ 1`). Our statements hold without this assumption (unused sources do not
  change the probability, and `gcd` is unaffected by zero loads). `load α j` is the paper's `nⱼ`.
- **Rounds** are numbered from 0 (`ω s j` is the bit of source `j` in round `s+1`).
- **Randomness and probability.** `Pr[P(t) solves O | α]` is the fraction of the `2^{kt}` equiprobable source
  realizations of length `t` (`probSolves`). This is Eq. (7)/(20) combined with Lemma B.1 of the full version
  (positive-probability node realizations are exactly those induced by source realizations, each with probability
  `2^{-kt}`). No measure theory and no infinite product space is used. "Eventually solvable" (Definition 3.3) is
  `Tendsto (probSolves …) atTop (𝓝 1)`.
- **Knowledge.** It is modelled by types defined by recursion on `t`: `BBKnow (t+1) = BBKnow t × Bool × Multiset
  (BBKnow t)` (Eq. (1), with the blackboard as a multiset, so the "lexicographic order" convention is not needed)
  and `MPKnow d (t+1) = MPKnow d t × Bool × (Fin d → MPKnow d t)` (Eq. (2)). The generic framework
  `FullInfoModel` records the three properties used by Lemma 3.2: locality, cumulativity and the shift/refinement
  property.
- **Port numberings** are bijections `Fin (n-1) ≃ {j // j ≠ i}` for every party (ports `0..n-2` instead of
  `1..n-1`).
- **Complexes.** The protocol complex, the realization complex and the output complex are not built as simplicial
  complexes. A facet of `P(t)` is a global state `κ : Fin n → Know t`, a facet of `O` is an output vector. The
  consistency projections `π(σ)`, `π̃(ρ)` of a single facet are given by the name sets of their simplices
  (`consistencyComplex`). Since name-preserving maps between complexes on the same name set are unique, "there is a
  name-preserving simplicial map `π̃(ρ) → π(τ)`" becomes inclusion of simplex sets (`RSolves`). Facets of `π̃(ρ)`
  are the consistency classes (`isFacet_consistencyComplex_iff`), so `dim γ + 1 = |γ|`.
- **The isomorphism `h` between facets of `P(t)` and `R(t)`** is implicit: knowledge is *computed* from the
  realization (so the facet of `P(t)` is a function of the facet of `R(t)`), and knowledge determines the party's
  own bits (`bbK_eq_iff`, `bits_eq_of_mpK_eq`).
- **Lemma 3.5** needs the output type to be nonempty (to extend the decision map to knowledge values that do not
  occur). This is a harmless side condition.
- **Algorithmic meaning of Definition 3.3.** The paper argues informally (after Definition 3.1) that per-facet
  solvability yields an algorithm one round later. We prove this for leader election in both models, with an
  explicit uniform decision rule (`exists_algorithm`, `eventuallySolvable_iff_exists_algorithm`,
  `theorem_4_1_algorithm`, `worstCase_algorithm_iff`). The impossibility results are stated for per-facet
  solvability, which covers every algorithm (`probAlg_le_probSolves`).
- **Lemma 4.3** is stated for every `g` dividing all loads (in particular `g = gcd`). It is stated for every
  realization, since all source realizations have positive probability.
- **Standard (two-sided) port model, knowledge version.** For the "if" direction of Theorem 4.2 we use the
  full-information knowledge of the standard model in the paper's framework (`tsModel`, a `FullInfoModel`):
  `Kᵢ(t) = (Kᵢ(t-1), Xᵢ(t), ((q_p, K_{πᵢ(p)}(t-1)))_p)`, where `q_p` is the port of `πᵢ(p)` leading back to `i`.
  The positive result is per-facet solvability (Definition 3.3), as for Theorem 4.1.
- **Standard (two-sided) port model.** We also prove Lemma 4.3 and Corollary 4.4 in CSLib's port-numbering model
  `Cslib.PortNumbering` (messages may depend on the port; receivers learn the sender's port), for *every*
  deterministic algorithm. There, each party gets the whole random stream of its source as its input. This is
  stronger than the paper, because the algorithm may read future bits, and that only strengthens impossibility.
  The statement is about classes of equal *states* of an arbitrary algorithm rather than knowledge classes.
- **Theorem 4.1, "if" direction.** Besides the limit, we prove the quantitative bound of Eq. (25),
  `Pr[S(t)] ≥ 1 - (k-1)/2^t` (`theorem_4_1_bound`). We prove eventual solvability itself through Lemma 3.2,
  using a single positive-probability realization of length 1 (source `j` emits 1, all others 0).
- **Case `k = 1` of Theorem 4.1** is not treated separately. The paper's "base case" says `n₁ = 1` forces `n = 1`.
  Our proof is uniform in `k`.

## Not formalized

- **Theorem 5.1 / Theorem C.1** (name-independent tasks reduce to leader election). The statement is informal:
  "solvable" is not defined for tasks with inputs, and the reduction sends per-port messages, which Eq. (2) does
  not allow.
- The topological discussion (homotopy, Figures 1–3) has no formal content beyond the definitions above.
