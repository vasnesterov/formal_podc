# Differences between the formalization and the paper

Paper: Charron-Bost, Lambein-Monette, *Know your audience*, arXiv 2311.17728 v1 (full version of the PODC 2024 brief
announcement). Only Sections 2–4 (static networks) are formalized.

## Statement-level issues (with the deciding rule of `verdicts.md`)

1. **Theorem 4.1, (ii) ⇒ (i), false for every model at `n = 1`.** `isSingleton` is computable and not
   frequency-based (`theorem_4_1_ii_imp_i_false`). Taken alone this is degenerate (R2: `n ≤ 1`), hence ⚠️ for
   outdegree and output port awareness.
2. **Theorem 4.1, (ii) ⇒ (i), false for symmetric communications at `n = 2` (`K₂`).** `isPair` is computable and not
   frequency-based on lengths ≥ 2 (`theorem_4_1_false_symmetric_K2`). Theorem 4.1 is the headline result (R5), so
   the grade hinges on R2. **Decision (review): degenerate, hence ⚠️.** Reasons:
   * *The paper's model does not rescue the theorem.* §2.1 defines the round graph as `([n], E_t)` with `E_t` a set of
     pairs (a simple digraph) and a self-loop at every vertex; §2.2 gives the transition function the *multiset* of
     received messages (so agents learn their indegree); multigraphs appear only in §3, for bases of fibrations
     ("executions … defined for simple edge graphs naturally extend to multi-graphs"). Theorem 4.1 quantifies over
     `f : ⋃_{n>0} Ω^n → X` and "the class of static strongly connected networks", which contains `n = 1, 2`. If
     multigraph networks were allowed (`R_1`, `R_2` legal), indegree would no longer reveal `n ≤ 2`; but they are not.
     So the statement is false as written, not an artefact of our modelling.
   * *Implied assumption?* The proof's rings `R_n`, `R_m`, `R_p` are simple networks only for sizes ≥ 3, so the paper
     implicitly works with `n ≥ 3`, but it never states it and claims all `n > 0`; R4 alone would not excuse it.
   * *Degenerate (R2: "n = 2 when the problem is trivial for 2").* The failures occur exactly at the sizes where the
     network is unique and self-identifying: `n = 1` in every model, and `n = 2` only with symmetric links, where `K₂`
     is the only 2-agent network and both agents know it after two rounds. There, function computation is trivial:
     every multiset-based function of 2 inputs is computable. In the directed models `K₂` is not recognisable
     (it is covered by `C_4`) and the theorem holds at `n = 2`. The counterexample functions only separate these
     trivial sizes from the rest; on all networks of size ≥ 3 the characterisation, its examples (average computable,
     sum not) and its proof are correct. The project's precedents grade `n = 2` failures where the 2-agent instance is
     trivial as degenerate (e.g. GoodCaseLatencyBB, CommComplexityBA, AllBAExpensive). The paper's own footnote to
     Table 1 ("for `n < 4` the topology always allows the recovery of the multiset") shows the same kind of
     small-network exception is treated by the authors as a side remark.
   * *Borderline.* R2 lists `K₂` as non-degenerate "for a distributed algorithm". Here no algorithm fails on `K₂`;
     the false claim is an impossibility whose only counterexamples exploit that `K₂` is trivially solvable. A reader
     who weighs R2's `K₂` example more heavily would grade 🚨 (R5, headline). The formalization author proposed 🚨;
     the review grades ⚠️ for the reasons above.
3. **Corollary 4.2 is false as stated** (same counterexamples; `corollary_4_2_false`). It is a corollary of the
   headline and was proved by the same flawed argument. Covered by item 2.
4. **Lemma 3.3 is imprecise.** It holds only for vectors whose length is the size of some network in the class
   (`Computes.perm_eq` takes such a network as hypothesis). The assumption holds at every use in the paper (R3/R4: ⚠️).
5. **Theorem 4.1 (i) ⇒ (ii), Corollary 4.3 and Corollary 4.4 are true as stated** (`theorem_4_1_i_imp_ii`,
   `corollary_4_3`, `corollary_4_4`).

## Proof-level issues

6. **§4.1:** the rings `R_p` for `p ∈ {1, 2}` (and `R_n`, `R_m` for input lengths ≤ 2) are multigraphs (`R_2`: two parallel edges plus a loop; `R_1`: three
   loops), not networks of the class, so "A δ-computes `f^φ` on `R_p`" is unjustified. Replaced by coverings of
   directed cycles `C_{n'n} → C_n` (`n ≥ 2`) or bidirectional rings (`n ≥ 3`) plus Lemma 3.3 at length `nn'`
   (`eq_of_freq_eq_of_covers`).
7. **§4.3, symmetric variant (not formalized):** it assumes that the minimum base has a Hamiltonian path
   ("up to permutation, none of `d_{1,2}, …, d_{m−1,m}` is zero"). This is false, e.g., for a star with distinct
   inputs. A spanning tree repairs it. (`pdftotext` renders the fraction in the definition of `z_i` upside down; the
   rendered page has the correct orientation `d_{2,1}⋯d_{i,i−1} / d_{1,2}⋯d_{i−1,i}`.)
8. **§4.2, rank one:** the paper's Perron–Frobenius argument is replaced by an elementary maximum principle
   (`exists_eq_mul_of_irreducible`). Both are correct.

## Modelling choices

9. **Networks** are simple digraphs on `Fin n` with self-loops, as in §2.1 (`Network`: out-neighbourhoods +
   output port numbering; ports `0, …, d−1` instead of `1, …, d`). The port numbering is part of the network and
   quantified over (it is irrelevant for models that do not see ports).
10. **Lifting lemma** is stated for fibrations between simple networks: vertex maps that are bijective on
    in-neighbourhoods. The paper states it for multigraphs. Model compatibility (`Fibration.Compatible`) asks for
    outdegree preservation (outdegree awareness) and also port preservation (output port awareness). This is the
    paper's fibration of valued/coloured graphs. Surjectivity is part of the structure but not needed for lifting.
11. **Algorithms**: arbitrary state/message types, `init : Ω → Q`, `send : Q → ℕ → ℕ → M`,
    `trans : Q → Multiset M → Q`, `out : Q → X`. The paper uses states `Ω × X` (with further components), a set
    `Q₀` of initial states, and "every execution". Our counterexample algorithms output the right value from round
    1 (resp. 2) from *any* initial configuration (`detectOne_out`, `detectTwo_out`), so they also compute in the
    paper's sense. Our positive algorithms start from a fixed initial state. That is an algorithm in the paper's
    sense with `Q₀` = the initial states; the paper's own positive claims (self-stabilization) are stronger and not
    formalized.
12. **Functions** `f : List Ω → X`; the value on `[]` is irrelevant. `freq l a = count a l / |l|` is the paper's
    `ν_v`. `FrequencyBased`, `MultisetBased` follow §2.3. `FrequencyBasedFrom k` is our corrected class.
13. **Computability**: convergence in a topological space `X`; the main statements take `[MetricSpace X]`. The
    counterexamples use `X = ℕ` (discrete metric).
14. **Communication models**: symmetric communications = simple broadcast on bidirectional networks, as in §2.2.
15. **Leaders**: one leader is an input component `Bool` with exactly one `true` (`OneLeader`). The function
    computed is `f` of the values. The extension to `ℓ` known leaders (remark after Cor. 4.4) is not formalized.
16. **Known size / bound**: classes `sizeEq k`, `sizeLE B`; "computable when `n` (a bound) is known" = computable in
    each of these classes (§4.4).

## Algorithmic differences (positive direction)

17. The paper's algorithm is Boldi–Vigna's finite-state self-stabilizing minimum-base construction, followed by
    Gaussian elimination over `ℤ`. Ours is an infinite-state view algorithm. At round `t + 2` it decodes the
    depth-`⌊t/2⌋+1` colour-refinement classes found within lookahead `t − ⌊t/2⌋`, solves eq. (1) by choosing any
    positive integer solution, and outputs `f` of the resulting multiset. Correctness needs refinement to have
    stabilised and the lookahead to cover all agents. We prove "eventually", without the paper's `n + D` bound.
    Finite-state operation, self-stabilization and the time bound are not formalized.
18. **Output port awareness** uses the outdegree algorithm (allowed in that model), not the covering-based variant
    of §4.3. **Symmetric communications** use untagged views and read class outdegrees as indegrees (no
    outdegree-learning phase), not the formula of §4.3.
19. For the corrected classes the algorithm tests `n = 1` (indegree 1) and, for symmetric communications,
    `n = 2` (the `K₂` test of the counterexample). Otherwise it outputs `f` of the decoded multiset repeated 2
    (resp. 3) times, so that its length is in the range where `f` is frequency-based.

## Not formalized

20. Section 5 (dynamic networks: Lemma 5.1, Theorem 5.2 / Push-Sum, Corollaries 5.3–5.5, §5.5), Section 6, Tables 1–2
    beyond the static rows of the three models, the simple-broadcast column (cited results), and the claim that
    "`f` frequency-based ⇒ computable" holds in linear time.
