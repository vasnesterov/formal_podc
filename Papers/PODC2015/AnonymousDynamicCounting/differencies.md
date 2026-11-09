# Differences between the formalization and the paper

Paper: G. A. Di Luna, R. Baldoni, *Investigating the Cost of Anonymity on Dynamic Networks*, PODC 2015
brief announcement; formalized from the full version arXiv:1505.03509v1.

## Mistakes in the paper (with labels)

1. ✏️ **Lemma 4, statement.** It says `min(Σ⁺k_r, Σ⁻k_r) = Σ⁻k_r = ½(3^r + 1) − 1`. The proof derives
   `Σ⁺k_r = ½(3^(r+1) + 1)`, hence `Σ⁻k_r = ½(3^(r+1) + 1) − 1 = ½(3^(r+1) − 1)`, which is correct
   (`lemma_4`; e.g. `Σ⁻k_1 = 4`, as the paper itself states before Lemma 2). The printed exponent is
   wrong (`lemma_4_statement_false`). The proof of Lemma 5 uses the correct value.
2. ✏️ **Lemma 5, round bound and quantifier.** The paper's round `r` means that the leader knows
   `m_r = M_r s_r` (rounds `0..r`). In that indexing indistinguishability holds iff
   `Σ⁻k_r ≤ n`, i.e. `r ≤ ⌊log₃(2n+1)⌋ − 1`, not `r ≤ ⌊log₃(2n+1)⌋` as printed. For `n = 3`, `r = 1` all
   pairs of sizes 3 and 4 are distinguished (`lemma_5_paper_indexing_false`), as the paper notes itself
   after Equation 5 ("if `n ≤ 3` it is possible to obtain the count in 2 rounds"). The proof of Lemma 5
   uses `½(3^(r+1)+1) − 1 ≤ n`, the correct condition, and Theorem 1 states `r < ⌊log₃(2|W|+1)⌋ − 1`,
   consistent with it. (In the round count of Definition 7, `S(v_l, t)` after `t` rounds, the printed
   bound `t ≤ ⌊log₃(2n+1)⌋` is exactly right: `lemma_5` with `3^t ≤ 2n+1`.) The statement also reads
   "Let us consider `M, M′` … does not exist an algorithm that distinguishes", which literally quantifies
   over all pairs; the intended (and proved) claim is existential.
3. ✏️ **Discussion.** "counting in `G(PD)₂` still requires `Ω(|V|)` rounds" should be `Ω(log |V|)`.
4. 🔧 **Proof of Lemma 2 (gap, statement true).** Independence of the rows of `M′_{r−1}`, "no row of `U`
   is a combination of rows of `M′_{r−1}`", and independence of the rows of `U` do not together imply
   independence of all rows (counterexample in `ℚ²`: `{e₁}`, `{e₂, e₁+e₂}`). The needed fact,
   `span U ∩ span M′_{r−1} = 0`, follows from the block structure. The independence of the rows of
   `M′_{r−1}` is argued only for combinations of two rows. We prove Lemma 2 differently: the kernel is
   computed directly (`inKer_iff`), then rank-nullity gives rank = number of rows (`lemma_2`).
5. 🔧 **Proof of Corollary 1 (gap, statement true).** "From this observation and Theorem 2 the corollary
   follows" omits the causality argument that yields the additive `D` (Theorem 2 alone gives only
   `Ω(log |V|)` on the chain network, which is not in `G(PD)₂`). With a chain of `D − 1` nodes between
   `v_l` and `v₁, v₂`, the leader is at distance `D + 1` from `W`, so the network has dynamic diameter
   `D + 1`. Repaired: `leader_agree` (states of a chain node at distance `d` from the relays agree `d`
   rounds longer) and `chainNet_diam` (our chain has `D − 1` nodes *including* the leader, giving
   diameter `D`); `corollary_1`.

## Typos (no claim affected)

- Lemma 2, base case: "`det(M_0) = 1`" for a non-square matrix.
- Before Equation 5: "9 variables (i.e. `3²` rows)" (columns).
- After Equation 2: `s′_0 = s_0 + t k_0` with `t ∈ ℕ` (should be `ℤ`, e.g. the example uses `s_0 = s′_0 − 2k_0`).
- Proof of Lemma 3, last paragraph: "for Lemma 2, `k_{r−1} = [(k_{r−2})_1 k_0 …]`" refers to the
  construction in Lemma 3's own induction step.
- Footnote/Definition 7: "`S(v_l, r)` = `[C(v_l, 0), …, C(v_l, r − 1)]`", but Section 4.2 writes the
  state after round 0 as `S(v_l, 0) = [{(1,[⊥]), (2,[⊥])}]`. The two indexings differ by one (source of
  item 2).

## Modelling choices and differences

- **Rounds.** Our `t` counts completed rounds (`DAlgo.leader M t`, `NAlgo.run G t v`). The paper's
  `M_r`, `k_r`, `m_r` are our objects for `t = r + 1` (words of length `r + 1`).
- **Counting (Definition 2).** "outputs `|V|` and terminates" is formalized as "the first output of the
  leader is `|V|`" (`FirstOutput`), with a deadline `f |V|` for a whole class of networks
  (`CountsWithin`, `CountsBy`). A per-instance lower bound (the literal reading of Lemma 1 / Theorem 1:
  "on an instance `M`") is meaningless for deterministic algorithms (an algorithm can hard-code one
  answer), so all lower bounds are stated for classes with a uniform deadline function.
- **Theorem 1** is stated as `2|W| + 1 < 3^(f |W|)` (`theorem_1`), i.e. `f |W| > ⌊log₃(2|W|+1)⌋`
  (`theorem_1_log`). The paper: no solution at a round `r < ⌊log₃(2|W|+1)⌋ − 1`, i.e. at least
  `⌊log₃(2|W|+1)⌋` rounds; ours is stronger by one round.
- **`M(DBL_k)`.** Parallel edges between `w` and the leader carry distinct labels, so a round of `M` is a
  nonempty label set `L r w ⊆ Fin k`; labels `1, 2` of the paper are `0, 1` in Lean. A node receives the
  leader's message once per incident edge, with the label (`DAlgo.run`); the leader receives
  `(label, message)` for every edge.
- **Leader state (Definition 7).** The paper defines the leader state as the sequence of multisets
  `C(v_l, i)` and remarks that it can be built by a message-passing protocol. We prove both directions:
  every algorithm's leader state is a function of these views (`DAlgo.leader_eq_of_view_eq`), and
  the full-information algorithm `fullInfo` computes them (`fullInfo_leader`).
- **Lemma 5 construction.** Nodes following the words with `k_r = −1` (resp. `+1`), one per word, plus
  `n − Σ⁻k_r` extra nodes with label set `{1,2}` in every round (`kGraph`). The paper's `s_r` with
  `(s_r)_j ≥ 1` exactly on the negative positions and `Σ s_r = n` is the same up to where the extra
  mass is put. Views are compared by counting (`card_rowMem_pos_eq_neg`).
- **Lemma 5 sharpness** (`lemma_5_sharp`) is an addition: it is the uniqueness part of the paper's
  kernel discussion ("under which condition of the kernel space we have a unique solution").
- **Lemmas 2–4** are stated for `k = 2`, as in the paper. Lemma 2 is stated both as a kernel
  characterization over any commutative ring (`inKer_iff`) and in matrix form over `ℚ` (`lemma_2`:
  `ker = span{k_r}`, `finrank ker = 1`, rank = #rows `= 3^(r+1) − 1`, rows linearly independent).
  Columns and rows are indexed by words (`List Lab`), not by positions in the lexicographic order.
  Lemma 3's block form `k_r = [k_{r−1}, k_{r−1}, −k_{r−1}]` is the first-letter recursion `kvec_cons`
  (`lemma_3`).
- **Lemma 1** is proved for every `k` and every chain length `L` (`L = 0` is the paper's `G`). The
  relays (`V₁`) are pairwise adjacent in our `G`; the paper does not fix edges inside `V₁`. The paper's
  `G_id` (relays with identifiers) is skipped: we simulate the anonymous `G` directly (the
  `M(DBL_k)`-leader knows each relay's identity from the labels). The simulation is round-for-round
  (`simAlgo_output`): there is no delay, since the `M`-leader simulates the relays in the same round.
- **Theorem 2** is proved directly (`chain_lower_bound` with `L = 0`) and also by the paper's route
  (`theorem_2_via_lemma_1`). The direct proof gains one round because the `G(PD)₂` leader hears from
  `V₂` one round late. The class is `InPD 2` (connected rounds, persistent distances `≤ 2`); the
  hard instances are `chainNet 2 0 M`.
- **Corollary 1.** The class is "every round connected and dynamic diameter `≤ D`" for `D ≥ 3`
  (`DiamLE`, via CSLib journeys; "a flood from `(x, r)` reaches `y` by the end of round `r + D − 1`",
  matching Figure 1, where `D = 4` and the flood started at round 0 arrives at round 3). For `D = 2` the
  construction does not apply (`W`-to-`W` floods need 3 rounds), and `D + Ω(log |V|)` is then the same
  as Theorem 2.
- **Not formalized:** the Discussion's `O(1)` algorithm with degree knowledge; the claim that the
  bound also holds in the model without edges inside a layer; the abstract's "`D ≤ 2h` in `G(PD)_h`";
  Figure examples.
