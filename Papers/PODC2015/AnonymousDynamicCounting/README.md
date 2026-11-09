# The Cost of Anonymity on Dynamic Networks — PODC 2015

Giuseppe Antonio Di Luna, Roberto Baldoni. *Brief Announcement: Investigating the Cost of Anonymity on
Dynamic Networks.* PODC 2015. DOI [10.1145/2767386.2767442](https://doi.org/10.1145/2767386.2767442).
Formalized version: arXiv [1505.03509](https://arxiv.org/abs/1505.03509) v1 (the full version, with all
proofs); numbering follows it.

**Verdict: 🔧 Easy fix.** All main results hold: counting in `G(PD)₂` takes `Ω(log |V|)` rounds
(Theorem 2), and with constant dynamic diameter `D` it takes `D + Ω(log |V|)` rounds (Corollary 1). The
linear-algebra core (Lemmas 2–4) is right. Lemma 4's formula and Lemma 5's round bound are each printed
off by one; their proofs and Theorem 1 use the right values. Two proofs have local gaps, which we
closed: the rank argument of Lemma 2 and the chain argument of Corollary 1.

## Mistakes in the paper

### ✏️ Slips
- **Lemma 4** states `Σ⁻ k_r = ½(3^r + 1) − 1`, but its proof derives `½(3^(r+1) + 1) − 1`, the true value
  (`lemma_4`). The text before Lemma 2 itself lists `Σ⁻ k_1 = 4`, while the printed formula gives `1`
  (`lemma_4_statement_false`).
- **Lemma 5** claims indistinguishability up to round `r ≤ ⌊log₃(2n+1)⌋`. In the paper's own indexing
  (the leader knows `m_r = M_r s_r` at round `r`) this is one round too many. For `n = 3`, `r = 1` every
  pair of multigraphs of sizes 3 and 4 is distinguished, as the text after Equation 5 says itself
  (`lemma_5_paper_indexing_false`, from the sharp form `lemma_5_sharp`). The proof gives
  `r ≤ ⌊log₃(2n+1)⌋ − 1`, which is what Theorem 1 uses. (Read with Definition 7's indexing, where
  `S(v_l, r)` holds rounds `0..r−1`, the printed bound is exactly right (`lemma_5`); the slip is then
  in the proof's first step, which derives `½(3^(r+1)+1) − 1 ≤ n` from `r ≤ ⌊log₃(2n+1)⌋`.) The lemma
  also says "Let us consider `M, M′`" where it means "there exist `M, M′`".
- **Discussion:** counting in the restricted `G(PD)₂` "still requires `Ω(|V|)` rounds" should read
  `Ω(log |V|)`.

### Typos
- Lemma 2, base case: "`det(M_0) = 1`" for the 2×3 matrix `M_0`.
- Before Equation 5: "9 variables (i.e. `3²` rows)" should be columns; after Equation 2, `s′_0 = s_0 + t k_0`
  needs `t ∈ ℤ`, not `t ∈ ℕ`.
- Proof of Lemma 3, last step: the block form of `k_{r−1}` comes from Lemma 3's own construction, not
  from Lemma 2.

## Proof gaps (statements true)

### 🔧 Lemma 2 (rows of `M_r` are linearly independent)
The proof shows three facts: the rows of `M′_{r−1}` are independent, no row of `U` is a combination of
rows of `M′_{r−1}`, and the rows of `U` are independent. These three facts do not imply that all rows
together are independent.

**Impact.** Statement true; proved (`lemma_2`).

**Details.** For example, `e₁` and `{e₂, e₁+e₂}` satisfy all three facts, yet `e₁, e₂, e₁+e₂` are
dependent. The proof needs `span U ∩ span M′_{r−1} = 0`. This follows from the paper's block
observation: on every 3-column block a combination of `U`-rows is `a(1,0,1) + b(0,1,1)`, which is
constant only for `a = b = 0`. The independence argument for `M′_{r−1}` also treats only combinations of
two rows.

**Repair.** We compute the kernel directly: the integer, rational or any-ring solutions of `M_r d = 0`
are exactly the multiples of `k_r` (`inKer_iff`, by induction on the first letter, i.e. the paper's
block form `k_r = [k_{r−1}, k_{r−1}, −k_{r−1}]`). Rank-nullity then gives rank = number of rows
`= 3^(r+1) − 1` (`lemma_2`).

### 🔧 Corollary 1 (`D + Ω(log |V|)` for constant `D`)
The proof attaches the `G(PD)₂` part to the leader by "a static chain of `D − 1` nodes" and says the
corollary follows from Theorem 2. Theorem 2 alone does not give the additive `D`, and with `D − 1` chain
nodes the dynamic diameter is `D + 1`, not `D`.

**Impact.** Statement true; proved with explicit constants (`corollary_1`).

**Details.** The additive `D` needs a causality argument. Information from `W` reaches the leader
only through the chain, so the leader's state at round `T` depends only on what happened in `W`
before round `T − D + 1`.

**Repair.** We use a chain of `D − 1` nodes counting the leader. This network is 1-interval connected,
has dynamic diameter `D` (`chainNet_diam`), and the leader cannot tell apart two multigraphs whose
views agree for `t` rounds until round `t + D − 1` (`leader_agree`). Hence counting needs
`D + ⌊log₃(2(|V| − D − 1) + 1)⌋` rounds (`corollary_1`), and at least `D + ⌊log₃ |V|⌋` for
`|V| ≥ 2D + 1` (`corollary_1_log`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Synchronous rounds `0, 1, …`, deterministic algorithms, no failures, no randomness. All non-leader
  nodes run the same code from the same initial state; the leader starts in its own state.
- **Dynamic networks** (`DynNet`, `NAlgo`): in round `r` an adversary picks an arbitrary graph `E r`.
  Every node broadcasts one message of unbounded size and receives the *multiset* of its neighbours'
  messages (anonymous broadcast; the degree is not known before receiving). Counting (Definition 2):
  the leader's first output is `|V|`. A class of networks is counted within `f` if this happens by
  round `f |V|` on every network of the class (`NAlgo.CountsWithin`). This is weaker than "outputs and
  terminates", so the lower bounds are stronger. `G(PD)_h` (`InPD`): every round is connected and every
  node keeps a fixed distance `≤ h` from the leader. Dynamic diameter `≤ D` (`DiamLE`): a temporal
  journey (CSLib `DynNet.Journey`) from every `(x, r)` to every `(y, r + D)`.
- **`M(DBL_k)`** (`DBL`, `DAlgo`): in round `r` node `w` is joined to the leader by edges with the
  nonempty label set `L r w ⊆ {1..k}`, and every message arrives with its edge label. `hist` and `view`
  are the paper's node state `S(w, t)` and leader multiset `C(v_l, t)` (Definitions 6, 7).
  `leader_eq_of_view_eq` proves the paper's remark that the leader's state is a function of the views.
  `fullInfo` attains them, so the views are exactly what a leader can know.
- **Indexing.** Our `t` counts completed rounds. The paper's `M_r`, `k_r` (knowledge at the end of round
  `r`) are our objects for `t = r + 1`.
- The reduction network `chainNet k L M` has a static path of `L + 1` nodes ending in the leader, `k`
  relays (the paper's `V₁`), and `W`. Relay `j` and `w` are adjacent in round `r` iff `j ∈ L r w`. We
  make the relays pairwise adjacent; the paper leaves this open, and either choice is in `G(PD)₂`. For
  `L = 0` this is the paper's `G` (`chainNet_mem_PD`); for `L = D − 2` it is the network of Corollary 1.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (reduction `M(DBL_k)` → `G(PD)₂`, same round) | `lemma_1`, `simAlgo_output`, `chainNet_mem_PD` | `Network.lean` |
| Lemmas 2, 3 (kernel of `M_r` is `span k_r`, rank = #rows) | `inKer_iff`, `lemma_2`, `lemma_3` | `Kernel.lean` |
| Lemma 4 (`Σ k_r = 1`, `Σ⁻ k_r = ½(3^(r+1)+1) − 1`) | `lemma_4` (printed value: `lemma_4_statement_false`) | `Kernel.lean` |
| Lemma 5 (sizes `n`, `n+1` indistinguishable) | `lemma_5`; sharp: `lemma_5_sharp`, `fullInfo_distinguishes`; printed bound: `lemma_5_paper_indexing_false` | `Multigraph.lean` |
| Theorem 1 (`M(DBL_k)` lower bound) | `theorem_1`, `theorem_1_log` | `Multigraph.lean` |
| Theorem 2 (`Ω(log |V|)` on `G(PD)₂`) | `theorem_2`, `theorem_2_log`, `theorem_2_via_lemma_1` | `Network.lean` |
| Corollary 1 (`D + Ω(log |V|)`) | `corollary_1`, `corollary_1_log`, `chainNet_diam`, `leader_agree` | `Network.lean` |

Our bounds are slightly stronger than the paper's. Theorem 1: the leader of an `n`-node multigraph
needs more than `⌊log₃(2n+1)⌋` rounds. The paper says at least `⌊log₃(2|W|+1)⌋`. Theorem 2: on
`G(PD)₂`, `f |V| ≥ ⌊log₃(2|V| − 5)⌋ + 2`. This gains one round over the paper's route (Lemma 1 +
Theorem 1, `theorem_2_via_lemma_1`), because the `G(PD)₂` leader hears from `V₂` only through `V₁`.
`lemma_5_sharp` shows that Lemma 5 is tight. For `3^t > 2n + 1`, any two multigraphs of sizes `n`
and `n + 1` give different leader states after `t` rounds. This is the uniqueness half of the paper's
kernel analysis, and the bound of the method cannot be improved for the pair `(n, n+1)`.

**Not formalized.** The Discussion's `O(1)` algorithm when nodes know their degree in advance, and the
remark that the lower bound survives in the restricted model without edges inside a layer (our relays are
adjacent to each other). The abstract's "`D ≤ 2h` in `G(PD)_h`". Lemmas 2–5 are formalized for `k = 2`,
as in the paper. Theorem 1 is proved for all `k ≥ 2` through `M(DBL₂) ⊆ M(DBL_k)`; for `k = 1` counting
takes one round.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The lower-bound hypotheses are not vacuous: the classes contain the explicit networks
`chainNet` (`chainNet_mem_PD`, `chainNet_connected`, `chainNet_diam`). Journeys come from CSLib
(`Cslib.Computability.Distributed.DynamicNetworks.Journey`); everything else is self-contained, in
namespace `Podc.AnonymousDynamicCounting`. No `Podc/` code and no CSLib candidates.
