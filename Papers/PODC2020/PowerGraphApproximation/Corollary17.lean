import Papers.PODC2020.PowerGraphApproximation.Algorithm1
import Papers.PODC2020.PowerGraphApproximation.Centralized

/-!
# Corollary 17: Phase I of Algorithm 1 (`ε = 1/2`) followed by Algorithm 2 on `G²[U]`

[BCMPP20], Corollary 17 (combinatorial part): run Phase I of Algorithm 1 with `ε = 1/2`, then
run Algorithm 2 on the remaining graph `G²[U]`; the result is a `5/3`-approximation of MVC on
`G²`.

The paper justifies this by "the leader locally uses Theorem 12 to compute a 5/3-approximation
for the remaining graph". This does not follow from Theorem 12: `G²[U]` is an induced subgraph of
a square, not a square (every graph is an induced subgraph of some square), and the proof of
Theorem 12 (Lemma 13 (3)) needs the `G`-midpoint of every blue edge to be in the instance. The
corollary is nevertheless true: a midpoint outside `U` lies in `S` and has at most `l = 2`
`G`-neighbours in `U` (it is a non-centre or a processed centre), and Lemma 5 charges `S` at ratio
`3/2`, which is exactly what the triangles of part 1 are charged. See `induced_bound`.
-/

namespace Podc.PowerGraphApproximation

open SimpleGraph Finset Relation
open scoped Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **Corollary 17 of [BCMPP20]** (approximation part, sequential semantics). After Phase I of
Algorithm 1 with `ε = 1/2` (state `s`, cover `S = V \ R`) and a complete run of Algorithm 2 on
`G²[U]`, `U = R` (output `t.cover`), the set `S ∪ t.cover` is a vertex cover of `G²` of size at
most `(5/3) |OPT|`. -/
theorem corollary_17 {s : Algorithm1.State V}
    (h₁ : ReflTransGen (Algorithm1.Step G 2) Algorithm1.init s) {t : Centralized.State V}
    (h₂ : ReflTransGen (Centralized.Step G) (Centralized.init s.R) t)
    (ht : t.phase = .done) :
    (G.power 2).IsVertexCover (((univ \ s.R) ∪ t.cover : Finset V) : Set V) ∧
      ∀ OPT : Finset V, (G.power 2).IsVertexCover (OPT : Set V) →
        3 * ((univ \ s.R) ∪ t.cover).card ≤ 5 * OPT.card := by
  obtain ⟨hcov, hbound⟩ := Centralized.induced_bound h₂ ht
  refine ⟨Algorithm1.lemma_4 s hcov, fun OPT hOPT => ?_⟩
  have hS := (Algorithm1.inv_of_reach h₁).charge OPT (fun u _ v _ huv => hOPT huv)
  have hU := hbound OPT (fun u _ v _ huv => hOPT huv)
  have hsplit : (OPT ∩ (univ \ s.R)).card + (OPT ∩ s.R).card = OPT.card := by
    rw [← card_union_of_disjoint]
    · congr 1; ext v; by_cases hv : v ∈ s.R <;> simp [hv]
    · rw [Finset.disjoint_left]; intro v h1 h2
      exact (mem_sdiff.1 (mem_inter.1 h1).2).2 (mem_inter.1 h2).2
  have := card_union_le (univ \ s.R) t.cover
  omega

end Podc.PowerGraphApproximation
