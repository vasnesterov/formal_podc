import Papers.PODC2020.PowerGraphApproximation.Corollary17

/-!
# The proof of Corollary 17 misapplies Theorem 12

The proof of Corollary 17 says that the leader "locally uses Theorem 12 to compute a
5/3-approximation for the remaining graph" `G²[U]`. Theorem 12 is about squares `G²`, and the
remaining graph is only an induced subgraph of one. Here is a run where Algorithm 2 on the
remaining graph is only a 2-approximation.

`G` has vertices `aᵢ, bⱼ` (`i, j < 4`) and a midpoint `wᵢⱼ` adjacent to `aᵢ` and `bⱼ`. Phase I of
Algorithm 1 with `ε = 1/2` picks the centres `a₀, a₁, a₂, a₃` and moves all `wᵢⱼ` into `S`; it ends
with `U = {aᵢ} ∪ {bⱼ}` and `G²[U] = K₄,₄`. This graph is triangle-free and 4-regular, so parts 1
and 2 of Algorithm 2 do nothing and part 3 may take all 8 vertices (both endpoints of the perfect
matching `aᵢbᵢ`, a valid 2-approximation). But `{aᵢ}` (4 vertices) covers `G²[U]`.

The overall bound of Corollary 17 still holds (`corollary_17`); only the paper's argument fails.
-/

namespace Podc.PowerGraphApproximation.Cor17Gap

open SimpleGraph Finset Relation

/-- Vertices: `aᵢ`, `bⱼ`, `wᵢⱼ`. -/
abbrev V := Fin 4 ⊕ Fin 4 ⊕ (Fin 4 × Fin 4)

def a (i : Fin 4) : V := .inl i
def b (j : Fin 4) : V := .inr (.inl j)
def w (i j : Fin 4) : V := .inr (.inr (i, j))

/-- Adjacency: `aᵢ ~ wᵢⱼ ~ bⱼ`. -/
def adjB : V → V → Bool
  | .inl i, .inr (.inr (i', _)) => i == i'
  | .inr (.inr (i', _)), .inl i => i == i'
  | .inr (.inl j), .inr (.inr (_, j')) => j == j'
  | .inr (.inr (_, j')), .inr (.inl j) => j == j'
  | _, _ => false

/-- The graph `G`. -/
def G : SimpleGraph V where
  Adj u v := adjB u v = true
  symm := ⟨fun u v h => by revert u v; decide⟩
  loopless := ⟨fun v h => by revert v h; decide⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (adjB u v = true))

lemma gnbrs_eq (R : Finset V) (c : V) :
    Algorithm1.gnbrs G R c = R.filter fun v => G.Adj c v := by
  unfold Algorithm1.gnbrs; exact filter_congr_decidable _ _ _

lemma nbrs_eq (R : Finset V) (c : V) :
    Centralized.nbrs G R c = R.filter fun v => (G.power 2).Adj c v := by
  unfold Centralized.nbrs; exact filter_congr_decidable _ _ _

lemma pick' {s : Algorithm1.State V} {c : V} {C' R' : Finset V} (hc : c ∈ s.C)
    (hbig : 2 < (s.R.filter fun v => G.Adj c v).card) (hC : ∀ v, v ∈ C' ↔ v ≠ c ∧ v ∈ s.C)
    (hR : ∀ v, v ∈ R' ↔ v ∈ s.R ∧ ¬ (v ∈ s.R ∧ G.Adj c v)) :
    Algorithm1.Step G 2 s ⟨C', R'⟩ := by
  have h := Algorithm1.Step.pick (G := G) (l := 2) hc (by rwa [gnbrs_eq])
  convert h using 2
  · ext v; rw [hC, @mem_erase V (fun a b => Classical.propDecidable (a = b))]
  · ext v; rw [hR, @mem_sdiff V (fun a b => Classical.propDecidable (a = b)), gnbrs_eq,
      mem_filter]

/-- Centres not yet processed after `k` picks. -/
def Cs (k : ℕ) : Finset V := univ.filter fun v => ∀ i : Fin 4, v = a i → k ≤ i
/-- Vertices not in the cover after `k` picks. -/
def Rs (k : ℕ) : Finset V := univ.filter fun v => ∀ i j : Fin 4, v = w i j → k ≤ i

/-- The remaining set `U = {aᵢ} ∪ {bⱼ}`. -/
def U : Finset V := univ.filter fun v => ∀ i j : Fin 4, v ≠ w i j

lemma Rs_four : Rs 4 = U := by decide

lemma phase1 : ReflTransGen (Algorithm1.Step G 2) Algorithm1.init ⟨Cs 4, Rs 4⟩ := by
  have e0 : (Algorithm1.init : Algorithm1.State V) = ⟨Cs 0, Rs 0⟩ := by
    simp only [Algorithm1.init, Algorithm1.State.mk.injEq]; constructor <;> decide
  rw [e0]
  refine .tail (b := ⟨Cs 3, Rs 3⟩) (.tail (b := ⟨Cs 2, Rs 2⟩)
    (.tail (b := ⟨Cs 1, Rs 1⟩) (.single ?_) ?_) ?_) ?_
  · exact pick' (c := a 0) (by decide) (by decide) (by decide) (by decide)
  · exact pick' (c := a 1) (by decide) (by decide) (by decide) (by decide)
  · exact pick' (c := a 2) (by decide) (by decide) (by decide) (by decide)
  · exact pick' (c := a 3) (by decide) (by decide) (by decide) (by decide)

lemma phase1_final : Algorithm1.Final G 2 ⟨Cs 4, Rs 4⟩ := by
  intro c hc
  rw [gnbrs_eq]
  revert c
  decide

/-- The cover `{aᵢ}` of `G²[U]`. -/
def OA : Finset V := univ.filter fun v => ∃ i, v = a i

lemma U_card : U.card = 8 := by decide
lemma OA_card : OA.card = 4 := by decide

lemma triangleFree_U : Centralized.TriangleFree G U := by
  unfold Centralized.TriangleFree
  set_option synthInstance.maxHeartbeats 400000 in
  set_option synthInstance.maxSize 2000 in decide

lemma deg_U : ∀ u ∈ U, 4 ≤ Centralized.deg G U u := by
  simp only [Centralized.deg, nbrs_eq]; decide

lemma covers_OA : Centralized.CoversIn G U OA := by
  unfold Centralized.CoversIn; decide

/-- Taking all of `U` is a valid 2-approximate cover of `G²[U] = K₄,₄` (part 3 of Algorithm 2):
any cover contains an endpoint of each of the 4 disjoint edges `aᵢbᵢ`. -/
lemma twoApprox_U : Centralized.IsTwoApprox G U U := by
  refine ⟨subset_rfl, fun u hu _ _ _ => Or.inl hu, fun D hD hcov => ?_⟩
  have hab : ∀ i, (G.power 2).Adj (a i) (b i) := by decide
  have haU : ∀ i, a i ∈ U := by decide
  have hbU : ∀ i, b i ∈ U := by decide
  have h4 : (univ : Finset (Fin 4)).card ≤ D.card := by
    classical
    refine card_le_card_of_injOn (fun i => if a i ∈ D then a i else b i) ?_ ?_
    · intro i _
      simp only
      split_ifs with h
      · exact h
      · exact (hcov _ (haU i) _ (hbU i) (hab i)).resolve_left h
    · intro i _ j _ hij
      simp only at hij
      split_ifs at hij <;> simp_all [a, b]
  rw [U_card]
  simp only [card_univ, Fintype.card_fin] at h4
  omega

/-- **The argument of Corollary 17 fails.** Phase I of Algorithm 1 (`ε = 1/2`) ends with `U`,
and a complete run of Algorithm 2 (Theorem 12) on the remaining graph `G²[U]` outputs a cover
of size `8`, while `G²[U]` has a cover of size `4`: Algorithm 2 is not a `5/3`-approximation on
the remaining graph, contrary to the proof of Corollary 17. -/
theorem corollary_17_proof_gap :
    ∃ (s : Algorithm1.State V) (t : Centralized.State V),
      ReflTransGen (Algorithm1.Step G 2) Algorithm1.init s ∧ Algorithm1.Final G 2 s ∧
      ReflTransGen (Centralized.Step G) (Centralized.init s.R) t ∧ t.phase = .done ∧
      ∃ O : Finset V, O ⊆ s.R ∧ Centralized.CoversIn G s.R O ∧ O.card = 4 ∧
        t.cover.card = 8 ∧ 5 * O.card < 3 * t.cover.card := by
  refine ⟨⟨Cs 4, Rs 4⟩, ⟨.done, ∅, ∅, ∅, U⟩, phase1, phase1_final, ?_, rfl, OA, ?_, ?_,
    OA_card, ?_, ?_⟩
  · show ReflTransGen _ (Centralized.init (Rs 4)) _
    rw [Rs_four]
    exact .tail (.tail (.single (.endOne rfl triangleFree_U)) (.endTwo rfl deg_U))
      (.final rfl twoApprox_U)
  · show OA ⊆ Rs 4
    rw [Rs_four]; decide
  · show Centralized.CoversIn G (Rs 4) OA
    rw [Rs_four]; exact covers_OA
  · simp [Centralized.State.cover, U_card]
  · simp [Centralized.State.cover, U_card, OA_card]

end Podc.PowerGraphApproximation.Cor17Gap
