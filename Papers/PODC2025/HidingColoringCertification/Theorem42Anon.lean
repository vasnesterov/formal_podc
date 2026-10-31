import Papers.PODC2025.HidingColoringCertification.MinDegreeOne
import Papers.PODC2025.HidingColoringCertification.Theorem42

/-!
# Theorem 4.2 also fails for anonymous constant-size LCPs; Theorem 1 of arXiv v3 is false

* `baTheorem42Anon_false`: the BA's Theorem 4.2 restricted to anonymous LCPs (hiding against
  anonymous extraction algorithms) already fails with the constant-size LCP of Lemma 4.1 on
  `H` = all bipartite graphs. The proof of the BA (arXiv v1, Section 5.2) assumes "without
  restriction" that `H` consists only of the forgetful graphs, because "a strong and hiding LCP
  for `H` is one for every subclass" — false, since hiding only requires *one* hard instance in
  the class (the authors acknowledge this in v3, Section 2.2.4, and add `G ∩ H = ∅`).
* `v3Theorem1_false`: Theorem 1 of arXiv v3 ("for any class `G` of bipartite graphs that has
  non-empty intersection with `H`, there is a strong and hiding anonymous LCP for `2-col_G`")
  fails for `G = {P₃}`: an anonymous algorithm colours by degree.
-/

namespace Podc.HidingColoringCertification

open SimpleGraph

/-- The BA's Theorem 4.2 (`r = 1`) for anonymous LCPs. -/
def BATheorem42Anon (bound : ℕ → ℕ) : Prop :=
  ∀ (L : Type) (H : GraphClass), (∀ V G, H V G → G.Colorable 2) →
    (∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        H V G ∧ IsForgetful G 1 ∧ G.Connected ∧ ¬ IsCycleLike G ∧ G.minDegree ≠ 1) →
    ∀ S : LCP L, S.Anonymous → ¬ (S.Complete bound H ∧ S.Sound bound 2 ∧
      S.StronglySound bound 2 ∧ S.AnonHiding bound H 2)

variable {bound : ℕ → ℕ}

/-- **Theorem 4.2 fails for anonymous, constant-size LCPs** (`H` = all bipartite graphs, the LCP
of Lemma 4.1). -/
theorem baTheorem42Anon_false (hb : 8 ≤ bound 8) : ¬ BATheorem42Anon bound := by
  intro h
  exact h L1 Bipartite (fun _ _ hG => hG)
    ⟨Fin 14, inferInstance, thetaG, inferInstance, thetaG_colorable, thetaG_isForgetful,
      thetaG_connected, thetaG_not_cycleLike, thetaG_minDegree⟩ degOneLCP degOneLCP_anonymous
    ⟨degOneLCP_complete, degOneLCP_stronglySoundAll.stronglySound.sound,
      degOneLCP_stronglySoundAll.stronglySound, degOneLCP_anonHiding hb _ p6k2_colorable⟩

/-- The path `0–1–2`. -/
def path3 : SimpleGraph (Fin 3) := edgeGraph 3 [(0,1),(1,2)]

instance : DecidableRel path3.Adj := inferInstanceAs (DecidableRel (edgeGraph _ _).Adj)

/-- The class consisting of `P₃` only (bipartite, minimum degree 1). -/
def path3Class : GraphClass := fun _ G => Nonempty (G ≃g path3)

lemma path3_minDegree : path3.minDegree = 1 := by
  apply le_antisymm
  · have : path3.degree 0 = 1 := by decide
    exact this ▸ path3.minDegree_le_degree 0
  · apply le_minDegree_of_forall_le_degree
    have : ∀ v : Fin 3, 1 ≤ path3.degree v := by decide
    exact this

/-- **Theorem 1 of arXiv v3 is false**: no LCP whatsoever is hiding (even against anonymous
algorithms) on the class `{P₃}`, although `P₃` is bipartite with minimum degree 1. -/
theorem v3Theorem1_false {L : Type} (S : LCP L) : ¬ S.AnonHiding bound path3Class 2 := by
  intro h
  obtain ⟨P, -, ⟨e⟩, ℓ, -, -, u, v, huv, heq⟩ := h (fun μ => if μ.deg = 1 then 0 else 1)
  have hd : ∀ a b : Fin 3, path3.Adj a b → (path3.degree a = 1 ↔ ¬ path3.degree b = 1) := by
    decide
  have := hd (e u) (e v) (e.map_adj_iff.2 huv)
  rw [e.degree_eq, e.degree_eq] at this
  simp only [Function.comp, View.anon, PortGraph.view] at heq
  split_ifs at heq <;> simp_all

end Podc.HidingColoringCertification
