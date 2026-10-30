import Papers.PODC2020.BinaryLabelingClassification.Basic

/-!
# Relabelling invariance and distance lower bounds

* `edist_comap_equiv`: distances are invariant under relabelling the vertices along an
  equivalence.
* `WhiteSolvable.of_equiv`: solvability in `T` rounds only depends on the number of nodes: an
  algorithm on `V` can be run on any `S ≃ V` (the identifiers are renamed).
* `natAbs_le_edist`: a `1`-Lipschitz potential gives lower bounds on distances.
-/

namespace Podc.BinaryLabeling

open SimpleGraph Cslib.Local

variable {V S : Type*}

/-- A graph homomorphism does not increase distances. -/ -- CSLib candidate
lemma edist_map_hom_le {G : SimpleGraph S} {H : SimpleGraph V} (φ : G →g H) (u v : S) :
    H.edist (φ u) (φ v) ≤ G.edist u v := by
  by_cases h : G.Reachable u v
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_edist
    rw [← hp]
    calc H.edist (φ u) (φ v) ≤ (p.map φ).length := edist_le _
      _ = p.length := by rw [Walk.length_map]
  · rw [edist_eq_top_of_not_reachable h]; exact le_top

/-- Distances are invariant under relabelling along an equivalence. -/ -- CSLib candidate
lemma edist_comap_equiv (e : S ≃ V) (G : SimpleGraph S) (u v : S) :
    (G.comap e.symm).edist (e u) (e v) = G.edist u v := by
  apply le_antisymm
  · exact edist_map_hom_le (⟨e, fun {a b} h => by simpa using h⟩ : G →g G.comap e.symm) u v
  · have := edist_map_hom_le (⟨e.symm, fun {a b} h => h⟩ : G.comap e.symm →g G) (e u) (e v)
    convert this using 2
    · exact (e.symm_apply_apply u).symm
    · exact (e.symm_apply_apply v).symm

/-- Relabelling preserves degrees. -/
lemma deg_comap_equiv (e : S ≃ V) (G : SimpleGraph S) (u : S) :
    deg (G.comap e.symm) (e u) = deg G u := by
  unfold deg
  have : (G.comap e.symm).neighborSet (e u) = e '' G.neighborSet u := by
    ext w
    simp only [mem_neighborSet, comap_adj, Equiv.symm_apply_apply, Set.mem_image]
    constructor
    · intro h; exact ⟨e.symm w, h, by simp⟩
    · rintro ⟨z, hz, rfl⟩; simpa using hz
  rw [this, Set.ncard_image_of_injective _ e.injective]

/-- Relabelling preserves `X`-degrees. -/
lemma degX_comap_equiv (e : S ≃ V) (G : SimpleGraph S) (x : V → V → Bool) (u : S) :
    degX (G.comap e.symm) x (e u) = degX G (fun a b => x (e a) (e b)) u := by
  unfold degX
  have : {w | (G.comap e.symm).Adj (e u) w ∧ x (e u) w = true} =
      e '' {w | G.Adj u w ∧ x (e u) (e w) = true} := by
    ext w
    simp only [comap_adj, Equiv.symm_apply_apply, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h; exact ⟨e.symm w, by simpa using h, by simp⟩
    · rintro ⟨z, hz, rfl⟩; simpa using hz
  rw [this, Set.ncard_image_of_injective _ e.injective]

/-- Relabelling preserves solutions. -/
lemma isSolution_comap_equiv (e : S ≃ V) {P : Problem} {G : SimpleGraph S} {f : S → Bool}
    {x : V → V → Bool} (h : IsSolution P (G.comap e.symm) (f ∘ e.symm) x) :
    IsSolution P G f (fun a b => x (e a) (e b)) := by
  obtain ⟨hs, hw, hb⟩ := h
  refine ⟨fun v w hvw => hs (by simpa using hvw), fun v hv hd => ?_, fun v hv hd => ?_⟩
  · have := hw (e v) (by simpa using hv) (by rw [deg_comap_equiv]; exact hd)
    rwa [degX_comap_equiv] at this
  · have := hb (e v) (by simpa using hv) (by rw [deg_comap_equiv]; exact hd)
    rwa [degX_comap_equiv] at this

/-- Relabelling preserves instances. -/
lemma IsInstance.comap_equiv (e : S ≃ V) {G : SimpleGraph S} {f : S → Bool}
    (h : IsInstance G f) : IsInstance (G.comap e.symm) (f ∘ e.symm) :=
  ⟨(Iso.isTree_iff (Iso.comap e.symm G)).2 h.1, fun u v huv => h.2 huv⟩

/-- Relabelling preserves views. -/
lemma ViewEq.comap_equiv (e : S ≃ V) {R : ℕ} {G G' : SimpleGraph S} {f f' : S → Bool} {u : S}
    (h : ViewEq R G f G' f' u) :
    ViewEq R (G.comap e.symm) (f ∘ e.symm) (G'.comap e.symm) (f' ∘ e.symm) (e u) := by
  refine ⟨fun x hx y => ?_, fun x hx => ?_⟩
  · rw [show x = e (e.symm x) by simp, edist_comap_equiv] at hx
    simp only [comap_adj]
    exact h.1 hx _
  · rw [show x = e (e.symm x) by simp, edist_comap_equiv] at hx
    exact h.2 _ hx

/-- Running an algorithm on relabelled instances: if `Π` is solvable in `T` rounds on `V`, it is
solvable in `T` rounds on every `S ≃ V`. -/
theorem WhiteSolvable.of_equiv {P : Problem} {T : ℕ} (e : S ≃ V) (h : WhiteSolvable P V T) :
    WhiteSolvable P S T := by
  obtain ⟨A, hA, hs⟩ := h
  refine ⟨fun G f u w => A (G.comap e.symm) (f ∘ e.symm) (e u) (e w), ?_, fun G f hGf => ?_⟩
  · intro G f G' f' u hv
    funext w
    simp only
    rw [hA _ _ _ _ _ (ViewEq.comap_equiv e hv)]
  · have := isSolution_comap_equiv e (hs _ _ (hGf.comap_equiv e))
    convert this using 2
    funext b
    simp [whiteOut]

/-- A `1`-Lipschitz potential gives a lower bound on distances. -/ -- CSLib candidate
lemma natAbs_le_edist {G : SimpleGraph V} (φ : V → ℤ)
    (hφ : ∀ ⦃y z⦄, G.Adj y z → |φ y - φ z| ≤ 1) (u v : V) :
    ((φ u - φ v).natAbs : ℕ∞) ≤ G.edist u v := by
  have key : ∀ {a b : V} (p : G.Walk a b), (φ a - φ b).natAbs ≤ p.length := by
    intro a b p
    induction p with
    | nil => simp
    | cons h p ih =>
      rename_i x y z
      have h1 := hφ h
      rw [Walk.length_cons]
      have : |φ x - φ z| ≤ |φ x - φ y| + |φ y - φ z| := abs_sub_le _ _ _
      have h2 : ((φ x - φ z).natAbs : ℤ) ≤ (p.length : ℤ) + 1 := by
        rw [Int.natCast_natAbs]
        have : |φ y - φ z| ≤ (p.length : ℤ) := by
          rw [← Int.natCast_natAbs]; exact_mod_cast ih
        linarith
      omega
  by_cases h : G.Reachable u v
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_edist
    rw [← hp]; exact_mod_cast key p
  · rw [edist_eq_top_of_not_reachable h]; exact le_top

end Podc.BinaryLabeling
