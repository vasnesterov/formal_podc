import Mathlib

/-!
# A pairing lemma for bipartite compatibility graphs (used in Lemma 2)

`exists_pairing_cover` is the combinatorial core of the proof of Lemma 2 of Brandt (PODC 2019):
in a bipartite graph (sides given by `α`), if Hall's condition holds for every subset of `I` lying
on one side, then some matching covers all of `I` (a Mendelsohn–Dulmage-type statement). The
matching is given as an involution `σ` of `D` whose non-fixed points are matched along `R`.
-/

-- CSLib candidate (`exists_pairing_cover`, `exists_injOn_of_hall`)
namespace AutomaticSpeedup

open Classical in
/-- Hall's theorem for finsets of naturals: if every `J ⊆ S` has at least `|J|` neighbours in `D`,
there is an injective choice of a neighbour in `D` for every element of `S`. -/
theorem exists_injOn_of_hall (S D : Finset ℕ) (R : ℕ → ℕ → Prop)
    (hall : ∀ J ⊆ S, J.card ≤ (D.filter fun i => ∃ j ∈ J, R i j).card) :
    ∃ f : ℕ → ℕ, Set.InjOn f S ∧ ∀ x ∈ S, f x ∈ D ∧ R (f x) x := by
  classical
  have key := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun x : S => D.filter fun i => R i x)).1 ?_
  · obtain ⟨f, hinj, hf⟩ := key
    refine ⟨fun n => if hn : n ∈ S then (f ⟨n, hn⟩ : ℕ) else 0, ?_, ?_⟩
    · intro a ha b hb e
      simp only [Finset.mem_coe] at ha hb
      simp only [ha, hb, ↓reduceDIte] at e
      exact congrArg Subtype.val (hinj e)
    · intro x hx
      simpa [hx] using hf ⟨x, hx⟩
  · intro s
    calc s.card = (s.map (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
      _ ≤ _ := hall _ (by
          intro x hx
          simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
          obtain ⟨y, _, rfl⟩ := hx
          exact y.2)
      _ ≤ _ := Finset.card_le_card (by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_map, Function.Embedding.coe_subtype] at hi
          obtain ⟨hiD, j, ⟨y, hy, rfl⟩, hR⟩ := hi
          exact Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_filter.2 ⟨hiD, hR⟩⟩)

/-- Matching from a partial injection: if `h` is injective on `I` and maps every `v ∈ I` to an
`R`-neighbour `h v ∈ D` (with `R` symmetric and bipartite), then some matching (an involution `σ`
whose moved points are `R`-adjacent to their partner and lie in `D`) covers `I`. -/
theorem exists_pairing_of_injOn (R : ℕ → ℕ → Prop) (hR : ∀ i j, R i j → R j i) (α : ℕ → Bool)
    (hα : ∀ i j, R i j → α i ≠ α j) :
    ∀ (n : ℕ) (D I : Finset ℕ) (h : ℕ → ℕ), I.card = n → I ⊆ D →
      (∀ v ∈ I, h v ∈ D ∧ R v (h v)) → Set.InjOn h I →
      ∃ σ : ℕ → ℕ, (∀ i, σ (σ i) = i) ∧ (∀ i, σ i ≠ i → R i (σ i) ∧ i ∈ D) ∧
        ∀ i ∈ I, σ i ≠ i := by
  classical
  have hirr : ∀ i, ¬ R i i := fun i hi => hα i i hi rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D I h hcard hID hh hinj
  by_cases hA : ∃ v0 ∈ I, ∀ w ∈ I, h w ≠ v0
  · obtain ⟨v0, hv0, hpred⟩ := hA
    obtain ⟨hv1D, hRv01⟩ := hh v0 hv0
    set v1 := h v0 with hv1
    have hne : v0 ≠ v1 := fun e => hirr v0 (e ▸ hRv01)
    obtain ⟨σ', h1, h2, h3⟩ := ih ((I.erase v0).erase v1).card
      (lt_of_le_of_lt (Finset.card_erase_le) (hcard ▸ Finset.card_erase_lt_of_mem hv0))
      ((D.erase v0).erase v1) ((I.erase v0).erase v1) h rfl
      (fun x hx => by
        simp only [Finset.mem_erase] at hx ⊢
        exact ⟨hx.1, hx.2.1, hID hx.2.2⟩)
      (fun w hw => by
        simp only [Finset.mem_erase] at hw ⊢
        refine ⟨⟨fun e => hinj (Finset.mem_coe.2 hw.2.2) (Finset.mem_coe.2 hv0) e |> hw.2.1,
          hpred w hw.2.2, (hh w hw.2.2).1⟩, (hh w hw.2.2).2⟩)
      (hinj.mono (fun x hx => by
        simp only [Finset.coe_erase, Set.mem_sdiff] at hx
        exact hx.1.1))
    have hf0 : σ' v0 = v0 := by
      by_contra hc
      have := (h2 v0 hc).2
      simp at this
    have hf1 : σ' v1 = v1 := by
      by_contra hc
      have := (h2 v1 hc).2
      simp at this
    have hn0 : ∀ v, σ' v = v0 → v = v0 := fun v e => by rw [← h1 v, e, hf0]
    have hn1 : ∀ v, σ' v = v1 → v = v1 := fun v e => by rw [← h1 v, e, hf1]
    refine ⟨fun v => if v = v0 then v1 else if v = v1 then v0 else σ' v, ?_, ?_, ?_⟩
    · intro i
      by_cases e0 : i = v0
      · subst e0; simp [hne.symm]
      by_cases e1 : i = v1
      · subst e1; simp
      have a0 : σ' i ≠ v0 := fun e => e0 (hn0 i e)
      have a1 : σ' i ≠ v1 := fun e => e1 (hn1 i e)
      simp [e0, e1, a0, a1, h1]
    · intro i hi
      by_cases e0 : i = v0
      · subst e0; simp only [↓reduceIte]; exact ⟨hRv01, hID hv0⟩
      by_cases e1 : i = v1
      · subst e1; simp only [hne.symm, ↓reduceIte]; exact ⟨hR _ _ hRv01, hv1D⟩
      simp only [e0, e1, ↓reduceIte] at hi ⊢
      obtain ⟨hr, hd⟩ := h2 i hi
      exact ⟨hr, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)⟩
    · intro i hi
      by_cases e0 : i = v0
      · subst e0; simpa using hne.symm
      by_cases e1 : i = v1
      · subst e1; simpa using ⟨hne.symm, hne⟩
      simp only [e0, e1, ↓reduceIte]
      exact h3 i (by simp [e0, e1, hi])
  · simp only [not_exists, not_and, not_forall, not_not] at hA
    have hsub : I ⊆ I.image h := fun v hv => by
      obtain ⟨w, hw, e⟩ := hA v hv
      exact Finset.mem_image.2 ⟨w, hw, e⟩
    have himg : I = I.image h := Finset.eq_of_subset_of_card_le hsub Finset.card_image_le
    have hmap : ∀ v ∈ I, h v ∈ I := fun v hv => himg ▸ Finset.mem_image_of_mem h hv
    set g := Function.invFunOn h (I : Set ℕ) with hg
    have hgI : ∀ v ∈ I, g v ∈ I ∧ h (g v) = v := fun v hv => by
      obtain ⟨w, hw, e⟩ := hA v hv
      exact ⟨Function.invFunOn_mem ⟨w, hw, e⟩, Function.invFunOn_eq ⟨w, hw, e⟩⟩
    have hgh : ∀ v ∈ I, g (h v) = v := fun v hv => hinj.leftInvOn_invFunOn hv
    -- sides
    have hside_h : ∀ v ∈ I, α (h v) = !α v := fun v hv => by
      have := hα _ _ (hh v hv).2
      revert this; cases α v <;> cases α (h v) <;> simp
    have hside_g : ∀ v ∈ I, α (g v) = !α v := fun v hv => by
      have := hα _ _ (hh (g v) (hgI v hv).1).2
      rw [(hgI v hv).2] at this
      revert this; cases α v <;> cases α (g v) <;> simp
    refine ⟨fun v => if v ∈ I then (if α v then h v else g v) else v, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i ∈ I
      · by_cases ha : α i = true
        · simp [hi, ha, hmap i hi, hside_h i hi, hgh i hi]
        · simp only [Bool.not_eq_true] at ha
          have := hside_g i hi
          simp [hi, ha, (hgI i hi).1, this, (hgI i hi).2]
      · simp [hi]
    · intro i hi
      by_cases hiI : i ∈ I
      · refine ⟨?_, hID hiI⟩
        by_cases ha : α i = true
        · simp only [hiI, ha, ↓reduceIte]; exact (hh i hiI).2
        · simp only [hiI, ha, ↓reduceIte, Bool.false_eq_true]
          have := (hh (g i) (hgI i hiI).1).2
          rw [(hgI i hiI).2] at this
          exact hR _ _ this
      · simp [hiI] at hi
    · intro i hi
      by_cases ha : α i = true
      · simp only [hi, ha, ↓reduceIte]
        intro e
        have := (hh i hi).2
        rw [e] at this
        exact hirr i this
      · simp only [hi, ha, ↓reduceIte, Bool.false_eq_true]
        intro e
        have := (hh (g i) (hgI i hi).1).2
        rw [(hgI i hi).2, e] at this
        exact hirr i this


open Classical in
/-- Pairing lemma: if Hall's condition holds for all one-sided subsets of `I`, there is a matching
(an involution `σ` on `D`, pairs `{i, σ i}` adjacent in `R`) covering `I`. -/
theorem exists_pairing_cover {D I : Finset ℕ} (hI : I ⊆ D) (R : ℕ → ℕ → Prop)
    (hR : ∀ i j, R i j → R j i) (α : ℕ → Bool) (hα : ∀ i j, R i j → α i ≠ α j)
    (hall : ∀ J ⊆ I, (∀ i ∈ J, ∀ j ∈ J, α i = α j) →
      J.card ≤ (D.filter fun i => ∃ j ∈ J, R i j).card) :
    ∃ σ : ℕ → ℕ, (∀ i ∈ D, σ i ∈ D ∧ σ (σ i) = i ∧ (σ i ≠ i → R i (σ i))) ∧
      ∀ i ∈ I, σ i ≠ i := by
  have side : ∀ b : Bool, ∀ J ⊆ I.filter (fun i => α i = b),
      J.card ≤ (D.filter fun i => ∃ j ∈ J, R i j).card := fun b J hJ =>
    hall J (hJ.trans (Finset.filter_subset _ _)) (fun i hi j hj => by
      rw [(Finset.mem_filter.1 (hJ hi)).2, (Finset.mem_filter.1 (hJ hj)).2])
  obtain ⟨f, hfi, hf⟩ := exists_injOn_of_hall _ D R (side true)
  obtain ⟨g, hgi, hg⟩ := exists_injOn_of_hall _ D R (side false)
  have hflip : ∀ v w, R v w → α w = !α v := fun v w hr => by
    have := hα v w hr
    revert this; cases α v <;> cases α w <;> simp
  let h : ℕ → ℕ := fun v => if α v then f v else g v
  have hh : ∀ v ∈ I, h v ∈ D ∧ R v (h v) := fun v hv => by
    by_cases ha : α v = true
    · obtain ⟨h1, h2⟩ := hf v (Finset.mem_filter.2 ⟨hv, ha⟩)
      simp only [h, ha, ↓reduceIte]; exact ⟨h1, hR _ _ h2⟩
    · simp only [Bool.not_eq_true] at ha
      obtain ⟨h1, h2⟩ := hg v (Finset.mem_filter.2 ⟨hv, ha⟩)
      simp only [h, ha, ↓reduceIte, Bool.false_eq_true]; exact ⟨h1, hR _ _ h2⟩
  have hinj : Set.InjOn h I := by
    intro v hv w hw e
    simp only [Finset.mem_coe] at hv hw
    have hav := hflip _ _ (hh v hv).2
    have haw := hflip _ _ (hh w hw).2
    have hvw : α v = α w := by
      rw [e] at hav
      rw [hav] at haw
      revert haw; cases α v <;> cases α w <;> simp
    by_cases ha : α v = true
    · have ha' : α w = true := hvw ▸ ha
      simp only [h, ha, ha', ↓reduceIte] at e
      exact hfi (Finset.mem_filter.2 ⟨hv, ha⟩) (Finset.mem_filter.2 ⟨hw, ha'⟩) e
    · simp only [Bool.not_eq_true] at ha
      have ha' : α w = false := hvw ▸ ha
      simp only [h, ha, ha', ↓reduceIte, Bool.false_eq_true] at e
      exact hgi (Finset.mem_filter.2 ⟨hv, ha⟩) (Finset.mem_filter.2 ⟨hw, ha'⟩) e
  obtain ⟨σ, h1, h2, h3⟩ := exists_pairing_of_injOn R hR α hα _ D I h rfl hI hh hinj
  refine ⟨σ, fun i hi => ⟨?_, h1 i, fun hne => (h2 i hne).1⟩, h3⟩
  by_cases e : σ i = i
  · rw [e]; exact hi
  · exact (h2 (σ i) (by rw [h1]; exact Ne.symm e)).2

end AutomaticSpeedup
