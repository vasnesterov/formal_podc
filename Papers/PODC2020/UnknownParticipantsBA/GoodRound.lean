import Papers.PODC2020.UnknownParticipantsBA.Rotor

/-!
# A good round within the first `f + 1` iterations (repaired Lemma 4)

Abstract combinatorial core: correct nodes `v ∈ G` hold candidate sets `C v r` (`r` = iteration)
such that

* all correct identifiers are candidates (`G ⊆ C v r`),
* only existing nodes are candidates (`C v r ⊆ G ∪ F`),
* candidates are relayed within one iteration (`C v r ⊆ C u (r + 1)`; this also gives
  monotonicity).

If `|F| < |G|`, then some iteration `r ≤ |F|` is good: all correct nodes select the same correct
node `C[r mod |C|]`. In fact it is always the smallest correct identifier `c₁`.

Proof: if iterations `0, …, r` are all bad, then at least `r + 1` identifiers smaller than `c₁`
are candidates of somebody at iteration `r` (induction: if there were only `r + 1 ≤ ` of them at
iteration `r + 1`, they would be exactly the `≥ r + 1` relayed ones, hence held by everybody, and
everybody would select `c₁`, the element of rank `r + 1`). Such identifiers are faulty, so
`r + 1 ≤ |F|`.
-/

namespace UnknownBA

variable {I : Type*} [DecidableEq I] [LinearOrder I]

/-- `selSet C k = {c}` if exactly `k < |C|` elements of `C` are smaller than `c ∈ C`. -/
lemma selSet_eq_singleton {C : Finset I} {c : I} (hc : c ∈ C) {k : ℕ}
    (hk : (C.filter (· < c)).card = k) (hkC : k < C.card) : selSet C k = {c} := by
  ext x
  simp only [selSet, Finset.mem_filter, Finset.mem_singleton, Nat.mod_eq_of_lt hkC]
  constructor
  · rintro ⟨hx, hxk⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (C.filter (· < x)) ⊂ (C.filter (· < c)) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨fun y hy => ?_, fun h => ?_⟩
        · simp only [Finset.mem_filter] at hy ⊢; exact ⟨hy.1, hy.2.trans hlt⟩
        · have : x ∈ C.filter (· < c) := by simp [hx, hlt]
          rw [← h] at this; simp at this
      have := Finset.card_lt_card this; omega
    · have : (C.filter (· < c)) ⊂ (C.filter (· < x)) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨fun y hy => ?_, fun h => ?_⟩
        · simp only [Finset.mem_filter] at hy ⊢; exact ⟨hy.1, hy.2.trans hlt⟩
        · have : c ∈ C.filter (· < x) := by simp [hc, hlt]
          rw [← h] at this; simp at this
      have := Finset.card_lt_card this; omega
  · rintro rfl; exact ⟨hc, hk⟩

/-- `selSet C r` is a singleton for nonempty `C`. -/
lemma selSet_singleton {C : Finset I} (hC : C.Nonempty) (r : ℕ) : ∃ x ∈ C, selSet C r = {x} := by
  have hpos : 0 < C.card := Finset.card_pos.mpr hC
  set k := r % C.card with hk
  have hkC : k < C.card := Nat.mod_lt _ hpos
  -- the rank map is injective from `C` to `range |C|`, hence surjective
  have hinj : Set.InjOn (fun x => (C.filter (· < x)).card) C := by
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (C.filter (· < x)) ⊂ (C.filter (· < y)) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨fun z hz => ?_, fun h => ?_⟩
        · simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans hlt⟩
        · have : x ∈ C.filter (· < y) := by simp [Finset.mem_coe.mp hx, hlt]
          rw [← h] at this; simp at this
      have := Finset.card_lt_card this; simp only at hxy; omega
    · have : (C.filter (· < y)) ⊂ (C.filter (· < x)) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨fun z hz => ?_, fun h => ?_⟩
        · simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans hlt⟩
        · have : y ∈ C.filter (· < x) := by simp [Finset.mem_coe.mp hy, hlt]
          rw [← h] at this; simp at this
      have := Finset.card_lt_card this; simp only at hxy; omega
  have hmaps : ∀ x ∈ C, (C.filter (· < x)).card ∈ Finset.range C.card := by
    intro x hx
    rw [Finset.mem_range]
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,
      fun h => ?_⟩)
    have : x ∈ C.filter (· < x) := by rw [h]; exact hx
    simp at this
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := C) (t := Finset.range C.card)
    (fun x hx => (C.filter (· < x)).card) (fun x hx => hmaps x hx)
    (fun x y hx hy h => hinj hx hy h) (by simp)
  obtain ⟨x, hx, hxk⟩ := hsurj k (Finset.mem_range.mpr hkC)
  refine ⟨x, hx, ?_⟩
  have : selSet C r = selSet C k := by
    simp only [selSet, ← hk, Nat.mod_eq_of_lt hkC]
  rw [this]
  exact selSet_eq_singleton hx hxk.symm hkC

/-- **Repaired Lemma 4** (abstract form). -/
theorem exists_good_round (G F : Finset I) (hGF : F.card < G.card) (C : I → ℕ → Finset I)
    (hG : ∀ v ∈ G, ∀ r ≤ F.card, G ⊆ C v r)
    (hF : ∀ v ∈ G, ∀ r ≤ F.card, C v r ⊆ G ∪ F)
    (hrel : ∀ v ∈ G, ∀ u ∈ G, ∀ r < F.card, C v r ⊆ C u (r + 1)) :
    ∃ r ≤ F.card, ∃ p ∈ G, ∀ v ∈ G, selSet (C v r) r = {p} := by
  have hGne : G.Nonempty := Finset.card_pos.mp (by omega)
  set c := G.min' hGne with hc_def
  have hcG : c ∈ G := G.min'_mem hGne
  let U : ℕ → Finset I := fun r => G.biUnion fun v => C v r
  let low : Finset I → Finset I := fun D => D.filter (· < c)
  -- a round in which every correct node has exactly `r` candidates below `c` is good
  have good_of : ∀ r ≤ F.card, (∀ v ∈ G, (low (C v r)).card = r) →
      ∀ v ∈ G, selSet (C v r) r = {c} := by
    intro r hr h v hv
    refine selSet_eq_singleton (hG v hv r hr hcG) (h v hv) ?_
    have := Finset.card_le_card (hG v hv r hr); omega
  -- identifiers below `c` are faulty
  have low_U : ∀ r ≤ F.card, low (U r) ⊆ F := by
    intro r hr x hx
    simp only [low, U, Finset.mem_filter, Finset.mem_biUnion] at hx
    obtain ⟨⟨v, hv, hxv⟩, hxc⟩ := hx
    rcases Finset.mem_union.mp (hF v hv r hr hxv) with h | h
    · exact absurd (G.min'_le x h) (by rw [← hc_def]; exact not_le.mpr hxc)
    · exact h
  have low_mono : ∀ r v, v ∈ G → low (C v r) ⊆ low (U r) := by
    intro r v hv x hx
    simp only [low, U, Finset.mem_filter, Finset.mem_biUnion] at hx ⊢
    exact ⟨⟨v, hv, hx.1⟩, hx.2⟩
  by_contra hcon
  push Not at hcon
  have bad : ∀ r ≤ F.card, ¬ ∀ v ∈ G, selSet (C v r) r = {c} := by
    intro r hr h
    obtain ⟨v, hv, hne⟩ := hcon r hr c hcG
    exact hne (h v hv)
  have claim : ∀ r ≤ F.card, r + 1 ≤ (low (U r)).card := by
    intro r
    induction r with
    | zero =>
      intro hr
      by_contra hlt
      push Not at hlt
      apply bad 0 hr (good_of 0 hr fun v hv => ?_)
      have := Finset.card_le_card (low_mono 0 v hv); omega
    | succ r ih =>
      intro hr
      have ih := ih (by omega)
      by_contra hlt
      push Not at hlt
      apply bad (r + 1) hr (good_of (r + 1) hr fun v hv => ?_)
      have h1 : low (U r) ⊆ low (C v (r + 1)) := by
        intro x hx
        simp only [low, U, Finset.mem_filter, Finset.mem_biUnion] at hx ⊢
        obtain ⟨⟨u, hu, hxu⟩, hxc⟩ := hx
        exact ⟨hrel u hu v hv r (by omega) hxu, hxc⟩
      have := Finset.card_le_card h1
      have := Finset.card_le_card (low_mono (r + 1) v hv)
      omega
  have h1 := claim F.card le_rfl
  have h2 := Finset.card_le_card (low_U F.card le_rfl)
  omega

end UnknownBA
