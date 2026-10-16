import Papers.PODC2019.AutomaticSpeedup.Lemma1
import Papers.PODC2019.AutomaticSpeedup.Matching

/-!
# Lemma 2 of Brandt (PODC 2019, §5.1): auxiliary material

* `tritOne_g_iff`: the edge condition of `Π'_1` in terms of trit sequences;
* `pick`: a canonical pair of trit sequences summing to `22…2`;
* `countAt_pairs`, `countAt_replicate_ones`: in a choice built from complementary pairs and
  copies of `11…1`, every position has as many `0`s as `2`s.
-/

namespace AutomaticSpeedup

open Problem

variable {k : ℕ}

theorem tritOne_g_iff {Δ : ℕ} {Y Z : Set (Trit k)} :
    ({Y, Z} : Multiset _) ∈ (tritOne k).g Δ ↔
      ∃ y ∈ Y, ∃ z ∈ Z, ∀ j, (y j).val + (z j).val = 2 := by
  rw [tritOne, nodeStepMax_g_iff]
  constructor
  · rintro ⟨-, -, y, hy, z, hz, a, b, he, hab⟩
    rcases pair_eq_pair_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨y, hy, z, hz, hab⟩
    · exact ⟨y, hy, z, hz, fun j => by rw [add_comm]; exact hab j⟩
  · rintro ⟨y, hy, z, hz, h⟩
    exact ⟨fun _ _ => trivial, fun _ _ => trivial, y, hy, z, hz, y, z, rfl, h⟩

theorem tritOne_g_comm {Δ : ℕ} {Y Z : Set (Trit k)} :
    ({Y, Z} : Multiset _) ∈ (tritOne k).g Δ ↔ ({Z, Y} : Multiset _) ∈ (tritOne k).g Δ := by
  rw [Multiset.pair_comm]

/-- A pair `(y, z) ∈ Y × Z` with tritwise sum `22…2`, if there is one. -/
noncomputable def pick (Y Z : Set (Trit k)) : Trit k × Trit k := by
  classical
  exact if h : ∃ p : Trit k × Trit k, p.1 ∈ Y ∧ p.2 ∈ Z ∧ ∀ j, (p.1 j).val + (p.2 j).val = 2
    then h.choose else (ones k, ones k)

theorem pick_spec {Δ : ℕ} {Y Z : Set (Trit k)} (h : ({Y, Z} : Multiset _) ∈ (tritOne k).g Δ) :
    (pick Y Z).1 ∈ Y ∧ (pick Y Z).2 ∈ Z ∧ ∀ j, ((pick Y Z).1 j).val + ((pick Y Z).2 j).val = 2 := by
  obtain ⟨y, hy, z, hz, hyz⟩ := tritOne_g_iff.1 h
  have hex : ∃ p : Trit k × Trit k, p.1 ∈ Y ∧ p.2 ∈ Z ∧ ∀ j, (p.1 j).val + (p.2 j).val = 2 :=
    ⟨(y, z), hy, hz, hyz⟩
  unfold pick
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

theorem countAt_map (s : Multiset ℕ) (w : ℕ → Trit k) (j : Fin k) (y : Fin 3) :
    countAt (s.map w) j y = Multiset.card (s.filter fun i => w i j = y) := by
  simp [countAt, Multiset.filter_map]

theorem countAt_pairs (s : Multiset ℕ) (w x : ℕ → Trit k)
    (h : ∀ i ∈ s, ∀ j, (w i j).val + (x i j).val = 2) (j : Fin k) :
    countAt (s.map w + s.map x) j 0 = countAt (s.map w + s.map x) j 2 := by
  have key : ∀ u v : ℕ → Trit k, (∀ i ∈ s, (u i j).val + (v i j).val = 2) →
      countAt (s.map u) j 0 = countAt (s.map v) j 2 := by
    intro u v huv
    rw [countAt_map, countAt_map]
    congr 1
    apply Multiset.filter_congr
    intro i hi
    have := huv i hi
    rw [Fin.ext_iff, Fin.ext_iff]
    simp only [Fin.isValue, Fin.val_zero, Fin.val_two]
    omega
  rw [countAt_add, countAt_add, key w x (fun i hi => h i hi j),
    key x w (fun i hi => by rw [add_comm]; exact h i hi j), add_comm]

theorem countAt_replicate_ones (n : ℕ) (j : Fin k) {y : Fin 3} (hy : y ≠ 1) :
    countAt (Multiset.replicate n (ones k)) j y = 0 := by
  unfold countAt
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro a ha
  rw [Multiset.eq_of_mem_replicate ha]
  exact fun h => hy h.symm

theorem rel_map_of {α : Type*} {s : Multiset ℕ} {w : ℕ → α} {Q : ℕ → Set α}
    (h : ∀ i ∈ s, w i ∈ Q i) : Multiset.Rel (· ∈ ·) (s.map w) (s.map Q) := by
  rw [Multiset.rel_map]
  exact Multiset.rel_refl_of_refl_on h

open Classical in
/-- Lemma 2 (same statement as `lemma_2` in `Lemmas123.lean`). -/
theorem lemma_2_aux {Δ : ℕ} (hΔ : 2 ^ (4 ^ k + 1) ≤ Δ) {Q : ℕ → Set (Trit k)}
    (hQ : (Multiset.range Δ).map Q ∈ (tritOne k).h Δ) {Pinf : Set (Trit k)}
    (hP : Δ - 2 ^ (4 ^ k) ≤ ((Multiset.range Δ).map Q).count Pinf ∧ ones k ∈ Pinf)
    (α : ℕ → Bool) :
    ∃ J ⊆ (Finset.range Δ).filter
        (fun i => ({Q i, Pinf} : Multiset _) ∉ (tritOne k).g Δ ∧ ones k ∉ Q i),
      ((Finset.range Δ).filter fun i =>
          ∃ j ∈ J, ({Q i, Q j} : Multiset _) ∈ (tritOne k).g Δ ∧ α i ≠ α j).card < J.card ∧
      ∀ j ∈ J, ∀ i ∈ (Finset.range Δ).filter
          (fun i => ∃ j ∈ J, ({Q i, Q j} : Multiset _) ∈ (tritOne k).g Δ ∧ α i ≠ α j),
        α j ≠ α i := by
  set D := Finset.range Δ with hD
  set I := D.filter (fun i => ({Q i, Pinf} : Multiset _) ∉ (tritOne k).g Δ ∧ ones k ∉ Q i)
    with hI
  by_cases hex : ∃ J ⊆ I, (∀ i ∈ J, ∀ j ∈ J, α i = α j) ∧
      (D.filter fun i => ∃ j ∈ J, ({Q i, Q j} : Multiset _) ∈ (tritOne k).g Δ ∧ α i ≠ α j).card
        < J.card
  · obtain ⟨J, hJI, hJα, hJc⟩ := hex
    refine ⟨J, hJI, hJc, fun j hj i hi => ?_⟩
    obtain ⟨j', hj', -, hne⟩ := (Finset.mem_filter.1 hi).2
    rw [hJα j hj j' hj']
    exact hne.symm
  exfalso
  push Not at hex
  obtain ⟨σ, hσ, hσI⟩ := exists_pairing_cover (Finset.filter_subset _ D)
    (fun i j => ({Q i, Q j} : Multiset _) ∈ (tritOne k).g Δ ∧ α i ≠ α j)
    (fun i j h => ⟨tritOne_g_comm.1 h.1, h.2.symm⟩) α (fun i j h => h.2)
    (fun J hJ hα => by convert hex J hJ hα)
  -- the pieces of the partition of the ports
  set inM : ℕ → Prop := fun i => σ i ≠ i ∧ (i ∈ I ∨ σ i ∈ I) with hinM
  set Dm := Multiset.range Δ with hDm
  set M1 := Dm.filter (fun i => inM i ∧ i < σ i) with hM1
  set M2 := Dm.filter (fun i => inM i ∧ σ i < i) with hM2
  set Pm := Dm.filter (fun i => Q i = Pinf) with hPm
  set U := Dm.filter (fun i => ¬ inM i ∧ Q i ≠ Pinf ∧ ones k ∉ Q i) with hU
  set O := Dm.filter (fun i => ¬ inM i ∧ Q i ≠ Pinf ∧ ones k ∈ Q i) with hO
  have hDmD : ∀ i, i ∈ Dm ↔ i ∈ D := fun i => by simp [hDm, hD]
  have hR : ∀ i ∈ D, σ i ≠ i → ({Q i, Q (σ i)} : Multiset _) ∈ (tritOne k).g Δ :=
    fun i hi hne => ((hσ i hi).2.2 hne).1
  have hIm : ∀ i, i ∈ I → ({Q i, Pinf} : Multiset _) ∉ (tritOne k).g Δ ∧ ones k ∉ Q i :=
    fun i hi => (Finset.mem_filter.1 hi).2
  -- ports carrying `P∞` are not matched
  have hPnot : ∀ i ∈ D, Q i = Pinf → ¬ inM i := by
    rintro i hi hQi ⟨hne, hI' | hI'⟩
    · exact (hIm i hI').2 (hQi ▸ hP.2)
    · have h1 := hσ i hi
      have := hR (σ i) h1.1 (by rw [h1.2.1]; exact hne.symm)
      rw [h1.2.1, hQi] at this
      exact (hIm _ hI').1 this
  have hpart : Dm = M1 + M2 + Pm + U + O := by
    ext a
    simp only [Multiset.count_add, Multiset.count_filter, hM1, hM2, hPm, hU, hO]
    by_cases ha : a ∈ Dm
    · rw [Multiset.count_eq_one_of_mem (Multiset.nodup_range Δ) ha]
      have hP' := hPnot a ((hDmD a).1 ha)
      by_cases h1 : inM a
      · have h2 : σ a ≠ a := h1.1
        have h3 : Q a ≠ Pinf := fun h => hP' h h1
        by_cases h4 : a < σ a
        · simp [h1, h3, h4, show ¬ σ a < a by omega]
        · simp [h1, h3, h4, show σ a < a by omega]
      · by_cases h3 : Q a = Pinf
        · simp [h1, h3]
        · by_cases h5 : ones k ∈ Q a <;> simp [h1, h3, h5]
    · rw [Multiset.count_eq_zero_of_notMem ha]
      simp
  have hM2eq : M2 = M1.map σ := by
    have hinj : ∀ x ∈ M1, ∀ y ∈ M1, σ x = σ y → x = y := by
      intro x hx y hy hxy
      have hx' := (hσ x ((hDmD x).1 (Multiset.mem_of_mem_filter hx))).2.1
      have hy' := (hσ y ((hDmD y).1 (Multiset.mem_of_mem_filter hy))).2.1
      rw [← hx', ← hy', hxy]
    rw [Multiset.Nodup.ext (Multiset.Nodup.filter _ (Multiset.nodup_range Δ))
      (Multiset.Nodup.map_on hinj (Multiset.Nodup.filter _ (Multiset.nodup_range Δ)))]
    intro a
    simp only [hM1, Multiset.mem_filter, Multiset.mem_map, hinM]
    constructor
    · rintro ⟨ha, ⟨hne, hI'⟩, hlt⟩
      have h1 := hσ a ((hDmD a).1 ha)
      refine ⟨σ a, ⟨(hDmD _).2 h1.1, ⟨by rw [h1.2.1]; exact hne.symm, ?_⟩, by rw [h1.2.1]; exact hlt⟩,
        h1.2.1⟩
      rw [h1.2.1]; exact hI'.symm
    · rintro ⟨b, ⟨hb, ⟨hne, hI'⟩, hlt⟩, rfl⟩
      have h1 := hσ b ((hDmD b).1 hb)
      refine ⟨(hDmD _).2 h1.1, ⟨by rw [h1.2.1]; exact hne.symm, ?_⟩, by rw [h1.2.1]; exact hlt⟩
      rw [h1.2.1]; exact hI'.symm
  have hM1R : ∀ i ∈ M1, ({Q i, Q (σ i)} : Multiset _) ∈ (tritOne k).g Δ := by
    intro i hi
    rw [Multiset.mem_filter] at hi
    exact hR i ((hDmD i).1 hi.1) hi.2.1.1
  have hUR : ∀ i ∈ U, ({Q i, Pinf} : Multiset _) ∈ (tritOne k).g Δ := by
    intro i hi
    rw [Multiset.mem_filter] at hi
    obtain ⟨hiD, hnM, -, hno⟩ := hi
    by_contra hg
    have hiI : i ∈ I := Finset.mem_filter.2 ⟨(hDmD i).1 hiD, hg, hno⟩
    exact hnM ⟨hσI i hiI, Or.inl hiI⟩
  have hOR : ∀ i ∈ O, ones k ∈ Q i := fun i hi => (Multiset.mem_filter.1 hi).2.2.2
  -- cardinalities
  have hPmQ : Pm.map Q = Multiset.replicate (Multiset.card Pm) Pinf := by
    rw [Multiset.eq_replicate]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 hb
    exact (Multiset.mem_filter.1 hi).2
  have hcPm : Multiset.card Pm = (Dm.map Q).count Pinf := by
    rw [Multiset.count_map, hPm]
    congr 1
    exact Multiset.filter_congr fun _ _ => eq_comm
  have hUle : Multiset.card U ≤ Multiset.card (Dm.filter fun i => ¬ Q i = Pinf) :=
    Multiset.card_le_card (Multiset.monotone_filter_right _ fun i h => h.2.1)
  have hsplit := Multiset.filter_add_not (fun i => Q i = Pinf) Dm
  have hsplitc := congrArg Multiset.card hsplit
  rw [Multiset.card_add] at hsplitc
  have hcDm : Multiset.card Dm = Δ := Multiset.card_range Δ
  have hpow : 2 ^ (4 ^ k + 1) = 2 * 2 ^ (4 ^ k) := by rw [pow_succ]; ring
  have hUP : Multiset.card U ≤ Multiset.card Pm := by
    have : Multiset.card Pm = Multiset.card (Dm.filter fun i => Q i = Pinf) := rfl
    omega
  -- the choice
  set w : ℕ → Trit k := fun i => (pick (Q i) (Q (σ i))).1
  set x : ℕ → Trit k := fun i => (pick (Q i) (Q (σ i))).2
  set w' : ℕ → Trit k := fun i => (pick (Q i) Pinf).1
  set x' : ℕ → Trit k := fun i => (pick (Q i) Pinf).2
  set n := Multiset.card Pm - Multiset.card U
  set c := (M1.map w + M1.map x) + (U.map w' + U.map x') + Multiset.replicate n (ones k) +
    Multiset.replicate (Multiset.card O) (ones k)
  have hrel : Multiset.Rel (· ∈ ·) c ((Multiset.range Δ).map Q) := by
    have hQd : (Multiset.range Δ).map Q = (M1.map Q + M1.map (fun i => Q (σ i))) +
        (U.map Q + U.map (fun _ => Pinf)) + Multiset.replicate n Pinf + O.map Q := by
      rw [← hDm, hpart, hM2eq]
      simp only [Multiset.map_add, Multiset.map_map, Function.comp_def, hPmQ,
        Multiset.map_const']
      have : Multiset.card Pm = Multiset.card U + n := by omega
      rw [this, Multiset.replicate_add]
      abel
    rw [hQd]
    refine ((Multiset.Rel.add (Multiset.Rel.add ?_ ?_) ?_)).add ?_
    · exact Multiset.Rel.add (rel_map_of fun i hi => (pick_spec (hM1R i hi)).1)
        (rel_map_of fun i hi => (pick_spec (hM1R i hi)).2.1)
    · exact Multiset.Rel.add (rel_map_of fun i hi => (pick_spec (hUR i hi)).1)
        (rel_map_of (Q := fun _ => Pinf) fun i hi => (pick_spec (hUR i hi)).2.1)
    · exact rel_replicate_right'.2 ⟨by simp, fun y hy => by
        rw [Multiset.eq_of_mem_replicate hy]; exact hP.2⟩
    · rw [← Multiset.map_const']
      exact rel_map_of hOR
  obtain ⟨j, -, hj⟩ := good_of_nodeAll hQ.1 hrel
  have e : countAt c j 0 = countAt c j 2 := by
    have e1 := countAt_pairs M1 w x (fun i hi => (pick_spec (hM1R i hi)).2.2) j
    have e2 := countAt_pairs U w' x' (fun i hi => (pick_spec (hUR i hi)).2.2) j
    simp only [c, countAt_add] at e1 e2 ⊢
    simp only [countAt_replicate_ones _ j (show (0 : Fin 3) ≠ 1 by decide),
      countAt_replicate_ones _ j (show (2 : Fin 3) ≠ 1 by decide)]
    omega
  omega

end AutomaticSpeedup
