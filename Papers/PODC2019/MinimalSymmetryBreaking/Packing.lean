import Papers.PODC2019.MinimalSymmetryBreaking.Tree

/-!
# Sizes of balls and separated sets in the oriented tree

* `card_Ball_le`: `|B_r| ≤ (2k+1)^r`; `le_card_Ball`: `r + 1 ≤ |B_r|` (for `k ≥ 1`).
* `exists_separated`: inside `B_R` there is a set `S` of nodes whose balls of radius `ρ` are
  pairwise disjoint, with `|B_R| ≤ |S| · |B_{2ρ}|` (a maximal such set).
-/

-- CSLib candidate
namespace Podc.MinimalSymmetryBreaking

open Finset Function
open scoped Classical

noncomputable section

variable {k : ℕ}

lemma mem_ball_iff_norm {v w : Tree k} {r : ℕ} : w ∈ ball v r ↔ (v⁻¹ * w).norm ≤ r := Iff.rfl

/-- Every non-identity element is `dir p * w'` with `w'` one shorter. -/
lemma exists_dir_mul (w : Tree k) (hw : w ≠ 1) :
    ∃ p : Fin k × Bool, ((dir p)⁻¹ * w).norm + 1 = w.norm := by
  have hne : w.toWord ≠ [] := by rwa [Ne, FreeGroup.toWord_eq_nil_iff]
  obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨a, ?_⟩
  rw [dir_inv, norm_dir_mul, if_pos (by simp [hl])]
  have : 1 ≤ w.norm := by unfold FreeGroup.norm; rw [hl]; simp
  omega

lemma Ball_succ_subset (r : ℕ) :
    (Ball (r + 1) : Finset (Tree k)) ⊆ {1} ∪ (univ ×ˢ Ball r).image (fun q => dir q.1 * q.2) := by
  intro w hw
  rw [mem_Ball] at hw
  by_cases h1 : w = 1
  · simp [h1]
  · obtain ⟨p, hp⟩ := exists_dir_mul w h1
    refine mem_union_right _ (mem_image.2 ⟨(p, (dir p)⁻¹ * w), ?_, by simp⟩)
    simp only [mem_product, mem_univ, true_and, mem_Ball]; omega

/-- `|B_r| ≤ (2k+1)^r`. -/
theorem card_Ball_le (r : ℕ) : (Ball r : Finset (Tree k)).card ≤ (2 * k + 1) ^ r := by
  induction r with
  | zero =>
    have : (Ball 0 : Finset (Tree k)) = {1} := by
      ext w; simp [FreeGroup.norm_eq_zero]
    simp [this]
  | succ r ih =>
    calc (Ball (r + 1) : Finset (Tree k)).card
        ≤ ({1} ∪ (univ ×ˢ Ball r).image (fun q : (Fin k × Bool) × Tree k => dir q.1 * q.2)).card :=
          card_le_card (Ball_succ_subset r)
      _ ≤ 1 + (univ ×ˢ (Ball r : Finset (Tree k))).card := by
          refine (card_union_le _ _).trans ?_
          simp only [card_singleton]
          exact Nat.add_le_add_left card_image_le _
      _ = 1 + 2 * k * (Ball r : Finset (Tree k)).card := by
          simp [card_product, Fintype.card_prod, mul_comm]
      _ ≤ (2 * k + 1) ^ (r + 1) := by
          rw [pow_succ]
          have : 1 ≤ (2 * k + 1) ^ r := Nat.one_le_pow _ _ (by omega)
          nlinarith

/-- `r + 1 ≤ |B_r|`: the powers `g₀^i`, `i ≤ r`, are distinct. -/
theorem le_card_Ball (hk : 0 < k) (r : ℕ) : r + 1 ≤ (Ball r : Finset (Tree k)).card := by
  let g : Tree k := FreeGroup.of ⟨0, hk⟩
  have hinj : Set.InjOn (fun i : ℕ => g ^ i) (range (r + 1) : Set ℕ) := by
    intro i _ j _ h
    have := congrArg FreeGroup.norm h
    simpa [g, FreeGroup.norm_of_pow] using this
  calc r + 1 = (range (r + 1)).card := (card_range _).symm
    _ = ((range (r + 1)).image (fun i : ℕ => g ^ i)).card := (card_image_of_injOn hinj).symm
    _ ≤ _ := by
        apply card_le_card
        intro w hw
        simp only [mem_image, mem_range] at hw
        obtain ⟨i, hi, rfl⟩ := hw
        simp [g, FreeGroup.norm_of_pow]; omega

/-- The ball of radius `r` around `s`, as a finite set. -/
def BallAt (s : Tree k) (r : ℕ) : Finset (Tree k) := (Ball r).map (Equiv.mulLeft s).toEmbedding

lemma mem_BallAt {s w : Tree k} {r : ℕ} : w ∈ BallAt s r ↔ w ∈ ball s r := by
  simp [BallAt, mem_map_mulLeft, mem_ball]

lemma card_BallAt (s : Tree k) (r : ℕ) : (BallAt s r).card = (Ball r : Finset (Tree k)).card := by
  simp [BallAt]

/-- Balls of radius `ρ` that meet have centres at distance `≤ 2ρ`. -/
lemma mem_ball_of_not_disjoint {s w : Tree k} {ρ : ℕ} (h : ¬ Disjoint (ball w ρ) (ball s ρ)) :
    w ∈ ball s (2 * ρ) := by
  rw [Set.not_disjoint_iff] at h
  obtain ⟨u, h1, h2⟩ := h
  rw [mem_ball] at h1 h2 ⊢
  have : s⁻¹ * w = (s⁻¹ * u) * (w⁻¹ * u)⁻¹ := by group
  rw [this]
  have := FreeGroup.norm_mul_le (s⁻¹ * u) (w⁻¹ * u)⁻¹
  rw [FreeGroup.norm_inv_eq] at this
  omega

/-- A set of nodes whose `ρ`-balls are pairwise disjoint. -/
def Separated (ρ : ℕ) (S : Finset (Tree k)) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → Disjoint (ball s ρ) (ball s' ρ)

/-- **Packing.** Inside any finite set `T` there is a set `S ⊆ T` with pairwise disjoint balls of
radius `ρ` and `|T| ≤ |S| · |B_{2ρ}|`. -/
theorem exists_separated (T : Finset (Tree k)) (ρ : ℕ) :
    ∃ S ⊆ T, Separated ρ S ∧ T.card ≤ S.card * (Ball (2 * ρ) : Finset (Tree k)).card := by
  obtain ⟨S, hS, hmax⟩ := (T.powerset.filter (Separated ρ)).exists_max_image card
    ⟨∅, by simp [Separated]⟩
  simp only [mem_filter, mem_powerset] at hS hmax
  refine ⟨S, hS.1, hS.2, ?_⟩
  have hcov : T ⊆ S.biUnion (fun s => BallAt s (2 * ρ)) := by
    intro w hw
    by_cases hwS : w ∈ S
    · exact mem_biUnion.2 ⟨w, hwS, mem_BallAt.2 (by simp [mem_ball])⟩
    · by_contra hno
      have hsep : Separated ρ (insert w S) := by
        intro a ha b hb hab
        rw [mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · by_contra hd
          exact hno (mem_biUnion.2 ⟨b, hb, mem_BallAt.2 (mem_ball_of_not_disjoint hd)⟩)
        · by_contra hd
          exact hno (mem_biUnion.2 ⟨a, ha, mem_BallAt.2
            (mem_ball_of_not_disjoint (fun h => hd (Disjoint.symm h)))⟩)
        · exact hS.2 a ha b hb hab
      have := hmax (insert w S) ⟨insert_subset hw hS.1, hsep⟩
      rw [card_insert_of_notMem hwS] at this
      omega
  calc T.card ≤ (S.biUnion (fun s => BallAt s (2 * ρ))).card := card_le_card hcov
    _ ≤ ∑ s ∈ S, (BallAt s (2 * ρ)).card := card_biUnion_le
    _ = S.card * (Ball (2 * ρ) : Finset (Tree k)).card := by
        simp [card_BallAt]

end

end Podc.MinimalSymmetryBreaking
