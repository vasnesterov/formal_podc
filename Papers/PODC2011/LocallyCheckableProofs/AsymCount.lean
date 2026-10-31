import Papers.PODC2011.LocallyCheckableProofs.Basic

/-!
# Almost all graphs are asymmetric with many common neighbours (counting for Theorem 6.1)

The proof of Theorem 6.1 of Göös–Suomela uses that almost all graphs are asymmetric
(Erdős–Rényi). We need only a crude, self-contained version: for large `k`, at least half of the
`2 ^ (k choose 2)` graphs on `Fin k` are asymmetric and have at least three common neighbours for
every pair of distinct vertices (`exists_many_good`).
-/

namespace Podc.LocallyCheckableProofs

open Finset

/-- `H` is asymmetric: the identity is its only automorphism. -/
def Asymm {k : ℕ} (H : SimpleGraph (Fin k)) : Prop :=
  ∀ σ : Equiv.Perm (Fin k), (∀ a b, H.Adj (σ a) (σ b) ↔ H.Adj a b) → σ = 1

/-- Any two distinct vertices of `H` have at least three common neighbours. -/
def ThreeCommon {k : ℕ} (H : SimpleGraph (Fin k)) : Prop :=
  ∀ a b, a ≠ b → ∃ c₁ c₂ c₃, c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ ∧ (H.Adj a c₁ ∧ H.Adj b c₁) ∧
    (H.Adj a c₂ ∧ H.Adj b c₂) ∧ (H.Adj a c₃ ∧ H.Adj b c₃)

namespace AsymCount

/-! ### Generic counting tools -/

/-- Counting functions `α → Bool` that are determined by a "summary" `φ g ∈ R` together with
their values outside `T`: there are at most `|R| · 2 ^ (|α| - |T|)` of them. -/
-- CSLib candidate
theorem card_le_of_determined {α β : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (𝒜 : Finset (α → Bool)) (φ : (α → Bool) → β) (R : Finset β)
    (hR : ∀ g ∈ 𝒜, φ g ∈ R)
    (hdet : ∀ g ∈ 𝒜, ∀ g' ∈ 𝒜, φ g = φ g' → (∀ z ∉ T, g z = g' z) → g = g') :
    #𝒜 ≤ #R * 2 ^ (Fintype.card α - #T) := by
  classical
  have h := Finset.card_le_card_of_injOn
    (fun g => (φ g, fun z : {z // z ∉ T} => g z.1))
    (s := 𝒜) (t := R ×ˢ (univ : Finset ({z // z ∉ T} → Bool)))
    (fun g hg => by simp [hR g hg]) (by
      intro g hg g' hg' he
      simp only [Prod.mk.injEq] at he
      exact hdet g hg g' hg' he.1 (fun z hz => congrFun he.2 ⟨z, hz⟩))
  refine h.trans (le_of_eq ?_)
  rw [card_product, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl,
    Fintype.card_coe]

/-- A permutation `π` without fixed points on `D` admits a subset `T ⊆ D` with `π T ∩ T = ∅` and
`|D| ≤ 3 |T|` (a maximal such set). -/
-- CSLib candidate
theorem exists_large_sep {β : Type*} [DecidableEq β] (π : Equiv.Perm β) (D : Finset β)
    (hD : ∀ z ∈ D, π z ≠ z) : ∃ T ⊆ D, (∀ z ∈ T, π z ∉ T) ∧ #D ≤ 3 * #T := by
  set 𝒯 := D.powerset.filter (fun T => ∀ z ∈ T, π z ∉ T) with h𝒯
  have hne : 𝒯.Nonempty := ⟨∅, by simp [h𝒯]⟩
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image 𝒯 Finset.card hne
  simp only [h𝒯, mem_filter, mem_powerset] at hT
  refine ⟨T, hT.1, hT.2, ?_⟩
  have hsub : D ⊆ T ∪ T.image π ∪ T.image π.symm := by
    intro z hz
    by_cases hzT : z ∈ T
    · simp [hzT]
    have hnot : insert z T ∉ 𝒯 := by
      intro hin
      have := hmax _ hin
      rw [card_insert_of_notMem hzT] at this
      omega
    simp only [h𝒯, mem_filter, mem_powerset, not_and, not_forall, not_not] at hnot
    obtain ⟨w, hw, hπw⟩ := hnot (insert_subset hz hT.1)
    rw [mem_insert] at hw hπw
    rcases hw with rfl | hw
    · rcases hπw with h | h
      · exact absurd h (hD _ hz)
      · simp only [mem_union, mem_image]
        exact Or.inr ⟨π w, h, by simp⟩
    · rcases hπw with h | h
      · simp only [mem_union, mem_image]
        exact Or.inl (Or.inr ⟨w, hw, h⟩)
      · exact absurd h (hT.2 w hw)
  calc #D ≤ #(T ∪ T.image π ∪ T.image π.symm) := card_le_card hsub
    _ ≤ #T + #T + #T := by
      refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans
        (add_le_add le_rfl card_image_le)) card_image_le)
    _ = 3 * #T := by ring

/-- `Σ_σ y ^ |supp σ| ≤ (1 + n y) ^ n` over the permutations of an `n`-element type: compare with
the sum over all functions and factor it. -/
-- CSLib candidate
theorem sum_perm_pow_card_support_le {α : Type*} [Fintype α] [DecidableEq α] {y : ℝ}
    (hy : 0 ≤ y) :
    ∑ σ : Equiv.Perm α, y ^ #{a | σ a ≠ a} ≤ (1 + Fintype.card α * y) ^ Fintype.card α := by
  set w : α → α → ℝ := fun a b => if b = a then 1 else y with hw
  have hw0 : ∀ a b, 0 ≤ w a b := fun a b => by simp only [hw]; split_ifs <;> linarith
  have key : ∀ f : α → α, y ^ #{a | f a ≠ a} = ∏ a, w a (f a) := by
    intro f
    rw [← Finset.prod_const, Finset.prod_filter]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    simp only [hw]
    split_ifs <;> simp_all
  calc ∑ σ : Equiv.Perm α, y ^ #{a | σ a ≠ a}
      = ∑ f ∈ (univ : Finset (Equiv.Perm α)).image (fun σ : Equiv.Perm α => (⇑σ : α → α)),
          ∏ a, w a (f a) := by
        rw [Finset.sum_image (fun σ _ τ _ h => Equiv.ext (congrFun h))]
        exact Finset.sum_congr rfl (fun σ _ => key σ)
    _ ≤ ∑ f : α → α, ∏ a, w a (f a) :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun f _ _ => Finset.prod_nonneg (fun a _ => hw0 a (f a)))
    _ = ∏ a : α, ∑ b, w a b := (Fintype.prod_sum (fun a b => w a b)).symm
    _ ≤ ∏ _a : α, (1 + Fintype.card α * y) := by
        refine Finset.prod_le_prod₀ (fun a _ => Finset.sum_nonneg (fun b _ => hw0 a b))
          (fun a _ => ?_)
        rw [← Finset.add_sum_erase _ _ (mem_univ a)]
        simp only [hw, ↓reduceIte]
        have : ∑ x ∈ univ.erase a, (if x = a then (1 : ℝ) else y) = ∑ x ∈ univ.erase a, y :=
          Finset.sum_congr rfl (fun x hx => by simp [ne_of_mem_erase hx])
        rw [this, Finset.sum_const, card_erase_of_mem (mem_univ a), card_univ, nsmul_eq_mul]
        gcongr
        exact_mod_cast Nat.sub_le _ _
    _ = (1 + Fintype.card α * y) ^ Fintype.card α := by simp

/-! ### Encoding graphs on `Fin k` by functions `Sym2 (Fin k) → Bool` -/

/-- The graph on `Fin k` encoded by `g : Sym2 (Fin k) → Bool` (diagonal values are ignored). -/
def toGraph {k : ℕ} (g : Sym2 (Fin k) → Bool) : SimpleGraph (Fin k) where
  Adj a b := a ≠ b ∧ g s(a, b) = true
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

theorem toGraph_adj {k : ℕ} (g : Sym2 (Fin k) → Bool) (a b : Fin k) :
    (toGraph g).Adj a b ↔ a ≠ b ∧ g s(a, b) = true := Iff.rfl

/-- The permutation of `Sym2 α` induced by a permutation of `α`. -/
def symPerm {α : Type*} (σ : Equiv.Perm α) : Equiv.Perm (Sym2 α) where
  toFun := Sym2.map σ
  invFun := Sym2.map σ.symm
  left_inv z := by simp [Sym2.map_map]
  right_inv z := by simp [Sym2.map_map]

theorem symPerm_mk {α : Type*} (σ : Equiv.Perm α) (a b : α) :
    symPerm σ s(a, b) = s(σ a, σ b) := rfl

open Classical in
/-- Encodings whose graph is invariant under the vertex permutation `σ`. -/
noncomputable def invSet {k : ℕ} (σ : Equiv.Perm (Fin k)) : Finset (Sym2 (Fin k) → Bool) :=
  {g | ∀ a b, (toGraph g).Adj (σ a) (σ b) ↔ (toGraph g).Adj a b}

theorem invSet_apply {k : ℕ} {σ : Equiv.Perm (Fin k)} {g : Sym2 (Fin k) → Bool}
    (hg : g ∈ invSet σ) {z : Sym2 (Fin k)} (hz : ¬ z.IsDiag) : g (symPerm σ z) = g z := by
  classical
  induction z using Sym2.ind with
  | _ a b =>
    simp only [invSet, mem_filter, mem_univ, true_and] at hg
    have hab : a ≠ b := by simpa using hz
    have h := hg a b
    simp only [toGraph_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq, hab, not_false_eq_true,
      true_and] at h
    rw [symPerm_mk]
    exact Bool.eq_iff_iff.mpr h

/-- A graph invariant under a permutation moving `m` vertices is rare: the number of encodings
invariant under `σ` is at most `2 ^ (N - m ⌊(k-2)/6⌋)`. -/
theorem card_invSet_mul_le {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    #(invSet σ) * 2 ^ (#{a | σ a ≠ a} * ((k - 2) / 6)) ≤ 2 ^ Fintype.card (Sym2 (Fin k)) := by
  classical
  set π := symPerm σ with hπ
  set M : Finset (Fin k) := {a | σ a ≠ a} with hM
  set D : Finset (Sym2 (Fin k)) := {z | ¬ z.IsDiag ∧ π z ≠ z} with hDdef
  have hD : ∀ z ∈ D, π z ≠ z := by
    intro z hz
    simp only [hDdef, mem_filter, mem_univ, true_and] at hz
    exact hz.2
  obtain ⟨T, hTD, hTsep, hDT⟩ := exists_large_sep π D hD
  have hDlow : #M * (k - 2) ≤ 2 * #D := by
    set P := M.sigma (fun u => univ \ {u, σ u}) with hPdef
    have hP : #P = #M * (k - 2) := by
      rw [hPdef, card_sigma, Finset.sum_congr rfl (g := fun _ => k - 2), sum_const, smul_eq_mul]
      intro u hu
      simp only [hM, mem_filter, mem_univ, true_and] at hu
      rw [card_univ_sdiff, Fintype.card_fin, card_pair (Ne.symm hu)]
    rw [← hP]
    refine card_le_mul_card_image_of_maps_to (f := fun p => s(p.1, p.2)) ?_ 2 ?_
    · rintro ⟨u, x⟩ hp
      simp only [hPdef, mem_sigma, hM, mem_filter, mem_univ, true_and, mem_sdiff, mem_insert,
        mem_singleton, not_or] at hp
      simp only [hDdef, mem_filter, mem_univ, true_and, Sym2.mk_isDiag_iff, hπ, symPerm_mk,
        ne_eq, Sym2.eq_iff, not_or, not_and]
      refine ⟨fun h => hp.2.1 h.symm, fun h => absurd h hp.1, fun h => absurd h.symm hp.2.2⟩
    · intro z _
      induction z using Sym2.ind with
      | _ a b =>
        calc #{p ∈ P | s(p.1, p.2) = s(a, b)}
            ≤ #({⟨a, b⟩, ⟨b, a⟩} : Finset ((_ : Fin k) × Fin k)) := by
              refine card_le_card (fun p hp => ?_)
              obtain ⟨u, x⟩ := p
              simp only [mem_filter, Sym2.eq_iff] at hp
              rcases hp.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
          _ ≤ 2 := card_le_two
  have hT : #M * ((k - 2) / 6) ≤ #T := by
    have h6 : (k - 2) / 6 * 6 ≤ k - 2 := Nat.div_mul_le_self _ _
    have : #M * ((k - 2) / 6) * 6 ≤ #M * (k - 2) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ h6
    omega
  have hcard := card_le_of_determined T (invSet σ) (fun _ => ()) {()} (by simp) (by
    intro g hg g' hg' _ hoff
    funext z
    by_cases hz : z ∈ T
    · have hzD := hTD hz
      have hdiag : ¬ z.IsDiag := by
        simp only [hDdef, mem_filter, mem_univ, true_and] at hzD
        exact hzD.1
      rw [← invSet_apply hg hdiag, ← invSet_apply hg' hdiag]
      exact hoff _ (hTsep z hz)
    · exact hoff z hz)
  have hTN : #T ≤ Fintype.card (Sym2 (Fin k)) := card_le_univ T
  calc #(invSet σ) * 2 ^ (#M * ((k - 2) / 6))
      ≤ 2 ^ (Fintype.card (Sym2 (Fin k)) - #T) * 2 ^ #T := by
        refine Nat.mul_le_mul (by simpa using hcard) (Nat.pow_le_pow_right (by norm_num) hT)
    _ = 2 ^ Fintype.card (Sym2 (Fin k)) := by rw [← pow_add, Nat.sub_add_cancel hTN]

open Classical in
/-- Encodings in which no vertex outside `{u, v, c₁, c₂}` is joined (in the encoding) to both `u`
and `v`. -/
noncomputable def ncSet {k : ℕ} (u v c₁ c₂ : Fin k) : Finset (Sym2 (Fin k) → Bool) :=
  {g | ∀ w ∉ ({u, v, c₁, c₂} : Finset (Fin k)), ¬ (g s(u, w) = true ∧ g s(v, w) = true)}

/-- Few common neighbours are rare: `|ncSet u v c₁ c₂| ≤ 2 ^ N (3/4) ^ (k - 4)`. -/
theorem card_ncSet_le {k : ℕ} {u v : Fin k} (huv : u ≠ v) (c₁ c₂ : Fin k) :
    (#(ncSet u v c₁ c₂) : ℝ) ≤ 2 ^ Fintype.card (Sym2 (Fin k)) * (3 / 4) ^ (k - 4) := by
  classical
  set B : Finset (Fin k) := {u, v, c₁, c₂} with hB
  set A : Finset (Fin k) := univ \ B with hAdef
  have hA : k - 4 ≤ #A := by
    rw [hAdef, card_univ_sdiff, Fintype.card_fin]
    have : #B ≤ 4 := card_le_four
    omega
  have hAu : ∀ w ∈ A, w ≠ u ∧ w ≠ v := by
    intro w hw
    simp only [hAdef, hB, mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton,
      not_or] at hw
    exact ⟨hw.1, hw.2.1⟩
  set T : Finset (Sym2 (Fin k)) := A.image (fun w => s(u, w)) ∪ A.image (fun w => s(v, w))
    with hTdef
  have hT : #T = 2 * #A := by
    rw [hTdef, card_union_of_disjoint, card_image_of_injOn, card_image_of_injOn]
    · ring
    · intro w _ w' _ h; exact Sym2.congr_right.mp h
    · intro w _ w' _ h; exact Sym2.congr_right.mp h
    · rw [disjoint_left]
      intro z hz hz'
      simp only [mem_image] at hz hz'
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨w', hw', h⟩ := hz'
      rw [Sym2.eq_iff] at h
      rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · exact huv h.symm
      · exact (hAu w hw).2 h.symm
  set S3 : Finset (Bool × Bool) := {(false, false), (false, true), (true, false)} with hS3
  have hcard := card_le_of_determined T (ncSet u v c₁ c₂)
    (fun g (w : A) => (g s(u, w.1), g s(v, w.1))) (Fintype.piFinset fun _ => S3) (by
      intro g hg
      simp only [ncSet, mem_filter, mem_univ, true_and] at hg
      rw [Fintype.mem_piFinset]
      intro w
      have hw := hg w.1 (mem_sdiff.mp w.2).2
      revert hw
      cases g s(u, w.1) <;> cases g s(v, w.1) <;> simp [hS3]) (by
      intro g _ g' _ hφ hoff
      funext z
      by_cases hz : z ∈ T
      · simp only [hTdef, mem_union, mem_image] at hz
        rcases hz with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
        · exact (Prod.mk.inj (congrFun hφ ⟨w, hw⟩)).1
        · exact (Prod.mk.inj (congrFun hφ ⟨w, hw⟩)).2
      · exact hoff z hz)
  rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_coe,
    show #S3 = 3 by rfl, hT] at hcard
  have hTN : 2 * #A ≤ Fintype.card (Sym2 (Fin k)) := hT ▸ card_le_univ T
  have h1 : (#(ncSet u v c₁ c₂) : ℝ) * 4 ^ #A ≤ 3 ^ #A * 2 ^ Fintype.card (Sym2 (Fin k)) := by
    have : #(ncSet u v c₁ c₂) * 4 ^ #A ≤ 3 ^ #A * 2 ^ Fintype.card (Sym2 (Fin k)) := by
      calc #(ncSet u v c₁ c₂) * 4 ^ #A
          ≤ 3 ^ #A * 2 ^ (Fintype.card (Sym2 (Fin k)) - 2 * #A) * 2 ^ (2 * #A) := by
            rw [show (4 : ℕ) ^ #A = 2 ^ (2 * #A) by rw [pow_mul]; norm_num]
            exact Nat.mul_le_mul_right _ hcard
        _ = 3 ^ #A * 2 ^ Fintype.card (Sym2 (Fin k)) := by
            rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hTN]
    exact_mod_cast this
  have h4 : (0 : ℝ) < 4 ^ #A := by positivity
  calc (#(ncSet u v c₁ c₂) : ℝ) = #(ncSet u v c₁ c₂) * 4 ^ #A / 4 ^ #A := by field_simp
    _ ≤ 3 ^ #A * 2 ^ Fintype.card (Sym2 (Fin k)) / 4 ^ #A := by gcongr
    _ = 2 ^ Fintype.card (Sym2 (Fin k)) * (3 / 4) ^ #A := by rw [div_pow]; ring
    _ ≤ 2 ^ Fintype.card (Sym2 (Fin k)) * (3 / 4) ^ (k - 4) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hA)
          (by positivity)

theorem exists_ncSet_of_not_threeCommon {k : ℕ} {g : Sym2 (Fin k) → Bool}
    (h : ¬ ThreeCommon (toGraph g)) : ∃ u v c₁ c₂ : Fin k, u ≠ v ∧ g ∈ ncSet u v c₁ c₂ := by
  classical
  simp only [ThreeCommon, not_forall] at h
  obtain ⟨u, v, huv, hno⟩ := h
  set C : Finset (Fin k) := {w | (toGraph g).Adj u w ∧ (toGraph g).Adj v w} with hC
  have hC2 : #C ≤ 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨c₁, h₁, c₂, h₂, c₃, h₃, h12, h13, h23⟩ := two_lt_card.mp hlt
    simp only [hC, mem_filter, mem_univ, true_and] at h₁ h₂ h₃
    exact hno ⟨c₁, c₂, c₃, h12, h13, h23, h₁, h₂, h₃⟩
  obtain ⟨c₁, c₂, hsub⟩ : ∃ c₁ c₂, C ⊆ {c₁, c₂} := by
    obtain h0 | h1 | h2 : #C = 0 ∨ #C = 1 ∨ #C = 2 := by omega
    · exact ⟨u, u, by simp [card_eq_zero.mp h0]⟩
    · obtain ⟨a, ha⟩ := card_eq_one.mp h1
      exact ⟨a, a, by simp [ha]⟩
    · obtain ⟨a, b, _, hab⟩ := card_eq_two.mp h2
      exact ⟨a, b, hab.le⟩
  refine ⟨u, v, c₁, c₂, huv, ?_⟩
  simp only [ncSet, mem_filter, mem_univ, true_and]
  intro w hw ⟨hu, hv⟩
  simp only [mem_insert, mem_singleton, not_or] at hw
  have : w ∈ C := by
    simp only [hC, mem_filter, mem_univ, true_and, toGraph_adj]
    exact ⟨⟨Ne.symm hw.1, hu⟩, ⟨Ne.symm hw.2.1, hv⟩⟩
  have := hsub this
  simp only [mem_insert, mem_singleton] at this
  rcases this with h | h
  · exact hw.2.2.1 h
  · exact hw.2.2.2 h

/-! ### Elementary eventual inequalities -/

theorem eventually_asym : ∃ K, ∀ k ≥ K, 8 * k ^ 2 ≤ 2 ^ ((k - 2) / 6) := by
  have aux : ∀ j ≥ 20, 8 * (6 * j + 8) ^ 2 ≤ 2 ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih =>
      have : (6 * (j + 1) + 8) ^ 2 ≤ 2 * (6 * j + 8) ^ 2 := by nlinarith
      rw [pow_succ 2 j]
      omega
  refine ⟨122, fun k hk => ?_⟩
  have hj : 20 ≤ (k - 2) / 6 := by omega
  have hk' : k ≤ 6 * ((k - 2) / 6) + 8 := by omega
  calc 8 * k ^ 2 ≤ 8 * (6 * ((k - 2) / 6) + 8) ^ 2 := by gcongr
    _ ≤ 2 ^ ((k - 2) / 6) := aux _ hj

theorem eventually_three : ∃ K : ℕ, ∀ k : ℕ, k ≥ K → (k : ℝ) ^ 4 * (3 / 4) ^ (k - 4) ≤ 1 / 4 := by
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one 4 (r := 3 / 4) (by norm_num [abs_of_pos])
  have hev := ht.eventually (Iio_mem_nhds (show (0 : ℝ) < (3 / 4) ^ 4 / 4 by norm_num))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max K 4, fun k hk => ?_⟩
  have h1 := hK k (le_of_max_le_left hk)
  have h4 : 4 ≤ k := le_of_max_le_right hk
  have hsplit : ((3 : ℝ) / 4) ^ k = (3 / 4) ^ (k - 4) * (3 / 4) ^ 4 := by
    rw [← pow_add, Nat.sub_add_cancel h4]
  rw [hsplit] at h1
  have h34 : (0 : ℝ) < (3 / 4) ^ 4 := by norm_num
  nlinarith

/-! ### Counting bad encodings -/

open Classical in
/-- For `k` large (as quantified by the two hypotheses), at most half of all encodings
`Sym2 (Fin k) → Bool` give a graph that is not asymmetric or has a pair of distinct vertices with
at most two common neighbours. -/
theorem two_mul_card_bad_le {k : ℕ} (hk₁ : 8 * k ^ 2 ≤ 2 ^ ((k - 2) / 6))
    (hk₂ : (k : ℝ) ^ 4 * (3 / 4) ^ (k - 4) ≤ 1 / 4) :
    2 * #{g : Sym2 (Fin k) → Bool | ¬ (Asymm (toGraph g) ∧ ThreeCommon (toGraph g))}
      ≤ 2 ^ Fintype.card (Sym2 (Fin k)) := by
  classical
  set N := Fintype.card (Sym2 (Fin k)) with hN
  set c := (k - 2) / 6 with hc
  set y : ℝ := (1 / 2) ^ c with hy
  set Q : Finset (Fin k × Fin k × Fin k × Fin k) := {q | q.1 ≠ q.2.1} with hQ
  set bad : Finset (Sym2 (Fin k) → Bool) :=
    {g | ¬ (Asymm (toGraph g) ∧ ThreeCommon (toGraph g))} with hbad
  have hsub : bad ⊆
      (univ.erase 1).biUnion invSet ∪ Q.biUnion (fun q => ncSet q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    intro g hg
    simp only [hbad, mem_filter, mem_univ, true_and, not_and_or] at hg
    rcases hg with h | h
    · apply mem_union_left
      simp only [Asymm, not_forall] at h
      obtain ⟨σ, hσ, hne⟩ := h
      exact mem_biUnion.mpr ⟨σ, mem_erase.mpr ⟨hne, mem_univ _⟩, by simp [invSet, hσ]⟩
    · apply mem_union_right
      obtain ⟨u, v, c₁, c₂, huv, hg⟩ := exists_ncSet_of_not_threeCommon h
      exact mem_biUnion.mpr ⟨(u, v, c₁, c₂), by simp [hQ, huv], hg⟩
  have hinv : ∀ σ : Equiv.Perm (Fin k), (#(invSet σ) : ℝ) ≤ 2 ^ N * y ^ #{a | σ a ≠ a} := by
    intro σ
    have h := card_invSet_mul_le σ
    have h' : (#(invSet σ) : ℝ) * 2 ^ (#{a | σ a ≠ a} * c) ≤ 2 ^ N := by exact_mod_cast h
    have hpos : (0 : ℝ) < 2 ^ (#{a | σ a ≠ a} * c) := by positivity
    rw [hy, ← pow_mul, one_div_pow, mul_comm c, mul_one_div, le_div_iff₀ hpos]
    exact h'
  have hy0 : 0 ≤ y := by positivity
  have hky : (k : ℝ) * (k * y) ≤ 1 / 8 := by
    have : (8 : ℝ) * k ^ 2 ≤ 2 ^ c := by exact_mod_cast hk₁
    rw [hy, one_div_pow,
      show (k : ℝ) * (k * (1 / 2 ^ c)) = k ^ 2 / 2 ^ c by ring, div_le_iff₀ (by positivity)]
    linarith
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hA : ∑ σ ∈ (univ : Finset (Equiv.Perm (Fin k))).erase 1, (#(invSet σ) : ℝ) ≤ 2 ^ N / 4 := by
    calc ∑ σ ∈ (univ : Finset (Equiv.Perm (Fin k))).erase 1, (#(invSet σ) : ℝ)
        ≤ ∑ σ ∈ univ.erase 1, 2 ^ N * y ^ #{a | σ a ≠ a} := sum_le_sum (fun σ _ => hinv σ)
      _ = 2 ^ N * (∑ σ : Equiv.Perm (Fin k), y ^ #{a | σ a ≠ a} - 1) := by
          rw [sum_erase_eq_sub (mem_univ _), ← mul_sum]; simp [mul_sub]
      _ ≤ 2 ^ N * ((1 + k * y) ^ k - 1) := by
          gcongr
          simpa using sum_perm_pow_card_support_le (α := Fin k) hy0
      _ ≤ 2 ^ N * (Real.exp (k * (k * y)) - 1) := by
          gcongr
          rw [Real.exp_nat_mul]
          gcongr
          linarith [Real.add_one_le_exp (k * y)]
      _ ≤ 2 ^ N * (2 * (k * (k * y))) := by
          gcongr
          have h0 : 0 ≤ (k : ℝ) * (k * y) := by positivity
          have := Real.abs_exp_sub_one_le (x := k * (k * y)) (by rw [abs_of_nonneg h0]; linarith)
          rw [abs_of_nonneg h0] at this
          exact (le_abs_self _).trans this
      _ ≤ 2 ^ N * (2 * (1 / 8)) := by gcongr
      _ = 2 ^ N / 4 := by ring
  have hB : ∑ q ∈ Q, (#(ncSet q.1 q.2.1 q.2.2.1 q.2.2.2) : ℝ) ≤ 2 ^ N / 4 := by
    calc ∑ q ∈ Q, (#(ncSet q.1 q.2.1 q.2.2.1 q.2.2.2) : ℝ)
        ≤ ∑ q ∈ Q, 2 ^ N * (3 / 4) ^ (k - 4) := by
          refine sum_le_sum (fun q hq => ?_)
          simp only [hQ, mem_filter, mem_univ, true_and] at hq
          exact card_ncSet_le hq _ _
      _ = #Q * (2 ^ N * (3 / 4) ^ (k - 4)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) ^ 4 * (2 ^ N * (3 / 4) ^ (k - 4)) := by
          gcongr
          have : #Q ≤ k ^ 4 := by
            refine (card_le_univ Q).trans (le_of_eq ?_)
            simp only [Fintype.card_prod, Fintype.card_fin]
            ring
          exact_mod_cast this
      _ = 2 ^ N * ((k : ℝ) ^ 4 * (3 / 4) ^ (k - 4)) := by ring
      _ ≤ 2 ^ N * (1 / 4) := by gcongr
      _ = 2 ^ N / 4 := by ring
  have hcard : (#bad : ℝ) ≤ 2 ^ N / 2 := by
    have h1 := (card_le_card hsub).trans ((card_union_le _ _).trans
      (add_le_add (card_biUnion_le (s := univ.erase 1) (t := invSet))
        (card_biUnion_le (s := Q) (t := fun q => ncSet q.1 q.2.1 q.2.2.1 q.2.2.2))))
    have h2 : (#bad : ℝ) ≤ ∑ σ ∈ (univ : Finset (Equiv.Perm (Fin k))).erase 1, (#(invSet σ) : ℝ) +
        ∑ q ∈ Q, (#(ncSet q.1 q.2.1 q.2.2.1 q.2.2.2) : ℝ) := by exact_mod_cast h1
    linarith
  have : (2 * #bad : ℝ) ≤ 2 ^ N := by linarith
  exact_mod_cast this

end AsymCount

open AsymCount in
/-- For large `k`, at least `2 ^ (k choose 2) / 2` graphs on `Fin k` are asymmetric and have three
common neighbours for every pair of distinct vertices. -/
theorem exists_many_good : ∃ K, ∀ k ≥ K, ∃ 𝒢 : Finset (SimpleGraph (Fin k)),
    (∀ H ∈ 𝒢, Asymm H ∧ ThreeCommon H) ∧ 2 ^ (k.choose 2) ≤ 2 * 𝒢.card := by
  classical
  obtain ⟨K₁, hK₁⟩ := eventually_asym
  obtain ⟨K₂, hK₂⟩ := eventually_three
  refine ⟨max K₁ K₂, fun k hk => ?_⟩
  set good : Finset (Sym2 (Fin k) → Bool) :=
    {g | Asymm (toGraph g) ∧ ThreeCommon (toGraph g)} with hgood
  refine ⟨good.image toGraph, ?_, ?_⟩
  · intro H hH
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hH
    simpa [hgood] using hg
  have hbad := two_mul_card_bad_le (hK₁ k (le_of_max_le_left hk)) (hK₂ k (le_of_max_le_right hk))
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Sym2 (Fin k) → Bool)))
    (fun g => Asymm (toGraph g) ∧ ThreeCommon (toGraph g))
  rw [card_univ, Fintype.card_fun, Fintype.card_bool] at hsum
  have hfib : #good ≤ #(good.image toGraph) * 2 ^ k := by
    have := card_le_card_of_injOn (fun g => (toGraph g, fun a : Fin k => g s(a, a)))
      (s := good) (t := good.image toGraph ×ˢ (univ : Finset (Fin k → Bool)))
      (fun g hg => mem_product.mpr ⟨mem_image_of_mem _ hg, mem_univ _⟩) (by
        intro g _ g' _ h
        simp only [Prod.mk.injEq] at h
        funext z
        induction z using Sym2.ind with
        | _ a b =>
          by_cases hab : a = b
          · subst hab; exact congrFun h.2 a
          · have := congrArg (fun G : SimpleGraph (Fin k) => G.Adj a b) h.1
            simp only [toGraph_adj, ne_eq, hab, not_false_eq_true, true_and, eq_iff_iff] at this
            exact Bool.eq_iff_iff.mpr this)
    rwa [card_product, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
  have hN : Fintype.card (Sym2 (Fin k)) = k.choose 2 + k := by
    rw [Sym2.card, Fintype.card_fin, Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
  rw [hN, pow_add] at hsum hbad
  have hpos : 0 < 2 ^ k := by positivity
  have : 2 ^ k.choose 2 * 2 ^ k ≤ 2 * #(good.image toGraph) * 2 ^ k := by nlinarith
  exact Nat.le_of_mul_le_mul_right this hpos

end Podc.LocallyCheckableProofs
