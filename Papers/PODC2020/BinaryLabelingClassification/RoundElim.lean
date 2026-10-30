import Mathlib

/-!
# FDSO(s) is a fixed point of round elimination (Lemmas 10.8 and 10.9)

Section 10 of *Classification of Distributed Binary Labeling Problems* (Balliu, Brandt, Efron,
Hirvonen, Maus, Olivetti, Suomela; PODC 2020, arXiv:1911.13294v3), [BBEHMOS20].

This file formalizes the purely combinatorial part of the round elimination argument (§10.3,
§10.5, §10.6):

* Configurations of a node of degree `k` are tuples `c : Fin k → α`; the constraint only sees the
  multiset of labels `cfg c` (the paper's configurations are multisets). Constraints are therefore
  predicates on `Multiset α`.
* Output problems (§10.3). For a set-valued configuration `Y : Fin k → Set α`,
  `allChoices C Y` (every choice `c i ∈ Y i` satisfies `C`) and `exChoice C Y` (some choice
  satisfies `C`). The black output problem of `(W, B)` has white constraint `exChoice W` and black
  constraint `allChoices B`; the white output problem is the colour-swapped construction.
* Maximality (§10.3, "Simplification via maximality"): `Dom Y Z` (`Z` dominates `Y` up to a
  permutation of the ports) and `IsMaximal C Y`.
* `Lbl`: the four labels `A, H, T, X` of FDSO(s) (Definition 10.6), and the renaming `ι` of the
  bold labels of Lemmas 10.8/10.9 as sets of labels: `A = {X}`, `H = {H, X}`, `T = {T, X}`,
  `X = {A, H, T, X}`. The bold labels are again represented by `Lbl`, via `ι`.

Main results:

* `lemma_10_8_black`, `lemma_10_8_white`: the black output problem of FDSO(s) is `Π₁ = (W₁, B₁)`.
* `lemma_10_9_white`, `lemma_10_9_black`: the white output problem of `Π₁` is FDSO(s) again.
* `fdso_fixedPoint`: the package of the four statements.
-/

namespace Podc.BinaryLabeling.RoundElim

open Finset

/-! ### Generic notions -/

section Generic

variable {α : Type*} {k : ℕ}

/-- The multiset of labels of a configuration `c` of a degree-`k` node. -/
def cfg (c : Fin k → α) : Multiset α := (Finset.univ : Finset (Fin k)).val.map c

/-- Every choice `c i ∈ Y i` gives a configuration satisfying `C` (the constraint of the output
problem on the side that *starts* the output problem, §10.3). -/
def allChoices (C : Multiset α → Prop) (Y : Fin k → Set α) : Prop :=
  ∀ c : Fin k → α, (∀ i, c i ∈ Y i) → C (cfg c)

/-- Some choice `c i ∈ Y i` gives a configuration satisfying `C` (the constraint of the output
problem on the other side, §10.3). -/
def exChoice (C : Multiset α → Prop) (Y : Fin k → Set α) : Prop :=
  ∃ c : Fin k → α, (∀ i, c i ∈ Y i) ∧ C (cfg c)

/-- `Z` dominates `Y`: after permuting the ports, `Y i ⊆ Z i` for all `i`. -/
def Dom (Y Z : Fin k → Set α) : Prop :=
  ∃ π : Equiv.Perm (Fin k), ∀ i, Y i ⊆ Z (π i)

/-- `Y` is a maximal configuration of the set-constraint `C`: every configuration of `C`
dominating `Y` is dominated by `Y` (§10.3, "Simplification via maximality"). -/
def IsMaximal (C : (Fin k → Set α) → Prop) (Y : Fin k → Set α) : Prop :=
  C Y ∧ ∀ Z, C Z → Dom Y Z → Dom Z Y

lemma cfg_comp_perm (c : Fin k → α) (σ : Equiv.Perm (Fin k)) : cfg (c ∘ σ) = cfg c := by
  unfold cfg
  rw [← Multiset.map_map]
  congr 1
  simp

lemma allChoices_comp_perm (C : Multiset α → Prop) (Z : Fin k → Set α) (σ : Equiv.Perm (Fin k))
    (h : allChoices C Z) : allChoices C (Z ∘ σ) := by
  intro c hc
  have := h (c ∘ σ.symm) (fun j => by simpa using hc (σ.symm j))
  rwa [cfg_comp_perm] at this

lemma count_cfg [DecidableEq α] (c : Fin k → α) (a : α) :
    (cfg c).count a = (univ.filter fun i => c i = a).card := by
  unfold cfg
  rw [Multiset.count_map]
  simp only [Finset.card, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun _ _ => eq_comm)

lemma mem_cfg {c : Fin k → α} {a : α} : a ∈ cfg c ↔ ∃ i, c i = a := by
  simp [cfg]

lemma count_cfg_mono [DecidableEq α] {c c' : Fin k → α} {a : α} (h : ∀ i, c i = a → c' i = a) :
    (cfg c).count a ≤ (cfg c').count a := by
  rw [count_cfg, count_cfg]
  exact Finset.card_le_card (fun i => by simpa using h i)

lemma cfg_const (a : α) : cfg (fun _ : Fin k => a) = Multiset.replicate k a := by
  simp [cfg, Multiset.map_const']

lemma cfg_update [DecidableEq α] (c : Fin k → α) (j : Fin k) (a : α) :
    cfg (Function.update c j a) = a ::ₘ (cfg c).erase (c j) := by
  have key : ∀ c' : Fin k → α, cfg c' = c' j ::ₘ ((univ : Finset (Fin k)).val.erase j).map c' := by
    intro c'
    unfold cfg
    conv_lhs => rw [← Multiset.cons_erase (Finset.mem_univ_val j)]
    rw [Multiset.map_cons]
  rw [key, key c, Multiset.erase_cons_head]
  simp only [Function.update_self]
  congr 1
  refine Multiset.map_congr rfl (fun i hi => ?_)
  have : i ≠ j := by
    rintro rfl
    simp [Multiset.Nodup.mem_erase_iff (Finset.nodup _)] at hi
  simp [Function.update_of_ne this]

lemma cfg_ite (S : Finset (Fin k)) (a b : α) [DecidablePred (· ∈ S)] :
    cfg (fun i => if i ∈ S then a else b) =
      Multiset.replicate S.card a + Multiset.replicate (k - S.card) b := by
  unfold cfg
  rw [← Multiset.filter_add_not (· ∈ S) (univ : Finset (Fin k)).val, Multiset.map_add]
  have hS : Multiset.card (Multiset.filter (· ∈ S) (univ : Finset (Fin k)).val) = S.card := by
    change ((univ : Finset (Fin k)).filter (· ∈ S)).card = S.card
    simp
  have hT : Multiset.card (Multiset.filter (fun i => ¬ i ∈ S) (univ : Finset (Fin k)).val) =
      k - S.card := by
    have h1 := Multiset.card_add (Multiset.filter (· ∈ S) (univ : Finset (Fin k)).val)
      (Multiset.filter (fun i => ¬ i ∈ S) (univ : Finset (Fin k)).val)
    rw [Multiset.filter_add_not] at h1
    simp only [Finset.card_val, Finset.card_univ, Fintype.card_fin] at h1
    omega
  congr 1
  · rw [Multiset.eq_replicate]
    refine ⟨by simp [hS], fun x hx => ?_⟩
    simp only [Multiset.mem_map, Multiset.mem_filter] at hx
    obtain ⟨i, ⟨_, hi⟩, rfl⟩ := hx
    simp [hi]
  · rw [Multiset.eq_replicate]
    refine ⟨by simp [hT], fun x hx => ?_⟩
    simp only [Multiset.mem_map, Multiset.mem_filter] at hx
    obtain ⟨i, ⟨_, hi⟩, rfl⟩ := hx
    simp [hi]

lemma replicate_erase [DecidableEq α] (n : ℕ) (a : α) :
    (Multiset.replicate n a).erase a = Multiset.replicate (n - 1) a := by
  cases n with
  | zero => simp
  | succ n => simp [Multiset.replicate_succ]

/-- One label `a` at port `i`, label `b` everywhere else. -/
lemma cfg_single [DecidableEq α] (i : Fin k) (a b : α) :
    cfg (Function.update (fun _ => b) i a) = a ::ₘ Multiset.replicate (k - 1) b := by
  rw [cfg_update, cfg_const, replicate_erase]

/-- Label `a` at port `i`, `a'` at port `j ≠ i`, label `b ≠ a` everywhere else. -/
lemma cfg_pair [DecidableEq α] {i j : Fin k} (hij : i ≠ j) {a b : α} (hab : a ≠ b) (a' : α) :
    cfg (Function.update (Function.update (fun _ => b) i a) j a') =
      a ::ₘ a' ::ₘ Multiset.replicate (k - 2) b := by
  rw [cfg_update, cfg_single, Function.update_of_ne hij.symm, Multiset.erase_cons_tail _ hab,
    replicate_erase, Multiset.cons_swap]
  rfl

end Generic

/-! ### Labels, renaming, and the abstract maximality argument -/

/-- The four labels of FDSO(s) (Definition 10.6). -/
inductive Lbl
  | A
  | H
  | T
  | X
  deriving DecidableEq, Repr

open Lbl

/-- The renaming of the bold labels of Lemmas 10.8 and 10.9 as sets of labels:
`A = {X}`, `H = {H, X}`, `T = {T, X}`, `X = {A, H, T, X}`. -/
def bold : Lbl → Set Lbl
  | A => {X}
  | H => {H, X}
  | T => {T, X}
  | X => Set.univ

@[simp] lemma X_mem_bold (l : Lbl) : X ∈ bold l := by cases l <;> simp [bold]

@[simp] lemma A_mem_bold (l : Lbl) : A ∈ bold l ↔ l = X := by cases l <;> simp [bold]

@[simp] lemma H_mem_bold (l : Lbl) : H ∈ bold l ↔ l = H ∨ l = X := by cases l <;> simp [bold]

@[simp] lemma T_mem_bold (l : Lbl) : T ∈ bold l ↔ l = T ∨ l = X := by cases l <;> simp [bold]

/-- A label of the set `bold l` avoiding `X` whenever possible. -/
def rep : Lbl → Lbl
  | A => X
  | H => H
  | T => T
  | X => A

lemma rep_mem_bold (l : Lbl) : rep l ∈ bold l := by cases l <;> simp [rep]

lemma cfg_comp {k : ℕ} (f : Lbl → Lbl) (y : Fin k → Lbl) : cfg (f ∘ y) = (cfg y).map f := by
  unfold cfg
  rw [Multiset.map_map]

/-- Changing the representative choice `rep ∘ y` at one port. -/
lemma cfg_update_rep {k : ℕ} (y : Fin k → Lbl) (i : Fin k) (l : Lbl) :
    cfg (Function.update (rep ∘ y) i l) = l ::ₘ ((cfg y).map rep).erase (rep (y i)) := by
  rw [cfg_update, cfg_comp]
  rfl

/-- The abstract maximality argument of the proofs of Lemmas 10.8(1) and 10.9(1): if every
configuration `bold ∘ y` with `G y` is valid and *rigid* (no valid configuration strictly
contains it), and every valid configuration is contained in one of them, then the maximal valid
configurations are exactly the `bold ∘ y` with `G y`. -/
theorem isMaximal_allChoices_iff {k : ℕ} {C G : Multiset Lbl → Prop}
    (hvalid : ∀ y : Fin k → Lbl, G (cfg y) → allChoices C (bold ∘ y))
    (hrigid : ∀ y : Fin k → Lbl, G (cfg y) → ∀ Z, allChoices C Z →
      (∀ i, bold (y i) ⊆ Z i) → ∀ i, Z i ⊆ bold (y i))
    (hdom : ∀ Y : Fin k → Set Lbl, allChoices C Y → ∃ y, G (cfg y) ∧ ∀ i, Y i ⊆ bold (y i))
    (Y : Fin k → Set Lbl) :
    IsMaximal (allChoices C) Y ↔ ∃ y, G (cfg y) ∧ Y = bold ∘ y := by
  constructor
  · rintro ⟨hY, hmax⟩
    obtain ⟨y, hy, hYy⟩ := hdom Y hY
    obtain ⟨ρ, hρ⟩ := hmax (bold ∘ y) (hvalid y hy) ⟨Equiv.refl _, hYy⟩
    have heq : ∀ i, Y (ρ i) = bold (y i) := fun i =>
      (hrigid y hy (Y ∘ ρ) (allChoices_comp_perm C Y ρ hY) hρ i).antisymm (hρ i)
    refine ⟨y ∘ ρ.symm, by rwa [cfg_comp_perm], funext fun j => ?_⟩
    simpa using heq (ρ.symm j)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨hvalid y hy, fun Z hZ ⟨π, hπ⟩ => ⟨π.symm, fun j => ?_⟩⟩
    simpa using hrigid y hy (Z ∘ π) (allChoices_comp_perm C Z π hZ) hπ (π.symm j)

/-! ### The problems FDSO(s) and Π₁ -/

/-- The white constraint of FDSO(s) (Definition 10.6), as a set of multisets of size `d`:
`A X^{d-1} | H^{s+1} X^{d-s-1} | T^{d-s+1} X^{s-1}`. -/
def W0 (d s : ℕ) (m : Multiset Lbl) : Prop :=
  m = A ::ₘ Multiset.replicate (d - 1) X ∨
  m = Multiset.replicate (s + 1) H + Multiset.replicate (d - s - 1) X ∨
  m = Multiset.replicate (d - s + 1) T + Multiset.replicate (s - 1) X

/-- The black constraint of FDSO(s) (Definition 10.6): `X[AHTX]^{δ-1} | HT[AHTX]^{δ-2}`,
i.e. (on multisets of size `δ`) the configuration contains an `X`, or both an `H` and a `T`. -/
def B0 (m : Multiset Lbl) : Prop := X ∈ m ∨ (H ∈ m ∧ T ∈ m)

/-- The white constraint `W₁` of `Π₁` (Lemma 10.8), in the bold labels:
`X[AHTX]^{d-1} | H^{s+1}[AHTX]^{d-s-1} | T^{d-s+1}[AHTX]^{s-1}`, i.e. (on multisets of size `d`)
the configuration contains an `X`, or at least `s+1` labels `H`, or at least `d-s+1` labels `T`. -/
def W1 (d s : ℕ) (m : Multiset Lbl) : Prop :=
  X ∈ m ∨ s + 1 ≤ m.count H ∨ d - s + 1 ≤ m.count T

/-- The black constraint `B₁` of `Π₁` (Lemma 10.8), in the bold labels:
`A X^{δ-1} | H T X^{δ-2}`. -/
def B1 (δ : ℕ) (m : Multiset Lbl) : Prop :=
  m = A ::ₘ Multiset.replicate (δ - 1) X ∨ m = H ::ₘ T ::ₘ Multiset.replicate (δ - 2) X

lemma exists_mem_not_mem {Y S : Set Lbl} (h : ¬ Y ⊆ S) : ∃ x ∈ Y, x ∉ S := Set.not_subset.mp h

/-! ### Lemma 10.8: the black output problem of FDSO(s) is `Π₁` -/

section Lemma108

variable {d s δ : ℕ}

/-- The configurations `A X^{δ-1}` and `H T X^{δ-2}` of `B₁` are valid black configurations of the
black output problem of FDSO(s). -/
lemma B1_valid (y : Fin δ → Lbl) (hy : B1 δ (cfg y)) : allChoices B0 (bold ∘ y) := by
  intro c hc
  rcases hy with h | h
  · obtain ⟨i, hi⟩ := mem_cfg.mp (show A ∈ cfg y by simp [h])
    have := hc i
    simp only [Function.comp, hi, bold, Set.mem_singleton_iff] at this
    exact Or.inl (mem_cfg.mpr ⟨i, this⟩)
  · obtain ⟨i, hi⟩ := mem_cfg.mp (show H ∈ cfg y by simp [h])
    obtain ⟨j, hj⟩ := mem_cfg.mp (show T ∈ cfg y by simp [h])
    have hci := hc i
    have hcj := hc j
    simp only [Function.comp, hi, hj, bold, Set.mem_insert_iff, Set.mem_singleton_iff] at hci hcj
    rcases hci with hci | hci
    · rcases hcj with hcj | hcj
      · exact Or.inr ⟨mem_cfg.mpr ⟨i, hci⟩, mem_cfg.mpr ⟨j, hcj⟩⟩
      · exact Or.inl (mem_cfg.mpr ⟨j, hcj⟩)
    · exact Or.inl (mem_cfg.mpr ⟨i, hci⟩)

/-- No valid black configuration strictly contains `A X^{δ-1}` or `H T X^{δ-2}`. -/
lemma B1_rigid (y : Fin δ → Lbl) (hy : B1 δ (cfg y)) (Z : Fin δ → Set Lbl)
    (hZ : allChoices B0 Z) (hsup : ∀ i, bold (y i) ⊆ Z i) (i : Fin δ) : Z i ⊆ bold (y i) := by
  intro l hl
  by_contra hn
  have hc : ∀ j, Function.update (rep ∘ y) i l j ∈ Z j := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hl
    · rw [Function.update_of_ne hj]; exact hsup j (rep_mem_bold _)
  have h := hZ _ hc
  rw [cfg_update_rep] at h
  have hmem : y i ∈ cfg y := mem_cfg.mpr ⟨i, rfl⟩
  rcases hy with hy | hy <;> rw [hy] at h hmem <;> cases hv : y i <;> rw [hv] at hn hmem h <;>
    cases l <;> simp_all [B0, bold, rep, Multiset.mem_replicate]

/-- Every valid black configuration of the black output problem of FDSO(s) is contained in
`A X^{δ-1}` or `H T X^{δ-2}` (proof of Lemma 10.8 (1)). -/
lemma B1_dom (Y : Fin δ → Set Lbl) (hY : allChoices B0 Y) :
    ∃ y, B1 δ (cfg y) ∧ ∀ i, Y i ⊆ bold (y i) := by
  by_cases h1 : ∃ i, Y i ⊆ {X}
  · obtain ⟨i, hi⟩ := h1
    refine ⟨Function.update (fun _ => X) i A, Or.inl (cfg_single i A X), fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; simpa [bold] using hi
    · simp [Function.update_of_ne hj, bold]
  simp only [not_exists] at h1
  by_cases h2 : ∃ i, Y i ⊆ {H, X}
  swap
  · simp only [not_exists] at h2
    choose c hcY hcS using fun i => exists_mem_not_mem (h2 i)
    exfalso
    rcases hY c hcY with h | ⟨h, -⟩ <;> obtain ⟨i, hi⟩ := mem_cfg.mp h <;>
      exact hcS i (by simp [hi])
  by_cases h3 : ∃ j, Y j ⊆ {T, X}
  swap
  · simp only [not_exists] at h3
    choose c hcY hcS using fun i => exists_mem_not_mem (h3 i)
    exfalso
    rcases hY c hcY with h | ⟨-, h⟩ <;> obtain ⟨i, hi⟩ := mem_cfg.mp h <;>
      exact hcS i (by simp [hi])
  obtain ⟨i, hi⟩ := h2
  obtain ⟨j, hj⟩ := h3
  have hij : i ≠ j := by
    rintro rfl
    apply h1 i
    intro x hx
    have h1 := hi hx
    have h2 := hj hx
    cases x <;> simp_all
  refine ⟨Function.update (Function.update (fun _ => X) i H) j T,
    Or.inr (cfg_pair hij (by decide) T), fun l => ?_⟩
  by_cases hlj : l = j
  · subst hlj; simpa [bold] using hj
  · rw [Function.update_of_ne hlj]
    by_cases hli : l = i
    · subst hli; simpa [bold] using hi
    · simp [Function.update_of_ne hli, bold]

/-- **Lemma 10.8 (1)** of [BBEHMOS20]: the maximal black configurations of the black output
problem of FDSO(s) are exactly `A X^{δ-1}` and `H T X^{δ-2}` (in the bold labels). -/
theorem lemma_10_8_black (Y : Fin δ → Set Lbl) :
    IsMaximal (allChoices B0) Y ↔ ∃ y : Fin δ → Lbl, B1 δ (cfg y) ∧ Y = bold ∘ y :=
  isMaximal_allChoices_iff B1_valid B1_rigid B1_dom Y

/-- **Lemma 10.8 (2)** of [BBEHMOS20]: a white configuration in the bold labels satisfies the
white constraint of the black output problem of FDSO(s) (some choice is a white configuration of
FDSO(s)) iff it belongs to `W₁ = X[AHTX]^{d-1} | H^{s+1}[AHTX]^{d-s-1} | T^{d-s+1}[AHTX]^{s-1}`. -/
theorem lemma_10_8_white (hsd : s ≤ d) (y : Fin d → Lbl) :
    exChoice (W0 d s) (bold ∘ y) ↔ W1 d s (cfg y) := by
  constructor
  · rintro ⟨c, hc, hW⟩
    by_cases hX : X ∈ cfg y
    · exact Or.inl hX
    have hX' : ∀ i, y i ≠ X := fun i h => hX (mem_cfg.mpr ⟨i, h⟩)
    rcases hW with h | h | h
    · exfalso
      obtain ⟨i, hi⟩ := mem_cfg.mp (show A ∈ cfg c by simp [h])
      have := hc i
      rw [hi] at this
      exact hX' i (by simpa using this)
    · refine Or.inr (Or.inl ?_)
      have : (cfg c).count H = s + 1 := by simp [h, Multiset.count_replicate]
      rw [← this]
      refine count_cfg_mono fun i hi => ?_
      have := hc i
      rw [hi] at this
      simpa [hX' i] using this
    · refine Or.inr (Or.inr ?_)
      have : (cfg c).count T = d - s + 1 := by simp [h, Multiset.count_replicate]
      rw [← this]
      refine count_cfg_mono fun i hi => ?_
      have := hc i
      rw [hi] at this
      simpa [hX' i] using this
  · rintro (h | h | h)
    · obtain ⟨i, hi⟩ := mem_cfg.mp h
      refine ⟨Function.update (fun _ => X) i A, fun j => ?_, Or.inl (cfg_single i A X)⟩
      by_cases hj : j = i
      · subst hj; simp [hi]
      · simp [Function.update_of_ne hj]
    · rw [count_cfg] at h
      obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq h
      refine ⟨fun i => if i ∈ S then H else X, fun j => ?_, Or.inr (Or.inl ?_)⟩
      · by_cases hj : j ∈ S
        · have := hS hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          simp [hj, this]
        · simp [hj]
      · rw [cfg_ite, hcard, Nat.sub_add_eq]
    · rw [count_cfg] at h
      obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq h
      refine ⟨fun i => if i ∈ S then T else X, fun j => ?_, Or.inr (Or.inr ?_)⟩
      · by_cases hj : j ∈ S
        · have := hS hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          simp [hj, this]
        · simp [hj]
      · rw [cfg_ite, hcard, show d - (d - s + 1) = s - 1 by omega]

end Lemma108

/-! ### Lemma 10.9: the white output problem of `Π₁` is FDSO(s) -/

section Lemma109

variable {d s δ : ℕ}

/-- The configurations of `W₀` are valid white configurations of the white output problem of
`Π₁`. -/
lemma W0_valid (y : Fin d → Lbl) (hy : W0 d s (cfg y)) : allChoices (W1 d s) (bold ∘ y) := by
  intro c hc
  by_cases hX : X ∈ cfg c
  · exact Or.inl hX
  have hX' : ∀ i, c i ≠ X := fun i h => hX (mem_cfg.mpr ⟨i, h⟩)
  rcases hy with h | h | h
  · exfalso
    obtain ⟨i, hi⟩ := mem_cfg.mp (show A ∈ cfg y by simp [h])
    have := hc i
    simp only [Function.comp, hi, bold, Set.mem_singleton_iff] at this
    exact hX' i this
  · refine Or.inr (Or.inl ?_)
    have : (cfg y).count H = s + 1 := by simp [h, Multiset.count_replicate]
    rw [← this]
    refine count_cfg_mono fun i hi => ?_
    have := hc i
    simp only [Function.comp, hi, bold, Set.mem_insert_iff, Set.mem_singleton_iff] at this
    simpa [hX' i] using this
  · refine Or.inr (Or.inr ?_)
    have : (cfg y).count T = d - s + 1 := by simp [h, Multiset.count_replicate]
    rw [← this]
    refine count_cfg_mono fun i hi => ?_
    have := hc i
    simp only [Function.comp, hi, bold, Set.mem_insert_iff, Set.mem_singleton_iff] at this
    simpa [hX' i] using this

/-- No valid white configuration of the white output problem of `Π₁` strictly contains a
configuration of `W₀`. -/
lemma W0_rigid (hs : 0 < s) (hsd : s < d) (y : Fin d → Lbl) (hy : W0 d s (cfg y))
    (Z : Fin d → Set Lbl) (hZ : allChoices (W1 d s) Z) (hsup : ∀ i, bold (y i) ⊆ Z i)
    (i : Fin d) : Z i ⊆ bold (y i) := by
  intro l hl
  by_contra hn
  have hc : ∀ j, Function.update (rep ∘ y) i l j ∈ Z j := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hl
    · rw [Function.update_of_ne hj]; exact hsup j (rep_mem_bold _)
  have h := hZ _ hc
  rw [cfg_update_rep] at h
  have hmem : y i ∈ cfg y := mem_cfg.mpr ⟨i, rfl⟩
  rcases hy with hy | hy | hy <;> rw [hy] at h hmem <;>
    (try rw [Multiset.replicate_succ] at h hmem) <;>
    cases hv : y i <;> rw [hv] at hn hmem h <;> cases l <;>
    simp_all [W1, bold, rep, Multiset.mem_replicate] <;> omega

/-- Every valid white configuration of the white output problem of `Π₁` is contained in one of
`A X^{d-1}`, `H^{s+1} X^{d-s-1}`, `T^{d-s+1} X^{s-1}` (proof of Lemma 10.9 (1), including the
counting argument for the "flexible" ports whose set contains both `H` and `T`). -/
lemma W0_dom (hs : 0 < s) (hsd : s < d) (Y : Fin d → Set Lbl) (hY : allChoices (W1 d s) Y) :
    ∃ y, W0 d s (cfg y) ∧ ∀ i, Y i ⊆ bold (y i) := by
  classical
  by_cases h1 : ∃ i, Y i ⊆ {X}
  · obtain ⟨i, hi⟩ := h1
    refine ⟨Function.update (fun _ => X) i A, Or.inl (cfg_single i A X), fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; simpa [bold] using hi
    · simp [Function.update_of_ne hj, bold]
  simp only [not_exists] at h1
  set P := univ.filter (fun i => Y i ⊆ {H, X}) with hP
  set Q := univ.filter (fun i => Y i ⊆ {T, X}) with hQ
  by_cases h2 : s + 1 ≤ P.card
  · obtain ⟨S, hSP, hS⟩ := Finset.exists_subset_card_eq h2
    refine ⟨fun i => if i ∈ S then H else X, Or.inr (Or.inl ?_), fun j => ?_⟩
    · rw [cfg_ite, hS, Nat.sub_add_eq]
    · by_cases hj : j ∈ S
      · have := hSP hj
        simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at this
        simpa [hj, bold] using this
      · simp [hj, bold]
  by_cases h3 : d - s + 1 ≤ Q.card
  · obtain ⟨S, hSQ, hS⟩ := Finset.exists_subset_card_eq h3
    refine ⟨fun i => if i ∈ S then T else X, Or.inr (Or.inr ?_), fun j => ?_⟩
    · rw [cfg_ite, hS, show d - (d - s + 1) = s - 1 by omega]
    · by_cases hj : j ∈ S
      · have := hSQ hj
        simp only [hQ, Finset.mem_filter, Finset.mem_univ, true_and] at this
        simpa [hj, bold] using this
      · simp [hj, bold]
  exfalso
  simp only [not_le] at h2 h3
  -- the flexible ports: neither forced to `H` nor to `T`, and without an `A`
  set F := univ.filter (fun i => i ∉ P ∧ i ∉ Q ∧ A ∉ Y i) with hF
  obtain ⟨FH, hFH, hFHc⟩ :=
    Finset.exists_subset_card_eq (min_le_left F.card (s - P.card))
  let c : Fin d → Lbl := fun i =>
    if i ∈ P then H else if i ∈ Q then T else if A ∈ Y i then A else if i ∈ FH then H else T
  have hc : ∀ i, c i ∈ Y i := by
    intro i
    obtain ⟨x, hx, hxX⟩ := exists_mem_not_mem (h1 i)
    simp only [c]
    split_ifs with hiP hiQ hiA
    · have := (Finset.mem_filter.mp hiP).2 hx
      cases x <;> simp_all
    · have := (Finset.mem_filter.mp hiQ).2 hx
      cases x <;> simp_all
    · exact hiA
    all_goals
      have hP' : ¬ Y i ⊆ {H, X} := fun h => hiP (by simp [hP, h])
      have hQ' : ¬ Y i ⊆ {T, X} := fun h => hiQ (by simp [hQ, h])
      obtain ⟨u, hu, huS⟩ := exists_mem_not_mem hP'
      obtain ⟨v, hv, hvS⟩ := exists_mem_not_mem hQ'
      cases u <;> cases v <;> simp_all
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro i hiP hiQ
    apply h1 i
    intro x hx
    have h1 := (Finset.mem_filter.mp hiP).2 hx
    have h2 := (Finset.mem_filter.mp hiQ).2 hx
    cases x <;> simp_all
  have hPQF : Disjoint (P ∪ Q) F := by
    rw [Finset.disjoint_left]
    intro i hi hiF
    simp only [hF, Finset.mem_filter] at hiF
    rcases Finset.mem_union.mp hi with h | h <;> tauto
  have hcard : P.card + Q.card + F.card ≤ d := by
    have := Finset.card_le_univ (P ∪ Q ∪ F)
    rw [Finset.card_union_of_disjoint hPQF, Finset.card_union_of_disjoint hPQ,
      Fintype.card_fin] at this
    exact this
  have hH : (cfg c).count H ≤ s := by
    rw [count_cfg]
    calc (univ.filter fun i => c i = H).card ≤ (P ∪ FH).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, c] at hi
          rw [Finset.mem_union]
          split_ifs at hi <;> simp_all
      _ ≤ P.card + FH.card := Finset.card_union_le _ _
      _ ≤ s := by omega
  have hT : (cfg c).count T ≤ d - s := by
    rw [count_cfg]
    calc (univ.filter fun i => c i = T).card ≤ (Q ∪ (F \ FH)).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, c] at hi
          rw [Finset.mem_union, Finset.mem_sdiff]
          split_ifs at hi with hiP hiQ hiA hiFH <;> simp_all
      _ ≤ Q.card + (F \ FH).card := Finset.card_union_le _ _
      _ = Q.card + (F.card - FH.card) := by rw [Finset.card_sdiff_of_subset hFH]
      _ ≤ d - s := by
          rw [hFHc, Nat.min_def]
          split_ifs <;> omega
  have hX : X ∉ cfg c := by
    rw [mem_cfg]
    rintro ⟨i, hi⟩
    simp only [c] at hi
    split_ifs at hi
  rcases hY c hc with h | h | h
  · exact hX h
  · omega
  · omega

/-- **Lemma 10.9 (1)** of [BBEHMOS20]: the maximal white configurations of the white output
problem of `Π₁` are exactly `A X^{d-1}`, `H^{s+1} X^{d-s-1}` and `T^{d-s+1} X^{s-1}` (in the
bold labels of the second renaming), i.e. the white constraint of FDSO(s). -/
theorem lemma_10_9_white (hs : 0 < s) (hsd : s < d) (Y : Fin d → Set Lbl) :
    IsMaximal (allChoices (W1 d s)) Y ↔ ∃ y : Fin d → Lbl, W0 d s (cfg y) ∧ Y = bold ∘ y :=
  isMaximal_allChoices_iff W0_valid (W0_rigid hs hsd) (W0_dom hs hsd) Y

/-- **Lemma 10.9 (2)** of [BBEHMOS20]: a black configuration in the bold labels satisfies the
black constraint of the white output problem of `Π₁` (some choice is a black configuration of
`Π₁`) iff it belongs to `X[AHTX]^{δ-1} | HT[AHTX]^{δ-2}`, the black constraint of FDSO(s). -/
theorem lemma_10_9_black (y : Fin δ → Lbl) : exChoice (B1 δ) (bold ∘ y) ↔ B0 (cfg y) := by
  constructor
  · rintro ⟨c, hc, h | h⟩
    · obtain ⟨i, hi⟩ := mem_cfg.mp (show A ∈ cfg c by simp [h])
      have := hc i
      rw [hi] at this
      exact Or.inl (mem_cfg.mpr ⟨i, by simpa using this⟩)
    · obtain ⟨i, hi⟩ := mem_cfg.mp (show H ∈ cfg c by simp [h])
      obtain ⟨j, hj⟩ := mem_cfg.mp (show T ∈ cfg c by simp [h])
      have hci := hc i
      have hcj := hc j
      rw [hi] at hci
      rw [hj] at hcj
      simp only [Function.comp, H_mem_bold, T_mem_bold] at hci hcj
      rcases hci with hci | hci
      · rcases hcj with hcj | hcj
        · exact Or.inr ⟨mem_cfg.mpr ⟨i, hci⟩, mem_cfg.mpr ⟨j, hcj⟩⟩
        · exact Or.inl (mem_cfg.mpr ⟨j, hcj⟩)
      · exact Or.inl (mem_cfg.mpr ⟨i, hci⟩)
  · rintro (h | ⟨hH, hT⟩)
    · obtain ⟨i, hi⟩ := mem_cfg.mp h
      refine ⟨Function.update (fun _ => X) i A, fun j => ?_, Or.inl (cfg_single i A X)⟩
      by_cases hj : j = i
      · subst hj; simp [hi]
      · simp [Function.update_of_ne hj]
    · obtain ⟨i, hi⟩ := mem_cfg.mp hH
      obtain ⟨j, hj⟩ := mem_cfg.mp hT
      have hij : i ≠ j := by
        rintro rfl
        rw [hi] at hj
        cases hj
      refine ⟨Function.update (Function.update (fun _ => X) i H) j T, fun l => ?_,
        Or.inr (cfg_pair hij (by decide) T)⟩
      by_cases hlj : l = j
      · subst hlj; simp [hj]
      · rw [Function.update_of_ne hlj]
        by_cases hli : l = i
        · subst hli; simp [hi]
        · simp [Function.update_of_ne hli]

end Lemma109

/-! ### FDSO(s) is a fixed point -/

/-- **FDSO(s) is a fixed point of round elimination** (§10.6 of [BBEHMOS20], Lemmas 10.8 and
10.9 together). For `0 < s < d` (and any black degree `δ`):

* the black output problem of FDSO(s) `= (W₀, B₀)` is `Π₁ = (W₁, B₁)` (Lemma 10.8): its maximal
  black configurations are exactly `B₁` and, on these labels, its white constraint is `W₁`;
* the white output problem of `Π₁` is FDSO(s) again (Lemma 10.9): its maximal white configurations
  are exactly `W₀` and, on these labels, its black constraint is `B₀`.

In both steps the labels of the output problem are identified with `Lbl` by the renaming `bold`. -/
theorem fdso_fixedPoint {d s δ : ℕ} (hs : 0 < s) (hsd : s < d) :
    ((∀ Y : Fin δ → Set Lbl,
        IsMaximal (allChoices B0) Y ↔ ∃ y : Fin δ → Lbl, B1 δ (cfg y) ∧ Y = bold ∘ y) ∧
      ∀ y : Fin d → Lbl, exChoice (W0 d s) (bold ∘ y) ↔ W1 d s (cfg y)) ∧
    ((∀ Y : Fin d → Set Lbl,
        IsMaximal (allChoices (W1 d s)) Y ↔ ∃ y : Fin d → Lbl, W0 d s (cfg y) ∧ Y = bold ∘ y) ∧
      ∀ y : Fin δ → Lbl, exChoice (B1 δ) (bold ∘ y) ↔ B0 (cfg y)) :=
  ⟨⟨lemma_10_8_black, lemma_10_8_white hsd.le⟩,
    ⟨lemma_10_9_white hs hsd, lemma_10_9_black⟩⟩

end Podc.BinaryLabeling.RoundElim
