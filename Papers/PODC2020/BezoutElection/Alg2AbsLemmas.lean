import Papers.PODC2020.BezoutElection.Alg2Abs

/-!
# Algorithm 2, per-register abstraction: helper lemmas
-/

set_option linter.unusedSectionVars false

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P]

/-! ### Counting identifiers -/

section Count

variable [Fintype P] {ids : P → Id} {n : ℕ}

lemma card_le_of_ne (hn : Fintype.card P = n) (D : Finset Id) (ℓ : P)
    (hD : ∀ a ∈ D, ∃ j, ids j = a ∧ j ≠ ℓ) : D.card ≤ n - 1 := by
  have hsub : D ⊆ (Finset.univ.erase ℓ).image ids := by
    intro a ha
    obtain ⟨j, rfl, hj⟩ := hD a ha
    exact Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩
  calc D.card ≤ ((Finset.univ.erase ℓ).image ids).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.erase ℓ).card := Finset.card_image_le
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hn]

lemma mem_of_card_eq_of_ne (hid : Function.Injective ids) (hn : Fintype.card P = n)
    (D : Finset Id) (ℓ : P) (hD : ∀ a ∈ D, ∃ j, ids j = a ∧ j ≠ ℓ) (hc : D.card = n - 1)
    (j : P) (hj : j ≠ ℓ) : ids j ∈ D := by
  have hsub : D ⊆ (Finset.univ.erase ℓ).image ids := by
    intro a ha
    obtain ⟨j, rfl, hj⟩ := hD a ha
    exact Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩
  have hcard : ((Finset.univ.erase ℓ).image ids).card ≤ D.card := by
    rw [Finset.card_image_of_injective _ hid, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hn, hc]
  rw [Finset.eq_of_subset_of_card_le hsub hcard]
  exact Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩

/-- A set of `n - 1` identifiers satisfying `Q`, where `Q (ids p)` fails, contains every
other identifier. -/
lemma all_of_card (hid : Function.Injective ids) (hn : Fintype.card P = n)
    (D : Finset Id) (Q : P → Prop) (p : P) (hD : ∀ a ∈ D, ∃ i, ids i = a ∧ Q i) (hp : ¬Q p)
    (hc : D.card = n - 1) (j : P) (hj : j ≠ p) : ids j ∈ D ∧ Q j := by
  have hD' : ∀ a ∈ D, ∃ i, ids i = a ∧ i ≠ p := by
    intro a ha
    obtain ⟨i, rfl, hi⟩ := hD a ha
    exact ⟨i, rfl, by rintro rfl; exact hp hi⟩
  have hm := mem_of_card_eq_of_ne hid hn D p hD' hc j hj
  obtain ⟨i, hi, hq⟩ := hD _ hm
  rw [hid hi] at hq
  exact ⟨hm, hq⟩

end Count

/-! ### Updating one process -/

namespace AState

/-- Replace the local state of `p`. -/
def upd (A : AState Id P) (p : P) (l : ALoc Id) : AState Id P := ⟨A.reg, Function.update A.loc p l⟩

@[simp] lemma upd_reg (A : AState Id P) (p : P) (l : ALoc Id) : (A.upd p l).reg = A.reg := rfl
@[simp] lemma upd_loc_self (A : AState Id P) (p : P) (l : ALoc Id) : (A.upd p l).loc p = l := by
  simp [upd]
lemma upd_loc_ne (A : AState Id P) {p j : P} (l : ALoc Id) (h : j ≠ p) :
    (A.upd p l).loc j = A.loc j := by
  simp [upd, Function.update_of_ne h]

/-- Replace the status of `p`. -/
def setSt (A : AState Id P) (p : P) (s : AStatus Id) : AState Id P := A.upd p { A.loc p with st := s }

@[simp] lemma setSt_reg (A : AState Id P) (p : P) (s : AStatus Id) : (A.setSt p s).reg = A.reg := rfl
@[simp] lemma setSt_ph (A : AState Id P) (p j : P) (s : AStatus Id) :
    ((A.setSt p s).loc j).ph = (A.loc j).ph := by
  by_cases h : j = p
  · subst h; simp [setSt]
  · simp [setSt, upd_loc_ne _ _ h]
@[simp] lemma setSt_D (A : AState Id P) (p j : P) (s : AStatus Id) :
    ((A.setSt p s).loc j).D = (A.loc j).D := by
  by_cases h : j = p
  · subst h; simp [setSt]
  · simp [setSt, upd_loc_ne _ _ h]
@[simp] lemma setSt_lo (A : AState Id P) (p j : P) (s : AStatus Id) :
    ((A.setSt p s).loc j).lo = (A.loc j).lo := by
  by_cases h : j = p
  · subst h; simp [setSt]
  · simp [setSt, upd_loc_ne _ _ h]
@[simp] lemma setSt_lv (A : AState Id P) (p j : P) (s : AStatus Id) :
    ((A.setSt p s).loc j).lv = (A.loc j).lv := by
  by_cases h : j = p
  · subst h; simp [setSt]
  · simp [setSt, upd_loc_ne _ _ h]
@[simp] lemma setSt_ca (A : AState Id P) (p j : P) (s : AStatus Id) :
    ((A.setSt p s).loc j).ca = (A.loc j).ca := by
  by_cases h : j = p
  · subst h; simp [setSt]
  · simp [setSt, upd_loc_ne _ _ h]
@[simp] lemma setSt_st_self (A : AState Id P) (p : P) (s : AStatus Id) :
    ((A.setSt p s).loc p).st = s := by simp [setSt]
lemma setSt_st_ne (A : AState Id P) {p j : P} (s : AStatus Id) (h : j ≠ p) :
    ((A.setSt p s).loc j).st = (A.loc j).st := by simp [setSt, upd_loc_ne _ _ h]

variable {ids : P → Id}

lemma val_upd {A : AState Id P} {p : P} {l : ALoc Id} {u : Reg Id} (h : (A.upd p l).Val u) :
    A.Val u ∨ (l.st = .pend u ∧ u.level = A.reg.level) ∨
      (l.st = .copy u ∧ u.level = A.reg.level ∧ l.lv = A.reg.level) := by
  rcases h with h | ⟨j, h1, h2⟩ | ⟨j, h1, h2, h3⟩
  · exact Or.inl (Or.inl h)
  · by_cases hj : j = p
    · subst hj; simp at h1; exact Or.inr (Or.inl ⟨h1, h2⟩)
    · rw [upd_loc_ne _ _ hj] at h1; exact Or.inl (Or.inr (Or.inl ⟨j, h1, h2⟩))
  · by_cases hj : j = p
    · subst hj; simp at h1 h3; exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
    · rw [upd_loc_ne _ _ hj] at h1 h3
      exact Or.inl (Or.inr (Or.inr ⟨j, h1, h2, h3⟩))

lemma actLoser_upd {A : AState Id P} {p : P} {l : ALoc Id} {a : Id} (h : A.ActLoser ids a)
    (hp : (A.loc p).lv = A.reg.level → (A.loc p).lo = true → l.lv = A.reg.level ∧ l.lo = true) :
    (A.upd p l).ActLoser ids a := by
  obtain ⟨i, h1, h2, h3⟩ := h
  refine ⟨i, h1, ?_⟩
  by_cases hi : i = p
  · subst hi; simpa using hp h2 h3
  · rw [upd_loc_ne _ _ hi]; exact ⟨h2, h3⟩

lemma quiet_upd {A : AState Id P} {p ℓ j : P} {l : ALoc Id} (hj : j ≠ p) :
    (A.upd p l).Quiet ids ℓ j ↔ A.Quiet ids ℓ j := by
  simp only [Quiet, upd_reg, upd_loc_ne _ _ hj]

lemma threat_upd {A : AState Id P} {p j : P} {l : ALoc Id} (hj : j ≠ p) :
    (A.upd p l).Threat ids j ↔ A.Threat ids j := by
  simp only [Threat, upd_reg, upd_loc_ne _ _ hj]

end AState

/-! ### Outcomes of `procX` -/

section Proc

variable {n U : ℕ} {me : Id} {l : ALoc Id} {r : Reg Id} {ok fin : Bool}

lemma procX_lvup (h1 : ¬(r.level = l.lv ∧ r.level < U)) (h2 : l.lv < r.level) :
    procX n U me l r ok fin = ({ l with ph := .electing, D := ∅, lo := false, lv := l.lv + 1 }, none) := by
  unfold procX; simp only [h1, h2, ↓reduceIte]

lemma procX_skip (h1 : ¬(r.level = l.lv ∧ r.level < U)) (h2 : ¬l.lv < r.level) :
    procX n U me l r ok fin = (l, none) := by
  unfold procX; simp only [h1, h2, ↓reduceIte]

end Proc

end BezoutElection.Alg2
