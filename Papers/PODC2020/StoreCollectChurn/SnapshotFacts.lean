import Papers.PODC2020.StoreCollectChurn.SnapshotPos

/-!
# What collects return: update sequence numbers (Lemma 11 / Lemma 13 ingredients)

`usq (W r)` is the update sequence number of `r`'s entry in a store-collect view (`0` if absent).
For collects `C₁` returning before `C₂` is invoked, `usq ∘ C₁ ≤ usq ∘ C₂` pointwise
(`usq_le_of_before`); a store completed before a collect is invoked is reflected in it
(`usq_ge_of_storeDone`).
-/

namespace Podc.StoreCollectChurn.Snap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P] {E : List (Ev P V)} {pk : Pick P V}

/-- Update sequence number of an entry (`0` if absent). -/
def usq : Option (SCVal P V) → ℕ
  | none => 0
  | some x => x.usqno

lemma fIdx_le_length {α β : Type} (f : α → Option β) (l : List α) (i : ℕ) :
    fIdx f l i ≤ (l.filterMap f).length := by
  unfold fIdx
  exact ((List.take_sublist i l).filterMap f).length_le

lemma val_eq_none_iff (hpast : Past E E.length) {a : ℕ} {r : P} {y : SCVal P V}
    (ha : StE E a r y) : y.val = none ↔ y.usqno = 0 := by
  have haL : a < E.length := by
    by_contra h; rw [StE, List.getElem?_eq_none (by omega)] at ha; cases ha
  have hf := hpast.1 a haL r y ha
  rw [hf.ok.1]
  have h1 := hf.le_cnt
  have h2 := fIdx_le_length (updOf r) E a
  unfold valOf
  split_ifs with h0
  · simp [h0]
  · simp only [h0, iff_false]
    rw [List.getElem?_eq_getElem (by unfold updArgs; unfold updCnt at h1; omega)]
    simp

variable (hrun : run pk E ≠ none) (hreg : Regular (scSched E))
include hrun hreg

lemma past : Past E E.length := past_of_run pk hreg hrun

lemma rU_eq (hpast : Past E E.length) {i j : ℕ} {q : P} {W : SCView P V} (hc : ColE E i j q W)
    (r : P) : rU W r = if usq (W r) = 0 then none else some (usq (W r)) := by
  unfold rU
  rcases hW : W r with _ | y
  · simp [usq]
  · obtain ⟨a, -, ha, -⟩ := reg1_some hreg hc hW
    have := val_eq_none_iff hpast ha
    simp only [Option.bind_some, usq]
    rcases hv : y.val with _ | v
    · simp [this.1 hv]
    · have : y.usqno ≠ 0 := fun h0 => by rw [this.2 h0] at hv; cases hv
      simp [this]

/-- Equal `r(V).usqno` means equal update sequence numbers. -/
lemma usq_eq_of_rU {i₁ j₁ i₂ j₂ : ℕ} {q₁ q₂ : P} {W₁ W₂ : SCView P V}
    (h₁ : ColE E i₁ j₁ q₁ W₁) (h₂ : ColE E i₂ j₂ q₂ W₂) (h : ∀ r, rU W₁ r = rU W₂ r) (r : P) :
    usq (W₁ r) = usq (W₂ r) := by
  have hp := past hrun hreg
  have := h r
  rw [rU_eq hrun hreg hp h₁, rU_eq hrun hreg hp h₂] at this
  split_ifs at this with ha hb hb <;> simp_all

/-- The next store-collect event of a node after position `a` exists if some later one does. -/
lemma exists_nextE {a k : ℕ} {e e' : SCEv P (SCVal P V)} (ha : E[a]? = some (.sc e))
    (hk : E[k]? = some (.sc e')) (hp : e'.proc = e.proc) (hak : a < k) :
    ∃ b, b ≤ k ∧ NextE E a b := by
  classical
  have hex : ∃ c, a < c ∧ ∃ e'', E[c]? = some (.sc e'') ∧ e''.proc = e.proc := ⟨k, hak, e', hk, hp⟩
  obtain ⟨hc1, e'', hc2, hc3⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, Nat.find_min' hex ⟨hak, e', hk, hp⟩, hc1, e, e'', ha, hc2, hc3, ?_⟩
  intro m hm1 hm2 f hf hfp
  exact Nat.find_min hex hm2 ⟨hm1, f, hf, hfp⟩

/-- Two stores of a node: the earlier one completes before the later one is invoked. -/
lemma store_done_before {a a' : ℕ} {r : P} {x x' : SCVal P V} (ha : StE E a r x)
    (ha' : StE E a' r x') (hlt : a < a') : ∃ b, NextE E a b ∧ b < a' := by
  obtain ⟨b, hb, hn⟩ := exists_nextE hrun hreg ha ha' rfl hlt
  refine ⟨b, hn, lt_of_le_of_ne hb fun h => ?_⟩
  subst h
  have := next_of_store hrun ha hn
  rw [StE] at ha'; rw [ha'] at this; cases this

/-- Collects are monotone in update sequence numbers (from regularity (2)). -/
lemma usq_le_of_before {i₁ j₁ i₂ j₂ : ℕ} {q₁ q₂ : P} {W₁ W₂ : SCView P V}
    (h₁ : ColE E i₁ j₁ q₁ W₁) (h₂ : ColE E i₂ j₂ q₂ W₂) (hlt : j₁ < i₂) (r : P) :
    usq (W₁ r) ≤ usq (W₂ r) := by
  have hp := past hrun hreg
  rcases hW : W₁ r with _ | x₁
  · simp [usq]
  obtain ⟨x₂, hx₂, hor⟩ := reg2 hreg h₁ h₂ hlt r x₁ hW
  rw [hx₂]
  simp only [usq]
  rcases hor with rfl | hn
  · exact le_rfl
  obtain ⟨a₁, -, ha₁, -⟩ := reg1_some hreg h₁ hW
  obtain ⟨a₂, -, ha₂, -⟩ := reg1_some hreg h₂ hx₂
  rcases lt_trichotomy a₁ a₂ with h | rfl | h
  · have ha₂L : a₂ < E.length := by
      by_contra h'; rw [StE, List.getElem?_eq_none (by omega)] at ha₂; cases ha₂
    exact (hp.1 a₂ ha₂L r x₂ ha₂).mono a₁ h x₁ ha₁
  · rw [StE] at ha₁ ha₂; rw [ha₁] at ha₂; cases ha₂; exact le_rfl
  · obtain ⟨b, hb, hba⟩ := store_done_before hrun hreg ha₂ ha₁ h
    exact absurd ⟨a₂, b, a₁, ha₂, hb, hba, ha₁⟩ hn

/-- A store completed before a collect is invoked is reflected in the collected view. -/
lemma usq_ge_of_storeDone {a b i j : ℕ} {p q : P} {x : SCVal P V} {W : SCView P V}
    (ha : StE E a p x) (hab : NextE E a b) (hbi : b < i) (hc : ColE E i j q W) :
    x.usqno ≤ usq (W p) := by
  have hp := past hrun hreg
  rcases hW : W p with _ | y
  · exact absurd ⟨a, b, ⟨⟨x, ha⟩, hab⟩, hbi⟩ (reg1_none hreg hc hW)
  obtain ⟨a', -, ha', hno⟩ := reg1_some hreg hc hW
  simp only [usq]
  rcases lt_trichotomy a a' with h | rfl | h
  · have ha'L : a' < E.length := by
      by_contra h'; rw [StE, List.getElem?_eq_none (by omega)] at ha'; cases ha'
    exact (hp.1 a' ha'L p y ha').mono a h x ha
  · rw [StE] at ha ha'; rw [ha] at ha'; cases ha'; exact le_rfl
  · exact absurd ⟨a, b, h, ⟨⟨x, ha⟩, hab⟩, hbi⟩ hno

/-- An entry of a collected view was stored before the collect returned, and its usqno is at
most the number of updates its node invoked by then. -/
lemma usq_le_updCnt {i j : ℕ} {q p : P} {W : SCView P V} (hc : ColE E i j q W) :
    ∃ a, a < j ∧ usq (W p) ≤ updCnt E a p := by
  have hp := past hrun hreg
  rcases hW : W p with _ | y
  · exact ⟨0, by have := hc.2.2.1; omega, by simp [usq]⟩
  obtain ⟨a, haj, ha, -⟩ := reg1_some hreg hc hW
  have haL : a < E.length := by
    by_contra h'; rw [StE, List.getElem?_eq_none (by omega)] at ha; cases ha
  exact ⟨a, haj, (hp.1 a haL p y ha).le_cnt⟩

/-- The real value of an entry is the argument of the corresponding update. -/
lemma rVal_eq_valOf {i j : ℕ} {q : P} {W : SCView P V} (hc : ColE E i j q W) (r : P) :
    rVal W r = valOf E r (usq (W r)) := by
  have hp := past hrun hreg
  unfold rVal
  rcases hW : W r with _ | y
  · simp [usq, valOf]
  obtain ⟨a, -, ha, -⟩ := reg1_some hreg hc hW
  have haL : a < E.length := by
    by_contra h'; rw [StE, List.getElem?_eq_none (by omega)] at ha; cases ha
  simp only [Option.bind_some, usq]
  exact (hp.1 a haL r y ha).ok.1

end Podc.StoreCollectChurn.Snap
