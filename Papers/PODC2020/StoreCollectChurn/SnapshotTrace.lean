import Papers.PODC2020.StoreCollectChurn.SnapshotModel

/-!
# Positions in an execution of Algorithm 7

The regularity hypothesis is about the store-collect schedule `scSched E = E.filterMap scOf`,
whose positions differ from those of `E`.  This file restates the consequences of `Regular` that
the linearizability proof uses directly in positions of `E`.
-/

namespace Podc.StoreCollectChurn.Snap

variable {P V : Type}

/-! ## Generic facts about `filterMap` positions -/

section FilterMap

variable {α β : Type} (f : α → Option β)

/-- Index in `l.filterMap f` of the element at position `i` of `l`. -/
def fIdx (l : List α) (i : ℕ) : ℕ := ((l.take i).filterMap f).length

lemma fIdx_mono {l : List α} {i j : ℕ} (h : i ≤ j) : fIdx f l i ≤ fIdx f l j := by
  unfold fIdx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← List.take_append_drop i (l.take (i + k)), List.take_take, min_eq_left (by omega),
    List.filterMap_append, List.length_append]
  omega

lemma getElem?_filterMap_fIdx {l : List α} {i : ℕ} {a : α} {b : β} (h : l[i]? = some a)
    (hf : f a = some b) : (l.filterMap f)[fIdx f l i]? = some b := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [fIdx, List.filterMap_cons, hf]
    · simp only [List.getElem?_cons_succ] at h
      have := ih h
      rcases hx : f x with _ | c
      · simpa [fIdx, List.filterMap_cons, hx] using this
      · simpa [fIdx, List.filterMap_cons, hx] using this

lemma fIdx_lt {l : List α} {i j : ℕ} {a : α} {b : β} (h : l[i]? = some a) (hf : f a = some b)
    (hij : i < j) : fIdx f l i < fIdx f l j := by
  have hi : i < l.length := by
    rcases Nat.lt_or_ge i l.length with h' | h'
    · exact h'
    · simp [List.getElem?_eq_none h'] at h
  have h1 : fIdx f l (i + 1) = fIdx f l i + 1 := by
    unfold fIdx
    rw [List.take_add_one, List.filterMap_append, List.length_append, h]
    simp [hf]
  have := fIdx_mono f (l := l) (show i + 1 ≤ j by omega)
  omega

lemma exists_of_getElem?_filterMap {l : List α} {k : ℕ} {b : β}
    (h : (l.filterMap f)[k]? = some b) :
    ∃ i a, l[i]? = some a ∧ f a = some b ∧ fIdx f l i = k := by
  induction l generalizing k with
  | nil => simp at h
  | cons x l ih =>
    rcases hx : f x with _ | c
    · rw [List.filterMap_cons, hx] at h
      obtain ⟨i, a, h1, h2, h3⟩ := ih h
      refine ⟨i + 1, a, by simpa using h1, h2, ?_⟩
      simp only [fIdx, List.take_succ_cons, List.filterMap_cons, hx] at h3 ⊢
      exact h3
    · rw [List.filterMap_cons, hx] at h
      rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        exact ⟨0, x, by simp, by rw [hx, h], by simp [fIdx]⟩
      · simp only [List.getElem?_cons_succ] at h
        obtain ⟨i, a, h1, h2, h3⟩ := ih h
        refine ⟨i + 1, a, by simpa using h1, h2, ?_⟩
        simp only [fIdx, List.take_succ_cons, List.filterMap_cons, hx, List.length_cons] at h3 ⊢
        omega

end FilterMap

/-! ## Store-collect events at positions of `E` -/

variable (E : List (Ev P V))

/-- `STORE_p(x)` is invoked at position `a` of `E`. -/
def StE (a : ℕ) (p : P) (x : SCVal P V) : Prop := E[a]? = some (.sc (.stInv p x))

/-- `b` is the next store-collect event of the node of the store-collect event at `a`. -/
def NextE (a b : ℕ) : Prop :=
  a < b ∧ ∃ e e', E[a]? = some (.sc e) ∧ E[b]? = some (.sc e') ∧ e'.proc = e.proc ∧
    ∀ k, a < k → k < b → ∀ e'', E[k]? = some (.sc e'') → e''.proc ≠ e.proc

/-- A collect by `p` invoked at `i` and returning `W` at `j`. -/
def ColE (i j : ℕ) (p : P) (W : SCView P V) : Prop :=
  E[i]? = some (.sc (.colInv p)) ∧ E[j]? = some (.sc (.ret p W)) ∧ NextE E i j

/-- A store by `p` invoked at `a` whose response is at `b`. -/
def StDoneE (a b : ℕ) (p : P) : Prop := (∃ x, StE E a p x) ∧ NextE E a b

variable {E}

local notation "ι" => fIdx Ev.scOf E

lemma sc_at {i : ℕ} {e : SCEv P (SCVal P V)} (h : E[i]? = some (.sc e)) :
    (scSched E)[ι i]? = some e :=
  getElem?_filterMap_fIdx Ev.scOf h rfl

lemma idx_lt {i j : ℕ} {e : SCEv P (SCVal P V)} (h : E[i]? = some (.sc e)) (hij : i < j) :
    ι i < ι j := fIdx_lt Ev.scOf h rfl hij

lemma nextE_next {a b : ℕ} (h : NextE E a b) : Next (scSched E) (ι a) (ι b) := by
  obtain ⟨hab, e, e', ha, hb, hp, hbt⟩ := h
  refine ⟨idx_lt ha hab, e, e', sc_at ha, sc_at hb, hp, ?_⟩
  intro k hk1 hk2 e'' hk
  obtain ⟨i, c, hi, hc, rfl⟩ := exists_of_getElem?_filterMap Ev.scOf hk
  cases c with
  | sc c =>
    simp only [Ev.scOf, Option.some.injEq] at hc
    subst hc
    have h1 : a < i := by
      by_contra h'
      have := fIdx_mono Ev.scOf (l := E) (show i ≤ a by omega)
      omega
    have h2 : i < b := by
      by_contra h'
      have := fIdx_mono Ev.scOf (l := E) (show b ≤ i by omega)
      omega
    exact hbt i h1 h2 _ hi
  | hinv => simp [Ev.scOf] at hc
  | hret => simp [Ev.scOf] at hc

lemma colE_op {i j : ℕ} {p : P} {W : SCView P V} (h : ColE E i j p W) :
    CollectOp (scSched E) (ι i) (ι j) W :=
  ⟨p, sc_at h.1, sc_at h.2.1, nextE_next h.2.2⟩

lemma stE_at {a : ℕ} {p : P} {x : SCVal P V} (h : StE E a p x) :
    StoreAt (scSched E) (ι a) p x := sc_at h

lemma stDone {a b : ℕ} {p : P} (h : StDoneE E a b p) : StoreDone (scSched E) (ι a) (ι b) p := by
  obtain ⟨⟨x, hx⟩, hn⟩ := h
  exact ⟨⟨x, stE_at hx⟩, nextE_next hn⟩

lemma stE_of_storeAt {k : ℕ} {p : P} {x : SCVal P V} (h : StoreAt (scSched E) k p x) :
    ∃ a, StE E a p x ∧ ι a = k := by
  obtain ⟨i, c, hi, hc, rfl⟩ := exists_of_getElem?_filterMap Ev.scOf h
  cases c with
  | sc c =>
    simp only [Ev.scOf, Option.some.injEq] at hc
    subst hc
    exact ⟨i, hi, rfl⟩
  | hinv => simp [Ev.scOf] at hc
  | hret => simp [Ev.scOf] at hc

lemma lt_of_idx_lt {a b : ℕ} (h : ι a < ι b) : a < b := by
  by_contra h'
  have := fIdx_mono Ev.scOf (l := E) (show b ≤ a by omega)
  omega

/-! ## Regularity in positions of `E` -/

/-- Regularity (1), first half, in positions of `E`. -/
lemma reg1_none (hreg : Regular (scSched E)) {i j : ℕ} {q p : P} {W : SCView P V}
    (hc : ColE E i j q W) (hW : W p = none) : ¬ ∃ a b, StDoneE E a b p ∧ b < i := by
  rintro ⟨a, b, hd, hb⟩
  obtain ⟨-, e, e', -, he', -⟩ := hd.2
  exact (hreg.1 _ _ _ (colE_op hc) p).1 hW ⟨ι a, ι b, stDone hd, idx_lt he' hb⟩

/-- Regularity (1), second half, in positions of `E`. -/
lemma reg1_some (hreg : Regular (scSched E)) {i j : ℕ} {q p : P} {W : SCView P V}
    {x : SCVal P V} (hc : ColE E i j q W) (hW : W p = some x) :
    ∃ a, a < j ∧ StE E a p x ∧ ¬ ∃ a' b', a < a' ∧ StDoneE E a' b' p ∧ b' < i := by
  obtain ⟨k, hk, hst, hno⟩ := (hreg.1 _ _ _ (colE_op hc) p).2 x hW
  obtain ⟨a, ha, rfl⟩ := stE_of_storeAt hst
  refine ⟨a, lt_of_idx_lt hk, ha, ?_⟩
  rintro ⟨a', b', h1, hd, h2⟩
  obtain ⟨-, e, e', -, he', -⟩ := hd.2
  exact hno ⟨ι a', ι b', idx_lt ha h1, stDone hd, idx_lt he' h2⟩

/-- Regularity (2) in positions of `E`. -/
lemma reg2 (hreg : Regular (scSched E)) {i₁ j₁ i₂ j₂ : ℕ} {q₁ q₂ : P} {W₁ W₂ : SCView P V}
    (h₁ : ColE E i₁ j₁ q₁ W₁) (h₂ : ColE E i₂ j₂ q₂ W₂) (hlt : j₁ < i₂) (p : P)
    (x₁ : SCVal P V) (hx : W₁ p = some x₁) : ∃ x₂, W₂ p = some x₂ ∧
      (x₁ = x₂ ∨ ¬ ∃ a b k, StE E a p x₂ ∧ NextE E a b ∧ b < k ∧ StE E k p x₁) := by
  obtain ⟨x₂, hx₂, h⟩ := hreg.2 _ _ _ _ _ _ (colE_op h₁) (colE_op h₂)
    (fIdx_lt Ev.scOf h₁.2.1 rfl hlt) p x₁ hx
  refine ⟨x₂, hx₂, h.imp_right fun hn => ?_⟩
  rintro ⟨a, b, k, ha, hab, hbk, hk⟩
  obtain ⟨-, e, e', -, he', -⟩ := id hab
  exact hn ⟨ι a, ι b, ι k, stE_at ha, nextE_next hab, idx_lt he' hbk, stE_at hk⟩

end Podc.StoreCollectChurn.Snap
