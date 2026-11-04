import Papers.PODC2013.TMObservationalRefinement.Basic

/-!
# The opacity relation (Definition 4)

`Opac H S` is Definition 4 verbatim: a bijection `θ` between the positions of `H` and `S`
preserving actions, per-thread order and real-time order (`committed`/`aborted` before `txbegin`).

Main facts:
* `opac_nil_left`: `Opac [] S ↔ S = []`;
* `opac_cons_iff`: `Opac H (ψ :: S)` iff `H = A ++ ψ :: B` where no action of `A` must precede
  `ψ` (`¬ Constrained a ψ`) and `Opac (A ++ B) S`.
These two give an inductive description of the relation, used in the rearrangement lemma and in
the necessity proof.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.TMObservationalRefinement

open IKind

variable {T O M : Type}

/-- `Constrained a b` (for `a` before `b`): `a` and `b` are in per-thread order (same thread) or in
real-time order (`a` is `committed`/`aborted`, `b` is `txbegin`). -/
def Constrained (a b : IAct T O M) : Prop :=
  a.1 = b.1 ∨ (a.2.isEnd = true ∧ b.2 = txbegin)

/-- **Definition 4** (opacity relation between histories), `H ⊑ S`. -/
def Opac (H S : List (IAct T O M)) : Prop :=
  ∃ θ : Fin H.length ≃ Fin S.length, (∀ i, H[i] = S[θ i]) ∧
    ∀ i j : Fin H.length, i < j → Constrained H[i] H[j] → θ i < θ j

/-- A cast-free description of a witness of `Opac` with natural-number indices. -/
structure OpacWit (H S : List (IAct T O M)) (θ σ : ℕ → ℕ) : Prop where
  lt : ∀ i < H.length, θ i < S.length
  get : ∀ i (h : i < H.length) (h' : θ i < S.length), H[i] = S[θ i]
  left : ∀ i < H.length, σ (θ i) = i
  lt' : ∀ j < S.length, σ j < H.length
  right : ∀ j < S.length, θ (σ j) = j
  order : ∀ i j (hij : i < j) (hj : j < H.length),
    Constrained (H[i]'(lt_trans hij hj)) H[j] → θ i < θ j

lemma opac_iff_wit (H S : List (IAct T O M)) : Opac H S ↔ ∃ θ σ, OpacWit H S θ σ := by
  constructor
  · rintro ⟨θ, hget, hord⟩
    refine ⟨fun i => if h : i < H.length then θ ⟨i, h⟩ else 0,
      fun j => if h : j < S.length then θ.symm ⟨j, h⟩ else 0, ?_⟩
    constructor
    · intro i hi; simp [hi]
    · intro i hi h'; simp only [hi, dite_true]; exact hget ⟨i, hi⟩
    · intro i hi; simp [hi]
    · intro j hj; simp [hj]
    · intro j hj; simp [hj]
    · intro i j hij hj hc
      simp only [hj, lt_trans hij hj, dite_true]
      exact hord ⟨i, _⟩ ⟨j, hj⟩ hij hc
  · rintro ⟨θ, σ, w⟩
    refine ⟨⟨fun i => ⟨θ i, w.lt i i.2⟩, fun j => ⟨σ j, w.lt' j j.2⟩,
      fun i => Fin.ext (w.left i i.2), fun j => Fin.ext (w.right j j.2)⟩, ?_, ?_⟩
    · intro i; exact w.get i i.2 _
    · intro i j hij hc; exact w.order i j hij j.2 hc

lemma opac_nil_left (S : List (IAct T O M)) : Opac [] S ↔ S = [] := by
  rw [opac_iff_wit]
  constructor
  · rintro ⟨θ, σ, w⟩
    rcases S with _ | ⟨a, S⟩
    · rfl
    · exact absurd (w.lt' 0 (by simp)) (by simp)
  · rintro rfl
    exact ⟨id, id, fun i h => by simp at h, fun i h => by simp at h, fun i h => by simp at h,
      fun j h => by simp at h, fun j h => by simp at h, fun i j _ h => by simp at h⟩

section mid
variable (A B : List (IAct T O M)) (ψ : IAct T O M)

private lemma get_mid_left (i : ℕ) (h : i < A.length) :
    (A ++ ψ :: B)[i]'(by simp; omega) = (A ++ B)[i]'(by simp; omega) := by
  rw [List.getElem_append_left h, List.getElem_append_left h]

private lemma get_mid (h : A.length < (A ++ ψ :: B).length) : (A ++ ψ :: B)[A.length] = ψ := by
  simp

private lemma get_mid_right (i : ℕ) (h1 : A.length ≤ i) (h2 : i < (A ++ B).length) :
    (A ++ ψ :: B)[i + 1]'(by simp at h2 ⊢; omega) = (A ++ B)[i] := by
  rw [List.getElem_append_right (by omega), List.getElem_append_right h1]
  simp only [show i + 1 - A.length = (i - A.length) + 1 by omega, List.getElem_cons_succ]

end mid

/-- Inserting a matching first action: the "if" direction of `opac_cons_iff`. -/
lemma Opac.cons_intro {A B S : List (IAct T O M)} {ψ : IAct T O M}
    (hA : ∀ a ∈ A, ¬ Constrained a ψ) (h : Opac (A ++ B) S) : Opac (A ++ ψ :: B) (ψ :: S) := by
  rw [opac_iff_wit] at h ⊢
  obtain ⟨θ, σ, w⟩ := h
  have hlen : (A ++ ψ :: B).length = (A ++ B).length + 1 := by simp; omega
  have hlenAB : (A ++ B).length = A.length + B.length := by simp
  let θ' : ℕ → ℕ := fun i =>
    if i < A.length then θ i + 1 else if i = A.length then 0 else θ (i - 1) + 1
  have key : ∀ k (hk : k < (A ++ ψ :: B).length), k ≠ A.length →
      ∃ k', ∃ hk' : k' < (A ++ B).length, (A ++ ψ :: B)[k] = (A ++ B)[k'] ∧
        θ' k = θ k' + 1 ∧ (k < A.length → k' = k) ∧ (A.length < k → k' = k - 1) := by
    intro k hk hkn
    by_cases hkl : k < A.length
    · exact ⟨k, by omega, get_mid_left A B ψ k hkl, by simp [θ', hkl], fun _ => rfl,
        fun h => by omega⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      refine ⟨k', by omega, get_mid_right A B ψ k' (by omega) (by omega), by simp [θ', hkl, hkn],
        fun h => by omega, fun _ => by omega⟩
  refine ⟨θ', fun j => if j = 0 then A.length else
    if σ (j - 1) < A.length then σ (j - 1) else σ (j - 1) + 1, ?_⟩
  constructor
  · intro i hi
    simp only [List.length_cons, θ']
    split_ifs with h1 h2
    · have := w.lt i (by omega); omega
    · omega
    · have := w.lt (i - 1) (by omega); omega
  · intro i hi h'
    by_cases hin : i = A.length
    · subst hin; simp [θ']
    · obtain ⟨i', hi', e, t, -, -⟩ := key i hi hin
      simp only [t, List.getElem_cons_succ, e]
      exact w.get i' hi' _
  · intro i hi
    by_cases h1 : i < A.length
    · simp [θ', h1, w.left i (by omega)]
    by_cases h2 : i = A.length
    · simp [θ', h2]
    · have := w.left (i - 1) (by omega)
      simp only [θ']
      rw [if_neg h1, if_neg h2, if_neg (by omega), Nat.add_sub_cancel, this, if_neg (by omega)]
      omega
  · intro j hj
    simp only [List.length_cons] at hj
    split_ifs with h1 h2
    · omega
    · have := w.lt' (j - 1) (by omega); omega
    · have := w.lt' (j - 1) (by omega); omega
  · intro j hj
    simp only [List.length_cons] at hj
    by_cases h0 : j = 0
    · simp [θ', h0]
    have hl := w.lt' (j - 1) (by omega)
    have hr := w.right (j - 1) (by omega)
    rw [if_neg h0]
    by_cases h1 : σ (j - 1) < A.length
    · rw [if_pos h1]; simp only [θ', if_pos h1, hr]; omega
    · rw [if_neg h1]
      simp only [θ']
      rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel, hr]; omega
  · intro i j hij hj hc
    by_cases hjn : j = A.length
    · subst hjn
      rw [get_mid] at hc
      exact absurd hc (hA _ (by rw [List.getElem_append_left hij]; exact List.getElem_mem _))
    by_cases hin : i = A.length
    · subst hin; simp only [θ', lt_irrefl, if_false, if_true]
      split_ifs <;> omega
    obtain ⟨i', hi', ei, ti, hi1, hi2⟩ := key i (by omega) hin
    obtain ⟨j', hj', ej, tj, hj1, hj2⟩ := key j hj hjn
    rw [ti, tj]
    have hij' : i' < j' := by
      rcases Nat.lt_or_gt_of_ne hin with h | h <;> rcases Nat.lt_or_gt_of_ne hjn with h' | h'
      · rw [hi1 h, hj1 h']; exact hij
      · rw [hi1 h, hj2 h']; omega
      · omega
      · rw [hi2 h, hj2 h']; omega
    have := w.order i' j' hij' hj' (by rw [← ei, ← ej]; exact hc)
    omega

/-- Removing the first action of `S`: the "only if" direction of `opac_cons_iff`. -/
lemma Opac.cons_elim {H S : List (IAct T O M)} {ψ : IAct T O M} (h : Opac H (ψ :: S)) :
    ∃ A B, H = A ++ ψ :: B ∧ (∀ a ∈ A, ¬ Constrained a ψ) ∧ Opac (A ++ B) S := by
  rw [opac_iff_wit] at h
  obtain ⟨θ, σ, w⟩ := h
  set k := σ 0 with hk
  have hkH : k < H.length := w.lt' 0 (by simp)
  have hθk : θ k = 0 := w.right 0 (by simp)
  have hHk : H[k] = ψ := by
    have := w.get k hkH (by rw [hθk]; simp); simpa [hθk] using this
  refine ⟨H.take k, H.drop (k + 1), ?_, ?_, ?_⟩
  · conv_lhs => rw [← List.take_append_drop k H]
    congr 1
    rw [List.drop_eq_getElem_cons hkH, hHk]
  · intro a ha hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    simp only [List.length_take] at hi
    have hi' : i < k := by omega
    rw [List.getElem_take] at hc
    have := w.order i k hi' hkH (by rw [hHk]; exact hc)
    omega
  · -- positions of `A ++ B` correspond to positions `≠ k` of `H`
    have hHe : H = H.take k ++ ψ :: H.drop (k + 1) := by
      conv_lhs => rw [← List.take_append_drop k H]
      congr 1; rw [List.drop_eq_getElem_cons hkH, hHk]
    set A := H.take k
    set B := H.drop (k + 1)
    have hA : A.length = k := by simp [A]; omega
    have hlenH : H.length = (A ++ B).length + 1 := by
      conv_lhs => rw [hHe]
      simp; omega
    rw [opac_iff_wit]
    have hne : ∀ i < H.length, i ≠ k → θ i ≠ 0 := by
      intro i hi hik h0; apply hik; rw [← w.left i hi, h0]
    let adj : ℕ → ℕ := fun i => if i < k then i else i + 1
    have hadj : ∀ i (hi : i < (A ++ B).length), ∃ h : adj i < H.length, (A ++ B)[i] = H[adj i] := by
      intro i hi
      refine ⟨by simp only [adj]; split_ifs <;> omega, ?_⟩
      have e1 : ∀ (h : adj i < H.length), H[adj i] = (A ++ ψ :: B)[adj i]'(by
          rw [← hHe]; exact h) := by
        intro h; congr 1
      rw [e1]
      simp only [adj]
      split_ifs with h1
      · rw [get_mid_left A B ψ i (by omega)]
      · rw [get_mid_right A B ψ i (by omega) hi]
    refine ⟨fun i => θ (adj i) - 1, fun j => if σ (j + 1) < k then σ (j + 1) else σ (j + 1) - 1, ?_⟩
    constructor
    · intro i hi
      obtain ⟨h, -⟩ := hadj i hi
      have h1 := w.lt _ h
      have h2 := hne _ h (by simp only [adj]; split_ifs <;> omega)
      simp only [List.length_cons] at h1; omega
    · intro i hi h'
      obtain ⟨h, e⟩ := hadj i hi
      rw [e, w.get _ h (by have := w.lt _ h; omega)]
      have h2 := hne _ h (by simp only [adj]; split_ifs <;> omega)
      obtain ⟨m, hm⟩ : ∃ m, θ (adj i) = m + 1 := ⟨θ (adj i) - 1, by omega⟩
      simp only [hm, List.getElem_cons_succ, Nat.add_sub_cancel]
    · intro i hi
      obtain ⟨h, -⟩ := hadj i hi
      have h2 := hne _ h (by simp only [adj]; split_ifs <;> omega)
      have hl := w.left _ h
      rw [show θ (adj i) - 1 + 1 = θ (adj i) by omega, hl]
      simp only [adj]; split_ifs <;> omega
    · intro j hj
      have := w.lt' (j + 1) (by simp; omega)
      have hσ : σ (j + 1) ≠ k := by
        intro he; have := w.right (j + 1) (by simp; omega); rw [he, hθk] at this; omega
      split_ifs <;> omega
    · intro j hj
      have hlt := w.lt' (j + 1) (by simp; omega)
      have hσ : σ (j + 1) ≠ k := by
        intro he; have := w.right (j + 1) (by simp; omega); rw [he, hθk] at this; omega
      have hr := w.right (j + 1) (by simp; omega)
      simp only [adj]
      by_cases h1 : σ (j + 1) < k
      · simp only [h1, if_true]; omega
      · rw [if_neg h1, if_neg (by omega), Nat.sub_add_cancel (by omega)]; omega
    · intro i j hij hj hc
      obtain ⟨hi', ei⟩ := hadj i (by omega)
      obtain ⟨hj', ej⟩ := hadj j hj
      have hadjlt : adj i < adj j := by simp only [adj]; split_ifs <;> omega
      have := w.order (adj i) (adj j) hadjlt hj' (by rw [← ei, ← ej]; exact hc)
      have h2 := hne _ hi' (by simp only [adj]; split_ifs <;> omega)
      omega

/-- **Inductive description of Definition 4.** -/
theorem opac_cons_iff (H S : List (IAct T O M)) (ψ : IAct T O M) :
    Opac H (ψ :: S) ↔
      ∃ A B, H = A ++ ψ :: B ∧ (∀ a ∈ A, ¬ Constrained a ψ) ∧ Opac (A ++ B) S := by
  constructor
  · exact Opac.cons_elim
  · rintro ⟨A, B, rfl, hA, h⟩; exact h.cons_intro hA

end Podc.TMObservationalRefinement
