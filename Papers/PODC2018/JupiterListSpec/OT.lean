import Mathlib

/-!
# List operations and the OT functions of Figure A.1

Wei, Huang, Lu, *Specification and Implementation of Replicated List: The Jupiter Protocol
Revisited*, PODC 2018 (brief announcement); full version arXiv:1708.04754v4.

* `LOp E` — the operations `Ins(a, p, pr)`, `Del(a, p)`, `NOP` on lists of elements of `E`
  (Section 2.3 and Appendix A; the priority of a `Del` is irrelevant and omitted).
* `LOp.apply` — the paper's semantics: a position larger than the list size means
  "at the end" (Section 2.3).
* `xf o₁ o₂` — the first component of `OT(o₁, o₂)` of Figure A.1 (`o₁` transformed against `o₂`);
  the cases with `NOP` (not listed in Figure A.1) are the obvious ones.
* `Real o x l` — `x` is a transformed form of the original operation `o` that is *valid* at the
  list `l`: an insertion of the same element at a position `≤ |l|`, a deletion of the same element
  at a position where it actually sits, or (for a deletion) `NOP` if the element is already gone.

Main facts: `square` (CP1 for valid operations, plus preservation of `Real`) and
`cp1_fails` (CP1 fails for the out-of-range positions the paper explicitly allows).
-/

namespace Podc.JupiterListSpec

/-- List operations of Section 2.3 / Appendix A: `ins a p pr` inserts `a` at `p` with priority
`pr`; `del a p` deletes the element at `p` (recording that it is `a`); `nop` does nothing. -/
inductive LOp (E : Type) where
  | ins (a : E) (p : ℕ) (pr : ℕ)
  | del (a : E) (p : ℕ)
  | nop
  deriving DecidableEq, Repr

variable {E : Type}

namespace LOp

/-- Applying an operation to a list (Section 2.3): positions beyond the end mean "at the end". -/
def apply : LOp E → List E → List E
  | .ins a p _, l => l.insertIdx (min p l.length) a
  | .del _ p, l => l.eraseIdx (min p (l.length - 1))
  | .nop, l => l

end LOp

/-- The OT functions of Figure A.1: `xf o₁ o₂` is `o₁` transformed against `o₂`, i.e. the first
component of `OT(o₁, o₂)`; the second component is `xf o₂ o₁`. -/
def xf : LOp E → LOp E → LOp E
  | .ins a₁ p₁ pr₁, .ins _ p₂ pr₂ =>
      if p₁ < p₂ then .ins a₁ p₁ pr₁
      else if p₂ < p₁ then .ins a₁ (p₁ + 1) pr₁
      else if pr₂ < pr₁ then .ins a₁ (p₁ + 1) pr₁
      else .ins a₁ p₁ pr₁
  | .ins a₁ p₁ pr₁, .del _ p₂ => if p₁ ≤ p₂ then .ins a₁ p₁ pr₁ else .ins a₁ (p₁ - 1) pr₁
  | .del a₁ p₁, .ins _ p₂ _ => if p₁ < p₂ then .del a₁ p₁ else .del a₁ (p₁ + 1)
  | .del a₁ p₁, .del _ p₂ =>
      if p₁ < p₂ then .del a₁ p₁ else if p₂ < p₁ then .del a₁ (p₁ - 1) else .nop
  | .nop, _ => .nop
  | o, .nop => o

/-- `Real o x l`: `x` is a (possibly transformed) form of the original operation `o` which is valid
at list `l` and has the same effect as `o`: it inserts the same element (absent from `l`) at a
position `≤ |l|` with the same priority, or deletes the same element at the position where it sits
in `l`, or — only for a deletion — is `NOP` because the element is no longer in `l`. -/
def Real : LOp E → LOp E → List E → Prop
  | .ins a _ pr, .ins a' p pr', l => a' = a ∧ pr' = pr ∧ p ≤ l.length ∧ a ∉ l
  | .del a _, .del a' p, l => a' = a ∧ l[p]? = some a
  | .del a _, .nop, l => a ∉ l
  | .nop, .nop, _ => True
  | _, _, _ => False

/-- Independence of two concurrent original operations: inserted elements are fresh w.r.t. the
other operation, and two concurrent insertions have different priorities. -/
def Indep : LOp E → LOp E → Prop
  | .ins a₁ _ pr₁, .ins a₂ _ pr₂ => a₁ ≠ a₂ ∧ pr₁ ≠ pr₂
  | .ins a _ _, .del b _ => a ≠ b
  | .del a _, .ins b _ _ => a ≠ b
  | _, _ => True

theorem Indep.symm {o₁ o₂ : LOp E} (h : Indep o₁ o₂) : Indep o₂ o₁ := by
  cases o₁ <;> cases o₂ <;> simp_all [Indep, eq_comm]

/-! ### Auxiliary list lemmas -/

namespace LOp

theorem apply_ins_of_le {a : E} {p pr : ℕ} {l : List E} (h : p ≤ l.length) :
    (LOp.ins a p pr).apply l = l.insertIdx p a := by
  simp [apply, Nat.min_eq_left h]

theorem apply_del_of_lt {a : E} {p : ℕ} {l : List E} (h : p < l.length) :
    (LOp.del a p).apply l = l.eraseIdx p := by
  simp only [apply]
  rw [Nat.min_eq_left (by omega)]

@[simp] theorem apply_nop (l : List E) : (LOp.nop : LOp E).apply l = l := rfl

end LOp

private theorem lt_length_of_getElem?_eq_some {l : List E} {p : ℕ} {a : E} (h : l[p]? = some a) :
    p < l.length :=
  (List.getElem?_eq_some_iff.1 h).1

private theorem insertIdx_eq_take_drop (c : E) :
    ∀ (l : List E) (p : ℕ), p ≤ l.length → l.insertIdx p c = l.take p ++ c :: l.drop p
  | _, 0, _ => by simp
  | [], _ + 1, h => by simp at h
  | x :: l, p + 1, h => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    rw [insertIdx_eq_take_drop c l p (by simpa using h)]

private theorem eraseIdx_eraseIdx_of_lt (l : List E) {i j : ℕ} (h : i < j) :
    (l.eraseIdx j).eraseIdx i = (l.eraseIdx i).eraseIdx (j - 1) := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_eraseIdx]
  split_ifs <;> first | rfl | (congr 1; omega)

private theorem nodup_insertIdx {l : List E} {p : ℕ} {a : E} (hp : p ≤ l.length) (ha : a ∉ l)
    (hl : l.Nodup) : (l.insertIdx p a).Nodup :=
  (List.perm_insertIdx a l hp).nodup_iff.2 (List.nodup_cons.2 ⟨ha, hl⟩)

private theorem mem_eraseIdx_of_nodup {l : List E} {p : ℕ} {a : E} (h : l[p]? = some a)
    (hl : l.Nodup) (b : E) : b ∈ l.eraseIdx p ↔ b ∈ l ∧ b ≠ a := by
  have hp := lt_length_of_getElem?_eq_some h
  rw [List.mem_eraseIdx_iff_getElem?]
  constructor
  · rintro ⟨i, hi, hb⟩
    refine ⟨List.mem_of_getElem? hb, ?_⟩
    rintro rfl
    exact hi ((hl.getElem?_inj hp).1 (h.trans hb.symm)).symm
  · rintro ⟨hb, hba⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb
    refine ⟨i, ?_, hi⟩
    rintro rfl
    exact hba (Option.some_injective _ (hi.symm.trans h))

private theorem xf_nop_right (x : LOp E) : xf x .nop = x := by cases x <;> rfl

private theorem xf_nop_left (x : LOp E) : xf .nop x = .nop := by cases x <;> rfl

private theorem real_ins_inv {o : LOp E} {a : E} {p pr : ℕ} {l : List E}
    (h : Real o (.ins a p pr) l) : ∃ q, o = .ins a q pr ∧ p ≤ l.length ∧ a ∉ l := by
  rcases o with ⟨b, q, r⟩ | ⟨b, q⟩ | _ <;> simp only [Real] at h
  obtain ⟨rfl, rfl, hp, ha⟩ := h
  exact ⟨q, rfl, hp, ha⟩

private theorem real_del_inv {o : LOp E} {a : E} {p : ℕ} {l : List E}
    (h : Real o (.del a p) l) : ∃ q, o = .del a q ∧ l[p]? = some a := by
  rcases o with ⟨b, q, r⟩ | ⟨b, q⟩ | _ <;> simp only [Real] at h
  obtain ⟨rfl, ha⟩ := h
  exact ⟨q, rfl, ha⟩

private theorem real_nop_inv {o : LOp E} {l : List E}
    (h : Real o .nop l) : o = .nop ∨ ∃ a q, o = .del a q ∧ a ∉ l := by
  rcases o with ⟨b, q, r⟩ | ⟨b, q⟩ | _ <;> simp only [Real] at h
  · exact Or.inr ⟨b, q, rfl, h⟩
  · exact Or.inl rfl

/-- An element absent from `l` and not inserted by `o` stays absent after a valid form of `o`. -/
private theorem not_mem_apply {o x : LOp E} {l : List E} {b : E} {q : ℕ}
    (h : Real o x l) (hd : Indep (.del b q) o) (hb : b ∉ l) : b ∉ x.apply l := by
  rcases x with ⟨a, p, pr⟩ | ⟨a, p⟩ | _
  · obtain ⟨q', rfl, hp, -⟩ := real_ins_inv h
    simp only [Indep] at hd
    rw [LOp.apply_ins_of_le hp, List.mem_insertIdx hp]
    tauto
  · obtain ⟨q', rfl, ha⟩ := real_del_inv h
    rw [LOp.apply_del_of_lt (lt_length_of_getElem?_eq_some ha)]
    exact fun hb' => hb (List.eraseIdx_subset hb')
  · exact hb

private theorem square_ins_ins {a₁ a₂ : E} {p₁ p₂ pr₁ pr₂ q₁ : ℕ} {l : List E}
    (hp₁ : p₁ ≤ l.length) (hp₂ : p₂ ≤ l.length) (ha₁ : a₁ ∉ l) (ha : a₁ ≠ a₂)
    (hpr : pr₁ ≠ pr₂) :
    (xf (.ins a₁ p₁ pr₁) (.ins a₂ p₂ pr₂)).apply ((LOp.ins a₂ p₂ pr₂).apply l) =
      (xf (.ins a₂ p₂ pr₂) (.ins a₁ p₁ pr₁)).apply ((LOp.ins a₁ p₁ pr₁).apply l) ∧
    Real (.ins a₁ q₁ pr₁) (xf (.ins a₁ p₁ pr₁) (.ins a₂ p₂ pr₂)) ((LOp.ins a₂ p₂ pr₂).apply l) := by
  have hl₁ := List.length_insertIdx_of_le_length hp₁ a₁
  have hl₂ := List.length_insertIdx_of_le_length hp₂ a₂
  have hm : a₁ ∉ l.insertIdx p₂ a₂ := by rw [List.mem_insertIdx hp₂]; tauto
  rw [LOp.apply_ins_of_le hp₁, LOp.apply_ins_of_le hp₂]
  simp only [xf]
  split_ifs <;> (try omega) <;>
    (rw [LOp.apply_ins_of_le (by omega), LOp.apply_ins_of_le (by omega)];
     refine ⟨?_, rfl, rfl, by omega, hm⟩)
  all_goals first
    | exact (List.insertIdx_comm _ _ (by omega) hp₂).symm
    | exact List.insertIdx_comm _ _ (by omega) hp₁

private theorem square_ins_del {a₁ a₂ : E} {p₁ p₂ pr₁ q₁ : ℕ} {l : List E}
    (hp₁ : p₁ ≤ l.length) (ha₂ : l[p₂]? = some a₂) (ha₁ : a₁ ∉ l) :
    (xf (.ins a₁ p₁ pr₁) (.del a₂ p₂)).apply ((LOp.del a₂ p₂).apply l) =
      (xf (.del a₂ p₂) (.ins a₁ p₁ pr₁)).apply ((LOp.ins a₁ p₁ pr₁).apply l) ∧
    Real (.ins a₁ q₁ pr₁) (xf (.ins a₁ p₁ pr₁) (.del a₂ p₂)) ((LOp.del a₂ p₂).apply l) := by
  have hp₂ := lt_length_of_getElem?_eq_some ha₂
  have hl₁ := List.length_insertIdx_of_le_length hp₁ a₁
  have hl₂ := List.length_eraseIdx_of_lt hp₂
  have hm : a₁ ∉ l.eraseIdx p₂ := fun h => ha₁ (List.eraseIdx_subset h)
  rw [LOp.apply_ins_of_le hp₁, LOp.apply_del_of_lt hp₂]
  simp only [xf]
  split_ifs <;> (try omega) <;>
    (rw [LOp.apply_ins_of_le (by omega), LOp.apply_del_of_lt (by omega)];
     refine ⟨?_, rfl, rfl, by omega, hm⟩)
  · exact List.insertIdx_eraseIdx_of_le hp₂ (by omega)
  · rw [List.insertIdx_eraseIdx_of_ge hp₂ (by omega), Nat.sub_add_cancel (by omega)]

private theorem square_del_ins {a₁ a₂ : E} {p₁ p₂ pr₂ q₁ : ℕ} {l : List E}
    (ha₁ : l[p₁]? = some a₁) (hp₂ : p₂ ≤ l.length) :
    (xf (.del a₁ p₁) (.ins a₂ p₂ pr₂)).apply ((LOp.ins a₂ p₂ pr₂).apply l) =
      (xf (.ins a₂ p₂ pr₂) (.del a₁ p₁)).apply ((LOp.del a₁ p₁).apply l) ∧
    Real (.del a₁ q₁) (xf (.del a₁ p₁) (.ins a₂ p₂ pr₂)) ((LOp.ins a₂ p₂ pr₂).apply l) := by
  have hp₁ := lt_length_of_getElem?_eq_some ha₁
  have hl₁ := List.length_eraseIdx_of_lt hp₁
  have hl₂ := List.length_insertIdx_of_le_length hp₂ a₂
  rw [LOp.apply_del_of_lt hp₁, LOp.apply_ins_of_le hp₂]
  simp only [xf]
  split_ifs <;> (try omega) <;>
    (rw [LOp.apply_ins_of_le (by omega), LOp.apply_del_of_lt (by omega)];
     refine ⟨?_, rfl, ?_⟩)
  · rw [List.insertIdx_eraseIdx_of_ge hp₁ (by omega), Nat.sub_add_cancel (by omega)]
  · rwa [List.getElem?_insertIdx_of_lt (by omega)]
  · exact (List.insertIdx_eraseIdx_of_le hp₁ (by omega)).symm
  · rwa [List.getElem?_insertIdx_of_gt (by omega), Nat.add_sub_cancel]

private theorem square_del_del {a₁ a₂ : E} {p₁ p₂ q₁ : ℕ} {l : List E} (hl : l.Nodup)
    (ha₁ : l[p₁]? = some a₁) (ha₂ : l[p₂]? = some a₂) :
    (xf (.del a₁ p₁) (.del a₂ p₂)).apply ((LOp.del a₂ p₂).apply l) =
      (xf (.del a₂ p₂) (.del a₁ p₁)).apply ((LOp.del a₁ p₁).apply l) ∧
    Real (.del a₁ q₁) (xf (.del a₁ p₁) (.del a₂ p₂)) ((LOp.del a₂ p₂).apply l) := by
  have hp₁ := lt_length_of_getElem?_eq_some ha₁
  have hp₂ := lt_length_of_getElem?_eq_some ha₂
  have hl₁ := List.length_eraseIdx_of_lt hp₁
  have hl₂ := List.length_eraseIdx_of_lt hp₂
  rw [LOp.apply_del_of_lt hp₁, LOp.apply_del_of_lt hp₂]
  simp only [xf]
  rcases lt_trichotomy p₁ p₂ with h | rfl | h
  · simp only [h, show ¬p₂ < p₁ by omega, ↓reduceIte]
    rw [LOp.apply_del_of_lt (by omega), LOp.apply_del_of_lt (by omega)]
    refine ⟨eraseIdx_eraseIdx_of_lt l h, rfl, ?_⟩
    rwa [List.getElem?_eraseIdx_of_lt h]
  · simp only [lt_self_iff_false, ↓reduceIte]
    refine ⟨trivial, ?_⟩
    simp only [Real]
    rw [mem_eraseIdx_of_nodup ha₁ hl]
    simp
  · simp only [h, show ¬p₁ < p₂ by omega, ↓reduceIte]
    rw [LOp.apply_del_of_lt (by omega), LOp.apply_del_of_lt (by omega)]
    refine ⟨(eraseIdx_eraseIdx_of_lt l h).symm, rfl, ?_⟩
    rwa [List.getElem?_eraseIdx_of_ge (by omega), Nat.sub_add_cancel (by omega)]

/-- **CP1** (Section 2.4) for valid operations, together with the preservation of `Real`:
if `x₁`, `x₂` are valid forms of independent operations `o₁`, `o₂` at the same duplicate-free
list, then applying `x₂` then `xf x₁ x₂` gives the same list as applying `x₁` then `xf x₂ x₁`,
and `xf x₁ x₂` is a valid form of `o₁` at the new list. -/
theorem square {o₁ o₂ x₁ x₂ : LOp E} {l : List E} (hl : l.Nodup)
    (h₁ : Real o₁ x₁ l) (h₂ : Real o₂ x₂ l) (hd : Indep o₁ o₂) :
    (xf x₁ x₂).apply (x₂.apply l) = (xf x₂ x₁).apply (x₁.apply l) ∧
      Real o₁ (xf x₁ x₂) (x₂.apply l) := by
  rcases x₁ with ⟨a₁, p₁, pr₁⟩ | ⟨a₁, p₁⟩ | _
  · rcases x₂ with ⟨a₂, p₂, pr₂⟩ | ⟨a₂, p₂⟩ | _
    · obtain ⟨q₁, rfl, hp₁, ha₁⟩ := real_ins_inv h₁
      obtain ⟨q₂, rfl, hp₂, -⟩ := real_ins_inv h₂
      obtain ⟨hne, hpr⟩ := hd
      exact square_ins_ins hp₁ hp₂ ha₁ hne hpr
    · obtain ⟨q₁, rfl, hp₁, ha₁⟩ := real_ins_inv h₁
      obtain ⟨q₂, rfl, ha₂⟩ := real_del_inv h₂
      exact square_ins_del hp₁ ha₂ ha₁
    · rw [xf_nop_right, xf_nop_left]
      exact ⟨rfl, h₁⟩
  · rcases x₂ with ⟨a₂, p₂, pr₂⟩ | ⟨a₂, p₂⟩ | _
    · obtain ⟨q₁, rfl, ha₁⟩ := real_del_inv h₁
      obtain ⟨q₂, rfl, hp₂, -⟩ := real_ins_inv h₂
      exact square_del_ins ha₁ hp₂
    · obtain ⟨q₁, rfl, ha₁⟩ := real_del_inv h₁
      obtain ⟨q₂, rfl, ha₂⟩ := real_del_inv h₂
      exact square_del_del hl ha₁ ha₂
    · rw [xf_nop_right, xf_nop_left]
      exact ⟨rfl, h₁⟩
  · rw [xf_nop_left, xf_nop_right]
    refine ⟨rfl, ?_⟩
    rcases real_nop_inv h₁ with rfl | ⟨b, q, rfl, hb⟩
    · trivial
    · exact not_mem_apply h₂ hd hb

/-- Valid operations keep lists duplicate-free. -/
theorem Real.nodup {o x : LOp E} {l : List E} (h : Real o x l) (hl : l.Nodup) :
    (x.apply l).Nodup := by
  rcases o with ⟨b, q, r⟩ | ⟨b, q⟩ | _ <;> rcases x with ⟨a, p, pr⟩ | ⟨a, p⟩ | _ <;>
    simp only [Real] at h
  · obtain ⟨rfl, rfl, hp, ha⟩ := h
    rw [LOp.apply_ins_of_le hp]
    exact nodup_insertIdx hp ha hl
  · obtain ⟨rfl, ha⟩ := h
    rw [LOp.apply_del_of_lt (lt_length_of_getElem?_eq_some ha)]
    exact hl.eraseIdx _
  · exact hl
  · exact hl

/-- Elements after a valid insertion. -/
theorem Real.mem_ins {a : E} {q pr : ℕ} {x : LOp E} {l : List E} (h : Real (.ins a q pr) x l)
    (b : E) : b ∈ x.apply l ↔ b ∈ l ∨ b = a := by
  rcases x with ⟨a', p, pr'⟩ | ⟨a', p⟩ | _ <;> simp only [Real] at h
  obtain ⟨rfl, rfl, hp, -⟩ := h
  rw [LOp.apply_ins_of_le hp, List.mem_insertIdx hp, or_comm]

/-- Elements after a valid deletion (or its `NOP` form). -/
theorem Real.mem_del {a : E} {q : ℕ} {x : LOp E} {l : List E} (h : Real (.del a q) x l)
    (hl : l.Nodup) (b : E) : b ∈ x.apply l ↔ b ∈ l ∧ b ≠ a := by
  rcases x with ⟨a', p, pr'⟩ | ⟨a', p⟩ | _ <;> simp only [Real] at h
  · obtain ⟨rfl, ha⟩ := h
    rw [LOp.apply_del_of_lt (lt_length_of_getElem?_eq_some ha)]
    exact mem_eraseIdx_of_nodup ha hl b
  · simp only [LOp.apply_nop]
    exact ⟨fun hb => ⟨hb, by rintro rfl; exact h hb⟩, And.left⟩

/-- Elements after a `NOP`. -/
theorem Real.mem_nop {x : LOp E} {l : List E} (h : Real .nop x l) (b : E) :
    b ∈ x.apply l ↔ b ∈ l := by
  rcases x with ⟨a', p, pr'⟩ | ⟨a', p⟩ | _ <;> simp only [Real] at h
  rfl

/-- A valid operation preserves the relative order of the elements it does not insert. -/
theorem Real.sublist {o x : LOp E} {l : List E} (h : Real o x l) (hl : l.Nodup) {a b : E}
    (ha : a ∈ l) (hb : b ∈ l) (hab : [a, b].Sublist (x.apply l)) : [a, b].Sublist l := by
  rcases o with ⟨c, q, r⟩ | ⟨c, q⟩ | _ <;> rcases x with ⟨c', p, pr⟩ | ⟨c', p⟩ | _ <;>
    simp only [Real] at h
  · classical
    obtain ⟨rfl, rfl, hp, hc⟩ := h
    rw [LOp.apply_ins_of_le hp, insertIdx_eq_take_drop c' l p hp] at hab
    have hf := hab.filter (fun y => decide (y ≠ c'))
    have hac : a ≠ c' := by rintro rfl; exact hc ha
    have hbc : b ≠ c' := by rintro rfl; exact hc hb
    have hl' : l.filter (fun y => decide (y ≠ c')) = l := by
      rw [List.filter_eq_self]
      intro y hy
      simp only [ne_eq, decide_eq_true_eq]
      rintro rfl
      exact hc hy
    have e1 : [a, b].filter (fun y => decide (y ≠ c')) = [a, b] := by
      simp [hac, hbc]
    have e2 : (l.take p ++ c' :: l.drop p).filter (fun y => decide (y ≠ c')) = l := by
      rw [← List.take_append_drop p l, List.filter_append] at hl'
      conv_rhs => rw [← List.take_append_drop p l]
      simpa [List.filter_append, List.filter_cons] using hl'
    rwa [e1, e2] at hf
  · obtain ⟨rfl, ha'⟩ := h
    rw [LOp.apply_del_of_lt (lt_length_of_getElem?_eq_some ha')] at hab
    exact hab.trans (List.eraseIdx_sublist _ _)
  · exact hab
  · exact hab

/-- A valid insertion puts the element at the requested position. -/
theorem Real.getElem?_ins {a a' : E} {q p pr pr' : ℕ} {l : List E}
    (h : Real (.ins a q pr) (.ins a' p pr') l) : ((LOp.ins a' p pr').apply l)[p]? = some a := by
  obtain ⟨rfl, rfl, hp, -⟩ := h
  rw [LOp.apply_ins_of_le hp, List.getElem?_insertIdx_self]
  simp [hp]

/-- **CP1 fails for Figure A.1 under the paper's out-of-range convention** (Section 2.3:
"For p larger than the list size, we assume a deletion at the end"). On the list `[x]`,
`o₁ = Del(x, 5)` (deleting the last element) and `o₂ = Ins(b, 1)` (appending `b`) give
`[x]` via `o₂; OT(o₁, o₂)` but `[b]` via `o₁; OT(o₂, o₁)`. -/
theorem cp1_fails :
    (xf (LOp.del 0 5) (LOp.ins 1 1 0)).apply ((LOp.ins 1 1 0).apply [0]) = [0] ∧
      (xf (LOp.ins 1 1 0) (LOp.del 0 5)).apply ((LOp.del (0 : ℕ) 5).apply [0]) = [1] := by
  decide

end Podc.JupiterListSpec
