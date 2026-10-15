import Cslib.Foundations.SocialChoice.Aggregation
import Papers.PODC2022.ArrowTopology.SignModel

/-!
# Three alternatives: profiles ↔ consistent sign triples

For a type of alternatives `X = {x, y, z}` (three distinct elements, `ThreeAlts X`), the three
pairs are `pr 0 = (x, y)`, `pr 1 = (y, z)`, `pr 2 = (z, x)` (the paper's `AB, BC, CA`).

* `sig1 r j`: the sign of preference `r` on the pair `pr j` (`true` = first ranked above second);
  `sig R j i = sig1 (R i) j` is the signature of a profile: the triangle of `N_I` it spans.
* `sig1_outTri`, `sig_consistent`: signatures are consistent (no cyclic preference).
* `exists_sig1_eq`, `exists_sig_eq`: every consistent sign triple is realised.
* `sig1_injective`, `sig_injective`: a preference (profile) is determined by its signature.
* `P_iff`: every comparison `r.P a b` is read off the signature.
-/

namespace Podc.ArrowTopology

open Cslib.SocialChoice

/-- Three distinct alternatives exhausting `X`. -/
structure ThreeAlts (X : Type*) where
  x : X
  y : X
  z : X
  hxy : x ≠ y
  hyz : y ≠ z
  hxz : x ≠ z
  cover : ∀ w, w = x ∨ w = y ∨ w = z

namespace ThreeAlts

variable {X ι : Type*} (T : ThreeAlts X)

/-- The three pairs `AB, BC, CA`. -/
def pr : Fin 3 → X × X := ![(T.x, T.y), (T.y, T.z), (T.z, T.x)]

open Classical in
/-- Sign of a preference on the pair `pr j`. -/
noncomputable def sig1 (r : Pref X) (j : Fin 3) : Bool := decide (r.P (T.pr j).1 (T.pr j).2)

/-- Signature of a profile: the triangle of `N_I` it spans. -/
noncomputable def sig (R : Profile ι X) : Fin 3 → ι → Bool := fun j i => T.sig1 (R i) j

theorem sig1_eq_true_iff (r : Pref X) (j : Fin 3) :
    T.sig1 r j = true ↔ r.P (T.pr j).1 (T.pr j).2 := by
  simp [sig1]

theorem sig1_eq_false_iff (r : Pref X) (j : Fin 3) :
    T.sig1 r j = false ↔ r.P (T.pr j).2 (T.pr j).1 := by
  have hne : (T.pr j).1 ≠ (T.pr j).2 := by
    fin_cases j
    · exact T.hxy
    · exact T.hyz
    · exact T.hxz.symm
  rw [← r.not_P_iff hne]
  simp [sig1]

theorem sig1_outTri (r : Pref X) : OutTri (T.sig1 r 0) (T.sig1 r 1) (T.sig1 r 2) := by
  rintro ⟨h1, h2⟩
  cases hb : T.sig1 r 0
  · have h0 := (T.sig1_eq_false_iff r 0).1 hb
    have h1' := (T.sig1_eq_false_iff r 1).1 (h1 ▸ hb)
    have h2' := (T.sig1_eq_false_iff r 2).1 (h2 ▸ h1 ▸ hb)
    simp only [pr, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1' h2'
    exact r.irrefl _ (r.trans (r.trans h0 h2') h1')
  · have h0 := (T.sig1_eq_true_iff r 0).1 hb
    have h1' := (T.sig1_eq_true_iff r 1).1 (h1 ▸ hb)
    have h2' := (T.sig1_eq_true_iff r 2).1 (h2 ▸ h1 ▸ hb)
    simp only [pr, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1' h2'
    exact r.irrefl _ (r.trans (r.trans h0 h1') h2')

theorem sig_consistent (R : Profile ι X) : Consistent (T.sig R) :=
  fun i => T.sig1_outTri (R i)

open Classical in
/-- Positions (`0` = top) of `x, y, z` in the order with signs `b0, b1, b2` on `AB, BC, CA`. -/
def ranks (b0 b1 b2 : Bool) : ℕ × ℕ × ℕ :=
  match b0, b1, b2 with
  | true, true, false => (0, 1, 2)    -- x y z
  | true, false, true => (1, 2, 0)    -- z x y
  | false, true, true => (2, 0, 1)    -- y z x
  | true, false, false => (0, 2, 1)   -- x z y
  | false, true, false => (1, 0, 2)   -- y x z
  | false, false, true => (2, 1, 0)   -- z y x
  | _, _, _ => (0, 1, 2)

open Classical in
/-- The preference with signs `b0, b1, b2` (when these are not all equal). -/
noncomputable def ofSigns (b0 b1 b2 : Bool) : Pref X :=
  Pref.ofRank fun w =>
    if w = T.x then (ranks b0 b1 b2).1 else if w = T.y then (ranks b0 b1 b2).2.1
    else (ranks b0 b1 b2).2.2

open Classical in
theorem sig1_ofSigns {b0 b1 b2 : Bool} (h : OutTri b0 b1 b2) :
    T.sig1 (T.ofSigns b0 b1 b2) 0 = b0 ∧ T.sig1 (T.ofSigns b0 b1 b2) 1 = b1 ∧
      T.sig1 (T.ofSigns b0 b1 b2) 2 = b2 := by
  have hyx := T.hxy.symm
  have hzy := T.hyz.symm
  have hzx := T.hxz.symm
  have key : ∀ j, T.sig1 (T.ofSigns b0 b1 b2) j = true ↔
      (fun w => if w = T.x then (ranks b0 b1 b2).1 else if w = T.y then (ranks b0 b1 b2).2.1
        else (ranks b0 b1 b2).2.2) (T.pr j).1 <
      (fun w => if w = T.x then (ranks b0 b1 b2).1 else if w = T.y then (ranks b0 b1 b2).2.1
        else (ranks b0 b1 b2).2.2) (T.pr j).2 := by
    intro j
    rw [sig1_eq_true_iff]
    unfold ofSigns
    rw [Pref.ofRank_P_iff]
    revert h
    fin_cases j <;> cases b0 <;> cases b1 <;> cases b2 <;>
      simp [OutTri, pr, ranks, hyx, hzy, hzx]
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [Bool.eq_iff_iff, key]
    revert h
    cases b0 <;> cases b1 <;> cases b2 <;>
      simp [OutTri, pr, ranks, hyx, hzy, hzx]

theorem exists_sig1_eq {b0 b1 b2 : Bool} (h : OutTri b0 b1 b2) :
    ∃ r : Pref X, T.sig1 r 0 = b0 ∧ T.sig1 r 1 = b1 ∧ T.sig1 r 2 = b2 :=
  ⟨_, T.sig1_ofSigns h⟩

/-- Every consistent sign triple is the signature of a profile. -/
theorem exists_sig_eq (t : Fin 3 → ι → Bool) (ht : Consistent t) : ∃ R, T.sig R = t := by
  choose r hr using fun i => T.exists_sig1_eq (ht i)
  refine ⟨r, ?_⟩
  funext j i
  fin_cases j
  · exact (hr i).1
  · exact (hr i).2.1
  · exact (hr i).2.2

/-- Comparisons are determined by the signature. -/
theorem P_iff (r : Pref X) {a b : X} (hab : a ≠ b) :
    r.P a b ↔ (∃ j, T.pr j = (a, b) ∧ T.sig1 r j = true) ∨
      (∃ j, T.pr j = (b, a) ∧ T.sig1 r j = false) := by
  constructor
  · intro h
    rcases T.cover a with rfl | rfl | rfl <;> rcases T.cover b with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hab
      | exact Or.inl ⟨0, rfl, (T.sig1_eq_true_iff r 0).2 h⟩
      | exact Or.inl ⟨1, rfl, (T.sig1_eq_true_iff r 1).2 h⟩
      | exact Or.inl ⟨2, rfl, (T.sig1_eq_true_iff r 2).2 h⟩
      | exact Or.inr ⟨0, rfl, (T.sig1_eq_false_iff r 0).2 h⟩
      | exact Or.inr ⟨1, rfl, (T.sig1_eq_false_iff r 1).2 h⟩
      | exact Or.inr ⟨2, rfl, (T.sig1_eq_false_iff r 2).2 h⟩
  · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
    · have := (T.sig1_eq_true_iff r j).1 h; rw [hj] at this; exact this
    · have := (T.sig1_eq_false_iff r j).1 h; rw [hj] at this; exact this

/-- A preference is determined by its signature. -/
theorem sig1_injective {r r' : Pref X} (h : ∀ j, T.sig1 r j = T.sig1 r' j) : r = r' := by
  ext a b
  by_cases hab : a = b
  · subst hab; simp [r.irrefl, r'.irrefl]
  · rw [T.P_iff r hab, T.P_iff r' hab]; simp only [h]

theorem sig_injective : Function.Injective (T.sig (ι := ι)) := by
  intro R S h
  funext i
  exact T.sig1_injective fun j => congrFun (congrFun h j) i

end ThreeAlts

end Podc.ArrowTopology
