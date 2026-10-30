/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Foundations/Data/Mazurkiewicz/NTrace.lean
import Podc.Foundations.Data.Mazurkiewicz.Defs

/-!
# Mazurkiewicz traces of duplicate-free schedules and their prefix order

For a symmetric dependence relation `D` on `α`, `NTrace D` is the type of traces of
duplicate-free schedules: duplicate-free lists modulo `NEquiv D` (same letters, same relative
order of dependent letters).

* `NTrace.mk l h`, `NTrace.rep`: the class of a duplicate-free list and a representative;
* `NTrace.supp`: the set of letters of a trace;
* the prefix order `x ≤ y ↔ ∃ z, y = x · z` (`NTrace.mk_le_mk_iff`) is a partial order with
  bottom `ε` and binary meets (greatest lower bounds);
* `NTrace.Pfx D l l'`: the list-level characterisation of the prefix order on duplicate-free
  lists (`NTrace.le_iff_pfx`, `NTrace.mk_le_mk_iff_pfx`, `NTrace.pfx_iff_exists`);
* `NTrace.lub S`: the least upper bound of a *compatible* (bounded above) finite set
  (`NTrace.isLUB_lub`); the order is *coherent*: a pairwise compatible finite set is compatible
  (`NTrace.compat_of_pairwise`);
* `NTrace.snoc x a`: append the letter `a` (if it does not already occur);
* `NTrace.compat_snoc`: appending pairwise independent new letters to a compatible family keeps
  it compatible.
-/

namespace Cslib.Mazurkiewicz

/-! ### Auxiliary facts about `Before`, `NEquiv` and prefixes of duplicate-free lists -/

namespace NTrace

section Aux

variable {α : Type*} {D : α → α → Prop}

@[simp] lemma before_nil (a b : α) : ¬ Before ([] : List α) a b := by
  rintro ⟨i, j, -, hi, -⟩; simp at hi

lemma before_cons {x : α} {l : List α} {a b : α} :
    Before (x :: l) a b ↔ (x = a ∧ b ∈ l) ∨ Before l a b := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        exact Or.inl ⟨hi, List.mem_of_getElem? (by simpa using hj)⟩
      | succ i => exact Or.inr ⟨i, j, by omega, by simpa using hi, by simpa using hj⟩
  · rintro (⟨rfl, hb⟩ | ⟨i, j, hij, hi, hj⟩)
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
      exact ⟨0, j + 1, by omega, rfl, by simp [hj]⟩
    · exact ⟨i + 1, j + 1, by omega, by simpa using hi, by simpa using hj⟩

lemma mem_left_of_before {l : List α} {a b : α} (h : Before l a b) : a ∈ l := by
  obtain ⟨i, j, -, hi, -⟩ := h; exact List.mem_of_getElem? hi

lemma mem_right_of_before {l : List α} {a b : α} (h : Before l a b) : b ∈ l := by
  obtain ⟨i, j, -, -, hj⟩ := h; exact List.mem_of_getElem? hj

@[simp] lemma before_singleton (x a b : α) : ¬ Before [x] a b := by
  simp [before_cons]

lemma before_append {l m : List α} {a b : α} :
    Before (l ++ m) a b ↔ Before l a b ∨ Before m a b ∨ (a ∈ l ∧ b ∈ m) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.cons_append, before_cons, ih, List.mem_append, List.mem_cons]
    constructor
    · rintro (⟨rfl, hb | hb⟩ | h | h | ⟨ha, hb⟩)
      · exact Or.inl (Or.inl ⟨rfl, hb⟩)
      · exact Or.inr (Or.inr ⟨Or.inl rfl, hb⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨Or.inr ha, hb⟩)
    · rintro ((⟨rfl, hb⟩ | h) | h | ⟨rfl | ha, hb⟩)
      · exact Or.inl ⟨rfl, Or.inl hb⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl ⟨rfl, Or.inr hb⟩
      · exact Or.inr (Or.inr (Or.inr ⟨ha, hb⟩))

lemma before_filter {l : List α} {p : α → Bool} {a b : α} :
    Before (l.filter p) a b ↔ Before l a b ∧ p a ∧ p b := by
  induction l with
  | nil => simp
  | cons x l ih =>
    by_cases hx : p x
    · simp only [List.filter_cons_of_pos hx, before_cons, ih, List.mem_filter]
      constructor
      · rintro (⟨rfl, hb, hpb⟩ | ⟨h, hpa, hpb⟩)
        · exact ⟨Or.inl ⟨rfl, hb⟩, hx, hpb⟩
        · exact ⟨Or.inr h, hpa, hpb⟩
      · rintro ⟨⟨rfl, hb⟩ | h, hpa, hpb⟩
        · exact Or.inl ⟨rfl, hb, hpb⟩
        · exact Or.inr ⟨h, hpa, hpb⟩
    · simp only [List.filter_cons_of_neg hx, before_cons, ih]
      constructor
      · rintro ⟨h, hpa, hpb⟩; exact ⟨Or.inr h, hpa, hpb⟩
      · rintro ⟨⟨rfl, hb⟩ | h, hpa, hpb⟩
        · exact absurd hpa hx
        · exact ⟨h, hpa, hpb⟩

lemma before_irrefl {l : List α} (hl : l.Nodup) (a : α) : ¬ Before l a a := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    rw [before_cons]
    rintro (⟨rfl, ha⟩ | h)
    · exact hl.1 ha
    · exact ih hl.2 h

lemma before_asymm {l : List α} (hl : l.Nodup) {a b : α} (h : Before l a b) :
    ¬ Before l b a := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    rw [before_cons] at h ⊢
    rintro (⟨rfl, ha⟩ | h')
    · rcases h with ⟨rfl, -⟩ | h
      · exact hl.1 ha
      · exact hl.1 (mem_right_of_before h)
    · rcases h with ⟨rfl, -⟩ | h
      · exact hl.1 (mem_right_of_before h')
      · exact ih hl.2 h h'

lemma before_ne {l : List α} (hl : l.Nodup) {a b : α} (h : Before l a b) : a ≠ b := by
  rintro rfl; exact before_irrefl hl a h

lemma before_total {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    Before l a b ∨ Before l b a := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [before_cons]
    rcases List.mem_cons.1 ha with h1 | h1 <;> rcases List.mem_cons.1 hb with h2 | h2
    · exact absurd (h1.trans h2.symm) hab
    · exact Or.inl (Or.inl ⟨h1.symm, h2⟩)
    · exact Or.inr (Or.inl ⟨h2.symm, h1⟩)
    · rcases ih h1 h2 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

lemma nequiv_refl (l : List α) : NEquiv D l l := ⟨List.Perm.refl _, fun _ _ _ h => h⟩

lemma nequiv_trans {l l' l'' : List α} (h : NEquiv D l l') (h' : NEquiv D l' l'') :
    NEquiv D l l'' :=
  ⟨h.1.trans h'.1, fun a b hab hb => h'.2 a b hab (h.2 a b hab hb)⟩

lemma nequiv_mem_iff {l l' : List α} (h : NEquiv D l l') {a : α} : a ∈ l ↔ a ∈ l' :=
  h.1.mem_iff

/-- `NEquiv D` is symmetric on duplicate-free lists. -/
lemma nequiv_symm [Std.Symm D] {l l' : List α} (hl' : l'.Nodup) (h : NEquiv D l l') :
    NEquiv D l' l := by
  refine ⟨h.1.symm, fun a b hab hb => ?_⟩
  rcases before_total (h.1.mem_iff.2 (mem_left_of_before hb))
    (h.1.mem_iff.2 (mem_right_of_before hb))
    (before_ne hl' hb) with h1 | h1
  · exact h1
  · exact absurd (h.2 b a (Std.Symm.symm a b hab) h1) (before_asymm hl' hb)

/-- For duplicate-free lists, `NEquiv D` means: same letters and same order of dependent
letters. -/
lemma nequiv_iff [Std.Symm D] {l l' : List α} (hl : l.Nodup) (hl' : l'.Nodup) :
    NEquiv D l l' ↔ (∀ a, a ∈ l ↔ a ∈ l') ∧
      ∀ a b, D a b → (Before l a b ↔ Before l' a b) := by
  refine ⟨fun h => ⟨fun a => nequiv_mem_iff h,
    fun a b hab => ⟨h.2 a b hab, (nequiv_symm hl' h).2 a b hab⟩⟩,
    fun h => ⟨(List.perm_ext_iff_of_nodup hl hl').2 h.1, fun a b hab => (h.2 a b hab).1⟩⟩

variable (D) in
/-- `Pfx D l l'`: the trace of `l` is a prefix of the trace of `l'` (for duplicate-free lists):
the letters of `l` occur in `l'`, dependent letters of `l` are ordered in `l'` as in `l`, and every
letter of `l'` not in `l` that depends on a letter `b` of `l` occurs after `b` in `l'`. -/
def Pfx (l l' : List α) : Prop :=
  (∀ a ∈ l, a ∈ l') ∧ (∀ a b, D a b → Before l a b → Before l' a b) ∧
    ∀ a b, D a b → b ∈ l → a ∈ l' → a ∉ l → Before l' b a

lemma pfx_refl (l : List α) : Pfx D l l :=
  ⟨fun _ h => h, fun _ _ _ h => h, fun _ _ _ _ ha hna => absurd ha hna⟩

lemma pfx_of_nequiv {l l' : List α} (h : NEquiv D l l') : Pfx D l l' :=
  ⟨fun _ ha => (nequiv_mem_iff h).1 ha, h.2,
    fun _ _ _ _ ha hna => absurd ((nequiv_mem_iff h).2 ha) hna⟩

lemma Pfx.trans [Std.Symm D] {l₁ l₂ l₃ : List α} (h : Pfx D l₁ l₂) (h' : Pfx D l₂ l₃) :
    Pfx D l₁ l₃ := by
  refine ⟨fun a ha => h'.1 a (h.1 a ha), fun a b hab hb => h'.2.1 a b hab (h.2.1 a b hab hb),
    fun a b hab hb ha hna => ?_⟩
  by_cases ha2 : a ∈ l₂
  · exact h'.2.1 b a (Std.Symm.symm a b hab) (h.2.2 a b hab hb ha2 hna)
  · exact h'.2.2 a b hab (h.1 b hb) ha ha2

lemma pfx_antisymm {l l' : List α} (hl : l.Nodup) (hl' : l'.Nodup) (h : Pfx D l l')
    (h' : Pfx D l' l) : NEquiv D l l' :=
  ⟨(List.perm_ext_iff_of_nodup hl hl').2 fun a => ⟨h.1 a, h'.1 a⟩, h.2.1⟩

lemma Pfx.before_iff [Std.Symm D] {l l' : List α} (h : Pfx D l l') (hl' : l'.Nodup) {a b : α}
    (hab : D a b) (ha : a ∈ l) (hb : b ∈ l) : Before l a b ↔ Before l' a b := by
  refine ⟨h.2.1 a b hab, fun h' => ?_⟩
  rcases before_total ha hb (before_ne hl' h') with h1 | h1
  · exact h1
  · exact absurd (h.2.1 b a (Std.Symm.symm a b hab) h1) (before_asymm hl' h')

lemma Pfx.mem_of_before {l l' : List α} (h : Pfx D l l') (hl' : l'.Nodup) {a b : α}
    (hab : D a b) (h' : Before l' a b) (hb : b ∈ l) : a ∈ l := by
  by_contra ha
  exact before_asymm hl' h' (h.2.2 a b hab hb (mem_left_of_before h') ha)

lemma pfx_append (l z : List α) : Pfx D l (l ++ z) := by
  refine ⟨fun a ha => List.mem_append_left _ ha,
    fun a b _ hb => before_append.2 (Or.inl hb), fun a b _ hb ha hna => ?_⟩
  rcases List.mem_append.1 ha with ha | ha
  · exact absurd ha hna
  · exact before_append.2 (Or.inr (Or.inr ⟨hb, ha⟩))

lemma pfx_filter {l : List α} {p : α → Bool}
    (hp : ∀ a b, D a b → Before l a b → p b → p a) : Pfx D (l.filter p) l := by
  refine ⟨fun a ha => List.mem_of_mem_filter ha, fun a b _ hb => (before_filter.1 hb).1,
    fun a b hab hb ha hna => ?_⟩
  rw [List.mem_filter] at hb hna
  have hpa : ¬ p a := fun h => hna ⟨ha, h⟩
  rcases before_total ha hb.1 (by rintro rfl; exact hpa hb.2) with h | h
  · exact absurd (hp a b hab h hb.2) hpa
  · exact h

lemma Pfx.of_subset [Std.Symm D] {l m z : List α} (hz : z.Nodup)
    (h : Pfx D l z) (h' : Pfx D m z) (hsub : ∀ a ∈ l, a ∈ m) : Pfx D l m := by
  refine ⟨hsub, fun a b hab hb => ?_, fun a b hab hb ha hna => ?_⟩
  · exact (h'.before_iff hz hab (hsub a (mem_left_of_before hb))
      (hsub b (mem_right_of_before hb))).2 (h.2.1 a b hab hb)
  · exact (h'.before_iff hz (Std.Symm.symm a b hab) (hsub b hb) ha).2
      (h.2.2 a b hab hb (h'.1 a ha) hna)

/-- Two prefixes of a common list have no dependent "cross pair". -/
lemma Pfx.not_dep_cross [Std.Symm D] {l m z : List α} (hz : z.Nodup) (h : Pfx D l z)
    (h' : Pfx D m z) {a b : α} (ha : a ∈ l) (ham : a ∉ m) (hb : b ∈ m) (hbl : b ∉ l) :
    ¬ D a b := fun hab =>
  before_asymm hz (h.2.2 b a (Std.Symm.symm a b hab) ha (h'.1 b hb) hbl)
    (h'.2.2 a b hab hb (h.1 a ha) ham)

lemma pfx_iff_exists [Std.Symm D] {l l' : List α} (hl : l.Nodup) (hl' : l'.Nodup) :
    Pfx D l l' ↔ ∃ z, NEquiv D l' (l ++ z) := by
  classical
  constructor
  · intro h
    have hnd : (l ++ l'.filter fun a => a ∉ l).Nodup :=
      List.nodup_append.2 ⟨hl, hl'.filter _, fun a ha b hb => by
        rintro rfl; simp only [List.mem_filter, decide_eq_true_eq] at hb; exact hb.2 ha⟩
    refine ⟨l'.filter fun a => a ∉ l, (List.perm_ext_iff_of_nodup hl' hnd).2 fun a => ?_,
      fun a b hab hb => ?_⟩
    · simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
      by_cases ha : a ∈ l
      · simp [ha, h.1 a ha]
      · simp [ha]
    · simp only [before_append, before_filter, List.mem_filter, decide_eq_true_eq]
      by_cases ha : a ∈ l <;> by_cases hb' : b ∈ l
      · exact Or.inl ((h.before_iff hl' hab ha hb').2 hb)
      · exact Or.inr (Or.inr ⟨ha, (mem_right_of_before hb), hb'⟩)
      · exact absurd (h.mem_of_before hl' hab hb hb') ha
      · exact Or.inr (Or.inl ⟨hb, ha, hb'⟩)
  · rintro ⟨z, hz⟩
    have hnd : (l ++ z).Nodup := hz.1.nodup_iff.1 hl'
    exact (pfx_append l z).trans (pfx_of_nequiv (nequiv_symm hnd hz))

end Aux

end NTrace

variable {α : Type*} (D : α → α → Prop) [Std.Symm D]

/-- The setoid of duplicate-free lists under `NEquiv D`. -/
def nSetoid : Setoid {l : List α // l.Nodup} where
  r l l' := NEquiv D l.1 l'.1
  iseqv := ⟨fun l => NTrace.nequiv_refl l.1, fun {_ l'} h => NTrace.nequiv_symm l'.2 h,
    fun h h' => NTrace.nequiv_trans h h'⟩

/-- Traces of duplicate-free schedules. -/
def NTrace : Type _ := Quotient (nSetoid D)

namespace NTrace

variable {D}

/-- The trace of a duplicate-free list. -/
def mk (l : List α) (h : l.Nodup) : NTrace D := Quotient.mk _ ⟨l, h⟩

/-- A representative of a trace. -/
noncomputable def rep (x : NTrace D) : List α := (Quotient.out x).1

lemma rep_nodup (x : NTrace D) : x.rep.Nodup := (Quotient.out x).2

@[simp] lemma mk_rep (x : NTrace D) : mk x.rep x.rep_nodup = x := Quotient.out_eq x

lemma mk_eq_mk_iff {l l' : List α} {h : l.Nodup} {h' : l'.Nodup} :
    mk (D := D) l h = mk l' h' ↔ NEquiv D l l' := Quotient.eq (r := nSetoid D)

lemma ind {p : NTrace D → Prop} (h : ∀ l (hl : l.Nodup), p (mk l hl)) (x : NTrace D) : p x := by
  rw [← mk_rep x]; exact h _ _

/-- The representative of `mk l h` is equivalent to `l`. -/
lemma rep_mk_nequiv (l : List α) (h : l.Nodup) : NEquiv D (mk (D := D) l h).rep l :=
  mk_eq_mk_iff.1 (mk_rep _)

@[simp] lemma mem_rep_mk {l : List α} {h : l.Nodup} {a : α} :
    a ∈ (mk (D := D) l h).rep ↔ a ∈ l :=
  nequiv_mem_iff (rep_mk_nequiv l h)

section Supp

variable [DecidableEq α]

/-- The letters of a trace. -/
noncomputable def supp (x : NTrace D) : Finset α := x.rep.toFinset

lemma mem_supp {x : NTrace D} {a : α} : a ∈ x.supp ↔ a ∈ x.rep := List.mem_toFinset

@[simp] lemma supp_mk (l : List α) (h : l.Nodup) : (mk (D := D) l h).supp = l.toFinset := by
  ext a; simp [supp]

end Supp

/-- The prefix order: `x ≤ y` iff `y = x · z` for some `z`. -/
instance : PartialOrder (NTrace D) where
  le x y := Pfx D x.rep y.rep
  le_refl x := pfx_refl _
  le_trans _ _ _ h h' := Pfx.trans h h'
  le_antisymm x y h h' :=
    (mk_rep x).symm.trans ((mk_eq_mk_iff.2 (pfx_antisymm x.rep_nodup y.rep_nodup h h')).trans
      (mk_rep y))

lemma le_iff_pfx {x y : NTrace D} : x ≤ y ↔ Pfx D x.rep y.rep := Iff.rfl

lemma le_mk_iff {x : NTrace D} {l : List α} {h : l.Nodup} : x ≤ mk l h ↔ Pfx D x.rep l :=
  ⟨fun hx => Pfx.trans hx (pfx_of_nequiv (rep_mk_nequiv l h)),
    fun hx => Pfx.trans hx (pfx_of_nequiv (nequiv_symm h (rep_mk_nequiv l h)))⟩

lemma mk_le_iff {y : NTrace D} {l : List α} {h : l.Nodup} : mk l h ≤ y ↔ Pfx D l y.rep :=
  ⟨fun hy => Pfx.trans (pfx_of_nequiv (nequiv_symm h (rep_mk_nequiv l h))) hy,
    fun hy => Pfx.trans (pfx_of_nequiv (rep_mk_nequiv l h)) hy⟩

lemma mk_le_mk_iff_pfx {l l' : List α} {h : l.Nodup} {h' : l'.Nodup} :
    mk (D := D) l h ≤ mk l' h' ↔ Pfx D l l' :=
  le_mk_iff.trans ⟨fun h₁ => Pfx.trans (pfx_of_nequiv (nequiv_symm h (rep_mk_nequiv l h))) h₁,
    fun h₁ => Pfx.trans (pfx_of_nequiv (rep_mk_nequiv l h)) h₁⟩

lemma mk_le_mk_iff {l l' : List α} {h : l.Nodup} {h' : l'.Nodup} :
    mk (D := D) l h ≤ mk l' h' ↔ ∃ z, NEquiv D l' (l ++ z) :=
  mk_le_mk_iff_pfx.trans (pfx_iff_exists h h')

/-- `l` is a prefix of `l ++ z`. -/
lemma mk_le_mk_append {l z : List α} {h : l.Nodup} {h' : (l ++ z).Nodup} :
    mk (D := D) l h ≤ mk (l ++ z) h' :=
  mk_le_mk_iff_pfx.2 (pfx_append l z)

/-- The empty trace `ε` is the least element. -/
instance : OrderBot (NTrace D) where
  bot := mk [] List.nodup_nil
  bot_le _ := mk_le_iff.2 ⟨by simp, by simp, by simp⟩

lemma bot_eq : (⊥ : NTrace D) = mk [] List.nodup_nil := rfl

section Lub

/-- Two dependent letters occurring in members of a compatible set occur in a common member. -/
lemma exists_mem_both {S : Finset (NTrace D)} {z : NTrace D} (hz : ∀ x ∈ S, x ≤ z) {a b : α}
    (hab : D a b) {x y : NTrace D} (hx : x ∈ S) (hy : y ∈ S) (ha : a ∈ x.rep) (hb : b ∈ y.rep) :
    ∃ s ∈ S, a ∈ s.rep ∧ b ∈ s.rep := by
  by_cases hbx : b ∈ x.rep
  · exact ⟨x, hx, ha, hbx⟩
  by_cases hay : a ∈ y.rep
  · exact ⟨y, hy, hay, hb⟩
  exact absurd hab (Pfx.not_dep_cross z.rep_nodup (hz x hx) (hz y hy) ha hay hb hbx)

open Classical in
/-- Auxiliary for `lub`: the letters of the members of `S`, in the order of a chosen upper
bound. -/
noncomputable def lubList (S : Finset (NTrace D)) (h : ∃ z, ∀ x ∈ S, x ≤ z) : List α :=
  (Classical.choose h).rep.filter fun a => decide (∃ x ∈ S, a ∈ x.rep)

lemma lubList_nodup {S : Finset (NTrace D)} (h : ∃ z, ∀ x ∈ S, x ≤ z) : (lubList S h).Nodup :=
  (Classical.choose h).rep_nodup.filter _

open Classical in
/-- The least upper bound of a compatible finite set of traces (junk otherwise). -/
noncomputable def lub (S : Finset (NTrace D)) : NTrace D :=
  if h : ∃ z, ∀ x ∈ S, x ≤ z then mk (lubList S h) (lubList_nodup h) else ⊥

lemma lub_eq {S : Finset (NTrace D)} (h : ∃ z, ∀ x ∈ S, x ≤ z) :
    lub S = mk (lubList S h) (lubList_nodup h) := by
  simp [lub, h]

lemma mem_lubList {S : Finset (NTrace D)} (h : ∃ z, ∀ x ∈ S, x ≤ z) {a : α} :
    a ∈ lubList S h ↔ ∃ x ∈ S, a ∈ x.rep := by
  simp only [lubList, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h' => h'.2, fun ⟨x, hx, ha⟩ => ⟨(Classical.choose_spec h x hx).1 a ha, x, hx, ha⟩⟩

lemma pfx_lubList {S : Finset (NTrace D)} (h : ∃ z, ∀ x ∈ S, x ≤ z) :
    Pfx D (lubList S h) (Classical.choose h).rep :=
  pfx_filter fun a b hab hb hpb => by
    simp only [decide_eq_true_eq] at hpb ⊢
    obtain ⟨x, hx, hbx⟩ := hpb
    exact ⟨x, hx, (Classical.choose_spec h x hx).mem_of_before (rep_nodup _) hab hb hbx⟩

/-- The letters of `lub S` are those of the members of `S`. -/
lemma mem_rep_lub {S : Finset (NTrace D)} (h : ∃ z, ∀ x ∈ S, x ≤ z) {a : α} :
    a ∈ (lub S).rep ↔ ∃ x ∈ S, a ∈ x.rep := by
  rw [lub_eq h, mem_rep_mk, mem_lubList]

lemma le_lub {S : Finset (NTrace D)} (h : ∃ z, ∀ x ∈ S, x ≤ z) {x : NTrace D} (hx : x ∈ S) :
    x ≤ lub S := by
  rw [lub_eq h, le_mk_iff]
  exact Pfx.of_subset (rep_nodup _) (Classical.choose_spec h x hx)
    (pfx_lubList h) fun a ha => (mem_lubList h).2 ⟨x, hx, ha⟩

lemma lub_le {S : Finset (NTrace D)} (h : ∃ z, ∀ x ∈ S, x ≤ z) {w : NTrace D}
    (hw : ∀ x ∈ S, x ≤ w) : lub S ≤ w := by
  rw [lub_eq h, mk_le_iff]
  have hz := Classical.choose_spec h
  refine ⟨fun a ha => ?_, fun a b hab hb => ?_, fun a b hab hb ha hna => ?_⟩
  · obtain ⟨x, hx, hax⟩ := (mem_lubList h).1 ha
    exact (hw x hx).1 a hax
  · obtain ⟨x, hx, hax⟩ := (mem_lubList h).1 (mem_left_of_before hb)
    obtain ⟨y, hy, hby⟩ := (mem_lubList h).1 (mem_right_of_before hb)
    obtain ⟨s, hs, has, hbs⟩ := exists_mem_both hz hab hx hy hax hby
    have hb' : Before (Classical.choose h).rep a b := (pfx_lubList h).2.1 a b hab hb
    exact (hw s hs).2.1 a b hab (((hz s hs).before_iff (rep_nodup _) hab has hbs).2 hb')
  · obtain ⟨x, hx, hbx⟩ := (mem_lubList h).1 hb
    exact (hw x hx).2.2 a b hab hbx ha fun hax => hna ((mem_lubList h).2 ⟨x, hx, hax⟩)

/-- A compatible (bounded above) finite set of traces has a least upper bound. -/
lemma isLUB_lub {S : Finset (NTrace D)} (h : ∃ z, ∀ x ∈ S, x ≤ z) :
    IsLUB (S : Set (NTrace D)) (lub S) :=
  ⟨fun _ hx => le_lub h hx, fun _ hw => lub_le h fun _ hx => hw hx⟩

/-- If `x` is compatible with every member of a compatible set `T`, then `x` is compatible with
`lub T`. -/
lemma exists_ub_lub {x : NTrace D} {T : Finset (NTrace D)} (hT : ∃ z, ∀ y ∈ T, y ≤ z)
    (hx : ∀ y ∈ T, ∃ v, x ≤ v ∧ y ≤ v) : ∃ w, x ≤ w ∧ lub T ≤ w := by
  classical
  have hL : ∀ a, a ∈ (lub T).rep ↔ ∃ y ∈ T, a ∈ y.rep := fun a => mem_rep_lub hT
  have hLT : ∀ y ∈ T, y ≤ lub T := fun y hy => le_lub hT hy
  have hnd : ((lub T).rep ++ x.rep.filter fun a => a ∉ (lub T).rep).Nodup :=
    List.nodup_append.2 ⟨rep_nodup _, (rep_nodup _).filter _, fun a ha b hb => by
      rintro rfl; simp only [List.mem_filter, decide_eq_true_eq] at hb; exact hb.2 ha⟩
  refine ⟨mk _ hnd, le_mk_iff.2 ⟨fun a ha => ?_, fun a b hab hb => ?_, fun a b hab hb ha hna => ?_⟩,
    le_mk_iff.2 (pfx_append _ _)⟩
  · by_cases h : a ∈ (lub T).rep <;> simp [h, ha]
  · simp only [before_append, before_filter, List.mem_filter, decide_eq_true_eq]
    by_cases ha : a ∈ (lub T).rep <;> by_cases hb' : b ∈ (lub T).rep
    · left
      obtain ⟨y, hy, hay⟩ := (hL a).1 ha
      obtain ⟨y', hy', hby⟩ := (hL b).1 hb'
      obtain ⟨s, hs, has, hbs⟩ := exists_mem_both hLT hab hy hy' hay hby
      obtain ⟨v, hxv, hsv⟩ := hx s hs
      exact (hLT s hs).2.1 a b hab ((hsv.before_iff (rep_nodup _) hab has hbs).2
        (hxv.2.1 a b hab hb))
    · exact Or.inr (Or.inr ⟨ha, (mem_right_of_before hb), hb'⟩)
    · exfalso
      obtain ⟨y, hy, hby⟩ := (hL b).1 hb'
      have hay : a ∉ y.rep := fun h => ha ((hL a).2 ⟨y, hy, h⟩)
      obtain ⟨v, hxv, hyv⟩ := hx y hy
      exact before_asymm (rep_nodup v) (hxv.2.1 a b hab hb)
        (hyv.2.2 a b hab hby (hxv.1 a (mem_left_of_before hb)) hay)
    · exact Or.inr (Or.inl ⟨hb, ha, hb'⟩)
  · have ha' : a ∈ (lub T).rep := by
      rcases List.mem_append.1 ha with ha | ha
      · exact ha
      · exact absurd (List.mem_of_mem_filter ha) hna
    obtain ⟨y, hy, hay⟩ := (hL a).1 ha'
    rw [before_append]
    by_cases hb' : b ∈ (lub T).rep
    · left
      obtain ⟨y', hy', hby⟩ := (hL b).1 hb'
      obtain ⟨s, hs, has, hbs⟩ := exists_mem_both hLT hab hy hy' hay hby
      obtain ⟨v, hxv, hsv⟩ := hx s hs
      exact (hLT s hs).2.1 b a (Std.Symm.symm a b hab)
        ((hsv.before_iff (rep_nodup _) (Std.Symm.symm a b hab) hbs has).2
          (hxv.2.2 a b hab hb (hsv.1 a has) hna))
    · exfalso
      have hby : b ∉ y.rep := fun h => hb' ((hL b).2 ⟨y, hy, h⟩)
      obtain ⟨v, hxv, hyv⟩ := hx y hy
      exact Pfx.not_dep_cross (rep_nodup v) hyv hxv hay hna hb hby hab

/-- Coherence: a pairwise compatible finite set of traces is compatible. -/
lemma compat_of_pairwise {S : Finset (NTrace D)}
    (h : ∀ x ∈ S, ∀ y ∈ S, ∃ z, x ≤ z ∧ y ≤ z) : ∃ z, ∀ x ∈ S, x ≤ z := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊥, by simp⟩
  | insert x T _ ih =>
    have hT := ih fun a ha b hb =>
      h a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
    obtain ⟨w, hxw, hLw⟩ := exists_ub_lub hT fun y hy =>
      h x (Finset.mem_insert_self _ _) y (Finset.mem_insert_of_mem hy)
    refine ⟨w, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hxw
    · exact (le_lub hT hy).trans hLw

/-- A prefix `p` of `x` is the restriction of (a representative of) `x` to the letters of `p`. -/
lemma eq_mk_filter_of_le {p x : NTrace D} (h : p ≤ x) {q : α → Bool}
    (hq : ∀ a, q a = true ↔ a ∈ p.rep) : p = mk (x.rep.filter q) (x.rep_nodup.filter _) := by
  have hf : Pfx D (x.rep.filter q) x.rep := pfx_filter fun a b hab hb hqb =>
    (hq a).2 (h.mem_of_before (rep_nodup _) hab hb ((hq b).1 hqb))
  have hsub1 : ∀ a ∈ p.rep, a ∈ x.rep.filter q := fun a ha =>
    List.mem_filter.2 ⟨h.1 a ha, (hq a).2 ha⟩
  have hsub2 : ∀ a ∈ x.rep.filter q, a ∈ p.rep := fun a ha => (hq a).1 (List.mem_filter.1 ha).2
  exact (mk_rep p).symm.trans (mk_eq_mk_iff.2 (pfx_antisymm (rep_nodup _) ((rep_nodup _).filter _)
    (Pfx.of_subset (rep_nodup _) h hf hsub1)
    (Pfx.of_subset (rep_nodup _) hf h hsub2)))

open Classical in
/-- The finite set of common lower bounds of `x` and `y` (auxiliary for `⊓`). -/
noncomputable def lowerBoundsFin (x y : NTrace D) : Finset (NTrace D) :=
  ((x.rep.toFinset.powerset.image fun A =>
    mk (D := D) (x.rep.filter fun a => decide (a ∈ A)) (x.rep_nodup.filter _))).filter
      fun p => p ≤ x ∧ p ≤ y

lemma mem_lowerBoundsFin {x y p : NTrace D} : p ∈ lowerBoundsFin x y ↔ p ≤ x ∧ p ≤ y := by
  classical
  unfold lowerBoundsFin
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨Finset.mem_image.2 ⟨p.rep.toFinset, ?_, ?_⟩, h⟩⟩
  · rw [Finset.mem_powerset]
    intro a ha
    rw [List.mem_toFinset] at ha ⊢
    exact h.1.1 a ha
  · exact (eq_mk_filter_of_le h.1 (by simp)).symm

lemma lowerBoundsFin_bdd (x y : NTrace D) : ∃ z, ∀ p ∈ lowerBoundsFin x y, p ≤ z :=
  ⟨x, fun _ hp => (mem_lowerBoundsFin.1 hp).1⟩

/-- Every pair of traces has a greatest lower bound (Aalbersberg–Rozenberg). -/
noncomputable instance : SemilatticeInf (NTrace D) :=
  { (inferInstance : PartialOrder (NTrace D)) with
    inf := fun x y => lub (lowerBoundsFin x y)
    inf_le_left := fun x y =>
      lub_le (lowerBoundsFin_bdd x y) fun _ hp => (mem_lowerBoundsFin.1 hp).1
    inf_le_right := fun x y =>
      lub_le (lowerBoundsFin_bdd x y) fun _ hp => (mem_lowerBoundsFin.1 hp).2
    le_inf := fun _ x y hx hy =>
      le_lub (lowerBoundsFin_bdd x y) (mem_lowerBoundsFin.2 ⟨hx, hy⟩) }

lemma inf_eq_lub (x y : NTrace D) : x ⊓ y = lub (lowerBoundsFin x y) := rfl

variable [DecidableEq α]

lemma supp_mono {x y : NTrace D} (h : x ≤ y) : x.supp ⊆ y.supp := fun a ha =>
  mem_supp.2 (h.1 a (mem_supp.1 ha))

@[simp] lemma supp_bot : (⊥ : NTrace D).supp = ∅ := by
  rw [bot_eq, supp_mk]; rfl

lemma supp_lub_subset {S : Finset (NTrace D)} (h : ∃ z, ∀ x ∈ S, x ≤ z) :
    (lub S).supp ⊆ S.biUnion supp := fun a ha => by
  obtain ⟨x, hx, hax⟩ := (mem_rep_lub h).1 (mem_supp.1 ha)
  exact Finset.mem_biUnion.2 ⟨x, hx, mem_supp.2 hax⟩

/-- The letters of the least upper bound are the letters of the members. -/
lemma supp_lub {S : Finset (NTrace D)} (h : ∃ z, ∀ x ∈ S, x ≤ z) :
    (lub S).supp = S.biUnion supp :=
  subset_antisymm (supp_lub_subset h) (Finset.biUnion_subset.2 fun _ hx => supp_mono (le_lub h hx))

/-- If `x ≤ y` and both have the same letters, then `x = y`. -/
lemma eq_of_le_of_supp_eq {x y : NTrace D} (h : x ≤ y) (hs : y.supp ⊆ x.supp) : x = y := by
  have hmem : ∀ a ∈ y.rep, a ∈ x.rep := fun a ha => mem_supp.1 (hs (mem_supp.2 ha))
  refine le_antisymm h ⟨hmem, fun a b hab hb => ?_, fun a _ _ _ ha hna => absurd (h.1 a ha) hna⟩
  exact (h.before_iff (rep_nodup _) hab (hmem a (mem_left_of_before hb))
    (hmem b (mem_right_of_before hb))).2 hb

end Lub

section Snoc

variable [DecidableEq α]

/-- Append the letter `a` to `x` (no-op if `a` already occurs in `x`). -/
noncomputable def snoc (x : NTrace D) (a : α) : NTrace D :=
  if h : a ∈ x.supp then x else
    mk (x.rep ++ [a]) (List.nodup_append.2 ⟨x.rep_nodup, List.nodup_singleton a,
      fun b hb c hc => by
        simp only [List.mem_singleton] at hc; subst hc; exact fun hab => h (by simp [supp, ← hab, hb])⟩)

lemma le_snoc (x : NTrace D) (a : α) : x ≤ x.snoc a := by
  unfold snoc
  split_ifs with h
  · exact le_rfl
  · exact le_mk_iff.2 (pfx_append _ _)

@[simp] lemma supp_snoc (x : NTrace D) (a : α) : (x.snoc a).supp = insert a x.supp := by
  unfold snoc
  split_ifs with h
  · exact (Finset.insert_eq_of_mem h).symm
  · ext b; simp [supp, or_comm]

lemma snoc_of_mem {x : NTrace D} {a : α} (h : a ∈ x.supp) : x.snoc a = x := by
  simp [snoc, h]

omit [DecidableEq α] in
/-- Every extension of `mk l` is represented by an extension of `l`. -/
lemma exists_append_of_le {l : List α} {hl : l.Nodup} {y : NTrace D} (h : mk l hl ≤ y) :
    ∃ z, ∃ hz : (l ++ z).Nodup, mk (l ++ z) hz = y := by
  obtain ⟨z, hz⟩ := (pfx_iff_exists hl y.rep_nodup).1 (mk_le_iff.1 h)
  have hnd : (l ++ z).Nodup := hz.1.nodup_iff.1 y.rep_nodup
  exact ⟨z, hnd, (mk_eq_mk_iff.2 (nequiv_symm hnd hz)).trans (mk_rep y)⟩

/-- Appending letters to a compatible family keeps it compatible, provided all letters that are
not in a common lower bound `g` of the family, together with the appended letters, are pairwise
independent. (Used for invariant (I) of Theorem 4.4.) -/
lemma compat_snoc {ι : Type*} (J : Finset ι) (t : ι → NTrace D) (e : ι → α) (g : NTrace D)
    (hc : ∃ z, ∀ j ∈ J, t j ≤ z) (hg : ∀ j ∈ J, g ≤ t j)
    (hind : ∀ a ∈ (J.biUnion fun j => (t j).supp \ g.supp) ∪
        (J.filter fun j => e j ∉ (t j).supp).image e,
      ∀ b ∈ (J.biUnion fun j => (t j).supp \ g.supp) ∪
        (J.filter fun j => e j ∉ (t j).supp).image e, a ≠ b → ¬ D a b) :
    ∃ z, ∀ j ∈ J, (t j).snoc (e j) ≤ z := by
  let _ : DecidableEq (NTrace D) := Classical.decEq _
  have hSc : ∃ z, ∀ x ∈ J.image t, x ≤ z := by
    obtain ⟨z, hz⟩ := hc
    exact ⟨z, fun x hx => by obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx; exact hz j hj⟩
  have hL : ∀ a, a ∈ (lub (J.image t)).rep ↔ ∃ j ∈ J, a ∈ (t j).rep := fun a => by
    rw [mem_rep_lub hSc]
    exact ⟨fun ⟨x, hx, ha⟩ => by obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx; exact ⟨j, hj, ha⟩,
      fun ⟨j, hj, ha⟩ => ⟨t j, Finset.mem_image_of_mem t hj, ha⟩⟩
  -- the appended letters that are new
  let E' := ((J.filter fun j => e j ∉ (t j).supp).image e).toList.filter
    fun a => a ∉ (lub (J.image t)).rep
  have hEmem : ∀ a ∈ E', a ∈ (J.filter fun j => e j ∉ (t j).supp).image e := fun a ha =>
    Finset.mem_toList.1 (List.mem_filter.1 ha).1
  have hnd : ((lub (J.image t)).rep ++ E').Nodup :=
    List.nodup_append.2 ⟨rep_nodup _, (Finset.nodup_toList _).filter _, fun a ha b hb => by
      rintro rfl; simp only [E', List.mem_filter, decide_eq_true_eq] at hb; exact hb.2 ha⟩
  refine ⟨mk _ hnd, fun j hj => ?_⟩
  have htL : t j ≤ lub (J.image t) := le_lub hSc (Finset.mem_image_of_mem t hj)
  have hLw : lub (J.image t) ≤ mk _ hnd := le_mk_iff.2 (pfx_append _ _)
  by_cases hej : e j ∈ (t j).supp
  · rw [snoc_of_mem hej]; exact htL.trans hLw
  simp only [snoc, hej, dite_false, mk_le_mk_iff_pfx]
  have hej' : e j ∉ (t j).rep := fun h => hej (mem_supp.2 h)
  have htLp : Pfx D (t j).rep (lub (J.image t)).rep := htL
  have heE : e j ∈ (J.filter fun j => e j ∉ (t j).supp).image e :=
    Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨hj, hej⟩, rfl⟩
  have heE' : e j ∉ (lub (J.image t)).rep → e j ∈ E' := fun h =>
    List.mem_filter.2 ⟨Finset.mem_toList.2 heE, by simpa using h⟩
  have hNmem : ∀ a ∈ (lub (J.image t)).rep, a ∉ (t j).rep →
      a ∈ J.biUnion fun j => (t j).supp \ g.supp := by
    intro a ha hat
    obtain ⟨k, hk, hak⟩ := (hL a).1 ha
    refine Finset.mem_biUnion.2 ⟨k, hk, Finset.mem_sdiff.2 ⟨mem_supp.2 hak, fun hag => hat ?_⟩⟩
    exact mem_supp.1 (supp_mono (hg j hj) hag)
  refine ⟨fun a ha => ?_, fun a b hab hb => ?_, fun a b hab hb ha hna => ?_⟩
  · rcases List.mem_append.1 ha with ha | ha
    · exact List.mem_append_left _ (htLp.1 a ha)
    · rw [List.mem_singleton] at ha; subst ha
      by_cases h : e j ∈ (lub (J.image t)).rep
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (heE' h)
  · rw [before_append] at hb ⊢
    rcases hb with hb | hb | ⟨ha, hb⟩
    · exact Or.inl (htLp.2.1 a b hab hb)
    · exact absurd hb (before_singleton _ _ _)
    · rw [List.mem_singleton] at hb; subst hb
      by_cases h : e j ∈ (lub (J.image t)).rep
      · exact Or.inl (htLp.2.2 (e j) a (Std.Symm.symm _ _ hab) ha h hej')
      · exact Or.inr (Or.inr ⟨htLp.1 a ha, heE' h⟩)
  · rw [List.mem_append, List.mem_singleton, not_or] at hna
    rcases List.mem_append.1 hb with hb | hb
    · rw [before_append]
      rcases List.mem_append.1 ha with ha | ha
      · exact Or.inl (htLp.2.2 a b hab hb ha hna.1)
      · exact Or.inr (Or.inr ⟨htLp.1 b hb, ha⟩)
    · rw [List.mem_singleton] at hb; subst hb
      exfalso
      refine hind a ?_ (e j) (Finset.mem_union_right _ heE) hna.2 hab
      rcases List.mem_append.1 ha with ha | ha
      · exact Finset.mem_union_left _ (hNmem a ha hna.1)
      · exact Finset.mem_union_right _ (hEmem a ha)

end Snoc

end NTrace

end Cslib.Mazurkiewicz
