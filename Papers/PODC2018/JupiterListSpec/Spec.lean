import Mathlib

/-!
# Abstract executions and the replicated list specifications (Sections 2.2–2.3)

The framework of Burckhardt et al. as used by Attiya et al. (PODC 2016) and by the paper:
an abstract execution `A = (H, vis)` is a sequence `H` of `do` events with a visibility relation
(here on positions in `H`). `Weak A` is the weak list specification `A_weak` (Definition 1) and
`Conv A` the convergence property `A_cp`.

`Weak.conv` shows that `A_weak ⊆ A_cp`: two `Read`s that see the same list updates return the same
list (the paper derives the convergence of CJupiter, Theorem 11, separately).
-/

namespace Podc.JupiterListSpec

/-- The signature of a user operation as recorded in a `do` event (Section 2.3): `Ins(a, k)`,
`Del(a, k)` (with the deleted element `a`, or `none` if the list was empty) and `Read`. -/
inductive Sig (E : Type) where
  | ins (a : E) (k : ℕ)
  | del (a : Option E) (k : ℕ)
  | read
  deriving DecidableEq, Repr

/-- A `do(o, w)` event at replica `rep`. -/
structure DoEv (R E : Type) where
  rep : R
  sig : Sig E
  ret : List E

/-- An abstract execution `(H, vis)`; `vis i j` means that event `H[i]` is visible to `H[j]`. -/
structure AbsExec (R E : Type) where
  H : List (DoEv R E)
  vis : ℕ → ℕ → Prop

variable {R E : Type}

namespace AbsExec

variable (A : AbsExec R E)

/-- Well-formedness of an abstract execution (Section 2.2): `vis` contains the per-replica order,
goes forward in `H`, and is transitive (hence acyclic). -/
def WF : Prop :=
  (∀ i j (hi : i < A.H.length) (hj : j < A.H.length), i < j → A.H[i].rep = A.H[j].rep →
      A.vis i j) ∧
    (∀ i j, A.vis i j → i < j ∧ j < A.H.length) ∧
    (∀ i j k, A.vis i j → A.vis j k → A.vis i k)

/-- `≤vis`. -/
def visLe (i j : ℕ) : Prop := i = j ∨ A.vis i j

/-- `elems(A)`: the inserted elements. -/
def elems : Set E := {a | ∃ e ∈ A.H, ∃ k, e.sig = .ins a k}

/-- **Definition 1 (weak list specification `A_weak`).** -/
def Weak : Prop :=
  ∃ lo : E → E → Prop, (∀ a b, lo a b → a ∈ A.elems ∧ b ∈ A.elems) ∧
    (∀ i (hi : i < A.H.length),
      -- 1(a)
      (∀ a, a ∈ A.H[i].ret ↔
        (∃ j, A.visLe j i ∧ ∃ e ∈ A.H[j]?, ∃ k, e.sig = .ins a k) ∧
          ¬ ∃ j, A.visLe j i ∧ ∃ e ∈ A.H[j]?, ∃ k, e.sig = .del (some a) k) ∧
      -- 1(b)
      A.H[i].ret.Pairwise lo ∧
      -- 1(c)
      (∀ a k, A.H[i].sig = .ins a k → A.H[i].ret[min k (A.H[i].ret.length - 1)]? = some a)) ∧
    -- 2
    (∀ a, ¬ lo a a) ∧
    (∀ i (hi : i < A.H.length), ∀ a b c, a ∈ A.H[i].ret → b ∈ A.H[i].ret → c ∈ A.H[i].ret →
      lo a b → lo b c → lo a c) ∧
    (∀ i (hi : i < A.H.length), ∀ a b, a ∈ A.H[i].ret → b ∈ A.H[i].ret → a ≠ b →
      lo a b ∨ lo b a)

/-- `H[j]` is a list update (`Ins` or `Del`). -/
def IsUpdate (j : ℕ) : Prop := ∃ e ∈ A.H[j]?, e.sig ≠ .read

/-- **The convergence property `A_cp`** (Section 2.3): two `Read`s that see the same set of list
updates return the same list. -/
def Conv : Prop :=
  ∀ i₁ i₂ (h₁ : i₁ < A.H.length) (h₂ : i₂ < A.H.length), A.H[i₁].sig = .read →
    A.H[i₂].sig = .read → (∀ j, A.IsUpdate j → (A.vis j i₁ ↔ A.vis j i₂)) →
    A.H[i₁].ret = A.H[i₂].ret

/-- `A_weak ⊆ A_cp`. -/
theorem Weak.conv [DecidableEq E] {A : AbsExec R E} (hw : A.Weak) : A.Conv := by
  obtain ⟨lo, -, h1, hirr, htr, -⟩ := hw
  intro i₁ i₂ hi₁ hi₂ hr₁ hr₂ hvis
  have hmem : ∀ a, a ∈ A.H[i₁].ret ↔ a ∈ A.H[i₂].ret := by
    intro a
    have key : ∀ (s : Sig E), s ≠ .read → ∀ j, (A.visLe j i₁ ∧ ∃ e ∈ A.H[j]?, e.sig = s) ↔
        (A.visLe j i₂ ∧ ∃ e ∈ A.H[j]?, e.sig = s) := by
      intro s hs j
      constructor
      · rintro ⟨hv, e, he, rfl⟩
        refine ⟨Or.inr ?_, e, he, rfl⟩
        rcases hv with rfl | hv
        · simp only [List.getElem?_eq_getElem hi₁, Option.mem_def, Option.some.injEq] at he
          exact absurd (he ▸ hr₁) hs
        · exact (hvis j ⟨e, he, hs⟩).1 hv
      · rintro ⟨hv, e, he, rfl⟩
        refine ⟨Or.inr ?_, e, he, rfl⟩
        rcases hv with rfl | hv
        · simp only [List.getElem?_eq_getElem hi₂, Option.mem_def, Option.some.injEq] at he
          exact absurd (he ▸ hr₂) hs
        · exact (hvis j ⟨e, he, hs⟩).2 hv
    rw [(h1 i₁ hi₁).1 a, (h1 i₂ hi₂).1 a]
    have kI : ∀ k, (∃ j, A.visLe j i₁ ∧ ∃ e ∈ A.H[j]?, e.sig = .ins a k) ↔
        (∃ j, A.visLe j i₂ ∧ ∃ e ∈ A.H[j]?, e.sig = .ins a k) :=
      fun k => exists_congr (fun j => key _ (by simp) j)
    have kD : ∀ k, (∃ j, A.visLe j i₁ ∧ ∃ e ∈ A.H[j]?, e.sig = .del (some a) k) ↔
        (∃ j, A.visLe j i₂ ∧ ∃ e ∈ A.H[j]?, e.sig = .del (some a) k) :=
      fun k => exists_congr (fun j => key _ (by simp) j)
    constructor
    · rintro ⟨⟨j, hj, e, he, k, hk⟩, hn⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨j', hj', e', he', hk'⟩ := (kI k).1 ⟨j, hj, e, he, hk⟩
        exact ⟨j', hj', e', he', k, hk'⟩
      · rintro ⟨j, hj, e, he, k, hk⟩
        obtain ⟨j', hj', e', he', hk'⟩ := (kD k).2 ⟨j, hj, e, he, hk⟩
        exact hn ⟨j', hj', e', he', k, hk'⟩
    · rintro ⟨⟨j, hj, e, he, k, hk⟩, hn⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨j', hj', e', he', hk'⟩ := (kI k).2 ⟨j, hj, e, he, hk⟩
        exact ⟨j', hj', e', he', k, hk'⟩
      · rintro ⟨j, hj, e, he, k, hk⟩
        obtain ⟨j', hj', e', he', hk'⟩ := (kD k).1 ⟨j, hj, e, he, hk⟩
        exact hn ⟨j', hj', e', he', k, hk'⟩
  have hnd : ∀ i (hi : i < A.H.length), A.H[i].ret.Nodup := by
    intro i hi
    refine List.Pairwise.imp ?_ (h1 i hi).2.1
    rintro a b hab rfl; exact hirr a hab
  apply List.Perm.eq_of_pairwise _ (h1 i₁ hi₁).2.1 (h1 i₂ hi₂).2.1
  · exact List.perm_of_nodup_nodup_toFinset_eq (hnd _ hi₁) (hnd _ hi₂)
      (by ext a; simp [hmem a])
  · intro a b ha hb hab hba
    by_contra hne
    exact hirr a (htr i₁ hi₁ a b a ha ((hmem b).2 hb) ha hab hba)

end AbsExec

/-! ### Order of elements in duplicate-free lists -/

theorem List.pair_sublist_trans {l : List E} (hl : l.Nodup) {a b c : E}
    (h₁ : [a, b].Sublist l) (h₂ : [b, c].Sublist l) : [a, c].Sublist l := by
  induction l with
  | nil => simp at h₁
  | cons d t ih =>
    rw [List.nodup_cons] at hl
    rw [List.sublist_cons_iff] at h₁ h₂
    rcases h₁ with h₁ | ⟨r, hr, h₁⟩ <;> rcases h₂ with h₂ | ⟨r', hr', h₂⟩
    · exact (ih hl.2 h₁ h₂).cons d
    · simp only [List.cons.injEq] at hr'; obtain ⟨rfl, rfl⟩ := hr'
      exact absurd (h₁.subset (by simp)) hl.1
    · simp only [List.cons.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
      exact List.cons_sublist_cons.2 (List.singleton_sublist.2 (h₂.subset (by simp)))
    · simp only [List.cons.injEq] at hr hr'; obtain ⟨rfl, rfl⟩ := hr; obtain ⟨rfl, -⟩ := hr'
      exact absurd (h₁.subset (by simp)) hl.1

theorem List.pair_sublist_total {l : List E} {a b : E} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    [a, b].Sublist l ∨ [b, a].Sublist l := by
  induction l with
  | nil => simp at ha
  | cons d t ih =>
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hab
    · exact Or.inl (List.cons_sublist_cons.2 (List.singleton_sublist.2 hb'))
    · exact Or.inr (List.cons_sublist_cons.2 (List.singleton_sublist.2 ha'))
    · rcases ih ha' hb' with h | h
      · exact Or.inl (h.cons d)
      · exact Or.inr (h.cons d)

end Podc.JupiterListSpec
