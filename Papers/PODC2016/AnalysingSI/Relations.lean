import Mathlib

/-!
# Relational algebra for "Analysing Snapshot Isolation"

Generic facts about binary relations used in Cerone–Gotsman, *Analysing Snapshot Isolation*
(PODC 2016): acyclicity, maxima with respect to a relation, linear extensions of strict partial
orders, and **Lemma 15** — the closed form of the least solution of the system of relational
inequalities of Figure 3, stated for arbitrary relations `B` (standing for `SO ∪ WR ∪ WW`),
`A` (standing for `RW`) and `R` (the commit-order edges that are forced).

We write `R ∘r S` for the sequential composition `R ; S` of the paper and `ReflGen R` for `R?`.
-/

-- CSLib candidate: generic relation/walk lemmas (Cslib/Foundations/Data/Relation or Combinatorics)
namespace Podc.AnalysingSI

open Relation

variable {α : Type*}

/-- A relation is *acyclic* if its transitive closure is irreflexive. -/
def Acyclic (R : α → α → Prop) : Prop := ∀ a, ¬ TransGen R a a

/-- `a` is the maximum of the set `A` with respect to `R` (`max_R(A)` of the paper):
`a ∈ A` and every other element of `A` is `R`-below `a`. -/
def IsMaxBy (R : α → α → Prop) (A : α → Prop) (a : α) : Prop :=
  A a ∧ ∀ b, A b → b = a ∨ R b a

/-- The maximum w.r.t. an irreflexive transitive relation is unique. -/
theorem IsMaxBy.unique {R : α → α → Prop} {A : α → Prop} {a b : α}
    (hirr : ∀ a, ¬ R a a) (htr : ∀ a b c, R a b → R b c → R a c)
    (ha : IsMaxBy R A a) (hb : IsMaxBy R A b) : a = b := by
  rcases ha.2 b hb.1 with h | h
  · exact h.symm
  rcases hb.2 a ha.1 with h' | h'
  · exact h'
  exact absurd (htr _ _ _ h h') (hirr _)

theorem acyclic_of_le {R S : α → α → Prop} (h : R ≤ S) (hS : Acyclic S) : Acyclic R :=
  fun a ha => hS a (TransGen.mono (fun _ _ h' => h _ _ h') a a ha)

/-- A transitive irreflexive relation is acyclic. -/
theorem acyclic_of_trans_irrefl {R : α → α → Prop} (htr : ∀ a b c, R a b → R b c → R a c)
    (hirr : ∀ a, ¬ R a a) : Acyclic R := by
  intro a ha
  have : ∀ x y, TransGen R x y → R x y := by
    intro x y h
    induction h with
    | single h => exact h
    | tail _ h ih => exact htr _ _ _ ih h
  exact hirr a (this a a ha)

theorem transGen_of_trans {R : α → α → Prop} (htr : ∀ a b c, R a b → R b c → R a c)
    {a b : α} (h : TransGen R a b) : R a b := by
  induction h with
  | single h => exact h
  | tail _ h ih => exact htr _ _ _ ih h

/-- Every strict partial order is contained in a strict total order (Szpilrajn). -/
theorem exists_strictTotal_extension (R : α → α → Prop)
    (htr : ∀ a b c, R a b → R b c → R a c) (hirr : ∀ a, ¬ R a a) :
    ∃ L : α → α → Prop, R ≤ L ∧ (∀ a b c, L a b → L b c → L a c) ∧ (∀ a, ¬ L a a) ∧
      (∀ a b, a ≠ b → L a b ∨ L b a) := by
  classical
  let P : α → α → Prop := ReflGen R
  have hP : IsPartialOrder α P :=
    { refl := fun a => ReflGen.refl
      trans := by
        intro a b c hab hbc
        rcases hab with _ | hab
        · exact hbc
        rcases hbc with _ | hbc
        · exact ReflGen.single hab
        exact ReflGen.single (htr _ _ _ hab hbc)
      antisymm := by
        intro a b hab hba
        rcases hab with _ | hab
        · rfl
        rcases hba with _ | hba
        · rfl
        exact absurd (htr _ _ _ hab hba) (hirr _) }
  obtain ⟨s, hs, hPs⟩ := extend_partialOrder P
  refine ⟨fun a b => s a b ∧ a ≠ b, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact ⟨hPs _ _ (ReflGen.single h), fun e => hirr a (e ▸ h)⟩
  · rintro a b c ⟨hab, nab⟩ ⟨hbc, nbc⟩
    refine ⟨hs.trans _ _ _ hab hbc, ?_⟩
    rintro rfl
    exact nab (hs.antisymm _ _ hab hbc)
  · exact fun a h => h.2 rfl
  · intro a b hab
    rcases hs.total a b with h | h
    · exact Or.inl ⟨h, hab⟩
    · exact Or.inr ⟨h, Ne.symm hab⟩

/-! ### Lemma 15: the least solution of the system of Figure 3 -/

section Lemma15

variable (B A R : α → α → Prop)

/-- The generating relation `((SO ∪ WR ∪ WW) ; RW?) ∪ R` of Lemma 15. -/
def genRel : α → α → Prop := fun a b => Comp B (ReflGen A) a b ∨ R a b

/-- `VIS = (((SO ∪ WR ∪ WW) ; RW?) ∪ R)* ; (SO ∪ WR ∪ WW)`, equation (1). -/
def visSol : α → α → Prop := Comp (ReflTransGen (genRel B A R)) B

/-- `CO = (((SO ∪ WR ∪ WW) ; RW?) ∪ R)⁺`, equation (1). -/
def coSol : α → α → Prop := TransGen (genRel B A R)

/-- The system of inequalities of Figure 3 for a pre-execution `(VIS, CO)`, with
`B = SO ∪ WR ∪ WW` and `A = RW`. -/
structure IsSolution (VIS CO : α → α → Prop) : Prop where
  /-- (S1) `SO ∪ WR ∪ WW ⊆ VIS`. -/
  s1 : B ≤ VIS
  /-- (S2) `CO ; VIS ⊆ VIS`. -/
  s2 : ∀ a b c, CO a b → VIS b c → VIS a c
  /-- (S3) `VIS ⊆ CO`. -/
  s3 : VIS ≤ CO
  /-- (S4) `CO ; CO ⊆ CO`. -/
  s4 : ∀ a b c, CO a b → CO b c → CO a c
  /-- (S5) `VIS ; RW ⊆ CO`. -/
  s5 : ∀ a b c, VIS a b → A b c → CO a c

variable {B A R}

/-- **Lemma 15 (part 1)** of Cerone–Gotsman. The relations of equation (1) solve the system of
inequalities of Figure 3. -/
theorem isSolution_sol : IsSolution B A (visSol B A R) (coSol B A R) where
  s1 := fun a b h => ⟨a, ReflTransGen.refl, h⟩
  s2 := by
    rintro a b c hab ⟨d, hbd, hdc⟩
    exact ⟨d, (TransGen.to_reflTransGen hab).trans hbd, hdc⟩
  s3 := by
    rintro a b ⟨d, had, hdb⟩
    exact TransGen.tail' had (Or.inl ⟨b, hdb, ReflGen.refl⟩)
  s4 := fun _ _ _ hab hbc => hab.trans hbc
  s5 := by
    rintro a b c ⟨d, had, hdb⟩ hbc
    exact TransGen.tail' had (Or.inl ⟨b, hdb, ReflGen.single hbc⟩)

/-- **Lemma 15 (part 2)** of Cerone–Gotsman. The relations of equation (1) are the least solution
of the system of Figure 3 whose commit order contains `R`. -/
theorem sol_le {VIS CO : α → α → Prop} (h : IsSolution B A VIS CO) (hR : R ≤ CO) :
    visSol B A R ≤ VIS ∧ coSol B A R ≤ CO := by
  have hgen : genRel B A R ≤ CO := by
    rintro a b (⟨c, hac, hcb⟩ | hab)
    · rcases hcb with _ | hcb
      · exact h.s3 _ _ (h.s1 _ _ hac)
      · exact h.s5 _ _ _ (h.s1 _ _ hac) hcb
    · exact hR _ _ hab
  have hco : coSol B A R ≤ CO := by
    intro a b hab
    induction hab with
    | single hab => exact hgen _ _ hab
    | tail _ hbc ih => exact h.s4 _ _ _ ih (hgen _ _ hbc)
  refine ⟨?_, hco⟩
  rintro a b ⟨d, had, hdb⟩
  rcases had.cases_head with rfl | ⟨e, hae, hed⟩
  · exact h.s1 _ _ hdb
  · exact h.s2 _ _ _ (hco _ _ (TransGen.head' hae hed)) (h.s1 _ _ hdb)

/-- Lemma 15, both parts: `(VIS, CO)` of equation (1) is the least solution with `R ⊆ CO`. -/
theorem lemma15 :
    IsSolution B A (visSol B A R) (coSol B A R) ∧ R ≤ coSol B A R ∧
      ∀ VIS CO, IsSolution B A VIS CO → R ≤ CO →
        visSol B A R ≤ VIS ∧ coSol B A R ≤ CO :=
  ⟨isSolution_sol, fun _ _ h => TransGen.single (Or.inr h), fun _ _ h hR => sol_le h hR⟩

end Lemma15

end Podc.AnalysingSI
