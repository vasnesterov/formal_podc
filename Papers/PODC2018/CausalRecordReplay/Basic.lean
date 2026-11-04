import Mathlib

/-!
# Relations on a finite set: covers, chains, strict total orders

Generic facts used throughout the formalization of Jones–Khan–Vaidya, *Optimal Record and Replay
under Causal Consistency* (PODC 2018):

* `Cov r` is the cover relation (the paper's transitive reduction `r̂`) of a relation `r`;
  for a strict partial order on a finite type it is the least relation whose transitive closure is
  `r` (`transGen_cov_eq`, `cov_le_of_transGen_eq`), so the paper's "(unique) transitive reduction"
  is well defined;
* chain induction along covers (`chain_induction`);
* strict total orders on a subset (`IsStrictTotalOn`) and their basic properties;
* one-step linear extension of a strict partial order (`addPair`).

-- CSLib candidate: Cslib/Foundations/Order/Cover.lean
-/

namespace Podc.CausalRecordReplay

open Relation

variable {α : Type*}

/-- The cover relation of `r`: `a ⋖ b` iff `a <ᵣ b` and nothing lies strictly in between. For a
strict partial order on a finite set this is its (unique) transitive reduction `r̂`. -/
def Cov (r : α → α → Prop) (a b : α) : Prop := r a b ∧ ∀ c, r a c → ¬ r c b

/-- Transitivity of a relation (with strict-implicit binders, convenient as an argument). -/
def TransRel (r : α → α → Prop) : Prop := ∀ ⦃a b c⦄, r a b → r b c → r a c

/-- A strict partial order (irreflexive and transitive), as two explicit fields. -/
structure IsStrictPO (r : α → α → Prop) : Prop where
  irrefl : ∀ a, ¬ r a a
  trans : ∀ {a b c}, r a b → r b c → r a c

/-- `r` is a strict total order on the subset `S` (and relates only elements of `S`). -/
structure IsStrictTotalOn (S : α → Prop) (r : α → α → Prop) : Prop where
  supp : ∀ {a b}, r a b → S a ∧ S b
  irrefl : ∀ a, ¬ r a a
  trans : ∀ {a b c}, r a b → r b c → r a c
  total : ∀ {a b}, S a → S b → a ≠ b → r a b ∨ r b a

namespace IsStrictTotalOn

variable {S : α → Prop} {r : α → α → Prop}

theorem toStrictPO (h : IsStrictTotalOn S r) : IsStrictPO r := ⟨h.irrefl, h.trans⟩

theorem asymm (h : IsStrictTotalOn S r) {a b : α} (hab : r a b) : ¬ r b a :=
  fun hba => h.irrefl a (h.trans hab hba)

theorem ne (h : IsStrictTotalOn S r) {a b : α} (hab : r a b) : a ≠ b := by
  rintro rfl; exact h.irrefl a hab

/-- In a strict total order, `¬ a < b` for two distinct elements of `S` means `b < a`. -/
theorem of_not (h : IsStrictTotalOn S r) {a b : α} (ha : S a) (hb : S b) (hne : a ≠ b)
    (hn : ¬ r a b) : r b a :=
  (h.total ha hb hne).resolve_left hn

/-- Two strict total orders on the same subset, one contained in the other, are equal. -/
theorem eq_of_le {s : α → α → Prop} (hr : IsStrictTotalOn S r) (hs : IsStrictTotalOn S s)
    (hle : ∀ a b, r a b → s a b) : r = s := by
  funext a b
  apply propext
  refine ⟨hle a b, fun hab => ?_⟩
  obtain ⟨ha, hb⟩ := hs.supp hab
  by_contra hn
  have := hr.of_not ha hb (hs.ne hab) hn
  exact hs.asymm hab (hle _ _ this)

end IsStrictTotalOn

section Cov

variable {r : α → α → Prop}

theorem Cov.rel {a b : α} (h : Cov r a b) : r a b := h.1

/-- A cover of a transitive closure is a single step of the generating relation. -/
theorem cov_transGen {g : α → α → Prop} {a b : α} (h : Cov (TransGen g) a b) : g a b := by
  obtain ⟨hab, hmin⟩ := h
  obtain ⟨c, hac, hcb⟩ := TransGen.head'_iff.mp hab
  rcases hcb.cases_head with rfl | ⟨d, hcd, hdb⟩
  · exact hac
  · exact absurd (TransGen.head' hcd hdb) (hmin c (TransGen.single hac))

/-- Every pair of a strict partial order on a finite type is joined by a chain of covers. -/
theorem transGen_cov [Finite α] (hr : IsStrictPO r) {a b : α} (hab : r a b) :
    TransGen (Cov r) a b := by
  suffices H : ∀ n, ∀ a b, Set.ncard {c | r a c ∧ r c b} = n → r a b → TransGen (Cov r) a b from
    H _ a b rfl hab
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab
    by_cases hc : ∃ c, r a c ∧ r c b
    · obtain ⟨c, hac, hcb⟩ := hc
      have hsub1 : {d | r a d ∧ r d c} ⊂ {d | r a d ∧ r d b} := by
        refine ⟨fun d hd => ⟨hd.1, hr.trans hd.2 hcb⟩, fun hsub => ?_⟩
        exact hr.irrefl c (hsub ⟨hac, hcb⟩).2
      have hsub2 : {d | r c d ∧ r d b} ⊂ {d | r a d ∧ r d b} := by
        refine ⟨fun d hd => ⟨hr.trans hac hd.1, hd.2⟩, fun hsub => ?_⟩
        exact hr.irrefl c (hsub ⟨hac, hcb⟩).1
      have h1 := Set.ncard_lt_ncard hsub1
      have h2 := Set.ncard_lt_ncard hsub2
      exact (ih _ (hn ▸ h1) a c rfl hac).trans (ih _ (hn ▸ h2) c b rfl hcb)
    · exact TransGen.single ⟨hab, fun c hac hcb => hc ⟨c, hac, hcb⟩⟩

/-- The transitive closure of the cover relation of a finite strict partial order is the order. -/
theorem transGen_cov_eq [Finite α] (hr : IsStrictPO r) : TransGen (Cov r) = r := by
  funext a b
  apply propext
  refine ⟨fun h => ?_, transGen_cov hr⟩
  induction h with
  | single h => exact h.1
  | tail _ h ih => exact hr.trans ih h.1

/-- The cover relation is contained in every relation whose transitive closure is `r`: it is the
unique minimal "transitive reduction". -/
theorem cov_le_of_transGen_eq {s : α → α → Prop} (hs : TransGen s = r) {a b : α}
    (h : Cov r a b) : s a b := by
  rw [← hs] at h
  exact cov_transGen h

/-- Chain induction: to prove `Q b` for `a <ᵣ b`, prove `Q a` and propagate `Q` along each cover
`x ⋖ y` with `a ≤ x` and `y ≤ b`. -/
theorem chain_induction [Finite α] (hr : IsStrictPO r) {a b : α} (hab : r a b) (Q : α → Prop)
    (h0 : Q a) (hs : ∀ x y, ReflGen r a x → Cov r x y → ReflGen r y b → Q x → Q y) : Q b := by
  have key : ∀ y, TransGen (Cov r) a y → ReflGen r y b → Q y := by
    intro y hy
    induction hy with
    | single h => exact fun hyb => hs a _ ReflGen.refl h hyb h0
    | @tail x y hax hxy ih =>
      intro hyb
      have hxb : ReflGen r x b := by
        rcases hyb with _ | hyb
        · exact ReflGen.single hxy.1
        · exact ReflGen.single (hr.trans hxy.1 hyb)
      have hax' : r a x := (transGen_cov_eq hr) ▸ hax
      exact hs x y (ReflGen.single hax') hxy hyb (ih hxb)
  exact key b (transGen_cov hr hab) ReflGen.refl

end Cov

/-- `ReflGen` of a transitive relation is transitive. -/
theorem reflGen_trans {r : α → α → Prop} (htr : TransRel r) {a b c : α}
    (h1 : ReflGen r a b) (h2 : ReflGen r b c) : ReflGen r a c := by
  rcases h1 with _ | h1
  · exact h2
  rcases h2 with _ | h2
  · exact ReflGen.single h1
  · exact ReflGen.single (htr h1 h2)

theorem reflGen_trans_left {r : α → α → Prop} (htr : TransRel r) {a b c : α}
    (h1 : ReflGen r a b) (h2 : r b c) : r a c := by
  rcases h1 with _ | h1
  · exact h2
  · exact htr h1 h2

theorem reflGen_trans_right {r : α → α → Prop} (htr : TransRel r)
    {a b c : α} (h1 : r a b) (h2 : ReflGen r b c) : r a c := by
  rcases h2 with _ | h2
  · exact h1
  · exact htr h1 h2

theorem reflGen_of_ne {r : α → α → Prop} {a b : α} (h : ReflGen r a b) (hne : a ≠ b) : r a b := by
  rcases h with _ | h
  · exact absurd rfl hne
  · exact h

theorem transGen_mono' {r s : α → α → Prop} (h : ∀ a b, r a b → s a b) {a b : α}
    (hab : TransGen r a b) : TransGen s a b := by
  induction hab with
  | single h' => exact TransGen.single (h _ _ h')
  | tail _ h' ih => exact TransGen.tail ih (h _ _ h')

theorem of_transGen_of_trans {r : α → α → Prop} (htr : TransRel r) {a b : α}
    (hab : TransGen r a b) : r a b := by
  induction hab with
  | single h => exact h
  | tail _ h ih => exact htr ih h

theorem reflTransGen_mono' {r s : α → α → Prop} (h : ∀ a b, r a b → s a b) {a b : α}
    (hab : ReflTransGen r a b) : ReflTransGen s a b := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail _ h' ih => exact ReflTransGen.tail ih (h _ _ h')

/-- Well-founded induction along a strict partial order on a finite type. -/
theorem IsStrictPO.transitive {r : α → α → Prop} (hr : IsStrictPO r) : TransRel r :=
  fun _ _ _ => hr.trans

theorem IsStrictPO.wellFounded [Finite α] {r : α → α → Prop} (hr : IsStrictPO r) :
    WellFounded r :=
  @Finite.wellFounded_of_trans_of_irrefl α _ r ⟨fun _ _ _ => hr.trans⟩ ⟨hr.irrefl⟩

/-- The reverse of a strict partial order is a strict partial order. -/
theorem IsStrictPO.swap {r : α → α → Prop} (hr : IsStrictPO r) : IsStrictPO (fun a b => r b a) :=
  ⟨hr.irrefl, fun h1 h2 => hr.trans h2 h1⟩

section AddPair

/-- One-step extension of a transitive relation `r` by the pair `(a, b)`: the transitive closure of
`r ∪ {(a, b)}`. -/
def addPair (r : α → α → Prop) (a b : α) (x y : α) : Prop :=
  r x y ∨ (ReflGen r x a ∧ ReflGen r b y)

variable {r : α → α → Prop}

theorem le_addPair {a b x y : α} (h : r x y) : addPair r a b x y := Or.inl h

theorem addPair_self (a b : α) : addPair r a b a b := Or.inr ⟨ReflGen.refl, ReflGen.refl⟩

theorem addPair_strictPO (hr : IsStrictPO r) {a b : α} (hne : a ≠ b) (hba : ¬ r b a) :
    IsStrictPO (addPair r a b) := by
  have hrt : TransRel r := fun _ _ _ => hr.trans
  refine ⟨fun x hx => ?_, fun {x y z} hxy hyz => ?_⟩
  · rcases hx with hx | ⟨hxa, hbx⟩
    · exact hr.irrefl x hx
    · rcases reflGen_trans hrt hbx hxa with _ | h
      · exact hne rfl
      · exact hba h
  · rcases hxy with hxy | ⟨hxa, hby⟩ <;> rcases hyz with hyz | ⟨hya, hbz⟩
    · exact Or.inl (hr.trans hxy hyz)
    · exact Or.inr ⟨ReflGen.single (reflGen_trans_right hrt hxy hya), hbz⟩
    · exact Or.inr ⟨hxa, reflGen_trans hrt hby (ReflGen.single hyz)⟩
    · exfalso
      rcases reflGen_trans hrt hby hya with _ | h
      · exact hne rfl
      · exact hba h

end AddPair

end Podc.CausalRecordReplay
