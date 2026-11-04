import Mathlib

/-!
# Sequential specifications and Kosa's operation classes (Chapter II of the thesis)

A sequential specification is the set of legal sequences of operation instances
`(argument, return value) : I × R` (the argument `I` includes the operation type). We assume, as
everywhere in the thesis, that it is *deterministic* (Definition A.1) and, as is standard, that
legality is *prefix closed*.

Definitions B.1–B.3 (immediately non-commuting, non-self-commuting, strongly non-self-commuting),
C.1–C.2 (looks like, equivalent), D.1–D.4 (mutator, accessor, pure accessor).

Under the literal Definitions D.1, D.2 and D.4 no operation type is a pure accessor
(`not_pureAccessor`): an accessor `op` has a legal `ρ` with `ρ ∘ op` illegal, and then `ρ ∘ op`
is not equivalent to `ρ`, so `op` is a mutator. The intended notion (Kosa) only compares legal
sequences: `NonMutator` (for every legal `ρ ∘ op`, `ρ ∘ op` is equivalent to `ρ`).

Also: list lemmas used to read off the linearizations (`det_seq`, `legal_filter_of_nonMutator`,
`peel`).
-/

namespace Podc.SharedObjectTimeBounds

variable {I R : Type*} (legal : List (I × R) → Prop)

/-- Legality is prefix closed. -/
def PrefixClosed : Prop := ∀ l₁ l₂, legal (l₁ ++ l₂) → legal l₁

/-- Definition A.1 (deterministic object). -/
def Deterministic : Prop :=
  ∀ ρ (a : I) (r r' : R), legal (ρ ++ [(a, r)]) → legal (ρ ++ [(a, r')]) → r = r'

/-- Definition B.1 (immediately non-commuting operation types). -/
def ImmNonCommuting (OP₁ OP₂ : I → Prop) : Prop :=
  ∃ (ρ : List (I × R)) (o₁ o₂ : I × R), OP₁ o₁.1 ∧ OP₂ o₂.1 ∧ legal (ρ ++ [o₁]) ∧ legal (ρ ++ [o₂]) ∧
    (¬ legal (ρ ++ [o₁, o₂]) ∨ ¬ legal (ρ ++ [o₂, o₁]))

/-- Definition B.2 (immediately non-self-commuting). -/
def ImmNonSelfCommuting (OP : I → Prop) : Prop := ImmNonCommuting legal OP OP

/-- Immediately self-commuting = not immediately non-self-commuting. -/
def ImmSelfCommuting (OP : I → Prop) : Prop := ¬ ImmNonSelfCommuting legal OP

/-- Definition B.3 (strongly immediately non-self-commuting). -/
def StronglyImmNonSelfCommuting (OP : I → Prop) : Prop :=
  ∃ (ρ : List (I × R)) (o₁ o₂ : I × R), OP o₁.1 ∧ OP o₂.1 ∧ legal (ρ ++ [o₁]) ∧ legal (ρ ++ [o₂]) ∧
    ¬ legal (ρ ++ [o₁, o₂]) ∧ ¬ legal (ρ ++ [o₂, o₁])

/-- Definition C.1 (`ρ₁` looks like `ρ₂`). -/
def LooksLike (ρ₁ ρ₂ : List (I × R)) : Prop := ∀ ρ₃, legal (ρ₁ ++ ρ₃) → legal (ρ₂ ++ ρ₃)

/-- Definition C.2 (equivalent sequences). -/
def Equivalent (ρ₁ ρ₂ : List (I × R)) : Prop := LooksLike legal ρ₁ ρ₂ ∧ LooksLike legal ρ₂ ρ₁

/-- Definition D.1 (mutator), literal. -/
def Mutator (OP : I → Prop) : Prop := ∃ (ρ : List (I × R)) (o : I × R), OP o.1 ∧ ¬ Equivalent legal (ρ ++ [o]) ρ

/-- Definition D.2 (accessor). -/
def Accessor (OP : I → Prop) : Prop := ∃ (ρ : List (I × R)) (o : I × R), OP o.1 ∧ legal ρ ∧ ¬ legal (ρ ++ [o])

/-- Definition D.4 (pure accessor), literal. -/
def PureAccessor (OP : I → Prop) : Prop := Accessor legal OP ∧ ¬ Mutator legal OP

/-- Under the literal definitions there is no pure accessor. -/
theorem not_pureAccessor (OP : I → Prop) : ¬ PureAccessor legal OP := by
  rintro ⟨⟨ρ, o, hop, hρ, hno⟩, hnm⟩
  refine hnm ⟨ρ, o, hop, fun h => hno ?_⟩
  simpa using h.2 [] (by simpa using hρ)

/-- The intended "non-mutator" (Kosa): appending a legal instance gives an equivalent sequence. -/
def NonMutator (OP : I → Prop) : Prop :=
  ∀ ρ (o : I × R), OP o.1 → legal (ρ ++ [o]) → Equivalent legal (ρ ++ [o]) ρ

variable {legal}

theorem ImmSelfCommuting.comm {OP : I → Prop} (h : ImmSelfCommuting legal OP) {ρ}
    {o₁ o₂ : I × R} (h₁ : OP o₁.1) (h₂ : OP o₂.1) (l₁ : legal (ρ ++ [o₁]))
    (l₂ : legal (ρ ++ [o₂])) : legal (ρ ++ [o₁, o₂]) ∧ legal (ρ ++ [o₂, o₁]) := by
  by_contra hc
  exact h ⟨ρ, o₁, o₂, h₁, h₂, l₁, l₂, by tauto⟩

/-- Determinism for sequences: legal continuations of the same prefix with the same arguments
coincide. -/
theorem det_seq (hpc : PrefixClosed legal) (hdet : Deterministic legal) :
    ∀ (l₁ l₂ ρ : List (I × R)), legal (ρ ++ l₁) → legal (ρ ++ l₂) →
      l₁.map Prod.fst = l₂.map Prod.fst → l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | o₁ :: t₁, o₂ :: t₂, ρ, h₁, h₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have e1 : legal (ρ ++ [o₁]) := hpc _ t₁ (by simpa using h₁)
    have e2 : legal (ρ ++ [o₂]) := hpc _ t₂ (by simpa using h₂)
    have ho : o₁ = o₂ := by
      obtain ⟨a₁, r₁⟩ := o₁; obtain ⟨a₂, r₂⟩ := o₂
      simp only at h; obtain ⟨rfl, -⟩ := h
      rw [hdet ρ a₁ r₁ r₂ e1 e2]
    subst ho
    rw [det_seq hpc hdet t₁ t₂ (ρ ++ [o₁]) (by simpa using h₁) (by simpa using h₂) h.2]

/-- Removing instances of a non-mutator from a legal sequence keeps it legal. -/
theorem legal_erase_of_nonMutator (hpc : PrefixClosed legal) {AOP : I → Prop}
    (hA : NonMutator legal AOP) {x y : List (I × R)} {o : I × R} (ho : AOP o.1)
    (h : legal (x ++ o :: y)) : legal (x ++ y) := by
  have hx : legal (x ++ [o]) := hpc _ y (by simpa using h)
  exact (hA x o ho hx).1 y (by simpa using h)

theorem legal_filter_of_nonMutator (hpc : PrefixClosed legal) {AOP : I → Prop}
    (hA : NonMutator legal AOP) {α : Type*} (f : α → I × R) (keep : α → Bool) :
    ∀ (L : List α) (ρ : List (I × R)), legal (ρ ++ L.map f) →
      (∀ c ∈ L, keep c = false → AOP (f c).1) → legal (ρ ++ (L.filter keep).map f)
  | [], ρ, h, _ => by simpa using h
  | c :: L, ρ, h, hk => by
    by_cases hc : keep c = true
    · simp only [List.filter_cons, hc, if_true, List.map_cons]
      have := legal_filter_of_nonMutator hpc hA f keep L (ρ ++ [f c]) (by simpa using h)
        (fun c' hc' => hk c' (List.mem_cons_of_mem _ hc'))
      simpa using this
    · simp only [Bool.not_eq_true] at hc
      simp only [List.filter_cons, hc, List.map_cons]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact legal_filter_of_nonMutator hpc hA f keep L ρ
        (legal_erase_of_nonMutator hpc hA (hk c List.mem_cons_self hc) (by simpa using h))
        (fun c' hc' => hk c' (List.mem_cons_of_mem _ hc'))

/-! ## Reading off linearizations -/

theorem sublist_pair_cons {α : Type*} {a b x : α} {L : List α} (h : [a, b].Sublist (x :: L))
    (hax : a ≠ x) : [a, b].Sublist L := by
  rcases List.sublist_cons_iff.mp h with h | ⟨l, h1, h2⟩
  · exact h
  · simp only [List.cons.injEq] at h1; exact absurd h1.1 hax

theorem sublist_pair_append {α : Type*} {a b : α} :
    ∀ {X Y : List α}, [a, b].Sublist (X ++ Y) → a ∉ X → [a, b].Sublist Y
  | [], _, h, _ => h
  | x :: X, Y, h, hX => by
    have hax : a ≠ x := fun e => hX (e ▸ List.mem_cons_self)
    exact sublist_pair_append (sublist_pair_cons h hax) (fun h' => hX (List.mem_cons_of_mem _ h'))

/-- If every element of `X` precedes (in `L`) the later elements of `X` and all of `Y`, and `L` is
a duplicate-free permutation of `X ++ Y`, then `L` starts with `X`. -/
theorem peel {α : Type*} :
    ∀ (X : List α) (Y L : List α), L.Perm (X ++ Y) → L.Nodup →
      X.Pairwise (fun a b => [a, b].Sublist L) → (∀ x ∈ X, ∀ y ∈ Y, [x, y].Sublist L) →
      ∃ L', L = X ++ L' ∧ L'.Perm Y
  | [], Y, L, hp, _, _, _ => ⟨L, rfl, by simpa using hp⟩
  | x :: X, Y, L, hp, hnd, hpw, hxy => by
    -- the head of `L` is `x`
    have hxL : x ∈ L := hp.symm.subset List.mem_cons_self
    obtain ⟨z, L', rfl⟩ : ∃ z L', L = z :: L' := by
      cases L with
      | nil => simp at hxL
      | cons z L' => exact ⟨z, L', rfl⟩
    have hzx : z = x := by
      by_contra hne
      have hz : z ∈ X ++ Y := by
        have := hp.subset (List.mem_cons_self (a := z) (l := L'))
        simp only [List.cons_append, List.mem_cons] at this
        exact this.resolve_left hne
      have hpair : [x, z].Sublist (z :: L') := by
        rcases List.mem_append.mp hz with hz | hz
        · exact List.rel_of_pairwise_cons hpw hz
        · exact hxy x List.mem_cons_self z hz
      have := (sublist_pair_cons hpair (Ne.symm hne)).subset (by simp : z ∈ [x, z])
      exact (List.nodup_cons.mp hnd).1 this
    subst hzx
    have hp' : L'.Perm (X ++ Y) := by simpa using hp
    have hnd' := (List.nodup_cons.mp hnd).2
    have hzX : ∀ a ∈ X ++ Y, a ≠ z := fun a ha h => (List.nodup_cons.mp hnd).1 (h ▸ hp'.symm.subset ha)
    obtain ⟨L'', h1, h2⟩ := peel X Y L' hp' hnd'
      ((List.pairwise_cons.mp hpw).2.imp_of_mem fun ha _ hab =>
        sublist_pair_cons hab (hzX _ (List.mem_append_left _ ha)))
      (fun a ha b hb => sublist_pair_cons (hxy a (List.mem_cons_of_mem _ ha) b hb)
        (hzX _ (List.mem_append_left _ ha)))
    exact ⟨L'', by rw [h1]; rfl, h2⟩

end Podc.SharedObjectTimeBounds
