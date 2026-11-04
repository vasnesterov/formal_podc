import Cslib.Computability.Distributed.SharedMemory.History

/-!
# Histories obtained by projecting event lists

A list of events `α : List E` of any type, together with a partial labelling
`f : E → Option (Label P A)`, induces the CSLib history `α.filterMap f`. This file characterizes
CSLib's notions on such a history (`Invoked`, `Completed`, `opOf`, `respOf`, `Precedes`) in terms
of *positions* in `α`: `IsInv f α x e` says that event `e` of `α` is the invocation of the instance
`x`, `IsRet f α x r` that event `r` is its response. Real-time order then becomes a comparison of
positions (`precedes_of_lt`, `lt_of_precedes`).

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Projection.lean
-/

namespace Podc.WritableObjects

open Cslib.SharedMemory

variable {E P : Type} {A : ObjSpec} [DecidableEq P]

/-- Event `e` of `α` is the invocation of the instance `x` in the projected history. -/
def IsInv (f : E → Option (Label P A)) (α : List E) (x : OpId P) (e : ℕ) : Prop :=
  ∃ (h : e < α.length) (o : A.Op), f α[e] = some (.inv x.1 o) ∧
    (opsOf ((α.take e).filterMap f) x.1).length = x.2

/-- Event `r` of `α` is the response of the instance `x` in the projected history. -/
def IsRet (f : E → Option (Label P A)) (α : List E) (x : OpId P) (r : ℕ) : Prop :=
  ∃ (h : r < α.length) (v : A.Resp), f α[r] = some (.ret x.1 v) ∧
    (respsOf ((α.take r).filterMap f) x.1).length = x.2

variable (f : E → Option (Label P A))

omit [DecidableEq P] in

lemma filterMap_take_succ (α : List E) {t : ℕ} (ht : t < α.length) :
    (α.take (t + 1)).filterMap f = (α.take t).filterMap f ++ (f α[t]).toList := by
  rw [List.take_add_one, List.filterMap_append, List.getElem?_eq_getElem ht]
  cases h : f α[t] <;> simp [h]

lemma opsOf_toList (o : Option (Label P A)) (p : P) :
    opsOf o.toList p = (o.bind (Label.invOf p)).toList := by
  cases o with
  | none => rfl
  | some l => cases h : l.invOf p <;> simp [opsOf, h]

lemma respsOf_toList (o : Option (Label P A)) (p : P) :
    respsOf o.toList p = (o.bind (Label.retOf p)).toList := by
  cases o with
  | none => rfl
  | some l => cases h : l.retOf p <;> simp [respsOf, h]

lemma invOf_eq_some_iff {ℓ : Label P A} {p : P} {o : A.Op} :
    ℓ.invOf p = some o ↔ ℓ = .inv p o := by
  cases ℓ <;> simp [Label.invOf]

lemma retOf_eq_some_iff {ℓ : Label P A} {p : P} {r : A.Resp} :
    ℓ.retOf p = some r ↔ ℓ = .ret p r := by
  cases ℓ <;> simp [Label.retOf]

/-- The operations of `p` in a prefix of length `t`, described by positions. -/
lemma opOf_take_iff (α : List E) (t : ℕ) (x : OpId P) (o : A.Op) :
    opOf ((α.take t).filterMap f) x = some o ↔
      ∃ (e : ℕ) (h : e < α.length), e < t ∧ f α[e] = some (.inv x.1 o) ∧
        (opsOf ((α.take e).filterMap f) x.1).length = x.2 := by
  induction t with
  | zero => simp [opOf]
  | succ t ih =>
    by_cases ht : t < α.length
    · rw [filterMap_take_succ f α ht]
      simp only [opOf, opsOf_append, opsOf_toList] at ih ⊢
      constructor
      · intro h
        rcases lt_or_ge x.2 (opsOf ((α.take t).filterMap f) x.1).length with hl | hl
        · rw [List.getElem?_append_left hl] at h
          obtain ⟨e, he, het, h1, h2⟩ := ih.1 h
          exact ⟨e, he, by omega, h1, h2⟩
        · rw [List.getElem?_append_right hl] at h
          cases hf : f α[t] with
          | none => simp [hf] at h
          | some ℓ =>
            simp only [hf, Option.bind_some] at h
            cases hi : ℓ.invOf x.1 with
            | none => simp [hi] at h
            | some o' =>
              simp only [hi, Option.toList_some] at h
              have h0 : x.2 - (opsOf ((α.take t).filterMap f) x.1).length = 0 := by
                by_contra hne
                rw [List.getElem?_eq_none (by simp; omega)] at h
                simp at h
              rw [h0] at h
              simp only [List.getElem?_cons_zero, Option.some.injEq] at h
              subst h
              rw [invOf_eq_some_iff] at hi
              exact ⟨t, ht, by omega, by rw [hf, hi], by omega⟩
      · rintro ⟨e, he, het, h1, h2⟩
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 het) with het | rfl
        · have := ih.2 ⟨e, he, het, h1, h2⟩
          rw [List.getElem?_append_left (by
            by_contra hc
            rw [List.getElem?_eq_none (by omega)] at this
            simp at this)]
          exact this
        · rw [List.getElem?_append_right (by omega), h2]
          simp [h1]
    · have h1 : α.take (t + 1) = α.take t := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      rw [h1, ih]
      constructor
      · rintro ⟨e, he, het, h⟩; exact ⟨e, he, by omega, h⟩
      · rintro ⟨e, he, het, h⟩; exact ⟨e, he, by omega, h⟩

/-- The responses of `p` in a prefix of length `t`, described by positions. -/
lemma respOf_take_iff (α : List E) (t : ℕ) (x : OpId P) (v : A.Resp) :
    respOf ((α.take t).filterMap f) x = some v ↔
      ∃ (r : ℕ) (h : r < α.length), r < t ∧ f α[r] = some (.ret x.1 v) ∧
        (respsOf ((α.take r).filterMap f) x.1).length = x.2 := by
  induction t with
  | zero => simp [respOf]
  | succ t ih =>
    by_cases ht : t < α.length
    · rw [filterMap_take_succ f α ht]
      simp only [respOf, respsOf_append, respsOf_toList] at ih ⊢
      constructor
      · intro h
        rcases lt_or_ge x.2 (respsOf ((α.take t).filterMap f) x.1).length with hl | hl
        · rw [List.getElem?_append_left hl] at h
          obtain ⟨e, he, het, h1, h2⟩ := ih.1 h
          exact ⟨e, he, by omega, h1, h2⟩
        · rw [List.getElem?_append_right hl] at h
          cases hf : f α[t] with
          | none => simp [hf] at h
          | some ℓ =>
            simp only [hf, Option.bind_some] at h
            cases hi : ℓ.retOf x.1 with
            | none => simp [hi] at h
            | some o' =>
              simp only [hi, Option.toList_some] at h
              have h0 : x.2 - (respsOf ((α.take t).filterMap f) x.1).length = 0 := by
                by_contra hne
                rw [List.getElem?_eq_none (by simp; omega)] at h
                simp at h
              rw [h0] at h
              simp only [List.getElem?_cons_zero, Option.some.injEq] at h
              subst h
              rw [retOf_eq_some_iff] at hi
              exact ⟨t, ht, by omega, by rw [hf, hi], by omega⟩
      · rintro ⟨e, he, het, h1, h2⟩
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 het) with het | rfl
        · have := ih.2 ⟨e, he, het, h1, h2⟩
          rw [List.getElem?_append_left (by
            by_contra hc
            rw [List.getElem?_eq_none (by omega)] at this
            simp at this)]
          exact this
        · rw [List.getElem?_append_right (by omega), h2]
          simp [h1]
    · have h1 : α.take (t + 1) = α.take t := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      rw [h1, ih]
      constructor
      · rintro ⟨e, he, het, h⟩; exact ⟨e, he, by omega, h⟩
      · rintro ⟨e, he, het, h⟩; exact ⟨e, he, by omega, h⟩

lemma opOf_iff (α : List E) (x : OpId P) (o : A.Op) :
    opOf (α.filterMap f) x = some o ↔
      ∃ (e : ℕ) (h : e < α.length), f α[e] = some (.inv x.1 o) ∧
        (opsOf ((α.take e).filterMap f) x.1).length = x.2 := by
  have := opOf_take_iff f α α.length x o
  rw [List.take_length] at this
  rw [this]
  constructor
  · rintro ⟨e, he, -, h⟩; exact ⟨e, he, h⟩
  · rintro ⟨e, he, h⟩; exact ⟨e, he, he, h⟩

lemma respOf_iff (α : List E) (x : OpId P) (v : A.Resp) :
    respOf (α.filterMap f) x = some v ↔
      ∃ (r : ℕ) (h : r < α.length), f α[r] = some (.ret x.1 v) ∧
        (respsOf ((α.take r).filterMap f) x.1).length = x.2 := by
  have := respOf_take_iff f α α.length x v
  rw [List.take_length] at this
  rw [this]
  constructor
  · rintro ⟨e, he, -, h⟩; exact ⟨e, he, h⟩
  · rintro ⟨e, he, h⟩; exact ⟨e, he, he, h⟩

lemma invoked_iff_opOf {h : List (Label P A)} {x : OpId P} :
    Invoked h x ↔ ∃ o, opOf h x = some o := by
  simp only [Invoked, opOf]
  constructor
  · intro hx; exact ⟨_, List.getElem?_eq_getElem hx⟩
  · rintro ⟨o, ho⟩
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at ho
    simp at ho

lemma completed_iff_respOf {h : List (Label P A)} {x : OpId P} :
    Completed h x ↔ ∃ v, respOf h x = some v := by
  simp only [Completed, respOf]
  constructor
  · intro hx; exact ⟨_, List.getElem?_eq_getElem hx⟩
  · rintro ⟨o, ho⟩
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at ho
    simp at ho

lemma invoked_take_iff (α : List E) (t : ℕ) (x : OpId P) :
    Invoked ((α.take t).filterMap f) x ↔ ∃ e < t, IsInv f α x e := by
  rw [invoked_iff_opOf]
  simp only [opOf_take_iff, IsInv]
  constructor
  · rintro ⟨o, e, he, het, h1, h2⟩; exact ⟨e, het, he, o, h1, h2⟩
  · rintro ⟨e, het, he, o, h1, h2⟩; exact ⟨o, e, he, het, h1, h2⟩

lemma completed_take_iff (α : List E) (t : ℕ) (x : OpId P) :
    Completed ((α.take t).filterMap f) x ↔ ∃ r < t, IsRet f α x r := by
  rw [completed_iff_respOf]
  simp only [respOf_take_iff, IsRet]
  constructor
  · rintro ⟨o, e, he, het, h1, h2⟩; exact ⟨e, het, he, o, h1, h2⟩
  · rintro ⟨e, het, he, o, h1, h2⟩; exact ⟨o, e, he, het, h1, h2⟩

lemma invoked_iff (α : List E) (x : OpId P) :
    Invoked (α.filterMap f) x ↔ ∃ e, IsInv f α x e := by
  have := invoked_take_iff f α α.length x
  rw [List.take_length] at this
  rw [this]
  exact ⟨fun ⟨e, _, h⟩ => ⟨e, h⟩, fun ⟨e, h⟩ => ⟨e, h.1, h⟩⟩

lemma completed_iff (α : List E) (x : OpId P) :
    Completed (α.filterMap f) x ↔ ∃ r, IsRet f α x r := by
  have := completed_take_iff f α α.length x
  rw [List.take_length] at this
  rw [this]
  exact ⟨fun ⟨e, _, h⟩ => ⟨e, h⟩, fun ⟨e, h⟩ => ⟨e, h.1, h⟩⟩

omit [DecidableEq P] in
/-- Every prefix of a projected history is the projection of a prefix. -/
lemma exists_take_of_prefix {α : List E} {β : List (Label P A)} (hβ : β <+: α.filterMap f) :
    ∃ t ≤ α.length, (α.take t).filterMap f = β := by
  induction α generalizing β with
  | nil => exact ⟨0, le_rfl, by simpa using hβ⟩
  | cons a α ih =>
    rcases β with _ | ⟨b, β⟩
    · exact ⟨0, by simp, by simp⟩
    · cases hfa : f a with
      | none =>
        rw [List.filterMap_cons_none hfa] at hβ
        obtain ⟨t, ht, h⟩ := ih hβ
        exact ⟨t + 1, by simp; omega, by simp [List.filterMap_cons_none hfa, h]⟩
      | some ℓ =>
        rw [List.filterMap_cons_some hfa, List.cons_prefix_cons] at hβ
        obtain ⟨rfl, hβ⟩ := hβ
        obtain ⟨t, ht, h⟩ := ih hβ
        exact ⟨t + 1, by simp; omega, by simp [List.filterMap_cons_some hfa, h]⟩

/-- Real-time order in a projected history, through prefixes of the event list. -/
lemma precedes_iff (α : List E) (x y : OpId P) :
    Precedes (α.filterMap f) x y ↔
      ∃ t ≤ α.length, Completed ((α.take t).filterMap f) x ∧
        ¬ Invoked ((α.take t).filterMap f) y := by
  constructor
  · rintro ⟨β, γ, hsplit, h1, h2⟩
    obtain ⟨t, ht, h⟩ := exists_take_of_prefix f (β := β) ⟨γ, hsplit.symm⟩
    exact ⟨t, ht, h ▸ h1, h ▸ h2⟩
  · rintro ⟨t, -, h1, h2⟩
    refine ⟨(α.take t).filterMap f, (α.drop t).filterMap f, ?_, h1, h2⟩
    rw [← List.filterMap_append, List.take_append_drop]

lemma opsOf_take_mono (α : List E) {s t : ℕ} (hst : s ≤ t) (p : P) :
    (opsOf ((α.take s).filterMap f) p).length ≤ (opsOf ((α.take t).filterMap f) p).length := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [List.take_add, List.filterMap_append, opsOf_append, List.length_append]
  omega

lemma opsOf_take_succ_of_inv {α : List E} {e : ℕ} (he : e < α.length) {p : P} {o : A.Op}
    (h : f α[e] = some (.inv p o)) :
    (opsOf ((α.take (e + 1)).filterMap f) p).length =
      (opsOf ((α.take e).filterMap f) p).length + 1 := by
  rw [filterMap_take_succ f α he, opsOf_append, opsOf_toList, h]
  simp

lemma respsOf_take_succ_of_ret {α : List E} {e : ℕ} (he : e < α.length) {p : P} {v : A.Resp}
    (h : f α[e] = some (.ret p v)) :
    (respsOf ((α.take (e + 1)).filterMap f) p).length =
      (respsOf ((α.take e).filterMap f) p).length + 1 := by
  rw [filterMap_take_succ f α he, respsOf_append, respsOf_toList, h]
  simp

lemma respsOf_take_mono (α : List E) {s t : ℕ} (hst : s ≤ t) (p : P) :
    (respsOf ((α.take s).filterMap f) p).length ≤
      (respsOf ((α.take t).filterMap f) p).length := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [List.take_add, List.filterMap_append, respsOf_append, List.length_append]
  omega

/-- Counts of invocations do not change over an interval without invocations of `p`. -/
lemma opsOf_take_eq (α : List E) (p : P) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ α.length)
    (h : ∀ k (hk : k < α.length), s ≤ k → k < t → (f α[k]).bind (Label.invOf p) = none) :
    (opsOf ((α.take t).filterMap f) p).length = (opsOf ((α.take s).filterMap f) p).length := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    rw [filterMap_take_succ f α (by omega), opsOf_append, opsOf_toList,
      h t (by omega) hst (by omega)]
    simpa using ih (by omega) (fun k hk h1 h2 => h k hk h1 (by omega))

/-- Counts of responses do not change over an interval without responses of `p`. -/
lemma respsOf_take_eq (α : List E) (p : P) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ α.length)
    (h : ∀ k (hk : k < α.length), s ≤ k → k < t → (f α[k]).bind (Label.retOf p) = none) :
    (respsOf ((α.take t).filterMap f) p).length =
      (respsOf ((α.take s).filterMap f) p).length := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    rw [filterMap_take_succ f α (by omega), respsOf_append, respsOf_toList,
      h t (by omega) hst (by omega)]
    simpa using ih (by omega) (fun k hk h1 h2 => h k hk h1 (by omega))

variable {f}

lemma IsInv.unique {α : List E} {x : OpId P} {e e' : ℕ} (h : IsInv f α x e)
    (h' : IsInv f α x e') : e = e' := by
  obtain ⟨he, o, h1, h2⟩ := h
  obtain ⟨he', o', h1', h2'⟩ := h'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := opsOf_take_mono f α (Nat.succ_le_of_lt hlt) x.1
    rw [opsOf_take_succ_of_inv f he h1] at this
    omega
  · have := opsOf_take_mono f α (Nat.succ_le_of_lt hlt) x.1
    rw [opsOf_take_succ_of_inv f he' h1'] at this
    omega

lemma IsRet.unique {α : List E} {x : OpId P} {e e' : ℕ} (h : IsRet f α x e)
    (h' : IsRet f α x e') : e = e' := by
  obtain ⟨he, o, h1, h2⟩ := h
  obtain ⟨he', o', h1', h2'⟩ := h'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := respsOf_take_mono f α (Nat.succ_le_of_lt hlt) x.1
    rw [respsOf_take_succ_of_ret f he h1] at this
    omega
  · have := respsOf_take_mono f α (Nat.succ_le_of_lt hlt) x.1
    rw [respsOf_take_succ_of_ret f he' h1'] at this
    omega

lemma IsInv.inj {α : List E} {x y : OpId P} {e : ℕ} (hx : IsInv f α x e)
    (hy : IsInv f α y e) : x = y := by
  obtain ⟨he, o, h1, h2⟩ := hx
  obtain ⟨he', o', h1', h2'⟩ := hy
  rw [h1] at h1'
  simp only [Option.some.injEq, Label.inv.injEq] at h1'
  obtain ⟨h3, -⟩ := h1'
  ext
  · exact h3
  · rw [← h2, ← h2', h3]

lemma IsRet.inj {α : List E} {x y : OpId P} {e : ℕ} (hx : IsRet f α x e)
    (hy : IsRet f α y e) : x = y := by
  obtain ⟨he, o, h1, h2⟩ := hx
  obtain ⟨he', o', h1', h2'⟩ := hy
  rw [h1] at h1'
  simp only [Option.some.injEq, Label.ret.injEq] at h1'
  obtain ⟨h3, -⟩ := h1'
  ext
  · exact h3
  · rw [← h2, ← h2', h3]

/-- Real-time order from positions: `x` returns before `y` is invoked (if ever). -/
lemma precedes_of_lt {α : List E} {x y : OpId P} {r : ℕ} (hr : IsRet f α x r)
    (hy : ∀ e, IsInv f α y e → r < e) : Precedes (α.filterMap f) x y := by
  rw [precedes_iff]
  refine ⟨r + 1, hr.1, (completed_take_iff f α _ x).2 ⟨r, by omega, hr⟩, ?_⟩
  rw [invoked_take_iff]
  rintro ⟨e, he, hie⟩
  have := hy e hie
  omega

/-- Real-time order gives an inequality of positions. -/
lemma lt_of_precedes {α : List E} {x y : OpId P} (h : Precedes (α.filterMap f) x y) {r e : ℕ}
    (hr : IsRet f α x r) (he : IsInv f α y e) : r < e := by
  rw [precedes_iff] at h
  obtain ⟨t, -, h1, h2⟩ := h
  rw [completed_take_iff] at h1
  rw [invoked_take_iff] at h2
  obtain ⟨r', hr't, hr'⟩ := h1
  rw [hr.unique hr'] 
  by_contra hc
  exact h2 ⟨e, by omega, he⟩

end Podc.WritableObjects
