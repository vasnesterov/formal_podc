import Cslib.Computability.Distributed.SharedMemory.Model

/-!
# Small lemmas about steps and histories in CSLib's shared-memory model

Used by the invariant proofs of `ParSketch` and `OptParSketch`. (CSLib candidates.)
-/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

namespace Impl

variable {I : Impl A B P L}

-- CSLib candidate
/-- The effect of an internal step whose action is known. -/
lemma step_tau_access {C C' : Config A B P L} {p : P} (h : I.step C (.tau p) = some C')
    {i : ι} {o : (B i).Op} {k : (B i).Resp → L} (hact : I.act p (C.loc p) = .access i o k) :
    C'.pend = C.pend ∧ C'.mem = Function.update C.mem i ((B i).δ (C.mem i) o).1 ∧
      C'.loc = Function.update C.loc p (k ((B i).δ (C.mem i) o).2) := by
  obtain ⟨-, hpend, i', o', k', hact', hmem, hloc⟩ := step_tau h
  rw [hact] at hact'
  obtain ⟨rfl, ho, hk⟩ := Action.access.inj hact'
  cases ho; cases hk
  exact ⟨hpend, hmem, hloc⟩

-- CSLib candidate
/-- An internal step is impossible when the next action is a response. -/
lemma step_tau_ret_none {C : Config A B P L} {p : P} {r : A.Resp} {l : L}
    (hact : I.act p (C.loc p) = .ret r l) : I.step C (.tau p) = none := by
  simp only [step]
  split_ifs
  · rfl
  · rw [hact]

-- CSLib candidate
/-- The effect of a response step whose action is known. -/
lemma step_ret_ret {C C' : Config A B P L} {p : P} {r : A.Resp} (h : I.step C (.ret p r) = some C')
    {r' : A.Resp} {l : L} (hact : I.act p (C.loc p) = .ret r' l) :
    r = r' ∧ C'.pend = Function.update C.pend p none ∧ C'.mem = C.mem ∧
      C'.loc = Function.update C.loc p l := by
  obtain ⟨-, hpend, hmem, l', hact', hloc⟩ := step_ret h
  rw [hact] at hact'
  obtain ⟨rfl, rfl⟩ := Action.ret.inj hact'
  exact ⟨rfl, hpend, hmem, hloc⟩

-- CSLib candidate
/-- A response step is impossible when the next action is an access. -/
lemma step_ret_access_none {C : Config A B P L} {p : P} {r : A.Resp} {i : ι} {o : (B i).Op}
    {k : (B i).Resp → L} (hact : I.act p (C.loc p) = .access i o k) :
    I.step C (.ret p r) = none := by
  simp only [step]
  split_ifs
  · rfl
  · rw [hact]

-- CSLib candidate
/-- A response step is impossible when the next action is not a response. -/
lemma step_ret_none_of_not_ret {C : Config A B P L} {p : P} {r : A.Resp}
    (hact : ∀ r' l, I.act p (C.loc p) ≠ .ret r' l) : I.step C (.ret p r) = none := by
  simp only [step]
  split_ifs
  · rfl
  · split
    · rfl
    · rename_i r' l h; exact absurd h (hact r' l)

end Impl

/-! ### Histories -/

-- CSLib candidate
/-- After an invocation by an idle process `p`, the new instance is `curOp α p`. -/
lemma opOf_concat_inv_curOp {α : List (Label P A)} {p : P} {o : A.Op}
    (hidle : (opsOf α p).length = (respsOf α p).length) :
    opOf (α ++ [.inv p o]) (curOp α p) = some o := by
  rw [opOf_concat_inv]; simp [curOp, hidle]

-- CSLib candidate
/-- An instance completed after a response of `p` either was completed before or is the current
instance of `p`. -/
lemma completed_concat_ret {α : List (Label P A)} {p : P} {r : A.Resp} {x : OpId P}
    (h : Completed (α ++ [.ret p r]) x) : Completed α x ∨ x = curOp α p := by
  obtain ⟨q, k⟩ := x
  simp only [Completed, respsOf_concat, Label.retOf_ret] at h
  by_cases hq : p = q
  · subst hq
    simp only [ite_true, Option.toList_some, List.length_append, List.length_singleton] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (by simp [curOp, h])
  · left; simpa [Completed, hq] using h

-- CSLib candidate
/-- Completion is unchanged by labels that are not responses. -/
lemma completed_concat_of_not_ret {α : List (Label P A)} {ℓ : Label P A}
    (hℓ : ∀ p r, ℓ ≠ .ret p r) {x : OpId P} :
    Completed (α ++ [ℓ]) x ↔ Completed α x := by
  simp only [Completed, respsOf_concat_of_ne (fun r => hℓ x.1 r)]

-- CSLib candidate
/-- The response of the current instance after its response step. -/
lemma respOf_concat_ret_curOp (α : List (Label P A)) (p : P) (r : A.Resp) :
    respOf (α ++ [.ret p r]) (curOp α p) = some r := by
  simp [respOf]

-- CSLib candidate
/-- Responses of other instances are unchanged by a response step of `p`. -/
lemma respOf_concat_ret_of_ne {α : List (Label P A)} {p : P} {r : A.Resp} {x : OpId P}
    (hx : x ≠ curOp α p) (hc : x.1 = p → x.2 < (respsOf α p).length ∨
      (respsOf α p).length < x.2) :
    respOf (α ++ [.ret p r]) x = respOf α x := by
  obtain ⟨q, k⟩ := x
  simp only [respOf, respsOf_concat, Label.retOf_ret]
  by_cases hq : p = q
  · subst hq
    simp only [ite_true, Option.toList_some]
    rcases hc rfl with h | h
    · exact List.getElem?_append_left h
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  · simp [hq]

end Cslib.SharedMemory
