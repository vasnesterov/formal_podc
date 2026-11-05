import Papers.PODC2011.UnboundedConcurrency.StackModel

/-!
# Steps from related configurations; the write/read case of Lemma 14

Afek–Morrison–Wertheim, PODC 2011, Section 5.3, proof of Lemma 14. Two configurations whose
memories agree except on one iterator stack `s` (where they are related by some relation) and in
which a process `r` has the same local state: a step of `r` keeps them related as long as the
operation of `r` on `s` (if any) behaves the same in both (`step_off`).

`write_read_next_false`: if after `α a b` only `u` and after `α b a` only `¬u` can be decided,
`a` cannot be poised to write to an iterator stack while `b` is poised to read the iterator that
this write initializes. In `α a b` that iterator is at position `2`, in `α b a` at position `1`;
everything else is equal. A fresh process `R` cannot tell the two apart until it reads this
iterator; stopping `R` just after this read in `α b a` and just before it in `α a b` gives two
executions of opposite valencies with the same memory.
-/

namespace Podc.UnboundedConcurrency

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

set_option linter.unusedSectionVars false

variable {R S : Type} [DecidableEq R] [DecidableEq S] {B : R → ObjSpec} {W : S → Type}
  {A : Alg (ST B W) ℕ Bool Bool}

/-- A step of `r` from two configurations in which `r` has the same local state, the memories
agree off the iterator stack `s`, and the states of `s` are related by `Pst`: afterwards `r` has
the same local state, the memories agree off `s`, and the states of `s` are related by `Pst'`,
provided that an operation `o` of `r` on `s` gives the same response on both states and leads to
`Pst'`-related states, and that `Pst'` holds if `r` is not poised on `s`. -/
lemma step_off {s : S} {Pst' : ISState (W s) → ISState (W s) → Prop} {C D : Cfg A} {r : ℕ}
    (hloc : C.loc r = D.loc r) (hmem : ∀ j, j ≠ .inr s → C.mem j = D.mem j)
    (hop : ∀ (o : ISOp (W s)) k, A.act (C.loc r) = .access (.inr s) o k →
      Pst' ((stk C s).δ o).1 ((stk D s).δ o).1 ∧ ((stk C s).δ o).2 = ((stk D s).δ o).2)
    (hPP : ¬ C.Poised r (.inr s) → Pst' (stk C s) (stk D s)) :
    (C.step r).loc r = (D.step r).loc r ∧
      (∀ j, j ≠ .inr s → (C.step r).mem j = (D.step r).mem j) ∧
      Pst' (stk (C.step r) s) (stk (D.step r) s) := by
  rcases Arrival.Cfg.out_or_poised C r with ⟨v, hv⟩ | ⟨i, o, k, hact⟩
  · have hv' : D.Out r v := by unfold Cfg.Out at *; rwa [← hloc]
    rw [Arrival.Cfg.step_of_out hv, Arrival.Cfg.step_of_out hv']
    exact ⟨hloc, hmem, hPP (Arrival.Cfg.not_out_of_poised · v hv |>.elim)⟩
  · have hact' : A.act (D.loc r) = .access i o k := hloc ▸ hact
    by_cases hi : i = .inr s
    · subst hi
      obtain ⟨h1, h2⟩ := hop o k hact
      refine ⟨?_, ?_, ?_⟩
      · rw [Arrival.Cfg.step_loc_self_of_access hact, Arrival.Cfg.step_loc_self_of_access hact']
        exact congrArg k h2
      · intro j hj
        rw [Arrival.Cfg.step_mem_other hact hj, Arrival.Cfg.step_mem_other hact' hj]
        exact hmem j hj
      · unfold stk stkM
        rw [Arrival.Cfg.step_mem_self_of_access hact, Arrival.Cfg.step_mem_self_of_access hact']
        exact h1
    · have hi' := hmem i hi
      refine ⟨?_, fun j hj => ?_, ?_⟩
      · rw [Arrival.Cfg.step_loc_self_of_access hact, Arrival.Cfg.step_loc_self_of_access hact',
          hi']
      · by_cases hji : j = i
        · subst hji
          rw [Arrival.Cfg.step_mem_self_of_access hact,
            Arrival.Cfg.step_mem_self_of_access hact', hi']
        · rw [Arrival.Cfg.step_mem_other hact hji, Arrival.Cfg.step_mem_other hact' hji]
          exact hmem j hj
      · unfold stk stkM
        rw [Arrival.Cfg.step_mem_other hact (Ne.symm hi),
          Arrival.Cfg.step_mem_other hact' (Ne.symm hi)]
        exact hPP (fun hp => hi (Arrival.Cfg.Poised.unique ⟨o, k, hact⟩ hp))

/-- Steps of other processes do not change the local state of `p`. -/
lemma loc_step_ne {C : Cfg A} {p r : ℕ} (h : p ≠ r) : (C.step r).loc p = C.loc p :=
  Arrival.Cfg.step_loc_other C h

/-! ### The relation of `write_read_next_false` -/

/-- Iterator stack states that differ only in the position of iterator `m`, which is one larger
in the first state. -/
def OffOne {V : Type} (m : ℕ) (s₁ s₂ : ISState V) : Prop :=
  s₁.vals = s₂.vals ∧ s₁.its.length = s₂.its.length ∧ m < s₂.its.length ∧
    (∀ k, k ≠ m → s₁.its[k]? = s₂.its[k]?) ∧ s₁.its[m]? = (s₂.its[m]?).map (· + 1)

lemma OffOne.step {V : Type} {m : ℕ} {s₁ s₂ : ISState V} (h : OffOne m s₁ s₂) (o : ISOp V)
    (ho : o ≠ .read m) :
    OffOne m (s₁.δ o).1 (s₂.δ o).1 ∧ (s₁.δ o).2 = (s₂.δ o).2 := by
  obtain ⟨hv, hl, hm, hne, hmm⟩ := h
  cases o with
  | write v =>
    simp only [ISState.δ_write, hl, and_true]
    refine ⟨by rw [hv], by simp [hl], by simp; omega, fun k hk => ?_, ?_⟩
    · simp only [List.getElem?_append]
      rw [hl]
      split_ifs
      · exact hne k hk
      · rfl
    · first
        | exact hmm
        | (rw [List.getElem?_append_left (hl ▸ hm), List.getElem?_append_left hm]; exact hmm)
  | read k =>
    have hk : k ≠ m := fun e => ho (by rw [e])
    rcases lt_or_ge k s₂.its.length with hk2 | hk2
    · have hk1 : k < s₁.its.length := hl ▸ hk2
      have he : s₁.its[k] = s₂.its[k] := by
        have := hne k hk
        rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk2] at this
        exact Option.some.inj this
      rw [ISState.δ_read_of_lt _ hk1, ISState.δ_read_of_lt _ hk2]
      refine ⟨⟨hv, by simp [hl], by simp; omega, fun j hj => ?_, ?_⟩, ?_⟩
      · by_cases hjk : j = k
        · subst hjk
          rw [List.getElem?_set_self hk1, List.getElem?_set_self hk2, he]
        · rw [List.getElem?_set_ne (Ne.symm hjk), List.getElem?_set_ne (Ne.symm hjk)]
          exact hne j hj
      · rw [List.getElem?_set_ne hk, List.getElem?_set_ne hk]
        exact hmm
      · simp [ISState.at, he, hv]
    · have hk1 : s₁.its.length ≤ k := hl ▸ hk2
      rw [ISState.δ_read_of_le _ hk1, ISState.δ_read_of_le _ hk2]
      exact ⟨⟨hv, hl, hm, hne, hmm⟩, rfl⟩

lemma OffOne.read_eq {V : Type} {m : ℕ} {s₁ s₂ : ISState V} (h : OffOne m s₁ s₂) :
    (s₂.δ (.read m)).1 = s₁ := by
  obtain ⟨hv, hl, hm, hne, hmm⟩ := h
  rw [ISState.δ_read_of_lt _ hm]
  ext1
  · exact hv.symm
  · apply List.ext_getElem?
    intro k
    simp only [List.getElem?_set]
    by_cases hk : k = m
    · subst hk
      simp [hm, hmm]
    · simp [Ne.symm hk, hne k hk]

section WaitFree

variable (hwf : WaitFree A (fun s => (Set.range s).Finite))
include hwf

/-- **Write against read of the new iterator** (the case `j = m + 1` of the proof of Lemma 14).
If after `α a b` only `u` and after `α b a` only `¬u` can be decided, then `a` is not poised to
write to an iterator stack `s` while `b` is poised to read the iterator of `s` that this write
initializes. -/
theorem write_read_next_false {x : ℕ → Bool} {α : List ℕ} {a b : ℕ} {u : Bool}
    (h₁ : Uni A x (α ++ [a, b]) u) (h₂ : Uni A x (α ++ [b, a]) (!u)) (hab : a ≠ b) {s : S}
    {va : W s} {ka kb : ISResp (W s) → A.L}
    (ha : A.act ((A.exec x α).loc a) = .access (.inr s) (ISOp.write va) ka)
    (hb : A.act ((A.exec x α).loc b) =
      .access (.inr s) (ISOp.read (stk (A.exec x α) s).its.length) kb) : False := by
  set C := A.exec x α with hC
  set m := (stk C s).its.length with hm
  have e1 : A.exec x (α ++ [a, b]) = (C.step a).step b := by
    rw [show α ++ [a, b] = α ++ [a] ++ [b] by simp, Alg.exec_concat, Alg.exec_concat]
  have e2 : A.exec x (α ++ [b, a]) = (C.step b).step a := by
    rw [show α ++ [b, a] = α ++ [b] ++ [a] by simp, Alg.exec_concat, Alg.exec_concat]
  -- the memories after `a b` and after `b a`
  have hb' : A.act ((C.step a).loc b) = .access (.inr s) (ISOp.read m) kb := by
    rw [loc_step_ne (Ne.symm hab)]; exact hb
  have ha' : A.act ((C.step b).loc a) = .access (.inr s) (ISOp.write va) ka := by
    rw [loc_step_ne hab]; exact ha
  have hs1 : stk ((C.step a).step b) s = ⟨va :: (stk C s).vals, (stk C s).its ++ [2]⟩ := by
    unfold stk stkM
    rw [Arrival.Cfg.step_mem_self_of_access hb', Arrival.Cfg.step_mem_self_of_access ha]
    show ((ISState.δ (ISState.δ (stk C s) (.write va)).1 (.read m)).1) = _
    rw [ISState.δ_write, ISState.δ_read_of_lt _ (by simp [hm])]
    simp [hm]
    exact ⟨rfl, rfl⟩
  have hs2 : stk ((C.step b).step a) s = ⟨va :: (stk C s).vals, (stk C s).its ++ [1]⟩ := by
    unfold stk stkM
    rw [Arrival.Cfg.step_mem_self_of_access ha', Arrival.Cfg.step_mem_self_of_access hb]
    show ((ISState.δ (ISState.δ (stk C s) (.read m)).1 (.write va)).1) = _
    rw [ISState.δ_read_of_le _ (le_of_eq hm.symm), ISState.δ_write]
    rfl
  have hoth : ∀ j, j ≠ .inr s → ((C.step a).step b).mem j = ((C.step b).step a).mem j := by
    intro j hj
    rw [Arrival.Cfg.step_mem_other hb' hj, Arrival.Cfg.step_mem_other ha hj,
      Arrival.Cfg.step_mem_other ha' hj, Arrival.Cfg.step_mem_other hb hj]
  -- a fresh process `R`
  obtain ⟨r, hr⟩ := exists_fresh (α ++ [a, b])
  have hra : r ≠ a := fun e => hr (by simp [e])
  have hrb : r ≠ b := fun e => hr (by simp [e])
  let Rel : Cfg A → Cfg A → Prop := fun C₁ C₂ => C₁.loc r = C₂.loc r ∧
    (∀ j, j ≠ .inr s → C₁.mem j = C₂.mem j) ∧ OffOne m (stk C₁ s) (stk C₂ s)
  let Bad : Cfg A → Prop := fun C₁ => ∃ k, A.act (C₁.loc r) = .access (.inr s) (ISOp.read m) k
  have hrel0 : Rel (A.exec x (α ++ [a, b])) (A.exec x (α ++ [b, a])) := by
    rw [e1, e2]
    refine ⟨by rw [loc_step_ne hrb, loc_step_ne hra, loc_step_ne hra, loc_step_ne hrb], hoth, ?_⟩
    rw [hs1, hs2]
    refine ⟨rfl, by simp, by simp [hm], fun k hk => ?_, ?_⟩
    · rcases lt_or_ge k (stk C s).its.length with h | h
      · rw [List.getElem?_append_left h, List.getElem?_append_left h]
      · have : (stk C s).its.length + 1 ≤ k := by omega
        rw [List.getElem?_eq_none (by simpa using this), List.getElem?_eq_none (by simpa using this)]
    · simp [hm]
  have hstep : ∀ C₁ C₂, Rel C₁ C₂ → ¬ Bad C₁ → Rel (C₁.step r) (C₂.step r) := by
    intro C₁ C₂ ⟨hl, hmem, hoff⟩ hbad
    obtain ⟨h1, h2, h3⟩ := step_off (Pst' := OffOne m) hl hmem
      (fun o k hact => hoff.step o (by rintro rfl; exact hbad ⟨k, hact⟩)) (fun _ => hoff)
    exact ⟨h1, h2, h3⟩
  obtain ⟨n, -, ⟨k, hbad⟩, hl, hmem, hoff⟩ :=
    solo_reach hwf Rel Bad r hstep (fun _ _ h => h.1) h₁ h₂ hrel0
  -- one more step of `R` in the second execution equalizes the memories
  set C₁ := A.exec x (α ++ [a, b] ++ List.replicate n r)
  set C₂ := A.exec x (α ++ [b, a] ++ List.replicate n r)
  have hbad2 : A.act (C₂.loc r) = .access (.inr s) (ISOp.read m) k := hl ▸ hbad
  apply false_of_mem_eq hwf (h₁.append (List.replicate n r)) (h₂.append (List.replicate n r ++ [r]))
  rw [← List.append_assoc, Alg.exec_concat]
  funext j
  by_cases hj : j = .inr s
  · subst hj
    rw [Arrival.Cfg.step_mem_self_of_access hbad2]
    exact (hoff.read_eq).symm
  · rw [Arrival.Cfg.step_mem_other hbad2 hj]
    exact hmem j hj

end WaitFree

end Podc.UnboundedConcurrency
