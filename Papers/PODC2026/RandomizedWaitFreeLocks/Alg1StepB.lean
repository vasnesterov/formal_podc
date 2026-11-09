import Papers.PODC2026.RandomizedWaitFreeLocks.Alg1StepA

/-!
# Algorithm 1: preservation of the invariant by lines 5, 9, 10 (`C.FAI`, `C.FAD`, return)
-/

namespace Podc.RandomizedWaitFreeLocks.Alg1

variable {P D : Type*} [DecidableEq P] [DecidableEq D] (own : D → P)

lemma inv_fad {c : Cfg P D} {p : P} (hI : Inv own c) (h : (c.loc p).pc = .fad) :
    Inv own { (c.tick.upd p { c.loc p with pc := .ret }) with
      C := c.C - 1, act := c.act.erase p } := by
  have hp : p ∈ c.act := (hI.act_iff p).2 (by simp [h, PC.inAct])
  refine hI.tick.frameG own { c.loc p with pc := .ret } (c.act.erase p) (c.C - 1) c.retT c.failed
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case refine_1 =>
    simp only; constructor
    · intro h'; cases h'
    · intro h'; exact absurd ((hI.idle_iff p).2 h') (by rw [h]; simp)
  case refine_2 => intro δ hd; exact hI.own_dsc p δ hd
  case refine_3 => simp [PC.inAct]
  case refine_4 => intro x hx; simp [hx]
  case refine_5 => rw [Finset.card_erase_of_mem hp, hI.C_eq]
  case refine_6 => intro h'; simp at h'
  case refine_7 =>
    intro x hx
    have hxp : x ≠ p := Finset.ne_of_mem_erase hx
    have hxa : x ∈ c.act := Finset.mem_of_mem_erase hx
    simp only [upd_loc, if_neg hxp, tick_loc, tick_act]
    refine le_trans ?_ (hI.k1 x hxa)
    gcongr
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_erase] at hz ⊢
    refine ⟨hz.1.2, ?_⟩
    rw [if_neg hz.1.1] at hz; exact hz.2
  case refine_8 =>
    intro x hx z hz
    have hxp : x ≠ p := Finset.ne_of_mem_erase hx
    have hzp : z ≠ p := Finset.ne_of_mem_erase hz
    simp only [upd_loc, if_neg hxp, if_neg hzp, tick_loc]
    exact hI.k2 x (Finset.mem_of_mem_erase hx) z (Finset.mem_of_mem_erase hz)
  case refine_9 => intros; rfl
  case refine_10 => intro δ hd; exact hI.o3 p δ hd
  case refine_11 => exact hI.o4
  all_goals (intros; try pcs)
  all_goals (try fin)
  case refine_24 δ he ho =>
    rcases hI.o1 δ he with h1 | ⟨h1, -⟩
    · exact Or.inl h1
    · right; rw [ho] at h1; first | exact ⟨h1, by simp [PC.post]⟩ | exact h1
  case refine_25 δ he ho hd _ => exact hI.o2 δ he (by rw [ho]; exact hd) (by rw [ho, h]; simp)

lemma inv_ret {c : Cfg P D} {p : P} {δ : D} (hI : Inv own c) (h : (c.loc p).pc = .ret)
    (hd : (c.loc p).dsc = some δ) (RT : D → Bool) (F : P → ℕ → Bool)
    (hRT : RT = if c.done δ then Function.update c.retT δ true else c.retT) :
    Inv own { (c.tick.upd p { c.loc p with pc := .idle, dsc := none }) with
      retT := RT, failed := F } := by
  have hp : p ∉ c.act := fun h' => by simpa [h, PC.inAct] using (hI.act_iff p).1 h'
  have hown : own δ = p := hI.own_dsc p δ hd
  refine hI.tick.frameG own { c.loc p with pc := .idle, dsc := none } c.act c.C RT F ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case refine_1 => simp
  case refine_2 => intro δ' h'; cases h'
  case refine_3 => simp [PC.inAct, hp]
  case refine_4 => intro x _; rfl
  case refine_5 => exact hI.C_eq
  case refine_6 => intro h'; exact absurd h' hp
  case refine_7 =>
    intro x hx
    have hxp : x ≠ p := fun e => hp (e ▸ hx)
    simp only [upd_loc, if_neg hxp, tick_loc, tick_act]
    refine le_trans ?_ (hI.k1 x hx)
    apply Nat.add_le_add_left; apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    rw [if_neg (fun e : z = p => hp (e ▸ hz.1))] at hz; exact hz
  case refine_8 =>
    intro x hx z hz
    have hxp : x ≠ p := fun e => hp (e ▸ hx)
    have hzp : z ≠ p := fun e => hp (e ▸ hz)
    simp only [upd_loc, if_neg hxp, if_neg hzp, tick_loc]
    exact hI.k2 x hx z hz
  case refine_9 =>
    intro δ' ho; rw [hRT]; split_ifs
    · rw [Function.update_of_ne (fun e => ho (by rw [e]; exact hown))]; rfl
    · rfl
  case refine_10 => intro δ' h'; cases h'
  case refine_11 =>
    intro δ' h'; rw [hRT] at h'; split_ifs at h' with hdn
    · by_cases e : δ' = δ
      · subst e; exact hdn
      · rw [Function.update_of_ne e] at h'; exact hI.o4 δ' h'
    · exact hI.o4 δ' h'
  case refine_24 =>
    intro δ' he ho
    left
    rcases hI.o1 δ' he with h1 | ⟨h1, -⟩
    · rw [hRT]; split_ifs
      · by_cases e : δ' = δ
        · subst e; simp
        · rw [Function.update_of_ne e]; exact h1
      · exact h1
    · rw [ho, hd] at h1; cases h1
      have := hI.o2 δ he (by rw [hown]; exact hd) (by rw [hown, h]; simp)
      rw [hRT, if_pos this]; simp
  all_goals (intros; try pcs)
  all_goals (try fin)

lemma inv_invoke {c : Cfg P D} {p : P} {δ : D} (hI : Inv own c) (h : (c.loc p).pc = .idle)
    (ho : own δ = p) (hr : c.retT δ = false) :
    Inv own { (c.tick.upd p
      { (c.loc p) with
        pc := .wr, dsc := some δ, b := c.C + 1, fT := c.T + 1,
        call := (c.loc p).call + 1, cidx := c.T }) with
      C := c.C + 1, act := insert p c.act } := by
  have hp : p ∉ c.act := fun h' => by simpa [h, PC.inAct] using (hI.act_iff p).1 h'
  have hdn : (c.loc p).dsc = none := (hI.idle_iff p).1 h
  refine hI.tick.frameG own { (c.loc p) with
      pc := .wr, dsc := some δ, b := c.C + 1, fT := c.T + 1, call := (c.loc p).call + 1,
      cidx := c.T } (insert p c.act) (c.C + 1) c.retT
    c.failed ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case refine_1 => simp
  case refine_2 => intro δ' h'; cases h'; exact ho
  case refine_3 => simp [PC.inAct]
  case refine_4 => intro x hx; simp [hx]
  case refine_5 => rw [Finset.card_insert_of_notMem hp, hI.C_eq]
  case refine_6 => intro _; simp
  case refine_7 =>
    intro x hx
    rcases eq_or_ne x p with rfl | hxp
    · simp only [upd_loc, if_pos rfl, tick_T]
      rw [hI.C_eq, add_comm 1]
      apply Nat.add_le_add_right; apply Finset.card_le_card
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_insert] at hz
      rcases hz with ⟨rfl | hz, h2⟩
      · simp at h2
      · exact hz
    · have hxa : x ∈ c.act := by simpa [hxp] using hx
      simp only [upd_loc, if_neg hxp, tick_loc]
      refine le_trans ?_ (hI.k1 x hxa)
      apply Nat.add_le_add_left; apply Finset.card_le_card
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_insert] at hz ⊢
      rcases hz with ⟨rfl | hz, h2⟩
      · simp at h2; have := (hI.fT_bd x hxa).2; omega
      · rw [if_neg (fun e : z = p => hp (e ▸ hz))] at h2; exact ⟨hz, h2⟩
  case refine_8 =>
    intro x hx z hz e
    simp only [upd_loc, tick_loc] at e
    have hb : ∀ y ∈ insert p c.act, y ≠ p → y ∈ c.act := fun y hy hyp => by simpa [hyp] using hy
    by_cases hxp : x = p <;> by_cases hzp : z = p
    · rw [hxp, hzp]
    · rw [if_pos hxp, if_neg hzp] at e; have := (hI.fT_bd z (hb z hz hzp)).2; simp at e; omega
    · rw [if_neg hxp, if_pos hzp] at e; have := (hI.fT_bd x (hb x hx hxp)).2; simp at e; omega
    · rw [if_neg hxp, if_neg hzp] at e; exact hI.k2 x (hb x hx hxp) z (hb z hz hzp) e
  case refine_9 => intros; rfl
  case refine_10 => intro δ' h'; cases h'; exact hr
  case refine_11 => exact hI.o4
  case refine_24 =>
    intro δ' he ho'
    left
    rcases hI.o1 δ' he with h1 | ⟨h1, -⟩
    · exact h1
    · rw [ho', hdn] at h1; cases h1
  all_goals (intros; try pcs)
  all_goals (try fin)

end Podc.RandomizedWaitFreeLocks.Alg1
