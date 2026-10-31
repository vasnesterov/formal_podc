import Papers.PODC2018.NestingSafeRecoverable.Alg1Local

/-!
# Algorithm 1: preservation of the invariant by all steps except line 4
-/

set_option linter.unusedSectionVars false

namespace Podc.NestingSafeRecoverable.Alg1

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V] {v₀ : V}
variable {C : (alg1 P V v₀).Cfg} {L : List (OpId P × RWOp V)} {G : Set V}

lemma ite_t {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

lemma ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

lemma lsame_push {p : P} {x : OpId P} (hx : x.1 = p) (o : RWOp V) :
    LSame (v₀ := v₀) p L (L ++ [(x, o)]) := by
  intro k hk
  have hkx : k ≠ x := fun e => hk (by rw [e, hx])
  refine ⟨by simp [hkx], ObjSpec.respIn_append_of_not_mem_right (by simp [hkx]),
    fun o h => h.append _⟩

/-- A step of a process running `READ`. -/
theorem Inv.step_read (hI : Inv C L G) {p : P} {pc : PC1} {v : Loc1 V}
    (h : C.st p = some (.read, pc, v)) : ∃ L', Inv (C.ev (.step p)) L' G := by
  obtain ⟨hs, hpc⟩ := hI.rInv h
  rcases hpc with ⟨rfl, hx⟩ | ⟨rfl, hresp⟩
  · obtain ⟨hop, hc⟩ := hI.cur h
    have he := ev_R_read (k := fun r => { v with temp := r }) h rfl
    refine ⟨L ++ [(curOp (N C.hist) p, .read)], ?_⟩
    have hwf := hI.wf.ev (.step p); have hpe := hI.pend.ev (.step p)
    rw [he] at hwf hpe ⊢
    refine hI.frame hwf hpe rfl rfl (fun q _ => rfl) (fun q hq => by simp [hq])
      (hI.lin.push hop hx hc) (runOps_concat_read _ _ _) (lsame_push rfl _) (hI.sinv p) ?_
    simp only [Function.update_self]
    refine ⟨hs, Or.inr ⟨rfl, ?_⟩⟩
    rw [ObjSpec.respIn_concat_self hx]
    exact congrArg some hI.state
  · exact ⟨L, hI.ret_step rfl (Alg.ev_step_ret C h rfl) hresp hs⟩

/-- A step of a process running `WRITE` (or its recovery), other than the write of `R` in
line 4. -/
theorem Inv.step_write (hI : Inv C L G) {p : P} {val : V} {pc : PC1} {v : Loc1 V}
    (h : C.st p = some (.write val, pc, v)) (hw4 : pc ≠ .w4) :
    ∃ L', Inv (C.ev (.step p)) L' G := by
  have hw := hI.wInv h
  cases pc with
  | w2 => exact ⟨L, hI.local_step rfl (ev_R_read h rfl) (winv_w2 hw hI.gR)⟩
  | w3 =>
    obtain ⟨hR, hSp, hS, hst, hh⟩ := ev_S_write (k := fun _ => v) h rfl
    have ht : v.temp ∈ G := hw.2.2.2.2.2.2
    by_cases hn : curOp (N C.hist) p ∈ L.map Prod.fst ∧ v.temp = Rv C
    · obtain ⟨L', h1, h2, h3, h4⟩ :=
        hI.retract h hn.1 (Or.inr (hw.2.1 hn.1 hw.2.2.2.2.1))
      exact ⟨L', hI.s_step rfl hR hSp hS hst hh h1 h2 h3 (sinv_true ht)
        (winv_w3_retract hw hn.2 h4)⟩
    · exact ⟨L, hI.s_step rfl hR hSp hS hst hh hI.lin rfl (LSame.rfl' _ _) (sinv_true ht)
        (winv_w3_keep hw hn)⟩
  | w4 => exact absurd rfl hw4
  | w5 =>
    obtain ⟨hR, hSp, hS, hst, hh⟩ := ev_S_write (k := fun _ => v) h rfl
    exact ⟨L, hI.s_step rfl hR hSp hS hst hh hI.lin rfl (LSame.rfl' _ _)
      (sinv_false (hI.cur h).1) (winv_w5 hw)⟩
  | w6 =>
    have hx : curOp (N C.hist) p ∈ L.map Prod.fst := hw.1.2 (Or.inl hw.2.2.2.2.1)
    refine ⟨L, hI.ret_step rfl (Alg.ev_step_ret C h rfl) ?_ hw.2.2.2.2.2⟩
    exact respIn_write _ (fun y hy hyx => by
      have := hI.lin.op_eq y hy; rw [hyx, (hI.cur h).1] at this; exact (Option.some.inj this).symm)
      hx
  | r8 => exact absurd hw.2.2.2.2 id
  | r9 => exact absurd hw.2.2.2.2 id
  | c11 => exact ⟨L, hI.local_step rfl (ev_S_read h rfl) (winv_c11 hw)⟩
  | c12 =>
    have he := Alg.ev_step_internal C h rfl
    by_cases h1 : v.flag = false ∧ v.curr ≠ some (wval v₀ (RWOp.write val))
    · rw [ite_t h1] at he
      exact ⟨L, hI.local_step rfl he (winv_c12_w2 hw h1)⟩
    · rw [ite_f h1] at he
      by_cases h2 : v.flag = true
      · rw [ite_t h2] at he
        exact ⟨L, hI.local_step rfl he (winv_c12_c14 hw h2)⟩
      · rw [ite_f h2] at he
        exact ⟨L, hI.local_step rfl he (winv_c12_c16 hw h1 h2)⟩
  | c14 => exact ⟨L, hI.local_step rfl (ev_R_read h rfl) (winv_c14 hw)⟩
  | c15 =>
    have he := Alg.ev_step_internal C h rfl
    by_cases h1 : v.curr = some v.temp
    · rw [ite_t h1] at he
      exact ⟨L, hI.local_step rfl he (winv_c15_w2 hw h1)⟩
    · rw [ite_f h1] at he
      exact ⟨L, hI.local_step rfl he (winv_c15_c16 hw h1 (hI.sinv p))⟩
  | c16 =>
    obtain ⟨hR, hSp, hS, hst, hh⟩ := ev_S_write (k := fun _ => v) h rfl
    exact ⟨L, hI.s_step rfl hR hSp hS hst hh hI.lin rfl (LSame.rfl' _ _)
      (sinv_false (hI.cur h).1) (winv_c16 hw)⟩
  | c17 =>
    have hx : curOp (N C.hist) p ∈ L.map Prod.fst := hw.1.2 (Or.inr (Or.inl hw.2.2.2.2))
    refine ⟨L, hI.ret_step rfl (Alg.ev_step_ret C h rfl) ?_ (by rw [hw.2.2.2.2])⟩
    exact respIn_write _ (fun y hy hyx => by
      have := hI.lin.op_eq y hy; rw [hyx, (hI.cur h).1] at this; exact (Option.some.inj this).symm)
      hx

end Podc.NestingSafeRecoverable.Alg1
