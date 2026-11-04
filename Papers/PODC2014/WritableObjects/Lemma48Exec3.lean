import Papers.PODC2014.WritableObjects.Lemma48Exec2

/-!
# Lemma 4.8, part 10: preservation of the state of a pending `Exec`
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} {T : ObjSpec} [NeZero n] {W : Writable T} {c c' : Cfg n T}

set_option hygiene false in
/-- In a step of `p` that does not change `q`'s local state, `p ≠ q`. -/
local macro "nq" p:ident : tactic => `(tactic| (
  have hne : $p ≠ q := by
    rintro rfl
    have h' := congrArg Loc.pc hq
    simp only [Function.update_self] at h'
    rw [h] at h'; simp at h'))

/-- A stable hint entry `H_p[q]` is not overwritten while `q` does not move. -/
lemma Inv.hH_stable (hs : Step W c c') {q : Fin n} (hq : c'.loc q = c.loc q) {p : Fin n}
    {x : ℤ} {j : Idx n} (hB : Bcore c p q x j) : c'.hH p q = c.hH p q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hps⟩ := hB
  cases hs
  case l18 p0 v f s m14 olds olds' h =>
    by_cases hp : p = p0
    · subst hp
      simp only [PSide, h] at hps
      simp [Function.update_of_ne (Ne.symm hps)]
    · simp [Function.update_of_ne hp]
  case l44 p0 x r h =>
    nq p0; exact upd2_ne _ _ _ _ _ (Ne.symm hne)
  all_goals rfl

/-- The state of a pending `Exec` of `q` is preserved by steps of other processes. -/
theorem Inv.exec_frame (hI : Inv W c) (hs : Step W c c') {q : Fin n} (hq : c'.loc q = c.loc q) :
    ExecInv c' q := by
  have h := hI.exec q
  have hlen := Inv.len_step hs
  obtain ⟨t, ht⟩ := Inv.tr_ext hs
  have hS : c'.S q = c.S q := by rw [hI.sEq_step hs q, hq, hI.sEq q]
  have hA := Inv.annc_frame hs hq
  have hptr : ∀ ts, ts ≤ c.tr.length → ptrAt c'.tr ts = ptrAt c.tr ts := fun ts h => by
    rw [ht, ptrAt_ext h]
  unfold ExecInv at h ⊢
  rw [hq]
  cases hpc : (c.loc q).pc <;> simp only [hpc] at h ⊢
  case e34 o => exact Inv.eqOK_frame hs hq h
  case e35 o x => exact ⟨Inv.eqOK_frame hs hq h.1, by rw [hS]; exact h.2⟩
  case e36 o x => exact ⟨Inv.eqOK_frame hs hq h.1, hI.winOK_frame hs hq h.2⟩
  case e37 o x i g ts =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨Inv.eqOK_frame hs hq h1, hI.winOK_frame hs hq h2, h3, by omega, fun i' hi => ?_⟩
    obtain ⟨e1, e2⟩ := h5 i' hi
    exact ⟨by rw [hptr ts h4]; exact e1, hI.a1_frame hs hq h2.1 e2⟩
  case e39 o x i g ts =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨Inv.eqOK_frame hs hq h1, hI.winOK_frame hs hq h2, h3, by omega, fun i' hi => ?_⟩
    obtain ⟨e1, e2, e3⟩ := h5 i' hi
    refine ⟨by rw [hptr ts h4]; exact e1, hA.trans e2, ?_⟩
    rcases e3 with ⟨hD, hP⟩ | ⟨j, hB⟩
    · exact Or.inl ⟨hI.dcore_frame hs hq hD, hI.ppok_step hs hP hD.2.1⟩
    · exact Or.inr ⟨j, hI.bcore_frame hs hq h2.1 hB⟩
  case e40 o x i g ts hv =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    refine ⟨Inv.eqOK_frame hs hq h1, hI.winOK_frame hs hq h2, h3, by omega,
      by rw [hptr ts h4]; exact h5, hA.trans h6, ?_, fun h' hv' hs' =>
        hI.i39_frame hs hq h2.1 (by simp [pre44, hpc]) (h8 h' hv' hs')⟩
    rcases h7 with ⟨hD, hP⟩ | ⟨h', hv', hH, hB⟩
    · exact Or.inl ⟨hI.dcore_frame hs hq hD, hI.ppok_step hs hP hD.2.1⟩
    · exact Or.inr ⟨h', hv', (Inv.hH_stable hs hq hB).trans hH, hI.bcore_frame hs hq h2.1 hB⟩
  case e43 o x i ts =>
    exact ⟨Inv.eqOK_frame hs hq h.1, hI.winOK_frame hs hq h.2.1,
      hI.commit_frame hs hq h.2.1.1 h.2.2⟩
  case eOp x i ts t =>
    exact ⟨hI.winOK_frame hs hq h.1, hI.commit_frame hs hq h.1.1 h.2.1, h.2.2⟩
  case e44 x r => exact hI.winOK_frame hs hq h
  case e45 x r => exact hI.winOK_frame hs hq h

end Podc.WritableObjects.WF
