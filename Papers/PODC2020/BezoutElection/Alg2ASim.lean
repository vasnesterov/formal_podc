import Papers.PODC2020.BezoutElection.Alg2Live
import Papers.PODC2020.BezoutElection.Alg2ALive4

/-!
# Algorithm 2: from fair executions to abstract runs of a register

Every step of the concrete algorithm acts on a register by one abstract transition (`sim_step`):
the for loop processes the local registers one by one (`loopFrom_res`).
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ}

/-- What the rest of the for loop does to the local register `k`: nothing (the loop stops at an
earlier write), or it processes it in an intermediate state `s_mid`. -/
def LoopRes (pp : Params) (s s_f : St Id m) (k : Fin m) : Prop :=
  (locX s_f k = locX s k ∧ ∃ j' w, s_f.pc = .write j' w ∧ j' < k.val) ∨
  (∃ s_mid : St Id m, locX s_mid k = locX s k ∧ s_mid.regs = s.regs ∧ s_mid.me = s.me ∧
    s_mid.finishing = s.finishing ∧ s_mid.toWin = s.toWin ∧
    (∀ k', s_mid.cand k' = s.cand k' ∨ s_mid.cand k' = s_f.cand k') ∧
    locX s_f k (vstatus (.pc s_f.pc) s_f k) = { (oX pp s_mid k).1 with st := stOf (oX pp s_mid k).2 })

lemma locX_ext {s s' : St Id m} {k : Fin m} (h : ∀ st, locX s' k st = locX s k st) :
    locX s' k = locX s k := funext h

/-- The for loop from position `j`. -/
theorem loopFrom_res (pp : Params) (s : St Id m) (j : ℕ) :
    (loopFrom pp s j).regs = s.regs ∧ (loopFrom pp s j).me = s.me ∧
    (loopFrom pp s j).finishing = s.finishing ∧
    (∀ k : Fin m, k.val < j → locX (loopFrom pp s j) k = locX s k) ∧
    (∀ k : Fin m, j ≤ k.val → LoopRes pp s (loopFrom pp s j) k) ∧
    ((loopFrom pp s j).pc = .collect 0 ∨
      ∃ j' w, j ≤ j' ∧ j' < m ∧ (loopFrom pp s j).pc = .write j' w) := by
  rw [loopFrom]
  by_cases hj : j < m
  · rw [dif_pos hj]
    obtain ⟨hme, hpc, hregs, hfin⟩ := procReg_fields pp s ⟨j, hj⟩
    have hsnd := procReg_snd pp s ⟨j, hj⟩
    have hne : ∀ k : Fin m, k ≠ ⟨j, hj⟩ → locX (procReg pp s ⟨j, hj⟩).1 k = locX s k :=
      fun k hk => locX_ext (procReg_locX_ne pp s ⟨j, hj⟩ k hk)
    rcases e : procReg pp s ⟨j, hj⟩ with ⟨s', _ | w⟩
    · -- no write: the loop goes on
      simp only
      rw [e] at hme hregs hfin hsnd hne
      simp only at hme hregs hfin hsnd
      have htw : s'.toWin = s.toWin := by
        have := procReg_toWin_nowin pp s ⟨j, hj⟩ (fun w hw => by rw [← hsnd] at hw; cases hw)
        rw [e] at this; exact this
      have hcand : ∀ k', k' ≠ (⟨j, hj⟩ : Fin m) → s'.cand k' = s.cand k' := by
        intro k' hk'
        have := congrArg ALoc.ca (congrFun (hne k' hk') .fresh)
        simpa [locX] using this
      have hlj : ∀ st, locX s' ⟨j, hj⟩ st = { (oX pp s ⟨j, hj⟩).1 with st := st } := by
        intro st; have := procReg_locX pp s ⟨j, hj⟩ st; rw [e] at this; exact this
      obtain ⟨r1, r2, r3, r4, r5, r6⟩ := loopFrom_res pp s' (j + 1)
      refine ⟨r1.trans hregs, r2.trans hme, r3.trans hfin, ?_, ?_, ?_⟩
      · intro k hk
        rw [r4 k (by omega)]
        exact hne k (fun h => by rw [h] at hk; simp at hk)
      · intro k hk
        by_cases hkj : k = ⟨j, hj⟩
        · -- the register `j` is processed now
          subst hkj
          right
          refine ⟨s, rfl, rfl, rfl, rfl, rfl, fun k' => Or.inl rfl, ?_⟩
          rw [r4 _ (by simp), hlj, ← hsnd]
          rcases r6 with h | ⟨j', w, hj1, -, h⟩
          · rw [h]; simp [vstatus, stOf]
          · rw [h]
            have h1 : ¬ j' < j := by omega
            have h2 : j' ≠ j := by omega
            simp [vstatus, stOf, h1, h2]
        · have hk' : j + 1 ≤ k.val := by
            have : k.val ≠ j := fun h => hkj (Fin.ext h)
            omega
          rcases r5 k hk' with ⟨h1, h2⟩ | ⟨s_mid, h1, h2, h3, h4, h5, h6, h7⟩
          · left; exact ⟨h1.trans (hne k hkj), h2⟩
          · right
            refine ⟨s_mid, h1.trans (hne k hkj), h2.trans hregs, h3.trans hme, h4.trans hfin,
              h5.trans htw, fun k' => ?_, h7⟩
            rcases h6 k' with h | h
            · by_cases hk'j : k' = ⟨j, hj⟩
              · subst hk'j
                right; rw [h]
                have := congrArg ALoc.ca (congrFun (r4 ⟨j, hj⟩ (by simp)) .fresh)
                simpa [locX] using this.symm
              · left; rw [h, hcand k' hk'j]
            · right; exact h
      · rcases r6 with h | ⟨j', w, h1, h2, h3⟩
        · exact Or.inl h
        · exact Or.inr ⟨j', w, by omega, h2, h3⟩
    · -- a write: the loop stops
      simp only
      rw [e] at hme hregs hfin hsnd hne
      simp only at hme hregs hfin hsnd
      have hlj : ∀ st, locX s' ⟨j, hj⟩ st = { (oX pp s ⟨j, hj⟩).1 with st := st } := by
        intro st; have := procReg_locX pp s ⟨j, hj⟩ st; rw [e] at this; exact this
      refine ⟨hregs, hme, hfin, ?_, ?_, Or.inr ⟨j, w, le_rfl, hj, rfl⟩⟩
      · intro k hk
        exact hne k (fun h => by rw [h] at hk; simp at hk)
      · intro k hk
        by_cases hkj : k = ⟨j, hj⟩
        · subst hkj
          right
          refine ⟨s, rfl, rfl, rfl, rfl, rfl, fun k' => Or.inl rfl, ?_⟩
          show locX s' ⟨j, hj⟩ (vstatus (.pc (.write j w)) { s' with pc := .write j w } ⟨j, hj⟩) = _
          rw [hlj, ← hsnd]
          simp [vstatus, stOf]
        · left
          refine ⟨hne k hkj, j, w, rfl, ?_⟩
          have : k.val ≠ j := fun h => hkj (Fin.ext h)
          omega
  · rw [dif_neg hj]
    refine ⟨rfl, rfl, rfl, fun k _ => rfl, fun k hk => by omega, Or.inl rfl⟩
termination_by m - j

end BezoutElection.Alg2

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P] [Fintype P]
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id} {R : Type} [Inhabited R]
  {out : Id → Finset Id → R}

/-- The intermediate state of a processing step agrees with the states before and after the
step on the candidate flags, and on `to_win` and `finishing` unless `finishing` was just set. -/
def MidOK (s s' s_mid : St Id m) : Prop :=
  (∀ k', s_mid.cand k' = s.cand k' ∨ s_mid.cand k' = s'.cand k') ∧
  ((s_mid.toWin = s.toWin ∧ s_mid.finishing = s.finishing) ∨
    (s.finishing = false ∧ s_mid.finishing = true ∧ s'.finishing = true))

lemma absAt_step (mem : Fin m → Reg Id) (loc : P → St Id m) (q : P) (s' : St Id m) (x : Fin m) :
    absAt π mem (Function.update loc q s') (vpcOf (Function.update loc q s')) x =
      (absAt π mem loc (vpcOf loc) x).upd q
        (locX s' ((π q).symm x) (vstatus (.pc s'.pc) s' ((π q).symm x))) := by
  rw [vpcOf_update, absAt_update]

lemma procL_locX (me : Id) (s : St Id m) (k : Fin m) (st : AStatus Id) (r : Reg Id)
    (ok fin : Bool) : procL pp.n pp.U me (locX s k st) r ok fin =
      { (procX pp.n pp.U me (locX s k .fresh) r ok fin).1 with
        st := stOf (procX pp.n pp.U me (locX s k .fresh) r ok fin).2 } := by
  rw [show locX s k st = { locX s k .fresh with st := st } from rfl, procL_st]; rfl

/-- The register transition of the rest of the for loop. -/
lemma loop_tr (q : P) (s s_f : St Id m) (k : Fin m) (hres : LoopRes pp s s_f k)
    (hregs : s_f.regs = s.regs) (hme : s.me = ids q) :
    (locX s_f k (vstatus (VPC.pc s_f.pc) s_f k) = locX s k (AStatus.copy (s.regs k))) ∨
    (∃ s_mid : St Id m, locX s_f k (vstatus (VPC.pc s_f.pc) s_f k) = procL pp.n pp.U (ids q)
      (locX s k (AStatus.copy (s.regs k))) (s.regs k) (okOf s_mid k) s_mid.finishing ∧
      (∀ k', s_mid.cand k' = s.cand k' ∨ s_mid.cand k' = s_f.cand k') ∧
      s_mid.toWin = s.toWin ∧ s_mid.finishing = s.finishing) := by
  rcases hres with ⟨h1, j', w, h2, h3⟩ | ⟨s_mid, h1, h2, h3, h4, h5, h6, h7⟩
  · left
    rw [h1, h2]; simp only [vstatus]; rw [if_pos h3, hregs]
  · right
    refine ⟨s_mid, ?_, h6, h5, h4⟩
    rw [h7, procL_locX]
    simp only [oX, h1, h2, h3, hme]

end BezoutElection.Alg2
