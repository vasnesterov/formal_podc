import Papers.PODC2020.BezoutElection.Alg2ASim2

/-!
# Algorithm 2, progress: the steps of a process

The effect of the internal steps (`tau_collect`, `tau_write`) and simple monotonicity facts:
`finishing` is never reset, and `to_win` only decreases while `finishing` does not change.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P] [Fintype P]
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id} {R : Type} [Inhabited R]
  {out : Id → Finset Id → R}

/-- The for loop never increases `to_win`. -/
theorem loopFrom_toWin (pp : Params) (s : St Id m) (j : ℕ) : (loopFrom pp s j).toWin ≤ s.toWin := by
  rw [loopFrom]
  by_cases hj : j < m
  · rw [dif_pos hj]
    have htw : (procReg pp s ⟨j, hj⟩).1.toWin ≤ s.toWin := by
      by_cases h : ∃ w, (oX pp s ⟨j, hj⟩).2 = some w ∧ w.level = (s.regs ⟨j, hj⟩).level + 1
      · obtain ⟨w, hw, hl⟩ := h; rw [procReg_toWin_win pp s _ w hw hl]; omega
      · push Not at h; rw [procReg_toWin_nowin pp s _ (fun w hw => h w hw)]
    rcases e : procReg pp s ⟨j, hj⟩ with ⟨s', _ | w⟩
    · simp only; rw [e] at htw; exact (loopFrom_toWin pp s' (j + 1)).trans htw
    · simp only; rw [e] at htw; exact htw
  · rw [dif_neg hj]
termination_by m - j

section Steps

variable {α : List (Label P (elecObj R))} {C C' : Cfg2 Id m R P} {q : P}

lemma tau_rmw (h : ((alg2 Id m pp out).impl ids π).step C (.tau q) = some C') :
    ∃ x0 f k, (alg2 Id m pp out).act (C.loc q) = .rmw x0 f k ∧ C' = { C with
      mem := Function.update C.mem () (Function.update (C.mem ()) (π q x0) (f (C.mem () (π q x0))))
      loc := Function.update C.loc q (k (C.mem () (π q x0))) } := by
  obtain ⟨-, h1 | ⟨k, hact, -⟩⟩ := SymAlg.impl_step_tau_cases h
  · exact h1
  · exfalso
    simp only [alg2] at hact
    split at hact <;> (try split at hact) <;> simp at hact

/-- A read of the collect. -/
lemma tau_collect (hI : RInv π pp ids out α C)
    (h : ((alg2 Id m pp out).impl ids π).step C (.tau q) = some C') {j : ℕ}
    (hpc : (C.loc q).pc = .collect j) :
    ∃ hj : j < m, C'.mem () = C.mem () ∧ C'.loc q =
      (if j + 1 < m then { (C.loc q).setReg ⟨j, hj⟩ (C.mem () (π q ⟨j, hj⟩)) with pc := .collect (j + 1) }
        else afterCollect pp ((C.loc q).setReg ⟨j, hj⟩ (C.mem () (π q ⟨j, hj⟩)))) ∧
      ∀ q', q' ≠ q → C'.loc q' = C.loc q' := by
  obtain ⟨x0, f, k, hact, rfl⟩ := tau_rmw h
  have hj := (hI.pcok q).1 j hpc
  rw [act_collect _ hpc hj] at hact
  simp only [SymAction.rmw.injEq] at hact
  obtain ⟨rfl, rfl, rfl⟩ := hact
  refine ⟨hj, by simp, by simp [St.setReg], fun q' hq' => by simp [Function.update_of_ne hq']⟩

/-- A write. -/
lemma tau_write (hI : RInv π pp ids out α C)
    (h : ((alg2 Id m pp out).impl ids π).step C (.tau q) = some C') {j : ℕ} {w : Reg Id}
    (hpc : (C.loc q).pc = .write j w) :
    ∃ hj : j < m, C'.mem () = Function.update (C.mem ()) (π q ⟨j, hj⟩) w ∧
      C'.loc q = loopFrom pp (C.loc q) (j + 1) ∧ ∀ q', q' ≠ q → C'.loc q' = C.loc q' := by
  obtain ⟨x0, f, k, hact, rfl⟩ := tau_rmw h
  have hj := (hI.pcok q).2 j w hpc
  rw [act_write _ hpc hj] at hact
  simp only [SymAction.rmw.injEq] at hact
  obtain ⟨rfl, rfl, rfl⟩ := hact
  refine ⟨hj, by simp, by simp, fun q' hq' => by simp [Function.update_of_ne hq']⟩

/-- Internal steps happen only in the collect and at writes. -/
lemma tau_pc (h : ((alg2 Id m pp out).impl ids π).step C (.tau q) = some C') :
    (∃ j, (C.loc q).pc = .collect j) ∨ ∃ j w, (C.loc q).pc = .write j w := by
  obtain ⟨x0, f, k, hact, -⟩ := tau_rmw h
  rcases hpc : (C.loc q).pc with _ | j | ⟨j, w⟩ | L | _
  · rw [act_idle _ hpc] at hact; cases hact
  · exact Or.inl ⟨j, rfl⟩
  · exact Or.inr ⟨j, w, rfl⟩
  · rw [act_ret _ hpc] at hact; cases hact
  · rw [act_fin _ hpc] at hact; cases hact

/-- `finishing` is never reset, and `to_win` decreases while `finishing` does not change. -/
lemma step_fin (hI : RInv π pp ids out α C) {ℓ : Label P (elecObj R)}
    (h : ((alg2 Id m pp out).impl ids π).step C ℓ = some C') (q : P) :
    ((C.loc q).finishing = true → (C'.loc q).finishing = true) ∧
      ((C'.loc q).finishing = (C.loc q).finishing → (C'.loc q).toWin ≤ (C.loc q).toWin) := by
  by_cases hq : ℓ.proc = q
  swap
  · rw [(Impl.step_other h hq).1]; exact ⟨id, fun _ => le_rfl⟩
  cases ℓ with
  | inv q' o =>
    simp only [Label.proc] at hq; subst hq
    obtain ⟨-, rfl⟩ := SymAlg.impl_step_inv_cases h
    simp only [Function.update_self]
    rcases hpc : (C.loc q').pc with _ | j | ⟨j, w⟩ | L | _ <;>
      simp [alg2, hpc]
  | ret q' r =>
    simp only [Label.proc] at hq; subst hq
    obtain ⟨-, s, hact, rfl⟩ := SymAlg.impl_step_ret_cases h
    simp only [Function.update_self]
    rcases hpc : (C.loc q').pc with _ | j | ⟨j, w⟩ | L | _
    · rw [act_idle _ hpc] at hact; cases hact; exact ⟨id, fun _ => le_rfl⟩
    · rw [act_collect _ hpc ((hI.pcok q').1 j hpc)] at hact; cases hact
    · rw [act_write _ hpc ((hI.pcok q').2 j w hpc)] at hact; cases hact
    · rw [act_ret _ hpc] at hact; cases hact; exact ⟨id, fun _ => le_rfl⟩
    · rw [act_fin _ hpc] at hact; cases hact; exact ⟨id, fun _ => le_rfl⟩
  | tau q' =>
    simp only [Label.proc] at hq; subst hq
    rcases tau_pc h with ⟨j, hpc⟩ | ⟨j, w, hpc⟩
    · obtain ⟨hj, -, hloc, -⟩ := tau_collect hI h hpc
      rw [hloc]
      split_ifs with hj1
      · exact ⟨id, fun _ => le_rfl⟩
      · unfold afterCollect
        dsimp only
        split_ifs with hsum hc
        · exact ⟨id, fun _ => le_rfl⟩
        · obtain ⟨-, -, hf, -⟩ := loopFrom_res pp
            { (C.loc q').setReg ⟨j, hj⟩ (C.mem () (π q' ⟨j, hj⟩)) with finishing := true, toWin := 1 } 0
          refine ⟨fun _ => hf, fun h' => ?_⟩
          exfalso
          have h2 : (C.loc q').finishing = false := hc.2
          have h3 : true = (C.loc q').finishing := hf.symm.trans h'
          rw [h2] at h3; cases h3
        · obtain ⟨-, -, hf, -⟩ := loopFrom_res pp
            ((C.loc q').setReg ⟨j, hj⟩ (C.mem () (π q' ⟨j, hj⟩))) 0
          exact ⟨fun h' => hf.trans h', fun _ => loopFrom_toWin _ _ _⟩
    · obtain ⟨hj, -, hloc, -⟩ := tau_write hI h hpc
      rw [hloc]
      obtain ⟨-, -, hf, -⟩ := loopFrom_res pp (C.loc q') (j + 1)
      exact ⟨fun h' => hf.trans h', fun _ => loopFrom_toWin _ _ _⟩

/-- The program counter after a read of the collect. -/
lemma tau_collect_pc (hI : RInv π pp ids out α C)
    (h : ((alg2 Id m pp out).impl ids π).step C (.tau q) = some C') {j : ℕ}
    (hpc : (C.loc q).pc = .collect j) :
    j < m ∧ (j + 1 < m → (C'.loc q).pc = .collect (j + 1)) ∧
      (¬j + 1 < m → (∃ L, (C'.loc q).pc = .ret L) ∨ (C'.loc q).pc = .collect 0 ∨
        ∃ j' w', j' < m ∧ (C'.loc q).pc = .write j' w') := by
  obtain ⟨hj, -, hloc, -⟩ := tau_collect hI h hpc
  refine ⟨hj, fun hj1 => by rw [hloc, if_pos hj1], fun hj1 => ?_⟩
  rw [hloc, if_neg hj1]
  unfold afterCollect
  dsimp only
  split_ifs
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr (loopFrom_pc _ _)
  · exact Or.inr (loopFrom_pc _ _)

/-- The program counter after a write. -/
lemma tau_write_pc (hI : RInv π pp ids out α C)
    (h : ((alg2 Id m pp out).impl ids π).step C (.tau q) = some C') {j : ℕ} {w : Reg Id}
    (hpc : (C.loc q).pc = .write j w) :
    j < m ∧ ((C'.loc q).pc = .collect 0 ∨ ∃ j' w', j < j' ∧ j' < m ∧ (C'.loc q).pc = .write j' w') := by
  obtain ⟨hj, -, hloc, -⟩ := tau_write hI h hpc
  refine ⟨hj, ?_⟩
  rw [hloc]
  rcases (loopFrom_res pp (C.loc q) (j + 1)).2.2.2.2.2 with h' | ⟨j', w', h1, h2, h3⟩
  · exact Or.inl h'
  · exact Or.inr ⟨j', w', by omega, h2, h3⟩

/-- At the end of a collect whose copies are up to date, `finishing` is set if at least `W n`
competitions are solved. -/
lemma tau_last_fin (hI : RInv π pp ids out α C)
    (h : ((alg2 Id m pp out).impl ids π).step C (.tau q) = some C') {j : ℕ}
    (hpc : (C.loc q).pc = .collect j) (hj1 : j + 1 = m)
    (hcopy : ∀ i : Fin m, i.val < j → ((C.loc q).regs i).level = (C.mem () (π q i)).level)
    (hW : pp.W * pp.n ≤ ∑ x, (C.mem () x).level) (hU : ∑ x, (C.mem () x).level ≠ pp.U * m) :
    (C'.loc q).finishing = true := by
  obtain ⟨hj, -, hloc, -⟩ := tau_collect hI h hpc
  rw [hloc, if_neg (by omega)]
  set s1 := (C.loc q).setReg ⟨j, hj⟩ (C.mem () (π q ⟨j, hj⟩)) with hs1
  have hsum : ∑ i, (s1.regs i).level = ∑ x, (C.mem () x).level := by
    rw [← Equiv.sum_comp (π q) (fun x => (C.mem () x).level)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = ⟨j, hj⟩
    · subst hi; simp [hs1, St.setReg]
    · have : i.val < j := by
        have : i.val ≠ j := fun h' => hi (Fin.ext h')
        have := i.isLt; omega
      simp only [hs1, St.setReg, Function.update_of_ne hi]
      exact hcopy i this
  unfold afterCollect
  dsimp only
  rw [if_neg (by rw [hsum]; exact hU)]
  split_ifs with hc
  all_goals rw [(loopFrom_res pp _ 0).2.2.1]
  · rw [hsum] at hc
    push Not at hc
    have := hc hW
    revert this; cases s1.finishing <;> simp

end Steps

end BezoutElection.Alg2
