import Papers.PODC2020.BezoutElection.Alg2Safety

/-!
# Algorithm 2: termination (Lemma 1), reduced to the progress of the competitions

* `step_level_mono`: the levels of the registers never decrease.
* `return_of_solved`: once all registers are at level `U` (all competitions solved), every
  pending process returns within finitely many of its own steps.
* `alg2_terminates_of_progress`: hence termination follows from the *progress property*
  `Progress` (as long as not all competitions are solved, some competition is eventually
  solved).

The progress property itself (the paper's argument "all competitions that have at least one
candidate terminate, and until `d` leaders are elected some competition has a candidate") is
`alg2_progress` (`Alg2Prog5.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P] {m : ℕ}
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id} {R : Type} [Inhabited R]
  {out : Id → Finset Id → R}

/-- Configurations of Algorithm 2. -/
abbrev Cfg2 (Id : Type) (m : ℕ) (R : Type) [Inhabited R] (P : Type) :=
  Config (elecObj R) (fun _ : Unit => memObj m (Reg Id) Reg.init) P (St Id m)

/-- The number of solved competitions: the sum of the levels. -/
def solved (C : Cfg2 Id m R P) : ℕ := ∑ x, (C.mem () x).level

/-- A pending write goes to a register of level below `U`. -/
lemma RInv.level_lt_of_write {α : List (Label P (elecObj R))} {C : Cfg2 Id m R P}
    (hI : RInv π pp ids out α C) {q : P} {j : ℕ} {w : Reg Id} (hpc : (C.loc q).pc = .write j w)
    (hj : j < m) : (C.mem () (π q ⟨j, hj⟩)).level < pp.U ∧
      (w.level = (C.mem () (π q ⟨j, hj⟩)).level ∨ w.level = (C.mem () (π q ⟨j, hj⟩)).level + 1) := by
  obtain ⟨g, G⟩ := hI.g
  have A0 := G.abs (π q ⟨j, hj⟩)
  have hst : ((absAt π (C.mem ()) C.loc (vpcOf C.loc) (π q ⟨j, hj⟩)).loc q).st = .pend w := by
    rw [absAt_loc, Equiv.symm_apply_apply]; simp [locX, vstatus, vpcOf, hpc]
  obtain ⟨-, hlt, hc⟩ := A0.1.pendLv q w hst
  refine ⟨hlt, ?_⟩
  rcases hc with ⟨h, -⟩ | h
  · exact Or.inl h
  · exact Or.inr h.1

/-- The levels of the registers never decrease. -/
theorem step_level_mono {α : List (Label P (elecObj R))} {C C' : Cfg2 Id m R P}
    {ℓ : Label P (elecObj R)} (hI : RInv π pp ids out α C)
    (h : ((alg2 Id m pp out).impl ids π).step C ℓ = some C') (x : Fin m) :
    (C.mem () x).level ≤ (C'.mem () x).level := by
  cases ℓ with
  | inv q o => obtain ⟨-, rfl⟩ := SymAlg.impl_step_inv_cases h; exact le_rfl
  | ret q r => obtain ⟨-, s, -, rfl⟩ := SymAlg.impl_step_ret_cases h; exact le_rfl
  | tau q =>
    obtain ⟨hp, ⟨x0, f, k, hact, rfl⟩ | ⟨k, hact, -⟩⟩ := SymAlg.impl_step_tau_cases h
    swap
    · exfalso
      simp only [alg2] at hact
      split at hact <;> (try split at hact) <;> simp at hact
    rcases hpc : (C.loc q).pc with _ | j | ⟨j, w⟩ | L | _
    · rw [act_idle _ hpc] at hact; cases hact
    · have hj := (hI.pcok q).1 j hpc
      rw [act_collect _ hpc hj] at hact
      simp only [SymAction.rmw.injEq] at hact
      obtain ⟨rfl, rfl, rfl⟩ := hact
      simp
    · have hj := (hI.pcok q).2 j w hpc
      rw [act_write _ hpc hj] at hact
      simp only [SymAction.rmw.injEq] at hact
      obtain ⟨rfl, rfl, rfl⟩ := hact
      obtain ⟨-, hw⟩ := hI.level_lt_of_write hpc hj
      simp only [Function.update_self]
      by_cases hx : x = π q ⟨j, hj⟩
      · subst hx; simp only [Function.update_self]; omega
      · simp [Function.update_of_ne hx]
    · rw [act_ret _ hpc] at hact; cases hact
    · rw [act_fin _ hpc] at hact; cases hact

/-- Progress measure of a process once all registers are at level `U`: the remaining number of
reads before returning (at most two collects). -/
def meas (pp : Params) (s : St Id m) : ℕ :=
  match s.pc with
  | .collect k =>
    if ∀ j : Fin m, j.val < k → (s.regs j).level = pp.U then m + 1 - k else 2 * m + 2 - k
  | _ => 0

variable [Nonempty P]

/-- Once all competitions are solved, every internal step of a process decreases its measure. -/
theorem tau_meas (hm : 0 < m) (hid : Function.Injective ids) (hn : Fintype.card P = pp.n)
    {α : List (Label P (elecObj R))} {C C' : Cfg2 Id m R P} (hI : RInv π pp ids out α C)
    (hU : ∀ x, (C.mem () x).level = pp.U) {q : P}
    (h : ((alg2 Id m pp out).impl ids π).step C (.tau q) = some C') :
    meas pp (C'.loc q) < meas pp (C.loc q) := by
  have hI' := rinv_step hm hid hn hI h
  obtain ⟨hp, ⟨x0, f, k, hact, rfl⟩ | ⟨k, hact, -⟩⟩ := SymAlg.impl_step_tau_cases h
  swap
  · exfalso
    simp only [alg2] at hact
    split at hact <;> (try split at hact) <;> simp at hact
  rcases hpc : (C.loc q).pc with _ | j | ⟨j, w⟩ | L | _
  · rw [act_idle _ hpc] at hact; cases hact
  · have hj := (hI.pcok q).1 j hpc
    rw [act_collect _ hpc hj] at hact
    simp only [SymAction.rmw.injEq] at hact
    obtain ⟨rfl, rfl, rfl⟩ := hact
    simp only [Function.update_self]
    set v := C.mem () (π q ⟨j, hj⟩) with hv
    have hvU : v.level = pp.U := hU _
    -- the copies read so far are of level at most `U`
    obtain ⟨g, G⟩ := hI.g
    have hcopyle : ∀ i : Fin m, i.val < j → ((C.loc q).regs i).level ≤ pp.U := by
      intro i hi
      have A := G.abs (π q i)
      have hst : ((absAt π (C.mem ()) C.loc (vpcOf C.loc) (π q i)).loc q).st =
          .copy ((C.loc q).regs i) := by
        rw [absAt_loc, Equiv.symm_apply_apply]; simp only [locX, vstatus, vpcOf, hpc]
        rw [if_neg (by omega)]
      have := (A.1.copyLv q _ hst).2
      simp only [absAt_reg, hU] at this; exact this
    have hold : meas pp (C.loc q) = if ∀ i : Fin m, i.val < j → ((C.loc q).regs i).level = pp.U
        then m + 1 - j else 2 * m + 2 - j := by simp [meas, hpc]
    rw [hold]
    -- the copies after the read
    have hregs : ∀ i : Fin m, (((C.loc q).setReg ⟨j, hj⟩ v).regs i).level =
        if i = ⟨j, hj⟩ then pp.U else ((C.loc q).regs i).level := by
      intro i; by_cases hi : i = ⟨j, hj⟩
      · subst hi; simp [St.setReg, hvU]
      · simp [St.setReg, Function.update_of_ne hi, hi]
    have hgood_iff : (∀ i : Fin m, i.val < j + 1 → (((C.loc q).setReg ⟨j, hj⟩ v).regs i).level = pp.U) ↔
        (∀ i : Fin m, i.val < j → ((C.loc q).regs i).level = pp.U) := by
      constructor
      · intro h i hi
        have := h i (by omega); rw [hregs, if_neg (fun h' => by rw [h'] at hi; simp at hi)] at this
        exact this
      · intro h i hi
        rw [hregs]
        split_ifs with h'
        · rfl
        · exact h i (by
            have : i.val ≠ j := fun h'' => h' (Fin.ext h'')
            omega)
    by_cases hj1 : j + 1 < m
    · rw [if_pos hj1]
      simp only [meas]
      rw [show (if ∀ i : Fin m, i.val < j + 1 → (({ (C.loc q).setReg ⟨j, hj⟩ v with
          pc := .collect (j + 1) } : St Id m).regs i).level = pp.U then m + 1 - (j + 1)
          else 2 * m + 2 - (j + 1)) = (if ∀ i : Fin m, i.val < j → ((C.loc q).regs i).level = pp.U
          then m + 1 - (j + 1) else 2 * m + 2 - (j + 1)) from if_congr hgood_iff rfl rfl]
      split_ifs <;> omega
    · rw [if_neg hj1]
      have hjm : j + 1 = m := by omega
      set s' := (C.loc q).setReg ⟨j, hj⟩ v with hs'
      by_cases hgood : ∀ i : Fin m, i.val < j → ((C.loc q).regs i).level = pp.U
      · rw [if_pos hgood]
        have hall : ∀ i : Fin m, (s'.regs i).level = pp.U := by
          intro i
          have := (hgood_iff.2 hgood) i (by omega)
          exact this
        have hsum : ∑ i, (s'.regs i).level = pp.U * m := by simp [hall, mul_comm]
        simp only [afterCollect, hsum, if_true, meas]
        omega
      · rw [if_neg hgood]
        push Not at hgood
        obtain ⟨i0, hi0, hne⟩ := hgood
        have hlt : ∑ i, (s'.regs i).level < ∑ _i : Fin m, pp.U := by
          apply Finset.sum_lt_sum
          · intro i _
            rw [hregs]; split_ifs with h'
            · exact le_rfl
            · exact hcopyle i (by have : i.val ≠ j := fun h'' => h' (Fin.ext h''); omega)
          · refine ⟨i0, mem_univ _, ?_⟩
            rw [hregs, if_neg (fun h' => by rw [h'] at hi0; simp at hi0)]
            exact lt_of_le_of_ne (hcopyle i0 hi0) hne
        have hsum : ∑ i, (s'.regs i).level ≠ pp.U * m := by
          intro h'; rw [h'] at hlt; simp [mul_comm] at hlt
        -- the for loop writes nothing: all registers are at level `U`
        have hpc' : (afterCollect pp s').pc = .collect 0 := by
          have hloop := hI'.pcok q
          unfold afterCollect at hloop ⊢
          simp only [hsum, if_false] at hloop ⊢
          rcases loopFrom_pc (pp := pp) (if pp.W * pp.n ≤ ∑ x, (s'.regs x).level ∧
              s'.finishing = false then { s' with finishing := true, toWin := 1 } else s') 0 with
            h1 | ⟨k', w', hk', h1⟩
          · exact h1
          · exfalso
            have hw := hI'.level_lt_of_write (q := q) (j := k') (w := w') (by
              simp only [Function.update_self]
              rw [if_neg hj1, ← hs']
              unfold afterCollect; simp only [hsum, if_false]; exact h1) hk'
            have := hU (π q ⟨k', hk'⟩)
            have hw1 := hw.1
            simp only [hv, Function.update_eq_self] at hw1
            omega
        simp only [meas, hpc']
        simp only [Fin.isValue, not_lt_zero', false_imp_iff, implies_true, if_true]
        omega
  · have hj := (hI.pcok q).2 j w hpc
    have := (hI.level_lt_of_write hpc hj).1
    rw [hU] at this; omega
  · rw [act_ret _ hpc] at hact; cases hact
  · rw [act_fin _ hpc] at hact; cases hact

omit [Nonempty P] in
/-- **Lemma 1 (termination) from the progress property.** If, in every fair execution in which all
processes participate, a competition is eventually solved as long as not all of them are solved,
then every process returns. -/
theorem alg2_terminates_of_progress (hm : 0 < m) (hid : Function.Injective ids)
    (hn : Fintype.card P = pp.n)
    (hprog : ∀ e : ((alg2 Id m pp out).impl ids π).InfExec, IsOneShot e → AllInvoke e →
      e.Fair → ∀ t, solved (e.cfg t) < pp.U * m → ∃ t', t ≤ t' ∧ solved (e.cfg t) < solved (e.cfg t')) :
    Terminates ((alg2 Id m pp out).impl ids π) := by
  intro e hos hall hfair p
  by_contra hnot
  push Not at hnot
  have : Nonempty P := ⟨p⟩
  have hR : ∀ t, RInv π pp ids out (e.pre t) (e.cfg t) :=
    fun t => rinv_run hm hid hn (e.run_pre t)
  have hlev : ∀ t x, ((e.cfg t).mem () x).level ≤ ((e.cfg (t + 1)).mem () x).level :=
    fun t x => step_level_mono (hR t) (e.step_eq t) x
  have hlevU : ∀ t x, ((e.cfg t).mem () x).level ≤ pp.U := by
    intro t x; obtain ⟨g, G⟩ := (hR t).g; exact (G.abs x).1.lvU
  have hSmono : ∀ t, solved (e.cfg t) ≤ solved (e.cfg (t + 1)) :=
    fun t => Finset.sum_le_sum fun x _ => hlev t x
  have hSle : ∀ t, solved (e.cfg t) ≤ pp.U * m := by
    intro t
    calc solved (e.cfg t) ≤ ∑ _x : Fin m, pp.U := Finset.sum_le_sum fun x _ => hlevU t x
      _ = pp.U * m := by simp [mul_comm]
  -- the number of solved competitions is eventually constant
  obtain ⟨t0, -, ht0⟩ := Nat.eventually_const_of_le_succ (f := fun t => solved (e.cfg t)) (N := 0)
    (fun t _ => hSle t) (fun t _ => hSmono t)
  by_cases hlt : solved (e.cfg t0) < pp.U * m
  · obtain ⟨t', ht', hgt⟩ := hprog e hos hall hfair t0 hlt
    rw [ht0 t' ht'] at hgt; exact lt_irrefl _ hgt
  -- all competitions are solved from `t0` on
  have hU : ∀ t, t0 ≤ t → ∀ x, ((e.cfg t).mem () x).level = pp.U := by
    have h0 : ∀ x, ((e.cfg t0).mem () x).level = pp.U := by
      have h2 : ∑ x, ((e.cfg t0).mem () x).level = ∑ _x : Fin m, pp.U := by
        have h3 : ∑ _x : Fin m, pp.U = pp.U * m := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
        have := hSle t0; simp only [solved] at hlt this; rw [h3]; omega
      intro x; exact (sum_eq_sum_iff_of_le (fun x _ => hlevU t0 x)).1 h2 x (mem_univ x)
    intro t ht x
    induction t, ht using Nat.le_induction with
    | base => exact h0 x
    | succ t _ ih => have := hlev t x; have := hlevU (t + 1) x; omega
  -- `p` is invoked and stays pending
  obtain ⟨tp, o, htp⟩ := hall p
  have hpend : ∀ t, tp + 1 ≤ t → (e.cfg t).pend p ≠ none := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      have h := e.step_eq tp
      rw [htp] at h
      obtain ⟨-, -, h1, -, -⟩ := Impl.step_inv h
      rw [h1]; simp
    | succ t _ ih =>
      intro hnone
      obtain ⟨r, hr⟩ := Impl.step_pend_none (e.step_eq t) ih hnone
      exact hnot t r hr
  set T := max t0 (tp + 1) with hT
  have hstep : ∀ t, T ≤ t → (e.lbl t).proc = p → e.lbl t = .tau p := by
    intro t ht hproc
    cases hl : e.lbl t with
    | inv q o' =>
      rw [hl] at hproc; simp only [Label.proc] at hproc; subst hproc
      have h := e.step_eq t; rw [hl] at h
      exact absurd (Impl.step_inv h).1 (hpend t (by omega))
    | tau q => rw [hl] at hproc; simp only [Label.proc] at hproc; subst hproc; rfl
    | ret q r => rw [hl] at hproc; simp only [Label.proc] at hproc; subst hproc; exact absurd hl (hnot t r)
  apply Nat.not_frequently_lt_of_succ_le (f := fun t => meas pp ((e.cfg t).loc p)) (N := T)
  · intro t ht
    by_cases hproc : (e.lbl t).proc = p
    · have h := e.step_eq t
      rw [hstep t ht hproc] at h
      exact (tau_meas hm hid hn (hR t) (hU t (by omega)) h).le
    · rw [(Impl.step_other (e.step_eq t) hproc).1]
  · intro N
    obtain ⟨t', ht', hproc, -⟩ := hfair p (max N T) (hpend _ (by omega))
    refine ⟨t', by omega, ?_⟩
    have h := e.step_eq t'
    rw [hstep t' (by omega) hproc] at h
    exact tau_meas hm hid hn (hR t') (hU t' (by omega)) h

omit [Nonempty P] in
/-- With no register every action is a response: processes return at their first step. -/
theorem terminates_of_m_zero (hm : m = 0) : Terminates ((alg2 Id m pp out).impl ids π) := by
  subst hm
  intro e hos hall hfair p
  obtain ⟨tp, o, htp⟩ := hall p
  have hp : (e.cfg (tp + 1)).pend p ≠ none := by
    have h := e.step_eq tp
    rw [htp] at h
    obtain ⟨-, -, h1, -, -⟩ := Impl.step_inv h
    rw [h1]; simp
  obtain ⟨t', -, hproc, hstep⟩ := hfair p (tp + 1) hp
  cases hl : e.lbl t' with
  | inv q o' => rw [hl] at hstep; exact absurd hstep (by simp [Label.IsStep])
  | ret q r => rw [hl] at hproc; simp only [Label.proc] at hproc; subst hproc; exact ⟨t', r, hl⟩
  | tau q =>
    exfalso
    rw [hl] at hproc; simp only [Label.proc] at hproc; subst hproc
    have h := e.step_eq t'
    rw [hl] at h
    obtain ⟨-, ⟨x, -, -, -, -⟩ | ⟨k, hact, -⟩⟩ := SymAlg.impl_step_tau_cases h
    · exact Fin.elim0 x
    · simp only [alg2] at hact
      split at hact <;> (try split at hact) <;> simp at hact

end BezoutElection.Alg2
