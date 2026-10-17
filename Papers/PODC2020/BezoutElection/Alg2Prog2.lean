import Papers.PODC2020.BezoutElection.Alg2Prog1

/-!
# Algorithm 2, progress: executions in which no competition is solved any more

`PCtx e` collects the hypotheses of the proof of `alg2_progress` by contradiction: from time `t0`
on, no competition is solved. Then no process ever returns, from some time `T` on every process is
pending and takes only internal steps, the levels of the registers are constant, and every process
reads every one of its local registers infinitely often (`reads`).
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P] [Fintype P]
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id} {R : Type} [Inhabited R]
  {out : Id → Finset Id → R}

/-- Hypotheses of the proof of `alg2_progress` by contradiction. -/
structure PCtx (e : ((alg2 Id m pp out).impl ids π).InfExec) where
  hm : 0 < m
  hid : Function.Injective ids
  hn : Fintype.card P = pp.n
  h1 : pp.W * pp.n ≤ pp.U * m
  h2 : pp.U * m ≤ pp.W * pp.n + pp.n
  hall : AllInvoke e
  hfair : e.IsFair
  t0 : ℕ
  hlt : solved (e.cfg t0) < pp.U * m
  hno : ∀ t ≥ t0, solved (e.cfg t) ≤ solved (e.cfg t0)

/-- The copies read in the current collect are up to date (levels). -/
def CopyInv (π : P → Equiv.Perm (Fin m)) (C : Cfg2 Id m R P) (q : P) : Prop :=
  ∀ j, (C.loc q).pc = .collect j → ∀ i : Fin m, i.val < j →
    ((C.loc q).regs i).level = (C.mem () (π q i)).level

lemma copyInv_step {α : List (Label P (elecObj R))} {C C' : Cfg2 Id m R P}
    {ℓ : Label P (elecObj R)} (hR : RInv π pp ids out α C)
    (h : ((alg2 Id m pp out).impl ids π).step C ℓ = some C') {q : P}
    (hlev : ∀ x, (C'.mem () x).level = (C.mem () x).level) (hℓ : ℓ.proc = q → ℓ = .tau q)
    (hI : CopyInv π C q) : CopyInv π C' q := by
  intro j hpc' i hi
  rw [hlev]
  by_cases hq : ℓ.proc = q
  swap
  · rw [(Impl.step_other h hq).1] at hpc' ⊢; exact hI j hpc' i hi
  rw [hℓ hq] at h
  rcases tau_pc h with ⟨j0, hpc⟩ | ⟨j0, w, hpc⟩
  · obtain ⟨hj, hmem, hloc, -⟩ := tau_collect hR h hpc
    obtain ⟨-, hmid, hlast⟩ := tau_collect_pc hR h hpc
    by_cases hj1 : j0 + 1 < m
    · rw [hmid hj1] at hpc'
      cases hpc'
      rw [hloc, if_pos hj1]
      by_cases hij : i = ⟨j0, hj⟩
      · subst hij; simp [St.setReg]
      · simp only [St.setReg, Function.update_of_ne hij]
        exact hI j0 hpc i (by have : i.val ≠ j0 := fun h' => hij (Fin.ext h'); omega)
    · rcases hlast hj1 with ⟨L, h'⟩ | h' | ⟨j', w', -, h'⟩
      · rw [h'] at hpc'; cases hpc'
      · rw [h'] at hpc'; cases hpc'; omega
      · rw [h'] at hpc'; cases hpc'
  · obtain ⟨-, h'⟩ := tau_write_pc hR h hpc
    rcases h' with h' | ⟨j', w', -, -, h'⟩
    · rw [h'] at hpc'; cases hpc'; omega
    · rw [h'] at hpc'; cases hpc'

namespace PCtx

variable {e : ((alg2 Id m pp out).impl ids π).InfExec} (Q : PCtx e)
include Q

lemma nonempty : Nonempty P := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h0 : pp.n = 0 := by rw [← Q.hn]; exact Fintype.card_eq_zero
  have h2 := Q.h2; have := Q.hlt
  rw [h0] at h2
  omega

lemma rinv (τ : ℕ) : RInv π pp ids out (e.lbls τ) (e.cfg τ) := by
  have := Q.nonempty
  exact rinv_run Q.hm Q.hid Q.hn (e.run_lbls τ)

lemma level_mono {a b : ℕ} (h : a ≤ b) (x : Fin m) :
    ((e.cfg a).mem () x).level ≤ ((e.cfg b).mem () x).level := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact ih.trans (step_level_mono (Q.rinv b) (e.step_eq b) x)

lemma solved_mono {a b : ℕ} (h : a ≤ b) : solved (e.cfg a) ≤ solved (e.cfg b) :=
  Finset.sum_le_sum fun x _ => Q.level_mono h x

lemma solved_le (τ : ℕ) : solved (e.cfg τ) ≤ solved (e.cfg Q.t0) := by
  rcases le_total τ Q.t0 with h | h
  · exact Q.solved_mono h
  · exact Q.hno τ h

/-- The levels are constant from `t0` on. -/
lemma lev_eq {τ : ℕ} (hτ : Q.t0 ≤ τ) (x : Fin m) :
    ((e.cfg τ).mem () x).level = ((e.cfg Q.t0).mem () x).level := by
  have hs : solved (e.cfg τ) = solved (e.cfg Q.t0) :=
    le_antisymm (Q.hno τ hτ) (Q.solved_mono hτ)
  exact ((Finset.sum_eq_sum_iff_of_le (fun x _ => Q.level_mono hτ x)).1 hs.symm x
    (mem_univ x)).symm

lemma not_all_U (τ : ℕ) : ¬∀ x, ((e.cfg τ).mem () x).level = pp.U := by
  intro hU
  have : solved (e.cfg τ) = pp.U * m := by simp [solved, hU, mul_comm]
  have := Q.solved_le τ; have := Q.hlt
  omega

/-- No process ever returns. -/
lemma no_ret (τ : ℕ) (q : P) (r : (elecObj R).Resp) : e.lbl τ ≠ .ret q r := by
  intro hl
  have hmem : Label.ret q r ∈ e.lbls (τ + 1) := by
    simp only [Impl.InfExec.lbls, List.mem_map, List.mem_range]
    exact ⟨τ, by omega, hl⟩
  obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.1 (outputs_ne_none_of_mem hmem)
  exact Q.not_all_U (τ + 1) ((Q.rinv (τ + 1)).out q r' hr').1

lemma pc_ne_ret (τ : ℕ) (q : P) (L : Finset Id) : ((e.cfg τ).loc q).pc ≠ .ret L := by
  intro hpc
  obtain ⟨g, G⟩ := (Q.rinv τ).g
  exact Q.not_all_U τ (G.ret q L (by simp [vpcOf, hpc])).1

lemma pend_ex : ∃ T ≥ Q.t0, ∀ τ ≥ T, ∀ q, (e.cfg τ).pend q ≠ none := by
  obtain ⟨T, hT, h⟩ := ev_forall_fin (fun q τ => (e.cfg τ).pend q ≠ none) (fun q => by
    obtain ⟨tq, o, htq⟩ := Q.hall q
    refine ⟨tq + 1, fun τ hτ => ?_⟩
    induction τ, hτ using Nat.le_induction with
    | base =>
      have h := e.step_eq tq
      rw [htq] at h
      obtain ⟨-, -, h1, -, -⟩ := Impl.step_inv h
      rw [h1]; simp
    | succ τ _ ih =>
      intro hnone
      obtain ⟨r, hr⟩ := Impl.step_pend_none (e.step_eq τ) ih hnone
      exact Q.no_ret τ q r hr) Q.t0
  exact ⟨T, hT, h⟩

/-- From time `T` on, all processes are pending. -/
noncomputable def T : ℕ := Classical.choose Q.pend_ex

lemma t0_le_T : Q.t0 ≤ Q.T := (Classical.choose_spec Q.pend_ex).1

lemma pend {τ : ℕ} (hτ : Q.T ≤ τ) (q : P) : (e.cfg τ).pend q ≠ none :=
  (Classical.choose_spec Q.pend_ex).2 τ hτ q

lemma lbl_tau {τ : ℕ} (hτ : Q.T ≤ τ) : e.lbl τ = .tau (e.lbl τ).proc := by
  cases hl : e.lbl τ with
  | inv q o =>
    have h := e.step_eq τ
    rw [hl] at h
    exact absurd (Impl.step_inv h).1 (Q.pend hτ q)
  | tau q => rfl
  | ret q r => exact absurd hl (Q.no_ret τ q r)

omit Q in
/-- The number of steps of a process before its next read of its local register `k`. -/
def rdMeas (m k : ℕ) : PC Id → ℕ
  | .collect j => if j ≤ k then k - j else (m - j) + m + k + 2
  | .write j _ => (m - j) + k + 1
  | _ => 0

/-- **Fairness for the registers**: every process reads each of its local registers infinitely
often. -/
lemma reads (q : P) (k : Fin m) (τ : ℕ) :
    ∃ τ' ≥ τ, e.lbl τ' = .tau q ∧ ((e.cfg τ').loc q).pc = .collect k.val := by
  by_contra hne
  push Not at hne
  refine InfExec.descent e Q.hfair q (max τ Q.T)
    (fun τ' => rdMeas m k.val ((e.cfg τ').loc q).pc) (fun τ' h => Q.pend (by omega) q) ?_ ?_
  · intro τ' _ hq
    have := (Impl.step_other (e.step_eq _) hq).1
    simp only [this, le_refl]
  · intro τ' hτ' hq
    have hl : e.lbl τ' = .tau q := by rw [Q.lbl_tau (by omega), hq]
    have h := e.step_eq τ'
    rw [hl] at h
    have hk := hne τ' (by omega) hl
    have hR := Q.rinv τ'
    have hkm := k.isLt
    show rdMeas m k.val ((e.cfg (τ' + 1)).loc q).pc < rdMeas m k.val ((e.cfg τ').loc q).pc
    rcases tau_pc h with ⟨j, hpc⟩ | ⟨j, w, hpc⟩
    · obtain ⟨hj, hmid, hlast⟩ := tau_collect_pc hR h hpc
      have hjk : j ≠ k.val := fun h' => hk (by rw [hpc, h'])
      rw [hpc]
      by_cases hj1 : j + 1 < m
      · rw [hmid hj1]; simp only [rdMeas]; split_ifs <;> omega
      · rcases hlast hj1 with ⟨L, h'⟩ | h' | ⟨j', w', hj', h'⟩
        · exact absurd h' (Q.pc_ne_ret _ q L)
        · rw [h']; simp only [rdMeas]; split_ifs <;> omega
        · rw [h']; simp only [rdMeas]; split_ifs <;> omega
    · obtain ⟨hj, h'⟩ := tau_write_pc hR h hpc
      rw [hpc]
      rcases h' with h' | ⟨j', w', h1, h2, h'⟩
      · rw [h']; simp only [rdMeas]; split_ifs <;> omega
      · rw [h']; simp only [rdMeas]; omega

lemma copyInv_from {q : P} {τ₁ : ℕ} (hτ₁ : Q.T ≤ τ₁) (hpc : ((e.cfg τ₁).loc q).pc = .collect 0)
    {τ : ℕ} (hτ : τ₁ ≤ τ) : CopyInv π (e.cfg τ) q := by
  induction τ, hτ using Nat.le_induction with
  | base => intro j hj i hi; rw [hpc] at hj; cases hj; omega
  | succ τ hτ ih =>
    have hT := Q.t0_le_T
    refine copyInv_step (Q.rinv τ) (e.step_eq τ) (fun x => ?_) (fun hq => ?_) ih
    · rw [Q.lev_eq (by omega), Q.lev_eq (τ := τ) (by omega)]
    · rw [Q.lbl_tau (by omega), hq]

/-- A process that has not set `finishing` sets it at its next complete collect when at least
`W n` competitions are solved. -/
lemma fin_set (q : P) (τ : ℕ) (hW : pp.W * pp.n ≤ solved (e.cfg Q.t0)) :
    ∃ τ' ≥ τ, ((e.cfg τ').loc q).finishing = true := by
  have hT := Q.t0_le_T
  obtain ⟨τ₁, hτ₁, -, hpc₁⟩ := Q.reads q ⟨0, Q.hm⟩ (max τ Q.T)
  obtain ⟨τ₂, hτ₂, hl, hpc₂⟩ := Q.reads q ⟨m - 1, by have := Q.hm; omega⟩ τ₁
  have h := e.step_eq τ₂
  rw [hl] at h
  have hsol : solved (e.cfg τ₂) = solved (e.cfg Q.t0) :=
    le_antisymm (Q.hno τ₂ (by omega)) (Q.solved_mono (by omega))
  refine ⟨τ₂ + 1, by omega, tau_last_fin (Q.rinv τ₂) h hpc₂ (by have := Q.hm; simp; omega)
    (Q.copyInv_from (by omega) hpc₁ (by omega) _ hpc₂) ?_ ?_⟩
  · show pp.W * pp.n ≤ solved (e.cfg τ₂); omega
  · show solved (e.cfg τ₂) ≠ pp.U * m; have := Q.hlt; omega

end PCtx

end BezoutElection.Alg2
