import Papers.PODC2020.BezoutElection.Alg2Prog2

/-!
# Algorithm 2, progress: the abstract runs of the registers

In an execution where no competition is solved any more (`PCtx`), every register `x` gives an
abstract run `Q.run x` (`sim_step`); for an open register it satisfies the hypotheses `LCtx0` of
the liveness of a competition (`Q.lctx0`). The candidate flags eventually stabilize
(`LCtx0.ca_stab`).
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

section Abstract

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

/-- A candidate stops being a candidate only by losing or by winning. -/
lemma procX_ca_false {me : Id} {l : ALoc Id} {r : Reg Id} {ok fin : Bool} (hca : l.ca = true)
    (h : (procX n U me l r ok fin).1.ca = false) :
    (procX n U me l r ok fin).1.lo = true ∨
      ∃ w, (procX n U me l r ok fin).2 = some w ∧ w.level = r.level + 1 := by
  unfold procX at h ⊢
  split_ifs at h ⊢ <;> simp_all

namespace LCtx0

variable {R : ARun n U ids} (X : LCtx0 R)
include X

/-- Once the losers are stable, candidates stay candidates. -/
lemma ca_mono {T₁ : ℕ} (hT₁ : ∀ t ≥ T₁, ∀ q, ((R.A t).loc q).lv = X.L) {T₂ : ℕ} (hT₂ : T₁ ≤ T₂)
    (hlos : ∀ t ≥ T₂, ∀ q, ((R.A t).loc q).lo = ((R.A T₂).loc q).lo) (t : ℕ) (ht : T₂ ≤ t) (q : P)
    (h : ((R.A t).loc q).ca = true) : ((R.A (t + 1)).loc q).ca = true := by
  rcases X.loc_cases t q with h1 | ⟨-, -, h1⟩ | ⟨-, v, ok, fin, hv, h1, -⟩ | ⟨-, w, -, h1⟩
  · rw [h1]; exact h
  · rw [h1]; exact h
  · by_contra hne
    have hne' : ((R.A (t + 1)).loc q).ca = false := by simpa using hne
    rw [h1] at hne'
    simp only [procL] at hne'
    rcases procX_ca_false h hne' with h2 | ⟨w, h2, h3⟩
    · have hlo := ((R.inv t).1.caAct q h).2
      have e1 := hlos t ht q
      have e2 := hlos (t + 1) (by omega) q
      rw [h1] at e2
      simp only [procL] at e2
      rw [h2] at e2
      rw [← e1, hlo] at e2
      cases e2
    · have hst : ((R.A (t + 1)).loc q).st = .pend w := by
        rw [h1]; simp [procL, h2, stOf]
      have := X.nowin (t + 1) q w hst
      have hv' := X.copy_level hv
      rw [hT₁ t (by omega)] at hv'
      omega
  · rw [h1]; exact h

/-- The candidates eventually stabilize. -/
lemma ca_stab : ∃ T₃, ∀ t ≥ T₃, ∀ q, ((R.A (t + 1)).loc q).ca = ((R.A t).loc q).ca := by
  obtain ⟨T₁, hT₁⟩ := X.active
  obtain ⟨T₂, hT₂, hlos⟩ := X.losers hT₁
  obtain ⟨T₃, hT₃, hc⟩ := Finset.eventually_const_of_subset_succ_of_finite
    (f := fun t => Finset.univ.filter (fun q => ((R.A t).loc q).ca = true)) (N := T₂)
    (fun t ht q hq => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact X.ca_mono hT₁ hT₂ hlos t ht q hq)
  refine ⟨T₃, fun t ht q => ?_⟩
  have h1 := Finset.ext_iff.1 (hc (t + 1) (by omega)) q
  have h2 := Finset.ext_iff.1 (hc t ht) q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  exact Bool.eq_iff_iff.2 (h1.trans h2.symm)

end LCtx0

end Abstract

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P] [Fintype P]
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id} {R : Type} [Inhabited R]
  {out : Id → Finset Id → R}

/-- The abstraction of the register `x` at time `τ`. -/
noncomputable def absT (e : ((alg2 Id m pp out).impl ids π).InfExec) (x : Fin m) (τ : ℕ) :
    AState Id P :=
  absAt π ((e.cfg τ).mem ()) (e.cfg τ).loc (vpcOf (e.cfg τ).loc) x

namespace PCtx

variable {e : ((alg2 Id m pp out).impl ids π).InfExec} (Q : PCtx e)
include Q

lemma simT (x : Fin m) (τ : ℕ) :
    SimOK pp ids π (absT e x τ) (absT e x (τ + 1)) (e.lbl τ).proc ((e.cfg τ).loc (e.lbl τ).proc)
      ((e.cfg (τ + 1)).loc (e.lbl τ).proc) x
      (∃ q, ∃ k : Fin m, e.lbl τ = .tau q ∧ ((e.cfg τ).loc q).pc = .collect k.val ∧ π q k = x) :=
  sim_step (Q.rinv τ) (e.step_eq τ) x

/-- The abstract transition of the step at time `τ` at the register `x`. -/
noncomputable def trT (x : Fin m) (τ : ℕ) : ATr := Classical.choose (Q.simT x τ)

lemma trT_spec (x : Fin m) (τ : ℕ) :
    ATrRel pp.n pp.U ids (absT e x τ) (e.lbl τ).proc (Q.trT x τ) (absT e x (τ + 1)) ∧
    ((∃ q, ∃ k : Fin m, e.lbl τ = .tau q ∧ ((e.cfg τ).loc q).pc = .collect k.val ∧ π q k = x) →
      Q.trT x τ = .read ∨ ∃ ok fin, Q.trT x τ = .readProc ok fin) ∧
    (∀ ok fin, (Q.trT x τ = .proc ok fin ∨ Q.trT x τ = .readProc ok fin) → ∃ s_mid : St Id m,
      ok = okOf s_mid ((π (e.lbl τ).proc).symm x) ∧ fin = s_mid.finishing ∧
      MidOK ((e.cfg τ).loc (e.lbl τ).proc) ((e.cfg (τ + 1)).loc (e.lbl τ).proc) s_mid) :=
  Classical.choose_spec (Q.simT x τ)

/-- The abstract run of the register `x` from time `T` on. -/
noncomputable def run (x : Fin m) : ARun pp.n pp.U ids where
  A i := absT e x (Q.T + i)
  who i := (e.lbl (Q.T + i)).proc
  tr i := Q.trT x (Q.T + i)
  step i := (Q.trT_spec x (Q.T + i)).1
  inv i := by obtain ⟨g, G⟩ := (Q.rinv (Q.T + i)).g; exact G.abs x

lemma run_loc (x : Fin m) (i : ℕ) (q : P) : ((Q.run x).A i).loc q =
    locX ((e.cfg (Q.T + i)).loc q) ((π q).symm x)
      (vstatus (.pc ((e.cfg (Q.T + i)).loc q).pc) ((e.cfg (Q.T + i)).loc q) ((π q).symm x)) := rfl

lemma run_reg (x : Fin m) (i : ℕ) : ((Q.run x).A i).reg = (e.cfg (Q.T + i)).mem () x := rfl

/-- No write of line N(11) is ever pending from time `T` on (it would solve a competition). -/
lemma nowin_conc {τ : ℕ} (hτ : Q.T ≤ τ) {q : P} {j : ℕ} {w : Reg Id}
    (hpc : ((e.cfg τ).loc q).pc = .write j w) (hj : j < m) :
    w.level = ((e.cfg τ).mem () (π q ⟨j, hj⟩)).level := by
  have hT := Q.t0_le_T
  rcases ((Q.rinv τ).level_lt_of_write hpc hj).2 with h | h
  · exact h
  · exfalso
    obtain ⟨τ', hτ', hq, -, hloc, -⟩ := e.first_act Q.hfair (Q.pend hτ q)
    have hl : e.lbl τ' = .tau q := by rw [Q.lbl_tau (by omega), hq]
    have h' := e.step_eq τ'
    rw [hl] at h'
    obtain ⟨hj', hmem, -, -⟩ := tau_write (Q.rinv τ') h' (by rw [hloc]; exact hpc)
    have e1 := Q.lev_eq (τ := τ' + 1) (by omega) (π q ⟨j, hj⟩)
    have e2 := Q.lev_eq (τ := τ) (by omega) (π q ⟨j, hj⟩)
    rw [hmem] at e1
    simp only [Function.update_self] at e1
    omega

lemma run_st_pend {x : Fin m} {i : ℕ} {q : P} {w : Reg Id}
    (h : (((Q.run x).A i).loc q).st = .pend w) :
    ((e.cfg (Q.T + i)).loc q).pc = .write ((π q).symm x).val w := by
  rw [run_loc] at h
  have h' : vstatus (.pc ((e.cfg (Q.T + i)).loc q).pc) ((e.cfg (Q.T + i)).loc q) ((π q).symm x) =
      .pend w := h
  rw [vstatus_pend_iff] at h'
  simp only [VPC.pc.injEq] at h'
  exact h'

/-- The hypotheses of the liveness of the competition of an open register. -/
noncomputable def lctx0 (x : Fin m) (hx : ((e.cfg Q.t0).mem () x).level < pp.U) :
    LCtx0 (Q.run x) where
  hid := Q.hid
  hn := Q.hn
  L := ((e.cfg Q.t0).mem () x).level
  hLU := hx
  lev i := Q.lev_eq (by have := Q.t0_le_T; omega) x
  nowin i q w h := by
    have hpc := Q.run_st_pend h
    have := Q.nowin_conc (by omega) hpc ((π q).symm x).isLt
    simp only [Fin.eta, Equiv.apply_symm_apply] at this
    rw [this, Q.lev_eq (by have := Q.t0_le_T; omega) x]
  fair q i := by
    obtain ⟨τ', hτ', hl, hpc⟩ := Q.reads q ((π q).symm x) (Q.T + i)
    refine ⟨τ' - Q.T, by omega, ?_, ?_⟩
    · show (e.lbl (Q.T + (τ' - Q.T))).proc = q
      rw [Nat.add_sub_cancel' (by omega), hl]; rfl
    · show Q.trT x (Q.T + (τ' - Q.T)) = .read ∨ ∃ ok fin, Q.trT x (Q.T + (τ' - Q.T)) = .readProc ok fin
      rw [Nat.add_sub_cancel' (by omega)]
      exact (Q.trT_spec x τ').2.1 ⟨q, _, hl, hpc, by simp⟩

end PCtx

end BezoutElection.Alg2
