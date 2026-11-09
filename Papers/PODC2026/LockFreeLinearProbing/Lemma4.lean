import Papers.PODC2026.LockFreeLinearProbing.StepDup

/-!
# Lemma 4: at most one final copy of each key

`Inv` holds in every reachable configuration (with some ghost timestamps); its field `l4` is
Lemma 4 of the paper.
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] {h : K → Fin m}
variable {P : Type} [DecidableEq P] {N : ℕ} {ts : P → ℕ} {C C' : Cfg K m P} {p : P}

/-- A local state that owns nothing and is not about to `SC` (idle, about to return, or at the
start of an operation). -/
def Quiet (l : Loc K m) : Prop :=
  l.pc.isVal = false ∧ l.pc.isIns = false ∧ recorded l = none ∧ LocInv l ∧
    l.pc ≠ .docRD ∧ l.pc ≠ .docSC ∧ l.pc ≠ .docRD2

lemma Inv.mono (hI : Inv h N ts C) : Inv h (N + 1) ts C :=
  { hI with ts_lt := fun q => Nat.lt_succ_of_lt (hI.ts_lt q) }

/-- Replacing a quiet local state by another one (invocations and returns). -/
lemma inv_swap_quiet (hI : Inv h N ts C) {l' : Loc K m} (hq : Quiet (C.loc p)) (hq' : Quiet l')
    (pend' : P → Option (dict K).Op)
    (hid : ∀ q, pend' q = none → (update C.loc p l' q).pc = .idle) :
    Inv h N ts { C with loc := update C.loc p l', pend := pend' } := by
  set C' : Cfg K m P := { C with loc := update C.loc p l', pend := pend' } with hC'
  have hJ : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => update_of_ne hq _ _
  have hp : C'.loc p = l' := update_self _ _ _
  have hv : ∀ q, (C'.loc q).pc.isVal → q ≠ p ∧ (C.loc q).pc.isVal := by
    intro q h1; by_cases hqp : q = p
    · subst hqp; rw [hp, hq'.1] at h1; cases h1
    · rw [hJ q hqp] at h1; exact ⟨hqp, h1⟩
  have hval : ∀ y, C'.val y = C.val y := fun _ => rfl
  have hlks : ∀ y, C'.lks y = C.lks y := fun _ => rfl
  refine ⟨hid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.ts_lt, ?_, ?_, ?_, hI.l4, ?_⟩
  · intro q; by_cases hqp : q = p
    · subst hqp; rw [hp]; exact hq'.2.2.2.1
    · rw [hJ q hqp]; exact hI.loc q
  · intro q x w hr hx; by_cases hqp : q = p
    · subst hqp; rw [hp, hq'.2.2.1] at hr; cases hr
    · rw [hJ q hqp] at hr; exact hI.link q x w hr hx
  · intro q h1; obtain ⟨hqp, h2⟩ := hv q h1; rw [hJ q hqp]; exact hI.own q h2
  · intro q r h1 h2 h3; obtain ⟨hqp, h1'⟩ := hv q h1; obtain ⟨hrp, h2'⟩ := hv r h2
    rw [hJ q hqp, hJ r hrp] at h3; exact hI.own_inj q r h1' h2' h3
  · intro c v t hc ht; obtain ⟨q, h1, h2, h3⟩ := hI.own2 c v t hc ht
    have hqp : q ≠ p := by rintro rfl; rw [hq.1] at h1; cases h1
    exact ⟨q, by rw [hJ q hqp]; exact ⟨h1, h2, h3⟩⟩
  · exact hI.p3
  · intro q h1 c hc; by_cases hqp : q = p
    · subst hqp; rw [hp, hq'.1, hq'.2.1] at h1; simp at h1
    · rw [hJ q hqp] at h1 hc; exact hI.p3' q h1 c hc
  · intro I J hIJ h1 h2 hk ht hc
    obtain ⟨hIp, h1'⟩ := hv I h1; obtain ⟨hJp, h2'⟩ := hv J h2
    rw [hJ I hIp] at hk ht hc; rw [hJ J hJp] at hk ht hc
    exact hI.a1 I J hIJ h1' h2' hk ht hc
  · intro I J hd h2 hj hk ht
    obtain ⟨hJp, h2'⟩ := hv J h2
    have hIp : I ≠ p := by
      rintro rfl; rw [hp] at hd
      rcases hd with ⟨h5 | h5, -⟩ | h5
      · exact hq'.2.2.2.2.1 h5
      · exact hq'.2.2.2.2.2.1 h5
      · exact hq'.2.2.2.2.2.2 h5
    rw [hJ I hIp] at hd hj hk ht; rw [hJ J hJp] at hj hk
    exact hI.doc I J hd h2' hj hk ht
  · intro J c h1 ht hc; obtain ⟨hJp, h1'⟩ := hv J h1
    rw [hJ J hJp] at ht hc ⊢; exact hI.a4 J c h1' ht hc
  · intro q h1 hE; by_cases hqp : q = p
    · subst hqp; rw [hp] at h1; have := hq'.2.1; rw [h1] at this; cases this
    · rw [hJ q hqp] at h1 hE ⊢; exact hI.isc q h1 hE

lemma quiet_start (o : DOp K) : Quiet (start h o) := by
  simp [Quiet, start, PC.isVal, PC.isIns, recorded, LocInv]

lemma quiet_of_idle {l : Loc K m} (hl : l.pc = .idle) : Quiet l := by
  simp [Quiet, hl, PC.isVal, PC.isIns, recorded, LocInv]

lemma quiet_of_ret {l : Loc K m} (hl : l.pc = .ret) : Quiet l := by
  simp [Quiet, hl, PC.isVal, PC.isIns, recorded, LocInv]

/-- The invariant is preserved by every step. -/
lemma inv_step (hI : Inv h N ts C) {ℓ : Label P (dict K)} (hs : (impl h).step C ℓ = some C') :
    ∃ ts', Inv h (N + 1) ts' C' := by
  cases ℓ with
  | inv p o =>
    obtain ⟨hp, -, hpend, hloc, hmem⟩ := Impl.step_inv hs
    have hC : C' = { C with loc := update C.loc p (start h o), pend := update C.pend p (some o) } := by
      cases C'; simp only at hpend hloc hmem; subst hpend hloc hmem; rfl
    subst hC
    refine ⟨ts, (inv_swap_quiet hI (quiet_of_idle (hI.idle p hp)) (quiet_start (h := h) o) _ ?_).mono⟩
    intro q hq
    by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [update_of_ne hqp] at hq ⊢; exact hI.idle q hq
  | ret p r =>
    obtain ⟨hp, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hs
    have hC : C' = { C with loc := update C.loc p l, pend := update C.pend p none } := by
      cases C'; simp only at hpend hloc hmem; subst hpend hloc hmem; rfl
    subst hC
    simp only [impl] at hact
    have hq : Quiet (C.loc p) ∧ l.pc = .idle := by
      unfold act at hact
      rcases hpc : (C.loc p).pc <;> rw [hpc] at hact <;> simp at hact
      · injection hact with h1 h2; subst h2; exact ⟨quiet_of_idle hpc, hpc⟩
      · injection hact with h1 h2; subst h2; exact ⟨quiet_of_ret hpc, rfl⟩
    refine ⟨ts, (inv_swap_quiet hI hq.1 (quiet_of_idle hq.2) _ ?_).mono⟩
    intro q _
    by_cases hqp : q = p
    · subst hqp; simp [hq.2]
    · rw [update_of_ne hqp]; apply hI.idle q
      simp only [update_of_ne hqp] at *; assumption
  | tau p =>
    rcases hpc : (C.loc p).pc
    · -- idle: no internal step
      exfalso; simp [Impl.step, impl, act, hpc] at hs
    · exact ⟨ts, tau_fsLL hI hpc hs⟩
    · exact ⟨ts, tau_bsLL hI hpc hs⟩
    · exact ⟨ts, tau_vcSC hI hpc hs⟩
    · exact ⟨ts, tau_vcRD hI hpc hs⟩
    · exact ⟨ts, tau_tdSCF hI hpc hs⟩
    · exact ⟨ts, tau_tdSCD hI hpc hs⟩
    · exact ⟨ts, tau_tdLL hI hpc hs⟩
    · exact ⟨ts, tau_iLL hI hpc hs⟩
    · exact tau_iSC hI hpc hs
    · exact ⟨ts, tau_dsLL hI hpc hs⟩
    · exact ⟨ts, tau_docRD hI hpc hs⟩
    · exact ⟨ts, tau_docSC hI hpc hs⟩
    · exact ⟨ts, tau_docRD2 hI hpc hs⟩
    · exact ⟨ts, tau_l57LL hI hpc hs⟩
    · exact tau_reTent hI (Or.inl hpc) hs
    · exact ⟨ts, tau_l66LL hI hpc hs⟩
    · exact ⟨ts, tau_l67SC hI hpc hs⟩
    · exact tau_reTent hI (Or.inr (Or.inl hpc)) hs
    · exact ⟨ts, tau_dcLL76 hI hpc hs⟩
    · exact tau_reTent hI (Or.inr (Or.inr hpc)) hs
    · exact ⟨ts, tau_dcLL79 hI hpc hs⟩
    · exact ⟨ts, tau_dcSC80 hI hpc hs⟩
    · exfalso; simp [Impl.step, impl, act, hpc] at hs

lemma inv_init : Inv h 1 (fun _ => 0) ((impl h).initCfg : Cfg K m P) := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => Nat.one_pos, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Impl.initCfg, impl, LocInv, recorded, PC.isVal, PC.isIns, Cfg.val, Cfg.lks]

/-- The invariant holds in every reachable configuration. -/
theorem inv_of_run {α : List (Label P (dict K))} (hα : (impl h).run α = some C) :
    ∃ ts, Inv h (α.length + 1) ts C := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run_nil, Option.some.injEq] at hα; subst hα; exact ⟨_, inv_init⟩
  | append_singleton α ℓ ih =>
    rw [Impl.run_concat] at hα
    cases hrun : (impl h).run α with
    | none => simp [hrun] at hα
    | some C₀ =>
      rw [hrun] at hα
      obtain ⟨ts, hI⟩ := ih hrun
      simpa using inv_step hI hα

/-- **Lemma 4** of the paper: at any point of an execution, for any key `v`, at most one cell of
the table contains `⟨v, final⟩`. -/
theorem lemma4 {α : List (Label P (dict K))} (hα : (impl h).run α = some C) (v : K)
    (i j : Fin m) (hi : (C.mem i).1 = .key v .fin) (hj : (C.mem j).1 = .key v .fin) : i = j := by
  obtain ⟨ts, hI⟩ := inv_of_run hα
  exact hI.l4 v i j hi hj

/-- **Proposition 3** of the paper: if cell `i` contains the key `v` (a copy with any tag), then
no cell between `h(v)` and `i` is empty. -/
theorem prop3 {α : List (Label P (dict K))} (hα : (impl h).run α = some C) (v : K) (t : Tag)
    (i : Fin m) (hi : (C.mem i).1 = .key v t) (j : Fin m) (hj : dist h v j ≤ dist h v i) :
    (C.mem j).1 ≠ .empty := by
  obtain ⟨ts, hI⟩ := inv_of_run hα
  exact hI.p3 i v t hi j hj

end Podc.LockFreeLinearProbing
