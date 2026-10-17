import Papers.PODC2021.GoodCaseLatencyBB.UnsyncClaim1
import Papers.PODC2021.GoodCaseLatencyBB.UnsyncClaim2
import Podc.Foundations.Labelling

/-!
# Theorem 10: BRB with unsynchronized start and `f > n/3` needs `Δ + 1.5δ`

Abraham–Nayak–Ren–Xiang, PODC 2021, Theorem 10 (Section 5.4, Appendix C.4).

With `δ = 2e` (even, `≥ 2`) and `δ < Δ`: if a protocol solves Byzantine reliable broadcast in the
unsynchronized-start model (delays `≤ Δ`, clock skew `≤ δ/2`) with `n ≤ 3f − 1`, `n ≥ 4`, then in
some good-case execution (honest broadcaster, synchronized start, delays `≤ δ`) some honest
process has not committed before time `Δ + 1.5δ`.

Proof: Executions 1–4 of `UnsyncRuns.lean`; Claim 1 (`claim1`: `g` cannot distinguish
Executions 1 and 2 before `Δ + 1.5δ`, and its mirror for `h`, Executions 4 and 3) and Claim 2
(`claim2`: Executions 2 and 3 are the same physical execution for `A, C`). Unforgeability of the
executions (`X_authValid`) is not discussed in the paper; it requires that in Execution 1 the
Byzantine `C` and `h` do not send their messages to `B` in time (we delay them by `L = Δ + 3e`):
otherwise `B` would relay, in Executions 2 and 3, signatures of `C` (resp. `h`) on messages that
the honest `C` (resp. `h`) never signs there.
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB.Thm10

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [DecidableEq P] [Fintype P]
variable {A : Algorithm P M S V V} {s : P} {v0 : V} {Δ e L : ℕ}

theorem DW_pos (he : 1 ≤ e) (hΔ : 2 * e < Δ) (hL : L = Δ + 3 * e) (i j : ℕ) :
    1 ≤ DW Δ e L i j := by
  unfold DW; split_ifs <;> omega

/-- **Unforgeability of the physical execution.** -/
theorem X_authValid {Au : Auth P M K} (hU : (lateStart A).Unforging Au) {lab lab' : P → ℕ}
    (hl : Labels s lab lab') (he : 1 ≤ e) (hΔ : 2 * e < Δ) (hL : L = Δ + 3 * e) (va vb : V) :
    (X A s v0 Δ e L lab lab' va vb).AuthValid Au (lateStart A) := by
  have hWf : ∀ (v : V) (l : P → ℕ) q, q ∉ (W (M := M) s v0 Δ e L v l).faulty :=
    fun _ _ q => Finset.notMem_empty q
  have hRf : ∀ q, q ∈ (X A s v0 Δ e L lab lab' va vb).faulty ↔ lab q = 2 := by
    intro q; simp [X]
  intro b hb τ r _ m hm x hx
  have hb2 : lab b = 2 := (hRf b).mp hb
  change m ∈ (if τ < Δ + e then
      (if lab r ≤ 1 then (W s v0 Δ e L va lab).out (lateStart A) b τ r
       else if 3 ≤ lab r then (W s v0 Δ e L vb lab').out (lateStart A) b τ r else [])
    else []) at hm
  split_ifs at hm with hτ h1 h3
  · -- replay of `W va lab` towards `g, A`
    refine tokens_replay_rel (lateStart A) hU (Ri := W s v0 Δ e L va lab)
      (R' := X A s v0 Δ e L lab lab' va vb)
      (fun q σ => lab q = 2 ∧ σ < Δ + e) ?_ τ b ⟨hb2, hτ⟩ (hWf _ _ b) hb r m hm x hx
    intro q σ ⟨hq2, hσ⟩ _ q' σ' hσ' hdl
    change σ' ≤ σ' + DW Δ e L (lab q') (lab q) - 1 at hσ'
    change σ' + DW Δ e L (lab q') (lab q) - 1 < σ at hdl
    rw [hq2] at hσ' hdl
    have hq'4 := hl.le4 q'
    by_cases h2 : lab q' = 2
    · exact Or.inl ⟨(hRf q').mpr h2, hWf _ _ q', h2, by omega⟩
    by_cases h34 : lab q' = 3 ∨ lab q' = 4
    · exfalso
      have : DW Δ e L (lab q') 2 = L := by rcases h34 with h | h <;> simp [DW, h]
      omega
    right
    have hq'c : q' ∉ (X A s v0 Δ e L lab lab' va vb).faulty := fun h => h2 ((hRf q').mp h)
    have hDW : DW Δ e L (lab q') 2 = 2 * e := by
      have : lab q' = 0 ∨ lab q' = 1 := by omega
      rcases this with h | h <;> simp [DW, h]
    rw [hDW] at hσ' hdl
    intro m' hm' x' hx'
    rw [Run.out_of_correct _ _ (hWf _ _ q'),
      ← claim1 hl he hΔ hL va vb q' σ' (by omega)] at hm'
    right
    refine mem_honestTokens_of_out (A := lateStart A) (r' := q) (σ' := σ') hq'c ?_
      (by rw [Run.out_of_correct (lateStart A) _ hq'c]; exact hm') hx'
    change σ' ≤ σ' + DW Δ e L (lab q') (lab q) - 1
    rw [hq2, hDW]; omega
  · -- replay of `W vb lab'` towards `C, h`
    have hl' := hl.swap
    refine tokens_replay_rel (lateStart A) hU (Ri := W s v0 Δ e L vb lab')
      (R' := X A s v0 Δ e L lab lab' va vb)
      (fun q σ => lab q = 2 ∧ σ < Δ + e) ?_ τ b ⟨hb2, hτ⟩ (hWf _ _ b) hb r m hm x hx
    intro q σ ⟨hq2, hσ⟩ _ q' σ' hσ' hdl
    change σ' ≤ σ' + DW Δ e L (lab' q') (lab' q) - 1 at hσ'
    change σ' + DW Δ e L (lab' q') (lab' q) - 1 < σ at hdl
    rw [hl.mirror q, hq2, hl.mirror q'] at hσ' hdl
    have hq'4 := hl.le4 q'
    by_cases h2 : lab q' = 2
    · exact Or.inl ⟨(hRf q').mpr h2, hWf _ _ q', h2, by omega⟩
    by_cases h01 : lab q' = 0 ∨ lab q' = 1
    · exfalso
      have : DW Δ e L (4 - lab q') (4 - 2) = L := by rcases h01 with h | h <;> simp [DW, h]
      omega
    right
    have hq'c : q' ∉ (X A s v0 Δ e L lab lab' va vb).faulty := fun h => h2 ((hRf q').mp h)
    have hDW : DW Δ e L (4 - lab q') (4 - 2) = 2 * e := by
      have : lab q' = 3 ∨ lab q' = 4 := by omega
      rcases this with h | h <;> simp [DW, h]
    rw [hDW] at hσ' hdl
    intro m' hm' x' hx'
    right
    rw [Run.out_of_correct _ _ (hWf _ _ q'),
      ← claim1 hl' he hΔ hL vb va q' σ' (by rw [hl.mirror q']; omega)] at hm'
    have h2' : lab' q' ≠ 2 := by rw [hl.mirror q']; omega
    rw [claim2 hl' he hΔ hL vb va σ' q' h2' (by simp only [off, hl.mirror q']; split_ifs <;> omega)]
      at hm'
    refine mem_honestTokens_of_out (A := lateStart A) (r' := q)
      (σ' := σ' + off lab e q' - off lab' e q') hq'c ?_
      (by rw [Run.out_of_correct (lateStart A) _ hq'c]; exact hm') hx'
    change _ ≤ σ' + DW Δ e L (lab' q') (lab' q) - 1
    rw [hl.mirror q, hq2, hl.mirror q', hDW]
    simp only [off, hl.mirror q']
    split_ifs <;> omega
  · simp at hm
  · simp at hm

/-! ### Admissibility of the executions -/

theorem W_enlarge_good {f : ℕ} {lab : P → ℕ} (he : 1 ≤ e) (hΔ : 2 * e < Δ) (hL : L = Δ + 3 * e)
    (va : V) (hle : ∀ p, lab p ≤ 4)
    (hF : (univ.filter fun p => lab p = 3 ∨ lab p = 4).card ≤ f) :
    (W s v0 Δ e L va lab).enlarge (lateStart A) (univ.filter fun p => lab p = 3 ∨ lab p = 4) ∈
      unsyncGood (M := M) f (2 * e) := by
  refine ⟨⟨hF, fun q τ p _ _ => ?_, fun q τ p hq hp => ?_, fun _ _ _ _ _ => ?_, fun _ _ _ _ => ?_⟩,
    fun _ _ => rfl⟩
  · simp only [Run.enlarge_dl, W]; have := DW_pos he hΔ hL (lab q) (lab p); omega
  · simp only [Run.enlarge_faulty, mem_filter, mem_univ, true_and] at hq hp
    simp only [Run.enlarge_dl, W]
    have h1 := hle q; have h2 := hle p
    have : DW Δ e L (lab q) (lab p) = 2 * e := by unfold DW; split_ifs <;> omega
    omega
  · simp [ustart, W]
  · simp [ustart, W]

theorem X_enlarge_valid {f : ℕ} {lab lab' : P → ℕ} (hl : Labels s lab lab') (he : 1 ≤ e)
    (hΔ : 2 * e < Δ) (hL : L = Δ + 3 * e) (va vb : V)
    (hF : (univ.filter fun p => lab p = 2 ∨ lab p = 4).card ≤ f) :
    (X A s v0 Δ e L lab lab' va vb).enlarge (lateStart A)
      (univ.filter fun p => lab p = 2 ∨ lab p = 4) ∈ unsyncRuns (M := M) f Δ e := by
  refine ⟨hF, fun q τ p _ _ => ?_, fun q τ p hq hp => ?_, fun q τ p hq hp => ?_,
    fun p q hp hq => ?_⟩
  · simp only [Run.enlarge_dl, X]; have := DX_pos he hΔ hL (lab q) (lab p); omega
  · simp only [Run.enlarge_faulty, mem_filter, mem_univ, true_and] at hq hp
    simp only [Run.enlarge_dl, X]
    have h1 := hl.le4 q; have h2 := hl.le4 p
    have : DX Δ e L (lab q) (lab p) ≤ Δ := by unfold DX; split_ifs <;> omega
    have := DX_pos he hΔ hL (lab q) (lab p)
    omega
  · simp only [Run.enlarge_faulty, mem_filter, mem_univ, true_and] at hq hp
    simp only [Run.enlarge_dl, X, ustart, Run.enlarge_inp]
    have h1 := hl.le4 q; have h2 := hl.le4 p
    split_ifs with h3
    · have : e + 1 ≤ DX Δ e L (lab q) (lab p) := by
        rw [h3]; unfold DX; split_ifs <;> omega
      omega
    · omega
  · simp only [ustart, Run.enlarge_inp, X]; split_ifs <;> omega

/-! ### Labels -/

theorem exists_labels10 {f : ℕ} (h4 : 4 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * f - 1) :
    ∃ lab : P → ℕ, (∀ p, lab p ≤ 4) ∧ lab s = 2 ∧ (∃ g, lab g = 0) ∧ (∃ h, lab h = 4) ∧
      (∃ x, lab x = 1) ∧ (univ.filter fun p => lab p = 0).card ≤ 1 ∧
      (univ.filter fun p => lab p = 4).card ≤ 1 ∧ (univ.filter fun p => lab p = 1).card ≤ f - 1 ∧
      (univ.filter fun p => lab p = 2).card ≤ f - 1 ∧
      (univ.filter fun p => lab p = 3).card ≤ f - 1 := by
  obtain ⟨lab, hs, hle, hc⟩ := Fintype.exists_labelling_apply_eq 5
    (fun i => if i = 3 then 0 else 1) (fun i => if i = 0 ∨ i = 4 then 1 else f - 1)
    (fun i _ => by split_ifs <;> omega) (by simp [sum_range_succ]; omega)
    (by simp [sum_range_succ]; omega) s (i₀ := 2) (by omega) (by simp)
  have hne : ∀ i < 5, i ≠ 3 → ∃ x, lab x = i := fun i hi h3 => by
    obtain ⟨x, -, hx⟩ := filter_nonempty_iff.1 (card_pos.1 (by simpa [h3] using (hc i hi).1))
    exact ⟨x, hx⟩
  exact ⟨lab, fun p => by have := hle p; omega, hs, hne 0 (by omega) (by omega),
    hne 4 (by omega) (by omega), hne 1 (by omega) (by omega), by simpa using (hc 0 (by omega)).2,
    by simpa using (hc 4 (by omega)).2, by simpa using (hc 1 (by omega)).2,
    by simpa using (hc 2 (by omega)).2, by simpa using (hc 3 (by omega)).2⟩

theorem UValid.mono {f d d' σ σ' : ℕ} {R : Run P M (V × ℕ)} (h : UValid f d σ R) (hd : d ≤ d')
    (hσ : σ ≤ σ') : UValid f d' σ' R :=
  ⟨h.card_faulty, h.dl_ge, fun q τ p hq hp => (h.dl_lt q τ p hq hp).trans_le (by omega),
    h.dl_start, fun p q hp hq => (h.skew p q hp hq).trans (by omega)⟩

theorem card_filter_or_le (c₁ c₂ : P → Prop) [DecidablePred c₁] [DecidablePred c₂] :
    (univ.filter fun p => c₁ p ∨ c₂ p).card ≤
      (univ.filter c₁).card + (univ.filter c₂).card := by
  rw [filter_or]; exact card_union_le _ _

/-- **Theorem 10 of [ANRX21].** Let `δ = 2e ≥ 2` and `δ < Δ`. A Byzantine reliable broadcast
protocol for the unsynchronized-start model (delays `≤ Δ`, clock skew `≤ δ/2`), resilient to
`f > n/3` faults (`n ≤ 3f − 1`, `n ≥ 4`), has good-case latency at least `Δ + 1.5δ`: in some
execution with an honest broadcaster, all processes starting at time `0` and all delays `≤ δ`,
some honest process has not committed before time `Δ + 1.5δ = Δ + 3e`. -/
theorem theorem_10 {Au : Auth P M K} (hU : (lateStart A).Unforging Au) {f : ℕ}
    (he : 1 ≤ e) (hΔ : 2 * e < Δ) (h4 : 4 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * f - 1)
    {a b : V} (hab : a ≠ b) (hA : IsBRBU Au A s (unsyncRuns f Δ e)) :
    ¬ LatencyWithin Au (lateStart A) s (unsyncGood (M := M) f (2 * e)) (Δ + 3 * e - 1) := by
  intro hlat
  obtain ⟨lab, hle, hs, ⟨g, hg⟩, ⟨h, hh⟩, ⟨x, hx⟩, c0, c4, c1, c2, c3⟩ :=
    exists_labels10 (s := s) h4 hn
  let lab' : P → ℕ := fun p => 4 - lab p
  have hl : Labels s lab lab' := ⟨hle, fun _ => rfl, hs⟩
  have hl' := hl.swap
  have hf1 : 1 ≤ f := by omega
  set L := Δ + 3 * e with hL
  -- the four executions
  let F1 : Finset P := univ.filter fun p => lab p = 3 ∨ lab p = 4
  let F2 : Finset P := univ.filter fun p => lab p = 2 ∨ lab p = 4
  let F3 : Finset P := univ.filter fun p => lab' p = 2 ∨ lab' p = 4
  let F4 : Finset P := univ.filter fun p => lab' p = 3 ∨ lab' p = 4
  have hF1 : F1.card ≤ f := (card_filter_or_le _ _).trans (by omega)
  have hF2 : F2.card ≤ f := (card_filter_or_le _ _).trans (by omega)
  have hF3 : F3.card ≤ f := by
    have e3 : F3 = univ.filter fun p => lab p = 2 ∨ lab p = 0 := by
      ext p; simp only [F3, lab', mem_filter, mem_univ, true_and]; have := hle p; omega
    rw [e3]; exact (card_filter_or_le _ _).trans (by omega)
  have hF4 : F4.card ≤ f := by
    have e4 : F4 = univ.filter fun p => lab p = 1 ∨ lab p = 0 := by
      ext p; simp only [F4, lab', mem_filter, mem_univ, true_and]; have := hle p; omega
    rw [e4]; exact (card_filter_or_le _ _).trans (by omega)
  have hle' : ∀ p, lab' p ≤ 4 := fun p => by simp only [lab']; omega
  set E1 := (W (M := M) s a Δ e L a lab).enlarge (lateStart A) F1
  set E2 := (X A s a Δ e L lab lab' a b).enlarge (lateStart A) F2
  set E3 := (X A s a Δ e L lab' lab b a).enlarge (lateStart A) F3
  set E4 := (W (M := M) s a Δ e L b lab').enlarge (lateStart A) F4
  have hWa : ∀ (v : V) (l : P → ℕ), (W (M := M) s a Δ e L v l).AuthValid Au (lateStart A) :=
    fun _ _ b' hb' => absurd hb' (Finset.notMem_empty b')
  have hE1 : E1 ∈ unsyncGood f (2 * e) := W_enlarge_good he hΔ hL a hle hF1
  have hE4 : E4 ∈ unsyncGood f (2 * e) := W_enlarge_good he hΔ hL b hle' hF4
  have hE2 : E2 ∈ unsyncRuns f Δ e := X_enlarge_valid hl he hΔ hL a b hF2
  have hE3 : E3 ∈ unsyncRuns f Δ e := X_enlarge_valid hl' he hΔ hL b a hF3
  have hA1 : E1.AuthValid Au (lateStart A) :=
    Run.enlarge_authValid hU (hWa _ _) (Finset.empty_subset _)
  have hA4 : E4.AuthValid Au (lateStart A) :=
    Run.enlarge_authValid hU (hWa _ _) (Finset.empty_subset _)
  have hXf : ∀ (l l' : P → ℕ) (va vb : V),
      (X A s a Δ e L l l' va vb).faulty ⊆ univ.filter fun p => l p = 2 ∨ l p = 4 := by
    intro l l' va vb p hp; simp [X] at hp; simp [hp]
  have hA2 : E2.AuthValid Au (lateStart A) :=
    Run.enlarge_authValid hU (X_authValid hU hl he hΔ hL a b) (hXf _ _ _ _)
  have hA3 : E3.AuthValid Au (lateStart A) :=
    Run.enlarge_authValid hU (X_authValid hU hl' he hΔ hL b a) (hXf _ _ _ _)
  -- Execution 1: `g` commits `a` before `Δ + 1.5δ`
  have good : ∀ (v : V) (l : P → ℕ) (F : Finset P) (p : P),
      (W (M := M) s a Δ e L v l).enlarge (lateStart A) F ∈ unsyncGood f (2 * e) →
      ((W (M := M) s a Δ e L v l).enlarge (lateStart A) F).AuthValid Au (lateStart A) →
      s ∉ F → p ∉ F → ∃ τ ≤ Δ + 3 * e - 1,
        (lateStart A).decide p ((W (M := M) s a Δ e L v l).st (lateStart A) τ p) = some v := by
    intro v l F p hR hRA hsF hpF
    set R := (W (M := M) s a Δ e L v l).enlarge (lateStart A) F
    have hRv : R ∈ unsyncRuns f Δ e := UValid.mono hR.1 (by omega) (Nat.zero_le _)
    have hval := hA.validity R hRv hRA hsF p hpF
    have hinp : (R.inp s).1 = v := by simp [R, W]
    rw [hinp] at hval
    obtain ⟨τ, hτ, hd⟩ := (hlat R hR hRA hsF p hpF).eq_of_agreement
      (fun w h1 h2 => hA.agreement R hRv hRA p hpF p hpF w v h1 h2) hval
    refine ⟨τ, hτ, ?_⟩
    rw [← Run.enlarge_st (Finset.empty_subset F) τ p hpF]; exact hd
  have hsF1 : s ∉ F1 := by simp [F1, hs]
  have hsF4 : s ∉ F4 := by simp [F4, lab', hs]
  obtain ⟨τg, hτg, hdg⟩ := good a lab F1 g hE1 hA1 hsF1 (by simp [F1, hg])
  obtain ⟨τh, hτh, hdh⟩ := good b lab' F4 h hE4 hA4 hsF4 (by simp [F4, lab', hh])
  -- transfer to Executions 2 and 3
  have hgF2 : g ∉ F2 := by simp [F2, hg]
  have hxF2 : x ∉ F2 := by simp [F2, hx]
  have hxF3 : x ∉ F3 := by simp [F3, lab', hx]
  have hhF3 : h ∉ F3 := by simp [F3, lab', hh]
  have d2g : E2.Decides (lateStart A) g a := by
    refine ⟨τg, ?_⟩
    rw [Run.enlarge_st (hXf _ _ _ _) τg g hgF2,
      claim1 hl he hΔ hL a b g τg (Or.inl ⟨hg, hτg⟩)]
    exact hdg
  obtain ⟨w, hw⟩ := hA.termination E2 hE2 hA2 ⟨g, hgF2, a, d2g⟩ x hxF2
  have hwa := hA.agreement E2 hE2 hA2 g hgF2 x hxF2 a w d2g hw
  subst hwa
  obtain ⟨τx, hτx⟩ := hw
  have d3x : E3.Decides (lateStart A) x a := by
    refine ⟨τx + off lab' e x - off lab e x, ?_⟩
    rw [Run.enlarge_st (hXf _ _ _ _) _ x hxF3,
      ← claim2 hl he hΔ hL a b τx x (by omega) (by simp [off, hx]),
      ← Run.enlarge_st (hXf _ _ _ _) τx x hxF2]
    exact hτx
  have d3h : E3.Decides (lateStart A) h b := by
    refine ⟨τh, ?_⟩
    rw [Run.enlarge_st (hXf _ _ _ _) τh h hhF3,
      claim1 hl' he hΔ hL b a h τh (Or.inl ⟨by simp [lab', hh], hτh⟩)]
    exact hdh
  exact hab (hA.agreement E3 hE3 hA3 x hxF3 h hhF3 a b d3x d3h)

end GoodCaseLatencyBB.Thm10
