import Papers.PODC2020.BezoutElection.Alg2Prog4

/-!
# Algorithm 2: the progress property and termination (Lemma 1)

Proof of `alg2_progress` by contradiction. Assume no competition is solved after `t0` (`PCtx`).
Once candidate flags, `to_win` and `finishing` are stable (`Stab`), every open register satisfies
the hypotheses `LCtx` of the liveness of a competition, so no eligible process can stay a
non-loser at an open register forever (`LCtx.contra`). But:

* if some process is a candidate at some register, that register is open, and the process stays
  an eligible non-loser there;
* otherwise, if some process still has `to_win > 0`, it is eligible at every open register, where
  nobody is a loser (no candidate, no pending win: the register is pristine);
* otherwise the counting of the global invariant (with `U m ≤ W n + n`) gives a process that has
  not set `finishing` while at least `W n` competitions are solved: it sets `finishing` at its
  next collect, contradicting stability.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P] [Fintype P]
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id} {R : Type} [Inhabited R]
  {out : Id → Finset Id → R}

namespace PCtx

variable {e : ((alg2 Id m pp out).impl ids π).InfExec} (Q : PCtx e)
include Q

/-- From the stable time on, an open register satisfies the hypotheses `LCtx`. -/
noncomputable def lctx (S : Stab Q) (x : Fin m) (hx : ((e.cfg Q.t0).mem () x).level < pp.U) :
    LCtx (Q.run x) where
  toLCtx0 := Q.lctx0 x hx
  T := S.Ts - Q.T
  okc q := okOf ((e.cfg S.Ts).loc q) ((π q).symm x)
  fc q := ((e.cfg S.Ts).loc q).finishing
  stab i hi ok fin h := by
    have hτ : S.Ts ≤ Q.T + i := by have := S.hT; omega
    obtain ⟨s_mid, hok, hfin, hc, htf⟩ := (Q.trT_spec x (Q.T + i)).2.2 ok fin h
    show ok = okOf ((e.cfg S.Ts).loc (e.lbl (Q.T + i)).proc) ((π (e.lbl (Q.T + i)).proc).symm x) ∧
      fin = ((e.cfg S.Ts).loc (e.lbl (Q.T + i)).proc).finishing
    generalize (e.lbl (Q.T + i)).proc = q at hok hfin hc htf ⊢
    have hcand : s_mid.cand = ((e.cfg S.Ts).loc q).cand := by
      funext y
      rcases hc y with h' | h'
      · rw [h', S.cand _ hτ q]
      · rw [h', S.cand _ (by omega) q]
    have htf' : s_mid.toWin = ((e.cfg S.Ts).loc q).toWin ∧
        s_mid.finishing = ((e.cfg S.Ts).loc q).finishing := by
      rcases htf with ⟨h1, h2⟩ | ⟨h1, -, h3⟩
      · exact ⟨h1.trans (S.tw _ hτ q), h2.trans (S.fin _ hτ q)⟩
      · exfalso
        rw [S.fin _ hτ q] at h1
        rw [S.fin _ (by omega) q, h1] at h3
        cases h3
    exact ⟨hok.trans (okOf_congr _ hcand htf'.1), hfin.trans htf'.2⟩
  caok i hi q hca := by
    have hτ : S.Ts ≤ Q.T + i := by have := S.hT; omega
    rw [run_ca] at hca
    obtain ⟨g, G⟩ := (Q.rinv (Q.T + i)).g
    obtain ⟨h1, h2⟩ := G.g7 q _ hca
    show okOf ((e.cfg S.Ts).loc q) ((π q).symm x) = true
    rw [← okOf_congr _ (S.cand _ hτ q) (S.tw _ hτ q)]
    simp only [okOf, decide_eq_true_eq]
    exact ⟨h2, h1⟩

/-- **No execution satisfies `PCtx`.** -/
theorem false_of_stab (S : Stab Q) : False := by
  have hT0 := Q.t0_le_T
  have hST := S.hT
  by_cases hA : ∃ q k, ((e.cfg S.Ts).loc q).cand k = true
  · -- a candidate stays an eligible non-loser at its register
    obtain ⟨q, k, hqk⟩ := hA
    have hca : ∀ i ≥ S.Ts - Q.T, (((Q.run (π q k)).A i).loc q).ca = true := by
      intro i hi
      rw [run_ca, Equiv.symm_apply_apply, S.cand _ (by omega) q]; exact hqk
    have hx : ((e.cfg Q.t0).mem () (π q k)).level < pp.U := by
      have := ((Q.run (π q k)).inv (S.Ts - Q.T)).1.caU q (hca _ le_rfl)
      rwa [run_reg, Q.lev_eq (by omega)] at this
    let X := Q.lctx S (π q k) hx
    exact X.contra (c := q) (X.caok _ le_rfl q (hca _ le_rfl)) (T' := S.Ts - Q.T)
      (fun i hi => (((Q.run (π q k)).inv i).1.caAct q (hca i hi)).2)
  have hA' : ∀ q k, ((e.cfg S.Ts).loc q).cand k = false := by
    intro q k; by_contra h; exact hA ⟨q, k, by simpa using h⟩
  -- an open register
  obtain ⟨x, hx⟩ : ∃ x, ((e.cfg Q.t0).mem () x).level < pp.U := by
    by_contra h
    push Not at h
    exact Q.not_all_U Q.t0 fun x => le_antisymm
      (by obtain ⟨g, G⟩ := (Q.rinv Q.t0).g; exact (G.abs x).1.lvU) (h x)
  by_cases hB : ∃ c, 0 < ((e.cfg S.Ts).loc c).toWin
  · -- an eligible process at a pristine register
    obtain ⟨c, hc⟩ := hB
    let X := Q.lctx S x hx
    have hok : X.okc c = true := by
      show okOf ((e.cfg S.Ts).loc c) ((π c).symm x) = true
      simp only [okOf, decide_eq_true_eq]
      exact ⟨fun y _ => hA' c y, hc⟩
    obtain ⟨T₁, hT₁⟩ := X.active
    refine X.contra hok (T' := max T₁ (S.Ts - Q.T)) (fun i hi => ?_)
    have hB := ((Q.run x).inv i).1
    rcases hB.wit with hP | ⟨c', hc', -⟩ | ⟨c', w, hw, hl⟩
    · exact hP.1 c (by rw [hT₁ i (by omega), X.lev i])
    · rw [run_ca, S.cand _ (by omega) c', hA'] at hc'; cases hc'
    · have := X.nowin i c' w hw; have := X.lev i; omega
  · -- counting
    push Not at hB
    obtain ⟨g, G⟩ := (Q.rinv S.Ts).g
    have hn11 : n11Count π ((e.cfg S.Ts).mem ()) (vpcOf (e.cfg S.Ts).loc) = 0 := by
      classical
      unfold n11Count
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro q - ⟨y, w, ⟨k, hk, rfl⟩, hl⟩
      have hpc : ((e.cfg S.Ts).loc q).pc = .write k.val w := by simpa [vpcOf] using hk
      have := Q.nowin_conc hST hpc k.isLt
      simp only [Fin.eta] at this
      omega
    have hS : ∑ y, ((e.cfg S.Ts).mem () y).level = solved (e.cfg Q.t0) :=
      le_antisymm (Q.hno _ (by omega)) (Q.solved_mono (by omega))
    have h5 := G.g5
    rw [hn11, add_zero, Finset.sum_add_distrib, hS] at h5
    have hwf : ∑ q, g.wf q = pp.W * pp.n := by
      by_cases hex : ∃ q, ((e.cfg S.Ts).loc q).finishing = true
      · exact G.g4 hex
      · push Not at hex
        calc ∑ q, g.wf q = ∑ _q : P, pp.W := sum_congr rfl fun q _ => by
              have := G.g1 q (by simpa using hex q); have := hB q; omega
          _ = pp.W * pp.n := by simp [Q.hn, mul_comm]
    obtain ⟨q, hq⟩ : ∃ q, ((e.cfg S.Ts).loc q).finishing = false := by
      by_contra hne
      push Not at hne
      have hwt : ∑ q, g.wt q = pp.n := by
        calc ∑ q, g.wt q = ∑ _q : P, 1 := sum_congr rfl fun q _ => by
              have := G.g2 q (by simpa using hne q); have := hB q; omega
          _ = pp.n := by simp [Q.hn]
      have := Q.hlt; have := Q.h2
      omega
    obtain ⟨τ', hτ', hfin⟩ := Q.fin_set q S.Ts (by omega)
    rw [S.fin _ hτ' q, hq] at hfin
    cases hfin

theorem false : False := by
  obtain ⟨S⟩ := Q.stab_ex
  exact Q.false_of_stab S

end PCtx

/-- **The progress property of the competitions.** In a fair execution in which all processes
participate, with `W n ≤ U m ≤ W n + n`, as long as not all `U m` competitions are solved, some
competition is eventually solved. -/
theorem alg2_progress (hm : 0 < m) (hid : Function.Injective ids) (hn : Fintype.card P = pp.n)
    (h1 : pp.W * pp.n ≤ pp.U * m) (h2 : pp.U * m ≤ pp.W * pp.n + pp.n)
    (e : ((alg2 Id m pp out).impl ids π).InfExec) (hall : AllInvoke e)
    (hfair : e.IsFair) (t : ℕ) (ht : solved (e.cfg t) < pp.U * m) :
    ∃ t', t ≤ t' ∧ solved (e.cfg t) < solved (e.cfg t') := by
  by_contra hne
  push Not at hne
  exact (PCtx.false ⟨hm, hid, hn, h1, h2, hall, hfair, t, ht, hne⟩)

/-- **Lemma 1 (termination).** -/
theorem alg2_terminates' (hid : Function.Injective ids) (hn : Fintype.card P = pp.n)
    (h1 : pp.W * pp.n ≤ pp.U * m) (h2 : pp.U * m ≤ pp.W * pp.n + pp.n) :
    Terminates ((alg2 Id m pp out).impl ids π) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact terminates_of_m_zero hm
  · exact alg2_terminates_of_progress hm hid hn
      (fun e _ hall hfair t ht => alg2_progress hm hid hn h1 h2 e hall hfair t ht)

end BezoutElection.Alg2
