import Papers.PODC2019.CryptoConsensusNumber.Fig3Pot
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Task
import Cslib.Foundations.Data.Nat.Descent

/-!
# Lemma 2 of Guerraoui et al. (PODC 2019): Figure 3 is wait-free

`fig3_waitFree`: if every account has at most `k` owners, every operation of Figure 3 returns
after finitely many steps of its process.

Proof (the paper's argument — "eventually `o` becomes the request with the lowest round
number" — is informal; we use a potential). Suppose `p` takes infinitely many steps without
returning. Reads and non-owner transfers return after at most one step, and the announcement
and the collect take `n + 1` steps, so `p` eventually loops forever for its transfer `tx` on
account `a`, and its `round_a` grows without bound. Then `tx` is never decided (otherwise `p`
would commit it). The potential `Φ_M` of `Fig3Pot.lean` never increases, but once `p` has
gone through `M` rounds, all rounds `< M` are decided, i.e. `Φ_M ≥ M`, for every `M`:
contradiction.
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig3

open Cslib.SharedMemory

set_option allowUnsafeReducibility true in
attribute [local reducible] atSpec snapObj kConsObj

variable {n : ℕ} {Acct : Type} [DecidableEq Acct] {μ : Acct → Finset (Fin n)} {q₀ : Acct → ℕ}
  {k : ℕ}

/-- Decisions are permanent. -/
lemma step_decExt (hk : KShared μ k) {C C' : Cfg μ q₀ k} {K : Set (Tx n Acct)} (hM : MInv μ C K)
    {ℓ : Label (Fin n) (AT μ q₀)} (h : (impl μ q₀ k).step C ℓ = some C') :
    DecExt C.mem C'.mem := by
  cases ℓ with
  | inv q o =>
    obtain ⟨h0, ha, -⟩ := Impl.step_inv h
    rw [step_inv_eq o h0 ha] at h; cases h; exact DecExt.refl _
  | ret q r =>
    obtain ⟨-, -, rfl⟩ := step_ret_eq h (fun hi => (hM.proc q).idle.2 hi)
    exact DecExt.refl _
  | tau q =>
    have h0 := (Impl.step_tau h).1
    cases hpc : (C.loc q).pc with
    | idle => rw [step_tau_idle_none hpc] at h; cases h
    | ret r => rw [step_tau_ret_none r hpc] at h; cases h
    | rscan a => rw [step_rscan a h0 hpc] at h; cases h; exact DecExt.refl _
    | write tx' =>
      rw [step_write tx' h0 hpc] at h; cases h
      intro a r d hd; rw [Dec_update_Reg]; exact hd
    | coll tx' i acc => rw [step_coll tx' i acc h0 hpc] at h; cases h; exact DecExt.refl _
    | snap tx' c => rw [step_snap tx' c h0 hpc] at h; cases h; exact DecExt.refl _
    | prop tx' c pr =>
      rw [step_prop' h0 hpc (hM.cnt_lt hk hpc)] at h; cases h
      intro a r d hd
      simp only [Dec, KC_update_KC]
      split_ifs with he
      · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        simp only [Dec] at hd; simp [hd]
      · exact hd
    | upd tx' c d =>
      rw [step_upd tx' c d h0 hpc] at h; cases h
      intro a r d' hd; rw [Dec_update_AS]; exact hd

/-- Decided rounds are below the sum of the round counters. -/
lemma MInv.dec_lt_sum {C : Cfg μ q₀ k} {K : Set (Tx n Acct)} (hM : MInv μ C K) {a : Acct}
    {r : ℕ} (hr : Dec C.mem a r ≠ none) : r < ∑ q, ((C.loc q).rnd a + 1) := by
  have h1 : (KC C.mem a r).2 ≠ 0 := fun h => hr ((hM.kcNone a r).2 h)
  rw [hM.cnt, invCnt, Finset.card_ne_zero] at h1
  obtain ⟨q, hq⟩ := h1
  have hq' : Invd (C.loc q) a r := by simpa using hq
  have : r < (C.loc q).rnd a + 1 := by unfold Invd at hq'; omega
  calc r < (C.loc q).rnd a + 1 := this
    _ ≤ ∑ q, ((C.loc q).rnd a + 1) :=
      Finset.single_le_sum (f := fun q => (C.loc q).rnd a + 1) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ q)

/-- The phase of a process in the loop. -/
def PC.phase : PC n Acct → ℕ
  | .prop _ _ _ => 1
  | .upd _ _ _ => 2
  | _ => 0

/-- Steps before the loop. -/
def PC.preSteps (n : ℕ) : PC n Acct → ℕ
  | .rscan _ => 1
  | .write _ => n + 1
  | .coll _ i _ => n - i.val
  | _ => 0

/-- **Lemma 2** (liveness part) of Guerraoui et al., *The Consensus Number of a
Cryptocurrency* (PODC 2019): if every account has at most `k` owners, the algorithm of
Figure 3 is wait-free. -/
theorem fig3_waitFree (hk : KShared μ k) : (impl μ q₀ k).WaitFree := by
  intro e p n₀ hpend
  by_contra hcon
  push Not at hcon
  -- invariants along the execution
  have hMI : ∀ m, ∃ K, MInv μ (e.cfg m) K := fun m => by
    obtain ⟨K, -, -, hM, -⟩ := inv_of_run hk (e.run_pre m); exact ⟨K, hM⟩
  have hother : ∀ m, (e.lbl m).proc ≠ p → (e.cfg (m + 1)).loc p = (e.cfg m).loc p :=
    fun m h => (Impl.step_other (e.step_eq m) h).1
  have htau : ∀ m ≥ n₀, (e.lbl m).proc = p → e.lbl m = .tau p := by
    intro m hm h
    have hs := e.step_eq m
    cases hl : e.lbl m with
    | inv q o =>
      rw [hl] at hs h; simp only [Label.proc] at h; subst h
      exact absurd (Impl.step_inv hs).1 (hpend m hm)
    | ret q r =>
      rw [hl] at hs h; simp only [Label.proc] at h; subst h
      exact absurd (by simp [(Impl.step_ret hs).2.1]) (hpend (m + 1) (by omega))
    | tau q => rw [hl] at h; simp only [Label.proc] at h; rw [h]
  -- a process about to return takes no more internal steps
  have hnoret : ∀ m ≥ n₀, ∀ r, ((e.cfg m).loc p).pc ≠ .ret r := by
    intro m hm r hr
    have key : ∀ j, ((e.cfg (m + j)).loc p).pc = .ret r ∧ e.lbl (m + j) ≠ .tau p := by
      intro j
      induction j with
      | zero =>
        refine ⟨hr, fun hl => ?_⟩
        simp only [Nat.add_zero] at hl
        have hs := e.step_eq m; rw [hl, step_tau_ret_none r hr] at hs; cases hs
      | succ j ih =>
        have hpc : ((e.cfg (m + (j + 1))).loc p).pc = .ret r := by
          by_cases hpr : (e.lbl (m + j)).proc = p
          · exact absurd (htau _ (by omega) hpr) ih.2
          · rw [show m + (j + 1) = m + j + 1 by omega, hother _ hpr]; exact ih.1
        refine ⟨hpc, fun hl => ?_⟩
        have hs := e.step_eq (m + (j + 1)); rw [hl, step_tau_ret_none r hpc] at hs; cases hs
    obtain ⟨m', hm', hl⟩ := hcon m
    have := (key (m' - m)).2
    rw [show m + (m' - m) = m' by omega] at this
    exact this hl
  -- `p` reaches the loop
  obtain ⟨T, hT, hTloop⟩ := e.exists_good p (fun m => (((e.cfg m).loc p).pc.loopC).isSome)
    (fun m => PC.preSteps n ((e.cfg m).loc p).pc) n₀
    (fun t' ht' _ => by
      obtain ⟨m, hm, hl⟩ := hcon t'
      exact ⟨m, hm, by rw [hl]; rfl, by rw [hl]; trivial⟩)
    (fun t' ht' hng hpr _ => by
      have hl := htau t' ht' hpr
      have hs := e.step_eq t'
      rw [hl] at hs
      have h0 := hpend t' ht'
      obtain ⟨K, hM⟩ := hMI t'
      cases hpc : ((e.cfg t').loc p).pc with
      | idle => exact absurd ((hM.proc p).idle.2 hpc) h0
      | ret r => exact absurd hpc (hnoret t' ht' r)
      | rscan a =>
        rw [step_rscan a h0 hpc] at hs; rw [← Option.some.inj hs]
        right; simp [PC.preSteps, hpc]
      | write tx' =>
        rw [step_write tx' h0 hpc] at hs; rw [← Option.some.inj hs]
        right; simp [PC.preSteps, hpc]
      | coll tx' i acc =>
        rw [step_coll tx' i acc h0 hpc] at hs; rw [← Option.some.inj hs]
        by_cases hi : i.val + 1 < n
        · right; simp [PC.preSteps, hpc, hi]; omega
        · left
          have := hM.coll_last hpc hi
          simp [hi, loopCheck, this, PC.loopC]
      | snap => simp [hpc, PC.loopC] at hng
      | prop => simp [hpc, PC.loopC] at hng
      | upd => simp [hpc, PC.loopC] at hng)
    (fun t' _ _ hnp => by
      right
      have : (e.lbl t').proc ≠ p := by
        intro h; apply hnp; refine ⟨h, ?_⟩
        rw [htau t' (by omega) h]; trivial
      rw [hother t' this])
  obtain ⟨⟨tx, c₀⟩, hc₀⟩ := Option.isSome_iff_exists.1 hTloop
  set a := tx.a with ha
  -- `p` stays in the loop for `tx`
  have hloop : ∀ m ≥ T, ∃ c, ((e.cfg m).loc p).pc.loopC = some (tx, c) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact ⟨c₀, hc₀⟩
    | succ m hm ih =>
      obtain ⟨c, hc⟩ := ih
      by_cases hpr : (e.lbl m).proc = p
      · have hl := htau m (by omega) hpr
        have hs := e.step_eq m
        rw [hl] at hs
        have h0 := hpend m (by omega)
        cases hpc : ((e.cfg m).loc p).pc with
        | snap tx' c' =>
          rw [step_snap tx' c' h0 hpc] at hs; rw [← Option.some.inj hs]
          rw [hpc] at hc; simp [PC.loopC] at hc
          exact ⟨c, by simp [PC.loopC, hc]⟩
        | prop tx' c' pr =>
          rw [step_prop' h0 hpc (by obtain ⟨K, hM⟩ := hMI m; exact hM.cnt_lt hk hpc)] at hs
          rw [← Option.some.inj hs]
          rw [hpc] at hc; simp [PC.loopC] at hc
          exact ⟨c, by simp [PC.loopC, hc]⟩
        | upd tx' c' d =>
          rw [step_upd tx' c' d h0 hpc] at hs
          have hcfg := Option.some.inj hs
          rw [hpc] at hc; simp only [PC.loopC, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨htx', hc'⟩ := hc
          subst tx' c'
          have hnr := hnoret (m + 1) (by omega)
          rw [← hcfg] at hnr ⊢
          simp only [Function.update_self] at hnr ⊢
          unfold loopCheck at hnr ⊢
          split_ifs at hnr ⊢ with hin
          · exact ⟨_, rfl⟩
          · exact absurd rfl (hnr _)
        | _ => rw [hpc] at hc; simp [PC.loopC] at hc
      · rw [hother m hpr]; exact ⟨c, hc⟩
  -- `round_a` of `p` grows without bound
  have hrnd : ∀ R t₀, T ≤ t₀ → ∃ m ≥ t₀, R ≤ ((e.cfg m).loc p).rnd a := by
    intro R t₀ ht₀
    obtain ⟨m, hm, hgood⟩ := e.exists_good p (fun m => R ≤ ((e.cfg m).loc p).rnd a)
      (fun m => 3 * (R - ((e.cfg m).loc p).rnd a) + (2 - PC.phase ((e.cfg m).loc p).pc)) t₀
      (fun t' ht' _ => by
        obtain ⟨m, hm, hl⟩ := hcon t'
        exact ⟨m, hm, by rw [hl]; rfl, by rw [hl]; trivial⟩)
      (fun t' ht' hng hpr _ => by
        have hl := htau t' (by omega) hpr
        have hs := e.step_eq t'
        rw [hl] at hs
        have h0 := hpend t' (by omega)
        obtain ⟨c, hc⟩ := hloop t' (by omega)
        cases hpc : ((e.cfg t').loc p).pc with
        | snap tx' c' =>
          rw [step_snap tx' c' h0 hpc] at hs; rw [← Option.some.inj hs]
          right; simp [PC.phase, hpc]
        | prop tx' c' pr =>
          rw [step_prop' h0 hpc (by obtain ⟨K, hM⟩ := hMI t'; exact hM.cnt_lt hk hpc)] at hs
          rw [← Option.some.inj hs]
          right; simp [PC.phase, hpc]
        | upd tx' c' d =>
          rw [step_upd tx' c' d h0 hpc] at hs
          have hcfg := Option.some.inj hs
          rw [hpc] at hc; simp only [PC.loopC, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨htx', hc'⟩ := hc
          subst tx' c'
          right
          have hnr := hnoret (t' + 1) (by omega)
          rw [← hcfg] at hnr ⊢
          simp only [Function.update_self] at hnr ⊢
          simp only [updLoc, Function.update_self, ← ha]
          simp only [hpc, PC.phase]
          have hlc : ∀ X h, PC.phase (loopCheck tx X h) = 0 := by
            intro X h; unfold loopCheck; split_ifs <;> rfl
          try simp only [hlc]
          try simp only at hng
          omega
        | _ => rw [hpc] at hc; simp [PC.loopC] at hc)
      (fun t' _ _ hnp => by
        right
        have : (e.lbl t').proc ≠ p := by
          intro h; apply hnp; refine ⟨h, ?_⟩
          rw [htau t' (by omega) h]; trivial
        rw [hother t' this])
    exact ⟨m, hm, hgood⟩
  -- `tx` is never decided
  have hund : ∀ m ≥ T, ∀ r b, Dec (e.cfg m).mem a r ≠ some (tx, b) := by
    intro m hm r b hd
    obtain ⟨m₁, hm₁, hR⟩ := hrnd (r + 1) m hm
    have hperm : ∀ j, Dec (e.cfg (m + j)).mem a r = some (tx, b) := by
      intro j
      induction j with
      | zero => exact hd
      | succ j ih =>
        obtain ⟨K, hM⟩ := hMI (m + j)
        exact step_decExt hk hM (e.step_eq (m + j)) a r _ ih
    have hd₁ := hperm (m₁ - m)
    rw [show m + (m₁ - m) = m₁ by omega] at hd₁
    obtain ⟨K, hM⟩ := hMI m₁
    obtain ⟨c, hc⟩ := hloop m₁ (by omega)
    obtain ⟨hin, hcK⟩ := (hM.proc p).loop tx c hc
    exact (hcK tx hin).2.2 (((hM.proc p).com tx.a tx).2
      ⟨r, show r < ((e.cfg m₁).loc p).rnd a by omega, b, hd₁⟩)
  -- the potential argument
  obtain ⟨K₀, hM₀⟩ := hMI T
  set Θ := ∑ q, beta p tx ((e.cfg T).loc q) + (n * (tx.r + 1) - Psi tx (e.cfg T).mem) with hΘ
  set S := ∑ q, (((e.cfg T).loc q).rnd a + 1) with hS
  set M := Θ + S + 1 with hM
  have hphi : ∀ m ≥ T, Phi p tx M (e.cfg m) ≤ Phi p tx M (e.cfg T) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | succ m hm ih =>
      obtain ⟨K, hMm⟩ := hMI m
      obtain ⟨c, hc⟩ := hloop m hm
      exact (phi_step hk hMm hc (hund m hm) M (e.lbl m) (e.step_eq m)).trans ih
  have hDT : Delta tx M (e.cfg T).mem ≤ S := by
    unfold Delta
    calc _ ≤ (Finset.range S).card := by
          apply Finset.card_le_card
          intro r hr
          simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
          exact hM₀.dec_lt_sum hr.2
      _ = S := Finset.card_range S
  obtain ⟨m, hm, hRm⟩ := hrnd M T le_rfl
  obtain ⟨Km, hMm⟩ := hMI m
  have hDm : Delta tx M (e.cfg m).mem = M := by
    unfold Delta
    rw [Finset.filter_true_of_mem, Finset.card_range]
    intro r hr
    rw [Finset.mem_range] at hr
    obtain ⟨d, hd, -⟩ := (hMm.proc p).asAll a r (by omega)
    rw [hd]; simp
  have h1 := hphi m hm
  unfold Phi at h1
  rw [hDm] at h1
  omega

end CryptoCons.Fig3
