import Papers.PODC2019.CryptoConsensusNumber.Fig3LStep3

/-!
# Lemma 2 of Guerraoui et al. (PODC 2019): Figure 3 is linearizable

`fig3_linearizable`: if every account has at most `k` owners, the algorithm of Figure 3
(from an atomic snapshot, registers and `k`-consensus objects) is a linearizable
implementation of the asset-transfer object.
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig3

open Cslib.SharedMemory

set_option allowUnsafeReducibility true in
attribute [local reducible] atSpec snapObj kConsObj

variable {n : ℕ} {Acct : Type} [DecidableEq Acct] {μ : Acct → Finset (Fin n)} {q₀ : Acct → ℕ}
  {k : ℕ}

/-- One step preserves the invariants. -/
lemma inv_step (hk : KShared μ k) {α : Hst μ q₀} {C C' : Cfg μ q₀ k} {K : Set (Tx n Acct)}
    {gid : Tx n Acct → ℕ} {L : LinL n Acct} (hrun : (impl μ q₀ k).run α = some C)
    (hM : MInv μ C K) (hL : LInv μ q₀ α C K gid L) (ℓ : Label (Fin n) (AT μ q₀))
    (h : (impl μ q₀ k).step C ℓ = some C') :
    ∃ K' gid' L', MInv μ C' K' ∧ LInv μ q₀ (α ++ [ℓ]) C' K' gid' L' := by
  cases ℓ with
  | inv q o =>
    obtain ⟨h0, ha, -⟩ := Impl.step_inv h
    rw [step_inv_eq o h0 ha] at h
    cases h
    cases o with
    | read a =>
      exact ⟨K, gid, L, hM.step_inv_read h0 a, hL.step_inv_read hM hrun h0 a⟩
    | transfer p' a b x =>
      have hp' : p' = q := ha
      subst hp'
      by_cases hq : p' ∈ μ a
      · have e : (impl μ q₀ k).invoke p' (C.loc p') (ATOp.transfer p' a b x) =
            { C.loc p' with pc := .write (newTx (C.loc p') p' a b x) } := by
          simp [impl, hq, newTx]
        rw [e]
        exact ⟨_, _, L, hM.step_inv_owner h0 a b x hq, hL.step_inv_owner hM hrun h0 a b x⟩
      · have e : (impl μ q₀ k).invoke p' (C.loc p') (ATOp.transfer p' a b x) =
            { C.loc p' with pc := .ret (.inl false) } := by
          simp [impl, hq]
        rw [e]
        exact ⟨K, gid, _, hM.step_inv_nonowner h0 _, hL.step_inv_nonowner hM hrun h0 a b x hq⟩
  | ret q r =>
    obtain ⟨h0, hpc, rfl⟩ := step_ret_eq h (fun hi => (hM.proc q).idle.2 hi)
    exact ⟨K, gid, L, hM.step_ret hpc, hL.step_ret hM hpc⟩
  | tau q =>
    have h0 := (Impl.step_tau h).1
    have hp := hM.proc q
    cases hpc : (C.loc q).pc with
    | idle => rw [step_tau_idle_none hpc] at h; cases h
    | ret r => rw [step_tau_ret_none r hpc] at h; cases h
    | rscan a =>
      rw [step_rscan a h0 hpc] at h; cases h
      exact ⟨K, gid, _, hM.step_rscan hpc _, hL.step_rscan hM hrun hpc⟩
    | write tx =>
      rw [step_write tx h0 hpc] at h; cases h
      refine ⟨K, gid, L, hM.step_write hpc, hL.tau_same hM q _ _ (U_update_Reg _ _)
        (fun a r => Dec_update_Reg _ _ a r) (by simp [hpc, PC.tx?]) (by simp [hpc])
        (by simp) (by simp) (by simp)⟩
    | coll tx i acc =>
      rw [step_coll tx i acc h0 hpc] at h; cases h
      refine ⟨K, gid, L, hM.step_coll hpc, hL.tau_same hM q _ _ rfl (fun _ _ => rfl) ?_
        (by simp [hpc]) ?_ ?_ ?_⟩
      · by_cases hi : i.val + 1 < n
        · simp [hi, hpc, PC.tx?]
        · have := hM.coll_last hpc hi
          simp [hi, hpc, PC.tx?, loopCheck, this]
      · intro r
        by_cases hi : i.val + 1 < n
        · simp [hi]
        · have := hM.coll_last hpc hi
          simp [hi, loopCheck, this]
      · intro a
        by_cases hi : i.val + 1 < n
        · simp [hi]
        · have := hM.coll_last hpc hi
          simp [hi, loopCheck, this]
      · intro tx' c' t res h1
        by_cases hi : i.val + 1 < n
        · simp [hi] at h1
        · have := hM.coll_last hpc hi
          simp [hi, loopCheck, this] at h1
    | snap tx c =>
      rw [step_snap tx c h0 hpc] at h; cases h
      refine ⟨K, gid, L, hM.step_snap hpc, hL.tau_same hM q _ _ rfl (fun _ _ => rfl)
        (by simp [hpc, PC.tx?]) (by simp [hpc]) (by simp) (by simp) ?_⟩
      intro tx' c' t res h1 _
      simp only [PC.prop.injEq, proposal] at h1
      obtain ⟨-, -, h1⟩ := h1
      simp only [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      rw [balance_eq_lst hL]
      refine ⟨fun h2 => by simpa using h2, fun h2 => ⟨L, [], by simp, by simpa using h2, by simp⟩⟩
    | prop tx c pr =>
      rw [step_prop' h0 hpc (hM.cnt_lt hk hpc)] at h; cases h
      obtain ⟨L', hL'⟩ := hL.step_prop hM hpc
      exact ⟨K, gid, L', hM.step_prop hpc, hL'⟩
    | upd tx c d =>
      rw [step_upd tx c d h0 hpc] at h; cases h
      have hM' := hM.step_upd hpc
      obtain ⟨L', hL'⟩ := hL.step_upd hM hM' hpc
      exact ⟨K, gid, L', hM', hL'⟩

/-- The invariants hold in every reachable configuration. -/
theorem inv_of_run (hk : KShared μ k) {α : Hst μ q₀} {C : Cfg μ q₀ k}
    (h : (impl μ q₀ k).run α = some C) :
    ∃ K gid L, MInv μ C K ∧ LInv μ q₀ α C K gid L := by
  refine Impl.run_induction (Q := fun α C => ∃ K gid L, MInv μ C K ∧ LInv μ q₀ α C K gid L)
    ⟨∅, fun _ => 0, [], MInv.init, LInv.init _⟩ ?_ h
  rintro α C₀ ℓ C hα ⟨K, gid, L, hM, hL⟩ h
  exact inv_step hk hα hM hL ℓ h

/-- **Lemma 2** (safety part) of Guerraoui et al., *The Consensus Number of a Cryptocurrency*
(PODC 2019): if every account has at most `k` owners, the algorithm of Figure 3 is a
linearizable implementation of the asset-transfer object from an atomic snapshot object,
registers and `k`-consensus objects. -/
theorem fig3_linearizable (hk : KShared μ k) : (impl μ q₀ k).Linearizable :=
  Impl.linearizable_of_run fun _ _ h =>
    let ⟨_, _, L, _, hL⟩ := inv_of_run hk h
    ⟨L, hL.lin⟩

end CryptoCons.Fig3
