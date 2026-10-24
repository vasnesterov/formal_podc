import Papers.PODC2021.TrustedHardwareUnidirectional.SRB

-- CSLib candidate: generic model (SRB systems / round-layer spec), see README.
/-!
# Fair executions of SRB systems exist

Non-vacuity of the liveness requirement: for every protocol, Byzantine set and clients there is
a fair execution (round-robin delivery, silent Byzantine processes).
-/

namespace Podc.TrustedHW

namespace SRBProtocol

noncomputable section

variable {P V M S : Type} [Fintype P] [DecidableEq P] [Nonempty P] (A : SRBProtocol P V M S)
  (F : Finset P) (cl : P → Client P V)

/-- The initial configuration (Byzantine processes start with the same local state). -/
def initConfig : SRBConfig P M S where
  log p := if p ∈ F then [] else (A.init p (cl p)).2
  dl _ _ := 0
  st p := (A.init p (cl p)).1

lemma initConfig_init : A.Init F cl (A.initConfig F cl) := by
  refine ⟨fun p hp => ⟨rfl, by simp [initConfig, hp]⟩, fun p hp => by simp [initConfig, hp],
    fun _ _ => rfl⟩

lemma card_pos : 0 < Fintype.card (P × P) := Fintype.card_pos

/-- The pair of processes scheduled at time `t` (round robin). -/
def pairAt (t : ℕ) : P × P :=
  (Fintype.equivFin (P × P)).symm ⟨t % Fintype.card (P × P), Nat.mod_lt _ card_pos⟩

/-- Process `qs.1` delivers the next message of `qs.2` if possible. -/
def stepPair (c : SRBConfig P M S) (qs : P × P) : SRBConfig P M S :=
  if h : qs.1 ∉ F ∧ c.dl qs.1 qs.2 < (c.log qs.2).length then
    A.deliver c cl qs.1 qs.2 ((c.log qs.2)[c.dl qs.1 qs.2])
  else c

/-- One round-robin step: the scheduled pair delivers if possible. -/
def rrStep (c : SRBConfig P M S) (t : ℕ) : SRBConfig P M S := A.stepPair F cl c (pairAt t)

/-- The round-robin execution. -/
def rrExec : ℕ → SRBConfig P M S
  | 0 => A.initConfig F cl
  | t + 1 => A.rrStep F cl (rrExec t) t

lemma rrExec_isExec : (A.system F cl).IsExec (A.rrExec F cl) := by
  refine ⟨A.initConfig_init F cl, fun t => ?_⟩
  show A.Step F cl _ (A.stepPair F cl (A.rrExec F cl t) (pairAt (P := P) t)) ∨
    A.stepPair F cl (A.rrExec F cl t) (pairAt (P := P) t) = _
  generalize pairAt (P := P) t = qs
  unfold stepPair
  split_ifs with h
  · left; exact Step.deliver _ _ _ _ h.1 (List.getElem?_eq_getElem h.2)
  · right; rfl

/-- **Round-robin executions are fair**: fairness is not vacuous. -/
theorem rrExec_fair : Fair F (A.rrExec F cl) := by
  intro q hq s k ⟨t0, ht0⟩ _
  have he := A.rrExec_isExec F cl
  set N := Fintype.card (P × P)
  have hN : 0 < N := card_pos
  set i := ((Fintype.equivFin (P × P)) (q, s)).val with hi
  have hiN : i < N := ((Fintype.equivFin (P × P)) (q, s)).isLt
  have hpair : ∀ τ, τ % N = i → pairAt τ = (q, s) := by
    intro τ hτ
    simp only [pairAt]
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    exact hτ
  -- the counter grows at every scheduled time while it is ≤ k
  have key : ∀ j, min j (k + 1) ≤ (A.rrExec F cl (t0 + j * N)).dl q s := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      obtain ⟨τ, hτ1, hτ2', hτN⟩ := exists_mod_eq (t0 + j * N) hN hiN
      have hτ2 : τ + 1 ≤ t0 + (j + 1) * N := by rw [Nat.succ_mul]; omega
      have hg := dl_le_of_le he hτ1 q s
      have hg' := dl_le_of_le he hτ2 q s
      by_cases hk : k + 1 ≤ (A.rrExec F cl τ).dl q s
      · have := dl_le_of_le he (show τ ≤ τ + 1 by omega) q s
        omega
      · have hlen : k < ((A.rrExec F cl τ).log s).length :=
          lt_of_lt_of_le ht0 (log_prefix_of_le he (by omega : t0 ≤ τ) s).length_le
        have hstep : (A.rrExec F cl (τ + 1)).dl q s = (A.rrExec F cl τ).dl q s + 1 := by
          show (A.stepPair F cl (A.rrExec F cl τ) (pairAt τ)).dl q s = _
          rw [hpair τ hτN]
          unfold stepPair
          rw [dite_eq_left ⟨hq, by dsimp only; omega⟩]
          exact deliver_dl_self
        omega
  refine ⟨t0 + (k + 1) * N, ?_⟩
  have := key (k + 1)
  simp only [min_self] at this
  omega

end

end SRBProtocol

end Podc.TrustedHW
