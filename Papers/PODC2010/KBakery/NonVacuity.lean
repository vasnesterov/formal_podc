import Papers.PODC2010.KBakery.Liveness

/-!
# Non-vacuity: a round-robin execution in which every process enters the CS

For every finite nonempty set of processes and every `k ≥ 1`, the round-robin schedule (with the
smallest remaining index chosen in every `foreach`) is an execution without crashes; by starvation
freedom every process enters the critical section in it. So the hypotheses of the liveness
theorems are satisfiable and the safety theorems are not vacuous.
-/

set_option linter.unusedSectionVars false

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P] [Nonempty P]

/-- The adversary's choice: the smallest index still to visit. -/
def pick (s : Cfg P) (p : P) : P :=
  if h : ((s.pc p).rem).Nonempty then ((s.pc p).rem).min' h else p

lemma pick_admissible (s : Cfg P) (p : P) : Admissible s p (pick s p) := by
  unfold Admissible pick
  split_ifs with h
  · exact Or.inl (min'_mem _ h)
  · exact Or.inr (not_nonempty_iff_eq_empty.1 h)

/-- Round-robin schedule. -/
noncomputable def rrSched (t : ℕ) : P :=
  (Fintype.equivFin P).symm ⟨t % Fintype.card P, Nat.mod_lt _ Fintype.card_pos⟩

/-- Configurations of the round-robin execution. -/
noncomputable def rrCfg (fife : Bool) (k : ℕ) : ℕ → Cfg P
  | 0 => Cfg.init
  | t + 1 => stepAt fife k (rrCfg fife k t) (rrSched t) (pick (rrCfg fife k t) (rrSched t))

/-- The round-robin execution. -/
noncomputable def rrRun (fife : Bool) (k : ℕ) : Run fife k P where
  s := rrCfg fife k
  sched := rrSched
  choice t := pick (rrCfg fife k t) (rrSched t)
  init := rfl
  adm t := pick_admissible _ _
  step _ := rfl

lemma rrSched_index (p : P) (n : ℕ) :
    rrSched (n * Fintype.card P + (Fintype.equivFin P p).val) = p := by
  unfold rrSched
  apply (Fintype.equivFin P).injective
  simp only [Equiv.apply_symm_apply]
  ext
  simp [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt (Fintype.equivFin P p).isLt]

lemma rrRun_not_crashed (fife : Bool) (k : ℕ) (p : P) : ¬ (rrRun (P := P) fife k).Crashed p := by
  rintro ⟨T, hT⟩
  have h := (hT (T * Fintype.card P + (Fintype.equivFin P p).val) (by
    have := Fintype.card_pos (α := P)
    nlinarith)).1
  exact h (rrSched_index p T)

/-- Every process enters the CS in the round-robin execution (both variants, every `k ≥ 1`). -/
theorem rrRun_enters_cs (fife : Bool) (k : ℕ) (hk : 1 ≤ k) (p : P) :
    ∃ t, ((rrRun (P := P) fife k).s t).pc p = .cs := by
  classical
  set r := rrRun (P := P) fife k
  set t₀ := (Fintype.equivFin P p).val
  -- before its first turn `p` is in the NCS
  have hncs : ∀ t ≤ t₀, (r.s t).pc p = .ncs := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
      have hs : r.sched t ≠ p := by
        intro h
        have := congrArg (fun q => (Fintype.equivFin P q).val) h
        simp only [r, rrRun, rrSched, Equiv.apply_symm_apply] at this
        rw [Nat.mod_eq_of_lt (by have := (Fintype.equivFin P p).isLt; omega)] at this
        omega
      rw [r.pc_succ_of_ne hs]; exact ih (by omega)
  have hs₀ : r.sched t₀ = p := by
    have := rrSched_index p 0; simp only [zero_mul, zero_add] at this; exact this
  have htry : ((r.s (t₀ + 1)).pc p).InTrying := by
    rw [r.step t₀, hs₀, stepAt_pc]
    simp [core, hncs t₀ le_rfl, PC.InTrying, PC.InDoorway]
  have hcr : (univ.filter fun q => r.Crashed q).card < k := by
    have : (univ.filter fun q => r.Crashed q) = ∅ := by
      ext q; simp [r, rrRun_not_crashed]
    rw [this]; simp; omega
  obtain ⟨t, -, ht⟩ := starvation_freedom r hcr p (rrRun_not_crashed fife k p) (t₀ + 1) htry
  exact ⟨t, ht⟩

end Podc.KBakery
