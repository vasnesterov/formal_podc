import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Main

/-!
# Non-vacuity of the fallback hypothesis (for `t = 0`)

The hypothesis `Fallback` of `theorem_3_1` is satisfiable: for `t = 0`, the one-round protocol
"send your input to everybody, decide the conjunction of all values" is a fallback with `Rfb = 1`
and `mfb = n`. (For `t ≥ 1` the paper uses the protocol of Momose and Ren, which we do not
formalize.)
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ}

/-- Send the input in round 0; decide the conjunction of the own input and all received values. -/
def andBA (n : ℕ) : Protocol (Fin n) Bool Bool Bool where
  send _ x h _ := if h.length = 0 then some x else none
  decide _ x h := match h with
    | [] => none
    | ib :: _ => some (x && decide (∀ q, ib q ≠ some false))

lemma andBA_status_succ (s : Scenario (Fin n) Bool Bool) (r : ℕ) (p : Fin n) :
    status ⊤ (andBA n) s (r + 1) p = some (s.input p &&
      decide (∀ q, deliver ⊤ (andBA n) s (hist ⊤ (andBA n) s 0) 0 q p ≠ some false)) := by
  have h1 : (hist ⊤ (andBA n) s (r + 1) p).take 1 = hist ⊤ (andBA n) s 1 p :=
    take_hist _ _ _ (by omega) p
  unfold status
  rcases hh : hist ⊤ (andBA n) s (r + 1) p with _ | ⟨ib, rest⟩
  · have := length_hist ⊤ (andBA n) s (r + 1) p; rw [hh] at this; simp at this
  · rw [hh] at h1
    simp only [List.take_succ_cons, List.take_zero, hist_succ, hist_zero, List.nil_append,
      List.cons.injEq, and_true] at h1
    subst h1; rfl

/-- `andBA` is a fallback protocol for `t = 0`. -/
theorem andBA_fallback [NeZero n] : Fallback (andBA n) (Auth.none (Fin n) Bool) 0 1 n where
  unforging := Protocol.unforging_none _
  solves := by
    intro s hZ hrel _ _
    have hb : s.byz = ∅ := eq_empty_of_mem_atMost_zero hZ
    -- the common decision
    have hdel : ∀ p q, deliver ⊤ (andBA n) s (hist ⊤ (andBA n) s 0) 0 q p =
        if q = p then none else some (s.input q) := by
      intro p q
      by_cases h : q = p
      · subst h; simp [deliver]
      · simp [deliver, h, hb, hrel 0 q p, andBA]
    have hval : ∀ p, (s.input p && decide (∀ q, deliver ⊤ (andBA n) s (hist ⊤ (andBA n) s 0) 0 q p
        ≠ some false)) = decide (∀ q, s.input q = true) := by
      intro p
      simp only [hdel]
      by_cases hall : ∀ q, s.input q = true
      · simp [hall]
      · push_neg at hall
        obtain ⟨q, hq⟩ := hall
        have hqf : s.input q = false := by simpa using hq
        have hR : decide (∀ q, s.input q = true) = false := by
          simp only [decide_eq_false_iff_not, not_forall]; exact ⟨q, by simp [hqf]⟩
        rw [hR]
        by_cases hqp : q = p
        · subst hqp; simp [hqf]
        · have hL : decide (∀ q', (if q' = p then none else some (s.input q')) ≠ some false)
              = false := by
            simp only [decide_eq_false_iff_not, not_forall, not_not]
            exact ⟨q, by simp [hqp, hqf]⟩
          rw [hL, Bool.and_false]
    have hdec : ∀ p, Decides ⊤ (andBA n) s p (decide (∀ q, s.input q = true)) := fun p =>
      ⟨1, by rw [andBA_status_succ, hval], fun r hr => by
        rw [show r = 0 by omega]; simp [status, andBA]⟩
    refine ⟨⟨fun p _ => ⟨_, hdec p⟩, fun v hv p hp => ?_, fun p _ q _ v w hv hw => ?_⟩,
      fun p _ => ⟨1, le_rfl, _, by rw [andBA_status_succ]⟩⟩
    · have hall : ∀ q, s.input q = v := fun q => hv q (by simp [Scenario.honest, hb])
      have := hdec p
      cases v
      · have h' : decide (∀ q, s.input q = true) = false := by
          simp only [decide_eq_false_iff_not, not_forall]
          exact ⟨p, by simp [hall p]⟩
        have h := hdec p; rw [h'] at h; exact h
      · have h' : decide (∀ q, s.input q = true) = true := by simp [hall]
        have h := hdec p; rw [h'] at h; exact h
    · rw [FirstSome.unique hv (hdec p), FirstSome.unique hw (hdec q)]
  msgs := by
    intro s p _ T
    calc ∑ r ∈ range T, sendsAt (andBA n) s r p ≤ ∑ r ∈ range T, (if r = 0 then n else 0) := by
          apply sum_le_sum
          intro r _
          split_ifs with h
          · unfold sendsAt; exact (card_le_univ _).trans (by simp)
          · unfold sendsAt
            apply Nat.le_of_eq
            rw [card_eq_zero, filter_eq_empty_iff]
            intro q _
            have hl := length_hist ⊤ (andBA n) s r p
            show ¬ (q ≠ p ∧ ((if (hist ⊤ (andBA n) s r p).length = 0 then some (s.input p)
              else none) : Option Bool).isSome = true)
            rw [hl]; simp [h]
      _ ≤ n := by
          rw [sum_ite_eq']
          split_ifs <;> omega

/-- **Non-vacuity of Theorem 3.1**: its hypotheses hold (for `t = 0`, with `andBA` as fallback). -/
theorem theorem_3_1_nonvacuous [NeZero n] (hn : 0 < n) :
    ∃ (π : Params n) (Mf Sf : Type) (Afb : Protocol (Fin n) Bool Mf Bool) (Af : Auth (Fin n) Mf Sf)
      (Rfb mfb : ℕ), 2 * π.t < n ∧ Fallback Afb Af π.t Rfb mfb ∧ Rfb ≤ 1 * n ∧ mfb ≤ 1 * n :=
  ⟨⟨0⟩, Bool, Empty, andBA n, Auth.none (Fin n) Bool, 1, n, by simpa using hn, andBA_fallback,
    by omega, by omega⟩

end Podc.FewToManyFaultsBA.Sync
