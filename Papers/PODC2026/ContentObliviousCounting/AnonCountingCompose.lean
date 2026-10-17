import Papers.PODC2026.ContentObliviousCounting.AnonCountingMain

/-!
# Anonymous counting: composability (Lemma 12)

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026, Lemma 12: the last phase (and with it the whole counting procedure, including the
broadcast of `count`) has the composable ending property. We prove the semantic condition
`Proc.Composable` of `Cslib/Computability/Distributed/ContentOblivious/Compose.lean` (bounded pulses, quiescent termination,
and `clean`: a node still running never waits on a link whose other end has returned unless a pulse
of the procedure is in transit on it), so the counting procedure can be followed by any other
procedure (Theorem 9).
-/

namespace Podc.ContentOblivious.AnonCounting

open Cslib.ContentOblivious Finset

set_option linter.unusedSectionVars false
set_option linter.deprecated false

lemma kind_f_not_term {n : ℕ} {κ : Kind} {p k : ℕ} (h : κ ≠ .end2 ∨ k = 0) :
    terminated (κ.f n p k) = false := by
  cases κ <;> simp only [Kind.f] <;> (try split_ifs) <;>
    simp_all [fst, nst, terminated] <;> split_ifs <;> simp [terminated]

lemma kind_g_not_term {n : ℕ} {κ : Kind} {b : ℕ} : terminated (κ.g n b) = false := by
  cases κ <;> simp [Kind.g, gst, lst, nst, terminated]

/-- Before the last wave, no node has terminated. -/
lemma stage_not_term {n : ℕ} {s : Stage} (hs : ∀ a b, s ≠ .pipe .end2 a b) (hs' : s ≠ .final)
    (p : ℕ) : terminated ((s.abs n).st p) = false := by
  cases s with
  | out j m t => simp only [Stage.abs, absOut]; split_ifs <;> simp [lst, nst, terminated]
  | back j m t => simp only [Stage.abs, absBack]; split_ifs <;> simp [lst, nst, terminated]
  | xfer j x y => simp only [Stage.abs, absXfer]; split_ifs <;> simp [lst, nst, terminated]
  | pipe κ a b =>
    simp only [Stage.abs, absPipe]
    split_ifs
    · exact kind_g_not_term
    · exact kind_f_not_term (Or.inl (fun h => hs a b (h ▸ rfl)))
  | final => exact absurd rfl hs'

/-- **Lemma 12** (composable ending): the counting procedure is composable. -/
theorem anonCount_composable {n : ℕ} [NeZero n] (ℓ : ZMod n) :
    anonCount.Composable (oriented n) (leaderInput ℓ) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine ⟨⟨totalPulses n, fun c hc => anonCount_totalSent_le ℓ c hc⟩, fun c hc hf => ?_, ?_⟩
  · obtain ⟨hq, hr, -⟩ := anonCount_final ℓ c hc hf
    exact ⟨hq, fun v => by rw [hr v]; rfl⟩
  · intro c hc v j hv hrd hw
    obtain ⟨s, hok, hm⟩ := reach_inv hc
    have hterm : ∀ x : ZMod n, (anonCount.result (c.st x)).isSome = terminated (c.st x) :=
      fun x => (anonCount.terminated_eq (c.st x)).symm
    rw [hterm, hm.1] at hw
    have hv' : terminated (c.st v) = false := by
      have := hterm v; rw [hv] at this; simpa using this.symm
    have htr : ∀ x b, c.recvd (x, b) < c.sent ((oriented n).peer (x, b)) ↔
        0 < (s.abs n).tr (pos ℓ x) b := by
      intro x b; rw [hm.2.1 x b]; omega
    rw [htr]
    by_cases hs : s = .final
    · subst hs; rw [hm.1] at hv'; exact absurd hv' (by simp [Stage.abs, absFinal]; split_ifs <;>
        simp [gst, fst, lst, nst, terminated])
    by_cases hs2 : ∃ a b, s = .pipe .end2 a b
    · obtain ⟨a, b, rfl⟩ := hs2
      obtain ⟨-, hpo⟩ := hok
      have hpo' := pipeOk_srcCnt.1 hpo
      have hb : b = 0 := by have := hpo'.1; simp only [Kind.K] at this; omega
      subst hb
      have hL := lead_lt hn
      rw [hm.1] at hv' hrd
      set q := pos ℓ v with hqdef
      have hqn : q < n := pos_lt ℓ v
      -- the neighbour's position
      have hwpos : pos ℓ ((oriented n).peer (v, j)).1 = if j then nxt n q else prv n q := by
        cases j
        · simp [pos_sub_one, hqdef]
        · simp [pos_add_one, hqdef]
      rw [hwpos] at hw
      -- a terminated node in the wave `end2` is a non-leader that has relayed the pulse
      have hdone : ∀ x < n, terminated ((absPipe n .end2 a 0).st x) = true → x ≠ lead n ∧ a x = 1 := by
        intro x hx hxt
        by_cases hxL : x = lead n
        · rw [hxL, pipe_st_lead, kind_g_not_term] at hxt; exact absurd hxt (by simp)
        · rw [pipe_st_ne hxL] at hxt
          have h1 := (hpo'.2.1 x hx hxL).1
          simp only [Kind.K] at h1
          refine ⟨hxL, ?_⟩
          by_contra h0
          have : a x = 0 := by omega
          rw [this, kind_f_not_term (Or.inr rfl)] at hxt; exact absurd hxt (by simp)
      simp only [Stage.abs] at hw hv' hrd ⊢
      cases j
      · -- port 0: the neighbour is the CCW one; the wave travels CCW, so this is impossible
        simp only [Bool.false_eq_true, ite_false] at hw
        obtain ⟨hwL, hwa⟩ := hdone _ (prv_lt hqn) hw
        have h1 := (hpo'.2.1 _ (prv_lt hqn) hwL).2
        simp only [src, Kind.cw, Bool.false_eq_true, ite_false, nxt_prv hqn, srcCnt] at h1
        by_cases hqL : q = lead n
        · rw [hqL, pipe_st_lead] at hrd
          simp [Kind.g, Kind.cw, gst, lst, nst, ready] at hrd
        · rw [if_neg hqL] at h1
          rw [pipe_st_ne hqL] at hv'
          have h2 := (hpo'.2.1 q hqn hqL).1
          simp only [Kind.K] at h2
          have : a q = 1 := by omega
          rw [this] at hv'; simp [Kind.f, fst, nst, terminated] at hv'
      · -- port 1: the neighbour is the CW one, from which the wave comes
        simp only [ite_true] at hw
        obtain ⟨hwL, hwa⟩ := hdone _ (nxt_lt hqn) hw
        simp only [absPipe, pipeTr_eq, Kind.cw, Kind.K, Bool.not_false, ite_true, src,
          Bool.false_eq_true, ite_false, srcCnt, if_neg hwL, hwa]
        by_cases hqL : q = lead n
        · simp [hqL]
        · rw [if_neg hqL]
          rw [pipe_st_ne hqL] at hv'
          have h2 := (hpo'.2.1 q hqn hqL).1
          simp only [Kind.K] at h2
          by_contra h0
          have : a q = 1 := by omega
          rw [this] at hv'; simp [Kind.f, fst, nst, terminated] at hv'
    · push Not at hs2
      have := stage_not_term (n := n) hs2 hs (pos ℓ ((oriented n).peer (v, j)).1)
      rw [this] at hw; exact absurd hw (by simp)

end Podc.ContentOblivious.AnonCounting
