import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Defs

/-!
# Runs of stage A

The local state `S π s r p` of party `p` after `r` rounds of a run of stage A in scenario `s`, and
the step lemma `S_succ`: the next state is the transition on the inbox augmented by self-delivery
(`aib`), where honest senders' messages are given by `out` of their current state.
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] (π : Params n)

lemma foldl_snd (p : Fin n) (h : History (Fin n) (Msg n)) (init : St n × ℕ) :
    (h.foldl (fun (sr : St n × ℕ) ib => (step π p sr.1 sr.2 ib, sr.2 + 1)) init).2 =
      init.2 + h.length := by
  induction h generalizing init with
  | nil => simp
  | cons ib h ih => simp [List.foldl_cons, ih]; omega

lemma stateOf_append (p : Fin n) (x : Bool) (h : History (Fin n) (Msg n))
    (ib : Fin n → Option (Msg n)) :
    stateOf π p x (h ++ [ib]) = step π p (stateOf π p x h) h.length ib := by
  unfold stateOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, foldl_snd]
  simp

@[simp] lemma stateOf_nil (p : Fin n) (x : Bool) : stateOf π p x [] = St.init x := rfl

/-- The graph of the network (complete). -/
abbrev G (n : ℕ) : SimpleGraph (Fin n) := ⊤

/-- The state of `p` after `r` rounds of stage A in scenario `s`. -/
noncomputable def S (s : Scenario (Fin n) Bool (Msg n)) (r : ℕ) (p : Fin n) : St n :=
  stateOf π p (s.input p) (hist (G n) (stageA π) s r p)

/-- The augmented inbox of `p` in round `r`. -/
noncomputable def aib (s : Scenario (Fin n) Bool (Msg n)) (r : ℕ) (p : Fin n) :
    Fin n → Option (Msg n) :=
  fun q => if q = p then out π p (S π s r p) r p
    else deliver (G n) (stageA π) s (hist (G n) (stageA π) s r) r q p

variable {π}

@[simp] lemma S_zero (s : Scenario (Fin n) Bool (Msg n)) (p : Fin n) :
    S π s 0 p = St.init (s.input p) := rfl

lemma S_succ (s : Scenario (Fin n) Bool (Msg n)) (r : ℕ) (p : Fin n) :
    S π s (r + 1) p = trans π p (S π s r p) r (aib π s r p) := by
  unfold S
  rw [hist_succ, stateOf_append, length_hist]
  rfl

lemma aib_self (s : Scenario (Fin n) Bool (Msg n)) (r : ℕ) (p : Fin n) :
    aib π s r p p = out π p (S π s r p) r p := by simp [aib]

lemma aib_byz {s : Scenario (Fin n) Bool (Msg n)} {r : ℕ} {p q : Fin n} (hq : q ∈ s.byz)
    (hqp : q ≠ p) : aib π s r p q = s.adv r q p := by
  simp [aib, hqp, deliver, hq, G]

/-- Honest messages (including self-delivery) are given by `out` (stage A, reliable runs). -/
lemma aib_honest {s : Scenario (Fin n) Bool (Msg n)} (hrel : s.Reliable) {r : ℕ} (hr : r < R0 n)
    (p : Fin n) {q : Fin n} (hq : q ∉ s.byz) : aib π s r p q = out π q (S π s r q) r p := by
  by_cases hqp : q = p
  · subst hqp; exact aib_self s r q
  · simp only [aib, hqp, ite_false, deliver, G, SimpleGraph.top_adj, Ne, not_false_eq_true,
      ite_true, hq, hrel r q p, stageA, length_hist, hr]
    rfl

/-- Honest parties send nothing after stage A. -/
lemma aib_honest_ge {s : Scenario (Fin n) Bool (Msg n)} {r : ℕ} (hr : R0 n ≤ r)
    {p q : Fin n} (hqp : q ≠ p) (hq : q ∉ s.byz) : aib π s r p q = none := by
  simp only [aib, hqp, ite_false, deliver, G, SimpleGraph.top_adj, Ne, not_false_eq_true,
    ite_true, hq, stageA, length_hist, not_lt.2 hr]
  split_ifs <;> rfl

end Podc.FewToManyFaultsBA.Sync
