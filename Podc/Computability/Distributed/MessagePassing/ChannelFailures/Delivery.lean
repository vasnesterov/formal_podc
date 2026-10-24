import Podc.Computability.Distributed.MessagePassing.ChannelFailures.Steps

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/ChannelFailures/Delivery.lean

/-!
# Eventual delivery in fair executions

In a fair `f`-execution, every message in transit on a reliable channel between correct
processes is eventually delivered (`Algorithm.Fair.delivered`): there is a later delivery event on
that channel whose head is the message. This is the basic tool of liveness proofs in the FIFO
`ChannelFailures` model.
-/

namespace Cslib.ChannelFailures

open Cslib.SharedMemory

variable {P : Type} {A : ObjSpec} {M L : Type} [DecidableEq P]
variable {Alg : Algorithm P A M L}

lemma _root_.List.IsPrefix.getElem?_eq_of_some {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂)
    {j : ℕ} {a : α} (hj : l₁[j]? = some a) : l₂[j]? = some a := by
  obtain ⟨t, rfl⟩ := h
  have : j < l₁.length := by
    by_contra hc; push Not at hc; rw [List.getElem?_eq_none hc] at hj; simp at hj
  rw [List.getElem?_append_left this, hj]

/-- **Eventual delivery.** In a fair `f`-execution, a message at position `j` of a channel
`q → p` between correct processes that may not disconnect is eventually at the head of the
channel when a delivery on it happens. -/
theorem Algorithm.Fair.delivered {f : FailurePattern P} {ev : ℕ → Event P A}
    (hf : Alg.Fair f ev) {q p : P} (hq : ¬ Algorithm.Crashed f ev q)
    (hp : ¬ Algorithm.Crashed f ev p) (hqp : (q, p) ∉ f.chans) :
    ∀ (j T : ℕ) (m : M), ((Alg.cfgAt ev T).chan q p)[j]? = some m →
      ∃ t ≥ T, ev t = .deliver q p ∧ ((Alg.cfgAt ev t).chan q p).head? = some m := by
  classical
  intro j
  induction j with
  | zero => ?_
  | succ j ih => ?_
  all_goals
    intro T m hm
    have hne : (Alg.cfgAt ev T).chan q p ≠ [] := by
      intro h; rw [h] at hm; simp at hm
    have hex : ∃ t, T ≤ t ∧ ev t = .deliver q p := by
      obtain ⟨t, ht, h⟩ := hf.2 q p hq hp hqp T hne
      exact ⟨t, ht, h⟩
    set t₁ := Nat.find hex with ht₁
    have hspec := Nat.find_spec hex
    have hmin : ∀ u, T ≤ u → u < t₁ → ev u ≠ .deliver q p := fun u h1 h2 h3 =>
      Nat.find_min hex h2 ⟨h1, h3⟩
    have hpre : (Alg.cfgAt ev T).chan q p <+: (Alg.cfgAt ev t₁).chan q p := by
      have h := chan_prefix_run Alg (Alg.cfgAt ev T)
        ((List.range (t₁ - T)).map fun i => ev (T + i)) (by
          intro e he
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
          exact hmin _ (by omega) (by simp at hi; omega))
      rwa [← cfgAt_add, Nat.add_sub_cancel' hspec.1] at h
    have hm' := hpre.getElem?_eq_of_some hm
  · refine ⟨t₁, hspec.1, hspec.2, ?_⟩
    cases hc : (Alg.cfgAt ev t₁).chan q p with
    | nil => simp [hc] at hm'
    | cons a rest => simp [hc] at hm' ⊢; exact hm'
  · cases hc : (Alg.cfgAt ev t₁).chan q p with
    | nil => simp [hc] at hm'
    | cons a rest =>
      have h1 := chan_step_deliver Alg (Alg.cfgAt ev t₁) hc
      have h2 : rest[j]? = some m := by simpa [hc] using hm'
      have h3 : ((Alg.cfgAt ev (t₁ + 1)).chan q p)[j]? = some m := by
        have : Alg.cfgAt ev (t₁ + 1) = (Alg.step (Alg.cfgAt ev t₁) (.deliver q p)).1 := by
          show (Alg.step (Alg.cfgAt ev t₁) (ev t₁)).1 = _; rw [hspec.2]
        rw [this]; exact h1.getElem?_eq_of_some h2
      obtain ⟨t, ht, h⟩ := ih (t₁ + 1) m h3
      exact ⟨t, by omega, h⟩

end Cslib.ChannelFailures
