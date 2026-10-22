import Podc.Computability.Distributed.SelfStabilization.ResetUnison.Unfair

-- CSLib candidate: Cslib/Computability/Distributed/SelfStabilization/ResetUnison/Sync.lean

/-!
# Reset-based unison under the synchronous daemon

For the Boulinier–Petit–Villain unison with `α ≥ n` (`ResetUnison/Basic.lean`), every synchronous
execution from a valid configuration is in `Γ₁` from time `n + α` on (`legit_sync`).

Proof: in a synchronous execution a positive non-`allCorrect` process resets immediately, so the
reset chains of `ResetUnison/Unfair.lean` have consecutive times `τ k = k`; since chains have
fewer than `n` links, no process resets from time `n` on (`sync_no_reset`). Afterwards the minimal
negative register increases at every step (`sync_climb`), so after `α` more steps all registers are
in `stab`, and then every edge is correct.

(Boulinier, Petit and Villain, *Synchronous vs. asynchronous unison*, Algorithmica 2008, give the
bound `α + lcp(g) + diam(g)` for general `α`; for `α ≥ n` the bound `n + α` proved here suffices.)
-/

namespace Cslib.SelfStabilization.ResetUnison

open Cslib.SelfStabilization

variable {V : Type*} {K α : ℕ} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
  {e : ℕ → V → ℤ}

theorem next_of_converge {γ : V → ℤ} {v : V} (h : ConvergeStep α G γ v) :
    next K α G γ v = γ v + 1 := by
  unfold next
  rw [ite_eq_left h]
  split_ifs <;> rw [phi_of_neg h.1.2]

/-- In a synchronous execution, a process enabled for `RA` executes it. -/
theorem sync_ra (_h : IsSyncExec (next K α G) e) {v : V} {t : ℕ}
    (hr : ResetInit K G (e t) v) :
    RA (K := K) (G := G) e (syncSet (next := next K α G) e) v t := by
  refine ⟨?_, hr⟩
  show next K α G (e t) v ≠ e t v
  rw [next_of_reset hr]; have := hr.2; omega

/-- In a synchronous execution, no process resets from time `n` on (for `α ≥ n`). -/
theorem sync_no_reset (hK : 3 ≤ K) (hα : Fintype.card V ≤ α) (hα1 : 1 ≤ α)
    (h : IsSyncExec (next K α G) e) :
    ∀ t, Fintype.card V ≤ t → ∀ v, ¬ ResetInit K G (e t) v := by
  intro t ht v hr
  have hu := h.isUnfairRun
  obtain ⟨j, w, τ, hc, hw, hτ⟩ := mem_chainEnds_of_RA hK hu t v (sync_ra h hr)
  have hres : ∀ s x, 0 < e s x → ¬ AllCorrect K G (e s) x → e (s + 1) x = -(α : ℤ) :=
    fun s x hp hac => (sync_ra h ⟨hac, hp⟩).succ hu
  have hcons : ∀ k, k ≤ j → τ k = k := by
    intro k
    induction k with
    | zero =>
      intro _
      by_contra hne
      have hi := hc.1
      have hpos := hi.1.2.2
      obtain ⟨h0v, h0a⟩ := hi.2 0 (Nat.zero_le _)
      have h1 := (hi.2 1 (by omega)).1
      rw [hres 0 _ (by rw [h0v]; exact hpos) h0a] at h1
      omega
    | succ k ih =>
      intro hk
      have hC := hc.2 k (by omega)
      have hlt := hC.2.2.1
      by_contra hne
      have hpos := hC.2.1.2.2
      obtain ⟨h1v, h1a⟩ := hC.2.2.2.2 (τ k + 1) (by omega) (by omega)
      have h2 := (hC.2.2.2.2 (τ k + 2) (by omega) (by rw [ih (by omega)] at hlt ⊢; omega)).1
      rw [hres (τ k + 1) _ (by rw [h1v]; exact hpos) h1a] at h2
      omega
  have := hc.length_lt hα hα1 hu
  have := hcons j le_rfl
  simp only at hw hτ
  omega

/-- After the last reset, the minimal negative register increases at every step. -/
theorem sync_climb (hK : 3 ≤ K) (hα : Fintype.card V ≤ α) (hα1 : 1 ≤ α)
    (h : IsSyncExec (next K α G) e) (h0 : Valid K α (e 0)) :
    ∀ k v, e (Fintype.card V + k) v < 0 → -(α : ℤ) + k ≤ e (Fintype.card V + k) v := by
  have hu := h.isUnfairRun
  have hval := valid_run (by omega) hu h0
  have hnr := sync_no_reset hK hα hα1 h
  set N := Fintype.card V
  intro k
  induction k with
  | zero => intro v _; simpa using (hval _ v).1
  | succ k ih =>
    intro v hv
    have hnra : ∀ x, ¬ RA (K := K) (G := G) e (syncSet (next := next K α G) e) x (N + k) :=
      fun x hr => hnr (N + k) (by omega) x hr.2
    rw [show N + (k + 1) = N + k + 1 by omega] at hv ⊢
    have hneg : e (N + k) v < 0 := by
      by_contra hnn
      push Not at hnn
      rcases nonneg_cases hu hnn (hnra v) with h1 | ⟨_, _, h1⟩
      · omega
      · rw [h1] at hv; unfold succK at hv; split_ifs at hv <;> omega
    have hk := ih v hneg
    rcases eq_or_lt_of_le hk with heq | hlt
    · -- `v` is minimal, so it executes `CA`
      have hc : ConvergeStep α G (e (N + k)) v := by
        refine ⟨⟨(hval _ v).1, hneg⟩, fun u hu' => ?_⟩
        have hu0 : e (N + k) u ≤ 0 := by
          by_contra hpos
          push Not at hpos
          apply hnr (N + k) (by omega) u ⟨fun hac => ?_, hpos⟩
          have := (hac v hu'.symm).2.1.1; omega
        refine ⟨⟨(hval _ u).1, hu0⟩, ?_⟩
        rcases eq_or_lt_of_le hu0 with h' | h'
        · omega
        · have := ih u h'; omega
      rw [h (N + k), next_of_converge hc]
      push_cast at heq ⊢; omega
    · rcases neg_cases hu hneg with h1 | ⟨_, h1, _⟩ <;> rw [h1] <;> push_cast at hlt ⊢ <;> omega

/-- **Synchronous convergence** (for `α ≥ n`): a synchronous execution from a valid configuration
is in `Γ₁` at time `n + α`, hence forever after. -/
theorem legit_sync [Nonempty V] (hK : 3 ≤ K) (hα : Fintype.card V ≤ α)
    (h : IsSyncExec (next K α G) e) (h0 : Valid K α (e 0)) :
    ∀ t, Fintype.card V + α ≤ t → Legit K G (e t) := by
  have hα1 : 1 ≤ α := le_trans Fintype.card_pos hα
  have hu := h.isUnfairRun
  have hval := valid_run (by omega) hu h0
  have hnr := sync_no_reset hK hα hα1 h
  have hcl := sync_climb hK hα hα1 h h0 α
  set N := Fintype.card V
  have hL : Legit K G (e (N + α)) := by
    have hnn : ∀ v, 0 ≤ e (N + α) v := fun v => by
      by_contra hneg; push Not at hneg; have := hcl v hneg; omega
    have hpos : ∀ v, 0 < e (N + α) v → AllCorrect K G (e (N + α)) v := fun v hp => by
      by_contra hac; exact hnr (N + α) (by omega) v ⟨hac, hp⟩
    intro v u hu'
    rcases eq_or_lt_of_le (hnn v) with hv | hv
    · rcases eq_or_lt_of_le (hnn u) with hu0 | hu0
      · exact ⟨⟨hnn v, (hval _ v).2⟩, ⟨hnn u, (hval _ u).2⟩, Or.inl (by rw [← hv, ← hu0])⟩
      · exact (hpos u hu0 v hu'.symm).symm
    · exact hpos v hv u hu'
  exact fun t ht => legit_run hK hu hL t ht

end Cslib.SelfStabilization.ResetUnison
