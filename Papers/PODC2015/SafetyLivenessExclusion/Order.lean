import Papers.PODC2015.SafetyLivenessExclusion.CounterexampleWF

/-!
# The order on liveness properties (§3.2)

The paper defines "`L₁` is weaker than `L₂`" semantically (every implementation ensuring `L₂`
ensures `L₁`) and states "It is easy to see that `L₁` is weaker than `L₂` iff `L₂ ⊆ L₁`"; all its
proofs then use `⊆`. The "if" direction is trivial; the "only if" direction fails, e.g. for the
reactive implementations (the class in which Theorem 4.9 holds): the history `inv₀` with an idle
correct `p₁` is fair for no reactive valid implementation, so adding it to wait-freedom gives a
semantically equivalent but strictly larger property (`weaker_iff_subset_false`).

We therefore formalize the paper's results with the inclusion order, as its proofs do.
-/

namespace Podc.SafetyLivenessExclusion.Counterexample

open Hist Impl

/-- The history `inv₀` (process `p₀` invoked; `p₁` idle). -/
def g0 : List E := [.inv 0 ()]

/-- In a reactive valid implementation, `inv₀` is never a fair history: the idle correct `p₁`
cannot take steps, but always has an enabled invocation. -/
theorem g0_not_fair {I : Impl 2 Unit Unit} (hV : I.Valid) (hR : I.Reactive) :
    Hist.fin g0 ∉ I.fairH := by
  have hσ : runStat g0 = some (Function.update (fun _ => PStat.idle) 0 .pend) := by decide
  have hidle : Function.update (fun _ => PStat.idle) (0 : Fin 2) PStat.pend 1 = .idle := by decide
  rintro (⟨c, l, hc, hfin, heq⟩ | ⟨e, hfair, he⟩)
  · cases heq
    obtain ⟨c', ht⟩ := hV.2.2 c g0 hc _ hσ 1 hidle ()
    exact hfin _ _ ht
  · obtain ⟨K, hK⟩ := he
    dsimp only at hK
    have hreach : ∀ k ≥ K, I.Reach (e.cfg k) g0 := fun k hk =>
      hK k hk ▸ ⟨e.cfg 0, e.pre k, e.init, e.run_pre k, rfl⟩
    have noact : ∀ k ≥ K, ¬ (e.act k).IsProc 1 := by
      intro k hk hp
      cases ha : e.act k with
      | ext e' =>
        have h1 := hK (k + 1) (by omega)
        rw [e.pre_succ, hist_append, hK k hk, ha] at h1
        simp at h1
      | step j =>
        rw [ha] at hp
        simp only [Act.IsProc] at hp; subst hp
        have ht := e.trans k
        rw [ha] at ht
        exact hR _ _ (hreach k hk) _ hσ 1 hidle ⟨_, ht⟩
      | base => rw [ha] at hp; exact hp
    rcases hfair 1 with h | h
    · obtain ⟨k, hk, hp⟩ := h K
      exact noact k hk hp
    · obtain ⟨k, hk, hne⟩ := h K
      obtain ⟨c', ht⟩ := hV.2.2 _ g0 (hreach k hk) _ hσ 1 hidle ()
      exact hne ⟨.ext (.inv 1 ()), rfl, id, c', ht⟩

theorem g0_not_waitFree : Hist.fin g0 ∉ WaitFree := by
  rintro ⟨-, h⟩
  have hσ : runStat g0 = some (Function.update (fun _ => PStat.idle) 0 .pend) := by decide
  obtain ⟨l', σ', hl', hpre, hσ', hne⟩ := h g0 (List.prefix_refl _) _ hσ 0 (by decide)
  have : l' = g0 := List.IsPrefix.eq_of_length hl' (le_antisymm hl'.length_le hpre.length_le)
  subst this
  rw [hσ] at hσ'; cases hσ'
  exact hne (by decide)

/-- **The remark of §3.2 is false** for the reactive implementations: there are liveness
properties `L₁ = WaitFree` and `L₂ = WaitFree ∪ {inv₀}` such that every implementation ensuring
`L₂` ensures `L₁` (so `L₁` is weaker than `L₂` in the paper's sense), yet `L₂ ⊄ L₁`. -/
theorem weaker_iff_subset_false :
    ∃ L₁ L₂ : Set (Hist E), WaitFree ⊆ L₁ ∧ WaitFree ⊆ L₂ ∧
      (∀ I : Impl 2 Unit Unit, I.Valid → I.Reactive → I.fairH ⊆ L₂ → I.fairH ⊆ L₁) ∧
      ¬ L₂ ⊆ L₁ := by
  refine ⟨WaitFree, WaitFree ∪ {Hist.fin g0}, le_rfl, Set.subset_union_left, ?_, ?_⟩
  · intro I hV hR hI h hh
    rcases hI hh with h' | h'
    · exact h'
    · rw [Set.mem_singleton_iff] at h'; subst h'; exact absurd hh (g0_not_fair hV hR)
  · intro h
    exact g0_not_waitFree (h (Or.inr rfl))

end Podc.SafetyLivenessExclusion.Counterexample
