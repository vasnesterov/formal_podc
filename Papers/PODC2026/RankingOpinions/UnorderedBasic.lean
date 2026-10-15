import Cslib.Computability.Distributed.PopulationProtocols.Symmetrize

/-!
# Fairness for asymmetric protocols, symmetrization, and small helpers

Breitkopf, Dallot, El-Hayek, Schmid, *Ranking Opinions with Few States in Population Protocols*,
PODC 2026 (arXiv:2605.18707), Section 5 (unordered setting).

The protocols of Section 5 (Ordering, Ord-Circles) are *asymmetric*: in most rules only the
initiator `a` of an interaction `(a, b)` changes its state. Definition 2.1 of the paper ("every
pair of agents interacts infinitely often") can be read with unordered pairs (this is
`Execution.WeaklyFair` of `Cslib.Computability.Distributed.PopulationProtocols.Basic`) or with ordered pairs
(`Execution.OrderedFair`, now in `Cslib.Computability.Distributed.PopulationProtocols.Symmetrize`: every agent meets every other agent infinitely often *as the
initiator*). Section 5 is only correct for the second reading (see `UnorderedOrdering.lean`,
`UnorderedOrdCircles.lean` for counterexamples under the first one).

We also define the *symmetrization* `P.symm` of a protocol (every interaction performs `δ` with
both role assignments, one after the other) and show that an execution of `P.symm` that is weakly
fair (unordered pairs) unfolds into an execution of `P` that is fair for ordered pairs. This is
the generic fix of the Section 5 protocols for the unordered reading of weak fairness.
-/

namespace Cslib.PopulationProtocol.Protocol

variable {Q A : Type*} [DecidableEq A] {P : Protocol Q}

/-- An execution is determined by its initial configuration and its schedule. -/
def Execution.ofSchedRec (P : Protocol Q) (C0 : Config A Q) (s : ℕ → A × A)
    (hs : ∀ t, (s t).1 ≠ (s t).2) : P.Execution A where
  config t := Nat.rec C0 (fun t C => P.interact C (s t).1 (s t).2) t
  sched := s
  sched_ne := hs
  step _ := rfl

@[simp] lemma Execution.ofSchedRec_zero (C0 : Config A Q) (s : ℕ → A × A)
    (hs : ∀ t, (s t).1 ≠ (s t).2) : (Execution.ofSchedRec P C0 s hs).config 0 = C0 := rfl

end Cslib.PopulationProtocol.Protocol

namespace RankingOpinions

/-- A sequence of natural numbers that is antitone from `T0` on is eventually constant. -/
lemma eventually_const_of_antitone (f : ℕ → ℕ) (T0 : ℕ) (h : ∀ t ≥ T0, f (t + 1) ≤ f t) :
    ∃ T ≥ T0, ∀ t ≥ T, f t = f T := by
  have mono : ∀ s ≥ T0, ∀ t ≥ s, f t ≤ f s := by
    intro s hs t hst
    induction t, hst using Nat.le_induction with
    | base => exact le_rfl
    | succ t hst ih => exact (h t (by omega)).trans ih
  induction hn : f T0 using Nat.strong_induction_on generalizing T0 with
  | _ n ih =>
  by_cases hc : ∀ t ≥ T0, f t = f T0
  · exact ⟨T0, le_rfl, hc⟩
  · push Not at hc
    obtain ⟨t, ht, hne⟩ := hc
    have hlt : f t < f T0 := lt_of_le_of_ne (mono T0 le_rfl t ht) hne
    obtain ⟨T, hT, hT'⟩ := ih (f t) (hn ▸ hlt) t (fun s hs => h s (by omega))
      (fun s hs u hu => mono s (by omega) u hu) rfl
    exact ⟨T, by omega, hT'⟩

/-- A bounded sequence of natural numbers that is monotone from `T0` on is eventually
constant. -/
lemma eventually_const_of_monotone (f : ℕ → ℕ) (B T0 : ℕ) (hB : ∀ t, f t ≤ B)
    (h : ∀ t ≥ T0, f t ≤ f (t + 1)) : ∃ T ≥ T0, ∀ t ≥ T, f t = f T := by
  obtain ⟨T, hT, hT'⟩ := eventually_const_of_antitone (fun t => B - f t) T0
    (fun t ht => by have := h t ht; have := hB t; have := hB (t + 1); omega)
  refine ⟨T, hT, fun t ht => ?_⟩
  have := hT' t ht; have := hB t; have := hB T; omega

end RankingOpinions
