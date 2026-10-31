import Papers.PODC2018.PartialReplicationCausal.Necessity.Model
import Papers.PODC2018.PartialReplicationCausal.Theorem3

/-!
# The algorithm of Section 3.2 is a metadata algorithm implementing causal consistency

`paperAlg X` is the edge-indexed timestamp algorithm of Section 3.2 as an instance of the general
class `Alg` of Theorem 1, and `paperAlg_implements` shows (from Theorem 3) that it implements
replica-centric causal consistency. Together with Theorem 1 (`Theorem1.lean`) this is the paper's
"necessary and sufficient" claim; it also shows that the hypothesis of Theorem 1 is satisfiable.
-/

namespace Podc.PartialReplicationCausal.Necessity

open Classical

variable {ι Reg : Type*} (X : ι → Set Reg)

/-- The algorithm of Section 3.2 as a metadata algorithm (metadata = edge-indexed timestamp). -/
noncomputable def paperAlg : Alg ι Reg (ι → ι → ℕ) where
  init := fun _ _ _ => 0
  write := fun i m x => incr X m i x
  ready := fun i m k _ T => m k i + 1 = T k i ∧
    ∀ j, j ≠ i → j ≠ k → TsEdge X i j i → TsEdge X k j i → T j i ≤ m j i
  merge := fun i m k _ T => merge X m i k T

variable {X}

/-- Forget the values. -/
def forget (s : St ι Reg (ι → ι → ℕ)) : State ι Reg :=
  ⟨s.n, fun a => ⟨(s.log a).src, (s.log a).reg, (s.log a).ts, (s.log a).pre⟩, s.md, s.app⟩

lemma forget_hb (s : St ι Reg (ι → ι → ℕ)) : HB s = PartialReplicationCausal.HB (forget s) := rfl

lemma forget_enabled {s : St ι Reg (ι → ι → ℕ)} {i : ι} {a : ℕ} :
    Enabled X (paperAlg X) s i a ↔ PartialReplicationCausal.Enabled X (forget s) i a := Iff.rfl

lemma forget_step {s s' : St ι Reg (ι → ι → ℕ)} (h : Step X (paperAlg X) s s') :
    PartialReplicationCausal.Step X (forget s) (forget s') := by
  cases h with
  | write i x ℓ hx _ =>
    have : forget (s.write (paperAlg X) i x ℓ) = (forget s).write X i x := by
      simp only [forget, St.write, State.write, paperAlg]
      congr 1
      funext a
      by_cases ha : a = s.n
      · subst ha; simp
      · simp [Function.update_of_ne ha]
    rw [this]; exact .write _ i x hx
  | apply i a ha =>
    have : forget (s.apply (paperAlg X) i a) = (forget s).apply X i a := rfl
    rw [this]; exact .apply _ i a (forget_enabled.1 ha)

lemma forget_reachable {s : St ι Reg (ι → ι → ℕ)} (hs : Reachable X (paperAlg X) s) :
    PartialReplicationCausal.Reachable X (forget s) := by
  obtain ⟨s₀, h₀, hrun⟩ := hs
  refine ⟨forget s₀, ⟨h₀.1, h₀.2.1, h₀.2.2⟩, ?_⟩
  induction hrun with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (forget_step hst)

/-- **Sufficiency (Theorem 3), in the setting of Theorem 1:** the algorithm of Section 3.2
implements replica-centric causal consistency. -/
theorem paperAlg_implements : Implements X (paperAlg X) := by
  refine ⟨fun s hs => theorem_3_safety (forget_reachable hs), ?_⟩
  intro E hE t u i hu hux hdeps
  let E' : PartialReplicationCausal.Execution X :=
    ⟨fun t => forget (E.σ t), ⟨E.init.1, E.init.2.1, E.init.2.2⟩, fun t => by
      rcases E.step t with h | h
      · exact Or.inl (forget_step h)
      · exact Or.inr (by rw [h])⟩
  exact theorem_3_liveness E' (fun i a t₀ h => hE i a t₀ fun t ht => forget_enabled.2 (h t ht))
    hu hux hdeps

end Podc.PartialReplicationCausal.Necessity
