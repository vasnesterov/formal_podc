import Papers.PODC2022.AsyncCycleColoring.Model

/-!
# Simulation of one algorithm by another through a state map

If `φ : S → S'` and `ψ : O → O'` intertwine the step functions of `A` and `A'`, then the
executions of `A'` from `φ ∘ init` are the images of the executions of `A` from `init`, under the
same schedule. Used for the symmetry of Algorithm 1 under reversing the order of identifiers.
-/

namespace AsyncCycle

variable {n : ℕ} {S O S' O' : Type*}

/-- Image of a configuration under state/output maps. -/
def Config.map (φ : S → S') (ψ : O → O') (c : Config n S O) : Config n S' O' :=
  ⟨fun p => φ (c.loc p), fun p => (c.reg p).map φ, fun p => (c.out p).map ψ⟩

theorem run_map {A : Alg S O} {A' : Alg S' O'} (φ : S → S') (ψ : O → O')
    (hstep : ∀ s l r, A'.step (φ s) (l.map φ) (r.map φ) = Sum.map φ ψ (A.step s l r))
    (init : ZMod n → S) (σ : ℕ → Finset (ZMod n)) (t : ℕ) :
    run A' (fun p => φ (init p)) σ t = (run A init σ t).map φ ψ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, run_succ, ih]
    set c := run A init σ t
    have hacts : ∀ p, (c.map φ ψ).Acts (σ (t + 1)) p ↔ c.Acts (σ (t + 1)) p := by
      intro p
      simp only [Config.Acts, Config.map, Option.map_eq_none_iff]
    have hreg : ∀ p, (c.map φ ψ).regAfter (σ (t + 1)) p = (c.regAfter (σ (t + 1)) p).map φ := by
      intro p
      unfold Config.regAfter
      by_cases h : c.Acts (σ (t + 1)) p
      · rw [ite_eq_left ((hacts p).2 h), ite_eq_left h]; rfl
      · rw [ite_eq_right (fun h' => h ((hacts p).1 h')), ite_eq_right h]; rfl
    have hres : ∀ p, (c.map φ ψ).res A' (σ (t + 1)) p = Sum.map φ ψ (c.res A (σ (t + 1)) p) := by
      intro p
      unfold Config.res
      rw [hreg, hreg]
      exact hstep _ _ _
    have hacts' : ∀ p, (Config.map φ ψ c).Acts (σ (t + 1)) p ↔ c.Acts (σ (t + 1)) p := hacts
    have hres' : ∀ p, Config.res A' (Config.map φ ψ c) (σ (t + 1)) p =
        Sum.map φ ψ (c.res A (σ (t + 1)) p) := hres
    unfold Config.next
    congr 1
    · funext p
      by_cases h : c.Acts (σ (t + 1)) p
      · have h' := (hacts' p).2 h
        simp only [h, h', ↓reduceIte]
        rw [hres' p]; rcases c.res A (σ (t + 1)) p with s | o <;> rfl
      · have h' : ¬ (Config.map φ ψ c).Acts (σ (t + 1)) p := fun h' => h ((hacts' p).1 h')
        simp only [h, h', ↓reduceIte]; rfl
    · funext p
      exact hreg p
    · funext p
      by_cases h : c.Acts (σ (t + 1)) p
      · have h' := (hacts' p).2 h
        simp only [h, h', ↓reduceIte]
        rw [hres' p]; rcases c.res A (σ (t + 1)) p with s | o <;> rfl
      · have h' : ¬ (Config.map φ ψ c).Acts (σ (t + 1)) p := fun h' => h ((hacts' p).1 h')
        simp only [h, h', ↓reduceIte]; rfl

theorem actsAt_map {A : Alg S O} {A' : Alg S' O'} (φ : S → S') (ψ : O → O')
    (hstep : ∀ s l r, A'.step (φ s) (l.map φ) (r.map φ) = Sum.map φ ψ (A.step s l r))
    (init : ZMod n → S) (σ : ℕ → Finset (ZMod n)) (t : ℕ) (p : ZMod n) :
    ActsAt A' (fun p => φ (init p)) σ t p ↔ ActsAt A init σ t p := by
  unfold ActsAt
  rw [run_map φ ψ hstep]
  simp only [Config.Acts, Config.map, Option.map_eq_none_iff]

theorem workActs_map {A : Alg S O} {A' : Alg S' O'} (φ : S → S') (ψ : O → O')
    (hstep : ∀ s l r, A'.step (φ s) (l.map φ) (r.map φ) = Sum.map φ ψ (A.step s l r))
    (init : ZMod n → S) (σ : ℕ → Finset (ZMod n)) (p : ZMod n) (T : ℕ) :
    workActs A' (fun p => φ (init p)) σ p T = workActs A init σ p T := by
  unfold workActs
  congr 1
  ext t
  simp only [Finset.mem_filter, actsAt_map φ ψ hstep]

end AsyncCycle
