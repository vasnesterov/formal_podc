import Papers.PODC2013.SpeculativeStabilization.Model

/-!
# Theorem 1: SSME is self-stabilizing for mutual exclusion under the unfair distributed daemon

The legitimate configurations are `Γ₁`. Convergence to `Γ₁` is the convergence of the
Boulinier–Petit–Villain unison under the unfair daemon (`ResetUnison.exists_legit`, proved here for
`α = n ≥ n`, `K > n`; the paper invokes [Boulinier, Petit, Villain, PODC 2004] as a black box).
In `Γ₁` at most one process is privileged (`legit_safe`), and every process executes its critical
section infinitely often (`ResetUnison.visits_of_legit`).
-/

namespace Podc.SpeculativeStabilization

open Cslib.SelfStabilization Cslib.SelfStabilization.ResetUnison

variable {V : Type*} [Fintype V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- From a configuration of `Γ₁`, every execution of SSME (under any daemon allowed by the unfair
one) satisfies mutual exclusion. -/
theorem mutualExclusion_of_gamma1 (hconn : G.Connected) {ident : V → ℕ}
    (hinj : Function.Injective ident) (hid : ∀ v, ident v < Fintype.card V)
    {e : ℕ → V → ℤ} {S : ℕ → Set V} (h : IsUnfairRun (ssme G) e S) (h0 : SValid G (e 0))
    {T0 : ℕ} (hL : Gamma1 G (e T0)) :
    (∀ t, T0 ≤ t → ∀ u v, Privileged G ident u (e t) → Privileged G ident v (e t) → u = v) ∧
      ∀ v T, ∃ t, T ≤ t ∧ Privileged G ident v (e t) ∧ v ∈ S t := by
  have hK := three_le_clockSize (G := G)
  refine ⟨fun t ht u v hu hv => legit_safe hconn hinj hid (legit_run hK h hL t ht) hu hv,
    fun v T => ?_⟩
  obtain ⟨h1, h2⟩ := privVal_bounds (G := G) hid v
  have hD := one_le_diam hconn (G := G)
  exact visits_of_legit hK card_lt_clockSize hconn (exists_adj hconn) h h0 hL v
    (by omega) (by omega) T

/-- **Theorem 1.** SSME is self-stabilizing for mutual exclusion under the unfair distributed
daemon (Definition 3), on every connected graph with `n ≥ 2` processes and identities
`{0, …, n - 1}` (any injective `id : V → {0, …, n-1}`). The legitimate set is `Γ₁`. -/
theorem theorem_1 (hconn : G.Connected) (ident : V → ℕ) (hinj : Function.Injective ident)
    (hid : ∀ v, ident v < Fintype.card V) :
    IsLegitimate (unfairExecs (ssme G) (SValid G)) (MutualExclusion (Privileged G ident))
      {x | Gamma1 G x.1} := by
  have hK := three_le_clockSize (G := G)
  refine ⟨fun ω ⟨h, h0⟩ => ?_, fun ω ⟨h, h0⟩ hL => ?_⟩
  · exact exists_legit hK le_rfl card_lt_clockSize hconn h h0
  · obtain ⟨hs, hl⟩ := mutualExclusion_of_gamma1 hconn hinj hid h h0 (T0 := 0) hL
    exact ⟨fun t u v hu hv => hs t (Nat.zero_le _) u v hu hv, hl⟩

/-- **Theorem 1**, in the form of Definition 3: SSME is self-stabilizing. -/
theorem theorem_1' (hconn : G.Connected) (ident : V → ℕ) (hinj : Function.Injective ident)
    (hid : ∀ v, ident v < Fintype.card V) :
    SelfStabilizing (unfairExecs (ssme G) (SValid G)) (MutualExclusion (Privileged G ident)) :=
  ⟨_, theorem_1 hconn ident hinj hid⟩

end Podc.SpeculativeStabilization
