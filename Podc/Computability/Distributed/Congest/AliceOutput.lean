import Cslib.Computability.Distributed.Congest.LowerBound
import Cslib.Computability.Distributed.Congest.Randomized

-- CSLib candidate: Cslib/Computability/Distributed/Congest/AliceOutput.lean

/-!
# Simulation with an output computed by Alice

`Cslib.Congest.LBFamily.simulation` produces a protocol computing "all nodes accept". Many
lower-bound reductions instead let Alice evaluate a *global* function of the final states of her
own nodes (e.g. "the spanner output by the nodes of `V_A` contains more than `τ` edges of a dense
subgraph inside `V_A`"). This file provides that variant:

* `LBFamily.simulation_alice`: a `T`-round algorithm with `B`-bit messages yields a protocol with
  `T · 2 · |Ecut| · B + 1` bits that computes `g x (final states)`, for every `g` that only looks
  at the states of `V_A`-nodes (and at Alice's input `x`).
* `LBFamily.rand_simulation_alice`: the same for randomized algorithms (private random strings,
  `LBFamily.withCoins`): the protocol on `(x, r_A)`, `(y, r_B)` computes `g` on the run with random
  strings `combine r_A r_B`; `LBFamily.errCount_simulation_alice` counts its bad coin pairs.
-/

namespace Cslib.Congest

open Cslib.CommunicationComplexity Protocol Finset

namespace LBFamily

variable {X Y V I σ : Type*} {B : ℕ} (F : LBFamily X Y V I) [∀ x y, DecidableRel (F.G x y).Adj]
  [DecidableEq V]

/-- The two-party protocol simulating the remaining `r` rounds from round `t`, after which Alice
announces (one bit) the value of `g` on her input and her simulated states. -/
noncomputable def simProtAlice [Fintype V] (A : Algorithm V I σ B) (x₀ : X) (y₀ : Y)
    (g : X → (V → σ) → Bool) :
    ℕ → ℕ → (ℕ → V → V → Msg B) → (ℕ → V → V → Msg B) → Protocol X Y Bool
  | 0, t, _, hB =>
      .alice 2 (fun x => if g x (F.simA A x y₀ hB t) then 1 else 0)
        fun i => .ret (decide (i = 1))
  | r + 1, t, hA, hB =>
      .alice (F.roundAlphabet B)
        (fun x => Fintype.equivFin _
          (fun p : F.Ecut => A.send p.1.1 (F.simA A x y₀ hB t p.1.1) p.1.2))
        fun i => .bob (F.roundAlphabet B)
          (fun y => Fintype.equivFin _
            (fun p : F.Ecut => A.send p.1.2 (F.simB A x₀ y hA t p.1.2) p.1.1))
          fun j => simProtAlice A x₀ y₀ g r (t + 1)
            (F.record hA t ((Fintype.equivFin _).symm i))
            (F.record hB t ((Fintype.equivFin _).symm j))

/-- The protocol for `r` rounds costs at most `r · 2 · |Ecut| · B + 1` bits. -/
lemma simProtAlice_cost [Fintype V] (A : Algorithm V I σ B) (x₀ : X) (y₀ : Y)
    (g : X → (V → σ) → Bool) :
    ∀ r t hA hB, (F.simProtAlice A x₀ y₀ g r t hA hB).CostLE (r * (2 * (F.Ecut.card * B)) + 1)
  | 0, t, hA, hB => by
      have h2 : Nat.clog 2 2 = 1 := by simpa using Nat.clog_pow 2 1 (by norm_num)
      simp only [simProtAlice, CostLE, zero_mul, zero_add, h2]
      exact ⟨le_rfl, fun _ => trivial⟩
  | r + 1, t, hA, hB => by
      simp only [simProtAlice, CostLE, clog_roundAlphabet]
      set m := F.Ecut.card * B
      have e : (r + 1) * (2 * m) = r * (2 * m) + 2 * m := by ring
      refine ⟨by rw [e]; omega, fun i => ⟨by rw [e]; omega, fun j => ?_⟩⟩
      have : (r + 1) * (2 * m) + 1 - m - m = r * (2 * m) + 1 := by rw [e]; omega
      rw [this]
      exact simProtAlice_cost A x₀ y₀ g r (t + 1) _ _

/-- The protocol computes `g` on the true final states, given correct message histories. -/
lemma simProtAlice_eval [Fintype V] (A : Algorithm V I σ B) (x₀ : X) (y₀ : Y)
    (g : X → (V → σ) → Bool)
    (hg : ∀ x s s', (∀ v, F.alice v = true → s v = s' v) → g x s = g x s') (x : X) (y : Y) :
    ∀ r t hA hB,
      (∀ s < t, ∀ a b, (a, b) ∈ F.Ecut → hA s a b = A.send a (A.run (F.G x y) (F.inp x y) s a) b) →
      (∀ s < t, ∀ a b, (a, b) ∈ F.Ecut → hB s a b = A.send b (A.run (F.G x y) (F.inp x y) s b) a) →
      (F.simProtAlice A x₀ y₀ g r t hA hB).eval x y = g x (A.run (F.G x y) (F.inp x y) (t + r))
  | 0, t, hA, hB, _, hhB => by
      have eA := F.simA_eq A x y y₀ hB t hhB
      have key : g x (F.simA A x y₀ hB t) = g x (A.run (F.G x y) (F.inp x y) t) :=
        hg x _ _ fun v hv => eA v hv
      simp only [simProtAlice, eval, add_zero]
      cases h : g x (F.simA A x y₀ hB t)
      · rw [← key, h]; simp
      · rw [← key, h]; simp
  | r + 1, t, hA, hB, hhA, hhB => by
      simp only [simProtAlice, eval, Equiv.symm_apply_apply]
      rw [simProtAlice_eval A x₀ y₀ g hg x y r (t + 1), show t + 1 + r = t + (r + 1) by omega]
      · intro s hs a b hab
        simp only [record]
        split_ifs with hst
        · subst hst
          exact congrArg (fun st => A.send a st b)
            (F.simA_eq A x y y₀ hB s hhB a (F.Ecut_sub _ hab).1)
        · exact hhA s (by omega) a b hab
      · intro s hs a b hab
        simp only [record]
        split_ifs with hst
        · subst hst
          exact congrArg (fun st => A.send b st a)
            (F.simB_eq A x x₀ y hA s hhA b (F.Ecut_sub _ hab).2)
        · exact hhB s (by omega) a b hab

omit [DecidableEq V] in
/-- **Simulation with Alice's output.** A `T`-round CONGEST algorithm with `B`-bit messages on a
family of lower bound graphs yields a protocol of cost `T · 2 · |Ecut| · B + 1` computing
`g x (final states)`, for any `g` that depends only on Alice's input and the final states of the
`V_A`-nodes. -/
theorem simulation_alice [Fintype V] [Nonempty X] [Nonempty Y]
    (A : Algorithm V I σ B) (T : ℕ) (g : X → (V → σ) → Bool)
    (hg : ∀ x s s', (∀ v, F.alice v = true → s v = s' v) → g x s = g x s') :
    ∃ P : Protocol X Y Bool, P.CostLE (T * (2 * (F.Ecut.card * B)) + 1) ∧
      ∀ x y, P.eval x y = g x (A.run (F.G x y) (F.inp x y) T) := by
  classical
  refine ⟨F.simProtAlice A (Classical.arbitrary X) (Classical.arbitrary Y) g T 0
    (fun _ _ _ _ => false) (fun _ _ _ _ => false), F.simProtAlice_cost A _ _ g T 0 _ _,
    fun x y => ?_⟩
  rw [F.simProtAlice_eval A _ _ g hg x y T 0 _ _ (fun s hs => absurd hs (Nat.not_lt_zero s))
    (fun s hs => absurd hs (Nat.not_lt_zero s)), zero_add]

/-! ### Randomized algorithms -/

variable {ρ : Type*}

omit [DecidableEq V] in
/-- **Simulation with Alice's output, randomized.** For a randomized algorithm (node `v` gets its
private random string as the second component of its input), Alice drawing the strings of `V_A`
and Bob those of `V_B`, the protocol computes `g` on the run with random strings
`combine r_A r_B`. -/
theorem rand_simulation_alice [Fintype V] [Nonempty X] [Nonempty Y] [Nonempty ρ]
    (A : Algorithm V (I × ρ) σ B) (T : ℕ) (g : X → (V → σ) → Bool)
    (hg : ∀ x s s', (∀ v, F.alice v = true → s v = s' v) → g x s = g x s') :
    ∃ P : Protocol (X × ({v // F.alice v = true} → ρ)) (Y × ({v // F.alice v = false} → ρ)) Bool,
      P.CostLE (T * (2 * (F.Ecut.card * B)) + 1) ∧
      ∀ x y rA rB, P.eval (x, rA) (y, rB) =
        g x (A.run (F.G x y) (fun v => (F.inp x y v, F.combine rA rB v)) T) := by
  classical
  obtain ⟨P, hc, hP⟩ := (F.withCoins (ρ := ρ)).simulation_alice A T (fun xr s => g xr.1 s)
    (fun xr s s' h => hg xr.1 s s' h)
  exact ⟨P, by simpa [withCoins] using hc, fun x y rA rB => hP (x, rA) (y, rB)⟩

/-- The number of bad coin pairs of the protocol of `rand_simulation_alice` (w.r.t. a target
`f`) is the number of random strings `r : V → ρ` on which `g` disagrees with `f x y`. -/
theorem errCount_simulation_alice [Fintype V] [Fintype ρ]
    (A : Algorithm V (I × ρ) σ B) (T : ℕ) (g : X → (V → σ) → Bool) (f : X → Y → Bool)
    (P : Protocol (X × ({v // F.alice v = true} → ρ)) (Y × ({v // F.alice v = false} → ρ)) Bool)
    (hP : ∀ x y rA rB, P.eval (x, rA) (y, rB) =
        g x (A.run (F.G x y) (fun v => (F.inp x y v, F.combine rA rB v)) T)) (x : X) (y : Y) :
    P.errCount f x y = (univ.filter fun r : V → ρ =>
      g x (A.run (F.G x y) (fun v => (F.inp x y v, r v)) T) ≠ f x y).card := by
  classical
  simp only [errCount]
  rw [← card_map (F.combineEquiv (ρ := ρ)).toEmbedding]
  congr 1
  ext r
  simp only [mem_map_equiv, mem_filter, mem_univ, true_and]
  rw [hP]
  have e : F.combine (F.combineEquiv.symm r).1 (F.combineEquiv.symm r).2 = r :=
    F.combineEquiv.apply_symm_apply r
  rw [e]

end LBFamily

end Cslib.Congest
