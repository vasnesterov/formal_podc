import Cslib.Computability.Distributed.SelfStabilization.Daemon
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole

-- CSLib candidate: Cslib/Computability/Distributed/SelfStabilization/ResetUnison/Basic.lean

/-!
# The reset-based asynchronous unison of Boulinier, Petit and Villain

The self-stabilizing asynchronous unison protocol of Boulinier, Petit and Villain (*When graph
theory helps self-stabilization*, PODC 2004), in the atomic-state model with the daemons of
`Cslib.SelfStabilization` (`IsUnfairRun`, `IsSyncExec`).

Every process `v` of the communication graph `G` has a register `r_v` holding a value of the
*bounded clock* `cherry(α, K) = {-α, …, 0, …, K - 1}`; values are integers and a configuration is
`γ : V → ℤ`; `Valid α K γ` says that all registers hold clock values. The increment `phi` is
`c ↦ c + 1` on negative values and `c ↦ c + 1 mod K` on `stab = {0, …, K - 1}` (written with
`succK` instead of `%`). The guarded rules are

* `NA :: NormalStep → r_v := φ(r_v)` (all neighbours correct and `r_v` locally minimal),
* `CA :: ConvergeStep → r_v := φ(r_v)` (`r_v ∈ init* = {-α, …, -1}`, all neighbours in
  `init = {-α, …, 0}` and not smaller),
* `RA :: ResetInit → r_v := -α` (some neighbour incorrect and `r_v ∉ init`, i.e. `r_v > 0`).

`Legit` is the set `Γ₁` of legitimate configurations: all registers in `stab` and neighbouring
registers at cyclic distance at most one.

## Main results (this file)

* `correct_succ`: a correct edge stays correct unless one of its endpoints resets;
* `exists_reset_of_allCorrect`: a process loses `AllCorrect` only if a neighbour resets;
* `legit_succ`: `Γ₁` is closed under every step of every daemon;
* `exists_normalStep_of_legit`: if `K > n`, some process is enabled in every legitimate
  configuration (no deadlock), and `not_terminal`: no valid configuration is terminal.

See `ResetUnison/Unfair.lean` (convergence under the unfair daemon for `α ≥ n`, liveness) and
`ResetUnison/Sync.lean` (synchronous convergence within `n + α` steps).
-/

namespace Cslib.SelfStabilization.ResetUnison

open Cslib.SelfStabilization

variable {V : Type*}

section Defs

variable (K : ℕ)

/-- The increment on `stab = {0, …, K - 1}`: `c ↦ c + 1 mod K`. -/
def succK (c : ℤ) : ℤ := if c + 1 = K then 0 else c + 1

/-- The increment `φ` of the bounded clock `cherry(α, K)`. -/
def phi (c : ℤ) : ℤ := if c < 0 then c + 1 else succK K c

/-- The local order `c ≤_l c'`: `c' - c ∈ {0, 1} mod K`. -/
def LocLe (c c' : ℤ) : Prop := c' = c ∨ c' = succK K c

/-- `c ∈ stab = {0, …, K - 1}`. -/
def InStab (c : ℤ) : Prop := 0 ≤ c ∧ c < K

/-- Two registers are *correct* (`correct_v(u)`): both in `stab`, at cyclic distance `≤ 1`. -/
def Correct (c c' : ℤ) : Prop := InStab K c ∧ InStab K c' ∧ (c' = c ∨ c' = succK K c ∨ c = succK K c')

instance (c c' : ℤ) : Decidable (LocLe K c c') := by unfold LocLe; infer_instance
instance (c c' : ℤ) : Decidable (Correct K c c') := by unfold Correct InStab; infer_instance

variable (α : ℕ)

/-- All registers hold values of the clock `cherry(α, K)`. -/
def Valid (γ : V → ℤ) : Prop := ∀ v, -(α : ℤ) ≤ γ v ∧ γ v < K

variable (G : SimpleGraph V)

/-- `allCorrect_v`: `v` is correct with all its neighbours. -/
def AllCorrect (γ : V → ℤ) (v : V) : Prop := ∀ u, G.Adj v u → Correct K (γ v) (γ u)

/-- Guard of rule `NA`. -/
def NormalStep (γ : V → ℤ) (v : V) : Prop :=
  AllCorrect K G γ v ∧ ∀ u, G.Adj v u → LocLe K (γ v) (γ u)

/-- Guard of rule `CA`: `r_v ∈ init*` and every neighbour is in `init` and not smaller. -/
def ConvergeStep (γ : V → ℤ) (v : V) : Prop :=
  (-(α : ℤ) ≤ γ v ∧ γ v < 0) ∧ ∀ u, G.Adj v u → (-(α : ℤ) ≤ γ u ∧ γ u ≤ 0) ∧ γ v ≤ γ u

/-- Guard of rule `RA`: not all neighbours correct and `r_v ∉ init` (for clock values: `r_v > 0`). -/
def ResetInit (γ : V → ℤ) (v : V) : Prop := ¬ AllCorrect K G γ v ∧ 0 < γ v

/-- The set `Γ₁` of legitimate configurations of asynchronous unison. -/
def Legit (γ : V → ℤ) : Prop := ∀ v, AllCorrect K G γ v

section Dec
variable [Fintype V] [DecidableRel G.Adj]
instance (γ : V → ℤ) (v : V) : Decidable (AllCorrect K G γ v) := by
  unfold AllCorrect; infer_instance
instance (γ : V → ℤ) (v : V) : Decidable (NormalStep K G γ v) := by
  unfold NormalStep; infer_instance
instance (γ : V → ℤ) (v : V) : Decidable (ConvergeStep α G γ v) := by
  unfold ConvergeStep; infer_instance
instance (γ : V → ℤ) (v : V) : Decidable (ResetInit K G γ v) := by
  unfold ResetInit; infer_instance
instance (γ : V → ℤ) : Decidable (Legit K G γ) := by unfold Legit; infer_instance
instance (γ : V → ℤ) : Decidable (Valid K α γ) := by unfold Valid; infer_instance
end Dec

/-- The local rule of the protocol (the guards are pairwise exclusive except for isolated
processes, where `NA` and `CA` have the same action). -/
def next [Fintype V] [DecidableRel G.Adj] (γ : V → ℤ) (v : V) : ℤ :=
  if NormalStep K G γ v then phi K (γ v)
  else if ConvergeStep α G γ v then phi K (γ v)
  else if ResetInit K G γ v then -(α : ℤ) else γ v

end Defs

/-! ### Arithmetic of the clock -/

section Arith

variable {K : ℕ}

theorem succK_of_nonneg {c : ℤ} (h0 : 0 ≤ c) (hc : c < K) :
    0 ≤ succK K c ∧ succK K c < K ∧ (succK K c = c + 1 ∨ (c + 1 = K ∧ succK K c = 0)) := by
  unfold succK; split_ifs <;> omega

theorem succK_le {c : ℤ} : succK K c ≤ c + 1 ∨ succK K c = 0 := by
  unfold succK; split_ifs <;> omega

theorem phi_of_neg {c : ℤ} (h : c < 0) : phi K c = c + 1 := by simp [phi, h]

theorem phi_of_nonneg {c : ℤ} (h : 0 ≤ c) : phi K c = succK K c := by
  simp [phi, not_lt.2 h]

theorem succK_ne_self (hK : 2 ≤ K) {c : ℤ} (_h0 : 0 ≤ c) (_hc : c < K) : succK K c ≠ c := by
  unfold succK; split_ifs <;> omega

theorem phi_ne_self (hK : 2 ≤ K) {c : ℤ} (_hc : c < K) : phi K c ≠ c := by
  unfold phi succK; split_ifs <;> omega

theorem Correct.symm {c c' : ℤ} (h : Correct K c c') : Correct K c' c := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h2, h1, by tauto⟩

/-- Iterated increments on `stab`. -/
theorem succK_iterate {z : ℤ} (_h0 : 0 ≤ z) (hz : z < K) {m : ℕ} (hm : m < K) :
    (succK K)^[m] z = if z + m < K then z + m else z + m - K := by
  induction m with
  | zero => simp [hz]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    unfold succK
    push_cast
    split_ifs <;> omega

theorem succK_iterate_ne (_hK : 1 ≤ K) {z : ℤ} (h0 : 0 ≤ z) (hz : z < K) {m : ℕ} (hm0 : 0 < m)
    (hm : m < K) : (succK K)^[m] z ≠ z := by
  rw [succK_iterate h0 hz hm]
  split_ifs <;> omega

theorem succK_iterate_mem {z : ℤ} (h0 : 0 ≤ z) (hz : z < K) (m : ℕ) :
    0 ≤ (succK K)^[m] z ∧ (succK K)^[m] z < K := by
  induction m with
  | zero => exact ⟨h0, hz⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨(succK_of_nonneg ih.1 ih.2).1, (succK_of_nonneg ih.1 ih.2).2.1⟩

/-- The arithmetic core of the closure of `Γ₁`: if two correct registers each either stay or
are incremented while locally minimal w.r.t. the other, they stay correct. -/
theorem correct_of_moves (hK : 3 ≤ K) {a b a' b' : ℤ} (h : Correct K a b)
    (ha : a' = a ∨ (LocLe K a b ∧ a' = succK K a))
    (hb : b' = b ∨ (LocLe K b a ∧ b' = succK K b)) : Correct K a' b' := by
  obtain ⟨⟨ha0, haK⟩, ⟨hb0, hbK⟩, hab⟩ := h
  unfold Correct InStab
  unfold LocLe at ha hb
  unfold succK at *
  rcases ha with rfl | ⟨ha1, rfl⟩ <;> rcases hb with rfl | ⟨hb1, rfl⟩ <;>
    split_ifs at * <;> omega

end Arith

/-! ### Steps of a run -/

section Run

variable {K α : ℕ} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- Rule `RA` is executed by `v` at step `t`. -/
def RA (e : ℕ → V → ℤ) (S : ℕ → Set V) (v : V) (t : ℕ) : Prop :=
  v ∈ S t ∧ ResetInit K G (e t) v

omit [Fintype V] [DecidableRel G.Adj] in
theorem not_normal_of_reset {γ : V → ℤ} {v : V} (h : ResetInit K G γ v) :
    ¬ NormalStep K G γ v := fun hn => h.1 hn.1

omit [Fintype V] [DecidableRel G.Adj] in
theorem not_converge_of_reset {γ : V → ℤ} {v : V} (h : ResetInit K G γ v) :
    ¬ ConvergeStep α G γ v := fun hc => by have := h.2; have := hc.1.2; omega

theorem next_of_reset {γ : V → ℤ} {v : V} (h : ResetInit K G γ v) :
    next K α G γ v = -(α : ℤ) := by
  simp [next, not_normal_of_reset h, not_converge_of_reset (α := α) h, h]

variable {e : ℕ → V → ℤ} {S : ℕ → Set V}

/-- The four possible behaviours of a process during a step. -/
theorem step_cases (h : IsUnfairRun (next K α G) e S) (t : ℕ) (v : V) :
    e (t + 1) v = e t v ∨
    (v ∈ S t ∧ NormalStep K G (e t) v ∧ e (t + 1) v = phi K (e t v)) ∨
    (v ∈ S t ∧ ConvergeStep α G (e t) v ∧ e (t + 1) v = phi K (e t v)) ∨
    (RA (K := K) (G := G) e S v t ∧ e (t + 1) v = -(α : ℤ)) := by
  by_cases hS : v ∈ S t
  · have hm := h.move t v hS
    unfold next at hm
    split_ifs at hm with h1 h2 h3
    · exact Or.inr (Or.inl ⟨hS, h1, hm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hS, h2, hm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨⟨hS, h3⟩, hm⟩))
    · exact Or.inl hm
  · exact Or.inl (h.stay t v hS)

theorem RA.succ (h : IsUnfairRun (next K α G) e S) {v : V} {t : ℕ}
    (hr : RA (K := K) (G := G) e S v t) : e (t + 1) v = -(α : ℤ) := by
  rw [h.move t v hr.1, next_of_reset hr.2]

/-- Validity is preserved by every step. -/
theorem valid_succ (hK : 1 ≤ K) (h : IsUnfairRun (next K α G) e S) {t : ℕ} (hv : Valid K α (e t)) :
    Valid K α (e (t + 1)) := by
  intro v
  have := hv v
  rcases step_cases h t v with h1 | ⟨_, _, h1⟩ | ⟨_, _, h1⟩ | ⟨_, h1⟩ <;> rw [h1]
  · exact this
  all_goals first
    | omega
    | (unfold phi; split_ifs
       · omega
       · have := succK_of_nonneg (K := K) (c := e t v) (by omega) this.2; omega)

theorem valid_run (hK : 1 ≤ K) (h : IsUnfairRun (next K α G) e S) (h0 : Valid K α (e 0)) (t : ℕ) :
    Valid K α (e t) := by
  induction t with
  | zero => exact h0
  | succ t ih => exact valid_succ hK h ih

/-- Registers grow by at most one per step (or wrap / reset to a value `≤ 0`). -/
theorem succ_le (h : IsUnfairRun (next K α G) e S) (t : ℕ) (v : V) :
    e (t + 1) v ≤ e t v + 1 ∨ e (t + 1) v ≤ 0 := by
  rcases step_cases h t v with h1 | ⟨_, _, h1⟩ | ⟨_, _, h1⟩ | ⟨_, h1⟩ <;> rw [h1]
  · omega
  all_goals first
    | omega
    | (unfold phi succK; split_ifs <;> omega)

/-- A process with a negative register stays or executes `CA` (increment by one). -/
theorem neg_cases (h : IsUnfairRun (next K α G) e S) {t : ℕ} {v : V} (hv : e t v < 0) :
    e (t + 1) v = e t v ∨
    (v ∈ S t ∧ e (t + 1) v = e t v + 1 ∧ ∀ u, G.Adj v u → e t u ≤ 0 ∧ e t v ≤ e t u) := by
  rcases step_cases h t v with h1 | ⟨hS, hn, h1⟩ | ⟨hS, hc, h1⟩ | ⟨hr, _⟩
  · exact Or.inl h1
  · refine Or.inr ⟨hS, by rw [h1, phi_of_neg hv], fun u hu => ?_⟩
    have := (hn.1 u hu).1.1; omega
  · exact Or.inr ⟨hS, by rw [h1, phi_of_neg hv], fun u hu => ⟨(hc.2 u hu).1.2, (hc.2 u hu).2⟩⟩
  · have := hr.2.2; omega

/-- A process with a nonnegative register that does not reset stays or executes `NA`. -/
theorem nonneg_cases (h : IsUnfairRun (next K α G) e S) {t : ℕ} {v : V} (hv : 0 ≤ e t v)
    (hr : ¬ RA (K := K) (G := G) e S v t) :
    e (t + 1) v = e t v ∨
    (v ∈ S t ∧ NormalStep K G (e t) v ∧ e (t + 1) v = succK K (e t v)) := by
  rcases step_cases h t v with h1 | ⟨hS, hn, h1⟩ | ⟨hS, hc, h1⟩ | ⟨hr', _⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hS, hn, by rw [h1, phi_of_nonneg hv]⟩
  · have := hc.1.2; omega
  · exact absurd hr' hr

/-- A correct edge stays correct unless one of its endpoints resets. -/
theorem correct_succ (hK : 3 ≤ K) (h : IsUnfairRun (next K α G) e S) {t : ℕ} {v u : V}
    (hadj : G.Adj v u) (hc : Correct K (e t v) (e t u)) (hv : ¬ RA (K := K) (G := G) e S v t)
    (hu : ¬ RA (K := K) (G := G) e S u t) : Correct K (e (t + 1) v) (e (t + 1) u) := by
  apply correct_of_moves hK hc
  · rcases nonneg_cases h hc.1.1 hv with h1 | ⟨_, hn, h1⟩
    · exact Or.inl h1
    · exact Or.inr ⟨hn.2 u hadj, h1⟩
  · rcases nonneg_cases h hc.2.1.1 hu with h1 | ⟨_, hn, h1⟩
    · exact Or.inl h1
    · exact Or.inr ⟨hn.2 v hadj.symm, h1⟩

/-- A process loses `allCorrect` only if some neighbour executes `RA`. -/
theorem exists_reset_of_allCorrect (hK : 3 ≤ K) (h : IsUnfairRun (next K α G) e S) {t : ℕ}
    {v : V} (hv : AllCorrect K G (e t) v) (hv' : ¬ AllCorrect K G (e (t + 1)) v) :
    ∃ u, G.Adj v u ∧ RA (K := K) (G := G) e S u t := by
  simp only [AllCorrect, not_forall] at hv'
  obtain ⟨u, hu, hnc⟩ := hv'
  by_contra hno
  exact hnc (correct_succ hK h hu (hv u hu) (fun hr => hr.2.1 hv) fun hr => hno ⟨u, hu, hr⟩)

/-- `Γ₁` is closed. -/
theorem legit_succ (hK : 3 ≤ K) (h : IsUnfairRun (next K α G) e S) {t : ℕ}
    (hL : Legit K G (e t)) : Legit K G (e (t + 1)) := by
  intro v
  by_contra hv
  obtain ⟨u, -, hr⟩ := exists_reset_of_allCorrect hK h (hL v) hv
  exact hr.2.1 (hL u)

theorem legit_run (hK : 3 ≤ K) (h : IsUnfairRun (next K α G) e S) {t : ℕ}
    (hL : Legit K G (e t)) : ∀ s, t ≤ s → Legit K G (e s) := by
  intro s hs
  induction hs with
  | refl => exact hL
  | step _ ih => exact legit_succ hK h ih

end Run

/-! ### No deadlock -/

section Deadlock

variable {K α : ℕ} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- If `K > n`, every legitimate configuration has a process enabled by `NA`. -/
theorem exists_normalStep_of_legit [Nonempty V] (hcard : Fintype.card V < K) {γ : V → ℤ}
    (hval : Valid K α γ) (hL : Legit K G γ) : ∃ v, NormalStep K G γ v := by
  by_contra hno
  push Not at hno
  have hp : ∀ v, ∃ u, G.Adj v u ∧ succK K (γ u) = γ v := by
    intro v
    have := hno v
    simp only [NormalStep, not_and, not_forall] at this
    obtain ⟨u, hu, hl⟩ := this (hL v)
    refine ⟨u, hu, ?_⟩
    obtain ⟨_, _, h3⟩ := hL v u hu
    unfold LocLe at hl
    tauto
  choose p hpadj hp using hp
  obtain ⟨v0⟩ := ‹Nonempty V›
  have hit : ∀ k, (succK K)^[k] (γ (p^[k] v0)) = γ v0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply' p, Function.iterate_succ_apply, hp]
      exact ih
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (Fintype.card V + 1) => p^[k] v0) (by simp)
  -- reduce to `i < j`
  have key : ∀ a b : ℕ, a < b → b ≤ Fintype.card V → p^[a] v0 = p^[b] v0 → False := by
    intro a b hab hb hpab
    have ha := hit a
    have hb' := hit b
    set y := γ (p^[b] v0)
    have hy0 : 0 ≤ y ∧ y < K := ⟨(hL _ _ (hpadj _)).1.1, (hval _).2⟩
    rw [hpab] at ha
    have hz := succK_iterate_mem (K := K) hy0.1 hy0.2 a
    have : (succK K)^[b - a] ((succK K)^[a] y) = (succK K)^[a] y := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le]
      exact hb'.trans ha.symm
    exact succK_iterate_ne (by omega) hz.1 hz.2 (by omega) (by omega) this
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact key i j h (by omega) hfij
  · exact key j i h (by omega) hfij.symm

/-- Outside `Γ₁`, some process is enabled. -/
theorem exists_enabled_of_not_legit {γ : V → ℤ} (hval : Valid K α γ) (hL : ¬ Legit K G γ) :
    ∃ v, next K α G γ v ≠ γ v := by
  classical
  by_cases hA : ∃ w, ResetInit K G γ w
  · obtain ⟨w, hw⟩ := hA
    refine ⟨w, ?_⟩
    rw [next_of_reset hw]; have := hw.2; omega
  push Not at hA
  by_cases hneg : ∃ w, γ w < 0
  · -- a minimal negative register executes `CA`
    obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun w => γ w < 0) γ
      (by obtain ⟨w, hw⟩ := hneg; exact ⟨w, by simp [hw]⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hmin
    have hc : ConvergeStep α G γ w := by
      refine ⟨⟨(hval w).1, hw⟩, fun u hu => ?_⟩
      have hu0 : γ u ≤ 0 := by
        by_contra hpos
        push Not at hpos
        apply hA u ⟨fun hac => ?_, hpos⟩
        have := (hac w hu.symm).2.1.1; omega
      refine ⟨⟨(hval u).1, hu0⟩, ?_⟩
      rcases lt_or_eq_of_le hu0 with h | h
      · exact hmin u h
      · omega
    refine ⟨w, ?_⟩
    unfold next
    split_ifs <;> (rw [phi_of_neg hw]; omega)
  · push Not at hneg
    exfalso
    apply hL
    intro v u hu
    by_contra hnc
    have hv0 := hneg v
    have hu0 := hneg u
    -- neither endpoint can be positive and incorrect, so both are zero
    have hv : γ v = 0 := by
      by_contra hne
      exact hA v ⟨fun hac => hnc (hac u hu), by omega⟩
    have hu : γ u = 0 := by
      by_contra hne
      exact hA u ⟨fun hac => hnc (hac v hu.symm).symm, by omega⟩
    apply hnc
    refine ⟨⟨hv0, (hval v).2⟩, ⟨hu0, (hval u).2⟩, Or.inl (by rw [hv, hu])⟩

/-- No valid configuration is terminal (for `K > n` and at least one process). -/
theorem not_terminal [Nonempty V] (hcard : Fintype.card V < K) {γ : V → ℤ}
    (hval : Valid K α γ) : ¬ Terminal (next K α G) γ := by
  intro ht
  by_cases hL : Legit K G γ
  · obtain ⟨v, hv⟩ := exists_normalStep_of_legit (α := α) hcard hval hL
    have := ht v
    simp only [next, hv, ite_true] at this
    have hpos := Fintype.card_pos (α := V)
    exact phi_ne_self (by omega) (hval v).2 this
  · obtain ⟨v, hv⟩ := exists_enabled_of_not_legit hval hL
    exact hv (ht v)

end Deadlock

end Cslib.SelfStabilization.ResetUnison
