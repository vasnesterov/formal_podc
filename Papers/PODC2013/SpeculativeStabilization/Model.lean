import Podc.Computability.Distributed.SelfStabilization.ResetUnison.Sync
import Mathlib

/-!
# Speculatively stabilizing mutual exclusion (Dubois–Guerraoui, PODC 2013): the model

* Mutual exclusion (Specification 1): `MutualExclusion priv ω` for executions
  `ω : ℕ → (V → Q) × Set V` (configuration and activated set at every step): at most one
  privileged process in every configuration, and every process executes its critical section
  (is privileged *and* activated) infinitely often.
* Daemons as execution classes (Definition 1): `unfairExecs` (distributed unfair daemon) and
  `syncExecs` (synchronous daemon), over the configurations satisfying a domain predicate.
* `SSME` (Algorithm 1): the Boulinier–Petit–Villain unison
  (`Cslib.SelfStabilization.ResetUnison`) with `α = n` and `K = (2n - 1)(diam g + 1) + 2`, and
  `privileged_v ≡ r_v = 2n + 2·diam(g)·id_v`.
-/

namespace Podc.SpeculativeStabilization

open Cslib.SelfStabilization Cslib.SelfStabilization.ResetUnison

variable {V Q : Type*}

/-! ### Specification and daemons -/

/-- Specification 1 (mutual exclusion) for an execution `ω t = (configuration, activated set)`:
at most one privileged process in every configuration (safety), and every process is privileged
and activated (executes its critical section) infinitely often (liveness). The predicate
`priv v γ` may depend on the whole configuration (the paper allows the states of `v` and of its
neighbours). -/
def MutualExclusion (priv : V → (V → Q) → Prop) (ω : ℕ → (V → Q) × Set V) : Prop :=
  (∀ t u v, priv u (ω t).1 → priv v (ω t).1 → u = v) ∧
    ∀ v T, ∃ t, T ≤ t ∧ priv v (ω t).1 ∧ v ∈ (ω t).2

/-- Executions under the distributed unfair daemon starting in a configuration of the domain
`dom`. -/
def unfairExecs (next : (V → Q) → V → Q) (dom : (V → Q) → Prop) :
    Set (ℕ → (V → Q) × Set V) :=
  {ω | IsUnfairRun next (fun t => (ω t).1) (fun t => (ω t).2) ∧ dom (ω 0).1}

/-- Executions under the synchronous daemon (every enabled process is activated) starting in a
configuration of the domain `dom`. -/
def syncExecs (next : (V → Q) → V → Q) (dom : (V → Q) → Prop) :
    Set (ℕ → (V → Q) × Set V) :=
  {ω | IsSyncExec next (fun t => (ω t).1) ∧
    (∀ t, (ω t).2 = syncSet (next := next) (fun t => (ω t).1) t) ∧ dom (ω 0).1}

/-- The synchronous daemon is weaker than the unfair one (`sd ≼ ud`). -/
theorem syncExecs_subset {next : (V → Q) → V → Q} {dom : (V → Q) → Prop} :
    syncExecs next dom ⊆ unfairExecs next dom := by
  rintro ω ⟨h, hS, h0⟩
  refine ⟨?_, h0⟩
  have := h.isUnfairRun
  convert this using 1
  funext t; exact hS t

/-! ### The protocol SSME -/

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The clock size `K = (2n - 1)(diam(g) + 1) + 2`. -/
noncomputable def clockSize : ℕ := (2 * Fintype.card V - 1) * (G.diam + 1) + 2

/-- Algorithm 1 (SSME): unison with clock `cherry(n, (2n - 1)(diam(g) + 1) + 2)`. -/
noncomputable def ssme : (V → ℤ) → V → ℤ := next (clockSize G) (Fintype.card V) G

/-- Configurations of SSME: all registers hold values of the clock. -/
def SValid (γ : V → ℤ) : Prop := Valid (clockSize G) (Fintype.card V) γ

/-- The privileged value of `v`: `2n + 2·diam(g)·id_v`. -/
noncomputable def privVal (ident : V → ℕ) (v : V) : ℤ := 2 * Fintype.card V + 2 * G.diam * ident v

/-- `privileged_v ≡ (r_v = 2n + 2·diam(g)·id_v)`. -/
def Privileged (ident : V → ℕ) (v : V) (γ : V → ℤ) : Prop := γ v = privVal G ident v

/-- The legitimate configurations `Γ₁` of the underlying unison. -/
def Gamma1 (γ : V → ℤ) : Prop := Legit (clockSize G) G γ

/-! ### Faithfulness of the clock arithmetic

The unison file writes the clock operations without `%`; they agree with the paper's
definitions on `stab = {0, …, K - 1}`. -/

section Faithful

/-- The paper's cyclic distance `d_K(c, c') = min{(c - c') mod K, (c' - c) mod K}`. -/
def dK (K : ℕ) (c c' : ℤ) : ℤ := min ((c - c') % K) ((c' - c) % K)

theorem emod_of_abs_lt {K : ℕ} {x : ℤ} (h1 : -(K : ℤ) < x) (h2 : x < K) :
    x % K = if 0 ≤ x then x else x + K := by
  split_ifs with h
  · exact Int.emod_eq_of_lt h h2
  · rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)

/-- `φ` on `stab` is `c ↦ (c + 1) mod K`. -/
theorem succK_eq_emod {K : ℕ} {c : ℤ} (h0 : 0 ≤ c) (hc : c < K) : succK K c = (c + 1) % K := by
  unfold succK
  split_ifs with h
  · rw [h, Int.emod_self]
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]

/-- The local order: `c ≤_l c' ↔ 0 ≤ (c' - c) mod K ≤ 1`, on `stab`. -/
theorem locLe_iff {K : ℕ} {c c' : ℤ} (h0 : 0 ≤ c) (hc : c < K) (h0' : 0 ≤ c') (hc' : c' < K) :
    LocLe K c c' ↔ (c' - c) % K ≤ 1 := by
  rw [emod_of_abs_lt (by omega) (by omega)]
  unfold LocLe succK
  split_ifs <;> omega

/-- `correct_v(u)`, as in the paper: both registers in `stab` and `d_K ≤ 1`. -/
theorem correct_iff {K : ℕ} {c c' : ℤ} :
    Correct K c c' ↔ InStab K c ∧ InStab K c' ∧ dK K c c' ≤ 1 := by
  unfold Correct InStab dK
  constructor
  · rintro ⟨⟨h0, hc⟩, ⟨h0', hc'⟩, h⟩
    refine ⟨⟨h0, hc⟩, ⟨h0', hc'⟩, ?_⟩
    rw [emod_of_abs_lt (by omega) (by omega), emod_of_abs_lt (x := c' - c) (by omega) (by omega)]
    unfold succK at h
    split_ifs at * <;> omega
  · rintro ⟨⟨h0, hc⟩, ⟨h0', hc'⟩, h⟩
    refine ⟨⟨h0, hc⟩, ⟨h0', hc'⟩, ?_⟩
    rw [emod_of_abs_lt (by omega) (by omega), emod_of_abs_lt (x := c' - c) (by omega) (by omega)]
      at h
    unfold succK
    split_ifs at * <;> omega

end Faithful

/-! ### Parameters -/

section Params

variable {G}

omit [DecidableRel G.Adj] in
theorem diam_lt_card [Nonempty V] (hconn : G.Connected) : G.diam < Fintype.card V := by
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp, hl⟩ := hconn.exists_path_of_dist u v
  rw [← huv, ← hl]
  exact hp.length_lt

omit [DecidableRel G.Adj] in
theorem one_le_diam [Nontrivial V] (hconn : G.Connected) : 1 ≤ G.diam := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  have hne : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hconn
  have h1 : G.dist u v ≤ G.diam := SimpleGraph.dist_le_diam hne
  have h2 : 0 < G.dist u v := hconn.pos_dist_of_ne huv
  omega

omit [Fintype V] [DecidableRel G.Adj] in
theorem exists_adj [Nontrivial V] (hconn : G.Connected) (v : V) : ∃ u, G.Adj v u := by
  obtain ⟨u, huv⟩ := exists_ne v
  obtain ⟨p⟩ := hconn.preconnected v u
  cases p with
  | nil => exact absurd rfl huv
  | cons h _ => exact ⟨_, h⟩

omit [DecidableRel G.Adj] in
theorem dist_le_diam (hconn : G.Connected) [Nonempty V] (u v : V) : G.dist u v ≤ G.diam :=
  SimpleGraph.dist_le_diam (SimpleGraph.connected_iff_ediam_ne_top.1 hconn)

omit [DecidableRel G.Adj] in
variable (G) in
theorem clockSize_eq [Nonempty V] : (clockSize G : ℤ) =
    2 * G.diam * (Fintype.card V - 1 : ℤ) + 2 * Fintype.card V + G.diam + 1 := by
  unfold clockSize
  have h := Fintype.card_pos (α := V)
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring

omit [DecidableRel G.Adj] in
theorem three_le_clockSize [Nonempty V] : 3 ≤ clockSize G := by
  have := Fintype.card_pos (α := V)
  unfold clockSize
  have : 1 ≤ 2 * Fintype.card V - 1 := by omega
  nlinarith

omit [DecidableRel G.Adj] in
theorem card_lt_clockSize : Fintype.card V < clockSize G := by
  unfold clockSize
  have : 2 * Fintype.card V - 1 ≥ Fintype.card V - 1 := by omega
  have : (2 * Fintype.card V - 1) * (G.diam + 1) ≥ 2 * Fintype.card V - 1 :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

omit [DecidableRel G.Adj] in
/-- Privileged values lie in `[2n, K - diam - 1]`. -/
theorem privVal_bounds [Nonempty V] {ident : V → ℕ} (hid : ∀ v, ident v < Fintype.card V) (v : V) :
    2 * (Fintype.card V : ℤ) ≤ privVal G ident v ∧
      privVal G ident v ≤ clockSize G - G.diam - 1 := by
  rw [clockSize_eq]
  unfold privVal
  have h1 : (ident v : ℤ) ≤ Fintype.card V - 1 := by have := hid v; omega
  have h2 : (0 : ℤ) ≤ 2 * G.diam := by positivity
  constructor
  · have : (0 : ℤ) ≤ 2 * G.diam * ident v := by positivity
    omega
  · have := mul_le_mul_of_nonneg_left h1 h2
    omega

omit [DecidableRel G.Adj] in
/-- Two different privileged values differ by `2·diam·(id_v - id_u)`. -/
theorem privVal_sub {ident : V → ℕ} (u v : V) :
    privVal G ident v - privVal G ident u = 2 * G.diam * ((ident v : ℤ) - ident u) := by
  unfold privVal; ring

end Params

/-! ### Safety in `Γ₁` -/

section Safety

variable {G}

omit [Fintype V] [DecidableRel G.Adj] in
/-- Along a walk of correct edges the registers change by at most the length, modulo `K`. -/
theorem legit_walk {K : ℕ} {γ : V → ℤ} (hL : Legit K G γ) {u v : V} (p : G.Walk u v) :
    ∃ δ : ℤ, |δ| ≤ p.length ∧ (K : ℤ) ∣ γ v - γ u - δ := by
  induction p with
  | nil => exact ⟨0, by simp, by simp⟩
  | @cons a b c hab p ih =>
    obtain ⟨δ, hδ, hd⟩ := ih
    obtain ⟨⟨ha0, haK⟩, ⟨hb0, hbK⟩, h3⟩ := hL a b hab
    have hε : ∃ ε : ℤ, |ε| ≤ 1 ∧ (K : ℤ) ∣ γ b - γ a - ε := by
      unfold succK at h3
      rcases h3 with h | h | h
      · exact ⟨0, by simp, by rw [h]; simp⟩
      · split_ifs at h with hh
        · exact ⟨1, by simp, ⟨-1, by omega⟩⟩
        · exact ⟨1, by simp, ⟨0, by omega⟩⟩
      · split_ifs at h with hh
        · exact ⟨-1, by simp, ⟨1, by omega⟩⟩
        · exact ⟨-1, by simp, ⟨0, by omega⟩⟩
    obtain ⟨ε, hε, he⟩ := hε
    refine ⟨δ + ε, ?_, ?_⟩
    · simp only [SimpleGraph.Walk.length_cons]; push_cast
      exact (abs_add_le _ _).trans (by omega)
    · have := dvd_add hd he
      convert this using 1; ring

omit [DecidableRel G.Adj] in
/-- In `Γ₁`, at most one process is privileged (proof of Theorem 1). -/
theorem legit_safe [Nontrivial V] (hconn : G.Connected) {ident : V → ℕ}
    (hinj : Function.Injective ident) (hid : ∀ v, ident v < Fintype.card V) {γ : V → ℤ}
    (hL : Gamma1 G γ) {u v : V} (hu : Privileged G ident u γ) (hv : Privileged G ident v γ) :
    u = v := by
  by_contra hne
  obtain ⟨p, -, hp⟩ := hconn.exists_path_of_dist u v
  obtain ⟨δ, hδ, hd⟩ := legit_walk hL p
  have hD := dist_le_diam hconn u v
  have hD1 := one_le_diam hconn (G := G)
  rw [hu, hv, privVal_sub, hp] at *
  have hab : (ident u : ℤ) ≠ ident v := by exact_mod_cast hinj.ne hne
  have ha := hid u
  have hb := hid v
  set m : ℤ := (ident v : ℤ) - ident u
  have hm1 : 1 ≤ |m| := Int.one_le_abs (sub_ne_zero.2 hab.symm)
  have hm2 : |m| ≤ Fintype.card V - 1 := abs_sub_le_iff.2 ⟨by omega, by omega⟩
  have hX := Int.eq_zero_of_abs_lt_dvd hd
  have hD0 : (0 : ℤ) ≤ G.diam := by positivity
  have hlo : 2 * (G.diam : ℤ) ≤ |2 * G.diam * m| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 * G.diam)]
    nlinarith
  have hhi : |2 * (G.diam : ℤ) * m| ≤ 2 * G.diam * (Fintype.card V - 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 * G.diam)]
    exact mul_le_mul_of_nonneg_left hm2 (by positivity)
  have hK := clockSize_eq G
  have hδ' : |δ| ≤ G.diam := by omega
  by_cases h0 : 2 * (G.diam : ℤ) * m - δ = 0
  · have : |2 * (G.diam : ℤ) * m| = |δ| := by rw [sub_eq_zero.1 h0]
    omega
  · apply h0; apply hX
    have := abs_sub (2 * (G.diam : ℤ) * m) δ
    omega

end Safety

end Podc.SpeculativeStabilization
