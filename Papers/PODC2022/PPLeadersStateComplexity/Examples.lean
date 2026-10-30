import Papers.PODC2022.PPLeadersStateComplexity.Protocol
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Abel

/-!
# Examples 4.1 and 4.2 of Leroux

* **Example 4.1.** A leaderless conservative protocol with `2` states stably computing
  `(i ≥ n)`; its interaction-width is exactly `n`.
* **Example 4.2.** A conservative Petri-net protocol with `6` states, `n` leaders and
  interaction-width `≤ 2` stably computing `(i ≥ n)`.

Together they show that the state complexity of counting predicates is trivial unless both the
interaction-width and the number of leaders are taken into account.
-/

namespace Podc.PPLeadersStateComplexity

set_option linter.unusedSectionVars false

/-! ## Example 4.1 -/

namespace Ex41

/-- The states `P = {i, p}` of Example 4.1. -/
inductive S
  | i
  | p
  deriving DecidableEq

instance : Fintype S := ⟨{.i, .p}, by intro x; cases x <;> simp⟩

theorem card_S : Fintype.card S = 2 := rfl

/-- The unit configuration `s` (one agent in state `s`). -/
abbrev e (s : S) : Config S := Pi.single s 1

theorem size_eq (α : Config S) : size α = α .i + α .p := by
  have : (Finset.univ : Finset S) = {S.i, S.p} := rfl
  simp [size, this]

theorem eq_iff {α β : Config S} : α = β ↔ α .i = β .i ∧ α .p = β .p := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; funext s; cases s <;> assumption

/-- The relation of Example 4.1: `α →* β` iff `β + m.i = α + m.p` for some `m` with
`m = 0 ∨ |α| ≥ n`. -/
def R (n : ℕ) (α β : Config S) : Prop :=
  ∃ m : ℕ, β + m • e .i = α + m • e .p ∧ (m = 0 ∨ n ≤ size α)

theorem R_iff {n : ℕ} {α β : Config S} :
    R n α β ↔ ∃ m : ℕ, β .i + m = α .i ∧ β .p = α .p + m ∧ (m = 0 ∨ n ≤ α .i + α .p) := by
  simp only [R, eq_iff, size_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp [and_assoc]

/-- The protocol of Example 4.1 (leaderless, `I = {i}`, `γ(i) = 0`, `γ(p) = 1`). -/
def protocol (n : ℕ) : Protocol S where
  R := R n
  refl α := R_iff.2 ⟨0, by simp⟩
  trans α β γ h1 h2 := by
    obtain ⟨m1, a1, b1, c1⟩ := R_iff.1 h1
    obtain ⟨m2, a2, b2, c2⟩ := R_iff.1 h2
    refine R_iff.2 ⟨m1 + m2, by omega, by omega, ?_⟩
    rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2 <;> omega
  add α β ρ h := by
    obtain ⟨m, a, b, c⟩ := R_iff.1 h
    refine R_iff.2 ⟨m, ?_, ?_, ?_⟩ <;> simp only [Pi.add_apply] <;> omega
  leaders := 0
  I := {.i}
  γ := fun s => match s with
    | .i => .zero
    | .p => .one

theorem protocol_leaders (n : ℕ) : (protocol n).numLeaders = 0 := by
  simp [Protocol.numLeaders, protocol, size]

/-- Example 4.1: the protocol is conservative. -/
theorem conservative (n : ℕ) : (protocol n).Conservative := by
  intro α β h
  obtain ⟨m, a, b, -⟩ := R_iff.1 h
  rw [size_eq, size_eq]; omega

/-- **Example 4.1.** The leaderless 2-state protocol stably computes `(i ≥ n)` for `n ≥ 1`. -/
theorem stablyComputesGe {n : ℕ} (hn : 1 ≤ n) : (protocol n).StablyComputesGe .i n := by
  refine ⟨rfl, ?_⟩
  intro ρ hρ α hα
  have hρp : ρ .p = 0 := hρ .p (by simp [protocol])
  obtain ⟨m, a, b, c⟩ := R_iff.1 hα
  simp only [protocol, zero_add] at a b c
  by_cases hk : n ≤ ρ .i
  · -- `α →* ρ(i).p`, which is `1`-output stable
    refine ⟨fun s => match s with | .i => 0 | .p => ρ .i, R_iff.2 ⟨α .i, ?_, ?_, ?_⟩, ?_⟩
    · simp
    · simp; omega
    · right; omega
    · simp only [Protocol.stable, countingPred, decide_eq_true hk, ite_true]
      intro β hβ
      obtain ⟨m', a', b', -⟩ := R_iff.1 hβ
      simp only at a' b'
      have hm' : m' = 0 := by omega
      ext j
      simp only [Protocol.outputs, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨s, hs, rfl⟩
        cases s
        · omega
        · rfl
      · rintro rfl; exact ⟨.p, by omega, rfl⟩
  · -- `α = ρ` is `0`-output stable
    have hm : m = 0 := by rcases c with c | c <;> omega
    subst hm
    refine ⟨α, (protocol n).refl α, ?_⟩
    simp only [Protocol.stable, countingPred, decide_eq_false hk, Bool.false_eq_true, ite_false]
    intro β hβ
    obtain ⟨m', a', b', c'⟩ := R_iff.1 hβ
    have hm' : m' = 0 := by rcases c' with c' | c' <;> omega
    rintro j ⟨s, hs, rfl⟩
    cases s
    · rfl
    · simp at b a hs; omega

/-- A transition of `R n` of width `< n` does nothing. -/
theorem trans_eq_of_width_lt {n : ℕ} {t : Trans S} (ht : R n t.1 t.2) (hw : t.width < n) :
    t.1 = t.2 := by
  obtain ⟨m, a, b, c⟩ := R_iff.1 ht
  have : size t.1 ≤ t.width := le_max_left _ _
  rw [size_eq] at this
  rw [eq_iff]; constructor <;> rcases c with c | c <;> omega

/-- **Example 4.1** (lower bound on the width): for `m < n`, `R n` does not have
interaction-width `≤ m`. -/
theorem not_hasWidthLE {n m : ℕ} (hm : m < n) : ¬ HasWidthLE (R n) m := by
  intro h
  obtain ⟨σ, hσ, hrun⟩ := h (fun s => match s with | .i => n | .p => 0)
    (fun s => match s with | .i => n - 1 | .p => 1) (R_iff.2 ⟨1, by simp; omega, by simp, by simp⟩)
  have key : ∀ (σ : List (Trans S)), (∀ t ∈ σ, R n t.1 t.2 ∧ t.width ≤ m) →
      ∀ α β, Run σ α β → α = β := by
    intro σ hσ
    induction σ with
    | nil => intro α β h; exact h
    | cons t σ ih =>
      rintro α β ⟨γ, ⟨ρ, rfl, rfl⟩, h2⟩
      have := trans_eq_of_width_lt (hσ t (List.mem_cons_self ..)).1
        (by have := (hσ t (List.mem_cons_self ..)).2; omega)
      rw [this]
      exact ih (fun t' ht' => hσ t' (List.mem_cons_of_mem _ ht')) _ _ h2
  have := congrFun (key σ hσ _ _ hrun) .p
  simp at this

/-- One step of width `n` moving an agent from `i` to `p` in a configuration of size `≥ n`. -/
theorem exists_step {n : ℕ} (hn : 1 ≤ n) {α : Config S} (hi : 1 ≤ α .i)
    (hs : n ≤ α .i + α .p) :
    ∃ t : Trans S, (R n t.1 t.2 ∧ t.width ≤ n) ∧
      t.Step α (fun s => match s with | .i => α .i - 1 | .p => α .p + 1) := by
  -- `t = (ρ + i, ρ + p)` with `|ρ| = n - 1`, `ρ ≤ α - i`
  set a := min (α .i - 1) (n - 1)
  set b := n - 1 - a
  refine ⟨(fun s => match s with | .i => a + 1 | .p => b,
    fun s => match s with | .i => a | .p => b + 1), ⟨R_iff.2 ⟨1, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · simp
  · simp
  · right; simp only; omega
  · simp only [Trans.width, size_eq]; omega
  · refine ⟨fun s => match s with | .i => α .i - 1 - a | .p => α .p - b, ?_, ?_⟩ <;>
      rw [eq_iff] <;> simp only [Pi.add_apply] <;> omega

/-- **Example 4.1** (upper bound on the width): `R n` has interaction-width `≤ n`. -/
theorem hasWidthLE {n : ℕ} (hn : 1 ≤ n) : HasWidthLE (R n) n := by
  intro α β h
  obtain ⟨m, a, b, c⟩ := R_iff.1 h
  clear h
  induction m generalizing α with
  | zero => exact ⟨[], fun _ h => by simp at h, (eq_iff.2 ⟨by omega, by omega⟩).symm⟩
  | succ m ih =>
    have hs : n ≤ α .i + α .p := by rcases c with c | c <;> omega
    obtain ⟨t, ht, hstep⟩ := exists_step hn (α := α) (by omega) hs
    obtain ⟨σ, hσ, hrun⟩ := ih (α := fun s => match s with | .i => α .i - 1 | .p => α .p + 1)
      (by simp only; omega) (by simp only; omega) (by right; simp only; omega)
    exact ⟨t :: σ, fun t' ht' => by
      rcases List.mem_cons.1 ht' with rfl | ht'
      exacts [ht, hσ t' ht'], ⟨_, hstep, hrun⟩⟩

/-- **Example 4.1.** The interaction-width of the protocol is exactly `n` (for `n ≥ 1`). -/
theorem width_eq {n : ℕ} (hn : 1 ≤ n) : width (protocol n).R = n := by
  refine le_antisymm (width_le_of_hasWidthLE (hasWidthLE hn)) (le_iInf₂ fun m hm => ?_)
  by_contra h
  exact not_hasWidthLE (by exact_mod_cast not_le.1 h) hm

end Ex41

/-! ## Example 4.2 -/

section Firing

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Firing `k` times a transition `t = (c + x, c + y)` (with catalyst `c`). -/
theorem reach_fire_pow {T : Finset (Trans P)} {t : Trans P} (ht : t ∈ T) {c x y : Config P}
    (h1 : t.1 = c + x) (h2 : t.2 = c + y) (k : ℕ) (ρ : Config P) :
    Reach T (c + k • x + ρ) (c + k • y + ρ) := by
  induction k generalizing ρ with
  | zero => simpa using Reach.refl T (c + ρ)
  | succ k ih =>
    have hstep : Reach T (c + (k + 1) • x + ρ) (c + k • x + (y + ρ)) := by
      refine ⟨[t], fun u hu => by simp at hu; exact hu ▸ ht, run_singleton.2
        ⟨k • x + ρ, ?_, ?_⟩⟩
      · rw [h1, succ_nsmul]; abel
      · rw [h2]; abel
    refine hstep.trans ?_
    have := ih (y + ρ)
    rwa [show c + k • y + (y + ρ) = c + (k + 1) • y + ρ by rw [succ_nsmul]; abel] at this

/-- Firing `k` times a transition `t = (c + x, c + y)` from `α ≥ c + k.x`. -/
theorem reach_fire {T : Finset (Trans P)} {t : Trans P} (ht : t ∈ T) {c x y : Config P}
    (h1 : t.1 = c + x) (h2 : t.2 = c + y) (k : ℕ) {α : Config P} (hα : c + k • x ≤ α) :
    Reach T α (α - k • x + k • y) := by
  have := reach_fire_pow ht h1 h2 k (α - c - k • x)
  convert this using 1 <;> funext s <;> have := hα s <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢ <;>
    generalize k * x s = a at * <;> omega

/-- A property preserved by every transition of `T` is preserved by `T`-reachability. -/
theorem Reach.invariant {T : Finset (Trans P)} (I : Config P → Prop)
    (hI : ∀ t ∈ T, ∀ ρ, I (t.1 + ρ) → I (t.2 + ρ)) {α β : Config P} (h : Reach T α β)
    (hα : I α) : I β := by
  obtain ⟨σ, hσ, hrun⟩ := h
  induction σ generalizing α with
  | nil => exact hrun ▸ hα
  | cons t σ ih =>
    obtain ⟨γ, ⟨ρ, rfl, rfl⟩, h2⟩ := hrun
    exact ih (hI t (hσ t (List.mem_cons_self ..)) ρ hα)
      (fun u hu => hσ u (List.mem_cons_of_mem _ hu)) h2

end Firing

namespace Ex42

/-- The states `P = {i, ī, p, p̄, q, q̄}` of Example 4.2. -/
inductive S
  | i
  | ib
  | p
  | pb
  | q
  | qb
  deriving DecidableEq

instance : Fintype S := ⟨{.i, .ib, .p, .pb, .q, .qb}, by intro x; cases x <;> simp⟩

theorem card_S : Fintype.card S = 6 := rfl

/-- The unit configuration `s` (one agent in state `s`). -/
abbrev e (s : S) : Config S := Pi.single s 1

theorem size_eq (α : Config S) : size α = α .i + α .ib + α .p + α .pb + α .q + α .qb := by
  have : (Finset.univ : Finset S) = {.i, .ib, .p, .pb, .q, .qb} := rfl
  simp [size, this]; ring

/-- `t = (i + ī, p + q)`. -/
def t : Trans S := (e .i + e .ib, e .p + e .q)
/-- `t_p = (p̄ + i, p + i)`. -/
def tp : Trans S := (e .pb + e .i, e .p + e .i)
/-- `t_q = (q̄ + i, q + i)`. -/
def tq : Trans S := (e .qb + e .i, e .q + e .i)
/-- `t̄_p = (p + ī, p̄ + ī)`. -/
def tbp : Trans S := (e .p + e .ib, e .pb + e .ib)
/-- `t̄_q = (q + ī, q̄ + ī)`. -/
def tbq : Trans S := (e .q + e .ib, e .qb + e .ib)
/-- `t_q̄ = (p + q̄, p + q)`. -/
def tqb : Trans S := (e .p + e .qb, e .p + e .q)
/-- `t_p̄ = (q + p̄, q + p)`. -/
def tpb : Trans S := (e .q + e .pb, e .q + e .p)

/-- The Petri net `T = {t, t_p, t̄_p, t_q, t̄_q, t_p̄, t_q̄}` of Example 4.2. -/
def T : Finset (Trans S) := {t, tp, tbp, tq, tbq, tpb, tqb}

/-- The output function: `γ⁻¹(1) = {i, p, q}`, `γ⁻¹(0) = {ī, p̄, q̄}`. -/
def γ : S → Out
  | .i => .one
  | .p => .one
  | .q => .one
  | .ib => .zero
  | .pb => .zero
  | .qb => .zero

/-- The protocol of Example 4.2: `(P, →T*, n.ī, {i}, γ)`. -/
def protocol (n : ℕ) : Protocol S := Protocol.ofNet T (n • e .ib) {.i} γ

theorem protocol_numLeaders (n : ℕ) : (protocol n).numLeaders = n := by
  simp [Protocol.numLeaders, protocol, Protocol.ofNet, size_eq]

/-- Every transition of `T`, applied to `t.1 + ρ`, in a pointwise form. -/
theorem forall_mem_T {I : Config S → Prop}
    (h : ∀ ρ : Config S, (I (e .i + e .ib + ρ) → I (e .p + e .q + ρ)) ∧
      (I (e .pb + e .i + ρ) → I (e .p + e .i + ρ)) ∧
      (I (e .qb + e .i + ρ) → I (e .q + e .i + ρ)) ∧
      (I (e .p + e .ib + ρ) → I (e .pb + e .ib + ρ)) ∧
      (I (e .q + e .ib + ρ) → I (e .qb + e .ib + ρ)) ∧
      (I (e .p + e .qb + ρ) → I (e .p + e .q + ρ)) ∧
      (I (e .q + e .pb + ρ) → I (e .q + e .p + ρ))) :
    ∀ u ∈ T, ∀ ρ, I (u.1 + ρ) → I (u.2 + ρ) := by
  intro u hu ρ
  simp only [T, Finset.mem_insert, Finset.mem_singleton] at hu
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h ρ
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h1, h2, h4, h3, h5, h7, h6]

/-- **Example 4.2.** The protocol is conservative. -/
theorem conservative (n : ℕ) : (protocol n).Conservative := by
  intro α β h
  refine Reach.invariant (fun β => size α = size β) (forall_mem_T (I := fun β => size α = size β) fun ρ => ?_) h rfl
  simp only [size_eq, Pi.add_apply, Pi.single_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp at h ⊢ <;> omega

/-- **Example 4.2.** The protocol has interaction-width at most `2`. -/
theorem hasWidthLE (n : ℕ) : HasWidthLE (protocol n).R 2 := by
  have h := hasWidthLE_reach T
  have hT : T.sup Trans.width ≤ 2 := by
    simp only [Finset.sup_le_iff, T, Finset.mem_insert, Finset.mem_singleton]
    rintro u (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [Trans.width, size_eq, t, tp, tq, tbp, tbq, tpb, tqb]
  intro α β hαβ
  obtain ⟨σ, hσ, hrun⟩ := h α β hαβ
  exact ⟨σ, fun u hu => ⟨(hσ u hu).1, (hσ u hu).2.trans hT⟩, hrun⟩

/-! ### Stable computation -/

/-- The run invariant of Example 4.2: `α(i) − α(ī) = ρ(i) − n` (with `k = ρ(i)`), and if
`α(i) = α(ī) = 0` then `α(p) > 0` and `α(q) > 0` (the last `t` fired produced a `p` and a `q`,
and no transition enabled when `α(i) = α(ī) = 0` consumes `p` or `q`). -/
def Inv (n k : ℕ) (α : Config S) : Prop :=
  α .i + n = α .ib + k ∧ (α .i = 0 → α .ib = 0 → 0 < α .p ∧ 0 < α .q)

/-- Configurations with no agent in `i`, `p`, `q` (they are dead and `0`-output). -/
def Z (α : Config S) : Prop := α .i = 0 ∧ α .p = 0 ∧ α .q = 0

/-- Nonzero configurations with no agent in `ī`, `p̄`, `q̄` (they are dead and `1`-output). -/
def O (α : Config S) : Prop := α .ib = 0 ∧ α .pb = 0 ∧ α .qb = 0 ∧ 0 < α .i + α .p + α .q

theorem Inv.reach {n k : ℕ} {α β : Config S} (h : Reach T α β) (hα : Inv n k α) : Inv n k β := by
  refine Reach.invariant (Inv n k) (forall_mem_T (I := Inv n k) fun ρ => ?_) h hα
  simp only [Inv, Pi.add_apply, Pi.single_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp at h ⊢ <;> omega

theorem Z.reach {α β : Config S} (h : Reach T α β) (hα : Z α) : Z β := by
  refine Reach.invariant Z (forall_mem_T (I := Z) fun ρ => ?_) h hα
  simp only [Z, Pi.add_apply, Pi.single_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp at h ⊢

theorem O.reach {α β : Config S} (h : Reach T α β) (hα : O α) : O β := by
  refine Reach.invariant O (forall_mem_T (I := O) fun ρ => ?_) h hα
  simp only [O, Pi.add_apply, Pi.single_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp at h ⊢

theorem Z.mem_S0 {n : ℕ} {α : Config S} (hα : Z α) : α ∈ (protocol n).S0 := by
  intro β hβ
  have hZ := hα.reach hβ
  rintro j ⟨s, hs, rfl⟩
  obtain ⟨h1, h2, h3⟩ := hZ
  cases s <;> simp_all [protocol, Protocol.ofNet, γ]

theorem O.mem_S1 {n : ℕ} {α : Config S} (hα : O α) : α ∈ (protocol n).S1 := by
  intro β hβ
  obtain ⟨h1, h2, h3, h4⟩ := hα.reach hβ
  ext j
  simp only [Protocol.outputs, Set.mem_ofPred_eq, Set.mem_singleton_iff, protocol,
    Protocol.ofNet]
  constructor
  · rintro ⟨s, hs, rfl⟩
    cases s <;> simp_all [γ]
  · rintro rfl
    by_cases hi : 0 < β .i
    · exact ⟨.i, hi, rfl⟩
    by_cases hp : 0 < β .p
    · exact ⟨.p, hp, rfl⟩
    exact ⟨.q, by omega, rfl⟩

/-- From a configuration satisfying the invariant with `α(i) = 0 ∨ α(ī) = 0`, a
`φ_{i ≥ n}(ρ)`-output stable configuration is reachable. -/
theorem finish {n k : ℕ} {α : Config S} (hα : Inv n k α) (h0 : α .i = 0 ∨ α .ib = 0) :
    ∃ β, Reach T α β ∧ β ∈ (protocol n).stable (countingPred .i n (k • e .i)) := by
  obtain ⟨hinv, hpq⟩ := hα
  have hk : (k • e .i) .i = k := by simp
  simp only [countingPred, hk, Protocol.stable]
  rcases Nat.eq_zero_or_pos (α .ib) with hib | hib
  · -- `α(ī) = 0`: `φ(ρ) = 1`
    have hnk : n ≤ k := by omega
    simp only [decide_eq_true hnk, ite_true]
    rcases Nat.eq_zero_or_pos (α .i) with hi | hi
    · -- `α(i) = α(ī) = 0`: use `t_p̄`, `t_q̄`
      obtain ⟨hp, hq⟩ := hpq hi hib
      have r1 := reach_fire (T := T) (t := tpb) (by simp [T]) (c := e .q) (x := e .pb) (y := e .p)
        rfl rfl (α .pb) (α := α) (by intro s; cases s <;> simp; all_goals omega)
      set α₁ := α - α .pb • e .pb + α .pb • e .p with hα₁
      have r2 := reach_fire (T := T) (t := tqb) (by simp [T]) (c := e .p) (x := e .qb) (y := e .q)
        rfl rfl (α₁ .qb) (α := α₁) (by intro s; cases s <;> simp [hα₁]; all_goals omega)
      refine ⟨_, r1.trans r2, O.mem_S1 ?_⟩
      simp [O, hα₁]; omega
    · -- `α(i) > 0`: use `t_p`, `t_q`
      have r1 := reach_fire (T := T) (t := tp) (by simp [T]) (c := e .i) (x := e .pb) (y := e .p)
        (add_comm _ _) (add_comm _ _) (α .pb) (α := α) (by intro s; cases s <;> simp; all_goals omega)
      set α₁ := α - α .pb • e .pb + α .pb • e .p with hα₁
      have r2 := reach_fire (T := T) (t := tq) (by simp [T]) (c := e .i) (x := e .qb) (y := e .q)
        (add_comm _ _) (add_comm _ _) (α₁ .qb) (α := α₁)
        (by intro s; cases s <;> simp [hα₁]; all_goals omega)
      refine ⟨_, r1.trans r2, O.mem_S1 ?_⟩
      simp [O, hα₁]; omega
  · -- `α(ī) > 0`: `φ(ρ) = 0`; use `t̄_p`, `t̄_q`
    have hnk : ¬ n ≤ k := by omega
    simp only [decide_eq_false hnk, Bool.false_eq_true, ite_false]
    have r1 := reach_fire (T := T) (t := tbp) (by simp [T]) (c := e .ib) (x := e .p) (y := e .pb)
      (add_comm _ _) (add_comm _ _) (α .p) (α := α) (by intro s; cases s <;> simp; all_goals omega)
    set α₁ := α - α .p • e .p + α .p • e .pb with hα₁
    have r2 := reach_fire (T := T) (t := tbq) (by simp [T]) (c := e .ib) (x := e .q) (y := e .qb)
      (add_comm _ _) (add_comm _ _) (α₁ .q) (α := α₁)
      (by intro s; cases s <;> simp [hα₁]; all_goals omega)
    refine ⟨_, r1.trans r2, Z.mem_S0 ?_⟩
    simp [Z, hα₁]; omega

/-- **Example 4.2.** For `n ≥ 1`, the 6-state protocol with `n` leaders stably computes
`(i ≥ n)`. -/
theorem stablyComputesGe {n : ℕ} (hn : 1 ≤ n) : (protocol n).StablyComputesGe .i n := by
  refine ⟨rfl, ?_⟩
  intro ρ hρ α hα
  have hρ' : ρ = ρ .i • e .i := by
    funext s
    cases s <;> simp <;> exact hρ _ (by simp [protocol, Protocol.ofNet])
  set k := ρ .i
  rw [hρ'] at hα ⊢
  have h0 : Inv n k (n • e .ib + k • e .i) := by
    simp only [Inv]; simp; omega
  have hα' : Inv n k α := h0.reach hα
  -- fire `t` `min(α(i), α(ī))` times
  set m := min (α .i) (α .ib)
  have r := reach_fire (T := T) (t := t) (by simp [T]) (c := 0) (x := e .i + e .ib)
    (y := e .p + e .q) (zero_add _).symm (zero_add _).symm m (α := α)
    (by intro s; cases s <;> simp [m])
  obtain ⟨β, hβ, hst⟩ := finish (hα'.reach r) (by simp [m]; omega)
  exact ⟨β, r.trans hβ, hst⟩

end Ex42

end Podc.PPLeadersStateComplexity
