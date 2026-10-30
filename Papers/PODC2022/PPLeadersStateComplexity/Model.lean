import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- CSLib candidate (generic Petri-net / labelled-multigraph infrastructure)
/-!
# Configurations, transitions and Petri nets (Sections 2–3 and Lemma 5.2 of Leroux)

Jérôme Leroux, *State Complexity of Protocols With Leaders*, PODC 2022 (arXiv 2109.15171v2).

A `P`-configuration is a vector `ρ ∈ ℕ^P`. A transition `t = (α_t, β_t)` is a pair of
configurations; it rewrites `α_t + ρ` into `β_t + ρ`. A Petri net is a finite set of
transitions. Restrictions `ρ|_Q` to a set of places `Q` are modelled *inside* `ℕ^P`: the
coordinates outside `Q` are set to `0` (`res Q ρ`).

## Main definitions

* `Config P`, `size ρ` (`|ρ|`), `supNorm ρ` (`‖ρ‖∞`).
* `Trans P`, `Trans.Step t α β` (`α →t β`), `Trans.width t` (`|t|`), `Trans.supNorm t`,
  `Trans.delta t` (the displacement `Δ(t) ∈ ℤ^P`).
* `Run σ α β` (`α →σ β` for a word `σ`), `IsWord T σ` (`σ ∈ T*`), `Reach T α β` (`α →T* β`),
  `netNorm T` (`‖T‖∞`).
* `res Q ρ`, `Trans.res Q t`, `resNet Q T` (`ρ|_Q`, `t|_Q`, `T|_Q`).

## Main statements

* `Run.add`: additivity of `→σ`.
* `Run.res`: `α →σ β` implies `α|_Q →σ|_Q β|_Q`.
* `run_lift`, `lemma_5_2`: **Lemma 5.2** (lifting a run of `T|_Q` to `T`).
-/

namespace Podc.PPLeadersStateComplexity

set_option linter.unusedSectionVars false

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- A `P`-configuration: a vector in `ℕ^P`. -/
abbrev Config (P : Type*) := P → ℕ

/-- The number of agents `|ρ| = ∑_p ρ(p)`. -/
def size (ρ : Config P) : ℕ := ∑ p, ρ p

/-- `‖ρ‖∞ = max_p ρ(p)`. -/
def supNorm (ρ : Config P) : ℕ := Finset.univ.sup ρ

theorem le_supNorm (ρ : Config P) (p : P) : ρ p ≤ supNorm ρ :=
  Finset.le_sup (f := ρ) (Finset.mem_univ p)

theorem supNorm_le_iff {ρ : Config P} {m : ℕ} : supNorm ρ ≤ m ↔ ∀ p, ρ p ≤ m := by
  simp [supNorm, Finset.sup_le_iff]

theorem supNorm_le_size (ρ : Config P) : supNorm ρ ≤ size ρ :=
  supNorm_le_iff.2 fun p => Finset.single_le_sum (fun q _ => Nat.zero_le (ρ q))
    (Finset.mem_univ p)

/-- The restriction `ρ|_Q`, seen as a `P`-configuration vanishing outside `Q`. -/
def res (Q : Finset P) (ρ : Config P) : Config P := fun p => if p ∈ Q then ρ p else 0

@[simp] theorem res_apply_of_mem {Q : Finset P} {p : P} (h : p ∈ Q) (ρ : Config P) :
    res Q ρ p = ρ p := by simp [res, h]

@[simp] theorem res_apply_of_not_mem {Q : Finset P} {p : P} (h : p ∉ Q) (ρ : Config P) :
    res Q ρ p = 0 := by simp [res, h]

@[simp] theorem res_add (Q : Finset P) (α β : Config P) : res Q (α + β) = res Q α + res Q β := by
  funext p; by_cases h : p ∈ Q <;> simp [h]

@[simp] theorem res_res (Q Q' : Finset P) (ρ : Config P) :
    res Q (res Q' ρ) = res (Q ∩ Q') ρ := by
  funext p; by_cases h : p ∈ Q <;> by_cases h' : p ∈ Q' <;> simp [h, h']

theorem res_univ (ρ : Config P) : res Finset.univ ρ = ρ := by
  funext p; simp

theorem res_le (Q : Finset P) (ρ : Config P) : res Q ρ ≤ ρ := by
  intro p; by_cases h : p ∈ Q <;> simp [h]

theorem supNorm_res_le (Q : Finset P) (ρ : Config P) : supNorm (res Q ρ) ≤ supNorm ρ :=
  supNorm_le_iff.2 fun p => (res_le Q ρ p).trans (le_supNorm ρ p)

/-- A `P`-transition `t = (α_t, β_t)`. -/
abbrev Trans (P : Type*) := Config P × Config P

namespace Trans

/-- The interaction-width `|t| = max(|α_t|, |β_t|)`. -/
def width (t : Trans P) : ℕ := max (size t.1) (size t.2)

/-- `‖t‖∞ = max(‖α_t‖∞, ‖β_t‖∞)`. -/
def supNorm (t : Trans P) : ℕ := max (Podc.PPLeadersStateComplexity.supNorm t.1)
  (Podc.PPLeadersStateComplexity.supNorm t.2)

/-- `α →t β`: there is `ρ` with `α = α_t + ρ` and `β = β_t + ρ`. -/
def Step (t : Trans P) (α β : Config P) : Prop := ∃ ρ, α = t.1 + ρ ∧ β = t.2 + ρ

/-- The displacement `Δ(t) = β_t − α_t ∈ ℤ^P`. -/
def delta (t : Trans P) : P → ℤ := fun p => (t.2 p : ℤ) - t.1 p

/-- The restriction `t|_Q = (α_t|_Q, β_t|_Q)`. -/
def res (Q : Finset P) (t : Trans P) : Trans P := (Podc.PPLeadersStateComplexity.res Q t.1,
  Podc.PPLeadersStateComplexity.res Q t.2)

theorem supNorm_le_width (t : Trans P) : t.supNorm ≤ t.width :=
  max_le_max (supNorm_le_size _) (supNorm_le_size _)

theorem fst_le_supNorm (t : Trans P) (p : P) : t.1 p ≤ t.supNorm :=
  (le_supNorm _ p).trans (le_max_left _ _)

theorem snd_le_supNorm (t : Trans P) (p : P) : t.2 p ≤ t.supNorm :=
  (le_supNorm _ p).trans (le_max_right _ _)

theorem abs_delta_le (t : Trans P) (p : P) : |t.delta p| ≤ t.supNorm := by
  have h1 := t.fst_le_supNorm p
  have h2 := t.snd_le_supNorm p
  simp only [delta, abs_le]
  constructor <;> omega

theorem step_iff {t : Trans P} {α β : Config P} :
    t.Step α β ↔ t.1 ≤ α ∧ β = α - t.1 + t.2 := by
  constructor
  · rintro ⟨ρ, rfl, rfl⟩
    refine ⟨fun p => Nat.le_add_right _ _, ?_⟩
    funext p; simp only [Pi.add_apply, Pi.sub_apply]; omega
  · rintro ⟨h, rfl⟩
    refine ⟨α - t.1, ?_, ?_⟩
    · funext p; have : t.1 p ≤ α p := h p
      simp only [Pi.add_apply, Pi.sub_apply]; omega
    · funext p; simp only [Pi.add_apply, Pi.sub_apply]; omega

theorem Step.apply_eq {t : Trans P} {α β : Config P} (h : t.Step α β) (p : P) :
    (β p : ℤ) = α p + t.delta p := by
  obtain ⟨ρ, rfl, rfl⟩ := h
  simp only [Pi.add_apply, delta, Nat.cast_add]; ring

theorem Step.add {t : Trans P} {α β : Config P} (h : t.Step α β) (ρ : Config P) :
    t.Step (α + ρ) (β + ρ) := by
  obtain ⟨γ, rfl, rfl⟩ := h
  exact ⟨γ + ρ, by rw [add_assoc], by rw [add_assoc]⟩

theorem Step.res {t : Trans P} {α β : Config P} (h : t.Step α β) (Q : Finset P) :
    (t.res Q).Step (Podc.PPLeadersStateComplexity.res Q α)
      (Podc.PPLeadersStateComplexity.res Q β) := by
  obtain ⟨γ, rfl, rfl⟩ := h
  exact ⟨Podc.PPLeadersStateComplexity.res Q γ, by simp [Trans.res], by simp [Trans.res]⟩

theorem Step.det {t : Trans P} {α β β' : Config P} (h : t.Step α β) (h' : t.Step α β') :
    β = β' := by
  rw [step_iff] at h h'; rw [h.2, h'.2]

end Trans

/-- `α →σ β`: the word `σ` of transitions leads from `α` to `β`. -/
def Run : List (Trans P) → Config P → Config P → Prop
  | [], α, β => α = β
  | t :: σ, α, β => ∃ γ, t.Step α γ ∧ Run σ γ β

/-- `σ ∈ T*`. -/
def IsWord (T : Finset (Trans P)) (σ : List (Trans P)) : Prop := ∀ t ∈ σ, t ∈ T

/-- The reachability relation `α →T* β` of a Petri net `T`. -/
def Reach (T : Finset (Trans P)) (α β : Config P) : Prop := ∃ σ, IsWord T σ ∧ Run σ α β

/-- `‖T‖∞ = max_{t ∈ T} ‖t‖∞`. -/
def netNorm (T : Finset (Trans P)) : ℕ := T.sup Trans.supNorm

/-- The restricted net `T|_Q`. -/
def resNet (Q : Finset P) (T : Finset (Trans P)) : Finset (Trans P) := T.image (Trans.res Q)

/-- The displacement of a word, `Δ(σ) = ∑ Δ(t)`. -/
def wordDelta (σ : List (Trans P)) : P → ℤ := fun p => (σ.map fun t => t.delta p).sum

theorem le_netNorm {T : Finset (Trans P)} {t : Trans P} (h : t ∈ T) : t.supNorm ≤ netNorm T :=
  Finset.le_sup (f := Trans.supNorm) h

@[simp] theorem run_nil {α β : Config P} : Run [] α β ↔ α = β := Iff.rfl

@[simp] theorem run_cons {t : Trans P} {σ : List (Trans P)} {α β : Config P} :
    Run (t :: σ) α β ↔ ∃ γ, t.Step α γ ∧ Run σ γ β := Iff.rfl

theorem run_singleton {t : Trans P} {α β : Config P} : Run [t] α β ↔ t.Step α β := by
  simp

theorem run_append {σ τ : List (Trans P)} {α γ : Config P} :
    Run (σ ++ τ) α γ ↔ ∃ β, Run σ α β ∧ Run τ β γ := by
  induction σ generalizing α with
  | nil => simp
  | cons t σ ih =>
    simp only [List.cons_append, run_cons, ih]
    constructor
    · rintro ⟨δ, h1, β, h2, h3⟩; exact ⟨β, ⟨δ, h1, h2⟩, h3⟩
    · rintro ⟨β, ⟨δ, h1, h2⟩, h3⟩; exact ⟨δ, h1, β, h2, h3⟩

theorem Run.append {σ τ : List (Trans P)} {α β γ : Config P} (h1 : Run σ α β) (h2 : Run τ β γ) :
    Run (σ ++ τ) α γ := run_append.2 ⟨β, h1, h2⟩

theorem Run.det {σ : List (Trans P)} {α β β' : Config P} (h : Run σ α β) (h' : Run σ α β') :
    β = β' := by
  induction σ generalizing α with
  | nil => exact h.symm.trans h'
  | cons t σ ih =>
    obtain ⟨γ, h1, h2⟩ := h
    obtain ⟨γ', h1', h2'⟩ := h'
    rw [h1.det h1'] at h2
    exact ih h2 h2'

theorem Run.add {σ : List (Trans P)} {α β : Config P} (h : Run σ α β) (ρ : Config P) :
    Run σ (α + ρ) (β + ρ) := by
  induction σ generalizing α with
  | nil => exact congrArg (· + ρ) h
  | cons t σ ih =>
    obtain ⟨γ, h1, h2⟩ := h
    exact ⟨γ + ρ, h1.add ρ, ih h2⟩

theorem Run.res {σ : List (Trans P)} {α β : Config P} (h : Run σ α β) (Q : Finset P) :
    Run (σ.map (Trans.res Q)) (Podc.PPLeadersStateComplexity.res Q α)
      (Podc.PPLeadersStateComplexity.res Q β) := by
  induction σ generalizing α with
  | nil => exact congrArg (Podc.PPLeadersStateComplexity.res Q) h
  | cons t σ ih =>
    obtain ⟨γ, h1, h2⟩ := h
    exact ⟨Podc.PPLeadersStateComplexity.res Q γ, h1.res Q, ih h2⟩

/-- The final configuration of a run is given by the displacement of the word. -/
theorem Run.apply_eq {σ : List (Trans P)} {α β : Config P} (h : Run σ α β) (p : P) :
    (β p : ℤ) = α p + wordDelta σ p := by
  induction σ generalizing α with
  | nil => rw [h]; simp [wordDelta]
  | cons t σ ih =>
    obtain ⟨γ, h1, h2⟩ := h
    rw [ih h2, h1.apply_eq]
    simp only [wordDelta, List.map_cons, List.sum_cons]; ring

theorem Run.pow {σ : List (Trans P)} {α δ : Config P} (h : Run σ α (α + δ)) (k : ℕ) :
    Run (List.flatten (List.replicate k σ)) α (α + k • δ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', List.flatten_append, List.flatten_singleton]
    refine ih.append ?_
    have := h.add (k • δ)
    have e : (k + 1) • δ = δ + k • δ := by rw [add_nsmul, one_nsmul, add_comm]
    rwa [add_assoc, ← e] at this

/-- Per-coordinate bound on a run: each step changes a place by at most `M`. -/
theorem Run.le_add {σ : List (Trans P)} {α β : Config P} {M : ℕ} (h : Run σ α β)
    (hM : ∀ t ∈ σ, t.supNorm ≤ M) (p : P) : β p ≤ α p + σ.length * M := by
  have := h.apply_eq p
  have hs : wordDelta σ p ≤ σ.length * M := by
    simp only [wordDelta]
    have : ∀ x ∈ σ.map (fun t => t.delta p), x ≤ (M : ℤ) := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      exact (le_abs_self _).trans ((t.abs_delta_le p).trans (by exact_mod_cast hM t ht))
    have := List.sum_le_length_nsmul _ _ this
    simpa using this
  omega

theorem Run.ge_sub {σ : List (Trans P)} {α β : Config P} {M : ℕ} (h : Run σ α β)
    (hM : ∀ t ∈ σ, t.supNorm ≤ M) (p : P) : α p ≤ β p + σ.length * M := by
  have := h.apply_eq p
  have hs : -(σ.length * M : ℤ) ≤ wordDelta σ p := by
    simp only [wordDelta]
    have : ∀ x ∈ σ.map (fun t => -t.delta p), x ≤ (M : ℤ) := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      exact (neg_le_abs _).trans ((t.abs_delta_le p).trans (by exact_mod_cast hM t ht))
    have := List.sum_le_length_nsmul _ _ this
    simp only [List.length_map, nsmul_eq_mul] at this
    have e : ∀ l : List (Trans P),
        (l.map (fun t => -t.delta p)).sum = -(l.map fun t => t.delta p).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    rw [e] at this
    linarith
  omega

theorem IsWord.append {T : Finset (Trans P)} {σ τ : List (Trans P)} (h1 : IsWord T σ)
    (h2 : IsWord T τ) : IsWord T (σ ++ τ) := by
  intro t ht
  rcases List.mem_append.1 ht with h | h
  exacts [h1 t h, h2 t h]

theorem IsWord.supNorm_le {T : Finset (Trans P)} {σ : List (Trans P)} (h : IsWord T σ) :
    ∀ t ∈ σ, t.supNorm ≤ netNorm T := fun t ht => le_netNorm (h t ht)

theorem IsWord.res {T : Finset (Trans P)} {σ : List (Trans P)} (h : IsWord T σ) (Q : Finset P) :
    IsWord (resNet Q T) (σ.map (Trans.res Q)) := by
  intro t ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
  exact Finset.mem_image_of_mem _ (h t' ht')

/-- Every word of `T|_Q` is the restriction of a word of `T`. -/
theorem IsWord.exists_of_resNet {T : Finset (Trans P)} {Q : Finset P} {σ : List (Trans P)}
    (h : IsWord (resNet Q T) σ) : ∃ σ', IsWord T σ' ∧ σ'.map (Trans.res Q) = σ := by
  induction σ with
  | nil => exact ⟨[], fun _ h => by simp at h, rfl⟩
  | cons t σ ih =>
    obtain ⟨σ', h1, h2⟩ := ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 (h t (List.mem_cons_self ..))
    refine ⟨t' :: σ', fun u hu => ?_, by simp [h2]⟩
    rcases List.mem_cons.1 hu with rfl | hu
    exacts [ht', h1 u hu]

theorem Trans.supNorm_res_le (Q : Finset P) (t : Trans P) : (t.res Q).supNorm ≤ t.supNorm :=
  max_le_max (Podc.PPLeadersStateComplexity.supNorm_res_le Q _)
    (Podc.PPLeadersStateComplexity.supNorm_res_le Q _)

theorem netNorm_resNet_le (Q : Finset P) (T : Finset (Trans P)) :
    netNorm (resNet Q T) ≤ netNorm T := by
  simp only [netNorm, resNet, Finset.sup_le_iff, Finset.mem_image]
  rintro _ ⟨t, ht, rfl⟩
  exact (t.supNorm_res_le Q).trans (le_netNorm ht)

/-! ### Reachability -/

theorem Reach.refl (T : Finset (Trans P)) (α : Config P) : Reach T α α :=
  ⟨[], fun _ h => by simp at h, rfl⟩

theorem Reach.trans {T : Finset (Trans P)} {α β γ : Config P} (h1 : Reach T α β)
    (h2 : Reach T β γ) : Reach T α γ := by
  obtain ⟨σ, hσ, h1⟩ := h1
  obtain ⟨τ, hτ, h2⟩ := h2
  exact ⟨σ ++ τ, hσ.append hτ, h1.append h2⟩

theorem Reach.add {T : Finset (Trans P)} {α β : Config P} (h : Reach T α β) (ρ : Config P) :
    Reach T (α + ρ) (β + ρ) := by
  obtain ⟨σ, hσ, h⟩ := h
  exact ⟨σ, hσ, h.add ρ⟩

theorem Reach.res {T : Finset (Trans P)} {α β : Config P} (h : Reach T α β) (Q : Finset P) :
    Reach (resNet Q T) (Podc.PPLeadersStateComplexity.res Q α)
      (Podc.PPLeadersStateComplexity.res Q β) := by
  obtain ⟨σ, hσ, h⟩ := h
  exact ⟨_, hσ.res Q, h.res Q⟩

/-! ### Components and bottom configurations (Section 6) -/

/-- The `T`-component of `ρ`: the configurations `β` with `ρ →T* β →T* ρ`. -/
def component (T : Finset (Trans P)) (ρ : Config P) : Set (Config P) :=
  {β | Reach T ρ β ∧ Reach T β ρ}

/-- `ρ` is `T`-bottom: its `T`-component is finite and every configuration reachable from `ρ`
can reach `ρ` back. -/
def IsBottom (T : Finset (Trans P)) (ρ : Config P) : Prop :=
  (component T ρ).Finite ∧ ∀ β, Reach T ρ β → Reach T β ρ

/-- The net `T` only acts on the places of `U`. -/
def NetOn (U : Finset P) (T : Finset (Trans P)) : Prop :=
  ∀ t ∈ T, ∀ p ∉ U, t.1 p = 0 ∧ t.2 p = 0

/-! ### Lemma 5.2 -/

/-- **Lemma 5.2**, with a per-place bound: if `σ|_Q` leads from `α|_Q` to `ρ` and every place
`p ∉ Q` holds at least `|σ| · M p` agents, where `M p` bounds what each transition of `σ` consumes
from `p`, then `σ` leads from `α` to some `β` with `β|_Q = ρ` and `β(p) ≥ α(p) − |σ| · M p`. -/
theorem run_lift {σ : List (Trans P)} {Q : Finset P} {α ρ : Config P} {M : P → ℕ}
    (hM : ∀ t ∈ σ, ∀ p ∉ Q, t.1 p ≤ M p)
    (h : Run (σ.map (Trans.res Q)) (res Q α) ρ) (hα : ∀ p ∉ Q, σ.length * M p ≤ α p) :
    ∃ β, Run σ α β ∧ res Q β = ρ ∧ ∀ p ∉ Q, α p ≤ β p + σ.length * M p := by
  induction σ generalizing α with
  | nil => exact ⟨α, rfl, h, fun p _ => by simp⟩
  | cons t σ ih =>
    obtain ⟨γ, h1, h2⟩ := h
    rw [Trans.step_iff] at h1
    have ht : t.1 ≤ α := by
      intro p
      by_cases hp : p ∈ Q
      · have := h1.1 p; simpa [Trans.res, hp] using this
      · have := hα p hp; have := hM t (List.mem_cons_self ..) p hp
        simp only [List.length_cons] at *
        nlinarith
    set α' := α - t.1 + t.2 with hα'
    have hγ : γ = res Q α' := by
      rw [h1.2]; funext p; by_cases hp : p ∈ Q <;> simp [Trans.res, hp, hα']
    rw [hγ] at h2
    obtain ⟨β, hβ1, hβ2, hβ3⟩ := ih (fun t' ht' => hM t' (List.mem_cons_of_mem _ ht')) h2
      (fun p hp => by
        have h3 := hα p hp; have h4 := hM t (List.mem_cons_self ..) p hp
        simp only [List.length_cons, hα', Pi.add_apply, Pi.sub_apply] at *
        have : (σ.length + 1) * M p = σ.length * M p + M p := by ring
        omega)
    refine ⟨β, ⟨α', Trans.step_iff.2 ⟨ht, rfl⟩, hβ1⟩, hβ2, fun p hp => ?_⟩
    have h3 := hβ3 p hp; have h4 := hM t (List.mem_cons_self ..) p hp
    simp only [List.length_cons, hα', Pi.add_apply, Pi.sub_apply] at *
    have : (σ.length + 1) * M p = σ.length * M p + M p := by ring
    omega

/-- **Lemma 5.2.** Let `σ` be a word of transitions of a `P`-Petri net `T` with
`α|_Q →σ|_Q ρ`. If `α(p) ≥ |σ| ‖T‖∞` for every `p ∈ P \ Q`, then `α →σ β` for some `β` with
`β|_Q = ρ` and `β(p) ≥ α(p) − |σ| ‖T‖∞` for every `p ∈ P \ Q`. -/
theorem lemma_5_2 {T : Finset (Trans P)} {σ : List (Trans P)} (hσ : IsWord T σ)
    {Q : Finset P} {α ρ : Config P} (h : Run (σ.map (Trans.res Q)) (res Q α) ρ)
    (hα : ∀ p ∉ Q, σ.length * netNorm T ≤ α p) :
    ∃ β, Run σ α β ∧ res Q β = ρ ∧ ∀ p ∉ Q, α p ≤ β p + σ.length * netNorm T :=
  run_lift (M := fun _ => netNorm T)
    (fun t ht p _ => (t.fst_le_supNorm p).trans (le_netNorm (hσ t ht))) h hα

end Podc.PPLeadersStateComplexity
