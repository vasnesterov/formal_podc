import Mathlib

/-!
# Dynamic balanced graph partitioning: the model

Pacut, Parham, Schmid, *Brief Announcement: Deterministic Lower Bound for Dynamic Balanced Graph
Partitioning*, PODC 2020, Section 1 ("Model") and Section 2 (learning model).

* Nodes form a finite type `V`; there are `ℓ` clusters `Fin ℓ`, each of capacity `k`.
  A *configuration* is a map `V → Fin ℓ`; it is `Balanced k` if no cluster holds more than `k`
  nodes (with `|V| = k ℓ` this means exactly `k` nodes per cluster, `card_fiber_eq`).
* A request is a pair of nodes. Serving request `(u, v)` in configuration `Q` costs `1` if `Q`
  separates `u` and `v` (external request) and `0` otherwise. Migrating from `P` to `Q` costs
  `α · dist P Q`, where `dist P Q` is the number of nodes placed differently.
* A *schedule* `O : ℕ → Config` serves request `σ[t]` in configuration `O (t+1)`, after migrating
  from `O t`; `O 0` is the initial configuration. `schedCost α σ O` is its total cost.
* A deterministic online algorithm (`OnlineAlg`) chooses, after seeing the requests `σ[0..t]`, the
  configuration `conf (σ.take (t+1))` in which `σ[t]` is served (it may repartition before serving).
  Its cost is `algCost`. `optCost` is the optimal offline cost (minimum over all balanced schedules
  starting in `init`).
* Learning model: the communication pattern admits a *perfect partition*, i.e. a balanced
  configuration in which every request is internal (`IsLearningInput`).
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DynamicPartitioningLB

open Finset

/-- A communication request between two nodes. -/
abbrev Req (V : Type*) := V × V

/-- A configuration: the cluster of every node. -/
abbrev Config (V : Type*) (ℓ : ℕ) := V → Fin ℓ

variable {V : Type*} [Fintype V] [DecidableEq V] {ℓ : ℕ}

/-- Every cluster holds at most `k` nodes. -/
def Balanced (k : ℕ) (P : Config V ℓ) : Prop :=
  ∀ s : Fin ℓ, (univ.filter (fun v => P v = s)).card ≤ k

/-- Number of nodes placed differently by `P` and `Q` (migrations needed from `P` to `Q`). -/
def dist (P Q : Config V ℓ) : ℕ := (univ.filter (fun v => P v ≠ Q v)).card

/-- Communication cost of request `r` served in configuration `Q`. -/
def sep (Q : Config V ℓ) (r : Req V) : ℕ := if Q r.1 = Q r.2 then 0 else 1

/-- Cost of the schedule `O` on the requests `σ`, the first of which is served at time `t + 1`
(from `O t` to `O (t+1)`). -/
def schedCostFrom (α : ℕ) (O : ℕ → Config V ℓ) : ℕ → List (Req V) → ℕ
  | _, [] => 0
  | t, r :: σ => α * dist (O t) (O (t + 1)) + sep (O (t + 1)) r + schedCostFrom α O (t + 1) σ

/-- Cost of the schedule `O` on the request sequence `σ`: migration from `O t` to `O (t+1)` and
service of `σ[t]` in `O (t+1)`. -/
def schedCost (α : ℕ) (σ : List (Req V)) (O : ℕ → Config V ℓ) : ℕ := schedCostFrom α O 0 σ

/-- An admissible (offline) schedule: starts in `init` and always respects the capacities. -/
def IsSchedule (k : ℕ) (init : Config V ℓ) (O : ℕ → Config V ℓ) : Prop :=
  O 0 = init ∧ ∀ t, Balanced k (O t)

/-- Optimal offline cost `OPT(σ)`. -/
noncomputable def optCost (k α : ℕ) (init : Config V ℓ) (σ : List (Req V)) : ℕ :=
  sInf {c | ∃ O, IsSchedule k init O ∧ schedCost α σ O = c}

/-- A deterministic online algorithm: after the requests `σ` have been revealed, it is in
configuration `conf σ` (the last request of `σ` is served there). -/
structure OnlineAlg (V : Type*) [Fintype V] (ℓ k : ℕ) (init : Config V ℓ) where
  /-- The configuration after the requests `σ` have been revealed (and the last one served). -/
  conf : List (Req V) → Config V ℓ
  conf_nil : conf [] = init
  balanced : ∀ σ, Balanced k (conf σ)

/-- The schedule followed by an online algorithm on `σ`. -/
def OnlineAlg.sched {k : ℕ} {init : Config V ℓ} (A : OnlineAlg V ℓ k init) (σ : List (Req V)) :
    ℕ → Config V ℓ := fun t => A.conf (σ.take t)

/-- `ALG(σ)`: total cost of the online algorithm `A` on `σ`. -/
def algCost {k : ℕ} {init : Config V ℓ} (α : ℕ) (A : OnlineAlg V ℓ k init) (σ : List (Req V)) :
    ℕ := schedCost α σ (A.sched σ)

/-- Learning model: the requests admit a *perfect partition* (a balanced configuration in which
no request is external). -/
def IsLearningInput (ℓ k : ℕ) (σ : List (Req V)) : Prop :=
  ∃ P : Config V ℓ, Balanced k P ∧ ∀ r ∈ σ, P r.1 = P r.2

/-- The first `T` requests of an infinite request sequence. -/
def prefixOf (σ : ℕ → Req V) (T : ℕ) : List (Req V) := (List.range T).map σ

/-- Learning model with a *static* communication pattern, as in Section 2 of the paper: the pattern
admits a perfect partition, and every pair that communicates does so forever (infinitely often). -/
def IsStaticLearningInput (ℓ k : ℕ) (σ : ℕ → Req V) : Prop :=
  (∃ P : Config V ℓ, Balanced k P ∧ ∀ t, P (σ t).1 = P (σ t).2) ∧
    ∀ t T, ∃ t', T ≤ t' ∧ σ t' = σ t

/-! ### Basic lemmas -/

lemma dist_self (P : Config V ℓ) : dist P P = 0 := by simp [dist]

lemma dist_comm (P Q : Config V ℓ) : dist P Q = dist Q P := by
  unfold dist; congr 1; ext v; simp [ne_comm]

lemma dist_triangle (P Q R : Config V ℓ) : dist P R ≤ dist P Q + dist Q R := by
  unfold dist
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro v hv
  simp only [mem_filter, mem_univ, true_and, mem_union] at hv ⊢
  by_contra h
  push Not at h
  exact hv (h.1.trans h.2)

lemma one_le_dist_of_ne {P Q : Config V ℓ} {v : V} (h : P v ≠ Q v) : 1 ≤ dist P Q :=
  card_pos.2 ⟨v, by simp [h]⟩

lemma dist_le_of_subset {P Q : Config V ℓ} {S : Finset V} (h : ∀ v, P v ≠ Q v → v ∈ S) :
    dist P Q ≤ S.card :=
  card_le_card fun v hv => h v (by simpa using hv)

lemma sep_eq_zero {Q : Config V ℓ} {r : Req V} (h : Q r.1 = Q r.2) : sep Q r = 0 := by
  simp [sep, h]

/-- A request that is external in the current configuration costs any algorithm at least `1`:
either it is served remotely or some node migrates (`α ≥ 1`). -/
lemma one_le_stepCost {α : ℕ} (hα : 1 ≤ α) {P Q : Config V ℓ} {r : Req V} (h : P r.1 ≠ P r.2) :
    1 ≤ α * dist P Q + sep Q r := by
  by_cases hq : Q r.1 = Q r.2
  · have : P r.1 ≠ Q r.1 ∨ P r.2 ≠ Q r.2 := by
      by_contra hc; push Not at hc; exact h (by rw [hc.1, hc.2, hq])
    have hd : 1 ≤ dist P Q := by
      rcases this with h1 | h1 <;> exact one_le_dist_of_ne h1
    nlinarith
  · simp [sep, hq]

lemma schedCostFrom_append (α : ℕ) (O : ℕ → Config V ℓ) (σ : List (Req V)) (r : Req V) :
    ∀ t, schedCostFrom α O t (σ ++ [r]) = schedCostFrom α O t σ +
      (α * dist (O (t + σ.length)) (O (t + σ.length + 1)) + sep (O (t + σ.length + 1)) r) := by
  induction σ with
  | nil => intro t; simp [schedCostFrom]
  | cons a σ ih =>
    intro t
    simp only [List.cons_append, schedCostFrom, ih (t + 1), List.length_cons]
    rw [show t + 1 + σ.length = t + (σ.length + 1) by omega]
    ring

lemma schedCostFrom_congr (α : ℕ) (σ : List (Req V)) :
    ∀ (t : ℕ) (O O' : ℕ → Config V ℓ), (∀ i, t ≤ i → i ≤ t + σ.length → O i = O' i) →
      schedCostFrom α O t σ = schedCostFrom α O' t σ := by
  induction σ with
  | nil => intros; rfl
  | cons a σ ih =>
    intro t O O' h
    simp only [schedCostFrom, List.length_cons] at h ⊢
    rw [h t le_rfl (by omega), h (t + 1) (by omega) (by omega),
      ih (t + 1) O O' (fun i hi hi' => h i (by omega) (by omega))]

lemma algCost_nil {k α : ℕ} {init : Config V ℓ} (A : OnlineAlg V ℓ k init) :
    algCost α A [] = 0 := rfl

/-- Cost of an online algorithm after one more request. -/
lemma algCost_append {k α : ℕ} {init : Config V ℓ} (A : OnlineAlg V ℓ k init)
    (σ : List (Req V)) (r : Req V) :
    algCost α A (σ ++ [r]) =
      algCost α A σ + (α * dist (A.conf σ) (A.conf (σ ++ [r])) + sep (A.conf (σ ++ [r])) r) := by
  unfold algCost schedCost
  rw [schedCostFrom_append, schedCostFrom_congr α σ 0 (A.sched (σ ++ [r])) (A.sched σ)]
  · simp only [zero_add, OnlineAlg.sched]
    rw [List.take_append_of_le_length le_rfl, List.take_length,
      List.take_of_length_le (by simp)]
  · intro i _ hi
    simp only [OnlineAlg.sched]
    rw [List.take_append_of_le_length (by omega)]

/-- The cost of an online algorithm can only grow when more requests arrive. -/
lemma algCost_le_append {k α : ℕ} {init : Config V ℓ} (A : OnlineAlg V ℓ k init)
    (σ τ : List (Req V)) : algCost α A σ ≤ algCost α A (σ ++ τ) := by
  induction τ using List.reverseRecOn with
  | nil => simp
  | append_singleton τ r ih => rw [← List.append_assoc, algCost_append]; omega

lemma prefixOf_succ (σ : ℕ → Req V) (T : ℕ) : prefixOf σ (T + 1) = prefixOf σ T ++ [σ T] := by
  simp [prefixOf, List.range_succ]

lemma prefixOf_prefix (σ : ℕ → Req V) {m T : ℕ} (h : m ≤ T) : prefixOf σ m <+: prefixOf σ T := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => rw [prefixOf_succ]; exact ih.trans (List.prefix_append _ _)

lemma mem_prefixOf {σ : ℕ → Req V} {T : ℕ} {r : Req V} (h : r ∈ prefixOf σ T) : ∃ t, σ t = r := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 h; exact ⟨t, rfl⟩

/-- `OPT(σ)` is at most the cost of any admissible schedule. -/
lemma optCost_le {k α : ℕ} {init : Config V ℓ} {σ : List (Req V)} {O : ℕ → Config V ℓ}
    (hO : IsSchedule k init O) : optCost k α init σ ≤ schedCost α σ O :=
  Nat.sInf_le ⟨O, hO, rfl⟩

/-- `OPT(σ) ≥ 1` as soon as the first request is external in the initial configuration. -/
lemma one_le_optCost {k α : ℕ} (hα : 1 ≤ α) {init : Config V ℓ} (hinit : Balanced k init)
    {r : Req V} {σ : List (Req V)} (hr : init r.1 ≠ init r.2) :
    1 ≤ optCost k α init (r :: σ) := by
  refine le_csInf ?_ ?_
  · exact ⟨_, fun _ => init, ⟨rfl, fun _ => hinit⟩, rfl⟩
  rintro c ⟨O, ⟨h0, -⟩, rfl⟩
  simp only [schedCost, schedCostFrom, zero_add]
  have := one_le_stepCost hα (Q := O 1) (h0 ▸ hr : O 0 r.1 ≠ O 0 r.2)
  omega

lemma schedCostFrom_eq_zero (α : ℕ) {O : ℕ → Config V ℓ} {P : Config V ℓ} (σ : List (Req V))
    (hσ : ∀ r ∈ σ, P r.1 = P r.2) : ∀ t, (∀ i, t ≤ i → O i = P) → schedCostFrom α O t σ = 0 := by
  induction σ with
  | nil => intros; rfl
  | cons a σ ih =>
    intro t hO
    simp only [schedCostFrom, hO t le_rfl, hO (t + 1) (by omega), dist_self, mul_zero, zero_add]
    rw [sep_eq_zero (hσ a (by simp)),
      ih (fun r hr => hσ r (by simp [hr])) (t + 1) (fun i hi => hO i (by omega))]

/-- The schedule that moves to `P` before the first request and stays there costs at most
`α · dist init P` on requests that are all internal in `P`. -/
lemma schedCost_switch_le (α : ℕ) (init P : Config V ℓ) (σ : List (Req V))
    (hσ : ∀ r ∈ σ, P r.1 = P r.2) :
    schedCost α σ (fun t => if t = 0 then init else P) ≤ α * dist init P := by
  cases σ with
  | nil => simp [schedCost, schedCostFrom]
  | cons a σ =>
    simp only [schedCost, schedCostFrom, ite_eq_left, zero_add, one_ne_zero, ite_false]
    rw [sep_eq_zero (hσ a (by simp)), schedCostFrom_eq_zero α σ (fun r hr => hσ r (by simp [hr])) 1
      (fun i hi => ite_eq_right (by omega))]
    simp

/-- With `|V| = k ℓ`, a balanced configuration has exactly `k` nodes in every cluster. -/
lemma card_fiber_eq {k : ℕ} (hV : Fintype.card V = ℓ * k) {P : Config V ℓ} (hP : Balanced k P)
    (s : Fin ℓ) : (univ.filter (fun v => P v = s)).card = k := by
  have hsum : (univ : Finset V).card = ∑ s : Fin ℓ, (univ.filter (fun v => P v = s)).card :=
    card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  have hle : ∀ s ∈ (univ : Finset (Fin ℓ)), (univ.filter (fun v => P v = s)).card ≤ k :=
    fun s _ => hP s
  have heq : ∑ s : Fin ℓ, (univ.filter (fun v => P v = s)).card = ∑ _s : Fin ℓ, k := by
    rw [← hsum, card_univ, hV]; simp
  exact (sum_eq_sum_iff_of_le hle).1 heq s (mem_univ s)

end Papers.PODC2020.DynamicPartitioningLB
