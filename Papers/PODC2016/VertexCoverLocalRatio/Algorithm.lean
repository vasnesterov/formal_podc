import Papers.PODC2016.VertexCoverLocalRatio.LocalRatio

/-!
# Algorithm 1 as a synchronous iteration on the global state

One *iteration* of Algorithm 1 (three communication rounds, see `Distributed.lean`) acts on the
global state: the current weight `w_i(v)` and the status of every vertex (still running, returned
`InCover`, returned `NotInCover`).

The current neighbourhood `N_i(v)` of a running vertex is the set of its running neighbours
(`actN`); `Correctness.lean` shows this agrees with the bookkeeping of lines 9, 16, 29–31 of the
pseudocode (a neighbour is dropped exactly when it returns `InCover`).

In iteration `i`, a running vertex `v`
* requests `request_i(v,u) = vault(v)/d_i(v)` from every running neighbour `u`, where
  `vault(v) = a·w_0(v)` (`a = ε'` in the paper);
* answers the requests of its running neighbours from `bank(v) = w_i(v) - vault(v)` by a
  **response rule** `R` (`budget_i(v,u)`);
* sets `w_{i+1}(v) = w_i(v) - ∑_u budget_i(u,v) - ∑_u budget_i(v,u)`;
* returns `InCover` if `w_{i+1}(v) ≤ θ·w_0(v)` (`θ = ε'`), otherwise `NotInCover` if all its
  running neighbours returned `InCover` in this iteration, otherwise keeps running.

The response rule is abstract (`Rule.Spec σ`): every answer is in `[0, request]`, the answers sum to
at most `bank(v)`, and if some request is not answered in full then the answers sum to at least
`bank(v) - σ·w_0(v)`. The paper's rule (line 20: answer `min(request, remaining bank)` in an
arbitrary order) satisfies `Spec 0` for every order (`greedy_spec`); the CONGEST variant of
Section 4 satisfies `Spec (θ/2)` with `a = θ/2` (`Congest.lean`).
-/

set_option linter.unusedSectionVars false

namespace VertexCoverLocalRatio

open Finset SimpleGraph

/-- Status of a vertex. -/
inductive Status
  | active
  | inCover
  | notInCover
  deriving DecidableEq

/-- A response rule: given the responder `v`, its initial weight `w_0(v)`, its bank, the request
function and the set of requesting neighbours, the amounts `budget(v,u)` granted to each `u`. -/
abbrev Rule (V : Type*) := V → ℝ → ℝ → (V → ℝ) → Finset V → V → ℝ

/-- Specification of a response rule with slack factor `σ`. -/
def Rule.Spec {V : Type*} (R : Rule V) (σ : ℝ) : Prop :=
  ∀ (v : V) (w0 b : ℝ) (r : V → ℝ) (S : Finset V), 0 ≤ b → b ≤ w0 → (∀ u ∈ S, 0 ≤ r u) →
    (∀ u ∈ S, 0 ≤ R v w0 b r S u ∧ R v w0 b r S u ≤ r u) ∧
    ∑ u ∈ S, R v w0 b r S u ≤ b ∧
    (∀ u ∈ S, R v w0 b r S u < r u → b - σ * w0 ≤ ∑ u ∈ S, R v w0 b r S u)

/-! ### The paper's response rule: greedy in an arbitrary order (line 20) -/

/-- Answer the requesters in the order of the list `l`, each with
`min(request, remaining bank)`. -/
noncomputable def greedy {V : Type*} [DecidableEq V] (b : ℝ) (r : V → ℝ) : List V → V → ℝ
  | [] => fun _ => 0
  | u :: l => Function.update (greedy (b - min (r u) b) r l) u (min (r u) b)

theorem greedy_not_mem {V : Type*} [DecidableEq V] (r : V → ℝ) :
    ∀ (l : List V) (b : ℝ) (x : V), x ∉ l → greedy b r l x = 0
  | [], _, _, _ => rfl
  | u :: l, b, x, hx => by
    simp only [List.mem_cons, not_or] at hx
    simp only [greedy, Function.update_of_ne hx.1]
    exact greedy_not_mem r l _ x hx.2

/-- Properties of the greedy answers along a duplicate-free list. -/
theorem greedy_props {V : Type*} [DecidableEq V] (r : V → ℝ) :
    ∀ (l : List V), l.Nodup → ∀ b : ℝ, 0 ≤ b → (∀ u ∈ l, 0 ≤ r u) →
      (∀ u ∈ l, 0 ≤ greedy b r l u ∧ greedy b r l u ≤ r u) ∧
      ∑ u ∈ l.toFinset, greedy b r l u ≤ b ∧
      (∀ u ∈ l, greedy b r l u < r u → ∑ u ∈ l.toFinset, greedy b r l u = b)
  | [], _, b, hb, _ => by simp [greedy, hb]
  | u :: l, hnd, b, hb, hr => by
    rw [List.nodup_cons] at hnd
    have hm0 : 0 ≤ min (r u) b := le_min (hr u (by simp)) hb
    have hmb : min (r u) b ≤ b := min_le_right _ _
    obtain ⟨ih1, ih2, ih3⟩ := greedy_props r l hnd.2 (b - min (r u) b) (by linarith)
      (fun x hx => hr x (by simp [hx]))
    set g' := greedy (b - min (r u) b) r l
    have hg : ∀ x ∈ l, greedy b r (u :: l) x = g' x := by
      intro x hx
      have : x ≠ u := fun h => hnd.1 (h ▸ hx)
      simp only [greedy, Function.update_of_ne this, g']
    have hgu : greedy b r (u :: l) u = min (r u) b := by simp [greedy]
    have hsum : ∑ x ∈ (u :: l).toFinset, greedy b r (u :: l) x =
        min (r u) b + ∑ x ∈ l.toFinset, g' x := by
      rw [List.toFinset_cons, sum_insert (by simpa using hnd.1), hgu]
      congr 1
      exact sum_congr rfl fun x hx => hg x (by simpa using hx)
    have hS0 : 0 ≤ ∑ x ∈ l.toFinset, g' x :=
      sum_nonneg fun x hx => (ih1 x (by simpa using hx)).1
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hgu]; exact ⟨hm0, min_le_left _ _⟩
      · rw [hg x hx]; exact ih1 x hx
    · rw [hsum]; linarith
    · intro x hx hlt
      rw [hsum]
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hgu] at hlt
        have hmin : min (x |> r) b = b := by
          rcases min_choice (r x) b with h | h
          · rw [h] at hlt; exact absurd hlt (lt_irrefl _)
          · exact h
        rw [hmin] at ih2 ⊢
        linarith
      · rw [hg x hx] at hlt
        rw [ih3 x hx hlt]; ring

/-- The paper's rule with an arbitrary processing order `ord v S` (a duplicate-free enumeration
of the requesters `S`, which may depend on the responder `v`). -/
noncomputable def greedyRule {V : Type*} [DecidableEq V] (ord : V → Finset V → List V) : Rule V :=
  fun v _ b r S => greedy b r (ord v S)

/-- An enumeration of finite sets. -/
def IsOrdering {V : Type*} [DecidableEq V] (ord : V → Finset V → List V) : Prop :=
  ∀ v S, (ord v S).Nodup ∧ (ord v S).toFinset = S

/-- `Finset.toList` (an arbitrary but fixed order) is an ordering. -/
theorem isOrdering_toList {V : Type*} [DecidableEq V] : IsOrdering (V := V) fun _ S => S.toList :=
  fun _ S => ⟨S.nodup_toList, by simp⟩

/-- The paper's rule satisfies the specification with slack `0`, for every processing order. -/
theorem greedy_spec {V : Type*} [DecidableEq V] {ord : V → Finset V → List V}
    (hord : IsOrdering ord) : (greedyRule ord).Spec 0 := by
  intro v w0 b r S hb _ hr
  obtain ⟨hnd, hS⟩ := hord v S
  have hr' : ∀ u ∈ ord v S, 0 ≤ r u := fun u hu =>
    hr u (by rw [← hS]; exact List.mem_toFinset.2 hu)
  obtain ⟨h1, h2, h3⟩ := greedy_props r (ord v S) hnd b hb hr'
  simp only [greedyRule]
  have hm : ∀ u ∈ S, u ∈ ord v S := fun u hu => by rw [← hS] at hu; exact List.mem_toFinset.1 hu
  rw [hS] at h2 h3
  refine ⟨fun u hu => h1 u (hm u hu), h2, fun u hu hlt => ?_⟩
  rw [h3 u (hm u hu) hlt]; simp

/-! ### The global state and one iteration -/

/-- Global state at the beginning of an iteration. -/
structure GState (V : Type*) where
  /-- current weight `w_i` -/
  w : V → ℝ
  /-- status -/
  st : V → Status

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (θ a : ℝ) (R : Rule V) (w0 : V → ℝ)

/-- `N_i(v)`: the running neighbours. -/
def actN (s : GState V) (v : V) : Finset V :=
  (G.neighborFinset v).filter fun u => s.st u = .active

/-- `d_i(v) = |N_i(v)|`. -/
def dg (s : GState V) (v : V) : ℕ := (actN G s v).card

/-- `request_i(v,·) = vault(v)/d_i(v)` with `vault(v) = a·w_0(v)`. -/
noncomputable def req (s : GState V) (v : V) : ℝ := a * w0 v / dg G s v

/-- `bank(v) = w_i(v) - vault(v)`. -/
def bank (s : GState V) (v : V) : ℝ := s.w v - a * w0 v

/-- The requests received by `v`: `request_i(u,v)` from every running neighbour `u` (and `0`
from everybody else). -/
noncomputable def reqAt (s : GState V) (v : V) (u : V) : ℝ :=
  if u ∈ actN G s v then req G a w0 s u else 0

/-- `budget_i(v,u)`: the amount `v` grants to the request of `u`. -/
noncomputable def bud (s : GState V) (v u : V) : ℝ :=
  R v (w0 v) (bank a w0 s v) (reqAt G a w0 s v) (actN G s v) u

/-- Total amount granted to `v` by its neighbours (its own requests). -/
noncomputable def recv (s : GState V) (v : V) : ℝ := ∑ u ∈ actN G s v, bud G a R w0 s u v

/-- Total amount granted by `v` to its neighbours. -/
noncomputable def given (s : GState V) (v : V) : ℝ := ∑ u ∈ actN G s v, bud G a R w0 s v u

/-- `w_{i+1}(v)`. -/
noncomputable def newW (s : GState V) (v : V) : ℝ :=
  if s.st v = .active then s.w v - recv G a R w0 s v - given G a R w0 s v else s.w v

/-- `v` returns `InCover` in this iteration. -/
def cov (s : GState V) (v : V) : Prop :=
  s.st v = .active ∧ newW G a R w0 s v ≤ θ * w0 v

open scoped Classical in
/-- One iteration of Algorithm 1. -/
noncomputable def step (s : GState V) : GState V where
  w := newW G a R w0 s
  st v :=
    if s.st v = .active then
      if newW G a R w0 s v ≤ θ * w0 v then .inCover
      else if ∀ u ∈ actN G s v, cov G θ a R w0 s u then .notInCover
      else .active
    else s.st v

/-- Initial state: weights `w_0 = w`, everybody running. -/
def init : GState V := ⟨w0, fun _ => .active⟩

/-- The state at the beginning of iteration `i`. -/
noncomputable def run (i : ℕ) : GState V := (step G θ a R w0)^[i] (init w0)

/-- The output: the set of vertices that returned `InCover` by the beginning of iteration `T`. -/
noncomputable def output (T : ℕ) : Finset V := univ.filter fun v => (run G θ a R w0 T).st v = .inCover

end VertexCoverLocalRatio
