import Papers.PODC2026.LocalComputable.Concrete
import Mathlib.Tactic.IntervalCases

/-!
# The paper's "maximally `T`-safe" neighbourhoods are not a property of the view

Definition 5.1: `t` is *`T`-safe* for `v` in `G` if no network `G'` with a node `v'` whose
radius-`t` view equals that of `v` has `t > T(|V(G')|)`; `t` is *maximally `T`-safe* if `t` is
safe and `t + 1` is not. The paper then "extends these notions to the rooted neighbourhoods
themselves", and the algorithms of Theorems 5.3 and 5.4 let every node grow its view "until it
reaches a maximally `T`-safe neighbourhood" and stop there.

Whether `t` is maximally safe depends on the radius-`(t+1)` view, which the node does not know
after `t` rounds. We show in the concrete model of Section 3 (any `Δ ≥ 2`, `c ≥ 1`, `k ≥ 1`) and
for the computable non-decreasing bound `T(n) = ⌊(n-1)/2⌋`: the node `0` of a triangle `C₃` and
the node `0` of a 5-cycle `C₅` have the same radius-`1` view, radius `1 = T(3)` is maximally
safe in `C₃` but not in `C₅`. Hence no ball-growing algorithm stops exactly at the (first)
maximally safe radius (`no_alg_stops_at_maxSafe`); in `C₃` a node needs radius `2 > T(3)` to
recognise that radius `1` is maximally safe. The fix is our notion `Model.Critical`
("the radius-`t` view occurs in a network whose time bound is `≤ t`"), which is a property of
the radius-`t` view and is implied by maximal safety (`MaxSafe.critical`).
-/

namespace LocalComputable

namespace Model

variable {Net View : Type*} (M : Model Net View)

/-- Definition 5.1 (literal): `t` is `T`-safe for `v` in `G`. -/
def Safe (T : ℕ → ℕ) (G : Net) (v t : ℕ) : Prop :=
  ¬ ∃ G' v', v' < M.size G' ∧ M.view G' v' t = M.view G v t ∧ T (M.size G') < t

/-- Definition 5.1 (literal): `t` is maximally `T`-safe for `v` in `G`. -/
def MaxSafe (T : ℕ → ℕ) (G : Net) (v t : ℕ) : Prop :=
  M.Safe T G v t ∧ ¬ M.Safe T G v (t + 1)

variable {M}

/-- Safety of radius `t` only depends on the radius-`t` view. -/
theorem safe_congr {T : ℕ → ℕ} {G H : Net} {v w t : ℕ} (h : M.view G v t = M.view H w t) :
    M.Safe T G v t ↔ M.Safe T H w t := by
  simp only [Safe, h]

/-- A safe radius is within the time bound. -/
theorem Safe.le {T : ℕ → ℕ} {G : Net} {v t : ℕ} (hv : v < M.size G) (h : M.Safe T G v t) :
    t ≤ T (M.size G) := by
  by_contra hc
  exact h ⟨G, v, hv, rfl, by omega⟩

/-- Maximal safety implies criticality of the radius-`t` view. -/
theorem MaxSafe.critical {T : ℕ → ℕ} {G : Net} {v t : ℕ} (h : M.MaxSafe T G v t) :
    M.Critical T (M.view G v t) t := by
  have h2 := h.2
  simp only [Safe, not_not] at h2
  obtain ⟨G', v', hv', hx, hT⟩ := h2
  exact ⟨G', v', hv', M.restrict (Nat.le_succ t) hx, by omega⟩

variable (M)

/-- View-level reading of Definition 5.1 ("if `t` is maximally `T`-safe for `v`, then `N^t(v)` is
maximally `T`-safe"): the view is maximally safe for *some* node having it. -/
def MaxSafeView (T : ℕ → ℕ) (x : View) (t : ℕ) : Prop :=
  ∃ G v, v < M.size G ∧ M.view G v t = x ∧ M.MaxSafe T G v t

/-- Safety of a view (Definition 5.1, which depends only on the radius-`t` view). -/
def SafeView (T : ℕ → ℕ) (x : View) (t : ℕ) : Prop :=
  ¬ ∃ G' v', v' < M.size G' ∧ M.view G' v' t = x ∧ T (M.size G') < t

/-- Under the view-level reading, a view is maximally safe iff it is safe and critical. -/
theorem maxSafeView_iff (T : ℕ → ℕ) (x : View) (t : ℕ) :
    M.MaxSafeView T x t ↔ M.SafeView T x t ∧ M.Critical T x t := by
  constructor
  · rintro ⟨G, v, hv, rfl, hs, hns⟩
    refine ⟨hs, ?_⟩
    simp only [Safe, not_not] at hns
    obtain ⟨G', v', hv', hx, hT⟩ := hns
    exact ⟨G', v', hv', M.restrict (Nat.le_succ t) hx, by omega⟩
  · rintro ⟨hs, G, v, hv, rfl, hT⟩
    refine ⟨G, v, hv, rfl, hs, ?_⟩
    simp only [Safe, not_not]
    exact ⟨G, v, hv, rfl, by omega⟩

/-- Under the view-level reading, the first maximally safe radius of a node is its first critical
radius; so "grow until the view is maximally safe" stops within `T(n)` rounds. -/
theorem first_critical_maxSafeView (T : ℕ → ℕ) (G : Net) (v t : ℕ)
    (hc : M.Critical T (M.view G v t) t)
    (hmin : ∀ s < t, ¬ M.Critical T (M.view G v s) s) :
    M.MaxSafeView T (M.view G v t) t ∧ ∀ s < t, ¬ M.MaxSafeView T (M.view G v s) s := by
  refine ⟨(M.maxSafeView_iff T _ t).2 ⟨?_, hc⟩,
    fun s hs h => hmin s hs ((M.maxSafeView_iff T _ s).1 h).2⟩
  rintro ⟨G', v', hv', hx, hT⟩
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact hmin t' (by omega) ⟨G', v', hv', M.restrict (Nat.le_succ t') hx, by omega⟩

end Model

/-! ### The counterexample: `C₃` versus `C₅` -/

open PNet VTree

/-- The triangle, identifiers `1, 2, 3`, inputs `0`. -/
def tri : PNet := ⟨3, [[1, 2], [2, 0], [0, 1]], [1, 2, 3], [0, 0, 0]⟩

/-- The 5-cycle `0-1-3-4-2-0`, identifiers `1, …, 5`, inputs `0`; node `0` has the same
neighbours (with the same identifiers and ports) as in `tri`. -/
def pent : PNet := ⟨5, [[1, 2], [3, 0], [0, 4], [4, 1], [2, 3]], [1, 2, 3, 4, 5], [0, 0, 0, 0, 0]⟩

theorem tri_wf {Δ c k : ℕ} (hΔ : 2 ≤ Δ) (hc : 1 ≤ c) (hk : 1 ≤ k) : tri.WF Δ c k where
  len_nbr := rfl
  len_id := rfl
  len_inp := rfl
  nodup := by decide
  deg_le := fun v hv => by change v < 3 at hv; interval_cases v <;> simp [tri, nbrOf] <;> omega
  nbr_lt := by decide
  irrefl := by decide
  symm := by decide
  id_inj := by decide
  id_pos := by decide
  id_le := fun v hv => by
    have : tri.idOf v ≤ 3 := by change v < 3 at hv; interval_cases v <;> decide
    exact this.trans (Nat.le_self_pow (by omega) 3)
  inp_lt := fun v hv => by change v < 3 at hv; interval_cases v <;> simp [tri, inpOf] <;> omega

theorem pent_wf {Δ c k : ℕ} (hΔ : 2 ≤ Δ) (hc : 1 ≤ c) (hk : 1 ≤ k) : pent.WF Δ c k where
  len_nbr := rfl
  len_id := rfl
  len_inp := rfl
  nodup := by decide
  deg_le := fun v hv => by change v < 5 at hv; interval_cases v <;> simp [pent, nbrOf] <;> omega
  nbr_lt := by decide
  irrefl := by decide
  symm := by decide
  id_inj := by decide
  id_pos := by decide
  id_le := fun v hv => by
    have : pent.idOf v ≤ 5 := by change v < 5 at hv; interval_cases v <;> decide
    exact this.trans (Nat.le_self_pow (by omega) 5)
  inp_lt := fun v hv => by change v < 5 at hv; interval_cases v <;> simp [pent, inpOf] <;> omega

/-- The bound `T(n) = ⌊(n-1)/2⌋` (computable, non-decreasing). -/
def Thalf (n : ℕ) : ℕ := (n - 1) / 2

theorem fview_tri_one : fview tri 0 1 = fview pent 0 1 := rfl

theorem ids_tri_one : (fview tri 0 1).ids.toFinset.card = 3 := by
  simp [fview, VTree.ids, tri, nbrOf, idOf, inpOf]

theorem ids_pent_two : (fview pent 0 2).ids.toFinset.card = 5 := by
  simp [fview, VTree.ids, pent, nbrOf, idOf, inpOf]

variable {Δ c k : ℕ}

/-- `C₃` as a network of the concrete model. -/
def triNet (hΔ : 2 ≤ Δ) (hc : 1 ≤ c) (hk : 1 ≤ k) : Net Δ c k := ⟨tri, tri_wf hΔ hc hk⟩

/-- `C₅` as a network of the concrete model. -/
def pentNet (hΔ : 2 ≤ Δ) (hc : 1 ≤ c) (hk : 1 ≤ k) : Net Δ c k := ⟨pent, pent_wf hΔ hc hk⟩

/-- **The paper's maximally safe neighbourhoods are not determined by the view.** In the concrete
model (`Δ ≥ 2`, `c ≥ 1`, `k ≥ 1`) with `T(n) = ⌊(n-1)/2⌋`: node `0` of `C₃` and node `0` of `C₅`
have equal radius-`1` views, radius `1 = T(3)` is maximally `T`-safe in `C₃`, but no radius
`≤ 1` is maximally `T`-safe in `C₅`. -/
theorem maxSafe_not_view_determined (hΔ : 2 ≤ Δ) (hc : 1 ≤ c) (hk : 1 ≤ k) :
    (concreteModel Δ c k).view (triNet hΔ hc hk) 0 1 =
        (concreteModel Δ c k).view (pentNet hΔ hc hk) 0 1 ∧
      Thalf ((concreteModel Δ c k).size (triNet hΔ hc hk)) = 1 ∧
      (concreteModel Δ c k).MaxSafe Thalf (triNet hΔ hc hk) 0 1 ∧
      ∀ s ≤ 1, ¬ (concreteModel Δ c k).MaxSafe Thalf (pentNet hΔ hc hk) 0 s := by
  set G := triNet hΔ hc hk
  set H := pentNet hΔ hc hk
  have hview : (concreteModel Δ c k).view G 0 1 = (concreteModel Δ c k).view H 0 1 :=
    fview_tri_one
  -- radius 1 is safe for `C₃` (and hence for `C₅`): every network containing the view has
  -- at least 3 nodes
  have hsafe1 : (concreteModel Δ c k).Safe Thalf G 0 1 := by
    rintro ⟨G', v', hv', hx, hT⟩
    have h3 : 3 ≤ G'.1.n := by
      have := card_ids_le G'.2 (t := 1) hv'
      change (fview G'.1 v' 1) = fview tri 0 1 at hx
      rw [hx, ids_tri_one] at this
      exact this
    change (G'.1.n - 1) / 2 < 1 at hT
    omega
  -- radius 2 is not safe for `C₃`: `C₃` itself has `T(3) = 1 < 2`
  have hunsafe2 : ¬ (concreteModel Δ c k).Safe Thalf G 0 2 := by
    simp only [Model.Safe, not_not]
    exact ⟨G, 0, show 0 < 3 by omega, rfl, show (3 - 1) / 2 < 2 by omega⟩
  -- radius 2 is safe for `C₅`: every network containing the view has at least 5 nodes
  have hsafe2 : (concreteModel Δ c k).Safe Thalf H 0 2 := by
    rintro ⟨G', v', hv', hx, hT⟩
    have h5 : 5 ≤ G'.1.n := by
      have := card_ids_le G'.2 (t := 2) hv'
      change (fview G'.1 v' 2) = fview pent 0 2 at hx
      rw [hx, ids_pent_two] at this
      exact this
    change (G'.1.n - 1) / 2 < 2 at hT
    omega
  refine ⟨hview, (by show (3 - 1) / 2 = 1; rfl), ⟨hsafe1, hunsafe2⟩, fun s hs => ?_⟩
  rintro ⟨-, hns⟩
  interval_cases s
  · exact hns ((Model.safe_congr hview).mp hsafe1)
  · exact hns hsafe2

/-- Consequently, no ball-growing rule can stop exactly at the maximally safe radii: for any
candidate algorithm `B`, there is a node where `B` stops at radius `1` although `1` is not
maximally safe there, or does not stop at radius `1` although it is. -/
theorem no_alg_stops_at_maxSafe (hΔ : 2 ≤ Δ) (hc : 1 ≤ c) (hk : 1 ≤ k)
    {Out : Type*} (B : Alg VTree Out) :
    ¬ ∀ (G : Net Δ c k) (v t : ℕ), v < (concreteModel Δ c k).size G →
      ((B ((concreteModel Δ c k).view G v t) t).isSome ↔
        (concreteModel Δ c k).MaxSafe Thalf G v t) := by
  intro hB
  obtain ⟨hview, -, hG, hH⟩ := maxSafe_not_view_determined hΔ hc hk
  have h1 := (hB (triNet hΔ hc hk) 0 1 (show 0 < 3 by omega)).mpr hG
  rw [hview] at h1
  exact hH 1 le_rfl ((hB (pentNet hΔ hc hk) 0 1 (show 0 < 5 by omega)).mp h1)

/-- **The literal rule exceeds the time bound.** Any algorithm that never stops before a maximally
`T`-safe radius (the paper's "grow until the view is maximally `T`-safe") fails to stop within
`T(3) = 1` rounds at node `0` of `C₃`, for `T(n) = ⌊(n-1)/2⌋`. -/
theorem maxSafe_rule_exceeds (hΔ : 2 ≤ Δ) (hc : 1 ≤ c) (hk : 1 ≤ k) {Out : Type*}
    (B : Alg VTree Out)
    (hB : ∀ (G : Net Δ c k) (v t : ℕ), v < (concreteModel Δ c k).size G →
      (B ((concreteModel Δ c k).view G v t) t).isSome →
        ∃ s ≤ t, (concreteModel Δ c k).MaxSafe Thalf G v s) :
    (concreteModel Δ c k).out B (triNet hΔ hc hk) 0
      (Thalf ((concreteModel Δ c k).size (triNet hΔ hc hk))) = none := by
  obtain ⟨hview, hT, -, hH⟩ := maxSafe_not_view_determined hΔ hc hk
  rw [hT, Model.out_eq_none_iff]
  intro t ht
  have hv : (concreteModel Δ c k).view (triNet hΔ hc hk) 0 t =
      (concreteModel Δ c k).view (pentNet hΔ hc hk) 0 t :=
    (concreteModel Δ c k).restrict ht hview
  rw [hv]
  by_contra hne
  obtain ⟨s, hs, hms⟩ := hB (pentNet hΔ hc hk) 0 t (show 0 < 5 by omega)
    (Option.ne_none_iff_isSome.mp hne)
  exact hH s (hs.trans ht) hms

end LocalComputable
