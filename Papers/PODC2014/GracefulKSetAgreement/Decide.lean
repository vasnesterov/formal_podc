import Papers.PODC2014.GracefulKSetAgreement.Model

/-!
# Deciding journeys and root components of Boolean patterns

For communication patterns on `Fin n` given by a Boolean adjacency function `g` (`g t u v`:
`v` receives `u` in round `t`), journeys (`journey_iff_jset`), reachability
(`reachable_iff_reachB`) and root components (`isRootComp_iff_rootsB`) are characterized by
computable functions, so that properties of concrete runs can be checked by `decide`.
Completeness of the reachability computation is guaranteed by a decidable closedness check
(`AllClosed`) instead of a general fixpoint argument.
-/

-- CSLib candidate (generic tools for concrete dynamic networks)

namespace Podc.GracefulKSetAgreement

open Cslib.HeardOf Cslib.DynNet

variable {n : ℕ}

/-- The processes reached from `p` at time `s` by time `s + k`. -/
def jset (g : ℕ → Fin n → Fin n → Bool) (s : ℕ) (p : Fin n) : ℕ → Finset (Fin n)
  | 0 => {p}
  | k + 1 =>
    jset g s p k ∪ Finset.univ.filter (fun z => ∃ y ∈ jset g s p k, g (s + k) y z = true)

theorem journey_iff_jset {ρ : ℕ → Graph (Fin n)} {g : ℕ → Fin n → Fin n → Bool}
    (hρ : ∀ t u v, ρ t u v ↔ g t u v = true) (s : ℕ) (p : Fin n) :
    ∀ k q, Journey ρ s p (s + k) q ↔ q ∈ jset g s p k
  | 0, q => by simp [jset, journey_self_iff, eq_comm]
  | k + 1, q => by
    rw [← Nat.add_assoc, journey_succ_iff (Nat.le_add_right _ _)]
    simp only [jset, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      journey_iff_jset hρ s p k, ← hρ]
    constructor
    · rintro ⟨y, hy, rfl | h⟩
      · exact Or.inl hy
      · exact Or.inr ⟨y, hy, h⟩
    · rintro (h | ⟨y, hy, h⟩)
      · exact ⟨q, h, Or.inl rfl⟩
      · exact ⟨y, hy, Or.inr h⟩

/-- The processes reachable from `u` in the graph `g` (computed with `n` rounds). -/
def reachB (g : Fin n → Fin n → Bool) (u : Fin n) : Finset (Fin n) := jset (fun _ => g) 0 u n

/-- `X` is closed under out-edges of `g`. -/
def ClosedB (g : Fin n → Fin n → Bool) (X : Finset (Fin n)) : Prop :=
  ∀ y ∈ X, ∀ z, g y z = true → z ∈ X

instance (g : Fin n → Fin n → Bool) (X : Finset (Fin n)) : Decidable (ClosedB g X) := by
  unfold ClosedB; infer_instance

/-- All reachability computations of `g` are complete (checked by `decide`). -/
def AllClosed (g : Fin n → Fin n → Bool) : Prop := ∀ u, ClosedB g (reachB g u)

instance (g : Fin n → Fin n → Bool) : Decidable (AllClosed g) := by
  unfold AllClosed; infer_instance

theorem reachable_of_journey_const {G : Graph (Fin n)} {s t : ℕ} {x y : Fin n}
    (h : Journey (fun _ => G) s x t y) : (Digraph.mk G).Reachable x y := by
  induction h with
  | refl => exact .rfl
  | step _ hs ih =>
    rcases hs with rfl | hs
    · exact ih
    · exact ih.trans (Digraph.Adj.reachable (G := Digraph.mk G) hs)

theorem reachable_iff_reachB {G : Graph (Fin n)} {g : Fin n → Fin n → Bool}
    (hG : ∀ u v, G u v ↔ g u v = true) {u : Fin n} (hcl : ClosedB g (reachB g u)) (v : Fin n) :
    (Digraph.mk G).Reachable u v ↔ v ∈ reachB g u := by
  constructor
  · intro h
    have hu : u ∈ reachB g u := by
      rw [reachB, ← journey_iff_jset (ρ := fun _ => G) (fun _ => hG) 0 u n u]
      exact Journey.self (Nat.zero_le _)
    induction h with
    | refl => exact hu
    | tail _ hyz ih => exact hcl _ ih _ ((hG _ _).1 hyz)
  · intro h
    rw [reachB, ← journey_iff_jset (ρ := fun _ => G) (fun _ => hG) 0 u n v] at h
    exact reachable_of_journey_const h

/-- The ancestors of `r` in `g`. -/
def ancB (g : Fin n → Fin n → Bool) (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => r ∈ reachB g x

/-- The root components of `g`, as the ancestor sets of the vertices that reach all their
ancestors. -/
def rootsB (g : Fin n → Fin n → Bool) : List (Finset (Fin n)) :=
  ((List.finRange n).filterMap fun r =>
    if ∀ x, r ∈ reachB g x → x ∈ reachB g r then some (ancB g r) else none).dedup

theorem isRootComp_iff_rootsB {G : Graph (Fin n)} {g : Fin n → Fin n → Bool}
    (hG : ∀ u v, G u v ↔ g u v = true) (hcl : AllClosed g) (R : Set (Fin n)) :
    IsRootComp G R ↔ ∃ F ∈ rootsB g, R = ↑F := by
  have hr : ∀ x y, (Digraph.mk G).Reachable x y ↔ y ∈ reachB g x :=
    fun x y => reachable_iff_reachB hG (hcl x) y
  unfold IsRootComp
  rw [Digraph.isSourceComponent_iff]
  simp only [rootsB, List.mem_dedup, List.mem_filterMap, List.mem_finRange, true_and, hr]
  constructor
  · rintro ⟨r, rfl, h⟩
    refine ⟨ancB g r, ⟨r, by split_ifs; rfl⟩, ?_⟩
    ext x; simp [ancB]
  · rintro ⟨F, ⟨r, hrF⟩, rfl⟩
    split_ifs at hrF with h
    cases hrF
    exact ⟨r, by ext x; simp [ancB], h⟩

end Podc.GracefulKSetAgreement
