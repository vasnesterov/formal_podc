import Papers.PODC2010.TruncatedGaleShapley.Basic

/-!
# The example of §2.2: stable matchings are not robust

The path `0 - 1 - ⋯ - 10` (the figure of §2.2: the top row are the even nodes, the bottom row the
odd ones), where every node prefers its left neighbour. Its unique stable matching is
`{0,1}, {2,3}, …, {8,9}`. Transposing the preferences of node `1` (it now prefers `2` over `0`)
gives an instance whose unique stable matching `{1,2}, {3,4}, …, {9,10}` is edge-disjoint from the
first one (`pathPG_unique_stable`, `stable_matchings_disjoint`).
-/

namespace Podc.TruncatedGaleShapley

open Finset

namespace PrefGraph

variable {V : Type*} (P : PrefGraph V)

-- CSLib candidate (with `PrefGraph`)
/-- A forced pair: if every neighbour that `u` prefers to `v` and every neighbour that `v` prefers
to `u` is matched to somebody else, then in a stable matching `u` is matched to `v`. -/
lemma forced {p : V → Option V} (hp : P.IsMatching p) (hs : P.IsStable p) {u v : V}
    (huv : v ∈ P.N u)
    (hu : ∀ y ∈ P.N u, P.rank u y < P.rank u v → ∃ z, z ≠ u ∧ p y = some z)
    (hv : ∀ x ∈ P.N v, P.rank v x < P.rank v u → ∃ z, z ≠ v ∧ p x = some z) :
    p u = some v := by
  by_contra hne
  apply hs u v
  refine ⟨huv, ?_, ?_⟩
  · rcases hpu : p u with _ | x
    · trivial
    · show P.rank u v < P.rank u x
      have hx := hp.mem_N u x hpu
      rcases lt_trichotomy (P.rank u v) (P.rank u x) with h | h | h
      · exact h
      · exact absurd (hpu.trans (congrArg some (P.rank_inj hx huv h.symm))) hne
      · obtain ⟨z, hz, hpz⟩ := hu x hx h
        rw [hp.symm u x hpu] at hpz; cases hpz; exact absurd rfl hz
  · rcases hpv : p v with _ | x
    · trivial
    · show P.rank v u < P.rank v x
      have hx := hp.mem_N v x hpv
      rcases lt_trichotomy (P.rank v u) (P.rank v x) with h | h | h
      · exact h
      · have := P.rank_inj (P.symm huv) hx h; subst this
        exact absurd (hp.symm v u hpv) hne
      · obtain ⟨z, hz, hpz⟩ := hv x hx h
        rw [hp.symm v x hpv] at hpz; cases hpz; exact absurd rfl hz

/-- Side condition of `forced` when `u` prefers nobody to `v`. -/
lemma none_better {p : V → Option V} {u v : V} (h : ∀ y ∈ P.N u, ¬ P.rank u y < P.rank u v) :
    ∀ y ∈ P.N u, P.rank u y < P.rank u v → ∃ z, z ≠ u ∧ p y = some z :=
  fun y hy hr => absurd hr (h y hy)

end PrefGraph

/-- The path on `Fin 11`; every node prefers its left neighbour, except that with `flip = true`
node `1` prefers its right neighbour. -/
def pathPG (flip : Bool) : PrefGraph (Fin 11) where
  N v := univ.filter fun u => u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := by decide
  rank v u := if flip = true ∧ v = 1 then (if u.val < v.val then 1 else 0)
    else (if u.val < v.val then 0 else 1)
  rank_inj := by revert flip; decide

/-- The stable matchings of the two instances. -/
def pathStable : Bool → Fin 11 → Option (Fin 11)
  | false => ![some 1, some 0, some 3, some 2, some 5, some 4, some 7, some 6, some 9, some 8, none]
  | true => ![none, some 2, some 1, some 4, some 3, some 6, some 5, some 8, some 7, some 10, some 9]

lemma pathStable_isMatching (flip : Bool) : (pathPG flip).IsMatching (pathStable flip) := by
  constructor <;> revert flip <;> decide

lemma pathStable_isStable (flip : Bool) : (pathPG flip).IsStable (pathStable flip) := by
  unfold PrefGraph.IsStable PrefGraph.IsUnstable
  revert flip; decide

/-- A stable matching of the unflipped path is `pathStable false`. -/
lemma eq_pathStable_false {p : Fin 11 → Option (Fin 11)} (hp : (pathPG false).IsMatching p)
    (hs : (pathPG false).IsStable p) : p = pathStable false := by
  have F := fun u v huv hu hv => (pathPG false).forced hp hs (u := u) (v := v) huv hu hv
  have h0 : p 0 = some 1 := F 0 1 (by decide) (PrefGraph.none_better _ (by decide)) (PrefGraph.none_better _ (by decide))
  have h2 : p 2 = some 3 := F 2 3 (by decide) (by
    intro y hy hr
    have : y = 1 := by revert y; decide
    subst this; exact ⟨0, by decide, hp.symm _ _ h0⟩) (PrefGraph.none_better _ (by decide))
  have h4 : p 4 = some 5 := F 4 5 (by decide) (by
    intro y hy hr
    have : y = 3 := by revert y; decide
    subst this; exact ⟨2, by decide, hp.symm _ _ h2⟩) (PrefGraph.none_better _ (by decide))
  have h6 : p 6 = some 7 := F 6 7 (by decide) (by
    intro y hy hr
    have : y = 5 := by revert y; decide
    subst this; exact ⟨4, by decide, hp.symm _ _ h4⟩) (PrefGraph.none_better _ (by decide))
  have h8 : p 8 = some 9 := F 8 9 (by decide) (by
    intro y hy hr
    have : y = 7 := by revert y; decide
    subst this; exact ⟨6, by decide, hp.symm _ _ h6⟩) (PrefGraph.none_better _ (by decide))
  have h10 : p 10 = none := by
    rcases h : p 10 with _ | x
    · rfl
    · have hx := hp.mem_N 10 x h
      have : x = 9 := (by decide : ∀ x ∈ (pathPG false).N 10, x = 9) x hx
      subst this
      have h1 := hp.symm _ _ h
      rw [hp.symm _ _ h8] at h1
      exact absurd h1 (by decide)
  funext v
  fin_cases v
  · exact h0
  · exact hp.symm _ _ h0
  · exact h2
  · exact hp.symm _ _ h2
  · exact h4
  · exact hp.symm _ _ h4
  · exact h6
  · exact hp.symm _ _ h6
  · exact h8
  · exact hp.symm _ _ h8
  · exact h10

/-- A stable matching of the flipped path is `pathStable true`. -/
lemma eq_pathStable_true {p : Fin 11 → Option (Fin 11)} (hp : (pathPG true).IsMatching p)
    (hs : (pathPG true).IsStable p) : p = pathStable true := by
  have F := fun u v huv hu hv => (pathPG true).forced hp hs (u := u) (v := v) huv hu hv
  have h1 : p 1 = some 2 := F 1 2 (by decide) (PrefGraph.none_better _ (by decide)) (PrefGraph.none_better _ (by decide))
  have h3 : p 3 = some 4 := F 3 4 (by decide) (by
    intro y hy hr
    have : y = 2 := by revert y; decide
    subst this; exact ⟨1, by decide, hp.symm _ _ h1⟩) (PrefGraph.none_better _ (by decide))
  have h5 : p 5 = some 6 := F 5 6 (by decide) (by
    intro y hy hr
    have : y = 4 := by revert y; decide
    subst this; exact ⟨3, by decide, hp.symm _ _ h3⟩) (PrefGraph.none_better _ (by decide))
  have h7 : p 7 = some 8 := F 7 8 (by decide) (by
    intro y hy hr
    have : y = 6 := by revert y; decide
    subst this; exact ⟨5, by decide, hp.symm _ _ h5⟩) (PrefGraph.none_better _ (by decide))
  have h9 : p 9 = some 10 := F 9 10 (by decide) (by
    intro y hy hr
    have : y = 8 := by revert y; decide
    subst this; exact ⟨7, by decide, hp.symm _ _ h7⟩) (PrefGraph.none_better _ (by decide))
  have h0 : p 0 = none := by
    rcases h : p 0 with _ | x
    · rfl
    · have hx := hp.mem_N 0 x h
      have : x = 1 := (by decide : ∀ x ∈ (pathPG true).N 0, x = 1) x hx
      subst this
      have h' := hp.symm _ _ h
      rw [h1] at h'
      exact absurd h' (by decide)
  funext v
  fin_cases v
  · exact h0
  · exact h1
  · exact hp.symm _ _ h1
  · exact h3
  · exact hp.symm _ _ h3
  · exact h5
  · exact hp.symm _ _ h5
  · exact h7
  · exact hp.symm _ _ h7
  · exact h9
  · exact hp.symm _ _ h9

/-- **§2.2.** Each of the two path instances (which differ only in the preferences of node `1`)
has a unique stable matching, `pathStable flip`. -/
theorem pathPG_unique_stable (flip : Bool) (p : Fin 11 → Option (Fin 11))
    (hp : (pathPG flip).IsMatching p) : (pathPG flip).IsStable p ↔ p = pathStable flip := by
  refine ⟨fun hs => ?_, fun h => h ▸ pathStable_isStable flip⟩
  cases flip
  · exact eq_pathStable_false hp hs
  · exact eq_pathStable_true hp hs

/-- **§2.2.** The two unique stable matchings are edge-disjoint ("a single transposition in
preferences can force every match to break up"). -/
theorem stable_matchings_disjoint :
    Disjoint (matchingEdges (pathStable false)) (matchingEdges (pathStable true)) := by
  decide

/-- The two instances differ only in the preferences of node `1`. -/
lemma pathPG_rank_eq {v : Fin 11} (hv : v ≠ 1) (u : Fin 11) :
    (pathPG false).rank v u = (pathPG true).rank v u := by
  simp [pathPG, hv]

end Podc.TruncatedGaleShapley
