import Papers.PODC2023.TreeExplorationBFDN.Model

/-!
# Subtrees of a `RootedTree` (ancestor relation)

Basic facts about `InSub T v w` (`w ∈ T(v)`) and `towards` used by the BFDN analysis.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} (T : G.RootedTree)

namespace InSub

variable {T}

theorem refl (v : V) : InSub T v v := ⟨0, rfl⟩

theorem root (w : V) : InSub T T.root w := ⟨T.depth w, T.iterate_depth w⟩

theorem trans {u v w : V} (h1 : InSub T u v) (h2 : InSub T v w) : InSub T u w := by
  obtain ⟨m, hm⟩ := h1; obtain ⟨n, hn⟩ := h2
  exact ⟨m + n, by rw [Function.iterate_add_apply, hn, hm]⟩

theorem of_parent {v w : V} (h : InSub T v (T.parent w)) : InSub T v w := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

theorem parent_self (w : V) : InSub T (T.parent w) w := ⟨1, rfl⟩

theorem depth_le {v w : V} (h : InSub T v w) : T.depth v ≤ T.depth w := by
  obtain ⟨n, rfl⟩ := h
  rw [T.depth_iterate]; omega

theorem eq_of_depth {v w : V} (h : InSub T v w) (hd : T.depth w ≤ T.depth v) : v = w := by
  obtain ⟨n, rfl⟩ := h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · have h1 := T.depth_iterate w n
    by_cases hw : T.parent^[n] w = T.root
    · rw [hw, T.depth_root] at hd
      have : w = T.root := (RootedTree.depth_eq_zero_iff).1 (by omega)
      rw [hw, this]
    · have := RootedTree.depth_of_iterate_eq (T := T) rfl hw
      omega

/-- The ancestor of `w` at a given depth is unique. -/
theorem unique {v v' w : V} (h : InSub T v w) (h' : InSub T v' w) (hd : T.depth v = T.depth v') :
    v = v' := by
  obtain ⟨n, rfl⟩ := h; obtain ⟨m, rfl⟩ := h'
  rcases le_total n m with hnm | hnm
  · have e : T.parent^[m] w = T.parent^[m - n] (T.parent^[n] w) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    rw [e] at hd ⊢
    exact (eq_of_depth ⟨m - n, rfl⟩ (le_of_eq hd)).symm
  · have e : T.parent^[n] w = T.parent^[n - m] (T.parent^[m] w) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    rw [e] at hd ⊢
    exact eq_of_depth ⟨n - m, rfl⟩ (le_of_eq hd.symm)

/-- Going up from `w ≠ v` inside `T(v)` stays in `T(v)`. -/
theorem parent_of_ne {v w : V} (h : InSub T v w) (hne : w ≠ v) : InSub T v (T.parent w) := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | n
  · exact absurd hn hne
  · exact ⟨n, by rw [Function.iterate_succ_apply] at hn; exact hn⟩

/-- A child of a node of `T(v)` is in `T(v)`. -/
theorem child {v w x : V} (h : InSub T v w) (hx : T.parent x = w) : InSub T v x :=
  of_parent (hx ▸ h)

theorem ne_root_of_depth {v w : V} (h : InSub T v w) (hv : v ≠ T.root) : w ≠ T.root := by
  rintro rfl
  exact hv (eq_of_depth h (by rw [T.depth_root]; omega))

/-- Two nodes of the same depth have disjoint subtrees. -/
theorem disjoint {v v' w : V} (h : InSub T v w) (h' : InSub T v' w) (hd : T.depth v = T.depth v') :
    v = v' := unique h h' hd

end InSub

theorem depth_parent_le (w : V) : T.depth (T.parent w) ≤ T.depth w :=
  InSub.depth_le (InSub.parent_self w)

theorem depth_parent_of_ne {w : V} (hw : w ≠ T.root) : T.depth (T.parent w) + 1 = T.depth w :=
  T.depth_parent w hw

section towards

variable {T}

theorem iterate_towards {v a : V} (h : InSub T v a) (hlt : T.depth v < T.depth a) :
    T.parent^[T.depth a - T.depth v] a = v := by
  obtain ⟨n, hn⟩ := h
  by_cases hv' : v = T.root
  · subst hv'; exact T.iterate_eq_root_of_le (by rw [T.depth_root]; omega)
  · have hv := hv'
    have := RootedTree.depth_of_iterate_eq (T := T) hn hv
    have e : T.depth a - T.depth v = n := by omega
    rw [e, hn]

theorem parent_towards {v a : V} (h : InSub T v a) (hlt : T.depth v < T.depth a) :
    T.parent (towards T v a) = v := by
  unfold towards
  rw [← Function.iterate_succ_apply' T.parent]
  rw [show (T.depth a - T.depth v - 1).succ = T.depth a - T.depth v by omega]
  exact iterate_towards h hlt

theorem towards_inSub {v a : V} : InSub T (towards T v a) a := ⟨_, rfl⟩

theorem depth_towards {v a : V} (_h : InSub T v a) (hlt : T.depth v < T.depth a) :
    T.depth (towards T v a) = T.depth v + 1 := by
  unfold towards; rw [T.depth_iterate]; omega

theorem towards_ne_root {v a : V} (h : InSub T v a) (hlt : T.depth v < T.depth a) :
    towards T v a ≠ T.root := by
  intro h'
  have := depth_towards (T := T) h hlt
  rw [h', T.depth_root] at this; omega

theorem inSub_towards {v a : V} (h : InSub T v a) (hlt : T.depth v < T.depth a) :
    InSub T v (towards T v a) := by
  have := InSub.parent_self (T := T) (towards T v a)
  rwa [parent_towards h hlt] at this

end towards

end Podc.TreeExplorationBFDN
