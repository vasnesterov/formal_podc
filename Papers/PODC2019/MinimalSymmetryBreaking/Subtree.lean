import Papers.PODC2019.MinimalSymmetryBreaking.Packing

/-!
# Non-vacuity: finite subtrees of every size

`IsSubtree V`: `V` contains the origin and the parent of each of its other nodes, so the subgraph of
the oriented tree induced by `V` is a (connected) tree. For every `K` and every `n ≥ |B_K|` there is
such a `V` with `B_K ⊆ V` and `|V| = n` (`exists_subtree`); these are the instances of
Theorem 6.
-/

namespace Podc.MinimalSymmetryBreaking

open Finset Function
open scoped Classical

noncomputable section

variable {k : ℕ}

/-- `V` is a subtree containing the origin: every other node has a neighbour in `V` closer to the
origin. -/
def IsSubtree (V : Finset (Tree k)) : Prop :=
  1 ∈ V ∧ ∀ w ∈ V, w ≠ 1 → ∃ p, w * dir p ∈ V ∧ (w * dir p).norm < w.norm

lemma norm_mul_dir (w : Tree k) (p : Fin k × Bool) :
    (w * dir p).norm = (dir (p.1, !p.2) * w⁻¹).norm := by
  rw [← dir_inv, show w * dir p = ((dir p)⁻¹ * w⁻¹)⁻¹ by group, FreeGroup.norm_inv_eq]

lemma exists_mul_dir_lt (w : Tree k) (hw : w ≠ 1) : ∃ p, (w * dir p).norm + 1 = w.norm := by
  obtain ⟨p, hp⟩ := exists_dir_mul w⁻¹ (by simpa using hw)
  refine ⟨p, ?_⟩
  rw [norm_mul_dir, show (p.1, !p.2) = (p.1, !p.2) from rfl, ← dir_inv]
  rwa [FreeGroup.norm_inv_eq] at hp

lemma exists_mul_dir_gt (hk : 0 < k) (w : Tree k) : ∃ p, (w * dir p).norm = w.norm + 1 := by
  set d : Fin k := ⟨0, hk⟩
  by_contra h
  push_neg at h
  have h1 := h (d, true)
  have h2 := h (d, false)
  rw [norm_mul_dir, norm_dir_mul] at h1 h2
  rw [← FreeGroup.norm_inv_eq (x := w)] at h1 h2
  split_ifs at h1 h2 with e1 e2 <;> simp_all

lemma isSubtree_Ball (K : ℕ) : IsSubtree (Ball K : Finset (Tree k)) := by
  refine ⟨by simp, fun w hw h1 => ?_⟩
  obtain ⟨p, hp⟩ := exists_mul_dir_lt w h1
  refine ⟨p, ?_, by omega⟩
  rw [mem_Ball] at hw ⊢; omega

/-- **Non-vacuity of Theorem 6.** For every `K` and `n ≥ |B_K|` there is an `n`-node subtree
containing `B_K`. -/
theorem exists_subtree (hk : 0 < k) (K : ℕ) :
    ∀ n, (Ball K : Finset (Tree k)).card ≤ n →
      ∃ V : Finset (Tree k), IsSubtree V ∧ Ball K ⊆ V ∧ V.card = n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact ⟨Ball K, isSubtree_Ball K, subset_rfl, rfl⟩
  | succ m _ ih =>
    obtain ⟨V, hV, hKV, hcard⟩ := ih
    have hne : V.Nonempty := ⟨1, hV.1⟩
    obtain ⟨v, hv, hmax⟩ := V.exists_max_image FreeGroup.norm hne
    obtain ⟨p, hp⟩ := exists_mul_dir_gt hk v
    set w := v * dir p
    have hw : w ∉ V := fun h => by have := hmax w h; omega
    refine ⟨insert w V, ⟨mem_insert_of_mem hV.1, fun u hu h1 => ?_⟩,
      hKV.trans (subset_insert _ _), by rw [card_insert_of_notMem hw, hcard]⟩
    rcases mem_insert.1 hu with rfl | hu
    · refine ⟨(p.1, !p.2), mem_insert_of_mem ?_, ?_⟩
      · rw [show w * dir (p.1, !p.2) = v by simp [w, ← dir_inv]]; exact hv
      · rw [show w * dir (p.1, !p.2) = v by simp [w, ← dir_inv]]; omega
    · obtain ⟨q, hq, hlt⟩ := hV.2 u hu h1
      exact ⟨q, mem_insert_of_mem hq, hlt⟩

end

end Podc.MinimalSymmetryBreaking
