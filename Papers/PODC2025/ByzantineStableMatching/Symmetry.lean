import Papers.PODC2025.ByzantineStableMatching.Problem
import Cslib.Computability.Distributed.Byzantine.LockStep.Relabel

/-!
# Swapping the two sides

The problems `sSM` and `bSM` are symmetric under exchanging `L` and `R`; we transport solvability
along `Equiv.sumComm` (via the generic relabelling lemmas of `Cslib.Byzantine.LockStep.Relabel`). This gives
the "symmetric" cases the paper leaves to the reader.
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum

variable {k : ℕ}

/-- Exchange of the two sides. -/
abbrev swapE : Party k ≃ Party k := Equiv.sumComm (Fin k) (Fin k)

@[simp] lemma swapE_inl (i : Fin k) : (swapE (inl i) : Party k) = inr i := rfl
@[simp] lemma swapE_inr (i : Fin k) : (swapE (inr i) : Party k) = inl i := rfl
@[simp] lemma swapE_symm : (swapE : Party k ≃ Party k).symm = swapE := rfl

lemma swap_image_thresholds {tL tR : ℕ} {B : Set (Party k)} (hB : B ∈ thresholds k tR tL) :
    swapE '' B ∈ thresholds k tL tR := by
  have h1 : inl ⁻¹' (swapE '' B) = (inr ⁻¹' B : Set (Fin k)) := by
    ext i; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨p, hp, hpi⟩
      rcases p with j | j <;> simp at hpi
      subst hpi; exact hp
    · intro h; exact ⟨inr i, h, rfl⟩
  have h2 : inr ⁻¹' (swapE '' B) = (inl ⁻¹' B : Set (Fin k)) := by
    ext i; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨p, hp, hpi⟩
      rcases p with j | j <;> simp at hpi
      subst hpi; exact hp
    · intro h; exact ⟨inl i, h, rfl⟩
  exact ⟨h1 ▸ hB.2, h2 ▸ hB.1⟩

lemma mem_swap_image {H : Set (Party k)} {p : Party k} : swapE p ∈ swapE '' H ↔ p ∈ H :=
  Set.mem_image_equiv.trans (by simp)

lemma partner_swap (p : Party k) (z : Fin k) : partner (swapE p) z = swapE (partner p z) := by
  rcases p with i | i <;> rfl

lemma commonProps_swap {H : Set (Party k)} {dec : Party k → Option (Fin k) → Prop}
    (h : CommonProps (swapE '' H) (fun p' o => dec (swapE.symm p') o)) : CommonProps H dec := by
  obtain ⟨hT, hS, hN⟩ := h
  refine ⟨fun p hp => ?_, fun i j hi hj => ?_, fun p q hp hq hpq z z' hz hz' => ?_⟩
  · simpa using hT (swapE p) (mem_swap_image.mpr hp)
  · have := hS j i (mem_swap_image.mpr hj) (mem_swap_image.mpr hi)
    simp only [swapE_symm, swapE_inl, swapE_inr] at this
    exact this.symm
  · have := hN (swapE p) (swapE q) (mem_swap_image.mpr hp) (mem_swap_image.mpr hq)
      (fun h => hpq (swapE.injective h)) z z' (by simpa using hz) (by simpa using hz')
    rw [partner_swap, partner_swap] at this
    exact fun h => this (by rw [h])

lemma sSM_swap (x : Party k → Fin k) (H : Set (Party k)) (dec : Party k → Option (Fin k) → Prop)
    (h : sSM k (x ∘ swapE.symm) (swapE '' H) (fun p' o => dec (swapE.symm p') o)) :
    sSM k x H dec := by
  refine ⟨commonProps_swap h.1, fun i j hi hj hxi hxj => ?_⟩
  have := h.2 j i (mem_swap_image.mpr hj) (mem_swap_image.mpr hi) (by simpa using hxj)
    (by simpa using hxi)
  simp only [swapE_symm, swapE_inl, swapE_inr] at this
  exact ⟨this.2, this.1⟩

lemma bSM_swap (x : Party k → Equiv.Perm (Fin k)) (H : Set (Party k))
    (dec : Party k → Option (Fin k) → Prop)
    (h : bSM k (x ∘ swapE.symm) (swapE '' H) (fun p' o => dec (swapE.symm p') o)) :
    bSM k x H dec := by
  refine ⟨commonProps_swap h.1, fun i j oi oj hi hj hoi hoj hb => ?_⟩
  exact h.2 j i oj oi (mem_swap_image.mpr hj) (mem_swap_image.mpr hi) (by simpa using hoj)
    (by simpa using hoi) ⟨by simpa using hb.2, by simpa using hb.1⟩

lemma comap_swap_adj (G : SimpleGraph (Party k)) (p q : Party k) :
    G.Adj (swapE p) (swapE q) ↔ (G.comap swapE).Adj p q := Iff.rfl

/-- Swapping sides (sSM, unauthenticated). -/
theorem sSM_solvable_swap {G : SimpleGraph (Party k)} {tL tR : ℕ}
    (h : Solvable G (thresholds k tL tR) (sSM k)) :
    Solvable (G.comap swapE) (thresholds k tR tL) (sSM k) :=
  Solvable.relabel swapE (comap_swap_adj G) h (fun _ hB => swap_image_thresholds hB) sSM_swap

/-- Swapping sides (sSM, authenticated). -/
theorem sSM_solvableAuth_swap {G : SimpleGraph (Party k)} {tL tR : ℕ}
    (h : SolvableAuth G (thresholds k tL tR) (sSM k)) :
    SolvableAuth (G.comap swapE) (thresholds k tR tL) (sSM k) :=
  SolvableAuth.relabel swapE (comap_swap_adj G) h (fun _ hB => swap_image_thresholds hB) sSM_swap

/-- Swapping sides (bSM, unauthenticated). -/
theorem bSM_solvable_swap {G : SimpleGraph (Party k)} {tL tR : ℕ}
    (h : Solvable G (thresholds k tL tR) (bSM k)) :
    Solvable (G.comap swapE) (thresholds k tR tL) (bSM k) :=
  Solvable.relabel swapE (comap_swap_adj G) h (fun _ hB => swap_image_thresholds hB) bSM_swap

/-- Swapping sides (bSM, authenticated). -/
theorem bSM_solvableAuth_swap {G : SimpleGraph (Party k)} {tL tR : ℕ}
    (h : SolvableAuth G (thresholds k tL tR) (bSM k)) :
    SolvableAuth (G.comap swapE) (thresholds k tR tL) (bSM k) :=
  SolvableAuth.relabel swapE (comap_swap_adj G) h (fun _ hB => swap_image_thresholds hB) bSM_swap

lemma fully_comap_swap : (fully k).comap swapE = fully k := by
  ext p q; simp only [fully, SimpleGraph.comap_adj, SimpleGraph.top_adj]; exact (swapE (k := k)).injective.ne_iff

lemma bipartite_comap_swap : (bipartite k).comap swapE = bipartite k := by
  ext p q; rcases p with i | i <;> rcases q with j | j <;> simp

lemma oneSided_comap_swap : (oneSided k).comap swapE = oneSidedR k := by
  ext p q; rcases p with i | i <;> rcases q with j | j <;> simp

lemma oneSidedR_comap_swap : (oneSidedR k).comap swapE = oneSided k := by
  ext p q; rcases p with i | i <;> rcases q with j | j <;> simp

end Papers.PODC2025.ByzantineStableMatching
