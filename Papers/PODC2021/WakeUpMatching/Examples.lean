import Papers.PODC2021.WakeUpMatching.Theorem63

/-!
# Theorem 6.3: both values occur in the load-one case

`K₂` has minimum NAF load `1` and matching cover number `1`; the triangle `K₃` has minimum NAF
load `1` and matching cover number `2`. So the exception "if the NAF-load of `G` equals 1, the
matching cover number of `G` can be 1 or 2" in Theorem 6.3 is genuine, and the hypotheses of
`theorem_6_3_load_one` are satisfiable.
-/

namespace Podc.WakeUpMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem one_le_load [Nonempty V] {f : V → V} : 1 ≤ load f := by
  obtain ⟨v⟩ := ‹Nonempty V›
  exact le_trans (show 1 ≤ inDeg f (f v) from card_pos.2 ⟨v, by simp⟩) (inDeg_le_load f (f v))

theorem one_le_matchingCoverNumber [Nonempty V] (hG : ∀ v, ∃ w, G.Adj v w) :
    1 ≤ matchingCoverNumber G :=
  (one_le_load (f := (minNAFLoad_spec hG).choose)).trans
    ((minNAFLoad_spec hG).choose_spec.2.symm ▸ minNAFLoad_le_matchingCoverNumber hG)

/-- If some NAF has load `1`, the minimum NAF load is `1`. -/
theorem minNAFLoad_eq_one [Nonempty V] {f : V → V} (hf : IsNAF G f) (h1 : load f ≤ 1) :
    minNAFLoad G = 1 := by
  have := minNAFLoad_le hf
  obtain ⟨g, hg, hgl⟩ := minNAFLoad_spec (exists_naf_iff.1 ⟨f, hf⟩)
  have := one_le_load (f := g)
  omega

/-- `K₂`: minimum NAF load `1`, matching cover number `1`. -/
theorem k2 : minNAFLoad (⊤ : SimpleGraph (Fin 2)) = 1 ∧
    matchingCoverNumber (⊤ : SimpleGraph (Fin 2)) = 1 := by
  have hf : IsNAF (⊤ : SimpleGraph (Fin 2)) (fun v => v + 1) := by
    intro v; fin_cases v <;> decide
  have hl : load (fun v : Fin 2 => v + 1) ≤ 1 := load_le_iff.2 (by decide)
  refine ⟨minNAFLoad_eq_one hf hl, le_antisymm ?_ (one_le_matchingCoverNumber fun v => ⟨_, hf v⟩)⟩
  -- the single edge is a perfect matching
  let M : (⊤ : SimpleGraph (Fin 2)).Subgraph := ⊤
  have hM : M.IsMatching := by
    intro v _
    refine ⟨v + 1, by simp [M], fun y hy => ?_⟩
    simp [M] at hy; omega
  exact matchingCoverNumber_le (M := fun _ : Fin 1 => M) ⟨fun _ => hM, fun v => ⟨0, by simp [M]⟩⟩

/-- `K₃`: minimum NAF load `1`, matching cover number `2`. -/
theorem k3 : minNAFLoad (⊤ : SimpleGraph (Fin 3)) = 1 ∧
    matchingCoverNumber (⊤ : SimpleGraph (Fin 3)) = 2 := by
  have hf : IsNAF (⊤ : SimpleGraph (Fin 3)) (fun v => v + 1) := by
    intro v; fin_cases v <;> decide
  have hl : load (fun v : Fin 3 => v + 1) ≤ 1 := load_le_iff.2 (by decide)
  have hG : ∀ v, ∃ w, (⊤ : SimpleGraph (Fin 3)).Adj v w := fun v => ⟨_, hf v⟩
  have h1 := minNAFLoad_eq_one hf hl
  refine ⟨h1, (theorem_6_3_load_one hG h1).resolve_left fun hmc => ?_⟩
  -- one matching covering three vertices would be a perfect matching of `K₃`
  have hmem : matchingCoverNumber (⊤ : SimpleGraph (Fin 3)) ∈
      {k | ∃ M : Fin k → (⊤ : SimpleGraph (Fin 3)).Subgraph, IsMatchingCover _ M} :=
    Nat.sInf_mem ⟨_, (exists_cover_of_naf (le_refl 2) hf
      (fun w => (inDeg_le_load _ w).trans (hl.trans (by norm_num))))⟩
  rw [hmc] at hmem
  obtain ⟨M, hM⟩ := hmem
  have hperf : (M 0).IsPerfectMatching := by
    refine ⟨hM.1 0, fun v => ?_⟩
    obtain ⟨i, hi⟩ := hM.2 v
    rwa [Subsingleton.elim i 0] at hi
  have := hperf.even_card
  simp only [Fintype.card_fin] at this
  exact (Nat.not_even_iff_odd.2 (by decide)) this

end Podc.WakeUpMatching
