import Papers.PODC2024.SSLeaderElectionDirected.Termination

/-!
# Silent self-stabilization of C-MAI (Lemmas 2, 3 and Theorem 1)

* `target_le_of_terminal` (Lemma 2): in a terminal key configuration no key is below its target.
* `eq_target_of_terminal` (Lemma 3): if `α ≥ MAD`, every terminal key configuration is the target.
* `theorem1`: C-MAI is silent self-stabilizing under the distributed unfair daemon for
  `∀ p, MinOk(p)`.
-/

set_option linter.unusedSectionVars false

open Cslib.SelfStabilization Relation

namespace Papers.PODC2024.SSLeaderElectionDirected

namespace CMAI

variable {V : Type*} [Fintype V] {G : Digraph V} {D : Type*} [LinearOrder D]
  {α : ℕ} {I : V → D} {K : V → Key D}

/-- **Lemma 2.** In a terminal configuration, `p.K ⪰ (MinI(p), Mind(p))` for every `p`. -/
theorem target_le_of_terminal (hT : ∀ p, bestKey G α I K p = K p) (p : V) :
    target G I p ≤ K p := by
  classical
  by_contra h
  let B := Finset.univ.filter fun p => K p < target G I p
  have hB : B.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩⟩
  obtain ⟨pm, hpm, hmin⟩ := B.exists_min_image K hB
  have hpm' : K pm < target G I pm := (Finset.mem_filter.mp hpm).2
  have hall : ∀ k ∈ keySet G α I K pm, K pm < k := by
    intro k hk
    rcases mem_keySet.mp hk with rfl | ⟨q, hq, -, rfl⟩
    · exact lt_of_lt_of_le hpm' (selfKey_ge_target pm)
    · by_cases hqB : q ∈ B
      · exact lt_of_le_of_lt (hmin q hqB) (Key.lt_succ _)
      · have hq' : target G I q ≤ K q := by
          simpa [B] using hqB
        exact lt_of_lt_of_le hpm' ((target_le_succ_target hq).trans (Key.succ_le_succ hq'))
  have := hall _ (bestKey_mem (G := G) (α := α) (I := I) (K := K) (p := pm))
  rw [hT pm] at this
  exact lt_irrefl _ this

/-- **Lemma 3.** If `α ≥ MAD`, then in a terminal configuration `MinOk(p)` holds for every `p`. -/
theorem eq_target_of_terminal (hα : MADLe G α) (hT : ∀ p, bestKey G α I K p = K p) (p : V) :
    K p = target G I p := by
  induction h : mind G I p using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    apply le_antisymm _ (target_le_of_terminal hT p)
    rw [← hT p]
    apply bestKey_le
    cases n with
    | zero =>
      have hm : minI G I p = I p := ((mind_eq_zero_iff (G := G)).mp h).symm
      have : target G I p = ⟨I p, 0⟩ := Key.ext hm h
      rw [this]; exact selfKey_mem_keySet
    | succ m =>
      obtain ⟨q, hq, hmin, hmq⟩ := exists_pred_of_mind h
      have hKq : K q = target G I q := ih m (by omega) q hmq
      have heq : target G I p = (K q).succ := by
        rw [hKq]; exact Key.ext hmin.symm (by simp [target, hmq, h])
      have hle := mind_le_of_madLe (I := I) hα p
      rw [heq]
      exact succ_mem_keySet hq (by rw [hKq]; simp only [target]; omega)

/-- Conversely, the target configuration is terminal (if `α ≥ MAD`). -/
theorem bestKey_target (hα : MADLe G α) (p : V) :
    bestKey G α I (target G I) p = target G I p := by
  apply le_antisymm
  · apply bestKey_le
    rcases h : mind G I p with _ | m
    · have hm : minI G I p = I p := ((mind_eq_zero_iff (G := G)).mp h).symm
      have : target G I p = ⟨I p, 0⟩ := Key.ext hm h
      rw [this]; exact selfKey_mem_keySet
    · obtain ⟨q, hq, hmin, hmq⟩ := exists_pred_of_mind h
      have heq : target G I p = (target G I q).succ := Key.ext hmin.symm (by simp [target, hmq, h])
      have hle := mind_le_of_madLe (I := I) hα p
      rw [heq]
      exact succ_mem_keySet hq (by simp only [target]; omega)
  · apply le_bestKey
    intro k hk
    rcases mem_keySet.mp hk with rfl | ⟨q, hq, -, rfl⟩
    · exact selfKey_ge_target p
    · exact target_le_succ_target hq

/-! ### The algorithm C-MAI in the atomic-state model -/

variable (G α) in
/-- Algorithm C-MAI(D, ≺, I): the action `ReplaceKey` of every process. -/
noncomputable def next (I : V → D) (γ : V → CState D α) (p : V) : CState D α :=
  ⟨bestKey G α I (fun q => (γ q).1) p, bestKey_d_le⟩

theorem enabled_iff {γ : V → CState D α} {p : V} :
    Enabled (next G α I) γ p ↔ bestKey G α I (fun q => (γ q).1) p ≠ (γ p).1 := by
  simp [Enabled, next, Subtype.ext_iff]

theorem terminal_iff {γ : V → CState D α} :
    Terminal (next G α I) γ ↔ ∀ p, bestKey G α I (fun q => (γ q).1) p = (γ p).1 := by
  simp [Terminal, next, Subtype.ext_iff]

/-- An execution of C-MAI is a run with constant inputs. -/
theorem run_of_isRun {e : ℕ → V → CState D α} {S : ℕ → Set V} (h : IsUnfairRun (next G α I) e S) :
    Run G α (fun _ => I) (fun t p => (e t p).1) S where
  move t p hp := by rw [h.move t p hp]; rfl
  stay t p hp := by rw [h.stay t p hp]

/-- **Theorem 1.** If `α ≥ MAD`, C-MAI(D, ≺, I) is silent self-stabilizing in `G` under the
distributed unfair daemon for the predicate `∀ p, MinOk(p)`, i.e. `p.K = (MinI(p), Mind(p))`. -/
theorem theorem1 (hα : MADLe G α) :
    SilentSelfStabilizing (next G α I) (IsUnfairExec (next G α I))
      (fun γ => ∀ p, (γ p).1 = target G I p) := by
  refine ⟨fun e ⟨S, hS⟩ => ?_, fun γ hγ p => ?_⟩
  · obtain ⟨T', -, hT'⟩ := (run_of_isRun hS).eventually_const (T := 0) (fun _ _ => rfl)
    refine ⟨T', hS.terminal_of_const fun t ht => funext fun p => Subtype.ext ?_⟩
    exact congrFun (hT' t ht) p
  · exact eq_target_of_terminal hα (terminal_iff.mp hγ) p

end CMAI

end Papers.PODC2024.SSLeaderElectionDirected
