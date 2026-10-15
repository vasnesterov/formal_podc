import Papers.PODC2025.ByzantineStableMatching.Groups

/-!
# Lemma 7: one-sided / bipartite unauthenticated lower bound

Paper: for `n = 4` (`k = 2`) no protocol achieves sSM in a one-sided unauthenticated network with
`tL = 0`, `tR = 1`; proof via the 8-cycle `a1-c1-b1-d1-a2-c2-b2-d2-a1` (Fig. 3).

We prove directly, for every `k ≥ 2` and every network `G` without edges inside `L` (in particular
one-sided and bipartite networks), that sSM is unsolvable when `2 tR ≥ k` (for any `tL`, even `0`).
`L` is split into two nonempty groups `a`, `b`, `R` into two nonempty groups `c`, `d` of size
`≤ ⌈k/2⌉`. Double cover: the edges `a–d` cross between the copies, all others stay inside a copy;
this is the paper's 8-cycle (plus the `c–d` edges of the one-sided network, which may stay inside a
copy since `c` and `d` are never honest together). Unlike the paper we do not need to first reduce the
one-sided case to the bipartite one: the cover handles the extra edges directly.
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum

variable {k : ℕ}

namespace Lemma7

/-- Is `p` in group `a` (`L`, label `0`)? -/
def isA (gL : Fin k → Fin 2) : Party k → Bool
  | inl i => decide (gL i = 0)
  | inr _ => false

/-- Is `p` in group `d` (`R`, label `1`)? -/
def isD (gR : Fin k → Fin 2) : Party k → Bool
  | inl _ => false
  | inr j => decide (gR j = 1)

/-- The double cover: `a–d` edges cross. `L`-nodes favour `jC`; `R`-nodes of copy `false` favour
`iA`, of copy `true` favour `iB`. -/
def cover (gL gR : Fin k → Fin 2) (iA iB jC : Fin k) :
    CoverSystem (Party k) (Fin k) (Party k × Bool) where
  φ := Prod.fst
  nbr q p := some (p, xor q.2 ((isA gL q.1 && isD gR p) || (isD gR q.1 && isA gL p)))
  xq q := match q with
    | (inl _, _) => jC
    | (inr _, c) => if c then iB else iA

lemma fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

/-- The general form of Lemma 7. -/
theorem not_solvable_of_groups (G : SimpleGraph (Party k)) (hG : ∀ i i', ¬ G.Adj (inl i) (inl i'))
    {tL tR : ℕ} (gL gR : Fin k → Fin 2) (iA iB jC : Fin k) (hA : gL iA = 0) (hB : gL iB = 1)
    (hC : gR jC = 0) (hgR : ∀ z, {j | gR j = z}.ncard ≤ tR) :
    ¬ Solvable G (thresholds k tL tR) (sSM k) := by
  rintro ⟨M, alg, halg⟩
  set C := cover gL gR iA iB jC
  set BD : Set (Party k) := {p | isD gR p = true}
  set BC : Set (Party k) := {p | Sum.elim (fun _ => False) (fun j => gR j = 0) p}
  have hBD : BD ∈ thresholds k tL tR := by
    refine ⟨?_, ?_⟩
    · have : inl ⁻¹' BD = ∅ := by ext i; simp [BD, isD]
      rw [this, Set.ncard_empty]; exact Nat.zero_le _
    · have : inr ⁻¹' BD = {j | gR j = 1} := by ext j; simp [BD, isD]
      rw [this]; exact hgR 1
  have hBC : BC ∈ thresholds k tL tR := by
    refine ⟨?_, ?_⟩
    · have : inl ⁻¹' BC = ∅ := by ext i; simp [BC]
      rw [this, Set.ncard_empty]; exact Nat.zero_le _
    · have : inr ⁻¹' BC = {j | gR j = 0} := by ext j; simp [BC]
      rw [this]; exact hgR 0
  -- Lift into one copy, the group `d` being Byzantine.
  have liftCopy : ∀ c : Bool, C.Lift G BD (fun p => (p, c)) := by
    intro c
    refine ⟨fun _ _ => rfl, fun p q hp hq _ => ?_⟩
    simp only [BD, Set.mem_ofPred_eq, Bool.not_eq_true] at hp hq
    simp [C, cover, hp, hq]
  have hjC : inr jC ∉ BD := by simp [BD, isD, hC]
  -- Scenario 1: copy `false`, `a1` and `c1` are mutual favourites.
  have h1 : C.Decides G alg (inl iA, false) (some jC) := by
    have hs := halg (C.scenario G alg BD (fun p => (p, false)) fun _ => jC) hBD (fun _ _ _ h => h)
    have hiA : inl iA ∉ BD := by simp [BD, isD]
    have := (hs.2 iA jC hiA hjC (by rw [C.scenario_input_of_not_mem _ hiA]; rfl)
      (by rw [C.scenario_input_of_not_mem _ hjC]; rfl)).1
    exact (C.decides_scenario_iff (liftCopy false) _ hiA _).mp this
  -- Scenario 2: copy `true`, `b2` and `c2` are mutual favourites.
  have h2 : C.Decides G alg (inl iB, true) (some jC) := by
    have hs := halg (C.scenario G alg BD (fun p => (p, true)) fun _ => jC) hBD (fun _ _ _ h => h)
    have hiB : inl iB ∉ BD := by simp [BD, isD]
    have := (hs.2 iB jC hiB hjC (by rw [C.scenario_input_of_not_mem _ hiB]; rfl)
      (by rw [C.scenario_input_of_not_mem _ hjC]; rfl)).1
    exact (C.decides_scenario_iff (liftCopy true) _ hiB _).mp this
  -- Scenario 3: group `c` Byzantine; `a1`, `b2`, `d2` honest.
  set σ : Party k → Party k × Bool := fun p => (p, Sum.elim (fun i => decide (gL i = 1)) (fun _ => true) p)
  have hL : C.Lift G BC σ := by
    refine ⟨fun _ _ => rfl, fun p q hp hq hadj => ?_⟩
    rcases p with i | j <;> rcases q with i' | j'
    · exact absurd hadj (hG _ _)
    · have hj' : gR j' = 1 := by
        simp only [BC, Set.mem_ofPred_eq, Sum.elim_inr] at hq
        rcases fin2_cases (gR j') with h | h
        · exact absurd h hq
        · exact h
      rcases fin2_cases (gL i) with h | h <;> simp [σ, C, cover, isA, isD, hj', h]
    · have hj : gR j = 1 := by
        simp only [BC, Set.mem_ofPred_eq, Sum.elim_inr] at hp
        rcases fin2_cases (gR j) with h | h
        · exact absurd h hp
        · exact h
      rcases fin2_cases (gL i') with h | h <;> simp [σ, C, cover, isA, isD, hj, h]
    · simp [σ, C, cover, isA, isD]
  have hs := halg (C.scenario G alg BC σ fun _ => jC) hBC (fun _ _ _ h => h)
  have hiA : inl iA ∉ BC := by simp [BC]
  have hiB : inl iB ∉ BC := by simp [BC]
  have dA := (C.decides_scenario_iff (alg := alg) hL (fun _ => jC) hiA _).mpr
    (by simpa [σ, hA] using h1)
  have dB := (C.decides_scenario_iff (alg := alg) hL (fun _ => jC) hiB _).mpr
    (by simpa [σ, hB] using h2)
  have hne : (inl iA : Party k) ≠ inl iB := by
    intro h; cases h; rw [hA] at hB; exact absurd hB (by decide)
  exact hs.1.nonCompetition _ _ hiA hiB hne _ _ dA dB rfl

end Lemma7

/-- **Lemma 7** (generalized to every `k ≥ 2`): in any network without edges inside `L` (in
particular one-sided and bipartite networks), if `tR ≥ k/2` no unauthenticated protocol achieves sSM,
whatever `tL`. -/
theorem lemma7 (G : SimpleGraph (Party k)) (hG : ∀ i i', ¬ G.Adj (inl i) (inl i')) {tL tR : ℕ}
    (hk : 2 ≤ k) (hR : k ≤ 2 * tR) : ¬ Solvable G (thresholds k tL tR) (sSM k) := by
  set t := (k + 1) / 2
  obtain ⟨⟨jC, hC⟩, -, hgR⟩ :=
    split2_spec (k := k) (t := t) (x := (0 : Fin 2)) (y := 1) (by decide) (by omega) (by omega)
      (by omega)
  obtain ⟨⟨iA, hA⟩, ⟨iB, hB⟩, -⟩ :=
    split2_spec (k := k) (t := k - 1) (x := (0 : Fin 2)) (y := 1) (by decide) (by omega) (by omega)
      (by omega)
  exact Lemma7.not_solvable_of_groups G hG _ _ iA iB jC hA hB hC
    (fun z => (hgR z).trans (by omega))

end Papers.PODC2025.ByzantineStableMatching
