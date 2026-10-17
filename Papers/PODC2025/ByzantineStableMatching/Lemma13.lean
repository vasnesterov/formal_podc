import Papers.PODC2025.ByzantineStableMatching.Groups

/-!
# Lemma 13: authenticated one-sided / bipartite lower bound

Paper: if `tR = k` and `tL ≥ k/3`, bSM is impossible in a one-sided network, even with signatures.
The paper's proof first reduces to `k = 3` via "Corollary 2 and Lemma 3", which is incorrect: Lemma 3
only gives `⌊k/⌈k/3⌉⌋` Byzantine parties on the right of the 6-party system, which is `< 3` e.g. for
`k = 4, 5, 7` (and Corollary 2 is about unauthenticated bipartite networks). We instead run the
paper's split-brain argument (Fig. 4) directly for every `k ≥ 2`: `L` is split into groups `a`, `b`, `c`
of size `≤ ⌈k/3⌉` (`a`, `c` nonempty; `b` may be empty). All of `R` and group `b` are Byzantine and
each simulates two copies of itself; copy `1` talks only to `a` (and treats `c` as crashed), copy `2`
only to `c`. The simulation only relays honest signatures, so it is a legal authenticated adversary
(`CoverSystem.scenario_authValid`).
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum

variable {k : ℕ}

namespace Lemma13

/-- The split-brain system: node `(p, c)` is copy `c` of `p` (`false` = group 1, `true` = group 2).
Copies of group `a` only exist in group 1, copies of group `c` only in group 2 (the other copies are
never listened to). `L`-nodes favour `jV`; `R`-nodes of copy `false` favour `iA`, of copy `true`
favour `iC`. -/
def cover (gL : Fin k → Fin 3) (iA iC jV : Fin k) :
    CoverSystem (Party k) (Fin k) (Party k × Bool) :=
  CoverSystem.doubleCover
    (fun _ c p => match p with
      | inl i => if gL i = 0 then (if c then none else some false)
                 else if gL i = 2 then (if c then some true else none)
                 else some c
      | inr _ => some c)
    fun q => match q with
      | (inl _, _) => jV
      | (inr _, c) => if c then iC else iA

/-- The general form of Lemma 13 (for sSM). -/
theorem not_solvableAuth_of_groups (G : SimpleGraph (Party k))
    (hG : ∀ i i', ¬ G.Adj (inl i) (inl i')) {tL tR : ℕ} (hR : k ≤ tR)
    (gL : Fin k → Fin 3) (iA iC jV : Fin k) (hA : gL iA = 0) (hC : gL iC = 2)
    (hgL : ∀ z, {i | gL i = z}.ncard ≤ tL) :
    ¬ SolvableAuth G (thresholds k tL tR) (sSM k) := by
  rintro ⟨M, S, A, alg, hU, halg⟩
  set C := cover gL iA iC jV
  -- Byzantine group `z` of `L` only (crashed), or group `z` of `L` plus all of `R`.
  have hZL : ∀ z, {p : Party k | Sum.elim (fun i => gL i = z) (fun _ => False) p} ∈
      thresholds k tL tR := by
    intro z; refine ⟨?_, ?_⟩
    · exact (hgL z).trans_eq' (by congr 1)
    · have : inr ⁻¹' {p : Party k | Sum.elim (fun i => gL i = z) (fun _ => False) p} = ∅ := by
        ext; simp
      rw [this, Set.ncard_empty]; exact Nat.zero_le _
  have hZ3 : {p : Party k | Sum.elim (fun i => gL i = 1) (fun _ => True) p} ∈
      thresholds k tL tR := by
    refine ⟨(hgL 1).trans_eq' (by congr 1), ?_⟩
    have : inr ⁻¹' {p : Party k | Sum.elim (fun i => gL i = 1) (fun _ => True) p} = Set.univ := by
      ext; simp
    rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]; exact hR
  -- Scenario A (Fig. 4a): `c` crashed, everybody else honest, copy `false`.
  have hA' : C.Decides G alg (inl iA, false) (some jV) := by
    set B := {p : Party k | Sum.elim (fun i => gL i = 2) (fun _ => False) p}
    have hL : C.Lift G B (fun p => (p, false)) := by
      refine ⟨fun _ _ => rfl, fun p q hp _ _ => ?_⟩
      rcases p with i | j
      · have : gL i ≠ 2 := by simpa [B] using hp
        simp only [C, cover, CoverSystem.doubleCover]
        split_ifs <;> simp_all
      · rfl
    have hV : (C.scenario G alg B (fun p => (p, false)) fun _ => jV).AuthValid G alg A := by
      intro r b q m hb hq _ hm
      exfalso
      rcases b with i | j
      · have : gL i = 2 := by simpa [B] using hb
        simp [CoverSystem.scenario, C, cover, CoverSystem.doubleCover, this] at hm
      · simp [B] at hb
    have hs := halg _ (hZL 2) (fun _ _ _ h => h) hV
    have hiA : inl iA ∉ B := by simp [B, hA]
    have hjV : inr jV ∉ B := by simp [B]
    have := (hs.2 iA jV hiA hjV (by rw [C.scenario_input_of_not_mem _ hiA]; rfl)
      (by rw [C.scenario_input_of_not_mem _ hjV]; rfl)).1
    exact (C.decides_scenario_iff hL _ hiA _).mp this
  -- Scenario C (Fig. 4b): `a` crashed, everybody else honest, copy `true`.
  have hC' : C.Decides G alg (inl iC, true) (some jV) := by
    set B := {p : Party k | Sum.elim (fun i => gL i = 0) (fun _ => False) p}
    have hL : C.Lift G B (fun p => (p, true)) := by
      refine ⟨fun _ _ => rfl, fun p q hp _ _ => ?_⟩
      rcases p with i | j
      · have : gL i ≠ 0 := by simpa [B] using hp
        simp only [C, cover, CoverSystem.doubleCover]
        split_ifs <;> simp_all
      · rfl
    have hV : (C.scenario G alg B (fun p => (p, true)) fun _ => jV).AuthValid G alg A := by
      intro r b q m hb hq _ hm
      exfalso
      rcases b with i | j
      · have : gL i = 0 := by simpa [B] using hb
        simp [CoverSystem.scenario, C, cover, CoverSystem.doubleCover, this] at hm
      · simp [B] at hb
    have hs := halg _ (hZL 0) (fun _ _ _ h => h) hV
    have hiC : inl iC ∉ B := by simp [B, hC]
    have hjV : inr jV ∉ B := by simp [B]
    have := (hs.2 iC jV hiC hjV (by rw [C.scenario_input_of_not_mem _ hiC]; rfl)
      (by rw [C.scenario_input_of_not_mem _ hjV]; rfl)).1
    exact (C.decides_scenario_iff hL _ hiC _).mp this
  -- Scenario 3 (Fig. 4c): `b` and all of `R` Byzantine, split-brain.
  set B := {p : Party k | Sum.elim (fun i => gL i = 1) (fun _ => True) p}
  set σ : Party k → Party k × Bool :=
    fun p => (p, Sum.elim (fun i => decide (gL i = 2)) (fun _ => false) p)
  have hL : C.Lift G B σ := by
    refine ⟨fun _ _ => rfl, fun p q hp hq hadj => ?_⟩
    rcases p with i | j
    · rcases q with i' | j'
      · exact absurd hadj (hG _ _)
      · simp [B] at hq
    · simp [B] at hp
  have hV : (C.scenario G alg B σ fun _ => jV).AuthValid G alg A := by
    refine C.scenario_authValid hU hL (fun _ _ _ h => CoverSystem.doubleCover_φ_of_nbr_eq_some h)
      (fun q p q' _ hq' => ?_) _
    have h1 : q'.1 = p := CoverSystem.doubleCover_φ_of_nbr_eq_some hq'
    rcases p with i | j
    · by_cases h0 : gL i = 0
      · left
        refine ⟨inl i, by simp [B, h0], ?_⟩
        simp only [C, cover, CoverSystem.doubleCover, h0, ite_true] at hq'
        split_ifs at hq' <;> simp_all [σ]
      by_cases h2 : gL i = 2
      · left
        refine ⟨inl i, by simp [B, h2], ?_⟩
        simp only [C, cover, CoverSystem.doubleCover, h2, ite_true] at hq'
        split_ifs at hq' <;> simp_all [σ]
      · right
        have : gL i = 1 := by omega
        show q'.1 ∈ B
        rw [h1]; simp [B, this]
    · right; show q'.1 ∈ B; rw [h1]; simp [B]
  have hs := halg _ hZ3 (fun _ _ _ h => h) hV
  have hiA : inl iA ∉ B := by simp [B, hA]
  have hiC : inl iC ∉ B := by simp [B, hC]
  have dA := (C.decides_scenario_iff (alg := alg) hL (fun _ => jV) hiA _).mpr
    (by simpa [σ, hA] using hA')
  have dC := (C.decides_scenario_iff (alg := alg) hL (fun _ => jV) hiC _).mpr
    (by simpa [σ, hC] using hC')
  have hne : (inl iA : Party k) ≠ inl iC := by
    intro h; cases h; rw [hA] at hC; exact absurd hC (by decide)
  exact hs.1.nonCompetition _ _ hiA hiC hne _ _ dA dC rfl

end Lemma13

/-- **Lemma 13** (for sSM, generalized to every `k ≥ 2` and every network without edges inside `L`):
if `tR = k` (all of `R` may be Byzantine) and `tL ≥ k/3`, no authenticated protocol achieves sSM. -/
theorem lemma13_sSM (G : SimpleGraph (Party k)) (hG : ∀ i i', ¬ G.Adj (inl i) (inl i'))
    {tL tR : ℕ} (hk : 2 ≤ k) (hL : k ≤ 3 * tL) (hR : k ≤ tR) :
    ¬ SolvableAuth G (thresholds k tL tR) (sSM k) := by
  set t := (k + 2) / 3
  obtain ⟨gL, ⟨iA, hA⟩, ⟨iC, hC⟩, hgL⟩ :=
    exists_split (k := k) (t := t) (0 : Fin 3) 2 (by decide) hk (by omega)
  exact Lemma13.not_solvableAuth_of_groups G hG hR _ iA iC jV' hA hC
    (fun z => (hgL z).trans (by omega))
where jV' : Fin k := ⟨0, by omega⟩

end Papers.PODC2025.ByzantineStableMatching
