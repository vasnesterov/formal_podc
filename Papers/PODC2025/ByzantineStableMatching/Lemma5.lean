import Papers.PODC2025.ByzantineStableMatching.Groups

/-!
# Lemma 5: the fully-connected unauthenticated lower bound

Paper: for `n = 6` (`k = 3`) no protocol achieves sSM with `tL = tR = 1` in a fully-connected
unauthenticated network; proof by a 12-node double cover (Fig. 2).

We prove directly, for every `k ≥ 2` and every network `G` (in particular the fully-connected one),
that sSM is unsolvable when `3 tL ≥ k` and `3 tR ≥ k`. Each side is split into three groups
`a, b, c` (resp. `u, v, w`) of size `≤ ⌈k/3⌉` (the groups `b`, `u` may be empty, which covers `k = 2`
where the paper's route via Lemma 3 does not apply). The double cover is the paper's: each party has
two copies; the edges `a–c`, `a–w`, `c–u`, `u–w` (between groups with labels `0` and `2`) cross
between the copies, all other edges stay inside a copy. (We read off this voltage assignment from
the three honest sets of Fig. 2 (ii)–(iv), which pins it down uniquely.)
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum

variable {k : ℕ}

namespace Lemma5

/-- Edges between groups labelled `0` and `2` cross between the two copies. -/
def volt (a b : Fin 3) : Bool := (a = 0 && b = 2) || (a = 2 && b = 0)

/-- The double cover of Lemma 5. Node `(p, c)` is copy `c` of party `p`. All `L`-nodes have the
`v`-representative `jV` as favourite; `R`-nodes of copy `true` favour `iA`, of copy `false` favour
`iC`. -/
def cover (gL gR : Fin k → Fin 3) (iA iC jV : Fin k) :
    CoverSystem (Party k) (Fin k) (Party k × Bool) :=
  CoverSystem.doubleCover (fun q c p => some (xor c (volt (label gL gR q) (label gL gR p))))
    fun q => match q with
      | (inl _, _) => jV
      | (inr _, c) => if c then iA else iC

/-- The general form of Lemma 5. -/
theorem not_solvable_of_groups (G : SimpleGraph (Party k)) {tL tR : ℕ}
    (gL gR : Fin k → Fin 3) (iA iC jV : Fin k) (hA : gL iA = 0) (hC : gL iC = 2) (hV : gR jV = 1)
    (hgL : ∀ z, {i | gL i = z}.ncard ≤ tL) (hgR : ∀ z, {j | gR j = z}.ncard ≤ tR) :
    ¬ Solvable G (thresholds k tL tR) (sSM k) := by
  rintro ⟨M, alg, halg⟩
  set C := cover gL gR iA iC jV
  set lab := label gL gR
  have hZ : ∀ z : Fin 3, {p | lab p = z} ∈ thresholds k tL tR := fun z =>
    label_mem_thresholds gL gR {z} (hgL z) (hgR z)
  -- Scenario (ii): groups `c`, `w` Byzantine, copy `true` honest.
  have h2 : C.Decides G alg (inl iA, true) (some jV) := by
    have hL : C.Lift G {p | lab p = 2} (fun p => (p, true)) :=
      CoverSystem.doubleCover_lift fun p q hp hq _ => by
        have key : ∀ a b : Fin 3, a ≠ 2 → b ≠ 2 → xor true (volt a b) = true := by decide
        exact congrArg some (key _ _ hq hp)
    have hs := halg (C.scenario G alg {p | lab p = 2} (fun p => (p, true)) fun _ => jV) (hZ 2)
      (fun _ _ _ h => h)
    have hiA : inl iA ∉ {p | lab p = 2} := by simp [lab, hA]
    have hjV : inr jV ∉ {p | lab p = 2} := by simp [lab, hV]
    have := (hs.2 iA jV hiA hjV (by rw [C.scenario_input_of_not_mem _ hiA]; rfl)
      (by rw [C.scenario_input_of_not_mem _ hjV]; rfl)).1
    exact (C.decides_scenario_iff hL _ hiA _).mp this
  -- Scenario (iii): groups `a`, `u` Byzantine, copy `false` honest.
  have h3 : C.Decides G alg (inl iC, false) (some jV) := by
    have hL : C.Lift G {p | lab p = 0} (fun p => (p, false)) :=
      CoverSystem.doubleCover_lift fun p q hp hq _ => by
        have key : ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 → xor false (volt a b) = false := by decide
        exact congrArg some (key _ _ hq hp)
    have hs := halg (C.scenario G alg {p | lab p = 0} (fun p => (p, false)) fun _ => jV) (hZ 0)
      (fun _ _ _ h => h)
    have hiC : inl iC ∉ {p | lab p = 0} := by simp [lab, hC]
    have hjV : inr jV ∉ {p | lab p = 0} := by simp [lab, hV]
    have := (hs.2 iC jV hiC hjV (by rw [C.scenario_input_of_not_mem _ hiC]; rfl)
      (by rw [C.scenario_input_of_not_mem _ hjV]; rfl)).1
    exact (C.decides_scenario_iff hL _ hiC _).mp this
  -- Scenario (iv): groups `b`, `v` Byzantine; `a`, `u` honest in copy `true`, `c`, `w` in copy `false`.
  have hL : C.Lift G {p | lab p = 1} (fun p => (p, decide (lab p = 0))) :=
    CoverSystem.doubleCover_lift fun p q hp hq _ => by
      have key : ∀ a b : Fin 3, a ≠ 1 → b ≠ 1 →
          xor (decide (b = 0)) (volt b a) = decide (a = 0) := by decide
      exact congrArg some (key _ _ hp hq)
  have hs := halg (C.scenario G alg {p | lab p = 1} (fun p => (p, decide (lab p = 0))) fun _ => jV)
    (hZ 1) (fun _ _ _ h => h)
  have hiA : inl iA ∉ {p | lab p = 1} := by simp [lab, hA]
  have hiC : inl iC ∉ {p | lab p = 1} := by simp [lab, hC]
  have dA := (C.decides_scenario_iff (alg := alg) hL (fun _ => jV) hiA _).mpr (by simpa [lab, hA] using h2)
  have dC := (C.decides_scenario_iff (alg := alg) hL (fun _ => jV) hiC _).mpr (by simpa [lab, hC] using h3)
  have hne : (inl iA : Party k) ≠ inl iC := by
    intro h; cases h; rw [hA] at hC; exact absurd hC (by decide)
  exact hs.1.nonCompetition _ _ hiA hiC hne _ _ dA dC rfl

end Lemma5

/-- **Lemma 5** (generalized to every `k ≥ 2` and every network): if `tL ≥ k/3` and `tR ≥ k/3` then
no protocol achieves sSM, even in a fully-connected unauthenticated network. -/
theorem lemma5 (G : SimpleGraph (Party k)) {tL tR : ℕ} (hk : 2 ≤ k) (hL : k ≤ 3 * tL)
    (hR : k ≤ 3 * tR) : ¬ Solvable G (thresholds k tL tR) (sSM k) := by
  set t := (k + 2) / 3
  have hk3 : k ≤ 3 * t := by omega
  obtain ⟨gL, ⟨iA, hA⟩, ⟨iC, hC⟩, hgL⟩ :=
    exists_split (k := k) (t := t) (0 : Fin 3) 2 (by decide) hk hk3
  obtain ⟨gR, ⟨jV, hV⟩, -, hgR⟩ :=
    exists_split (k := k) (t := t) (1 : Fin 3) 0 (by decide) hk hk3
  exact Lemma5.not_solvable_of_groups G _ _ iA iC jV hA hC hV
    (fun z => (hgL z).trans (by omega)) (fun z => (hgR z).trans (by omega))

end Papers.PODC2025.ByzantineStableMatching
