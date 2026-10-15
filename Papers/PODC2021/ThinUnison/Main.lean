import Papers.PODC2021.ThinUnison.Protected
import Papers.PODC2021.ThinUnison.Good
import Papers.PODC2021.ThinUnison.StateSpace

/-!
# Theorem 1.1 of Emek–Keren (PODC 2021)

AlgAU with `k = 3D + 2` (`4k - 2 = 12D + 6` states) is a deterministic self-stabilizing
asynchronous unison algorithm on graphs of diameter at most `D` in the stone age model under any
fair (non-starving) asynchronous schedule; it stabilizes within
`N(D) = ∑_{j=1}^{k-1} (k-j)(k-j-1) + (2k - 3) + (D+1) · 2(k-1)(2k-2) ≤ 70 (D+1)³` rounds.
-/

namespace ThinUnison

open Cslib.StoneAge

/-- The stabilization time (in rounds) of AlgAU, `k = 3D + 2`: Corollary 2.15
(`∑_{j=1}^{k-1} (k-j)(k-j-1)` rounds until out-protected), Corollary 2.17 (`2k - 3` more rounds
until justified), Lemma 2.22 (`(D + 1) · 2(k-1)(2k-2)` more rounds until protected, hence good). -/
def stabRoundsK (k D : ℕ) : ℕ :=
  (D + 1) * (2 * ((k - 1) * (2 * k - 2))) + (2 * k - 3) + outRounds k 1

/-- The stabilization time for the paper's choice `k = 3D + 2`. -/
def stabRounds (D : ℕ) : ℕ := stabRoundsK (3 * D + 2) D

theorem outRounds_le (k i : ℕ) : outRounds k i ≤ k * k ^ 2 := by
  unfold outRounds
  calc ∑ j ∈ Finset.Ico i k, (k - j) * (k - j - 1)
      ≤ ∑ _j ∈ Finset.Ico i k, k ^ 2 := Finset.sum_le_sum fun j _ => by
        rw [sq]; exact Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
    _ = (k - i) * k ^ 2 := by simp
    _ ≤ k * k ^ 2 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)

/-- `N(D) = O(D³)`: explicitly `N(D) ≤ 70 (D + 1)³`. -/
theorem stabRounds_le (D : ℕ) : stabRounds D ≤ 70 * (D + 1) ^ 3 := by
  unfold stabRounds stabRoundsK
  have h1 := outRounds_le (3 * D + 2) 1
  have h2 : (3 * D + 2 - 1) * (2 * (3 * D + 2) - 2) = (3 * D + 1) * (6 * D + 2) := by
    congr 1; omega
  rw [h2]
  have h3 : 2 * (3 * D + 2) - 3 = 6 * D + 1 := by omega
  rw [h3]
  nlinarith [h1]

variable {V : Type*} {G : SimpleGraph V}

/-- The state space of AlgAU with parameter `k` has `4k - 2` states: `2k` able turns and `2k - 2`
faulty turns. (Here: an injection into `ℤ × Bool` with levels in `[-k, k]`.) -/
theorem turn_lvl_mem (k : ℕ) (ν : Turn k) : ν.lvl ∈ Finset.Icc (-(k : ℤ)) k := by
  have := ν.isLevel; unfold IsLevel at this; simp only [Finset.mem_Icc]; omega

/-- Theorem 1.1 of [EK21] for any parameter `k ≥ 3D + 2` (the paper takes `k = 3D + 2`). -/
theorem theorem_1_1_general [Finite V] {D k : ℕ} (hDk : 3 * D + 2 ≤ k) (hD : G.ediam ≤ D)
    (C0 : V → Turn k) {A : ℕ → Set V} (hA : Fair A) {d : ℕ} (hd : G.ediam ≤ d) (hdD : d ≤ D) :
    AUFrom G A (output (k := k)) (run G (algAU k) C0 A) d (R A (stabRoundsK k D)) := by
  set C := run G (algAU k) C0 A
  have hC : AURun G A C := aURun_run C0
  have hk1 : 1 ≤ k := by omega
  set T0 := R A (outRounds k 1) with hT0
  have hop : ∀ t, T0 ≤ t → AllOutProt G C t := fun t ht => hC.corollary_2_15 hA hk1 ht
  set T1 := (rho A)^[2 * k - 3] T0 with hT1
  have hjust : ∀ t, T1 ≤ t → Justified G C t := fun t ht => hC.corollary_2_17 hA hop ht
  have hT01 : T0 ≤ T1 := le_rho_iter hA _ _
  have hpersist : ∀ s, T1 ≤ s → AllProt G C s → AllProt G C (s + 1) := fun s hs h =>
    fun v => (hC.allGood_succ (AURun.lemma_2_18 (hjust s hs) h) v).1
  have hprot := hC.lemma_2_22 hA hDk hD (hop T1 hT01) hpersist
  set T2 := (rho A)^[(D + 1) * (2 * ((k - 1) * (2 * k - 2)))] T1 with hT2
  have hT12 : T1 ≤ T2 := le_rho_iter hA _ _
  have hgood : AllGood G C T2 := AURun.lemma_2_18 (hjust T2 hT12) hprot
  have hR : R A (stabRoundsK k D) = T2 := by
    rw [hT2, hT1, hT0, R, R, rho_iter_add, rho_iter_add]; rfl
  rw [hR]
  exact hC.auFrom_of_allGood hA hd (by omega) hgood

/-- **Theorem 1.1 of [EK21]** (AlgAU, `k = 3D + 2`). Let `G` be a finite graph of diameter at most
`D`, `C0` an arbitrary initial configuration and `A` an arbitrary fair schedule (every node is
activated infinitely often). Then from time `R(N(D))` on (`N(D) = stabRounds D = O(D³)` rounds,
`R(i) = ϱ^i(0)`), the execution of AlgAU solves asynchronous unison: all nodes are in output
(able) states, neighbouring clocks differ by at most one, clocks only advance by `+1`, and for every
`d ≤ D` bounding the diameter (e.g. `d = D`, or `d = diam G`, see `theorem_1_1_diam`) every node
advances its clock at least `i` times in `[t, ϱ^{d+i}(t))`, for all `t ≥ R(N(D))` and `i`. -/
theorem theorem_1_1 [Finite V] {D : ℕ} (hD : G.ediam ≤ D) (C0 : V → Turn (3 * D + 2))
    {A : ℕ → Set V} (hA : Fair A) {d : ℕ} (hd : G.ediam ≤ d) (hdD : d ≤ D) :
    AUFrom G A (output (k := 3 * D + 2)) (run G (algAU (3 * D + 2)) C0 A) d
      (R A (stabRounds D)) :=
  theorem_1_1_general le_rfl hD C0 hA hd hdD

/-- Theorem 1.1 with the liveness parameter `diam(G)` as in the paper's definition of AU. -/
theorem theorem_1_1_diam [Finite V] [Nonempty V] {D : ℕ} (hD : G.ediam ≤ D)
    (C0 : V → Turn (3 * D + 2)) {A : ℕ → Set V} (hA : Fair A) :
    AUFrom G A (output (k := 3 * D + 2)) (run G (algAU (3 * D + 2)) C0 A) G.diam
      (R A (stabRounds D)) :=
  have hne : G.ediam ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top D) hD
  theorem_1_1 hD C0 hA (ENat.natCast_toNat hne).ge (ENat.toNat_le_of_le_natCast hD)

/-- Self-stabilization in the paper's sense, as an existence statement: every execution
stabilizes within `O(D³)` rounds (`≤ 70 (D+1)³`). -/
theorem theorem_1_1_exists [Finite V] {D : ℕ} (hD : G.ediam ≤ D) (C0 : V → Turn (3 * D + 2))
    {A : ℕ → Set V} (hA : Fair A) :
    ∃ i ≤ 70 * (D + 1) ^ 3,
      AUFrom G A (output (k := 3 * D + 2)) (run G (algAU (3 * D + 2)) C0 A) D (R A i) :=
  ⟨stabRounds D, stabRounds_le D, theorem_1_1 hD C0 hA hD le_rfl⟩

/-- The state space of AlgAU for diameter bound `D` has `12D + 6 = O(D)` states. -/
theorem card_states (D : ℕ) : Fintype.card (Turn (3 * D + 2)) = 12 * D + 6 := by
  rw [card_turn (by omega)]; omega

/-! ## Non-vacuity

The hypotheses of Theorem 1.1 are satisfiable: e.g. the complete graph on three nodes has diameter
`≤ 1` and the synchronous schedule is fair (so is any round-robin schedule, `fair_roundRobin`).
Under the synchronous schedule `R(i) = i`. -/

theorem ediam_top_fin3_le : (⊤ : SimpleGraph (Fin 3)).ediam ≤ 1 := by
  refine SimpleGraph.ediam_le_coe_iff.2 fun u v => ?_
  by_cases h : u = v
  · subst h; exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · exact ⟨SimpleGraph.Walk.cons (by simpa using h) SimpleGraph.Walk.nil, by simp⟩

theorem R_sync {V : Type*} [Finite V] [Nonempty V] (n : ℕ) : R (sync : ℕ → Set V) n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [R, Function.iterate_succ_apply', ← R, ih, rho_sync]

example (C0 : Fin 3 → Turn 5) :
    AUFrom (⊤ : SimpleGraph (Fin 3)) sync (output (k := 5)) (run ⊤ (algAU 5) C0 sync) 1
      (stabRounds 1) := by
  have := theorem_1_1 (D := 1) ediam_top_fin3_le C0 fair_sync ediam_top_fin3_le le_rfl
  rwa [R_sync] at this

end ThinUnison
