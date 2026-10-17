import Papers.PODC2025.ByzantineStableMatching.Problem
import Cslib.Computability.Distributed.Byzantine.LockStep.Parallel
import Podc.Computability.Distributed.Byzantine.LockStep.GroupSim
import Mathlib
import Podc.Foundations.Data.Nat.CeilDiv

/-!
# Lemma 3: scaling down by group simulation

Constantinescu, Dufay, Ghinea, Wattenhofer, *Byzantine Stable Matching*, PODC 2025 (arXiv 2502.05889),
Lemma 3 (proof in Appendix A.2).

A protocol for many parties is turned into a protocol for few parties: every party `q` of the small
system simulates the group `grp ⁻¹' {q}` of the large system. The generic group simulation
(`GroupSim.Bundle`, `GroupSim.simHist`, `GroupSim.hist_bigScenario`, …) is shared library code
(`Podc/Computability/Distributed/Byzantine/LockStep/GroupSim.lean`).

* `GroupSim.Solvable.of_groupSim`: generic reduction (any party types, any specifications);
* `solvable_sSM_of_groups`: the reduction for sSM with sidewise group maps;
* `lemma3`: the paper's statement for the threshold adversary;
* `lemma3_auth` / `GroupSim.SolvableAuth.of_groupSim`: the authenticated versions.
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum Classical

/-! ## Sidewise group maps: the reduction for sSM -/

section Sidewise

variable {k d : ℕ} (gL gR : Fin k → Fin d) (repL repR : Fin d → Fin k)

/-- The sidewise group map: `inl i ↦ inl (gL i)`, `inr j ↦ inr (gR j)`. -/
def grpMap : Party k → Party d := Sum.map gL gR

/-- The representatives, sidewise. -/
def repMap : Party d → Party k := Sum.map repL repR

/-- Inputs of the simulated parties: the translated favourite of the simulator (it is the
representative's favourite; the other simulated parties get the same, arbitrary, favourite). -/
def simInput : Party d → Fin d → Party k → Fin k :=
  fun _ x p => Sum.elim (fun _ => repR x) (fun _ => repL x) p

/-- Output translation: if the representative matches the representative of a group of the other
side, output that group, otherwise nobody. -/
def simOutput : Party d → Option (Fin k) → Option (Fin d)
  | inl _, o => o.bind fun j => if repR (gR j) = j then some (gR j) else none
  | inr _, o => o.bind fun i => if repL (gL i) = i then some (gL i) else none

variable {gL gR repL repR}

lemma grpMap_repMap (hL : ∀ i, gL (repL i) = i) (hR : ∀ j, gR (repR j) = j) (q : Party d) :
    grpMap gL gR (repMap repL repR q) = q := by
  rcases q with i | j <;> simp [grpMap, repMap, hL, hR]

lemma simOutput_inl (hR : ∀ j, gR (repR j) = j) (i : Fin d) (o : Option (Fin k)) (j : Fin d) :
    simOutput gL gR repL repR (inl i) o = some j ↔ o = some (repR j) := by
  rcases o with _ | j₀
  · simp [simOutput]
  · simp only [simOutput, Option.bind_some, Option.some.injEq]
    constructor
    · intro h
      split_ifs at h with h₀
      · rw [← Option.some_injective _ h, h₀]
    · rintro rfl
      simp [hR]

lemma simOutput_inr (hL : ∀ i, gL (repL i) = i) (j : Fin d) (o : Option (Fin k)) (i : Fin d) :
    simOutput gL gR repL repR (inr j) o = some i ↔ o = some (repL i) := by
  rcases o with _ | i₀
  · simp [simOutput]
  · simp only [simOutput, Option.bind_some, Option.some.injEq]
    constructor
    · intro h
      split_ifs at h with h₀
      · rw [← Option.some_injective _ h, h₀]
    · rintro rfl
      simp [hL]

/-- The specification transfer for sSM: the representatives' decisions in the simulated run,
translated by `simOutput`, solve sSM on the small system. -/
lemma sSM_groupSim (hL : ∀ i, gL (repL i) = i) (hR : ∀ j, gR (repR j) = j)
    (x : Party d → Fin d) (B : Set (Party d)) (dec : Party k → Option (Fin k) → Prop)
    (dec' : Party d → Option (Fin d) → Prop)
    (h : sSM k (fun p => simInput repL repR (grpMap gL gR p) (x (grpMap gL gR p)) p)
      (grpMap gL gR ⁻¹' B)ᶜ dec)
    (hdec : ∀ q ∉ B, ∀ o', dec' q o' ↔
      ∃ o, dec (repMap repL repR q) o ∧ simOutput gL gR repL repR q o = o') :
    sSM d x Bᶜ dec' := by
  obtain ⟨hc, hst⟩ := h
  have hon : ∀ q, q ∈ Bᶜ → repMap repL repR q ∈ (grpMap gL gR ⁻¹' B)ᶜ := by
    intro q hq
    simpa [grpMap_repMap hL hR] using hq
  have decL : ∀ i, inl i ∈ Bᶜ → ∀ j, dec' (inl i) (some j) ↔ dec (inl (repL i)) (some (repR j)) := by
    intro i hi j
    rw [hdec _ hi]
    simp only [simOutput_inl hR, repMap, Sum.map_inl]
    exact ⟨fun ⟨o, ho, he⟩ => he ▸ ho, fun ho => ⟨_, ho, rfl⟩⟩
  have decR : ∀ j, inr j ∈ Bᶜ → ∀ i, dec' (inr j) (some i) ↔ dec (inr (repR j)) (some (repL i)) := by
    intro j hj i
    rw [hdec _ hj]
    simp only [simOutput_inr hL, repMap, Sum.map_inr]
    exact ⟨fun ⟨o, ho, he⟩ => he ▸ ho, fun ho => ⟨_, ho, rfl⟩⟩
  have injL : Function.Injective repL := fun a b e => by rw [← hL a, e, hL b]
  have injR : Function.Injective repR := fun a b e => by rw [← hR a, e, hR b]
  refine ⟨⟨fun q hq => ?_, fun i j hi hj => ?_, fun p q hp hq hpq z z' hz hz' => ?_⟩,
    fun i j hi hj hxi hxj => ?_⟩
  · obtain ⟨o, ho⟩ := hc.termination _ (hon q hq)
    exact ⟨_, (hdec q hq _).mpr ⟨o, ho, rfl⟩⟩
  · rw [decL i hi, decR j hj]
    exact hc.symmetry _ _ (hon _ hi) (hon _ hj)
  · rcases p with i | j <;> rcases q with i' | j'
    · rw [decL i hp] at hz
      rw [decL i' hq] at hz'
      have hne : inl (repL i) ≠ (inl (repL i') : Party k) := by
        simpa using fun e => hpq (by rw [injL e])
      have := hc.nonCompetition _ _ (hon _ hp) (hon _ hq) hne _ _ hz hz'
      simp only [repMap, Sum.map_inl, partner, ne_eq, Sum.inr.injEq] at this ⊢
      exact fun e => this (by rw [e])
    · simp [partner]
    · simp [partner]
    · rw [decR j hp] at hz
      rw [decR j' hq] at hz'
      have hne : inr (repR j) ≠ (inr (repR j') : Party k) := by
        simpa using fun e => hpq (by rw [injR e])
      have := hc.nonCompetition _ _ (hon _ hp) (hon _ hq) hne _ _ hz hz'
      simp only [repMap, Sum.map_inr, partner, ne_eq, Sum.inl.injEq] at this ⊢
      exact fun e => this (by rw [e])
  · rw [decL i hi, decR j hj]
    apply hst _ _ (hon _ hi) (hon _ hj)
    · simp [simInput, grpMap, hL, hxi]
    · simp [simInput, grpMap, hR, hxj]

/-- **Lemma 3, general form** (unauthenticated): with sidewise surjective group maps `gL`, `gR` with
representatives `repL`, `repR`, if cross-group edges of `Gk` are edges of `Gd` and the union of the
groups of an admissible Byzantine set of the small system is admissible in the large system, then
solvability of sSM transfers from `2k` to `2d` parties. -/
theorem solvable_sSM_of_groups {Gk : SimpleGraph (Party k)} {Gd : SimpleGraph (Party d)}
    {Zk : AdvStructure (Party k)} {Zd : AdvStructure (Party d)}
    (hL : ∀ i, gL (repL i) = i) (hR : ∀ j, gR (repR j) = j)
    (hadj : ∀ p q, Gk.Adj p q → grpMap gL gR p ≠ grpMap gL gR q →
      Gd.Adj (grpMap gL gR p) (grpMap gL gR q))
    (hZ : ∀ B ∈ Zd, grpMap gL gR ⁻¹' B ∈ Zk)
    (h : Solvable Gk Zk (sSM k)) : Solvable Gd Zd (sSM d) :=
  GroupSim.Solvable.of_groupSim (grpMap gL gR) (repMap repL repR) (grpMap_repMap hL hR)
    (simInput repL repR) (simOutput gL gR repL repR) hadj hZ
    (fun x B dec dec' h hdec => sSM_groupSim hL hR x B dec dec' h hdec) h

/-- **Lemma 3, general form** (authenticated). -/
theorem solvableAuth_sSM_of_groups {Gk : SimpleGraph (Party k)} {Gd : SimpleGraph (Party d)}
    {Zk : AdvStructure (Party k)} {Zd : AdvStructure (Party d)}
    (hL : ∀ i, gL (repL i) = i) (hR : ∀ j, gR (repR j) = j)
    (hadj : ∀ p q, Gk.Adj p q → grpMap gL gR p ≠ grpMap gL gR q →
      Gd.Adj (grpMap gL gR p) (grpMap gL gR q))
    (hZ : ∀ B ∈ Zd, grpMap gL gR ⁻¹' B ∈ Zk)
    (h : SolvableAuth Gk Zk (sSM k)) : SolvableAuth Gd Zd (sSM d) :=
  GroupSim.SolvableAuth.of_groupSim (grpMap gL gR) (repMap repL repR) (grpMap_repMap hL hR)
    (simInput repL repR) (simOutput gL gR repL repR) hadj hZ
    (fun x B dec dec' h hdec => sSM_groupSim hL hR x B dec dec' h hdec) h

end Sidewise

/-! ## Lemma 3 for the threshold adversary -/

section Threshold

variable {k d : ℕ}

/-- The concrete partition used for Lemma 3: `i ↦ i mod d`. For `0 < d ≤ k` its groups are nonempty
(`j` is in group `j`) and have size at most `⌈k/d⌉ = k ⌈/⌉ d`.
(The partition `i ↦ i / ⌈k/d⌉` would not do: e.g. for `k = 4`, `d = 3` it has only 2 groups.) -/
def modGroup (hd : 0 < d) (i : Fin k) : Fin d := ⟨i % d, Nat.mod_lt _ hd⟩

lemma modGroup_castLE (hd : 0 < d) (hdk : d ≤ k) (i : Fin d) :
    modGroup hd (Fin.castLE hdk i) = i := by
  ext; simp [modGroup, Nat.mod_eq_of_lt i.2]

/-- Groups of `modGroup` have at most `⌈k/d⌉` elements. -/
lemma ncard_preimage_modGroup_le (hd : 0 < d) (S : Set (Fin d)) :
    (modGroup (k := k) hd ⁻¹' S).ncard ≤ k ⌈/⌉ d * S.ncard := by
  set c := k ⌈/⌉ d with hc_def
  have hc : ∀ i : Fin k, i.val / d < c := fun i =>
    Nat.div_lt_of_lt_mul (i.2.trans_le (Nat.le_mul_ceilDiv hd))
  calc (modGroup hd ⁻¹' S).ncard ≤ (S ×ˢ (Set.univ : Set (Fin c))).ncard :=
        Set.ncard_le_ncard_of_injOn (fun i => (modGroup hd i, (⟨i.val / d, hc i⟩ : Fin c)))
          (fun i hi => ⟨hi, trivial⟩) (by
            intro i _ j _ e
            simp only [Prod.mk.injEq, modGroup, Fin.mk.injEq] at e
            ext
            rw [← Nat.div_add_mod i.val d, ← Nat.div_add_mod j.val d, e.1, e.2])
    _ = c * S.ncard := by
        rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, mul_comm]

lemma preimage_grpMap_mem_thresholds (hd : 0 < d) {tL tR : ℕ} {B : Set (Party d)}
    (hB : B ∈ thresholds d (tL / (k ⌈/⌉ d)) (tR / (k ⌈/⌉ d))) :
    grpMap (modGroup (k := k) hd) (modGroup hd) ⁻¹' B ∈ thresholds k tL tR := by
  obtain ⟨hBL, hBR⟩ := hB
  have eL : inl ⁻¹' (grpMap (modGroup (k := k) hd) (modGroup hd) ⁻¹' B) =
      modGroup hd ⁻¹' (inl ⁻¹' B) := by ext; simp [grpMap]
  have eR : inr ⁻¹' (grpMap (modGroup (k := k) hd) (modGroup hd) ⁻¹' B) =
      modGroup hd ⁻¹' (inr ⁻¹' B) := by ext; simp [grpMap]
  refine ⟨?_, ?_⟩
  · rw [eL]
    calc _ ≤ k ⌈/⌉ d * (inl ⁻¹' B).ncard := ncard_preimage_modGroup_le hd _
      _ ≤ k ⌈/⌉ d * (tL / (k ⌈/⌉ d)) := Nat.mul_le_mul_left _ hBL
      _ ≤ tL := Nat.mul_div_le _ _
  · rw [eR]
    calc _ ≤ k ⌈/⌉ d * (inr ⁻¹' B).ncard := ncard_preimage_modGroup_le hd _
      _ ≤ k ⌈/⌉ d * (tR / (k ⌈/⌉ d)) := Nat.mul_le_mul_left _ hBR
      _ ≤ tR := Nat.mul_div_le _ _

/-- The four networks of the paper are compatible with sidewise group maps. -/
lemma adj_grpMap {G : (n : ℕ) → SimpleGraph (Party n)}
    (hG : G = fully ∨ G = oneSided ∨ G = oneSidedR ∨ G = bipartite) (gL gR : Fin k → Fin d)
    (p q : Party k) (hpq : (G k).Adj p q) (hne : grpMap gL gR p ≠ grpMap gL gR q) :
    (G d).Adj (grpMap gL gR p) (grpMap gL gR q) := by
  rcases hG with rfl | rfl | rfl | rfl <;>
    rcases p with p | p <;> rcases q with q | q <;> simp_all [grpMap]

/-- **Lemma 3** of [Constantinescu–Dufay–Ghinea–Wattenhofer, PODC 2025] (unauthenticated): if sSM on
`2k` parties is solvable against `tL` Byzantine parties in `L` and `tR` in `R`, then for any
`0 < d ≤ k`, sSM on `2d` parties is solvable against `⌊tL / ⌈k/d⌉⌋` and `⌊tR / ⌈k/d⌉⌋` Byzantine
parties, on the same kind of network (fully connected, one-sided, or bipartite). -/
theorem lemma3 {G : (n : ℕ) → SimpleGraph (Party n)}
    (hG : G = fully ∨ G = oneSided ∨ G = oneSidedR ∨ G = bipartite) {k d tL tR : ℕ}
    (hd : 0 < d) (hdk : d ≤ k) (h : Solvable (G k) (thresholds k tL tR) (sSM k)) :
    Solvable (G d) (thresholds d (tL / (k ⌈/⌉ d)) (tR / (k ⌈/⌉ d))) (sSM d) :=
  solvable_sSM_of_groups (repL := Fin.castLE hdk) (repR := Fin.castLE hdk)
    (modGroup_castLE hd hdk) (modGroup_castLE hd hdk) (adj_grpMap hG _ _)
    (fun _ hB => preimage_grpMap_mem_thresholds hd hB) h

/-- **Lemma 3** of [Constantinescu–Dufay–Ghinea–Wattenhofer, PODC 2025], authenticated setting. -/
theorem lemma3_auth {G : (n : ℕ) → SimpleGraph (Party n)}
    (hG : G = fully ∨ G = oneSided ∨ G = oneSidedR ∨ G = bipartite) {k d tL tR : ℕ}
    (hd : 0 < d) (hdk : d ≤ k) (h : SolvableAuth (G k) (thresholds k tL tR) (sSM k)) :
    SolvableAuth (G d) (thresholds d (tL / (k ⌈/⌉ d)) (tR / (k ⌈/⌉ d))) (sSM d) :=
  solvableAuth_sSM_of_groups (repL := Fin.castLE hdk) (repR := Fin.castLE hdk)
    (modGroup_castLE hd hdk) (modGroup_castLE hd hdk) (adj_grpMap hG _ _)
    (fun _ hB => preimage_grpMap_mem_thresholds hd hB) h

/-- Remark: Lemma 3 does not give what the paper's Lemma 13 needs. Scaling from `k = 4` to `d = 3`
with `tR = k = 4` only yields `tR' = ⌊4 / ⌈4/3⌉⌋ = 2 < 3 = d` Byzantine parties on the right, so the
paper's appeal to Lemma 3 in Lemma 13 is not valid for such `k`. -/
lemma lemma3_not_enough_for_lemma13 : (4 : ℕ) / (4 ⌈/⌉ 3) = 2 := by
  norm_num [Nat.ceilDiv_eq_add_pred_div]

end Threshold

end Papers.PODC2025.ByzantineStableMatching
