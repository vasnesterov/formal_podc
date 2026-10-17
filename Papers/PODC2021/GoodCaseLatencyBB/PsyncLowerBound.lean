import Papers.PODC2021.GoodCaseLatencyBB.Basic
import Cslib.Computability.Distributed.Byzantine.PartialSync.TwoStepLowerBound
import Cslib.Foundations.Combinatorics.Labelling

/-!
# Theorem 7: partially synchronous BB with `n ≤ 5f − 2` needs 3 rounds in the good case

Abraham–Nayak–Ren–Xiang, PODC 2021, Section 4.2, Theorem 7 and Figure 4.

The five executions of the paper are exactly the executions `ρ₁, …, ρ₅` of the lower bound of
Kuznetsov–Tonkikh–Zhang (PODC 2021, Theorem 4.5), shared in the library module
`Cslib.Computability.Distributed.Byzantine.PartialSync.TwoStepLowerBound`, with the broadcaster in the role of the influential
process `p` and the groups `B, C, A, D, E` of Figure 4 in the roles of `P₁, …, P₅`:

| paper (Fig. 4) | here (`TwoStepLB`) |
|---|---|
| Execution 1 (`E` Byzantine, honest broadcaster sends `0`) | `ρ₅ = tsRun (I[s ↦ a]) E` |
| Execution 3 (broadcaster and `A` Byzantine) | `ρ₃` |
| Execution 2 (broadcaster and `D` Byzantine, `GST` late) | `ρ₄` |
| Executions 4, 5 | mirror images (labels `i ↦ 6 - i`, values swapped) |

We reuse the indistinguishability, validity and unforgeability lemmas proved there
(`TwoStepLB.decision_eq`: by agreement in `ρ₄`, a decision in `ρ₃` equals a two-round decision in
`ρ₅`); only the final step differs (here the decision of `ρ₅` is forced by the *validity* of
broadcast instead of an influential-process argument).

Two small deviations from the paper's executions (both harmless): in Execution 1 the Byzantine
`E` also sends its round-0 messages to `A` (they are identical to those of an honest `E`, which
`A` receives in Execution 2 as well), and Byzantine processes replay other executions only for a
bounded time (needed for unforgeability, which the paper does not discuss).
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Cslib.Byzantine.PartialSync.TwoStepLB Finset

variable {P M S V K : Type*} [Fintype P] [DecidableEq P]

/-- A labelling of the processes by groups: `0` = broadcaster, `3` = `A`, `1` = `B`, `5` = `E`,
`2` = `C`, `4` = `D` (Figure 4), with `|A|, |C|, |D| ≤ f − 1`, `|B|, |E| ≤ f`, `A ≠ ∅ ≠ B`. -/
theorem exists_labels (s : P) {f : ℕ} (hf : 2 ≤ f) (h3 : 3 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 5 * f - 2) :
    ∃ g : P → ℕ, (∀ q, g q = 0 ↔ q = s) ∧ (∀ q, g q ≤ 5) ∧
      (univ.filter fun q => g q = 3).card ≤ f - 1 ∧ (univ.filter fun q => g q = 2).card ≤ f - 1 ∧
      (univ.filter fun q => g q = 4).card ≤ f - 1 ∧ (univ.filter fun q => g q = 1).card ≤ f ∧
      (univ.filter fun q => g q = 5).card ≤ f ∧ (∃ x, g x = 3) ∧ (∃ x, g x = 1) := by
  obtain ⟨g, hs, hle, hc⟩ := Fintype.exists_labelling_apply_eq 6
    (fun i => if i = 0 ∨ i = 1 ∨ i = 3 then 1 else 0)
    (fun i => if i = 0 then 1 else if i = 1 ∨ i = 5 then f else f - 1)
    (fun i _ => by split_ifs <;> omega) (by simp [sum_range_succ, -sum_boole]; omega)
    (by simp [sum_range_succ]; omega) s (i₀ := 0) (by omega) (by simp)
  have hne : ∀ i, i = 1 ∨ i = 3 → ∃ x, g x = i := fun i hi => by
    obtain ⟨x, -, hx⟩ := filter_nonempty_iff.1 (card_pos.1 (by
      simpa [show i ≠ 0 by omega, hi] using (hc i (by omega)).1))
    exact ⟨x, hx⟩
  refine ⟨g, fun q => ⟨fun hq => ?_, fun h => h ▸ hs⟩, fun q => by have := hle q; omega,
    by simpa using (hc 3 (by omega)).2, by simpa using (hc 2 (by omega)).2,
    by simpa using (hc 4 (by omega)).2, by simpa using (hc 1 (by omega)).2,
    by simpa using (hc 5 (by omega)).2, hne 3 (by omega), hne 1 (by omega)⟩
  exact card_le_one.1 (by simpa using (hc 0 (by omega)).2) q (by simp [hq]) s (by simp [hs])

/-- **Theorem 7 of [ANRX21].** A partially synchronous Byzantine broadcast protocol (authenticated,
post-GST delay bound `D`) resilient to `f ≥ (n + 2) / 5` faults, i.e. `n ≤ 5f − 2`, does not have
good-case latency of 2 rounds: in some execution with an honest broadcaster and `GST = 0`, some
honest process has not committed after receiving the round-2 messages.
We need `f ≥ 2` and `n ≥ 3` (see `differencies.md` for `f = 1` and `n ≤ 2`). -/
theorem theorem_7 {A : Algorithm P M S V V} {Au : Auth P M K} (hU : A.Unforging Au) {s : P}
    {f D : ℕ} (hD : 0 < D) (hf : 2 ≤ f) (h3 : 3 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 5 * f - 2) {a b : V} (hab : a ≠ b) (hA : IsPsyncBB Au A s f D) :
    ¬ PsyncGoodCaseRounds Au A s f D 2 := by
  intro hlat
  obtain ⟨g, hgs, hg5, hc3, hc2, hc4, hc1, hc5, ⟨x3, hx3⟩, ⟨x1, hx1⟩⟩ := exists_labels s hf h3 hn
  -- the mirrored labelling
  let g' : P → ℕ := fun q => if g q = 0 then 0 else 6 - g q
  have hg' : ∀ q, (g q = 0 ∧ g' q = 0) ∨ (1 ≤ g q ∧ g q ≤ 5 ∧ g' q = 6 - g q) := by
    intro q; have := hg5 q; simp only [g']; split_ifs <;> omega
  have hsplit : ∀ (j : ℕ), 1 ≤ j → (univ.filter fun q => g q = 0 ∨ g q = j).card ≤
      1 + (univ.filter fun q => g q = j).card := by
    intro j hj
    have : (univ.filter fun q => g q = 0 ∨ g q = j) ⊆
        insert s (univ.filter fun q => g q = j) := by
      intro q hq
      simp only [mem_filter, mem_univ, true_and] at hq
      rcases hq with h0 | h0
      · exact mem_insert.mpr (Or.inl ((hgs q).mp h0))
      · exact mem_insert_of_mem (by simp [h0])
    exact (card_le_card this).trans ((card_insert_le _ _).trans (by omega))
  have hF4 : (F4 g).card ≤ f := by
    have := hsplit 4 (by omega); unfold F4; omega
  have hF4' : (F4 g').card ≤ f := by
    have e : F4 g' = univ.filter fun q => g q = 0 ∨ g q = 2 := by
      ext q; simp only [F4, mem_filter, mem_univ, true_and]; have := hg' q; omega
    have := hsplit 2 (by omega); rw [e]; omega
  let T5 : Finset P := univ.filter fun q => g q = 5
  let T1 : Finset P := univ.filter fun q => g q = 1
  let F3 : Finset P := univ.filter fun q => g q = 0 ∨ g q = 3
  have hF3 : F3.card ≤ f := by have := hsplit 3 (by omega); simp only [F3]; omega
  -- inputs: `I` arbitrary except at the broadcaster
  let I : P → V := fun _ => a
  let r3 : P → P → Option V := fun q x =>
    if q = s then (if g x = 1 ∨ g x = 2 then some a else some b) else some (I q)
  have hgs0 : g s = 0 := (hgs s).mpr rfl
  have hside : SideHyp g s I a b T5 F3 I r3 :=
    { hp := hgs
      hg := hg5
      hT5 := fun q => by simp [T5]
      hF3 := fun q => by simp [F3]
      hJ := fun _ _ => rfl
      hr3a := fun x hx => by simp only [r3, ite_true]; rw [ite_eq_left hx]
      hr3b := fun x hx => by simp only [r3, ite_true]; rw [ite_eq_right (by omega)]
      hr3 := fun q hq x => by
        have : q ≠ s := fun e => by rw [e, hgs0] at hq; omega
        simp [r3, this] }
  have hside' : SideHyp g' s I b a T1 F3 I r3 :=
    { hp := fun q => by rw [← hgs q]; have := hg' q; constructor <;> intro <;> omega
      hg := fun q => by have := hg' q; omega
      hT5 := fun q => by
        simp only [T1, mem_filter, mem_univ, true_and]; have := hg' q
        constructor <;> intro <;> omega
      hF3 := fun q => by
        simp only [F3, mem_filter, mem_univ, true_and]; have := hg' q
        constructor <;> intro <;> omega
      hJ := fun _ _ => rfl
      hr3a := fun x hx => by
        simp only [r3, ite_true]; rw [ite_eq_right (by have := hg' x; omega)]
      hr3b := fun x hx => by
        simp only [r3, ite_true]; rw [ite_eq_left (by have := hg' x; omega)]
      hr3 := fun q hq x => by
        have hq3 : g q = 3 := by have := hg' q; omega
        have : q ≠ s := fun e => by rw [e, hgs0] at hq3; omega
        simp [r3, this] }
  -- Execution 3 (`ρ₃`): the process `x1 ∈ B` commits some value
  set ρ3 := rho3 (M := M) A D F3 I r3
  have hx1F : x1 ∉ ρ3.faulty := by simp [ρ3, templateRun, F3, hx1]
  obtain ⟨w, hw⟩ := hA.termination ρ3 (rho3_valid hD hF3) (rho3_authValid hU) x1 hx1F
  -- Executions 1 and 5: the process `x3 ∈ A` commits `a` resp. `b` within two rounds
  have good : ∀ (T : Finset P) (c : V), T.card ≤ f → s ∉ T → x3 ∉ T →
      ∃ τ ≤ 2 * D + 1, A.decide x3
        ((tsRun (M := M) A D (Function.update I s c) T).st A τ x3) = some c := by
    intro T c hT hsT hx3T
    set R := tsRun (M := M) A D (Function.update I s c) T
    have hRV : R.Valid f D := tsRun_valid A hD _ hT
    have hRA : R.AuthValid Au A := tsRun_authValid A hU D _ T
    have hval := hA.validity R hRV hRA rfl hsT x3 hx3T
    simp only [R, tsRun, Function.update_self] at hval
    exact (hlat R ⟨hRV, rfl⟩ hRA hsT x3 hx3T).eq_of_agreement
      (fun w' h1 h2 => hA.agreement R hRV hRA x3 hx3T x3 hx3T w' c h1 h2) hval
  have hx3s : x3 ≠ s := fun e => by rw [e, hgs0] at hx3; omega
  have h5 := good T5 a (hc5) (by simp [T5, hgs0]) (by simp [T5, hx3])
  have h1 := good T1 b (hc1) (by simp [T1, hgs0]) (by simp [T1, hx3])
  have hag := hA.agreement
  have e1 : a = w := decision_eq hside hU hag hD hF4 hx3 h5 (Or.inl hx1) hw
  have e2 : b = w := decision_eq hside' hU hag hD hF4' (by simp [g', hx3]) h1
    (x1 := x1) (by simp [g', hx1]) hw
  exact hab (e1.trans e2.symm)

/-- Theorem 7 in the unauthenticated model. -/
theorem theorem_7_noAuth {A : Algorithm P M S V V} {s : P} {f D : ℕ} (hD : 0 < D) (hf : 2 ≤ f)
    (h3 : 3 ≤ Fintype.card P) (hn : Fintype.card P ≤ 5 * f - 2) {a b : V} (hab : a ≠ b)
    (hA : IsPsyncBB (Auth.none P M) A s f D) : ¬ PsyncGoodCaseRounds (Auth.none P M) A s f D 2 :=
  theorem_7 A.unforging_none hD hf h3 hn hab hA

end GoodCaseLatencyBB
