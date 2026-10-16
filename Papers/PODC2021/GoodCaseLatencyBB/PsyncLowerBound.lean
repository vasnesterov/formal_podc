import Papers.PODC2021.GoodCaseLatencyBB.Basic
import Papers.PODC2021.FastByzantineConsensus.Executions

/-!
# Theorem 7: partially synchronous BB with `n ≤ 5f − 2` needs 3 rounds in the good case

Abraham–Nayak–Ren–Xiang, PODC 2021, Section 4.2, Theorem 7 and Figure 4.

The five executions of the paper are exactly the executions `ρ₁, …, ρ₅` of the lower bound of
Kuznetsov–Tonkikh–Zhang (PODC 2021, Theorem 4.5, formalized in
`Papers/PODC2021/FastByzantineConsensus/`), with the broadcaster in the role of the influential
process `p` and the groups `B, C, A, D, E` of Figure 4 in the roles of `P₁, …, P₅`:

| paper (Fig. 4) | here / FBC |
|---|---|
| Execution 1 (`E` Byzantine, honest broadcaster sends `0`) | `ρ₅ = tsRun (I[s ↦ a]) E` |
| Execution 3 (broadcaster and `A` Byzantine) | `ρ₃` |
| Execution 2 (broadcaster and `D` Byzantine, `GST` late) | `ρ₄` |
| Executions 4, 5 | mirror images (labels `i ↦ 6 - i`, values swapped) |

We reuse the indistinguishability, validity and unforgeability lemmas proved there
(`rho4_st_eq_rho5_P3`, `rho4_st_eq_rho3`, `rho4_valid`, `rho4_authValid`, `rho3_valid`,
`rho3_authValid`); only the final step differs (here the decision of `ρ₅` is forced by the
*validity* of broadcast instead of an influential-process argument).

Two small deviations from the paper's executions (both harmless): in Execution 1 the Byzantine
`E` also sends its round-0 messages to `A` (they are identical to those of an honest `E`, which
`A` receives in Execution 2 as well), and Byzantine processes replay other executions only for a
bounded time (needed for unforgeability, which the paper does not discuss).
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset FastByzantineConsensus

variable {P M S V K : Type*} [Fintype P] [DecidableEq P]

/-- The core of Theorem 7 (one side): if a process `x3` of group `A` (label `3`) commits `v` within
two rounds in Execution 1 (`ρ₅`), then every process of `B ∪ C ∪ E` (labels `1, 2, 5`) that
commits in Execution 3 (`ρ₃`) commits `v`. -/
theorem decision_eq_rho3 {A : Algorithm P M S V V} {Au : Auth P M K} {f D : ℕ} {g : P → ℕ}
    {p : P} {I : P → V} {a b : V} {T5 F3 : Finset P} {J : P → V} {r3 : P → P → Option V}
    (h : SideHyp g p I a b T5 F3 J r3) (hU : A.Unforging Au)
    (hag : ∀ R : Run P M V, R.Valid f D → R.AuthValid Au A → ∀ x ∉ R.faulty, ∀ y ∉ R.faulty,
      ∀ v w, R.Decides A x v → R.Decides A y w → v = w)
    (hD : 0 < D) (hf : (F4 g).card ≤ f) {x3 : P} (hx3 : g x3 = 3) {v : V}
    (h5 : ∃ τ ≤ 2 * D + 1, A.decide x3 ((tsRun A D (Function.update I p a) T5).st A τ x3) = some v)
    {x1 : P} (hx1 : g x1 = 1 ∨ g x1 = 2 ∨ g x1 = 5) {w : V} (h3 : (rho3 A D F3 J r3).Decides A x1 w) :
    v = w := by
  obtain ⟨τ1, hτ1⟩ := h3
  obtain ⟨τ5, hτ5, hd5⟩ := h5
  have hx1F : x1 ∉ (rho4 A D g p I a b T5 (rho3 A D F3 J r3) τ1).faulty := fun hm => by
    have := mem_F4.mp hm; omega
  have hx3F : x3 ∉ (rho4 A D g p I a b T5 (rho3 A D F3 J r3) τ1).faulty := fun hm => by
    have := mem_F4.mp hm; omega
  refine hag _ (rho4_valid h hD τ1 hf) (rho4_authValid h hU hD τ1) x3 hx3F x1 hx1F v w
    ⟨τ5, ?_⟩ ⟨τ1, ?_⟩
  · rw [rho4_st_eq_rho5_P3 h hD τ1 hx3 τ5 hτ5]; exact hd5
  · rw [rho4_st_eq_rho3 h hD τ1 τ1 le_rfl x1 (by simpa using hx1)]; exact hτ1

/-- A labelling of the processes by groups: `0` = broadcaster, `3` = `A`, `1` = `B`, `5` = `E`,
`2` = `C`, `4` = `D` (Figure 4), with `|A|, |C|, |D| ≤ f − 1`, `|B|, |E| ≤ f`, `A ≠ ∅ ≠ B`. -/
theorem exists_labels (s : P) {f : ℕ} (hf : 2 ≤ f) (h3 : 3 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 5 * f - 2) :
    ∃ g : P → ℕ, (∀ q, g q = 0 ↔ q = s) ∧ (∀ q, g q ≤ 5) ∧
      (univ.filter fun q => g q = 3).card ≤ f - 1 ∧ (univ.filter fun q => g q = 2).card ≤ f - 1 ∧
      (univ.filter fun q => g q = 4).card ≤ f - 1 ∧ (univ.filter fun q => g q = 1).card ≤ f ∧
      (univ.filter fun q => g q = 5).card ≤ f ∧ (∃ x, g x = 3) ∧ (∃ x, g x = 1) := by
  set n := Fintype.card P
  let e := Fintype.equivFin P
  let σ : Equiv.Perm (Fin n) := Equiv.swap (e s) ⟨0, by omega⟩
  let ι : P → ℕ := fun q => (σ (e q)).val
  have hι : Function.Injective ι := by
    intro x y hxy
    exact e.injective (σ.injective (Fin.ext hxy))
  have hιs : ι s = 0 := by simp [ι, σ]
  have hιs' : ∀ q, ι q = 0 → q = s := fun q hq => hι (by rw [hq, hιs])
  have hιlt : ∀ q, ι q < n := fun q => (σ (e q)).isLt
  have hsurj : ∀ i < n, ∃ q, ι q = i := by
    intro i hi
    refine ⟨e.symm (σ.symm ⟨i, hi⟩), ?_⟩
    simp [ι]
  set a1 := min (f - 1) (n - 2) with ha1
  have ha1a : a1 ≤ f - 1 := min_le_left _ _
  have ha1b : a1 ≤ n - 2 := min_le_right _ _
  have ha1c : a1 = f - 1 ∨ a1 = n - 2 := by omega
  let lab : ℕ → ℕ := fun i => if i = 0 then 0 else if i < 1 + a1 then 3 else if i < 1 + a1 + f
    then 1 else if i < 1 + a1 + 2 * f then 5 else if i < 1 + a1 + 3 * f - 1 then 2 else 4
  have hcard : ∀ (j l r : ℕ), (∀ i, lab i = j → i < n → l ≤ i ∧ i < r) →
      (univ.filter fun q => lab (ι q) = j).card ≤ r - l := by
    intro j l r hlr
    calc (univ.filter fun q => lab (ι q) = j).card ≤ (Ico l r).card := by
          refine card_le_card_of_injOn ι (fun q hq => ?_) hι.injOn
          have := hlr _ (mem_filter.mp hq).2 (hιlt q)
          simpa using this
      _ = r - l := Nat.card_Ico l r
  refine ⟨fun q => lab (ι q), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    constructor
    · intro h0
      apply hιs'
      simp only [lab] at h0
      split_ifs at h0 <;> omega
    · rintro rfl; simp [lab, hιs]
  · intro q; simp only [lab]; split_ifs <;> omega
  · refine (hcard 3 1 (1 + a1) fun i hi _ => ?_).trans (by omega)
    simp only [lab] at hi; split_ifs at hi <;> omega
  · refine (hcard 2 (1 + a1 + 2 * f) (1 + a1 + 3 * f - 1) fun i hi _ => ?_).trans (by omega)
    simp only [lab] at hi; split_ifs at hi <;> omega
  · refine (hcard 4 (1 + a1 + 3 * f - 1) n fun i hi hn' => ?_).trans (by omega)
    simp only [lab] at hi; split_ifs at hi <;> omega
  · refine (hcard 1 (1 + a1) (1 + a1 + f) fun i hi _ => ?_).trans (by omega)
    simp only [lab] at hi; split_ifs at hi <;> omega
  · refine (hcard 5 (1 + a1 + f) (1 + a1 + 2 * f) fun i hi _ => ?_).trans (by omega)
    simp only [lab] at hi; split_ifs at hi <;> omega
  · obtain ⟨q, hq⟩ := hsurj 1 (by omega)
    exact ⟨q, by simp only [lab, hq]; split_ifs <;> omega⟩
  · obtain ⟨q, hq⟩ := hsurj (1 + a1) (by omega)
    exact ⟨q, by simp only [lab, hq]; split_ifs <;> omega⟩

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
  have e1 : a = w := decision_eq_rho3 hside hU hag hD hF4 hx3 h5 (Or.inl hx1) hw
  have e2 : b = w := decision_eq_rho3 hside' hU hag hD hF4' (by simp [g', hx3]) h1
    (x1 := x1) (by simp [g', hx1]) hw
  exact hab (e1.trans e2.symm)

/-- Theorem 7 in the unauthenticated model. -/
theorem theorem_7_noAuth {A : Algorithm P M S V V} {s : P} {f D : ℕ} (hD : 0 < D) (hf : 2 ≤ f)
    (h3 : 3 ≤ Fintype.card P) (hn : Fintype.card P ≤ 5 * f - 2) {a b : V} (hab : a ≠ b)
    (hA : IsPsyncBB (Auth.none P M) A s f D) : ¬ PsyncGoodCaseRounds (Auth.none P M) A s f D 2 :=
  theorem_7 A.unforging_none hD hf h3 hn hab hA

end GoodCaseLatencyBB
