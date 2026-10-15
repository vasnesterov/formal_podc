import Papers.PODC2021.FastByzantineConsensus.TwoStep

/-!
# Lemmas 4.2–4.4: consensus values of two-step executions and the influential process

Kuznetsov–Tonkikh–Zhang, PODC 2021, Section 4.1–4.2.

* Lemma 4.2 (indistinguishability ⇒ same decision) is the model's `Run.st_eq_of_inbox_eq` plus
  determinism; it is used inline.
* `tsRun_agree`: all correct processes of a two-step execution decide the same value (its
  *consensus value* `c(ρ)`).
* `lemma_4_3`: weak validity pins the consensus value of two-step executions from a constant
  initial configuration.
* `Influential`, `exists_influential` (Lemma 4.4, hybrid argument).
-/

set_option linter.unusedSectionVars false

namespace FastByzantineConsensus

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [Fintype P] [DecidableEq P]
variable (A : Algorithm P M S V V) {Au : Auth P M K} {f t δ : ℕ}

/-- The consensus value of a two-step execution is well defined. -/
theorem tsRun_agree (hA : SolvesConsensusAuth Au f δ A weakValidity) (hU : A.Unforging Au)
    (hδ : 0 < δ) (htf : t ≤ f) {I : P → V} {T : Finset P} (hT : T.card = t) {x y : P} {v w : V}
    (hx : x ∉ T) (hy : y ∉ T) (h1 : (tsRun (M := M) A δ I T).Decides A x v)
    (h2 : (tsRun (M := M) A δ I T).Decides A y w) : v = w :=
  hA.agreement _ (tsRun_valid A hδ I (hT ▸ htf)) (tsRun_authValid A hU δ I T) x hx y hy v w h1 h2

/-- **Lemma 4.3.** If all processes have the same input `x`, the consensus value of every
`T`-faulty two-step execution is `x`. -/
theorem lemma_4_3 (hA : SolvesConsensusAuth Au f δ A weakValidity) (hU : A.Unforging Au)
    (hTS : TwoStep A t δ) (hδ : 0 < δ) (htf : t ≤ f) (x : V) {T : Finset P} (hT : T.card = t)
    {y : P} (hy : y ∉ T) {v : V} (h : (tsRun (M := M) A δ (fun _ => x) T).Decides A y v) :
    v = x := by
  classical
  set R := tsRun (M := M) A δ (fun _ => x) T with hR
  obtain ⟨v₀, τ₀, hτ₀, hd⟩ := hTS (fun _ => x) T hT y hy
  have hv : v₀ = v := tsRun_agree A hA hU hδ htf hT hy hy ⟨τ₀, hd⟩ h
  subst hv
  let dl : P → ℕ → P → ℕ := fun q τ _ =>
    if q ∈ T ∧ δ ≤ τ then max (nextRound δ τ) (2 * δ + 2) else nextRound δ τ
  have hS : RoundSched δ dl := by
    intro q τ r
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [dl, show ¬ δ ≤ τ by omega, and_false, ite_false]; exact nextRound_of_lt h
    · simp only [dl]; split_ifs
      · exact (two_le_nextRound h).trans (le_max_left _ _)
      · exact two_le_nextRound h
  let ρ : Run P M V :=
    templateRun A δ ∅ (fun _ => x) (2 * δ + 2) (fun _ _ => none) (fun _ _ _ => []) dl
  have hρV : ρ.Valid f δ := by
    refine ⟨by simp [ρ, templateRun], fun q τ r _ _ => ?_, fun q τ r _ _ => ?_⟩
    · show τ ≤ dl q τ r
      simp only [dl]; split_ifs
      · exact (le_nextRound hδ).le.trans (le_max_left _ _)
      · exact (le_nextRound hδ).le
    · show dl q τ r ≤ max τ (2 * δ + 2) + δ
      have := nextRound_le (D := δ) (τ := τ)
      have h1 := le_max_left τ (2 * δ + 2)
      have h2 := le_max_right τ (2 * δ + 2)
      simp only [dl]; split_ifs
      · apply max_le <;> omega
      · omega
  have hρA : ρ.AuthValid Au A := by
    intro b hb; exact absurd hb (Finset.notMem_empty b)
  have hst : ∀ τ ≤ 2 * δ + 1, ∀ p ∈ {p | p ∉ T}, ρ.st A τ p = R.st A τ p := by
    refine ρ.st_eq_of_inbox_eq A (ref := fun _ => R) (fun _ _ => rfl) ?_
    intro τ hτ ih p hp
    apply Run.inbox_eq_of_dlv_eq
    intro q τ' hτ'
    simp only [Run.dlv]
    by_cases hq : q ∈ T
    · by_cases h1 : τ' < δ
      · have e1 : ρ.dl q τ' p = R.dl q τ' p := by
          show dl q τ' p = nextRound δ τ'
          simp [dl, show ¬ δ ≤ τ' by omega]
        have e2 : ρ.out A q τ' p = R.out A q τ' p := by
          rw [Run.out_of_correct A ρ (Finset.notMem_empty q), Run.out_of_faulty A R hq]
          rw [templateRun_st_early hS q τ' h1.le]
          simp [R, tsRun, h1]
        rw [e1, e2]
      · have e1 : ρ.dl q τ' p ≠ τ := by
          show dl q τ' p ≠ τ
          simp only [dl, hq, true_and, show δ ≤ τ' by omega, ite_true]
          have := le_max_right (nextRound δ τ') (2 * δ + 2); omega
        have e2 : R.out A q τ' p = [] := by
          rw [Run.out_of_faulty A R hq]; simp [R, tsRun, h1]
        simp [e1, e2]
    · have e1 : ρ.dl q τ' p = R.dl q τ' p := by
        show dl q τ' p = nextRound δ τ'
        simp [dl, hq]
      have e2 : ρ.out A q τ' p = R.out A q τ' p := by
        rw [Run.out_of_correct A ρ (Finset.notMem_empty q), Run.out_of_correct A R hq,
          ih q hq τ' hτ']
      rw [e1, e2]
  have hdρ : ρ.Decides A y v₀ := ⟨τ₀, by rw [hst τ₀ hτ₀ y hy]; exact hd⟩
  exact hA.validity ρ hρV hρA y (Finset.notMem_empty y) v₀ hdρ x
    (fun p => by simp [ρ, Run.inputConf, templateRun])

/-- A process `p` is **influential** (Section 4.2): there are initial configurations `I`, `I'`
differing only in the input of `p`, disjoint sets `T`, `T'` of size `t` not containing `p`, and a
`T`-faulty two-step execution from `I` and a `T'`-faulty two-step execution from `I'` with
different consensus values. -/
def Influential (t δ : ℕ) (p : P) : Prop :=
  ∃ (I I' : P → V) (T T' : Finset P), (∀ q ≠ p, I q = I' q) ∧ T.card = t ∧ T'.card = t ∧
    p ∉ T ∧ p ∉ T' ∧ Disjoint T T' ∧
    ∃ x ∉ T, ∃ x' ∉ T', ∃ v v', (tsRun (M := M) A δ I T).Decides A x v ∧
      (tsRun (M := M) A δ I' T').Decides A x' v' ∧ v ≠ v'

/-- **Lemma 4.4.** Every `t`-two-step consensus protocol has an influential process (for
`n ≥ 2t + 2` and at least two values). -/
theorem exists_influential (hA : SolvesConsensusAuth Au f δ A weakValidity)
    (hU : A.Unforging Au) (hTS : TwoStep A t δ) (hδ : 0 < δ) (htf : t ≤ f)
    (hn : 2 * t + 2 ≤ Fintype.card P) {a b : V} (hab : a ≠ b) : ∃ p, Influential A t δ p := by
  classical
  let e := Fintype.equivFin P
  let I : ℕ → P → V := fun i q => if (e q : ℕ) < i then b else a
  have hI0 : I 0 = fun _ => a := by funext q; simp [I]
  have hIn : I (Fintype.card P) = fun _ => b := by funext q; simp [I, (e q).isLt]
  have hne : ∀ q k (hk : k < Fintype.card P), q ≠ e.symm ⟨k, hk⟩ → (e q : ℕ) ≠ k :=
    fun q k hk h h' => h ((Equiv.eq_symm_apply e).mpr (Fin.ext h'))
  have hex : ∀ T : Finset P, T.card = t → ∃ y, y ∉ T := by
    intro T hT
    by_contra hc
    push Not at hc
    have := card_le_card (show (univ : Finset P) ⊆ T from fun y _ => hc y)
    rw [card_univ] at this; omega
  have hdec : ∀ (J : P → V) (T : Finset P), T.card = t → ∀ y ∉ T,
      ∃ v, (tsRun (M := M) A δ J T).Decides A y v := by
    intro J T hT y hy
    obtain ⟨v, τ, -, hτ⟩ := hTS J T hT y hy
    exact ⟨v, τ, hτ⟩
  have hsel : ∀ B : Finset P, B.card + t ≤ Fintype.card P → ∃ T, T ⊆ univ \ B ∧ T.card = t := by
    intro B hB
    exact exists_subset_card_eq (by rw [card_sdiff_of_subset (subset_univ _), card_univ]; omega)
  let pred : ℕ → Prop := fun i => 1 ≤ i ∧ ∃ T₁ : Finset P, T₁.card = t ∧
    (∀ q ∈ T₁, (e q : ℕ) ≠ i - 1) ∧ ∃ y ∉ T₁, (tsRun (M := M) A δ (I i) T₁).Decides A y b
  have hpn : pred (Fintype.card P) := by
    refine ⟨by omega, ?_⟩
    obtain ⟨T₁, hsub, hcard⟩ := hsel {e.symm ⟨Fintype.card P - 1, by omega⟩} (by simp; omega)
    obtain ⟨y, hy⟩ := hex T₁ hcard
    obtain ⟨v, hv⟩ := hdec (I (Fintype.card P)) T₁ hcard y hy
    refine ⟨T₁, hcard, fun q hq => hne q _ (by omega) ?_, y, hy, ?_⟩
    · have := hsub hq
      simpa using this
    · rw [hIn] at hv ⊢
      have hvb := lemma_4_3 A hA hU hTS hδ htf b hcard hy hv
      rwa [hvb] at hv
  have hex' : ∃ i, pred i := ⟨_, hpn⟩
  have hj : pred (Nat.find hex') := Nat.find_spec hex'
  have hjmin : ∀ m < Nat.find hex', ¬ pred m := fun m hm => Nat.find_min hex' hm
  have hjn : Nat.find hex' ≤ Fintype.card P := Nat.find_min' hex' hpn
  set j := Nat.find hex' with hj_def
  obtain ⟨hj1, T₁, hT₁, hT₁p, y₁, hy₁, hd₁⟩ := hj
  let p₁ := e.symm ⟨j - 1, by omega⟩
  let p₂ := e.symm ⟨j - 2, by omega⟩
  obtain ⟨T₀, hT₀sub, hT₀⟩ := hsel (T₁ ∪ {p₁, p₂}) (by
    have := card_union_le T₁ {p₁, p₂}
    have := card_insert_le p₁ {p₂}
    rw [card_singleton] at this; omega)
  have hT₀B : ∀ q ∈ T₀, q ∉ T₁ ∧ q ≠ p₁ ∧ q ≠ p₂ := by
    intro q hq
    have := hT₀sub hq
    simp only [mem_sdiff, mem_univ, true_and, mem_union, mem_insert, mem_singleton,
      not_or] at this
    exact this
  obtain ⟨y₀, hy₀⟩ := hex T₀ hT₀
  obtain ⟨v₀, hd₀⟩ := hdec (I (j - 1)) T₀ hT₀ y₀ hy₀
  have hv₀ : v₀ ≠ b := by
    intro hvb
    rw [hvb] at hd₀
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hj1' : j - 1 = 0 := by omega
      rw [hj1', hI0] at hd₀
      exact hab (lemma_4_3 A hA hU hTS hδ htf a hT₀ hy₀ hd₀).symm
    · refine hjmin (j - 1) (by omega) ⟨by omega, T₀, hT₀, fun q hq => ?_, y₀, hy₀, hd₀⟩
      have := hne q (j - 2) (by omega) (hT₀B q hq).2.2
      omega
  have hp₁T₁ : p₁ ∉ T₁ := fun h => hT₁p p₁ h (by simp [p₁])
  refine ⟨p₁, I (j - 1), I j, T₀, T₁, fun q hq => ?_, hT₀, hT₁, fun h => (hT₀B p₁ h).2.1 rfl,
    hp₁T₁, ?_, y₀, hy₀, y₁, hy₁, v₀, b, hd₀, hd₁, hv₀⟩
  · have := hne q (j - 1) (by omega) hq
    simp only [I]
    split_ifs <;> first | rfl | omega
  · rw [disjoint_left]; intro q hq; exact (hT₀B q hq).1

end FastByzantineConsensus
