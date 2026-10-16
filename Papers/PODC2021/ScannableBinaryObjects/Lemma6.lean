import Papers.PODC2021.ScannableBinaryObjects.Lemma5Step
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Lemma 6 and the reduction (Lemma 7) of Ovens (PODC 2021), for stages

* `lemma6_stage`: a stage with at least two active processes and `k' ≥ 2` live components has
  at least `k' + 1` base objects outside the frozen set.
* `reduce_stage` (replaces Lemma 7): from a stage with `k' ≥ 2` live components we obtain a stage
  with `k' - 1` live components, `h` active processes fewer and `h` frozen objects more, for any
  `h ≤ min(|A| - 1, 2^(k'-1))`. (The paper builds a new implementation `I'` by simulation; the
  executions of `I'` are exactly the restricted executions of `I` from the new stage.)
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

open Cslib.SharedMemory

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]
  {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type} {I : Impl (scannable O) B P L} {p₀ : P}

/-- The vector whose live components (`< k'`) are the binary digits of `t`, `0` elsewhere. -/
def wvec (k' t : ℕ) : Fin k → Bool := fun c => if c.val < k' then t.testBit c.val else false

lemma wvec_inj {k' t t' : ℕ} (hk : k' ≤ k) (ht : t < 2 ^ k') (ht' : t' < 2 ^ k')
    (h : (wvec k' t : Fin k → Bool) = wvec k' t') : t = t' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k'
  · have := congrFun h ⟨i, by omega⟩
    simpa [wvec, hi] using this
  · have h2 : 2 ^ k' ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

lemma vec_zero_eq_wvec {k' : ℕ} (hk : 1 ≤ k') :
    (vec k' 0 : Fin k → Bool) = wvec k' (2 ^ (k' - 1)) := by
  funext c
  simp only [vec, wvec, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases h1 : c.val + 1 < k'
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; simp; omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : c.val < k'
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]; simp; omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]; simp; omega

variable (hnm : ∀ c, (O c).NonMonotonic) (hof : I.ObstructionFree)
  (hall : ∀ p o, SingleUpdater p₀ p o → I.allowed p o) (hlin : I.Linearizable)
  (hbit : ∀ i, OneBit (B i).State)

include hnm hof hall hlin hbit in
/-- **Lemma 6** (for stages): at least `k' + 1` base objects outside the frozen set. -/
theorem lemma6_stage [Fintype ι] {ε X A F k'} (hS : Stage I p₀ ε X A F k') (hk : 2 ≤ k')
    (hA : 2 ≤ A.card) : F.card + k' + 1 ≤ Fintype.card ι := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨α, X1, A1, B1, hR⟩ := lemma5 hnm hof hall hlin hbit hS 1 (by omega)
    (Nat.one_le_two_pow)
  obtain ⟨b, hb⟩ := Finset.card_eq_one.1 hR.bcard
  have hbF : b ∉ F := fun h => Finset.disjoint_left.1 hR.disj (by simp [hb]) h
  obtain ⟨s, hsA, hs1⟩ : ∃ s ∈ A, s ∉ A1 := by
    by_contra hc; push Not at hc
    have := Finset.card_le_card (show A ⊆ A1 from hc); have := hR.card; omega
  have hs0 : s ≠ p₀ := fun e => hs1 (e ▸ hR.p0)
  set E := ε ++ α with hEdef
  have hE : I.run E = some X1 := run_append_eq hS.run hR.run
  have hsuE : SUExec p₀ E := suExec_append.2 ⟨hS.su, hR.lim.su⟩
  have hk1 := hS.k'le
  set top : Fin k := ⟨k' - 1, by omega⟩ with htopdef
  have htop : top.val + 1 = k' := by simp [top]; omega
  have hEtop : curVal p₀ E top = false := hR.high top (by omega)
  -- the targets `U_t`, `t ∈ T` (all vectors over the live components except `V₁`)
  set T := (Finset.range (2 ^ k')).erase (2 ^ (k' - 1)) with hT
  have hgo : ∀ t, ∃ lam Y, t ∈ T → I.runFrom X1 lam = some Y ∧ Lim p₀ {p₀} k' lam ∧
      (∀ ℓ ∈ lam, ℓ.proc = p₀) ∧ Y.pend p₀ = none ∧ curVal p₀ (E ++ lam) = wvec k' t ∧
      Absent p₀ (Vset k' 1) E lam := by
    intro t
    by_cases ht : t ∉ T
    · exact ⟨[], X1, fun h => absurd h ht⟩
    rw [not_not] at ht
    obtain ⟨lam, Y, hl1, hl2, hl3, hl4, hl5, hl6⟩ := goTo_exec hnm hof hall htop hE
      (hR.idle _ hR.p0) (wvec k' t) (fun c hc => by
        rw [hR.high c (by omega)]; simp [wvec]; omega)
    refine ⟨lam, Y, fun _ => ⟨hl1, hl4, hl3, hl2, hl5, ?_⟩⟩
    intro i h1 h2 hm
    obtain ⟨u, rfl⟩ : ∃ u, i = (opsOf E p₀).length + u := ⟨i - (opsOf E p₀).length, by omega⟩
    by_cases hu : u < (opsOf lam p₀).length
    · have h6 := hl6 u hu
      rw [hEtop] at h6
      have := Vset_top htop hm
      rw [h6] at this; exact Bool.false_ne_true this
    · have heq : (opsOf E p₀).length + u = (opsOf (E ++ lam) p₀).length := by
        simp only [opsOf_append, List.length_append] at h2 ⊢; omega
      rw [heq] at hm
      change curVal p₀ (E ++ lam) ∈ _ at hm
      rw [hl5] at hm
      obtain ⟨t', ht', he⟩ := hm
      have ht'0 : t' = 0 := by omega
      subst ht'0
      rw [vec_zero_eq_wvec (by omega)] at he
      have := wvec_inj hk1 (Finset.mem_range.1 (Finset.mem_of_mem_erase ht))
        (Nat.pow_lt_pow_right (by omega) (by omega)) he
      exact (Finset.ne_of_mem_erase ht) this
  choose lam Y hgo using hgo
  have hl1 := fun t ht => (hgo t ht).1
  have hl2 := fun t ht => (hgo t ht).2.1
  have hl3 := fun t ht => (hgo t ht).2.2.1
  have hl4 := fun t ht => (hgo t ht).2.2.2.1
  have hl5 := fun t ht => (hgo t ht).2.2.2.2.1
  have hl6 := fun t ht => (hgo t ht).2.2.2.2.2
  -- memory of `Y t` outside `F ∪ {b}` encoded in bits
  have enc : ∀ i, ∃ f : (B i).State → Bool, Function.Injective f := hbit
  choose f hf using enc
  have hcardS : Fintype.card {i : ι // i ∉ F ∧ i ≠ b} + F.card + 1 = Fintype.card ι := by
    have h1 : Fintype.card {i : ι // i ∉ F ∧ i ≠ b} = (Finset.univ.filter (fun i => i ∉ F ∧ i ≠ b)).card :=
      Fintype.card_subtype _
    have h2 : (Finset.univ.filter (fun i => i ∉ F ∧ i ≠ b)) = (insert b F)ᶜ := by
      ext i; simp [and_comm]
    rw [h1, h2, Finset.card_compl, Finset.card_insert_of_notMem hbF]
    have := Finset.card_le_univ (insert b F)
    rw [Finset.card_insert_of_notMem hbF] at this
    omega
  let g : ℕ → ({i : ι // i ∉ F ∧ i ≠ b} → Bool) := fun t i => f i.1 ((Y t).mem i.1)
  have hcardT : T.card = 2 ^ k' - 1 := by
    rw [hT, Finset.card_erase_of_mem (Finset.mem_range.2
      (Nat.pow_lt_pow_right (by omega) (by omega))), Finset.card_range]
  have hlt2 : (Finset.univ : Finset ({i : ι // i ∉ F ∧ i ≠ b} → Bool)).card < T.card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, hcardT]
    have hS' : Fintype.card {i : ι // i ∉ F ∧ i ≠ b} ≤ k' - 1 := by omega
    have : 2 ^ Fintype.card {i : ι // i ∉ F ∧ i ≠ b} ≤ 2 ^ (k' - 1) := Nat.pow_le_pow_right (by omega) hS'
    have : 2 ^ k' = 2 * 2 ^ (k' - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : 2 ≤ 2 ^ (k' - 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (k' - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  obtain ⟨t1, ht1, t2, ht2, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt2
    (f := g) (fun _ _ => Finset.mem_univ _)
  -- the memories coincide
  have hmemF : ∀ t ∈ T, ∀ i ∈ F, (Y t).mem i = X.mem i := fun t ht i hi =>
    hS.frozen (α ++ lam t) (Y t)
      (lim_append.2 ⟨hR.lim, (hl2 t ht).mono (by simp [hS.p0A]) le_rfl⟩)
      (by rw [I.runFrom_append_of_eq hR.run, hl1 t ht]) i hi
  have hmemb : ∀ t ∈ T, (Y t).mem b = X1.mem b := fun t ht =>
    hR.fixed (lam t) (Y t) ((hl2 t ht).mono (by simp [hR.p0]) le_rfl) (hl6 t ht) (hl1 t ht) b
      (by simp [hb])
  have hmem : (Y t1).mem = (Y t2).mem := by
    funext i
    by_cases hiF : i ∈ F
    · rw [hmemF t1 ht1 i hiF, hmemF t2 ht2 i hiF]
    · by_cases hib : i = b
      · subst hib; rw [hmemb t1 ht1, hmemb t2 ht2]
      · exact hf i (congrFun heq ⟨i, hiF, hib⟩)
  have hsY : ∀ t ∈ T, (Y t).loc s = X1.loc s ∧ (Y t).pend s = X1.pend s := fun t ht =>
    I.runFrom_other (hl1 t ht) (q := s) (fun ℓ hℓ he => hs0 (by rw [← he]; exact hl3 t ht ℓ hℓ))
  have hag : Impl.AgreeOn ({s} : Set P) (Y t1) (Y t2) :=
    ⟨hmem, fun q hq => by rw [Set.mem_singleton_iff.1 hq, (hsY t1 ht1).1, (hsY t2 ht2).1],
      fun q hq => by rw [Set.mem_singleton_iff.1 hq, (hsY t1 ht1).2, (hsY t2 ht2).2]⟩
  -- `s` completes its pending scan, then scans again
  have hY1 : I.run (E ++ lam t1) = some (Y t1) := run_append_eq hE (hl1 t1 ht1)
  have hY2 : I.run (E ++ lam t2) = some (Y t2) := run_append_eq hE (hl1 t2 ht2)
  obtain ⟨τ, W1, hw1, hw2, hw3, hw4⟩ := quiesce hof [s] hY1
  obtain ⟨W2, hw5, hag2⟩ := Impl.runFrom_agreeOn hag (fun ℓ hℓ => by simpa using hw3 ℓ hℓ) hw1
  have hτ0 : opsOf τ p₀ = [] := hw2 p₀
  have hsu : ∀ t ∈ T, SUExec p₀ (E ++ lam t ++ τ) := fun t ht =>
    suExec_append.2 ⟨suExec_append.2 ⟨hsuE, (hl2 t ht).su⟩, (lim_of_noInv (A := {s}) (k' := k')
      hw2 (fun ℓ hℓ => by simpa using hw3 ℓ hℓ)).su⟩
  have hp0W : ∀ (t : ℕ) (W : Config (scannable O) B P L), t ∈ T →
      I.runFrom (Y t) τ = some W → W.pend p₀ = none := fun t W ht hW => by
    rw [(I.runFrom_other hW (q := p₀) (fun ℓ hℓ he => hs0 (by
      rw [← he]; exact (by simpa using hw3 ℓ hℓ : ℓ.proc = s).symm))).2]; exact hl4 t ht
  have hcur : ∀ t ∈ T, curVal p₀ (E ++ lam t ++ τ) = wvec k' t := fun t ht => by
    rw [← hl5 t ht, curVal_append, hτ0]; rfl
  obtain ⟨Z1, -, -, -, -, hr1⟩ := solo_scan hof hall hlin (run_append_eq hY1 hw1) (hsu t1 ht1)
    (hp0W t1 W1 ht1 hw1) hs0 (hw4 s (by simp))
  obtain ⟨Z2, -, -, -, -, hr2⟩ := solo_scan hof hall hlin (run_append_eq hY2 hw5) (hsu t2 ht2)
    (hp0W t2 W2 ht2 hw5) hs0 (by rw [← hag2.pend s rfl]; exact hw4 s (by simp))
  rw [Impl.soloOp_eq_of_agree (hag2.agree rfl), hr2, hcur t1 ht1, hcur t2 ht2] at hr1
  simp only [List.cons.injEq, ScanResp.view.injEq, and_true] at hr1
  exact hne (wvec_inj hk1 (Finset.mem_range.1 (Finset.mem_of_mem_erase ht1))
    (Finset.mem_range.1 (Finset.mem_of_mem_erase ht2)) hr1.symm)

include hnm hof hall hlin hbit in
/-- **Reduction (replaces Lemma 7).** From a stage with `k' ≥ 2` live components and any
`h ≤ min(|A| - 1, 2^(k'-1))`, a stage with one live component fewer, `h` active processes fewer
and `h` frozen objects more. -/
theorem reduce_stage {ε X A F k'} (hS : Stage I p₀ ε X A F k') (hk : 2 ≤ k') {h : ℕ}
    (hh1 : h + 1 ≤ A.card) (hh2 : h ≤ 2 ^ (k' - 1)) :
    ∃ ε' X' A' F', Stage I p₀ ε' X' A' F' (k' - 1) ∧ A'.card + h = A.card ∧
      F'.card = F.card + h := by
  classical
  obtain ⟨α, Xh, Ah, Bh, hR⟩ := lemma5 hnm hof hall hlin hbit hS h hh1 hh2
  set E := ε ++ α with hEdef
  have hE : I.run E = some Xh := run_append_eq hS.run hR.run
  have hk1 := hS.k'le
  set top' : Fin k := ⟨k' - 2, by omega⟩
  have htop' : top'.val + 1 = k' - 1 := by simp [top']; omega
  set top : Fin k := ⟨k' - 1, by omega⟩
  -- `κ`: `p₀` resets all components to `0`
  obtain ⟨κ, X', hk1', hk2', hk3', hk4', hk5', -⟩ := goTo_exec hnm hof hall htop' hE
    (hR.idle _ hR.p0) (fun _ => false) (fun c hc => hR.high c (by omega))
  refine ⟨E ++ κ, X', Ah, F ∪ Bh, ?_, hR.card, ?_⟩
  · exact
    { run := run_append_eq hE hk1'
      su := suExec_append.2 ⟨suExec_append.2 ⟨hS.su, hR.lim.su⟩, hk4'.su⟩
      p0A := hR.p0
      idle := fun p hp => by
        by_cases hp0 : p = p₀
        · subst hp0; exact hk2'
        · rw [(I.runFrom_other hk1' (q := p) (fun ℓ hℓ he => hp0 (by
            rw [← he]; exact hk3' ℓ hℓ))).2]
          exact hR.idle p hp
      k'pos := by omega
      k'le := by omega
      high := fun c _ => by rw [hk5']
      frozen := by
        intro β G hβL hβ i hi
        have hκβ : I.runFrom Xh (κ ++ β) = some G := by rw [I.runFrom_append_of_eq hk1', hβ]
        rcases Finset.mem_union.1 hi with hi | hi
        · have e1 := hS.frozen (α ++ (κ ++ β)) G
            (lim_append.2 ⟨hR.lim, lim_append.2 ⟨hk4'.mono (by simp [hS.p0A]) (by omega),
              hβL.mono hR.sub (by omega)⟩⟩)
            (by rw [I.runFrom_append_of_eq hR.run, hκβ]) i hi
          have e2 := hS.frozen (α ++ κ) X'
            (lim_append.2 ⟨hR.lim, hk4'.mono (by simp [hS.p0A]) (by omega)⟩)
            (by rw [I.runFrom_append_of_eq hR.run, hk1']) i hi
          exact e1.trans e2.symm
        · have hlim : Lim p₀ Ah (k' - 1) (κ ++ β) :=
            lim_append.2 ⟨hk4'.mono (by simp [hR.p0]) le_rfl, hβL⟩
          have habs : ∀ γ, Lim p₀ Ah (k' - 1) γ → Absent p₀ (Vset k' h) E γ := fun γ hγ =>
            absent_of_top hγ (top := top) (by simp [top]) (hR.high top (by simp [top]; omega))
              (fun v hv => Vset_top (by simp [top]; omega) hv)
          have e1 := hR.fixed (κ ++ β) G (hlim.mono subset_rfl (by omega)) (habs _ hlim) hκβ i hi
          have e2 := hR.fixed κ X' (hk4'.mono (by simp [hR.p0]) (by omega))
            (habs _ (hk4'.mono (by simp [hR.p0]) le_rfl)) hk1' i hi
          exact e1.trans e2.symm }
  · rw [Finset.card_union_of_disjoint hR.disj.symm, hR.bcard]

end Cslib.SharedMemory.Scannable
