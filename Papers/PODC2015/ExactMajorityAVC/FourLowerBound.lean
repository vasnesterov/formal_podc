import Papers.PODC2015.ExactMajorityAVC.FourMain
import Papers.PODC2015.ExactMajorityAVC.AVCCorrect
import Cslib.Computability.Distributed.PopulationProtocols.RandomScheduler

/-!
# Claim B.8: protocols preserving `#S0 − #S1` need `Ω(1/ϵ)` parallel time

The uniformly random scheduler on labelled agents (`Cslib.PopulationProtocol.uniformKernel`):
each step draws an ordered pair of distinct agents uniformly among the `n(n−1)` pairs.

Let `P` keep `#S0 − #S1` invariant in every interaction (`Invariant P`, which by
`theorem_B_1_invariant` holds for every correct symmetric four-state protocol). Start with
`#S0 − #S1 = D ≥ 0` (majority `S0`, `D = ϵn`) and at least one agent in the minority state `S1`.
No configuration of `C_0` contains `S1`, so the convergence time is at least the first time `τ`
at which no agent is in `S1`. We prove (`hitProb_le`)

  `P(τ ≤ t) ≤ t · 2(D + 1) / (n(n − 1))`,

following the proof of Claim B.8: the number of `S1` agents never drops by two in one step, and it
drops from `1` to `0` only if the unique `S1` agent meets one of the `D + 1` agents in `S0`.
Consequently (`sum_tail_ge`) `∑_{t<K} P(τ > t) ≥ K − p·K(K−1)/2` with `p = 2(D+1)/(n(n−1))`;
since `E[τ] = ∑_t P(τ > t)`, taking `K ≈ 1/p` gives `E[τ] ≥ n(n−1)/(4(D+1))` steps up to
rounding, i.e. parallel time `Ω(1/ϵ)`.

`P(τ ≤ t)` is defined by the first-step recursion `hitProb` (probability of having visited
`Z = {no agent in S1}` within `t` steps).
-/

namespace Podc.ExactMajorityAVC.Four

open Cslib.PopulationProtocol Cslib.Probability.Markov Q4

-- CSLib candidate (`Probability/Markov`)
/-- Probability of visiting `Z` within `t` steps of the chain `T`, started at `x`
(first-step recursion). -/
noncomputable def hitProb {Xs : Type*} [Fintype Xs] (T : Matrix Xs Xs ℝ) (Z : Xs → Prop)
    [DecidablePred Z] : ℕ → Xs → ℝ
  | 0, x => if Z x then 1 else 0
  | t + 1, x => if Z x then 1 else ∑ y, T x y * hitProb T Z t y

variable {A : Type*} [DecidableEq A] [Fintype A]

set_option linter.unusedSectionVars false

/-- Number of agents in state `q`. -/
def cnt (q : Q4) (C : Config A Q4) : ℕ := (Finset.univ.filter fun a => C a = q).card

/-- No agent is in the minority state `S1`. -/
def NoS1 (C : Config A Q4) : Prop := cnt S1 C = 0

instance : DecidablePred (NoS1 (A := A)) := fun _ => inferInstanceAs (Decidable (_ = _))

lemma cnt_eq_sum (q : Q4) (C : Config A Q4) :
    (cnt q C : ℤ) = ∑ a, if C a = q then (1 : ℤ) else 0 := by
  simp [cnt, Finset.sum_boole]

lemma cnt_interact (P : Protocol Q4) (q : Q4) (C : Config A Q4) {a b : A} (hab : a ≠ b) :
    (cnt q (P.interact C a b) : ℤ) = cnt q C - (if C a = q then 1 else 0) -
      (if C b = q then 1 else 0) + (if (P.δ (C a) (C b)).1 = q then 1 else 0) +
      (if (P.δ (C a) (C b)).2 = q then 1 else 0) := by
  rw [cnt_eq_sum, cnt_eq_sum, sum_interact P (fun s => if s = q then 1 else 0) C hab]

/-- `#S0 − #S1` of a labelled configuration. -/
def diffL (C : Config A Q4) : ℤ := (cnt S0 C : ℤ) - cnt S1 C

lemma dq_pair_eq {z : Q4 × Q4} {p q : Q4} (h : dq z.1 + dq z.2 = dq p + dq q) :
    ((if z.1 = S0 then (1 : ℤ) else 0) - (if z.1 = S1 then 1 else 0)) +
      ((if z.2 = S0 then 1 else 0) - (if z.2 = S1 then 1 else 0)) =
    ((if p = S0 then (1 : ℤ) else 0) - (if p = S1 then 1 else 0)) +
      ((if q = S0 then 1 else 0) - (if q = S1 then 1 else 0)) := by
  obtain ⟨z1, z2⟩ := z
  cases z1 <;> cases z2 <;> cases p <;> cases q <;> simp_all [dq]

lemma invariant_dq {P : Protocol Q4} (hP : Invariant P) (p q : Q4) :
    dq (P.δ p q).1 + dq (P.δ p q).2 = dq p + dq q := by
  have := hP p q
  rw [diff_pair] at this
  rw [this, show ({p, q} : Multiset Q4) = pair (p, q) from rfl, diff_pair]

/-- `#S0 − #S1` is preserved by every interaction. -/
lemma diffL_interact {P : Protocol Q4} (hP : Invariant P) (C : Config A Q4) {a b : A}
    (hab : a ≠ b) : diffL (P.interact C a b) = diffL C := by
  unfold diffL
  rw [cnt_interact P S0 C hab, cnt_interact P S1 C hab]
  have := dq_pair_eq (invariant_dq hP (C a) (C b))
  linarith

/-- The number of `S1` agents drops by at most one per step, and it drops only when an `S1` agent
meets an `S0` agent. -/
lemma cnt_S1_interact {P : Protocol Q4} (hP : Invariant P) (C : Config A Q4) {a b : A}
    (hab : a ≠ b) :
    (cnt S1 C : ℤ) - 1 ≤ cnt S1 (P.interact C a b) ∧
      ((C a = S1 ∧ C b = S0) ∨ (C a = S0 ∧ C b = S1) ∨
        (cnt S1 C : ℤ) ≤ cnt S1 (P.interact C a b)) := by
  rw [cnt_interact P S1 C hab]
  have h := invariant_dq hP (C a) (C b)
  generalize (P.δ (C a) (C b)) = z at h ⊢
  obtain ⟨z1, z2⟩ := z
  generalize C a = p at h ⊢
  generalize C b = q at h ⊢
  cases z1 <;> cases z2 <;> cases p <;> cases q <;> simp_all [dq] <;> omega

lemma hitProb_zero {Xs : Type*} [Fintype Xs] (T : Matrix Xs Xs ℝ) {Z : Xs → Prop}
    [DecidablePred Z] {x : Xs} (h : ¬ Z x) : hitProb T Z 0 x = 0 := by
  simp [hitProb, h]

lemma hitProb_succ {Xs : Type*} [Fintype Xs] (T : Matrix Xs Xs ℝ) {Z : Xs → Prop}
    [DecidablePred Z] {x : Xs} (h : ¬ Z x) (t : ℕ) :
    hitProb T Z (t + 1) x = ∑ y, T x y * hitProb T Z t y := by
  simp [hitProb, h]

lemma hitProb_nonneg_le_one {Xs : Type*} [Fintype Xs] [DecidableEq Xs] {T : Matrix Xs Xs ℝ}
    (hT : T ∈ Matrix.rowStochastic ℝ Xs) (Z : Xs → Prop) [DecidablePred Z] :
    ∀ t x, 0 ≤ hitProb T Z t x ∧ hitProb T Z t x ≤ 1
  | 0, x => by unfold hitProb; split_ifs <;> norm_num
  | t + 1, x => by
    unfold hitProb
    split_ifs
    · norm_num
    · have ih := hitProb_nonneg_le_one hT Z t
      have hrow : ∑ y, T x y = 1 := (Matrix.mem_rowStochastic_iff_sum.1 hT).2 x
      have h0 : ∀ y, 0 ≤ T x y := fun y => Matrix.nonneg_of_mem_rowStochastic hT
      constructor
      · exact Finset.sum_nonneg fun y _ => mul_nonneg (h0 y) (ih y).1
      · calc ∑ y, T x y * hitProb T Z t y ≤ ∑ y, T x y * 1 :=
              Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih y).2 (h0 y)
          _ = 1 := by simp [hrow]

/-- **Claim B.8 (tail bound).** If `P` preserves `#S0 − #S1`, then from every configuration with
`#S0 − #S1 = D` and at least one agent in `S1`, under the uniformly random scheduler the
probability that no agent is in `S1` at some time `≤ t` is at most `t · 2(D+1)/(n(n−1))`. -/
theorem hitProb_le {P : Protocol Q4} (hP : Invariant P) (hA : 2 ≤ Fintype.card A) {D : ℤ}
    (hD0 : 0 ≤ D) :
    ∀ (t : ℕ) (C : Config A Q4), diffL C = D → 1 ≤ cnt S1 C →
      hitProb (uniformKernel P) NoS1 t C ≤
        t * (2 * (D + 1) / (Fintype.card (Pairs A) : ℝ)) := by
  set N : ℝ := ((Fintype.card (Pairs A) : ℕ) : ℝ) with hNdef
  have hN : 0 < N := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hA
    have : Nonempty (Pairs A) := ⟨⟨(a, b), hab⟩⟩
    rw [hNdef]; exact_mod_cast Fintype.card_pos
  have hDR : (0 : ℝ) ≤ (D : ℝ) + 1 := by exact_mod_cast (by omega : (0 : ℤ) ≤ D + 1)
  have hT := uniformKernel_mem (A := A) P hA
  intro t
  induction t with
  | zero =>
    intro C _ hC
    rw [hitProb_zero _ (show ¬ NoS1 C by unfold NoS1; omega)]
    simp
  | succ t ih =>
    intro C hD hC
    rw [hitProb_succ _ (show ¬ NoS1 C by unfold NoS1; omega)]
    -- one step: average over the random pair
    have hmv : ∑ y, uniformKernel P C y * hitProb (uniformKernel P) NoS1 t y =
        ∑ ω : Pairs A, 1 / N * hitProb (uniformKernel P) NoS1 t (P.interact C ω.1.1 ω.1.2) := by
      exact randomMap_mulVec (fun _ : Pairs A => 1 / N)
        (fun ω C => P.interact C ω.1.1 ω.1.2) (hitProb (uniformKernel P) NoS1 t) C
    rw [hmv]
    set bad : Finset (Pairs A) := Finset.univ.filter fun ω =>
      (C ω.1.1 = S1 ∧ C ω.1.2 = S0) ∨ (C ω.1.1 = S0 ∧ C ω.1.2 = S1)
    -- bound for every pair
    have hterm : ∀ ω : Pairs A, hitProb (uniformKernel P) NoS1 t (P.interact C ω.1.1 ω.1.2) ≤
        t * (2 * (D + 1) / N) + if ω ∈ bad ∧ cnt S1 C = 1 then 1 else 0 := by
      intro ω
      have hD' : diffL (P.interact C ω.1.1 ω.1.2) = D := by rw [diffL_interact hP C ω.2, hD]
      obtain ⟨h1, h2⟩ := cnt_S1_interact hP C ω.2
      have hle1 := (hitProb_nonneg_le_one hT NoS1 t (P.interact C ω.1.1 ω.1.2)).2
      have htp : 0 ≤ (t : ℝ) * (2 * (D + 1) / N) := by positivity
      by_cases hcase : 1 ≤ cnt S1 (P.interact C ω.1.1 ω.1.2)
      · have := ih _ hD' hcase
        split_ifs <;> linarith
      · have hc1 : cnt S1 C = 1 := by omega
        have hb : ω ∈ bad := by
          simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases h2 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · omega
        simp only [hb, hc1, and_self, ↓reduceIte]; linarith
    -- the number of bad pairs
    have hbad : ((bad.card : ℕ) : ℝ) ≤ 2 * (D + 1) ∨ cnt S1 C ≠ 1 := by
      by_cases hc1 : cnt S1 C = 1
      · left
        have hS0 : cnt S0 C = D + 1 := by unfold diffL at hD; omega
        -- `bad` injects into `{S1 agent} × {S0 agents}` (twice)
        have hcard : bad.card ≤ 2 * (cnt S1 C * cnt S0 C) := by
          have h1 : bad ⊆ (Finset.univ.filter fun ω : Pairs A => C ω.1.1 = S1 ∧ C ω.1.2 = S0) ∪
              (Finset.univ.filter fun ω : Pairs A => C ω.1.1 = S0 ∧ C ω.1.2 = S1) := by
            intro ω hω
            simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hω
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hω
          have hinj : ∀ (p q : Q4), (Finset.univ.filter fun ω : Pairs A =>
              C ω.1.1 = p ∧ C ω.1.2 = q).card ≤ cnt p C * cnt q C := by
            intro p q
            rw [cnt, cnt, ← Finset.card_product]
            refine Finset.card_le_card_of_injOn (fun ω => ω.1) (fun ω hω => ?_) ?_
            · simp only [Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_ofPred_eq] at hω
              simp [hω.1, hω.2]
            · intro ω _ ω' _ h; exact Subtype.ext h
          calc bad.card ≤ _ := Finset.card_le_card h1
            _ ≤ _ := Finset.card_union_le _ _
            _ ≤ cnt S1 C * cnt S0 C + cnt S0 C * cnt S1 C := add_le_add (hinj _ _) (hinj _ _)
            _ = 2 * (cnt S1 C * cnt S0 C) := by ring
        rw [hc1, one_mul] at hcard
        have : ((bad.card : ℕ) : ℤ) ≤ 2 * (D + 1) := by rw [← hS0]; exact_mod_cast hcard
        exact_mod_cast this
      · right; exact hc1
    calc ∑ ω : Pairs A, 1 / N * hitProb (uniformKernel P) NoS1 t (P.interact C ω.1.1 ω.1.2)
        ≤ ∑ ω : Pairs A, 1 / N * (t * (2 * (D + 1) / N) +
            if ω ∈ bad ∧ cnt S1 C = 1 then 1 else 0) :=
          Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hterm ω) (by positivity)
      _ = t * (2 * (D + 1) / N) + 1 / N * ((Finset.univ.filter fun ω : Pairs A =>
            ω ∈ bad ∧ cnt S1 C = 1).card : ℝ) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, Finset.sum_boole, ← hNdef]
          field_simp
      _ ≤ (t + 1 : ℕ) * (2 * (D + 1) / N) := by
          push_cast
          rcases hbad with hb | hb
          · have : ((Finset.univ.filter fun ω : Pairs A => ω ∈ bad ∧ cnt S1 C = 1).card : ℝ) ≤
                2 * (D + 1) := by
              refine le_trans ?_ hb
              exact_mod_cast Finset.card_le_card fun ω hω => by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω; exact hω.1
            have : 1 / N * ((Finset.univ.filter fun ω : Pairs A => ω ∈ bad ∧ cnt S1 C = 1).card
                : ℝ) ≤ 2 * (D + 1) / N := by
              rw [div_mul_eq_mul_div, one_mul]; gcongr
            linarith
          · have : (Finset.univ.filter fun ω : Pairs A => ω ∈ bad ∧ cnt S1 C = 1) = ∅ := by
              ext ω; simp [hb]
            rw [this]
            have : (0 : ℝ) ≤ 2 * (D + 1) / N := by positivity
            simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero]
            nlinarith

/-- Consequence for the expected convergence time: `∑_{t<K} P(τ > t) ≥ K − p·K(K−1)/2` with
`p = 2(D+1)/(n(n−1))` (and `E[τ] = ∑_t P(τ > t)` is at least this partial sum). -/
theorem sum_tail_ge {P : Protocol Q4} (hP : Invariant P) (hA : 2 ≤ Fintype.card A) {D : ℤ}
    (hD0 : 0 ≤ D) {C : Config A Q4} (hD : diffL C = D) (hC : 1 ≤ cnt S1 C) (K : ℕ) :
    (K : ℝ) - 2 * (D + 1) / (Fintype.card (Pairs A) : ℝ) * (K * (K - 1) / 2) ≤
      ∑ t ∈ Finset.range K, (1 - hitProb (uniformKernel P) NoS1 t C) := by
  set p : ℝ := 2 * (D + 1) / (Fintype.card (Pairs A) : ℝ)
  have h : ∀ t : ℕ, 1 - t * p ≤ 1 - hitProb (uniformKernel P) NoS1 t C := fun t => by
    have := hitProb_le hP hA hD0 t C hD hC; linarith
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have := h K
    push_cast
    nlinarith

/-- Hitting a smaller set is less likely. -/
lemma hitProb_mono {Xs : Type*} [Fintype Xs] [DecidableEq Xs] {T : Matrix Xs Xs ℝ}
    (hT : T ∈ Matrix.rowStochastic ℝ Xs) {Z Z' : Xs → Prop} [DecidablePred Z] [DecidablePred Z']
    (hZ : ∀ x, Z' x → Z x) : ∀ t x, hitProb T Z' t x ≤ hitProb T Z t x
  | 0, x => by
    unfold hitProb
    by_cases h' : Z' x
    · simp [h', hZ x h']
    · simp only [h', ↓reduceIte]; split_ifs <;> norm_num
  | t + 1, x => by
    have h0 : ∀ y, 0 ≤ T x y := fun y => Matrix.nonneg_of_mem_rowStochastic hT
    by_cases h' : Z' x
    · simp [hitProb, h', hZ x h']
    · by_cases h : Z x
      · rw [hitProb_succ T h', show hitProb T Z (t + 1) x = 1 by simp [hitProb, h]]
        calc ∑ y, T x y * hitProb T Z' t y ≤ ∑ y, T x y * 1 :=
              Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
                (hitProb_nonneg_le_one hT Z' t y).2 (h0 y)
          _ = 1 := by simp [(Matrix.mem_rowStochastic_iff_sum.1 hT).2 x]
      · rw [hitProb_succ T h', hitProb_succ T h]
        exact Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (hitProb_mono hT hZ t y) (h0 y)

/-- **Theorem B.1** (lower bound, tail form). Let `P` be a symmetric four-state protocol satisfying
the three correctness properties, run under the uniformly random scheduler on `n ≥ 2` agents,
started from a configuration with `#S0 − #S1 = D ≥ 0` (`D = ϵn` for an initial configuration)
and at least one agent in `S1`. The probability of reaching, within `t` steps, a configuration
in which all agents output `0` (in particular any configuration of `C_0`) is at most
`t · 2(D + 1)/(n(n − 1))`. Hence with probability at least `1/2` convergence takes at least
`n(n−1)/(4(D+1))` steps, i.e. parallel time `Ω(1/ϵ)`. -/
theorem theorem_B_1 {P : Protocol Q4} {γ : Q4 → Bool} (hC : Correct P γ) (hS : Symmetric P)
    (hA : 2 ≤ Fintype.card A) {D : ℤ} (hD0 : 0 ≤ D) (C : Config A Q4) (hD : diffL C = D)
    (hC1 : 1 ≤ cnt S1 C) (t : ℕ) :
    hitProb (uniformKernel P) (fun C : Config A Q4 => ∀ a, γ (C a) = false) t C ≤
      t * (2 * (D + 1) / (Fintype.card (Pairs A) : ℝ)) := by
  have g1 : γ S1 = true := gamma_S hC true
  classical
  refine le_trans (hitProb_mono (uniformKernel_mem P hA) (Z := NoS1) (fun E hE => ?_) t C)
    (hitProb_le (theorem_B_1_invariant hC hS) hA hD0 t C hD hC1)
  unfold NoS1 cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ ha
  have := hE a; rw [ha, g1] at this; cases this

end Podc.ExactMajorityAVC.Four
