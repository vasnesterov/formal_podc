import Papers.PODC2019.MinimalSymmetryBreaking.Speedup

/-!
# First speedup lemma (Lemma 7 for `Δ = 4`, Lemma 14 for `Δ = 2k`)

From a `(t+1)`-round node algorithm `A` for weak `c`-colouring we build a `t`-round edge algorithm
(`speedEdge A f`): the edge `e = {v, v gᵈ}` outputs the pair of sets of colours that are
*frequent* (probability `≥ f`) for `v` and for `v gᵈ`, given the random values within distance `t`
of `e`. We prove (`speedup1_ineq`) that for every threshold `f ≥ 0`
`f^Δ · (p' - Δ c f) ≤ p`, where `p` and `p'` are the local failure probabilities of `A` and of
the edge algorithm. This is the inequality `p ≥ (p' − 4cf) f⁴` of the paper's proof.
-/

namespace Podc.MinimalSymmetryBreaking

open Finset Function
open scoped Classical

noncomputable section

variable {k : ℕ} {Ω : Type} [Fintype Ω] [Inhabited Ω] (μ : FinDist Ω) {t : ℕ} {α : Type}
  [Fintype α]

/-- The nodes within distance `t` of the edge `{1, dir p}`. -/
def eReg (t : ℕ) (p : Fin k × Bool) : Set (Tree k) := ball 1 t ∪ ball (dir p) t

/-- Probability that the origin gets colour `i`, given the values near the edge `{1, dir p}`. -/
def frqO (A : NodeAlg k Ω (t + 1) α) (p : Fin k × Bool) (i : α) (x : Tree k → Ω) : ℝ :=
  cond μ (Ball (t + 3)) (eReg t p) (fun z => A.out z = i) x

/-- Probability that the neighbour `dir p` gets colour `i`, given the values near the edge
`{1, dir p}`. -/
def frqN (A : NodeAlg k Ω (t + 1) α) (p : Fin k × Bool) (i : α) (x : Tree k → Ω) : ℝ :=
  cond μ (Ball (t + 3)) (eReg t p) (fun z => A.out (shift (dir p) z) = i) x

/-- **The simulation of Lemma 7.** The edge `{1, gᵈ}` outputs the set of colours that are
frequent for its lower endpoint `1` and for its upper endpoint `gᵈ`. -/
def speedEdge (A : NodeAlg k Ω (t + 1) α) (f : ℝ) : EdgeAlg k Ω t (Finset α × Finset α) where
  out d x := (univ.filter fun i => f ≤ frqO μ A (d, true) i x,
    univ.filter fun i => f ≤ frqN μ A (d, true) i x)
  dep d := by
    intro x x' h
    have e1 : ∀ i, cond μ (Ball (t + 3)) (eReg t (d, true)) (fun z => A.out z = i) x =
        cond μ (Ball (t + 3)) (eReg t (d, true)) (fun z => A.out z = i) x' :=
      fun i => cond_dependsOn _ _ _ h
    have e2 : ∀ i, cond μ (Ball (t + 3)) (eReg t (d, true))
        (fun z => A.out (shift (dir (d, true)) z) = i) x =
        cond μ (Ball (t + 3)) (eReg t (d, true)) (fun z => A.out (shift (dir (d, true)) z) = i) x' :=
      fun i => cond_dependsOn _ _ _ h
    show (_, _) = (_, _)
    rw [Prod.mk.injEq]
    exact ⟨Finset.filter_congr fun i _ => by simp only [frqO, e1],
      Finset.filter_congr fun i _ => by simp only [frqN, e2]⟩

variable {μ}

lemma dependsOn_eq {β : Type*} {g : (Tree k → Ω) → β} {S : Set (Tree k)} (hg : DependsOn g S)
    (i : β) : DependsOn (fun z => g z = i) S := by
  intro x x' h; simp only [hg h]

lemma dir_mul_dir_not (p : Fin k × Bool) : dir p * dir (p.1, !p.2) = (1 : Tree k) := by
  rw [← dir_inv]; group

lemma dir_not_mul_dir (p : Fin k × Bool) : dir (p.1, !p.2) * dir p = (1 : Tree k) := by
  rw [← dir_inv]; group

lemma dir_false_eq (d : Fin k) : dir (d, false) = (dir (d, true))⁻¹ := by
  simpa using (dir_inv (d, true)).symm

lemma dir_false_mul_dir_true (d : Fin k) : dir (d, false) * dir (d, true) = (1 : Tree k) := by
  rw [dir_false_eq]; group

lemma norm_dir_mul_le (p : Fin k × Bool) (w : Tree k) : (dir p * w).norm ≤ w.norm + 1 := by
  rcases norm_dir_mul_cases p w with h | h <;> omega

lemma preimage_eReg (d : Fin k) (t : ℕ) :
    (fun w => (dir (d, false))⁻¹ * w) ⁻¹' eReg t (d, true) = eReg t (d, false) := by
  unfold eReg
  rw [Set.preimage_union, preimage_inv_mul_ball, preimage_inv_mul_ball, mul_one,
    dir_false_mul_dir_true, Set.union_comm]

/-- The frequency of a colour at the origin, seen from the shifted field, is the frequency at the
neighbour `gᵈ⁻¹` for the edge `{gᵈ⁻¹, 1}`. -/
lemma frqO_shift (A : NodeAlg k Ω (t + 1) α) (d : Fin k) (i : α) (x : Tree k → Ω) :
    frqO μ A (d, true) i (shift (dir (d, false)) x) = frqN μ A (d, false) i x := by
  unfold frqO frqN
  rw [cond_shift (D := ball 1 (t + 1)) (dependsOn_eq A.dep i) (ball_mono (by omega))
    (fun w hw => by
      have := norm_dir_mul_le (d, false) w; simp only [mem_ball, inv_one, one_mul] at hw; omega),
    preimage_eReg]

lemma frqN_shift (A : NodeAlg k Ω (t + 1) α) (d : Fin k) (i : α) (x : Tree k → Ω) :
    frqN μ A (d, true) i (shift (dir (d, false)) x) = frqO μ A (d, false) i x := by
  unfold frqO frqN
  rw [cond_shift (D := ball (dir (d, true)) (t + 1)) (dependsOn_eq (A.dep_shift _) i)
    ((ball_dir_subset_one _ _).trans (ball_mono (by omega)))
    (fun w hw => by
      simp only [mem_ball] at hw
      rw [dir_false_eq]
      omega),
    preimage_eReg]
  congr 1
  funext z
  rw [shift_shift, dir_false_mul_dir_true, shift_one]

/-- If the edge algorithm fails at the origin and the true colour of the origin is frequent for
the origin on all its edges, then it is frequent for every neighbour. -/
lemma speedEdge_fail_good (A : NodeAlg k Ω (t + 1) α) (f : ℝ) (x : Tree k → Ω)
    (hF : (speedEdge μ A f).Fail x) (hg : ∀ p, f ≤ frqO μ A p (A.out x) x) :
    ∀ p, f ≤ frqN μ A p (A.out x) x := by
  rintro ⟨d, b⟩
  have hd := hF d
  simp only [speedEdge, Prod.mk.injEq] at hd
  cases b with
  | true =>
    have h1 := hd.2
    have : A.out x ∈ univ.filter fun i => f ≤ frqN μ A (d, true) i (shift (dir (d, false)) x) := by
      simp only [mem_filter, mem_univ, true_and, frqN_shift]; exact hg (d, false)
    rw [← h1] at this
    simpa using this
  | false =>
    have h1 := hd.1
    have : A.out x ∈ univ.filter fun i => f ≤ frqO μ A (d, true) i x := by
      simpa using hg (d, true)
    rw [h1] at this
    simpa [frqO_shift] using this

lemma eReg_subset (p : Fin k × Bool) (t : ℕ) : eReg t p ⊆ ball (1 : Tree k) (t + 1) :=
  Set.union_subset (ball_mono (Nat.le_succ t)) (ball_dir_subset_one p t)

/-- Given the values within distance `t + 1` of the origin, the conditional probability that the
neighbour `dir p` gets colour `c` only depends on the values near the edge `{1, dir p}`. -/
lemma cond_ball_eq_frqN (A : NodeAlg k Ω (t + 1) α) (p : Fin k × Bool) (c : α)
    (x : Tree k → Ω) :
    cond μ (Ball (t + 3)) (ball 1 (t + 1)) (fun z => A.out (shift (dir p) z) = c) x =
      frqN μ A p c x := by
  unfold cond frqN cond
  refine condE_eq_of_dependsOn (D := ball (dir p) (t + 1) \ ball 1 (t + 1)) ?_ (eReg_subset p t)
    Set.disjoint_sdiff_left x
  apply (ind_dependsOn (dependsOn_eq (A.dep_shift (dir p)) c)).mono
  intro w hw
  by_cases hS : w ∈ ball (1 : Tree k) (t + 1)
  · left
    have := ball_inter_ball_subset (1 : Tree k) p t ⟨hS, by simpa using hw⟩
    simpa [eReg] using this
  · right; exact ⟨hw, hS⟩

/-- **First speedup inequality** (proof of Lemma 7 / Lemma 14): for every threshold `f ≥ 0`,
`f^(2k) · (p' − 2k·c·f) ≤ p`, where `p` is the local failure probability of the node algorithm
`A`, `p'` the one of the simulating edge algorithm, and `c = |α|`. -/
theorem speedup1_ineq (A : NodeAlg k Ω (t + 1) α) {f : ℝ} (hf : 0 ≤ f) :
    f ^ (2 * k) * ((speedEdge μ A f).failProb μ - 2 * k * Fintype.card α * f) ≤ A.failProb μ := by
  set F : Finset (Tree k) := Ball (t + 3)
  set S : Set (Tree k) := ball 1 (t + 1)
  set B := speedEdge μ A f
  let good : (Tree k → Ω) → Prop := fun x => ∀ p, f ≤ frqO μ A p (A.out x) x
  let K : (Tree k → Ω) → Prop := fun x => ∀ p, f ≤ frqN μ A p (A.out x) x
  -- the failure probabilities computed with the common support `F`
  have hA : A.failProb μ = prob μ F A.Fail := by
    unfold NodeAlg.failProb prob
    refine (expect_eq_of_subset (Ball_mono (by omega)) ?_).symm
    rw [coe_Ball]; exact ind_dependsOn A.fail_dependsOn
  have hB : B.failProb μ = prob μ F B.Fail := by
    unfold EdgeAlg.failProb prob
    refine (expect_eq_of_subset (Ball_mono (by omega)) ?_).symm
    rw [coe_Ball]; exact ind_dependsOn B.fail_dependsOn
  -- `K` depends on the values within distance `t + 1`
  have hK : DependsOn (ind K) S := by
    apply ind_dependsOn
    intro x x' h
    have hA' : A.out x = A.out x' := A.dep h
    simp only [K, hA']
    apply propext; apply forall_congr'; intro p
    rw [show frqN μ A p (A.out x') x = frqN μ A p (A.out x') x' from
      cond_dependsOn _ _ _ (fun w hw => h w (eReg_subset p t hw))]
  -- Step A: `f^(2k) Pr[K] ≤ p`
  have stepA : f ^ (2 * k) * prob μ F K ≤ prob μ F A.Fail := by
    have hprod : ∀ x, condE μ F S (fun z => ∏ p, ind (fun z => A.out (shift (dir p) z) = A.out z) z) x
        = ∏ p, frqN μ A p (A.out x) x := by
      intro x
      rw [condE_congr (h' := fun z => ∏ p, ind (fun z => A.out (shift (dir p) z) = A.out x) z)]
      · rw [condE_prod (D := fun p => ball (dir p) (t + 1) \ S) univ]
        · exact prod_congr rfl fun p _ => cond_ball_eq_frqN A p _ x
        · intro p _
          apply (ind_dependsOn (dependsOn_eq (A.dep_shift (dir p)) _)).mono
          intro w hw
          by_cases hS : w ∈ S
          · left; exact hS
          · right; exact ⟨hw, hS⟩
        · intro p _ q _ hpq
          simpa using disjoint_diff (1 : Tree k) hpq (t + 1)
      · intro z
        have : A.out (S.piecewise x z) = A.out x :=
          A.dep (fun w hw => by simp only [Set.piecewise, if_pos (show w ∈ S from hw)])
        simp only [ind, this]
    calc f ^ (2 * k) * prob μ F K = expect μ F (fun x => ind K x * f ^ (2 * k)) := by
          unfold prob; rw [expect_mul_const, mul_comm]
      _ ≤ expect μ F (fun x => ind K x * ∏ p, frqN μ A p (A.out x) x) := by
          apply expect_mono; intro x
          by_cases hx : K x
          · simp only [ind, hx, if_true, one_mul]
            calc f ^ (2 * k) = ∏ _p : Fin k × Bool, f := by
                  simp [Finset.prod_const, Fintype.card_prod, mul_comm]
              _ ≤ ∏ p, frqN μ A p (A.out x) x :=
                  Finset.prod_le_prod₀ (fun _ _ => hf) (fun p _ => hx p)
          · simp [ind, hx]
      _ = expect μ F (fun x => ind K x *
            ∏ p, ind (fun z => A.out (shift (dir p) z) = A.out z) x) := by
          simp only [← hprod]
          exact expect_mul_condE hK _
      _ ≤ prob μ F A.Fail := by
          unfold prob; apply expect_mono; intro x
          rw [show ind A.Fail x = ∏ p, ind (fun z => A.out (shift (dir p) z) = A.out z) x from
            ind_forall (fun p z => A.out (shift (dir p) z) = A.out z) x]
          calc ind K x * ∏ p, ind (fun z => A.out (shift (dir p) z) = A.out z) x
              ≤ 1 * ∏ p, ind (fun z => A.out (shift (dir p) z) = A.out z) x :=
                mul_le_mul_of_nonneg_right (ind_le_one _ _) (prod_ind_nonneg _ x)
            _ = _ := one_mul _
  -- Step B: `p' ≤ Pr[K] + Pr[¬ good]`
  have stepB : prob μ F B.Fail ≤ prob μ F K + prob μ F (fun x => ¬ good x) := by
    unfold prob
    rw [← expect_add]
    apply expect_mono; intro x
    by_cases hg : good x
    · by_cases hF : B.Fail x
      · have hK' : K x := speedEdge_fail_good A f x hF hg
        simp [ind, hF, hK', hg]
      · simp only [ind, hF, if_false]
        split_ifs <;> norm_num
    · simp only [ind, hg, not_false_eq_true, if_true]
      split_ifs <;> norm_num
  -- Step C: `Pr[¬ good] ≤ 2k c f`
  have stepC : prob μ F (fun x => ¬ good x) ≤ 2 * k * Fintype.card α * f := by
    calc prob μ F (fun x => ¬ good x)
        ≤ expect μ F (fun x => ∑ p : Fin k × Bool, ind (fun x => frqO μ A p (A.out x) x < f) x) := by
          unfold prob; apply expect_mono; intro x
          by_cases hg : good x
          · simp only [ind, hg, not_true_eq_false, if_false]
            exact sum_nonneg fun p _ => by split_ifs <;> norm_num
          · simp only [good, not_forall, not_le] at hg
            obtain ⟨p, hp⟩ := hg
            have h1 : ind (fun x => ¬ good x) x = 1 := by
              simp only [ind, good, not_forall, not_le]; rw [if_pos ⟨p, hp⟩]
            rw [h1]
            calc (1 : ℝ) = ind (fun x => frqO μ A p (A.out x) x < f) x := by simp [ind, hp]
              _ ≤ _ := single_le_sum (f := fun p => ind (fun x => frqO μ A p (A.out x) x < f) x)
                    (fun q _ => ind_nonneg _ _) (mem_univ p)
      _ = ∑ p : Fin k × Bool, prob μ F (fun x => frqO μ A p (A.out x) x < f) := by
          rw [expect_sum]; rfl
      _ ≤ ∑ _p : Fin k × Bool, Fintype.card α * f :=
          sum_le_sum fun p _ => prob_infrequent_le F (eReg t p) A.out hf
      _ = 2 * k * Fintype.card α * f := by
          simp [Fintype.card_prod]; ring
  rw [hA, hB]
  have hfk : 0 ≤ f ^ (2 * k) := pow_nonneg hf _
  calc f ^ (2 * k) * (prob μ F B.Fail - 2 * k * Fintype.card α * f)
      ≤ f ^ (2 * k) * prob μ F K := by
        apply mul_le_mul_of_nonneg_left _ hfk; linarith
    _ ≤ prob μ F A.Fail := stepA

end

end Podc.MinimalSymmetryBreaking
