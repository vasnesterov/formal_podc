import Papers.PODC2019.MinimalSymmetryBreaking.Speedup1

/-!
# Second speedup lemma (Lemma 8 for `Δ = 4`, Lemma 15 for `Δ = 2k`)

From an `r`-round edge algorithm `B` for weak edge `c`-colouring we build an `r`-round node
algorithm (`speedNode B f`): node `v` outputs, for each of its `2k` incident edges, the set of edge
colours that are frequent (probability `≥ f`) for that edge given the random values within
distance `r` of `v`. We prove (`speedup2_ineq`) that for every threshold `f ≥ 0`
`f^(Δ-1) · (p' − (Δ−1) c f) ≤ p`, where `p` and `p'` are the local failure probabilities of `B`
and of the node algorithm. This is the inequality `p ≥ (p' − 3cf) f³` of the paper's proof.

In the proof the paper's node `v'` is the origin and `v = dir (d₀, false)`, so that `v'` is the
neighbour of `v` in the positive direction of dimension `d₀`.
-/

namespace Podc.MinimalSymmetryBreaking

open Finset Function
open scoped Classical

noncomputable section

variable {k : ℕ} {Ω : Type} [Fintype Ω] [Inhabited Ω] (μ : FinDist Ω) {r : ℕ} {β : Type}
  [Fintype β]

/-- The value of the edge of the origin in slot `p`: the edge `{1, gᵈ}` for `p = (d, true)` and
the edge `{gᵈ⁻¹, 1}` for `p = (d, false)`. -/
def edgeOut (B : EdgeAlg k Ω r β) (p : Fin k × Bool) (z : Tree k → Ω) : β :=
  if p.2 then B.out p.1 z else B.out p.1 (shift (dir (p.1, false)) z)

/-- Probability that the edge in slot `p` of the origin gets colour `c`, given the values within
distance `r` of the origin. -/
def frqE (B : EdgeAlg k Ω r β) (p : Fin k × Bool) (c : β) (x : Tree k → Ω) : ℝ :=
  cond μ (Ball (r + 3)) (ball 1 r) (fun z => edgeOut B p z = c) x

/-- **The simulation of Lemma 8.** Each node outputs, for each of its `2k` edges, the set of
frequent colours of that edge. -/
def speedNode (B : EdgeAlg k Ω r β) (f : ℝ) : NodeAlg k Ω r (Fin k × Bool → Finset β) where
  out x p := univ.filter fun c => f ≤ frqE μ B p c x
  dep := by
    intro x x' h
    funext p
    exact Finset.filter_congr fun c _ => by simp only [frqE, cond_dependsOn _ _ _ h]

variable {μ}

lemma edgeOut_dep (B : EdgeAlg k Ω r β) (p : Fin k × Bool) :
    DependsOn (edgeOut B p) (ball 1 r ∪ ball (dir p) r) := by
  obtain ⟨d, b⟩ := p
  cases b with
  | true => exact B.dep d
  | false =>
    have := B.dep_shift d (dir (d, false))
    rw [dir_false_mul_dir_true, Set.union_comm] at this
    exact this

lemma edgeOut_shift_dir (B : EdgeAlg k Ω r β) (p : Fin k × Bool) (x : Tree k → Ω) :
    edgeOut B (p.1, !p.2) (shift (dir p) x) = edgeOut B p x := by
  obtain ⟨d, b⟩ := p
  cases b with
  | true =>
    simp only [edgeOut, Bool.not_true, Bool.false_eq_true, if_false, if_true]
    rw [shift_shift, show dir (d, true) * dir (d, false) = (1 : Tree k) by
      rw [dir_false_eq]; group, shift_one]
  | false => simp [edgeOut]

lemma ball_one_dir_subset (p : Fin k × Bool) : ball 1 r ∪ ball (dir p) r ⊆ ball (1 : Tree k) (r + 1) :=
  Set.union_subset (ball_mono (Nat.le_succ r)) (ball_dir_subset_one p r)

/-- The frequencies of a neighbour `u` are conditional probabilities given the ball around `u`. -/
lemma frqE_shift (B : EdgeAlg k Ω r β) (p : Fin k × Bool) (c : β) {u : Tree k}
    (hu : u.norm ≤ 1) (x : Tree k → Ω) :
    frqE μ B p c (shift u x) =
      cond μ (Ball (r + 3)) (ball u r) (fun z => edgeOut B p (shift u z) = c) x := by
  unfold frqE
  rw [cond_shift (D := ball 1 r ∪ ball (dir p) r) (dependsOn_eq (edgeOut_dep B p) c)
    ((ball_one_dir_subset p).trans (ball_mono (by omega)))
    (fun w hw => by
      have h1 := ball_one_dir_subset p hw
      simp only [mem_ball, inv_one, one_mul] at h1
      have := FreeGroup.norm_mul_le u w
      omega),
    preimage_inv_mul_ball, mul_one]

/-- **Second speedup inequality** (proof of Lemma 8 / Lemma 15): for every threshold `f ≥ 0`,
`f^(2k-1) · (p' − (2k−1)·c·f) ≤ p`, where `p` is the local failure probability of the edge
algorithm `B`, `p'` the one of the simulating node algorithm and `c = |β|`. -/
theorem speedup2_ineq (hk : 0 < k) (B : EdgeAlg k Ω r β) {f : ℝ} (hf : 0 ≤ f) :
    f ^ (2 * k - 1) * ((speedNode μ B f).failProb μ - (2 * k - 1) * Fintype.card β * f) ≤
      B.failProb μ := by
  set d₀ : Fin k := ⟨0, hk⟩
  set v : Tree k := dir (d₀, false)
  set F : Finset (Tree k) := Ball (r + 3)
  set S : Set (Tree k) := ball 1 (r + 1)
  set A := speedNode μ B f
  set J : Finset (Fin k × Bool) := univ.erase (d₀, true)
  have hv1 : v * dir (d₀, true) = 1 := dir_false_mul_dir_true d₀
  have hvn : v.norm ≤ 1 := by simp [v]
  -- the colours the edges of `v` (other than `{v, 1}`) are expected to take
  let target : Fin k × Bool → (Tree k → Ω) → β := fun p x =>
    if p = (d₀, false) then edgeOut B (d₀, false) x else edgeOut B (p.1, true) x
  let good : (Tree k → Ω) → Prop := fun x =>
    f ≤ frqE μ B (d₀, false) (edgeOut B (d₀, false) x) x ∧
    ∀ d, d ≠ d₀ → (f ≤ frqE μ B (d, true) (edgeOut B (d, true) x) x ∧
      f ≤ cond μ F (ball (dir (d, true)) r) (fun z => edgeOut B (d, true) z = edgeOut B (d, true) x) x)
  let G : (Tree k → Ω) → Prop := fun x => A.Fail x ∧ good x
  let K : (Tree k → Ω) → Prop := fun x => ∀ p ∈ J,
    f ≤ cond μ F (ball v r) (fun z => edgeOut B p (shift v z) = target p x) x
  -- the target colours depend on the values within distance `r + 1`
  have htarget : ∀ p, DependsOn (target p) S := by
    intro p x x' h
    have h1 : ∀ q, edgeOut B q x = edgeOut B q x' := fun q =>
      edgeOut_dep B q (fun w hw => h w (ball_one_dir_subset q hw))
    simp only [target, h1]
  have hgood : DependsOn good S := by
    intro x x' h
    have h1 : ∀ q, edgeOut B q x = edgeOut B q x' := fun q =>
      edgeOut_dep B q (fun w hw => h w (ball_one_dir_subset q hw))
    have h2 : ∀ q c, frqE μ B q c x = frqE μ B q c x' := fun q c =>
      cond_dependsOn _ _ _ (fun w hw => h w (ball_mono (Nat.le_succ r) hw))
    have h3 : ∀ d c, cond μ F (ball (dir (d, true)) r) (fun z => edgeOut B (d, true) z = c) x =
        cond μ F (ball (dir (d, true)) r) (fun z => edgeOut B (d, true) z = c) x' := fun d c =>
      cond_dependsOn _ _ _ (fun w hw => h w (ball_dir_subset_one _ r hw))
    simp only [good, h1, h2, h3]
  have hG : DependsOn (ind G) S := by
    apply ind_dependsOn
    intro x x' h
    simp only [G, A.fail_dependsOn h, hgood h]
  -- Claim: failure of the node algorithm in a good neighbourhood gives `K`
  have claim : ∀ x, G x → K x := by
    rintro x ⟨hF, hg⟩ p hp
    have hmem : ∀ q c, c ∈ A.out x q ↔ f ≤ frqE μ B q c x := fun q c => by
      simp [A, speedNode]
    have hv : A.out (shift v x) = A.out x := hF (d₀, false)
    -- it suffices that `target p x` is frequent for slot `p` at the origin
    suffices hs : f ≤ frqE μ B p (target p x) x by
      have : target p x ∈ A.out (shift v x) p := by rw [hv]; exact (hmem p _).2 hs
      have h2 : f ≤ frqE μ B p (target p x) (shift v x) := by simpa [A, speedNode] using this
      rwa [frqE_shift B p _ hvn] at h2
    obtain ⟨d, b⟩ := p
    by_cases hd : d = d₀
    · subst hd
      cases b with
      | true => exact absurd rfl (Finset.ne_of_mem_erase hp)
      | false => simpa [target] using hg.1
    · have hne : (d, b) ≠ (d₀, false) := by simp [hd]
      cases b with
      | true => simpa [target, hne] using (hg.2 d hd).1
      | false =>
        simp only [target, hne, if_false]
        have hgd : A.out (shift (dir (d, true)) x) = A.out x := hF (d, true)
        have h3 := (hg.2 d hd).2
        have h4 : f ≤ frqE μ B (d, false) (edgeOut B (d, true) x) (shift (dir (d, true)) x) := by
          rw [frqE_shift B _ _ (by simp)]
          have : (fun z => edgeOut B (d, false) (shift (dir (d, true)) z) = edgeOut B (d, true) x) =
              (fun z => edgeOut B (d, true) z = edgeOut B (d, true) x) := by
            funext z; rw [show (d, false) = ((d, true).1, !(d, true).2) from rfl,
              edgeOut_shift_dir]
          rw [this]; exact h3
        have : edgeOut B (d, true) x ∈ A.out (shift (dir (d, true)) x) (d, false) := by
          simpa [A, speedNode] using h4
        rw [hgd] at this
        exact (hmem _ _).1 this
  -- failure of `B` at `v`
  have hfailv : ∀ x, (∀ p ∈ J, edgeOut B p (shift v x) = target p x) → B.Fail (shift v x) := by
    intro x h d
    by_cases hd : d = d₀
    · subst hd
      have h1 := h (d₀, false) (by simp [J])
      simp only [target, if_true] at h1
      have : B.out d₀ (shift (dir (d₀, false)) (shift v x)) = edgeOut B (d₀, false) (shift v x) := rfl
      rw [this, h1]
      rfl
    · have h1 := h (d, true) (by simp [J, hd])
      have h2 := h (d, false) (by simp [J])
      simp only [target, show (d, true) ≠ (d₀, false) by simp, show (d, false) ≠ (d₀, false) by simp [hd],
        if_false] at h1 h2
      have e1 : B.out d (shift v x) = edgeOut B (d, true) (shift v x) := rfl
      have e2 : B.out d (shift (dir (d, false)) (shift v x)) = edgeOut B (d, false) (shift v x) := rfl
      rw [e1, e2, h1, h2]
  -- support changes
  have hBp : B.failProb μ = prob μ F (fun x => B.Fail (shift v x)) := by
    unfold EdgeAlg.failProb
    refine (prob_shift B.fail_dependsOn subset_rfl (fun w hw => ?_)).symm
    have := FreeGroup.norm_mul_le v w
    simp only [mem_ball, inv_one, one_mul] at hw
    omega
  have hAp : A.failProb μ = prob μ F A.Fail := by
    unfold NodeAlg.failProb prob
    refine (expect_eq_of_subset (Ball_mono (by omega)) ?_).symm
    rw [coe_Ball]; exact ind_dependsOn A.fail_dependsOn
  -- Step A: `f^(2k-1) Pr[G] ≤ p`
  have hJcard : J.card = 2 * k - 1 := by
    simp [J, Finset.card_erase_of_mem, Fintype.card_prod]; omega
  have hvS : ball v r ⊆ S := by
    have := ball_dir_subset (1 : Tree k) (d₀, false) r; rwa [one_mul] at this
  have stepA : f ^ (2 * k - 1) * prob μ F G ≤ prob μ F (fun x => B.Fail (shift v x)) := by
    have hprod : ∀ x, condE μ F S
        (fun z => ∏ p ∈ J, ind (fun z => edgeOut B p (shift v z) = target p z) z) x =
        ∏ p ∈ J, cond μ F (ball v r) (fun z => edgeOut B p (shift v z) = target p x) x := by
      intro x
      rw [condE_congr (h' := fun z => ∏ p ∈ J, ind (fun z => edgeOut B p (shift v z) = target p x) z)]
      · rw [condE_prod (D := fun p => ball (v * dir p) r \ ball v r) J]
        · refine prod_congr rfl fun p hp => ?_
          unfold cond
          refine condE_eq_of_dependsOn (D := ball (v * dir p) r \ ball v r) ?_ hvS ?_ x
          · have := ind_dependsOn (dependsOn_eq (dependsOn_shift (edgeOut_dep B p) v) (target p x))
            refine this.mono ?_
            rw [Set.preimage_union, preimage_inv_mul_ball, preimage_inv_mul_ball, mul_one]
            intro w hw
            by_cases h : w ∈ ball v r
            · left; exact h
            · right; rcases hw with hw | hw; exacts [absurd hw h, ⟨hw, h⟩]
          · have := disjoint_diff_ball v (Finset.ne_of_mem_erase hp) r
            rwa [hv1] at this
        · intro p _
          have := ind_dependsOn (dependsOn_eq (dependsOn_shift (edgeOut_dep B p) v) (target p x))
          refine this.mono ?_
          rw [Set.preimage_union, preimage_inv_mul_ball, preimage_inv_mul_ball, mul_one]
          intro w hw
          by_cases h : w ∈ ball v r
          · left; exact hvS h
          · right; rcases hw with hw | hw; exacts [absurd hw h, ⟨hw, h⟩]
        · intro p _ q _ hpq
          exact disjoint_diff v hpq r
      · intro z
        have : ∀ p, target p (S.piecewise x z) = target p x := fun p =>
          htarget p (fun w hw => by simp only [Set.piecewise, if_pos (show w ∈ S from hw)])
        simp only [ind, this]
    calc f ^ (2 * k - 1) * prob μ F G = expect μ F (fun x => ind G x * f ^ (2 * k - 1)) := by
          unfold prob; rw [expect_mul_const, mul_comm]
      _ ≤ expect μ F (fun x => ind G x *
            ∏ p ∈ J, cond μ F (ball v r) (fun z => edgeOut B p (shift v z) = target p x) x) := by
          apply expect_mono; intro x
          by_cases hx : G x
          · simp only [ind, hx, if_true, one_mul]
            have hK := claim x hx
            calc f ^ (2 * k - 1) = ∏ _p ∈ J, f := by rw [prod_const, hJcard]
              _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hf) (fun p hp => hK p hp)
          · simp [ind, hx]
      _ = expect μ F (fun x => ind G x *
            ∏ p ∈ J, ind (fun z => edgeOut B p (shift v z) = target p z) x) := by
          simp only [← hprod]
          exact expect_mul_condE hG _
      _ ≤ prob μ F (fun x => B.Fail (shift v x)) := by
          unfold prob; apply expect_mono; intro x
          have hP : 0 ≤ ∏ p ∈ J, ind (fun z => edgeOut B p (shift v z) = target p z) x :=
            prod_nonneg fun p _ => ind_nonneg _ _
          by_cases hall : ∀ p ∈ J, edgeOut B p (shift v x) = target p x
          · have := hfailv x hall
            calc ind G x * ∏ p ∈ J, ind (fun z => edgeOut B p (shift v z) = target p z) x
                ≤ 1 * 1 := mul_le_mul (ind_le_one _ _)
                  (Finset.prod_le_one₀ (fun p _ => ind_nonneg _ _) (fun p _ => ind_le_one _ _)) hP
                  zero_le_one
              _ = ind (fun x => B.Fail (shift v x)) x := by simp [ind, this]
          · push_neg at hall
            obtain ⟨p, hp, hne⟩ := hall
            rw [prod_eq_zero hp (by simp [ind, hne]), mul_zero]
            exact ind_nonneg _ _
  -- Step B: `p' ≤ Pr[G] + Pr[¬ good]`
  have stepB : prob μ F A.Fail ≤ prob μ F G + prob μ F (fun x => ¬ good x) := by
    unfold prob
    rw [← expect_add]
    apply expect_mono; intro x
    by_cases hg : good x
    · by_cases hF : A.Fail x
      · have hGx : G x := ⟨hF, hg⟩
        simp [ind, hF, hGx, hg]
      · simp only [ind, hF, if_false]
        split_ifs <;> norm_num
    · simp only [ind, hg, not_false_eq_true, if_true]
      split_ifs <;> norm_num
  -- Step C: `Pr[¬ good] ≤ (2k - 1) c f`
  have stepC : prob μ F (fun x => ¬ good x) ≤ (2 * k - 1) * Fintype.card β * f := by
    let b1 : (Tree k → Ω) → Prop := fun x => frqE μ B (d₀, false) (edgeOut B (d₀, false) x) x < f
    let b2 : Fin k → (Tree k → Ω) → Prop := fun d x =>
      frqE μ B (d, true) (edgeOut B (d, true) x) x < f
    let b3 : Fin k → (Tree k → Ω) → Prop := fun d x =>
      cond μ F (ball (dir (d, true)) r) (fun z => edgeOut B (d, true) z = edgeOut B (d, true) x) x < f
    have hpt : ∀ x, ind (fun x => ¬ good x) x ≤
        ind b1 x + ∑ d ∈ univ.erase d₀, (ind (b2 d) x + ind (b3 d) x) := by
      intro x
      have hnn : 0 ≤ ∑ d ∈ univ.erase d₀, (ind (b2 d) x + ind (b3 d) x) :=
        sum_nonneg fun d _ => add_nonneg (ind_nonneg _ _) (ind_nonneg _ _)
      by_cases hg : good x
      · simp only [ind, hg, not_true_eq_false, if_false]
        exact add_nonneg (by split_ifs <;> norm_num) hnn
      · have h1 : ind (fun x => ¬ good x) x = 1 := by simp [ind, hg]
        rw [h1]
        simp only [good, not_and_or, not_forall, not_le] at hg
        rcases hg with hg | ⟨d, hd, hg⟩
        · have : ind b1 x = 1 := by simp [ind, b1, hg]
          linarith
        · have hdmem : d ∈ univ.erase d₀ := by simp [hd]
          have hle : ind (b2 d) x + ind (b3 d) x ≤
              ∑ d ∈ univ.erase d₀, (ind (b2 d) x + ind (b3 d) x) :=
            single_le_sum (f := fun d => ind (b2 d) x + ind (b3 d) x)
              (fun _ _ => add_nonneg (ind_nonneg _ _) (ind_nonneg _ _)) hdmem
          have h2 : 1 ≤ ind (b2 d) x + ind (b3 d) x := by
            rcases hg with hg | hg
            · have : ind (b2 d) x = 1 := by simp [ind, b2, hg]
              rw [this]; linarith [ind_nonneg (b3 d) x]
            · have : ind (b3 d) x = 1 := by simp [ind, b3, hg]
              rw [this]; linarith [ind_nonneg (b2 d) x]
          linarith [ind_nonneg b1 x]
    have hc1 : prob μ F b1 ≤ Fintype.card β * f :=
      prob_infrequent_le F (ball 1 r) (edgeOut B (d₀, false)) hf
    have hc2 : ∀ d, prob μ F (b2 d) ≤ Fintype.card β * f := fun d =>
      prob_infrequent_le F (ball 1 r) (edgeOut B (d, true)) hf
    have hc3 : ∀ d, prob μ F (b3 d) ≤ Fintype.card β * f := fun d =>
      prob_infrequent_le F (ball (dir (d, true)) r) (edgeOut B (d, true)) hf
    have hcard : ((univ.erase d₀).card : ℝ) = k - 1 := by
      rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, Nat.cast_sub hk]
      simp
    calc prob μ F (fun x => ¬ good x)
        ≤ expect μ F (fun x => ind b1 x + ∑ d ∈ univ.erase d₀, (ind (b2 d) x + ind (b3 d) x)) :=
          expect_mono hpt
      _ = prob μ F b1 + ∑ d ∈ univ.erase d₀, (prob μ F (b2 d) + prob μ F (b3 d)) := by
          rw [expect_add, expect_sum]
          simp only [expect_add]; rfl
      _ ≤ Fintype.card β * f + ∑ _d ∈ univ.erase d₀, (Fintype.card β * f + Fintype.card β * f) := by
          gcongr with d hd
          · exact hc2 d
          · exact hc3 d
      _ = (2 * k - 1) * Fintype.card β * f := by
          rw [sum_const, nsmul_eq_mul, hcard]; ring
  rw [hAp, hBp]
  have hfk : 0 ≤ f ^ (2 * k - 1) := pow_nonneg hf _
  calc f ^ (2 * k - 1) * (prob μ F A.Fail - (2 * k - 1) * Fintype.card β * f)
      ≤ f ^ (2 * k - 1) * prob μ F G := by
        apply mul_le_mul_of_nonneg_left _ hfk; linarith
    _ ≤ _ := stepA

end

end Podc.MinimalSymmetryBreaking
