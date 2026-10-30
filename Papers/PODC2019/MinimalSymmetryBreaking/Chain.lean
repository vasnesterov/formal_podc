import Papers.PODC2019.MinimalSymmetryBreaking.Speedup2

/-!
# Iterating the speedup lemmas (Claims 11/16 and the first step of Claim 12)

* `failProb_zero_round`: a `0`-round weak `c`-colouring algorithm fails locally with probability
  at least `1 / c^Δ` (first step of the proof of Claim 12).
* `nodeLB_succ_of_edgeLB`, `edgeLB_of_nodeLB`: the lower-bound forms of the two speedup lemmas.
* `nodeLB_lb`: every `t`-round weak `c`-colouring algorithm fails with probability at least
  `lb t c`, defined by the recursion of Claim 11.
* `lb_ge`: Claim 16, `lb t c ≥ (p₀ / ((Δ+1) c₀))^((Δ+1)^(2t+1))` with `p₀ = 1/c₀^Δ`, where `c₀` is
  the palette of the `0`-round algorithm at the end of the chain.
-/

namespace Podc.MinimalSymmetryBreaking

open Finset Function
open scoped Classical

noncomputable section

variable {k : ℕ} {Ω : Type} [Fintype Ω] [Inhabited Ω] {μ : FinDist Ω}

/-! ### Zero rounds -/

lemma disjoint_ball_dir_zero (p : Fin k × Bool) :
    Disjoint (ball (dir p) 0) (ball (1 : Tree k) 0) := by
  rw [Set.disjoint_left]
  intro w h1 h2
  simp only [mem_ball, inv_one, one_mul, nonpos_iff_eq_zero, FreeGroup.norm_eq_zero,
    inv_mul_eq_one] at h1 h2
  have := norm_dir p
  rw [h1, h2] at this
  simp at this

lemma disjoint_ball_dir_dir_zero {p q : Fin k × Bool} (hpq : p ≠ q) :
    Disjoint (ball (dir p) 0) (ball (dir q) 0) := by
  rw [Set.disjoint_left]
  intro w h1 h2
  simp only [mem_ball, nonpos_iff_eq_zero, FreeGroup.norm_eq_zero, inv_mul_eq_one] at h1 h2
  exact hpq (dir_injective (h1.trans h2.symm))

/-- First step of the proof of Claim 12: a `0`-round algorithm (each node outputs a function of its
own random value) fails locally with probability `∑ᵢ qᵢ^(Δ+1) ≥ 1/c^Δ`. -/
theorem failProb_zero_round {α : Type} [Fintype α] (A : NodeAlg k Ω 0 α) :
    1 / (Fintype.card α : ℝ) ^ (2 * k) ≤ A.failProb μ := by
  set F : Finset (Tree k) := Ball 1
  set S : Set (Tree k) := ball 1 0
  set q : α → ℝ := fun c => prob μ (Ball 0) (fun z => A.out z = c)
  have hq : ∀ p c x, cond μ F S (fun z => A.out (shift (dir p) z) = c) x = q c := by
    intro p c x
    unfold cond
    rw [condE_eq_of_dependsOn (T := ∅) (D := ball (dir p) 0) (by
        rw [Set.empty_union]
        have := A.dep_shift (dir p)
        exact ind_dependsOn (dependsOn_eq this c)) (Set.empty_subset _)
      (disjoint_ball_dir_zero p) x]
    unfold condE
    simp only [Set.piecewise_empty]
    exact prob_shift (dependsOn_eq A.dep c) subset_rfl (fun w hw => by
      simp only [mem_ball, inv_one, one_mul] at hw
      have := norm_dir_mul_le p w; omega)
  have hqA : ∀ c, prob μ F (fun z => A.out z = c) = q c := by
    intro c
    unfold prob
    apply expect_eq_of_subset (Ball_mono (by omega))
    rw [coe_Ball]; exact ind_dependsOn (dependsOn_eq A.dep c)
  have hsum : ∑ c, q c = 1 := by
    rw [← (fun c => hqA c : ∀ c, prob μ F _ = q c) |> fun h => Finset.sum_congr rfl fun c _ => h c]
    unfold prob
    rw [← expect_sum]
    have : ∀ x : Tree k → Ω, ∑ c : α, ind (fun z => A.out z = c) x = 1 := by
      intro x
      rw [Finset.sum_eq_single (A.out x)]
      · simp [ind]
      · intro c _ hc; simp [ind, Ne.symm hc]
      · simp
    simp only [this, expect_const]
  have hfail : A.failProb μ = ∑ c, q c * q c ^ (2 * k) := by
    have h1 : A.failProb μ = prob μ F A.Fail := rfl
    rw [h1]
    unfold prob
    rw [← expect_condE F S]
    have h2 : ∀ x, condE μ F S (ind A.Fail) x = q (A.out x) ^ (2 * k) := by
      intro x
      rw [condE_congr (h' := fun z => ∏ p, ind (fun z => A.out (shift (dir p) z) = A.out x) z)]
      · rw [condE_prod (D := fun p => ball (dir p) 0) univ]
        · simp only [show ∀ p, condE μ F S (ind fun z => A.out (shift (dir p) z) = A.out x) x =
            q (A.out x) from fun p => hq p _ x]
          simp [Finset.prod_const, Fintype.card_prod, mul_comm]
        · intro p _
          exact (ind_dependsOn (dependsOn_eq (A.dep_shift (dir p)) _)).mono Set.subset_union_right
        · intro p _ q' _ hpq
          exact disjoint_ball_dir_dir_zero hpq
      · intro z
        have : A.out (S.piecewise x z) = A.out x :=
          A.dep (fun w hw => by simp only [Set.piecewise, if_pos (show w ∈ S from hw)])
        change ind (fun y => ∀ p, A.out (shift (dir p) y) = A.out y) _ = _
        rw [ind_forall]
        simp only [ind, this]
    rw [show condE μ F S (ind A.Fail) = fun x => q (A.out x) ^ (2 * k) from funext h2]
    have h3 : ∀ x : Tree k → Ω, q (A.out x) ^ (2 * k) =
        ∑ c, ind (fun z => A.out z = c) x * q c ^ (2 * k) := by
      intro x
      rw [Finset.sum_eq_single (A.out x)]
      · simp [ind]
      · intro c _ hc; simp [ind, Ne.symm hc]
      · simp
    simp only [h3]
    rw [expect_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [expect_mul_const]
    change prob μ F _ * _ = _
    rw [hqA]
  rw [hfail]
  have hq0 : ∀ c ∈ (univ : Finset α), 0 ≤ q c := fun c _ => prob_nonneg _ _
  have := pow_sum_div_card_le_sum_pow hq0 (2 * k)
  rw [hsum, one_pow, card_univ] at this
  calc 1 / (Fintype.card α : ℝ) ^ (2 * k) ≤ ∑ c, q c ^ (2 * k + 1) := this
    _ = ∑ c, q c * q c ^ (2 * k) := Finset.sum_congr rfl fun c _ => by ring

/-! ### Lower-bound forms of the speedup lemmas -/

variable (μ) in
/-- Every `t`-round node algorithm with at most `c` colours fails locally with probability at
least `L`. -/
def NodeLB (k t c : ℕ) (L : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α], Fintype.card α ≤ c → ∀ A : NodeAlg k Ω t α, L ≤ A.failProb μ

variable (μ) in
/-- Every `t`-round edge algorithm with at most `c` colours fails locally with probability at
least `L`. -/
def EdgeLB (k t c : ℕ) (L : ℝ) : Prop :=
  ∀ (β : Type) [Fintype β], Fintype.card β ≤ c → ∀ B : EdgeAlg k Ω t β, L ≤ B.failProb μ

/-- The bound produced by the first speedup lemma. -/
def phi1 (k : ℕ) (L : ℝ) (c : ℕ) : ℝ := (L / (2 * k + 1)) ^ (2 * k + 1) / (c : ℝ) ^ (2 * k)

/-- The bound produced by the second speedup lemma. -/
def phi2 (k : ℕ) (L : ℝ) (c : ℕ) : ℝ := (L / (2 * k)) ^ (2 * k) / (c : ℝ) ^ (2 * k - 1)

/-- **Lemma 7 / Lemma 14, lower-bound form.** If every `t`-round edge algorithm with `≤ 2^(2c)`
colours fails with probability `≥ L`, then every `(t+1)`-round node algorithm with `≤ c` colours
fails with probability `≥ (L/(Δ+1))^(Δ+1) / c^Δ`. -/
theorem nodeLB_succ_of_edgeLB {t c : ℕ} {L : ℝ} (hc : 1 ≤ c) (h : EdgeLB μ k t (2 ^ (2 * c)) L) :
    NodeLB μ k (t + 1) c (phi1 k L c) := by
  intro α _ hα A
  unfold phi1
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  rcases le_or_gt L 0 with hL | hL
  · have : (L / (2 * k + 1)) ^ (2 * k + 1) / (c : ℝ) ^ (2 * k) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      exact Odd.pow_nonpos ⟨k, rfl⟩ (div_nonpos_of_nonpos_of_nonneg hL (by positivity))
    exact this.trans (prob_nonneg _ _)
  · set f : ℝ := L / ((2 * k + 1) * c)
    have hf : 0 ≤ f := by positivity
    have hcard : Fintype.card (Finset α × Finset α) ≤ 2 ^ (2 * c) := by
      simp only [Fintype.card_prod, Fintype.card_finset, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hB := h _ hcard (speedEdge μ A f)
    have key := speedup1_ineq (μ := μ) A hf
    have hα' : (Fintype.card α : ℝ) ≤ c := by exact_mod_cast hα
    have h2 : 2 * (k : ℝ) * Fintype.card α * f ≤ 2 * k * c * f := by gcongr
    have hk0 : (2 * k + 1 : ℝ) ≠ 0 := by positivity
    have hc0 : (c : ℝ) ≠ 0 := hcpos.ne'
    have e1 : L - 2 * k * c * f = L / (2 * k + 1) := by simp only [f]; field_simp; ring
    have e2 : f = L / (2 * k + 1) / c := by simp only [f]; rw [div_div]
    calc (L / (2 * k + 1)) ^ (2 * k + 1) / (c : ℝ) ^ (2 * k) = f ^ (2 * k) * (L - 2 * k * c * f) := by
          rw [e1, e2]; ring
      _ ≤ f ^ (2 * k) * ((speedEdge μ A f).failProb μ - 2 * k * Fintype.card α * f) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hf _); linarith
      _ ≤ A.failProb μ := key

/-- **Lemma 8 / Lemma 15, lower-bound form.** If every `r`-round node algorithm with
`≤ 2^(Δ c)` colours fails with probability `≥ L`, then every `r`-round edge algorithm with `≤ c`
colours fails with probability `≥ (L/Δ)^Δ / c^(Δ-1)`. -/
theorem edgeLB_of_nodeLB (hk : 0 < k) {r c : ℕ} {L : ℝ} (hc : 1 ≤ c) (hL0 : 0 ≤ L)
    (h : NodeLB μ k r (2 ^ (2 * k * c)) L) : EdgeLB μ k r c (phi2 k L c) := by
  intro β _ hβ B
  unfold phi2
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 1 := ⟨2 * k - 1, by omega⟩
  have hm' : 2 * k - 1 = m := by omega
  rw [hm', hm]
  have hkR : (2 * k : ℝ) = m + 1 := by exact_mod_cast hm
  rcases hL0.eq_or_lt with hL | hL
  · subst hL
    have : ((0 : ℝ) / (2 * k)) ^ (m + 1) / (c : ℝ) ^ m = 0 := by simp
    rw [this]; exact prob_nonneg _ _
  · set f : ℝ := L / (2 * k * c)
    have hf : 0 ≤ f := by positivity
    have hcard : Fintype.card (Fin k × Bool → Finset β) ≤ 2 ^ (2 * k * c) := by
      simp only [Fintype.card_fun, Fintype.card_finset, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_bool, ← pow_mul]
      apply Nat.pow_le_pow_right (by norm_num)
      calc Fintype.card β * (k * 2) ≤ c * (k * 2) := Nat.mul_le_mul_right _ hβ
        _ = 2 * k * c := by ring
    have hA := h _ hcard (speedNode μ B f)
    have key := speedup2_ineq (μ := μ) hk B hf
    rw [hm'] at key
    have hβ' : (Fintype.card β : ℝ) ≤ c := by exact_mod_cast hβ
    have h2 : (2 * k - 1 : ℝ) * Fintype.card β * f ≤ (2 * k - 1) * c * f := by
      have : (0 : ℝ) ≤ 2 * k - 1 := by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      gcongr
    have hk0 : (2 * k : ℝ) ≠ 0 := by positivity
    have hc0 : (c : ℝ) ≠ 0 := hcpos.ne'
    have e1 : L - (2 * k - 1) * c * f = L / (2 * k) := by simp only [f]; field_simp; ring
    have e2 : f = L / (2 * k) / c := by simp only [f]; rw [div_div]
    calc (L / (2 * k)) ^ (m + 1) / (c : ℝ) ^ m = f ^ m * (L - (2 * k - 1) * c * f) := by
          rw [e1, e2]; ring
      _ ≤ f ^ m * ((speedNode μ B f).failProb μ - (2 * k - 1) * Fintype.card β * f) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hf _); linarith
      _ ≤ B.failProb μ := key

/-! ### The recursion of Claim 11 -/

/-- Palette growth of one full round of speedup: a node `c`-colouring becomes an edge
`2^(2c)`-colouring and then a node `2^(Δ·2^(2c))`-colouring. -/
def nodePal (k c : ℕ) : ℕ := 2 ^ (2 * k * 2 ^ (2 * c))

/-- The recursive lower bound of Claim 11 on the local failure probability of `t`-round node
algorithms with `c` colours. -/
def lb (k : ℕ) : ℕ → ℕ → ℝ
  | 0, c => 1 / (c : ℝ) ^ (2 * k)
  | t + 1, c => phi1 k (phi2 k (lb k t (nodePal k c)) (2 ^ (2 * c))) c

lemma one_le_two_pow (n : ℕ) : 1 ≤ 2 ^ n := Nat.one_le_two_pow

lemma phi1_nonneg {L : ℝ} (hL : 0 ≤ L) (c : ℕ) : 0 ≤ phi1 k L c := by unfold phi1; positivity

lemma phi2_nonneg {L : ℝ} (hL : 0 ≤ L) (c : ℕ) : 0 ≤ phi2 k L c := by unfold phi2; positivity

lemma lb_nonneg : ∀ t c, 0 ≤ lb k t c
  | 0, c => by simp only [lb]; positivity
  | t + 1, _ => phi1_nonneg (phi2_nonneg (lb_nonneg t _) _) _

/-- Every `t`-round node algorithm with at most `c` colours fails locally with probability at
least `lb k t c` (Lemmas 7 and 8 applied `t` times, then the `0`-round bound). -/
theorem nodeLB_lb (hk : 0 < k) : ∀ t c, 1 ≤ c → NodeLB μ k t c (lb k t c) := by
  intro t
  induction t with
  | zero =>
    intro c hc α _ hα A
    have hne : Nonempty α := ⟨A.out (fun _ => default)⟩
    have h1 : 1 ≤ Fintype.card α := Fintype.card_pos
    refine le_trans ?_ (failProb_zero_round A)
    simp only [lb]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hα) _
  | succ t ih =>
    intro c hc
    exact nodeLB_succ_of_edgeLB hc
      (edgeLB_of_nodeLB hk (one_le_two_pow _) (lb_nonneg _ _) (ih (nodePal k c) (one_le_two_pow _)))

/-! ### Claim 16: closed form -/

/-- The generic step bound `ψ(L) = (L / ((Δ+1) C))^(Δ+1)`. -/
def psi (k C : ℕ) (L : ℝ) : ℝ := (L / ((2 * k + 1) * C)) ^ (2 * k + 1)

lemma psi_nonneg {C : ℕ} {L : ℝ} (hL : 0 ≤ L) : 0 ≤ psi k C L := by
  unfold psi; positivity

lemma psi_le_one {C : ℕ} (hC : 1 ≤ C) {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1) : psi k C L ≤ 1 := by
  unfold psi
  apply pow_le_one₀ (by positivity)
  rw [div_le_one (by positivity)]
  have : (1 : ℝ) ≤ C := by exact_mod_cast hC
  nlinarith

lemma psi_le_phi1 {C c : ℕ} (hc : 1 ≤ c) (hcC : c ≤ C) {L : ℝ} (hL0 : 0 ≤ L) :
    psi k C L ≤ phi1 k L c := by
  unfold psi phi1
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcC' : (c : ℝ) ≤ C := by exact_mod_cast hcC
  rw [div_pow, div_pow, mul_pow, div_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc (c : ℝ) ^ (2 * k) ≤ (C : ℝ) ^ (2 * k) := pow_le_pow_left₀ (by positivity) hcC' _
    _ ≤ (C : ℝ) ^ (2 * k + 1) := pow_le_pow_right₀ (by linarith) (by omega)

lemma psi_le_phi2 (hk : 0 < k) {C c : ℕ} (hc : 1 ≤ c) (hcC : c ≤ C) {L : ℝ} (hL0 : 0 ≤ L)
    (hL1 : L ≤ 1) : psi k C L ≤ phi2 k L c := by
  unfold psi phi2
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcC' : (c : ℝ) ≤ C := by exact_mod_cast hcC
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : ((2 * k + 1 : ℝ) * C) ^ (2 * k + 1) = (2 * k + 1 : ℝ) ^ (2 * k + 1) * (C : ℝ) ^ (2 * k + 1) :=
    mul_pow _ _ _
  rw [div_pow, div_pow, div_div, hm]
  apply div_le_div₀ (by positivity) (pow_le_pow_of_le_one hL0 hL1 (by omega)) (by positivity)
  apply mul_le_mul
  · calc (2 * k : ℝ) ^ (2 * k) ≤ (2 * k + 1 : ℝ) ^ (2 * k) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ (2 * k + 1 : ℝ) ^ (2 * k + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  · calc (c : ℝ) ^ (2 * k - 1) ≤ (C : ℝ) ^ (2 * k - 1) :=
          pow_le_pow_left₀ (by positivity) hcC' _
      _ ≤ (C : ℝ) ^ (2 * k + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  · positivity
  · positivity

lemma phi1_mono {L L' : ℝ} (hL : 0 ≤ L) (h : L ≤ L') (c : ℕ) : phi1 k L c ≤ phi1 k L' c := by
  unfold phi1
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by gcongr) _

lemma phi2_mono {L L' : ℝ} (hL : 0 ≤ L) (h : L ≤ L') (c : ℕ) : phi2 k L c ≤ phi2 k L' c := by
  unfold phi2
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by gcongr) _

lemma le_nodePal (c : ℕ) : 2 ^ (2 * c) ≤ nodePal k c ∨ k = 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · right; exact hk
  · left
    unfold nodePal
    apply Nat.pow_le_pow_right (by norm_num)
    have : 2 * c ≤ 2 ^ (2 * c) := Nat.lt_two_pow_self.le
    nlinarith

lemma le_iterate_nodePal (hk : 0 < k) (t c : ℕ) : c ≤ (nodePal k)^[t] c := by
  induction t generalizing c with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    refine le_trans ?_ (ih _)
    rcases le_nodePal (k := k) c with h | h
    · exact le_trans (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))) h
    · omega

/-- `lb` dominates `2t` iterations of `ψ` started at `1/C^Δ`. -/
lemma psi_iterate_le_lb (hk : 0 < k) :
    ∀ t c C, 1 ≤ c → (nodePal k)^[t] c ≤ C → (psi k C)^[2 * t] (1 / (C : ℝ) ^ (2 * k)) ≤ lb k t c := by
  intro t
  induction t with
  | zero =>
    intro c C hc hC
    simp only [Function.iterate_zero, id, Nat.mul_zero, lb]
    have hC' : (c : ℝ) ≤ C := by exact_mod_cast hC
    apply one_div_le_one_div_of_le (pow_pos (by exact_mod_cast hc) _)
    exact pow_le_pow_left₀ (by positivity) hC' _
  | succ t ih =>
    intro c C hc hC
    have hC1 : 1 ≤ C := le_trans hc (le_trans (le_iterate_nodePal hk _ _) hC)
    have hpal : (nodePal k)^[t] (nodePal k c) ≤ C := by
      rwa [← Function.iterate_succ_apply]
    have hc2 : 2 ^ (2 * c) ≤ C := by
      rcases le_nodePal (k := k) c with h | h
      · exact le_trans h (le_trans (le_iterate_nodePal hk _ _) hpal)
      · omega
    have hcC : c ≤ C := le_trans (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))) hc2
    set X := (psi k C)^[2 * t] (1 / (C : ℝ) ^ (2 * k))
    have hX0 : ∀ m, 0 ≤ (psi k C)^[m] (1 / (C : ℝ) ^ (2 * k)) := by
      intro m
      induction m with
      | zero => simp only [Function.iterate_zero, id]; positivity
      | succ m ihm => rw [Function.iterate_succ_apply']; exact psi_nonneg ihm
    have hX1 : ∀ m, (psi k C)^[m] (1 / (C : ℝ) ^ (2 * k)) ≤ 1 := by
      intro m
      induction m with
      | zero =>
        simp only [Function.iterate_zero, id]
        apply div_le_one_of_le₀ _ (by positivity)
        exact one_le_pow₀ (by exact_mod_cast hC1)
      | succ m ihm => rw [Function.iterate_succ_apply']; exact psi_le_one hC1 (hX0 m) ihm
    have hIH := ih (nodePal k c) C (one_le_two_pow _) hpal
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    simp only [lb]
    calc psi k C (psi k C X) ≤ phi1 k (psi k C X) c :=
          psi_le_phi1 hc hcC (psi_nonneg (hX0 _))
      _ ≤ phi1 k (phi2 k X (2 ^ (2 * c))) c :=
          phi1_mono (psi_nonneg (hX0 _))
            (psi_le_phi2 hk (one_le_two_pow _) hc2 (hX0 _) (hX1 _)) c
      _ ≤ phi1 k (phi2 k (lb k t (nodePal k c)) (2 ^ (2 * c))) c := by
          apply phi1_mono _ _ c
          · unfold phi2; have := hX0 (2 * t); positivity
          · exact phi2_mono (hX0 _) hIH _

/-- Exponent bookkeeping for iterating `ψ`. -/
def psiExp (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => (2 * k + 1) * (psiExp k m + 1)

lemma psiExp_spec (m : ℕ) : 2 * k * psiExp k m + (2 * k + 1) = (2 * k + 1) ^ (m + 1) := by
  induction m with
  | zero => simp [psiExp]
  | succ m ih => simp only [psiExp]; rw [pow_succ, ← ih]; ring

lemma psiExp_le (m : ℕ) (hk : 0 < k) : psiExp k m ≤ (2 * k + 1) ^ (m + 1) := by
  have := psiExp_spec (k := k) m
  nlinarith

lemma psi_iterate_eq {C : ℕ} (L : ℝ) (m : ℕ) :
    (psi k C)^[m] L = L ^ ((2 * k + 1) ^ m) / (((2 * k + 1) * C : ℝ)) ^ psiExp k m := by
  induction m with
  | zero => simp [psiExp]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold psi
    simp only [psiExp]
    rw [div_div, div_pow, ← pow_mul, mul_pow, ← pow_mul, ← pow_succ, pow_succ (2 * k + 1) m]
    ring_nf

lemma psi_iterate_ge (hk : 0 < k) {C : ℕ} (hC : 1 ≤ C) {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (m : ℕ) : (L / ((2 * k + 1) * C)) ^ ((2 * k + 1) ^ (m + 1)) ≤ (psi k C)^[m] L := by
  rw [psi_iterate_eq, div_pow]
  have hM : (1 : ℝ) ≤ (2 * k + 1) * C := by
    have : (1 : ℝ) ≤ C := by exact_mod_cast hC
    nlinarith
  apply div_le_div₀ (by positivity)
  · exact pow_le_pow_of_le_one hL0 hL1 (Nat.pow_le_pow_right (by omega) (by omega))
  · positivity
  · exact pow_le_pow_right₀ hM (psiExp_le m hk)

/-- **Claim 16** (Claim 11 for `Δ = 4`). If `c₀ ≥ ((c ↦ 2^(Δ·2^(2c)))^[t]) c` bounds the palette
of the `0`-round algorithm at the end of the chain and `p₀ = 1/c₀^Δ` (the `0`-round bound), then
every `t`-round weak `c`-colouring algorithm fails locally with probability at least
`(p₀ / ((Δ+1) c₀))^((Δ+1)^(2t+1))`. -/
theorem claim_16 (hk : 0 < k) {t c c₀ : ℕ} (hc : 1 ≤ c) (hc₀ : (nodePal k)^[t] c ≤ c₀)
    {α : Type} [Fintype α] (hα : Fintype.card α ≤ c) (A : NodeAlg k Ω t α) :
    ((1 / (c₀ : ℝ) ^ (2 * k)) / ((2 * k + 1) * c₀)) ^ ((2 * k + 1) ^ (2 * t + 1)) ≤
      A.failProb μ := by
  have hC1 : 1 ≤ c₀ := le_trans hc (le_trans (le_iterate_nodePal hk _ _) hc₀)
  refine le_trans ?_ (nodeLB_lb (μ := μ) hk t c hc α hα A)
  refine le_trans ?_ (psi_iterate_le_lb hk t c c₀ hc hc₀)
  apply psi_iterate_ge hk hC1 (by positivity)
  apply div_le_one_of_le₀ _ (by positivity)
  exact one_le_pow₀ (by exact_mod_cast hC1)

end

end Podc.MinimalSymmetryBreaking
