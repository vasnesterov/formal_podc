import Mathlib

/-!
# The zero-communication edge colouring (ZEC) game (Section 6.2 of [CMNS25])

[CMNS25]: Y.-J. Chang, G. Mishra, H. T. Nguyen, F. D. Salim,
*Round and Communication Efficient Graph Coloring*, PODC 2025 (arXiv 2412.12589).

Vertices `v_A, v_B, v_1, …, v_7`. Alice receives a uniformly random pair `S_A ⊆ {1,…,7}` (her edges
are `{v_A, v_i}`, `i ∈ S_A`), Bob independently a uniformly random pair `S_B` (edges `{v_B, v_i}`).
Without communication and with private randomness only, each colours their own edges with
colours `{c_1, c_2, c_3}`. They win iff the union is a proper edge colouring.

## Model

* Indices `1..7` are `Fin 7`, colours are `Fin 3`; an input is a 2-element `Finset (Fin 7)`
  (`inputs`, 21 of them).
* An output of Alice is a map `a : Fin 7 → Fin 3`, `a i` being the colour of `{v_A, v_i}`; only the
  values on `S_A` matter for winning, so this loses no generality.
* A randomized private-coin strategy is a stochastic kernel `p : Finset (Fin 7) → (Fin 7 → Fin 3) → ℝ`
  (`IsStrategy`): `p s a` is the probability of output `a` on input `s`. Private randomness and
  independent inputs make the joint law of `(S_A, S_B, a, b)` the product
  `(1/21) (1/21) p_A(S_A, a) p_B(S_B, b)` (`winProb`).

## Main results

* `lemma_6_2`: every strategy pair wins with probability `≤ 11024/11025` (Lemma 6.2).
* `exists_losing_input`: deterministic strategies lose on some pair of inputs.
* `winProb_pos_example`: non-vacuity — some strategy pair has positive winning probability.
-/

namespace Podc.RoundEfficientColoring

open Finset

/-- The 21 possible inputs of a player: 2-subsets of `{1,…,7}` (here `Fin 7`). -/
def inputs : Finset (Finset (Fin 7)) := (univ : Finset (Fin 7)).powersetCard 2

/-- A randomized (private-coin) strategy: for every input `s`, `p s` is a probability distribution
on outputs `Fin 7 → Fin 3` (colour of the edge to `v_i`). -/
def IsStrategy (p : Finset (Fin 7) → (Fin 7 → Fin 3) → ℝ) : Prop :=
  (∀ s a, 0 ≤ p s a) ∧ ∀ s, ∑ a, p s a = 1

/-- Winning condition: Alice's edges (all sharing `v_A`) get distinct colours, Bob's edges (all
sharing `v_B`) get distinct colours, and for every `i ∈ S_A ∩ S_B` the edges `{v_A, v_i}` and
`{v_B, v_i}` get distinct colours. These are exactly the adjacencies of `G = (V, E_A ∪ E_B)`. -/
def win (sA sB : Finset (Fin 7)) (a b : Fin 7 → Fin 3) : Prop :=
  (∀ i ∈ sA, ∀ j ∈ sA, i ≠ j → a i ≠ a j) ∧
  (∀ i ∈ sB, ∀ j ∈ sB, i ≠ j → b i ≠ b j) ∧
  (∀ i ∈ sA ∩ sB, a i ≠ b i)

instance (sA sB : Finset (Fin 7)) (a b : Fin 7 → Fin 3) : Decidable (win sA sB a b) := by
  unfold win; infer_instance

/-- Probability that the players win the ZEC game with strategies `pA`, `pB`. -/
noncomputable def winProb (pA pB : Finset (Fin 7) → (Fin 7 → Fin 3) → ℝ) : ℝ :=
  (1 / 21) ^ 2 * ∑ sA ∈ inputs, ∑ sB ∈ inputs, ∑ a, ∑ b,
    pA sA a * pB sB b * (if win sA sB a b then 1 else 0)

/-! ### Auxiliary probability notation -/

/-- `pr p s P` = probability that the output satisfies `P` on input `s`. -/
noncomputable def pr (p : Finset (Fin 7) → (Fin 7 → Fin 3) → ℝ) (s : Finset (Fin 7))
    (P : (Fin 7 → Fin 3) → Prop) [DecidablePred P] : ℝ :=
  ∑ a, if P a then p s a else 0

lemma card_inputs : inputs.card = 21 := by
  simp [inputs, Finset.card_powersetCard]; rfl

lemma pair_mem_inputs {i j : Fin 7} (h : i ≠ j) : ({i, j} : Finset (Fin 7)) ∈ inputs := by
  simp [inputs, Finset.mem_powersetCard, Finset.card_pair h]

variable {p pA pB : Finset (Fin 7) → (Fin 7 → Fin 3) → ℝ}

lemma pr_true (hp : IsStrategy p) (s : Finset (Fin 7)) : pr p s (fun _ => True) = 1 := by
  simp [pr, hp.2 s]

lemma sum_pr_colour (hp : IsStrategy p) (s : Finset (Fin 7)) (i : Fin 7) :
    ∑ c : Fin 3, pr p s (fun a => a i = c) = 1 := by
  unfold pr
  rw [Finset.sum_comm]
  simp [hp.2 s]

/-- `Pr[P ∧ Q] ≥ Pr[P] + Pr[Q] - 1`. -/
lemma pr_and_ge (hp : IsStrategy p) (s : Finset (Fin 7)) (P Q : (Fin 7 → Fin 3) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    pr p s P + pr p s Q - 1 ≤ pr p s (fun a => P a ∧ Q a) := by
  have h1 : pr p s P + pr p s Q - 1 =
      ∑ a, ((if P a then p s a else 0) + (if Q a then p s a else 0) - p s a) := by
    simp only [pr, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp.2 s]
  rw [h1, pr]
  refine Finset.sum_le_sum fun a _ => ?_
  have := hp.1 s a
  split_ifs <;> simp_all

/-- Loss on a fixed input pair is at least `Pr_A[P] · Pr_B[Q]` whenever `P a ∧ Q b` forces a loss. -/
lemma pr_mul_pr_le_loss (sA sB : Finset (Fin 7)) (hA : IsStrategy pA) (hB : IsStrategy pB)
    (P Q : (Fin 7 → Fin 3) → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ a b, P a → Q b → ¬ win sA sB a b) :
    pr pA sA P * pr pB sB Q ≤
      ∑ a, ∑ b, pA sA a * pB sB b * (if win sA sB a b then 0 else 1) := by
  rw [pr, pr, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  have h1 := hA.1 sA a
  have h2 := hB.1 sB b
  by_cases hP : P a <;> by_cases hQ : Q b
  · simp [hP, hQ, h a b hP hQ]
  all_goals
    simp only [hP, hQ, ite_false, ite_true, zero_mul, mul_zero]
    split_ifs <;> positivity

/-- `1 - winProb` is the probability of losing. -/
lemma one_sub_winProb (hA : IsStrategy pA) (hB : IsStrategy pB) :
    1 - winProb pA pB = (1 / 21) ^ 2 * ∑ sA ∈ inputs, ∑ sB ∈ inputs, ∑ a, ∑ b,
      pA sA a * pB sB b * (if win sA sB a b then 0 else 1) := by
  have key : ∀ sA sB a b, pA sA a * pB sB b * (if win sA sB a b then 1 else 0) =
      pA sA a * pB sB b - pA sA a * pB sB b * (if win sA sB a b then 0 else 1) := by
    intro sA sB a b; split_ifs <;> ring
  have tot : ∀ sA sB, ∑ a, ∑ b, pA sA a * pB sB b = 1 := by
    intro sA sB; rw [← Finset.sum_mul_sum, hA.2, hB.2, one_mul]
  simp only [winProb, key, Finset.sum_sub_distrib, tot, Finset.sum_const, card_inputs]
  norm_num
  ring

/-- Loss probability is at least `1/441` times the loss on any single input pair. -/
lemma loss_ge_single (hA : IsStrategy pA) (hB : IsStrategy pB) {sA sB : Finset (Fin 7)}
    (hsA : sA ∈ inputs) (hsB : sB ∈ inputs) :
    (1 / 21) ^ 2 * ∑ a, ∑ b, pA sA a * pB sB b * (if win sA sB a b then 0 else 1)
      ≤ 1 - winProb pA pB := by
  have hnn : ∀ sA sB, 0 ≤ ∑ a, ∑ b, pA sA a * pB sB b * (if win sA sB a b then 0 else 1) := by
    intro sA sB
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    have := hA.1 sA a; have := hB.1 sB b
    split_ifs <;> positivity
  rw [one_sub_winProb hA hB]
  gcongr
  calc _ ≤ ∑ sB ∈ inputs, ∑ a, ∑ b, pA sA a * pB sB b * (if win sA sB a b then 0 else 1) :=
        Finset.single_le_sum (f := fun sB => ∑ a, ∑ b, pA sA a * pB sB b *
          (if win sA sB a b then 0 else 1)) (fun sB _ => hnn sA sB) hsB
    _ ≤ _ := Finset.single_le_sum (f := fun sA => ∑ sB ∈ inputs, ∑ a, ∑ b,
          pA sA a * pB sB b * (if win sA sB a b then 0 else 1))
          (fun sA _ => Finset.sum_nonneg fun sB _ => hnn sA sB) hsA

/-! ### Labels -/

/-- The label `L(v_i)` of the paper: colours `c` such that on some input containing `i` the edge
to `v_i` gets colour `c` with probability at least `1/5`. -/
noncomputable def label (p : Finset (Fin 7) → (Fin 7 → Fin 3) → ℝ) (i : Fin 7) : Finset (Fin 3) :=
  univ.filter fun c => ∃ s ∈ inputs, i ∈ s ∧ 1 / 5 ≤ pr p s (fun a => a i = c)

lemma mem_label {i : Fin 7} {c : Fin 3} :
    c ∈ label p i ↔ ∃ s ∈ inputs, i ∈ s ∧ 1 / 5 ≤ pr p s (fun a => a i = c) := by
  simp [label]

lemma label_nonempty (hp : IsStrategy p) (i : Fin 7) : (label p i).Nonempty := by
  set j : Fin 7 := if i = 0 then 1 else 0
  have hij : i ≠ j := by fin_cases i <;> simp [j]
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hlt : ∀ c : Fin 3, pr p {i, j} (fun a => a i = c) < 1 / 5 := by
    intro c
    by_contra hc
    have : c ∈ label p i := mem_label.2 ⟨_, pair_mem_inputs hij, by simp, not_lt.1 hc⟩
    simp [hne] at this
  have := sum_pr_colour hp {i, j} i
  rw [Fin.sum_univ_three] at this
  linarith [hlt 0, hlt 1, hlt 2]

/-- If `L(v_i) = {c}`, then on every input containing `i` the edge to `v_i` gets colour `c` with
probability at least `3/5`. -/
lemma pr_ge_of_label_eq (hp : IsStrategy p) {i : Fin 7} {c : Fin 3} (hL : label p i = {c})
    {s : Finset (Fin 7)} (hs : s ∈ inputs) (his : i ∈ s) :
    3 / 5 ≤ pr p s (fun a => a i = c) := by
  have hlt : ∀ c', c' ≠ c → pr p s (fun a => a i = c') < 1 / 5 := by
    intro c' hc'
    by_contra h
    have : c' ∈ label p i := mem_label.2 ⟨s, hs, his, not_lt.1 h⟩
    simp [hL, hc'] at this
  have hsum := sum_pr_colour hp s i
  rw [← Finset.add_sum_erase _ _ (mem_univ c)] at hsum
  have hle : ∑ c' ∈ univ.erase c, pr p s (fun a => a i = c') ≤ ∑ c' ∈ univ.erase c, (1 / 5 : ℝ) :=
    Finset.sum_le_sum fun c' hc' => (hlt c' (Finset.ne_of_mem_erase hc')).le
  rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ c)] at hle
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  push_cast at hle
  linarith

/-! ### The combinatorial core (pigeonhole) -/

/-- If no two indices share the same singleton label, at least four indices have a label of size
at least `2`. -/
lemma four_le_card_big (L : Fin 7 → Finset (Fin 3)) (hne : ∀ i, (L i).Nonempty)
    (h : ¬ ∃ i j c, i ≠ j ∧ L i = {c} ∧ L j = {c}) :
    4 ≤ (univ.filter fun i => 2 ≤ (L i).card).card := by
  set V := univ.filter fun i => (L i).card = 1
  have hinj : Set.InjOn L V := by
    intro i hi j hj hij
    simp only [V, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq,
      Finset.card_eq_one] at hi hj
    obtain ⟨c, hc⟩ := hi
    by_contra hne'
    exact h ⟨i, j, c, hne', hc, hij ▸ hc⟩
  have hV : V.card ≤ 3 := by
    rw [← Finset.card_image_of_injOn hinj]
    have hsub : V.image L ⊆ univ.filter fun t : Finset (Fin 3) => t.card = 1 := by
      intro t ht
      simp only [mem_image, V, mem_filter, mem_univ, true_and] at ht
      obtain ⟨i, hi, rfl⟩ := ht
      simpa using hi
    exact (Finset.card_le_card hsub).trans (by decide)
  have hsub : univ \ V ⊆ univ.filter fun i => 2 ≤ (L i).card := by
    intro i hi
    simp only [V, mem_sdiff, mem_univ, mem_filter, true_and] at hi ⊢
    have := (hne i).card_pos
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (subset_univ _)] at this
  simp only [card_univ, Fintype.card_fin] at this
  omega

/-- Pigeonhole core of the proof of Lemma 6.2: either one player has two indices with the same
singleton label (Case 1), or some index has a colour common to both labels (Case 2). -/
lemma labels_cases (LA LB : Fin 7 → Finset (Fin 3)) (hA : ∀ i, (LA i).Nonempty)
    (hB : ∀ i, (LB i).Nonempty) :
    (∃ i j c, i ≠ j ∧ LA i = {c} ∧ LA j = {c}) ∨ (∃ i j c, i ≠ j ∧ LB i = {c} ∧ LB j = {c}) ∨
      ∃ i c, c ∈ LA i ∧ c ∈ LB i := by
  by_cases h1 : ∃ i j c, i ≠ j ∧ LA i = {c} ∧ LA j = {c}
  · exact Or.inl h1
  by_cases h2 : ∃ i j c, i ≠ j ∧ LB i = {c} ∧ LB j = {c}
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ?_)
  have cA := four_le_card_big LA hA h1
  have cB := four_le_card_big LB hB h2
  obtain ⟨i, hi⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (subset_univ _) (subset_univ _)
    (by simp only [card_univ, Fintype.card_fin]; omega : (univ : Finset (Fin 7)).card <
      (univ.filter fun i => 2 ≤ (LA i).card).card + (univ.filter fun i => 2 ≤ (LB i).card).card)
  simp only [mem_inter, mem_filter, mem_univ, true_and] at hi
  obtain ⟨c, hc⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (subset_univ (LA i))
    (subset_univ (LB i)) (by simp only [card_univ, Fintype.card_fin]; omega)
  exact ⟨i, c, (mem_inter.1 hc).1, (mem_inter.1 hc).2⟩

/-! ### Lemma 6.2 -/

/-- Case 1 for Alice: two indices `i ≠ j` with `L_A(v_i) = L_A(v_j) = {c}` force a loss with
probability at least `1/(441·5)` (we keep a single input pair; the paper sums over Bob's inputs and
gets `1/105`). -/
lemma case1 (hA : IsStrategy pA) (hB : IsStrategy pB) {i j : Fin 7} {c : Fin 3} (hij : i ≠ j)
    (hi : label pA i = {c}) (hj : label pA j = {c}) :
    1 / 11025 ≤ 1 - winProb pA pB := by
  have hs := pair_mem_inputs hij
  have h1 := pr_ge_of_label_eq hA hi hs (by simp)
  have h2 := pr_ge_of_label_eq hA hj hs (by simp)
  have h3 := pr_and_ge hA {i, j} (fun a => a i = c) (fun a => a j = c)
  have h4 := pr_mul_pr_le_loss {i, j} {i, j} hA hB (fun a => a i = c ∧ a j = c) (fun _ => True)
    (by
      rintro a b ⟨ha, hb⟩ - hw
      exact hw.1 i (by simp) j (by simp) hij (ha.trans hb.symm))
  rw [pr_true hB, mul_one] at h4
  have h5 := loss_ge_single hA hB hs hs
  nlinarith

/-- Case 1 for Bob (symmetric). -/
lemma case1' (hA : IsStrategy pA) (hB : IsStrategy pB) {i j : Fin 7} {c : Fin 3} (hij : i ≠ j)
    (hi : label pB i = {c}) (hj : label pB j = {c}) :
    1 / 11025 ≤ 1 - winProb pA pB := by
  have hs := pair_mem_inputs hij
  have h1 := pr_ge_of_label_eq hB hi hs (by simp)
  have h2 := pr_ge_of_label_eq hB hj hs (by simp)
  have h3 := pr_and_ge hB {i, j} (fun a => a i = c) (fun a => a j = c)
  have h4 := pr_mul_pr_le_loss {i, j} {i, j} hA hB (fun _ => True) (fun b => b i = c ∧ b j = c)
    (by
      rintro a b - ⟨ha, hb⟩ hw
      exact hw.2.1 i (by simp) j (by simp) hij (ha.trans hb.symm))
  rw [pr_true hA, one_mul] at h4
  have h5 := loss_ge_single hA hB hs hs
  nlinarith

/-- Case 2: a colour `c ∈ L_A(v_i) ∩ L_B(v_i)` forces a loss with probability at least
`(1/21 · 1/5)^2 = 1/11025`. -/
lemma case2 (hA : IsStrategy pA) (hB : IsStrategy pB) {i : Fin 7} {c : Fin 3}
    (hcA : c ∈ label pA i) (hcB : c ∈ label pB i) :
    1 / 11025 ≤ 1 - winProb pA pB := by
  obtain ⟨TA, hTA, hiA, hpA⟩ := mem_label.1 hcA
  obtain ⟨TB, hTB, hiB, hpB⟩ := mem_label.1 hcB
  have h4 := pr_mul_pr_le_loss TA TB hA hB (fun a => a i = c) (fun b => b i = c)
    (by
      intro a b ha hb hw
      exact hw.2.2 i (mem_inter.2 ⟨hiA, hiB⟩) (ha.trans hb.symm))
  have h5 := loss_ge_single hA hB hTA hTB
  have h6 : 1 / 25 ≤ pr pA TA (fun a => a i = c) * pr pB TB (fun b => b i = c) := by
    nlinarith
  nlinarith

/-- Lemma 6.2 of [CMNS25]: for every pair of randomized private-coin strategies, the probability
of winning the ZEC game (producing a proper 3-edge colouring of `G = (V, E_A ∪ E_B)`) is at most
`11024/11025`. -/
theorem lemma_6_2 (pA pB : Finset (Fin 7) → (Fin 7 → Fin 3) → ℝ)
    (hA : IsStrategy pA) (hB : IsStrategy pB) :
    winProb pA pB ≤ 11024 / 11025 := by
  suffices 1 / 11025 ≤ 1 - winProb pA pB by linarith
  rcases labels_cases (label pA) (label pB) (label_nonempty hA) (label_nonempty hB) with
    ⟨i, j, c, hij, hi, hj⟩ | ⟨i, j, c, hij, hi, hj⟩ | ⟨i, c, hcA, hcB⟩
  · exact case1 hA hB hij hi hj
  · exact case1' hA hB hij hi hj
  · exact case2 hA hB hcA hcB

/-! ### Deterministic strategies -/

/-- The point-mass strategy of a deterministic strategy `f`. -/
noncomputable def detStrategy (f : Finset (Fin 7) → Fin 7 → Fin 3) :
    Finset (Fin 7) → (Fin 7 → Fin 3) → ℝ :=
  fun s a => if a = f s then 1 else 0

lemma detStrategy_isStrategy (f : Finset (Fin 7) → Fin 7 → Fin 3) :
    IsStrategy (detStrategy f) :=
  ⟨fun s a => by unfold detStrategy; split_ifs <;> norm_num,
    fun s => by simp [detStrategy]⟩

lemma winProb_det (fA fB : Finset (Fin 7) → Fin 7 → Fin 3) :
    winProb (detStrategy fA) (detStrategy fB) = (1 / 21) ^ 2 * ∑ sA ∈ inputs, ∑ sB ∈ inputs,
      (if win sA sB (fA sA) (fB sB) then 1 else 0) := by
  unfold winProb detStrategy
  congr 1
  refine Finset.sum_congr rfl fun sA _ => Finset.sum_congr rfl fun sB _ => ?_
  rw [Fintype.sum_eq_single (fA sA) (fun a ha => by simp [ha])]
  rw [Fintype.sum_eq_single (fB sB) (fun b hb => by simp [hb])]
  simp

/-- Deterministic corollary of Lemma 6.2 (`2Δ - 1 = 3` colours cannot be achieved without
communication for `Δ = 2`): any deterministic strategies lose on some pair of inputs. -/
theorem exists_losing_input (fA fB : Finset (Fin 7) → Fin 7 → Fin 3) :
    ∃ sA ∈ inputs, ∃ sB ∈ inputs, ¬ win sA sB (fA sA) (fB sB) := by
  by_contra h
  push Not at h
  have hw := lemma_6_2 _ _ (detStrategy_isStrategy fA) (detStrategy_isStrategy fB)
  rw [winProb_det] at hw
  have : ∑ sA ∈ inputs, ∑ sB ∈ inputs,
      (if win sA sB (fA sA) (fB sB) then (1 : ℝ) else 0) = 21 * 21 := by
    rw [Finset.sum_congr rfl fun sA hsA => Finset.sum_congr rfl fun sB hsB =>
      ite_eq_left (h sA hsA sB hsB)]
    simp [card_inputs]
  rw [this] at hw
  norm_num at hw

/-- Non-vacuity: some strategy pair wins with positive probability (Alice colours the edge to the
smaller index of her pair with `c_1` and the other with `c_2`; Bob uses `c_2`, `c_3` likewise). -/
theorem winProb_pos_example :
    ∃ pA pB, IsStrategy pA ∧ IsStrategy pB ∧ 0 < winProb pA pB := by
  let fA : Finset (Fin 7) → Fin 7 → Fin 3 := fun s i => if ∀ j ∈ s, i ≤ j then 0 else 1
  let fB : Finset (Fin 7) → Fin 7 → Fin 3 := fun s i => if ∀ j ∈ s, i ≤ j then 1 else 2
  refine ⟨_, _, detStrategy_isStrategy fA, detStrategy_isStrategy fB, ?_⟩
  rw [winProb_det]
  have hw : win {0, 1} {2, 3} (fA {0, 1}) (fB {2, 3}) := by decide
  have hnn : ∀ sA sB, (0 : ℝ) ≤ if win sA sB (fA sA) (fB sB) then 1 else 0 := by
    intro sA sB; split_ifs <;> norm_num
  have h1 : (1 : ℝ) ≤ ∑ sA ∈ inputs, ∑ sB ∈ inputs, if win sA sB (fA sA) (fB sB) then 1 else 0 :=
    calc (1 : ℝ) = if win {0, 1} {2, 3} (fA {0, 1}) (fB {2, 3}) then 1 else 0 := by simp [hw]
      _ ≤ ∑ sB ∈ inputs, if win {0, 1} sB (fA {0, 1}) (fB sB) then 1 else 0 :=
        Finset.single_le_sum (f := fun sB => if win {0, 1} sB (fA {0, 1}) (fB sB) then (1 : ℝ)
          else 0) (fun sB _ => hnn _ sB) (pair_mem_inputs (by decide))
      _ ≤ _ := Finset.single_le_sum (f := fun sA => ∑ sB ∈ inputs,
          if win sA sB (fA sA) (fB sB) then (1 : ℝ) else 0)
          (fun sA _ => Finset.sum_nonneg fun sB _ => hnn sA sB) (pair_mem_inputs (by decide))
  positivity

end Podc.RoundEfficientColoring
