import Papers.PODC2021.RandomizedSymmetryTopology.Model

/-!
# Lemma 3.2: the limit probability of solving a task is `0` or `1`

Fraigniaud, Gelles, Lotker, PODC 2021, Lemma 3.2.

The paper argues with Kolmogorov's zero–one law. We give an elementary counting proof which
needs only the three structural properties of full-information models (`FullInfoModel`):
if some window of `t₀` rounds of randomness makes the system solve the task, then so does the same
window occurring in rounds `j t₀ + 1, …, (j+1) t₀` (knowledge is a refinement of the knowledge of
the shifted run, `FullInfoModel.shift`), and the `m` disjoint windows are independent, so
`Pr[P(m t₀) solves O] ≥ 1 - (1 - p)^m` with `p = Pr[P(t₀) solves O] > 0`; moreover the probability
is nondecreasing in `t` (knowledge is cumulative, `FullInfoModel.prev`).

The counting part is stated for an abstract event `S ω t` (`IsGoodEvent`).
-/

open Finset Filter Topology

namespace Podc.RandomizedSymmetryTopology

variable {k : ℕ}

/-- An event `S ω t` ("the global state at time `t` is good") that depends only on the first `t`
rounds, persists in time, and is implied by the same event of a shifted run. -/
structure IsGoodEvent (S : Stream k → ℕ → Prop) : Prop where
  isLocal : ∀ ω ω' t, (∀ s < t, ω s = ω' s) → (S ω t ↔ S ω' t)
  mono : ∀ ω t, S ω t → S ω (t + 1)
  shift : ∀ ω s t, S (shiftStream ω s) t → S ω (s + t)

open Classical in
/-- The probability of `S` at time `t` under uniformly random source bits. -/
noncomputable def probEvent (S : Stream k → ℕ → Prop) (t : ℕ) : ℝ :=
  ((univ.filter fun r : Window k t => S (ext r) t).card : ℝ) / 2 ^ (k * t)

theorem probSolves_eq {n : ℕ} (M : FullInfoModel n k) {Out : Type} (O : Task n Out) :
    probSolves M O = probEvent (fun ω t => Solves O (M.K ω t)) := rfl

/-- `Solves O` is a good event in every full-information model. -/
theorem isGoodEvent_solves {n : ℕ} (M : FullInfoModel n k) {Out : Type} (O : Task n Out) :
    IsGoodEvent (fun ω t => Solves O (M.K ω t)) where
  isLocal ω ω' t h := by simp only [M.isLocal ω ω' t h]
  mono ω t h := by
    obtain ⟨g, hg⟩ := M.prev t
    exact h.of_comp g (hg ω)
  shift ω s t h := by
    obtain ⟨g, hg⟩ := M.shift ω s t
    exact h.of_comp g hg

theorem card_window (t : ℕ) : Fintype.card (Window k t) = 2 ^ (k * t) := by
  simp [Window, ← pow_mul]

namespace IsGoodEvent

variable {S : Stream k → ℕ → Prop}

theorem mono_le (hS : IsGoodEvent S) {ω : Stream k} {t t' : ℕ} (h : S ω t) (htt : t ≤ t') :
    S ω t' := by
  induction htt with
  | refl => exact h
  | step _ ih => exact hS.mono _ _ ih

theorem probEvent_nonneg (t : ℕ) : 0 ≤ probEvent S t := by
  unfold probEvent; positivity

theorem probEvent_le_one (t : ℕ) : probEvent S t ≤ 1 := by
  classical
  unfold probEvent
  rw [div_le_one (by positivity)]
  have := card_le_univ (univ.filter fun r : Window k t => S (ext r) t)
  rw [card_window] at this
  exact_mod_cast this

open Classical in
/-- If `S` at time `t` (depending only on the first `t` rounds) implies `S'` at time `t + 1`, then
`Pr[S at t] ≤ Pr[S' at t + 1]`. -/
theorem probEvent_le_succ_of {S' : Stream k → ℕ → Prop} {t : ℕ}
    (hloc : ∀ ω ω', (∀ s < t, ω s = ω' s) → (S ω t ↔ S ω' t)) (h : ∀ ω, S ω t → S' ω (t + 1)) :
    probEvent S t ≤ probEvent S' (t + 1) := by
  set G := univ.filter fun r : Window k t => S (ext r) t
  set G' := univ.filter fun r : Window k (t + 1) => S' (ext r) (t + 1)
  let e := Fin.succFunEquiv (Fin k → Bool) t
  have hsub : (G ×ˢ (univ : Finset (Fin k → Bool))).map e.symm.toEmbedding ⊆ G' := by
    intro r hr
    simp only [Finset.mem_map, mem_product, mem_univ, and_true, Equiv.coe_toEmbedding] at hr
    obtain ⟨⟨x, b⟩, hx, rfl⟩ := hr
    simp only [G, mem_filter, mem_univ, true_and] at hx
    simp only [G', mem_filter, mem_univ, true_and]
    apply h
    refine (hloc _ _ fun s hs => ?_).1 hx
    rw [ext_of_lt _ hs, ext_of_lt _ (by omega)]
    simp only [e, Fin.succFunEquiv, Equiv.symm_trans_apply]
    exact (Fin.append_left x (uniqueElim b) ⟨s, hs⟩).symm
  have hcard := card_le_card hsub
  rw [card_map, card_product, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at hcard
  unfold probEvent
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (G.card : ℝ) * 2 ^ (k * (t + 1)) = (G.card * 2 ^ k : ℕ) * 2 ^ (k * t) := by
        push_cast; ring
    _ ≤ (G'.card : ℝ) * 2 ^ (k * t) := by gcongr

/-- The probability is nondecreasing in time. -/
theorem probEvent_le_succ (hS : IsGoodEvent S) (t : ℕ) :
    probEvent S t ≤ probEvent S (t + 1) :=
  probEvent_le_succ_of (fun ω ω' h => hS.isLocal ω ω' t h) (fun ω => hS.mono ω t)

theorem monotone_probEvent (hS : IsGoodEvent S) : Monotone (probEvent S) :=
  monotone_nat_of_le_succ hS.probEvent_le_succ

open Classical in
/-- Disjoint windows (the events `E_{s t₀}` of the proof of Lemma 3.2):
`Pr[S at time m t₀] ≥ 1 - (1 - Pr[S at time t₀])^m`. -/
theorem one_sub_pow_le_probEvent (hS : IsGoodEvent S) (t₀ m : ℕ) :
    1 - (1 - probEvent S t₀) ^ m ≤ probEvent S (m * t₀) := by
  set G := univ.filter fun r : Window k t₀ => S (ext r) t₀
  set G' := univ.filter fun r : Window k (m * t₀) => S (ext r) (m * t₀)
  set B := univ.filter fun r : Window k (m * t₀) => ¬ S (ext r) (m * t₀)
  let Φ : Window k (m * t₀) ≃ (Fin m → Window k t₀) :=
    (finProdFinEquiv.arrowCongr (Equiv.refl _)).symm.trans (Equiv.curry _ _ _)
  have hΦ : ∀ r j (u : Fin t₀), Φ r j u = r (finProdFinEquiv (j, u)) := fun _ _ _ => rfl
  have hsub : B ⊆ (Fintype.piFinset fun _ => Gᶜ).map Φ.symm.toEmbedding := by
    intro r hr
    simp only [Finset.mem_map, Fintype.mem_piFinset, Equiv.coe_toEmbedding]
    refine ⟨Φ r, fun j => ?_, by simp⟩
    simp only [G, mem_compl, mem_filter, mem_univ, true_and]
    intro hj
    simp only [B, mem_filter, mem_univ, true_and] at hr
    apply hr
    have hjm : t₀ * j + t₀ ≤ m * t₀ := by
      have := Nat.mul_le_mul_left t₀ (Nat.succ_le_of_lt j.isLt)
      rw [Nat.mul_succ] at this; linarith [Nat.mul_comm t₀ m]
    have h1 : S (shiftStream (ext r) (t₀ * j)) t₀ := by
      refine (hS.isLocal _ _ t₀ fun s hs => ?_).1 hj
      have hlt : t₀ * j + s < m * t₀ := by omega
      rw [ext_of_lt _ hs, shiftStream, ext_of_lt _ hlt, hΦ]
      congr 1
      ext
      simp [finProdFinEquiv, add_comm]
    exact hS.mono_le (hS.shift _ _ _ h1) hjm
  have hcard := card_le_card hsub
  rw [card_map, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, card_compl,
    card_window] at hcard
  have hG : G.card ≤ 2 ^ (k * t₀) := by rw [← card_window]; exact card_le_univ _
  have hsplit : G'.card + B.card = 2 ^ (k * (m * t₀)) := by
    rw [← card_window]; exact card_filter_add_card_filter_not _
  have hN : (2 : ℝ) ^ (k * (m * t₀)) = ((2 : ℝ) ^ (k * t₀)) ^ m := by
    rw [← pow_mul]; ring_nf
  have hpos : (0 : ℝ) < 2 ^ (k * t₀) := by positivity
  have hG' : (G'.card : ℝ) = ((2 : ℝ) ^ (k * t₀)) ^ m - B.card := by
    rw [← hN]
    have : ((G'.card + B.card : ℕ) : ℝ) = ((2 ^ (k * (m * t₀)) : ℕ) : ℝ) := by rw [hsplit]
    push_cast at this; linarith
  have hB : (B.card : ℝ) ≤ ((2 : ℝ) ^ (k * t₀) - G.card) ^ m := by
    have : ((B.card : ℕ) : ℝ) ≤ (((2 ^ (k * t₀) - G.card) ^ m : ℕ) : ℝ) := by exact_mod_cast hcard
    rwa [Nat.cast_pow, Nat.cast_sub hG, Nat.cast_pow, Nat.cast_ofNat] at this
  unfold probEvent
  rw [hN, hG', one_sub_div hpos.ne', div_pow, sub_div, div_self (by positivity)]
  gcongr

/-- **Lemma 3.2** (abstract form): either the event never has positive probability, or its
probability tends to `1`. -/
theorem probEvent_zero_or_tendsto_one (hS : IsGoodEvent S) :
    (∀ t, probEvent S t = 0) ∨ Tendsto (probEvent S) atTop (𝓝 1) := by
  by_cases h : ∀ t, probEvent S t = 0
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨t₀, ht₀⟩ := h
  have hp : 0 < probEvent S t₀ := lt_of_le_of_ne (probEvent_nonneg t₀) (Ne.symm ht₀)
  have hbdd : BddAbove (Set.range (probEvent S)) := ⟨1, by rintro _ ⟨t, rfl⟩; exact probEvent_le_one t⟩
  have hlim := tendsto_atTop_ciSup hS.monotone_probEvent hbdd
  suffices hsup : (⨆ t, probEvent S t) = 1 by rwa [hsup] at hlim
  refine le_antisymm (ciSup_le probEvent_le_one) (le_of_forall_pos_lt_add fun ε hε => ?_)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε
    (show 1 - probEvent S t₀ < 1 by linarith)
  calc 1 < 1 - (1 - probEvent S t₀) ^ m + ε := by linarith
    _ ≤ probEvent S (m * t₀) + ε := by gcongr; exact hS.one_sub_pow_le_probEvent t₀ m
    _ ≤ (⨆ t, probEvent S t) + ε := by gcongr; exact le_ciSup hbdd _

end IsGoodEvent

/-- **Lemma 3.2.** For every input-free task `O` and every full-information model (blackboard or
message passing, with any randomness configuration and port numbering), the probability that the
global state solves `O` is nondecreasing and its limit is `0` or `1`; more precisely, either it is
`0` at every time, or it tends to `1`. -/
theorem lemma_3_2 {n : ℕ} (M : FullInfoModel n k) {Out : Type} (O : Task n Out) :
    (∀ t, probSolves M O t = 0) ∨ EventuallySolvable M O :=
  (isGoodEvent_solves M O).probEvent_zero_or_tendsto_one

/-- Lemma 3.2 in the paper's form: `lim_{t→∞} Pr[P(t) solves O | α] ∈ {0, 1}`. -/
theorem lemma_3_2' {n : ℕ} (M : FullInfoModel n k) {Out : Type} (O : Task n Out) :
    ∃ L ∈ ({0, 1} : Set ℝ), Tendsto (probSolves M O) atTop (𝓝 L) := by
  rcases lemma_3_2 M O with h | h
  · refine ⟨0, by simp, ?_⟩
    have : probSolves M O = fun _ => 0 := funext h
    rw [this]; exact tendsto_const_nhds
  · exact ⟨1, by simp, h⟩

/-- A single time with positive probability of solving suffices for eventual solvability. -/
theorem eventuallySolvable_of_pos {n : ℕ} (M : FullInfoModel n k) {Out : Type} {O : Task n Out}
    {t : ℕ} (ht : 0 < probSolves M O t) : EventuallySolvable M O :=
  (lemma_3_2 M O).resolve_left fun h => by simp [h t] at ht

/-- A task whose probability of being solved is `0` at all times is not eventually solvable. -/
theorem not_eventuallySolvable_of_zero {n : ℕ} (M : FullInfoModel n k) {Out : Type}
    {O : Task n Out} (h : ∀ t, probSolves M O t = 0) : ¬ EventuallySolvable M O := by
  intro hO
  have : Tendsto (probSolves M O) atTop (𝓝 0) := by
    have : probSolves M O = fun _ => 0 := funext h
    rw [this]; exact tendsto_const_nhds
  exact zero_ne_one (tendsto_nhds_unique this hO)

open Classical in
/-- Positive probability at time `t` iff some realization of length `t` solves. -/
theorem probSolves_pos_iff {n : ℕ} (M : FullInfoModel n k) {Out : Type} (O : Task n Out) (t : ℕ) :
    0 < probSolves M O t ↔ ∃ r : Window k t, Solves O (M.K (ext r) t) := by
  unfold probSolves
  rw [div_pos_iff_of_pos_right (by positivity), Nat.cast_pos, card_pos]
  simp [Finset.Nonempty]

open Classical in
/-- Probability `0` at time `t` iff no realization of length `t` solves. -/
theorem probSolves_eq_zero_iff {n : ℕ} (M : FullInfoModel n k) {Out : Type} (O : Task n Out)
    (t : ℕ) : probSolves M O t = 0 ↔ ∀ r : Window k t, ¬ Solves O (M.K (ext r) t) := by
  have h0 : 0 ≤ probSolves M O t := by unfold probSolves; positivity
  have := probSolves_pos_iff M O t
  constructor
  · intro h r hr; exact (this.2 ⟨r, hr⟩).ne' h
  · intro h; by_contra h'
    obtain ⟨r, hr⟩ := this.1 (lt_of_le_of_ne h0 (Ne.symm h'))
    exact h r hr

end Podc.RandomizedSymmetryTopology
