import Papers.PODC2025.MinimalistLE.Convergence
import Cslib.Probability.CoinField

/-!
# Probabilistic part: elimination of leaders window by window

Coins are i.i.d. `Bernoulli(p)` indexed by `ℕ × V` (`coinMeasure p`), and the execution is
`exec G init (field ω)`. For two leaders `u ≠ v` and a window `[t, t+L)`, `L = 2D+3`, the "good"
event `Good D t u v` (some `true` coin of `u` in `[t+2, t+D+2]`, all coins of `v` in `[t, t+L)`
`false`) depends only on coins of the window and has probability `Q = (1-(1-p)^{D+1})(1-p)^L`.
By `elim_window`, `u` and `v` are not both leaders at time `t+L` if the right one of `Good D t u v`,
`Good D t v u` happens (which one depends on the past through `N_t(u) ≥ N_t(v)`), so
`P(both leaders at t+L) ≤ (1-Q)·P(both leaders at t)`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory unitInterval Cslib.Probability
open scoped ENNReal

namespace MinimalistLE

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {init : V → St}

/-- The coin field `c t v = ω (t, v)`. -/
def field (ω : ℕ × V → Bool) : ℕ → V → Bool := fun t v => ω (t, v)

variable (G init) in
/-- `u` and `v` are both leaders in round `t`. -/
def Both (t : ℕ) (u v : V) : Set (ℕ × V → Bool) :=
  {ω | (exec G init (field ω) t u).leader = true ∧ (exec G init (field ω) t v).leader = true}

variable (G init) in
/-- `N_t(v) ≤ N_t(u)`. -/
def AtLeast (t : ℕ) (u v : V) : Set (ℕ × V → Bool) :=
  {ω | nbeep G init (field ω) t v ≤ nbeep G init (field ω) t u}

/-- The good event of the window `[t, t + 2D + 3)` for the ordered pair `(u, v)`. -/
def Good (D t : ℕ) (u v : V) : Set (ℕ × V → Bool) :=
  {ω | (∃ s, t + 2 ≤ s ∧ s ≤ t + D + 2 ∧ ω (s, u) = true) ∧
    ∀ s, t ≤ s → s < t + (2 * D + 3) → ω (s, v) = false}

/-- Coins of rounds `< t`. -/
def past (t : ℕ) : Finset (ℕ × V) := Finset.range t ×ˢ Finset.univ

theorem field_eq_of {ω ω' : ℕ × V → Bool} {t : ℕ} (h : ∀ i ∈ past (V := V) t, ω i = ω' i) :
    ∀ s < t, field ω s = field ω' s := fun s hs => funext fun v => h (s, v) (by simp [past, hs])

theorem determined_both (t : ℕ) (u v : V) : Determined (Both G init t u v) (past t) :=
  fun ω ω' h => by simp only [Both, Set.mem_ofPred_eq, exec_congr (field_eq_of h)]

theorem determined_atLeast (t : ℕ) (u v : V) : Determined (AtLeast G init t u v) (past t) :=
  fun ω ω' h => by simp only [AtLeast, Set.mem_ofPred_eq, nbeep_congr (field_eq_of h)]

/-- Coins of node `u` in rounds `[a, b]`. -/
def window (a b : ℕ) (u : V) : Finset (ℕ × V) := (Finset.Icc a b).image fun s => (s, u)

theorem card_window (a b : ℕ) (u : V) : (window a b u).card = b + 1 - a := by
  rw [window, Finset.card_image_of_injective _ fun x y h => (Prod.mk.inj h).1, Nat.card_Icc]

theorem mem_window {a b : ℕ} {u : V} {i : ℕ × V} : i ∈ window a b u ↔ a ≤ i.1 ∧ i.1 ≤ b ∧ i.2 = u := by
  obtain ⟨s, w⟩ := i
  simp only [window, Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
  constructor
  · rintro ⟨s', ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, rfl⟩; exact ⟨s, ⟨h1, h2⟩, rfl, rfl⟩

/-- `Good = (not all coins of u in [t+2, t+D+2] false) ∩ (all coins of v in [t, t+2D+2] false)`. -/
theorem good_eq (D t : ℕ) (u v : V) : Good D t u v =
    {ω | ∀ i ∈ window (t + 2) (t + D + 2) u, ω i = false}ᶜ ∩
      {ω | ∀ i ∈ window t (t + 2 * D + 2) v, ω i = false} := by
  ext ω
  simp only [Good, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, mem_window, and_imp,
    Prod.forall]
  refine and_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨s, h1, h2, h3⟩ h; simp [h s u h1 h2 rfl] at h3
  · intro h; by_contra h'; push Not at h'
    exact h fun s w h1 h2 hw => by subst hw; simpa using h' s h1 h2
  · rintro h s w h1 h2 rfl; exact h s h1 (by omega)
  · intro h s h1 h2; exact h s v h1 (by omega) rfl

theorem determined_good (D t : ℕ) (u v : V) :
    Determined (Good D t u v) (window (t + 2) (t + D + 2) u ∪ window t (t + 2 * D + 2) v) := by
  rw [good_eq]; exact (determined_forall_eq_false _).compl.inter (determined_forall_eq_false _)

/-- `Q = (1-(1-p)^{D+1})·(1-p)^{2D+3}` as an element of `ℝ≥0∞`. -/
noncomputable def goodProb (p : I) (D : ℕ) : ℝ≥0∞ :=
  (1 - (toNNReal (σ p) : ℝ≥0∞) ^ (D + 1)) * (toNNReal (σ p) : ℝ≥0∞) ^ (2 * D + 3)

theorem coinMeasure_good (p : I) (D t : ℕ) {u v : V} (huv : u ≠ v) :
    coinMeasure p (Good D t u v) = goodProb p D := by
  rw [good_eq, coinMeasure_inter p (determined_forall_eq_false _).compl (determined_forall_eq_false _),
    prob_compl_eq_one_sub (determined_forall_eq_false _).measurableSet, coinMeasure_forall_eq_false, coinMeasure_forall_eq_false,
    card_window, card_window, goodProb]
  · congr 3 <;> omega
  · rw [Finset.disjoint_left]; intro i hi hi'
    rw [mem_window] at hi hi'; exact huv (hi.2.2.symm.trans hi'.2.2)

theorem disjoint_past_good (D t : ℕ) (u v : V) :
    Disjoint (past (V := V) t) (window (t + 2) (t + D + 2) u ∪ window t (t + 2 * D + 2) v) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  simp only [past, Finset.mem_product, Finset.mem_range] at hi
  rcases Finset.mem_union.1 hi' with h | h <;> rw [mem_window] at h <;> omega

/-- **One window.** For `u ≠ v`,
`P(u, v both leaders in round t + 2D + 3) ≤ (1 - Q)·P(u, v both leaders in round t)`. -/
theorem both_step (hconn : G.Connected) (hW : ∀ v, (init v).phase = .W) (p : I) {D : ℕ}
    (hD : ∀ a b, G.dist a b ≤ D) {u v : V} (huv : u ≠ v) (t : ℕ) :
    coinMeasure p (Both G init (t + (2 * D + 3)) u v) ≤ (1 - goodProb p D) * coinMeasure p (Both G init t u v) := by
  set A := Both G init t u v
  set X := AtLeast G init t u v
  have hsub : Both G init (t + (2 * D + 3)) u v ⊆
      (A ∩ X ∩ (Good D t u v)ᶜ) ∪ ((A \ X) ∩ (Good D t v u)ᶜ) := by
    rintro ω ⟨hu, hv⟩
    have hA : ω ∈ A := ⟨leader_anti (by omega) hu, leader_anti (by omega) hv⟩
    by_cases hX : ω ∈ X
    · refine Or.inl ⟨⟨hA, hX⟩, fun hg => ?_⟩
      exact elim_window hconn hW hD hX hg.1 hg.2 hu hv
    · refine Or.inr ⟨⟨hA, hX⟩, fun hg => ?_⟩
      have hX' : nbeep G init (field ω) t u ≤ nbeep G init (field ω) t v := by
        simp only [X, AtLeast, Set.mem_ofPred_eq, not_le] at hX; omega
      exact elim_window hconn hW hD hX' hg.1 hg.2 hv hu
  have hAX : Determined (A ∩ X) (past t) := by
    simpa using (determined_both (G := G) (init := init) t u v).inter (determined_atLeast t u v)
  have hAX' : Determined (A \ X) (past t) := by
    simpa [Set.sdiff_eq] using
      (determined_both (G := G) (init := init) t u v).inter (determined_atLeast t u v).compl
  have hgc : ∀ a b : V, a ≠ b → coinMeasure p (Good D t a b)ᶜ = 1 - goodProb p D := fun a b hab => by
    rw [prob_compl_eq_one_sub (determined_good D t a b).measurableSet, coinMeasure_good p D t hab]
  calc coinMeasure p (Both G init (t + (2 * D + 3)) u v)
      ≤ coinMeasure p (A ∩ X ∩ (Good D t u v)ᶜ) + coinMeasure p ((A \ X) ∩ (Good D t v u)ᶜ) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = coinMeasure p (A ∩ X) * (1 - goodProb p D) + coinMeasure p (A \ X) * (1 - goodProb p D) := by
        rw [coinMeasure_inter p hAX (determined_good D t u v).compl (disjoint_past_good D t u v),
          coinMeasure_inter p hAX' (determined_good D t v u).compl (disjoint_past_good D t v u),
          hgc u v huv, hgc v u huv.symm]
    _ = (1 - goodProb p D) * coinMeasure p A := by
        rw [← add_mul, measure_inter_add_sdiff _ (determined_atLeast t u v).measurableSet, mul_comm]

/-- After `k` windows: `P(u, v both leaders in round k(2D+3)) ≤ (1 - Q)^k`. -/
theorem both_le (hconn : G.Connected) (hW : ∀ v, (init v).phase = .W) (p : I) {D : ℕ}
    (hD : ∀ a b, G.dist a b ≤ D) {u v : V} (huv : u ≠ v) (k : ℕ) :
    coinMeasure p (Both G init (k * (2 * D + 3)) u v) ≤ (1 - goodProb p D) ^ k := by
  induction k with
  | zero => simpa using prob_le_one
  | succ k ih =>
    rw [add_mul, one_mul, pow_succ, mul_comm _ (1 - goodProb p D)]
    exact (both_step hconn hW p hD huv _).trans (mul_le_mul_right ih _)

variable (G init) in
/-- Definition 1 from round `T` on: a single fixed node is the only leader in every round `t ≥ T`. -/
def UniqueFrom (T : ℕ) (ω : ℕ × V → Bool) : Prop :=
  ∃ u, ∀ t, T ≤ t → ∀ w, (exec G init (field ω) t w).leader = true ↔ w = u

/-- **Tail bound.** `P(no unique leader from round k(2D+3) on) ≤ n²·(1 - Q)^k`. -/
theorem not_uniqueFrom_le (hconn : G.Connected) (hI : GoodInit init) (p : I) {D : ℕ}
    (hD : ∀ a b, G.dist a b ≤ D) (k : ℕ) :
    coinMeasure p {ω | ¬ UniqueFrom G init (k * (2 * D + 3)) ω} ≤
      (Fintype.card V : ℝ≥0∞) ^ 2 * (1 - goodProb p D) ^ k := by
  classical
  have hsub : {ω | ¬ UniqueFrom G init (k * (2 * D + 3)) ω} ⊆
      ⋃ x : V × V, if x.1 = x.2 then ∅ else Both G init (k * (2 * D + 3)) x.1 x.2 := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_iUnion, not_exists] at hn
    refine hω (unique_forever hI fun a b ha hb => ?_)
    by_contra hab
    have := hn (a, b)
    simp only [hab, ↓reduceIte] at this
    exact this ⟨ha, hb⟩
  calc _ ≤ ∑ x : V × V, coinMeasure p (if x.1 = x.2 then ∅ else Both G init (k * (2 * D + 3)) x.1 x.2) :=
        (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _x : V × V, (1 - goodProb p D) ^ k := by
        gcongr with x
        split_ifs with h
        · simp
        · exact both_le hconn hI.waiting p hD h k
    _ = _ := by simp [Fintype.card_prod, sq]

end MinimalistLE
