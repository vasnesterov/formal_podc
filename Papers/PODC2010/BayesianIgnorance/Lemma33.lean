import Papers.PODC2010.BayesianIgnorance.UpperBounds

/-!
# Lemma 3.3: ignorance is bliss

Alon, Emek, Feldman, Tennenholtz, *Bayesian Ignorance* (PODC 2010), Lemma 3.3: there are `k`-agent
Bayesian NCS games on directed `Θ(k)`-vertex graphs with `worst-eq^P(G) / best-eq^C(G) = O(1/log k)`.

The graph `G_k` (Anshelevich et al.): vertices `x`, `z`, `y_1, …, y_{k-1}`; edges `(x, y_i)` of cost
`1/i`, `(x, z)` of cost `1 + ε`, and `(z, y_i)` of cost `0`. Agents `1, …, k-1` (here `some j`,
`j : Fin n`, `n = k - 1`) go from `x` to `y_i`; agent `k` (here `none`) goes from `x` to `z` or
stays at `x` (destination `x`), with probability `1/2` each.

* `worstEqP_le`: every Bayesian equilibrium has social cost `≤ 1 + ε` (all agents share `(x, z)`),
  provided `ε (2n + 1) < 1`. The paper leaves `ε` unspecified; some smallness is needed: agent `i`
  joins `(x, z)` only if `ε < 1/(2i + 1)`.
* `half_hnum_le_bestEqC`: when agent `k` stays at `x`, the unique equilibrium cost of the underlying
  game is `H(k-1)`, so `best-eq^C(G) ≥ H(k-1)/2`.
* `lemma_3_3`: the asymptotic statement.
-/

open Finset Cslib.GameTheory Cslib.GameTheory.BayesianGame
open scoped ENNReal NNReal

namespace Podc.BayesianIgnorance.Lemma33

/-- Vertices of `G_k`. -/
inductive Vx (n : ℕ) where
  | x
  | z
  | y (j : Fin n)
  deriving DecidableEq, Fintype

/-- Edges of `G_k`. -/
inductive Ex (n : ℕ) where
  | xz
  | xy (j : Fin n)
  | zy (j : Fin n)
  deriving DecidableEq, Fintype

variable {n : ℕ}

/-- Endpoints of the directed edges. -/
def ends : Ex n → Vx n × Vx n
  | .xz => (.x, .z)
  | .xy j => (.x, .y j)
  | .zy j => (.z, .y j)

/-- Edge costs: `(x, y_{j+1})` costs `1/(j+1)`, `(x, z)` costs `1 + ε`, `(z, y_j)` costs `0`. -/
noncomputable def ecost (ε : ℝ≥0) : Ex n → ℝ≥0
  | .xz => 1 + ε
  | .xy j => ((j : ℝ≥0) + 1)⁻¹
  | .zy _ => 0

/-- The directed network `G_k` (with `k = n + 1`). -/
noncomputable def net (n : ℕ) (ε : ℝ≥0) : Network (Vx n) (Ex n) := Network.directed ends (ecost ε)

/-- The two states: agent `k` (`none`) goes to `z` (`b = true`) or stays at `x` (`b = false`). -/
def state (n : ℕ) (b : Bool) : Option (Fin n) → Vx n × Vx n
  | none => (.x, if b then .z else .x)
  | some j => (.x, .y j)

/-- The common prior: both states with probability `1/2`. -/
noncomputable def prior (n : ℕ) : PMF (Option (Fin n) → Vx n × Vx n) :=
  (PMF.uniformOfFintype Bool).map (state n)

/-- The Bayesian NCS game of Lemma 3.3. -/
noncomputable abbrev game (n : ℕ) (ε : ℝ≥0) := (net n ε).bayesGame (prior n)

/-! ### Connectivity in `G_k` -/

lemma step_iff {ε : ℝ≥0} {e : Ex n} {u v : Vx n} : (net n ε).step e u v ↔ ends e = (u, v) :=
  Iff.rfl

lemma reach {ε : ℝ≥0} {F : Finset (Ex n)} {w : Vx n} (h : (net n ε).Connects F .x w) :
    w = .x ∨ (w = .z ∧ Ex.xz ∈ F) ∨ ∃ j, w = .y j ∧ (Ex.xy j ∈ F ∨ (Ex.xz ∈ F ∧ Ex.zy j ∈ F)) := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hst ih =>
    obtain ⟨e, he, hs⟩ := hst
    rw [step_iff] at hs
    cases e with
    | xz =>
      simp only [ends, Prod.mk.injEq] at hs
      exact Or.inr (Or.inl ⟨hs.2.symm, he⟩)
    | xy j =>
      simp only [ends, Prod.mk.injEq] at hs
      exact Or.inr (Or.inr ⟨j, hs.2.symm, Or.inl he⟩)
    | zy j =>
      simp only [ends, Prod.mk.injEq] at hs
      obtain ⟨h1, h2⟩ := hs
      subst h1 h2
      rcases ih with h | h | ⟨j', h, -⟩
      · cases h
      · exact Or.inr (Or.inr ⟨j, rfl, Or.inr ⟨h.2, he⟩⟩)
      · cases h

lemma connects_y_iff {ε : ℝ≥0} {F : Finset (Ex n)} {j : Fin n} :
    (net n ε).Connects F .x (.y j) ↔ Ex.xy j ∈ F ∨ (Ex.xz ∈ F ∧ Ex.zy j ∈ F) := by
  constructor
  · intro h
    rcases reach h with h | h | ⟨j', h, h'⟩
    · cases h
    · cases h.1
    · cases h; exact h'
  · rintro (h | ⟨h1, h2⟩)
    · exact Relation.ReflTransGen.single ⟨_, h, rfl⟩
    · exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨_, h1, rfl⟩) ⟨_, h2, rfl⟩

lemma connects_z_iff {ε : ℝ≥0} {F : Finset (Ex n)} :
    (net n ε).Connects F .x .z ↔ Ex.xz ∈ F := by
  constructor
  · intro h
    rcases reach h with h | h | ⟨j', h, -⟩
    · cases h
    · exact h.2
    · cases h
  · intro h; exact Relation.ReflTransGen.single ⟨_, h, rfl⟩

/-! ### The prior -/

lemma prior_ne_zero {t : Option (Fin n) → Vx n × Vx n} (h : prior n t ≠ 0) :
    ∃ b, t = state n b := by
  have : t ∈ (prior n).support := h
  rw [prior, PMF.support_map] at this
  obtain ⟨b, -, hb⟩ := this
  exact ⟨b, hb.symm⟩

lemma prior_state_ne_zero (b : Bool) : prior n (state n b) ≠ 0 := by
  rw [← PMF.mem_support_iff, prior, PMF.support_map]
  exact ⟨b, by simp, rfl⟩

lemma sum_prior (g : (Option (Fin n) → Vx n × Vx n) → ℝ≥0∞) :
    ∑ t, prior n t * g t = 2⁻¹ * g (state n true) + 2⁻¹ * g (state n false) := by
  rw [prior, sum_map_mul]
  simp [PMF.uniformOfFintype_apply]

lemma exCost_eq (ε : ℝ≥0) (s : Option (Fin n) → Vx n × Vx n → Finset (Ex n))
    (i : Option (Fin n)) :
    (game n ε).exCost s i =
      2⁻¹ * (net n ε).agentCost (state n true) (play s (state n true)) i +
      2⁻¹ * (net n ε).agentCost (state n false) (play s (state n false)) i := by
  rw [exCost]
  exact sum_prior _

lemma reachable_of_prior {ε : ℝ≥0} (i : Option (Fin n)) (t : Option (Fin n) → Vx n × Vx n)
    (h : prior n t ≠ 0) : (net n ε).Reachable (t i).1 (t i).2 := by
  obtain ⟨b, rfl⟩ := prior_ne_zero h
  rcases i with _ | j
  · cases b
    · exact (net n ε).connects_refl _ _
    · exact connects_z_iff.2 (Finset.mem_univ _)
  · exact connects_y_iff.2 (Or.inl (Finset.mem_univ _))

/-! ### Bayesian equilibria: everybody shares `(x, z)` -/

section BayesEq

variable {ε : ℝ≥0} {s : Option (Fin n) → Vx n × Vx n → Finset (Ex n)}

lemma exCost_ne_top (hs : (game n ε).IsBayesEq s) (i : Option (Fin n)) :
    (game n ε).exCost s i ≠ ⊤ :=
  (net n ε).exCost_ne_top_of_isBayesEq (prior n) hs i fun t h => reachable_of_prior i t h

lemma connects_of_eq (hs : (game n ε).IsBayesEq s) (i : Option (Fin n)) (b : Bool) :
    (net n ε).Connects (s i (state n b i)) (state n b i).1 (state n b i).2 := by
  by_contra h
  apply exCost_ne_top hs i
  have h' := (net n ε).agentCost_of_not_connects (t := state n b) (a := play s (state n b)) h
  rw [exCost_eq]
  cases b
  · rw [h']; simp
  · rw [h']; simp

lemma cost_xy_pos (ε : ℝ≥0) (j : Fin n) : 0 < (net n ε).cost (Ex.xy j) := by
  show 0 < ((j : ℝ≥0) + 1)⁻¹
  positivity

lemma cost_xz_pos (ε : ℝ≥0) : 0 < (net n ε).cost (Ex.xz (n := n)) := by
  show 0 < 1 + ε
  positivity

/-- Agent `j` never buys an edge `(x, y_{j'})` with `j' ≠ j`. -/
lemma xy_not_mem_some (hs : (game n ε).IsBayesEq s) {j j' : Fin n} (h : j' ≠ j) :
    Ex.xy j' ∉ s (some j) (.x, .y j) := by
  intro he
  refine (net n ε).not_isBayesEq_of_removable hs (exCost_ne_top hs _) he (cost_xy_pos ε j') ?_
    (t₀ := state n true) rfl (prior_state_ne_zero true)
  have hc := connects_of_eq hs (some j) true
  simp only [state] at hc
  rw [connects_y_iff] at hc ⊢
  simp only [Finset.mem_erase, ne_eq, Ex.xy.injEq, reduceCtorEq, not_false_eq_true, true_and]
  rcases hc with hc | hc
  · exact Or.inl ⟨fun h' => h h'.symm, hc⟩
  · exact Or.inr hc

/-- Agent `k` never buys an edge `(x, y_j)`. -/
lemma xy_not_mem_none (hs : (game n ε).IsBayesEq s) (b : Bool) (j : Fin n) :
    Ex.xy j ∉ s none (state n b none) := by
  intro he
  refine (net n ε).not_isBayesEq_of_removable hs (exCost_ne_top hs _) he (cost_xy_pos ε j) ?_
    (t₀ := state n b) rfl (prior_state_ne_zero b)
  cases b
  · exact (net n ε).connects_refl _ _
  · have hc := connects_of_eq hs none true
    simp only [state, ite_true] at hc ⊢
    rw [connects_z_iff] at hc ⊢
    simp [hc]

/-- Agent `j` does not buy both `(x, y_j)` and `(x, z)`. -/
lemma not_both (hs : (game n ε).IsBayesEq s) (j : Fin n) :
    ¬ (Ex.xy j ∈ s (some j) (.x, .y j) ∧ Ex.xz ∈ s (some j) (.x, .y j)) := by
  rintro ⟨h1, h2⟩
  refine (net n ε).not_isBayesEq_of_removable hs (exCost_ne_top hs _) h2 (cost_xz_pos ε) ?_
    (t₀ := state n true) rfl (prior_state_ne_zero true)
  rw [connects_y_iff]
  exact Or.inl (Finset.mem_erase.2 ⟨by simp, h1⟩)

lemma play_some (b : Bool) (j : Fin n) :
    play s (state n b) (some j) = s (some j) (.x, .y j) := rfl

lemma play_none (b : Bool) : play s (state n b) none = s none (state n b none) := rfl

/-- Nobody but agent `j` buys `(x, y_j)`. -/
lemma loadOthers_xy (hs : (game n ε).IsBayesEq s) (b : Bool) (j : Fin n) :
    Network.loadOthers (play s (state n b)) (some j) (Ex.xy j) = 0 := by
  rw [Network.loadOthers, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro (_ | j') - ⟨hne, he⟩
  · exact xy_not_mem_none hs b j (by simpa [play_none] using he)
  · exact xy_not_mem_some hs (j := j') (j' := j) (fun h => hne (by rw [h])) he

lemma card_lt (j : Fin n) : #(Finset.univ.filter fun j' : Fin n => j' < j) = j := by
  have : (Finset.univ.filter fun j' : Fin n => j' < j) = Finset.Iio j := by ext; simp
  rw [this, Fin.card_Iio]

lemma real_ineq {ε : ℝ} {j : ℕ} (hε : ε * (2 * j + 3) < 1) :
    (1 + ε) / (j + 2) + (1 + ε) / (j + 1) < 1 / (j + 1) + 1 / (j + 1) := by
  rw [div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity)
    (by positivity), div_lt_div_iff₀ (by positivity) (by positivity)]
  have h := mul_lt_mul_of_pos_right hε (by positivity : (0:ℝ) < ((j:ℝ) + 1) ^ 2)
  nlinarith [h]

/-- Every agent `j` buys `(x, z)` in a Bayesian equilibrium (induction on `j`), provided
`ε (2n + 1) < 1`. -/
lemma xz_mem (hs : (game n ε).IsBayesEq s) (hε : (ε : ℝ) * (2 * n + 1) < 1) (j : Fin n) :
    Ex.xz ∈ s (some j) (.x, .y j) := by
  obtain ⟨j, hj⟩ := j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_contra hxz
    set jj : Fin n := ⟨j, hj⟩ with hjj
    have hxy : Ex.xy jj ∈ s (some jj) (.x, .y jj) := by
      rcases connects_y_iff.1 (connects_of_eq hs (some jj) true) with h | h
      · exact h
      · exact absurd h.1 hxz
    set b : Finset (Ex n) := {Ex.xz, Ex.zy jj}
    have hb : (net n ε).Connects b .x (.y jj) := connects_y_iff.2 (Or.inr ⟨by simp [b], by simp [b]⟩)
    have hdev := hs (some jj) (fun _ => b)
    rw [exCost_eq, exCost_eq] at hdev
    -- the current payments are at least `1/(j+1)` in both states
    have hcur : ∀ β : Bool, (net n ε).agentCost (state n β) (play s (state n β)) (some jj) =
        (net n ε).payment (play s (state n β)) (some jj) := fun β =>
      (net n ε).agentCost_of_connects (connects_of_eq hs (some jj) β)
    have hcur' : ∀ β : Bool, ((j : ℝ≥0) + 1)⁻¹ ≤ (net n ε).payment (play s (state n β)) (some jj) := by
      intro β
      rw [Network.payment_eq]
      refine le_trans ?_ (Finset.single_le_sum (f := fun e => (net n ε).cost e /
        ((Network.loadOthers (play s (state n β)) (some jj) e : ℝ≥0) + 1))
        (fun _ _ => zero_le) (show Ex.xy jj ∈ play s (state n β) (some jj) from hxy))
      rw [loadOthers_xy hs β jj]
      simp [net, Network.directed, ecost, jj]
    -- the deviation costs `(1+ε)/(ℓ+1)` with `ℓ` the number of other agents on `(x, z)`
    set lo : Bool → ℕ := fun β => Network.loadOthers (play s (state n β)) (some jj) Ex.xz
    have hdevc : ∀ β : Bool, (net n ε).agentCost (state n β)
        (play (Function.update s (some jj) fun _ => b) (state n β)) (some jj) =
        (((1 + ε) / ((lo β : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) := by
      intro β
      rw [play_update, (net n ε).agentCost_of_connects (by rw [Function.update_self]; exact hb),
        Network.payment_update, Finset.sum_pair (by simp)]
      simp [net, Network.directed, ecost, lo]
    have hlo : ∀ β : Bool, (j : ℝ≥0) + (if β then 1 else 0) ≤ lo β := by
      intro β
      have hsub : (if β then insert none ((Finset.univ.filter fun j' : Fin n => j' < jj).map
          Function.Embedding.some) else (Finset.univ.filter fun j' : Fin n => j' < jj).map
          Function.Embedding.some) ⊆
          Finset.univ.filter fun i => i ≠ some jj ∧ Ex.xz ∈ play s (state n β) i := by
        intro i hi
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hsome : ∀ j' : Fin n, j' < jj → some j' ≠ some jj ∧
            Ex.xz ∈ play s (state n β) (some j') := by
          intro j' hj'
          exact ⟨by simpa using hj'.ne, ih j'.1 hj' j'.2⟩
        cases β
        · simp only [Bool.false_eq_true, ite_false, Finset.mem_map, Finset.mem_filter,
            Finset.mem_univ, true_and, Function.Embedding.some_apply] at hi
          obtain ⟨j', hj', rfl⟩ := hi
          exact hsome j' hj'
        · simp only [ite_true, Finset.mem_insert, Finset.mem_map, Finset.mem_filter,
            Finset.mem_univ, true_and, Function.Embedding.some_apply] at hi
          rcases hi with rfl | ⟨j', hj', rfl⟩
          · refine ⟨by simp, ?_⟩
            have := connects_of_eq hs none true
            simp only [state, ite_true] at this
            exact connects_z_iff.1 this
          · exact hsome j' hj'
      have := Finset.card_le_card hsub
      have hc : #(Finset.univ.filter fun j' : Fin n => j' < jj) = j := card_lt jj
      cases β
      · simp only [Bool.false_eq_true, ↓reduceIte, Finset.card_map, hc] at this
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero, lo, Network.loadOthers]
        exact_mod_cast this
      · simp only [↓reduceIte] at this
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_map, hc] at this
        simp only [↓reduceIte, lo, Network.loadOthers]
        exact_mod_cast this
    rw [hcur, hcur, hdevc, hdevc, ← mul_add, ← mul_add, ← ENNReal.coe_add,
      ← ENNReal.coe_add] at hdev
    have hle : (net n ε).payment (play s (state n true)) (some jj) +
        (net n ε).payment (play s (state n false)) (some jj) ≤
        (1 + ε) / ((lo true : ℝ≥0) + 1) + (1 + ε) / ((lo false : ℝ≥0) + 1) := by
      have := (ENNReal.mul_le_mul_iff_right (by simp : (2:ℝ≥0∞)⁻¹ ≠ 0) (by simp)).1 hdev
      exact_mod_cast this
    have h1 := hcur' true
    have h2 := hcur' false
    have h3 := hlo true
    have h4 := hlo false
    simp only [↓reduceIte, Bool.false_eq_true, add_zero] at h3 h4
    have hR : (((j : ℝ≥0) + 1)⁻¹ : ℝ) + ((j : ℝ≥0) + 1)⁻¹ ≤
        (1 + (ε : ℝ)) / ((lo true : ℝ) + 1) + (1 + ε) / ((lo false : ℝ) + 1) := by
      have := add_le_add h1 h2
      have := this.trans hle
      exact_mod_cast this
    have h3' : (j : ℝ) + 2 ≤ (lo true : ℝ) + 1 := by
      have : (j : ℝ) + 1 ≤ lo true := by exact_mod_cast h3
      linarith
    have h4' : (j : ℝ) + 1 ≤ (lo false : ℝ) + 1 := by
      have : (j : ℝ) ≤ lo false := by exact_mod_cast h4
      linarith
    have hε' : (ε : ℝ) * (2 * j + 3) < 1 := by
      have : (2 * (j : ℝ) + 3) ≤ 2 * n + 1 := by
        have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
        linarith
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left this ε.2) hε
    have := real_ineq hε'
    have hd1 : (1 + (ε : ℝ)) / ((lo true : ℝ) + 1) ≤ (1 + ε) / (j + 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) h3'
    have hd2 : (1 + (ε : ℝ)) / ((lo false : ℝ) + 1) ≤ (1 + ε) / (j + 1) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) h4'
    push_cast at hR
    simp only [one_div] at this
    linarith

/-- In a Bayesian equilibrium the only positive-cost edge bought is `(x, z)`. -/
lemma mem_biUnion (hs : (game n ε).IsBayesEq s) (hε : (ε : ℝ) * (2 * n + 1) < 1) (β : Bool)
    {e : Ex n} (he : e ∈ Finset.univ.biUnion (play s (state n β))) :
    e = Ex.xz ∨ ∃ j, e = Ex.zy j := by
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 he
  cases e with
  | xz => exact Or.inl rfl
  | zy j => exact Or.inr ⟨j, rfl⟩
  | xy j' =>
    exfalso
    rcases i with _ | j
    · exact xy_not_mem_none hs β j' hi
    · by_cases h : j' = j
      · subst h; exact not_both hs j' ⟨hi, xz_mem hs hε j'⟩
      · exact xy_not_mem_some hs h hi

lemma socialCost_le (hs : (game n ε).IsBayesEq s) (hε : (ε : ℝ) * (2 * n + 1) < 1) :
    (game n ε).socialCost s ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) := by
  rw [socialCost_eq]
  simp only [Network.bayesGame_prior]
  rw [sum_prior]
  have hβ : ∀ β : Bool, (game n ε).stateCost (state n β) (play s (state n β)) ≤
      ((1 + ε : ℝ≥0) : ℝ≥0∞) := by
    intro β
    rw [(net n ε).stateCost_bayesGame_of_forall (prior n) (a := play s (state n β))
      (fun i => connects_of_eq hs i β)]
    rw [ENNReal.coe_le_coe, Network.totalCost]
    calc ∑ e ∈ Finset.univ.biUnion (play s (state n β)), (net n ε).cost e
        = ∑ e ∈ Finset.univ.biUnion (play s (state n β)), if Ex.xz = e then 1 + ε else 0 := by
          refine Finset.sum_congr rfl fun e he => ?_
          rcases mem_biUnion hs hε β he with rfl | ⟨j, rfl⟩
          · simp [net, Network.directed, ecost]
          · simp [net, Network.directed, ecost]
      _ ≤ 1 + ε := by
          rw [Finset.sum_ite_eq]
          split_ifs <;> simp
  calc 2⁻¹ * (game n ε).stateCost (state n true) (play s (state n true)) +
        2⁻¹ * (game n ε).stateCost (state n false) (play s (state n false))
      ≤ 2⁻¹ * ((1 + ε : ℝ≥0) : ℝ≥0∞) + 2⁻¹ * ((1 + ε : ℝ≥0) : ℝ≥0∞) := by
        gcongr <;> exact hβ _
    _ = ((1 + ε : ℝ≥0) : ℝ≥0∞) := by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

/-- Lemma 3.3, partial-information side: every Bayesian equilibrium has social cost at most
`1 + ε` (all agents share the edge `(x, z)`), if `ε (2n + 1) < 1`. -/
theorem worstEqP_le (hε : (ε : ℝ) * (2 * n + 1) < 1) :
    (game n ε).worstEqP ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) :=
  BayesianGame.worstEqP_le _ fun _ hs => socialCost_le hs hε

end BayesEq

/-! ### Nash equilibria of the underlying game where agent `k` stays at `x` -/

section Nash

variable {ε : ℝ≥0} {a : Option (Fin n) → Finset (Ex n)}

lemma nash_xz_not_mem_none (ha : (game n ε).IsNashEq (state n false) a) : Ex.xz ∉ a none :=
  fun he => (net n ε).not_isNashEq_of_removable ha he (cost_xz_pos ε) ((net n ε).connects_refl _ _)

lemma nash_xz_not_mem_some (hε0 : 0 < ε) (ha : (game n ε).IsNashEq (state n false) a)
    (hc : ∀ i, (net n ε).Connects (a i) (state n false i).1 (state n false i).2) (j : Fin n) :
    Ex.xz ∉ a (some j) := by
  intro hj
  set J := Finset.univ.filter fun j : Fin n => Ex.xz ∈ a (some j)
  have hJ : J.Nonempty := ⟨j, by simp [J, hj]⟩
  set m := J.max' hJ
  have hm : Ex.xz ∈ a (some m) := by simpa [J] using J.max'_mem hJ
  -- at most `m` other agents share `(x, z)` with agent `m`
  have hlo : Network.loadOthers a (some m) Ex.xz ≤ (m : ℕ) := by
    have hsub : (Finset.univ.filter fun i => i ≠ some m ∧ Ex.xz ∈ a i) ⊆
        (Finset.univ.filter fun j' : Fin n => j' < m).map Function.Embedding.some := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases i with _ | j'
      · exact absurd hi.2 (nash_xz_not_mem_none ha)
      · simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.some_apply, Option.some.injEq, exists_eq_right]
        have hle : j' ≤ m := J.le_max' j' (by simp [J, hi.2])
        exact lt_of_le_of_ne hle fun h => hi.1 (by rw [h])
    have := Finset.card_le_card hsub
    rwa [Finset.card_map, card_lt m] at this
  have hdev := ha (some m) {Ex.xy m}
  simp only [Network.bayesGame_cost] at hdev
  have hyc : (net n ε).Connects {Ex.xy m} Vx.x (Vx.y m) :=
    connects_y_iff.2 (Or.inl (Finset.mem_singleton_self _))
  rw [(net n ε).agentCost_of_connects (hc _),
    (net n ε).agentCost_of_connects (by rw [Function.update_self]; exact hyc),
    Network.payment_update, Finset.sum_singleton, Network.payment_eq] at hdev
  have hdev' := ENNReal.coe_le_coe.1 hdev
  have h1 : (1 + ε) / ((m : ℝ≥0) + 1) ≤ ∑ e ∈ a (some m), (net n ε).cost e /
      ((Network.loadOthers a (some m) e : ℝ≥0) + 1) := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun e => (net n ε).cost e /
      ((Network.loadOthers a (some m) e : ℝ≥0) + 1)) (fun _ _ => zero_le) hm)
    show (1 + ε) / ((m : ℝ≥0) + 1) ≤ (1 + ε) / ((Network.loadOthers a (some m) Ex.xz : ℝ≥0) + 1)
    gcongr
  have h2 : (net n ε).cost (Ex.xy m) / ((Network.loadOthers a (some m) (Ex.xy m) : ℝ≥0) + 1) ≤
      ((m : ℝ≥0) + 1)⁻¹ := by
    show ((m : ℝ≥0) + 1)⁻¹ / _ ≤ _
    exact div_le_self zero_le (by simp)
  have h3 : ((m : ℝ≥0) + 1)⁻¹ < (1 + ε) / ((m : ℝ≥0) + 1) := by
    rw [div_eq_mul_inv]
    exact lt_mul_of_one_lt_left (by positivity) (by simpa using hε0)
  exact absurd (h1.trans (hdev'.trans h2)) (not_le.2 h3)

lemma sum_inv_eq_hnum : ∑ j : Fin n, ((j : ℝ≥0) + 1)⁻¹ = hnum n := by
  rw [hnum, Fin.sum_univ_eq_sum_range (fun j => ((j : ℝ≥0) + 1)⁻¹) n]

/-- When agent `k` stays at `x`, every Nash equilibrium of the underlying game costs at least
`H(k-1)`: nobody shares `(x, z)` (the agent with the largest index on it would rather take her
direct edge), so every agent `j` buys her direct edge `(x, y_j)`. -/
lemma hnum_le_stateCost (hε0 : 0 < ε) (ha : (game n ε).IsNashEq (state n false) a) :
    (hnum n : ℝ≥0∞) ≤ (game n ε).stateCost (state n false) a := by
  by_cases hc : ∀ i, (net n ε).Connects (a i) (state n false i).1 (state n false i).2
  · rw [(net n ε).stateCost_bayesGame_of_forall (prior n) hc, ENNReal.coe_le_coe,
      Network.totalCost, ← sum_inv_eq_hnum]
    have hsub : Finset.univ.image (Ex.xy (n := n)) ⊆ Finset.univ.biUnion a := by
      intro e he
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 he
      refine Finset.mem_biUnion.2 ⟨some j, Finset.mem_univ _, ?_⟩
      rcases connects_y_iff.1 (hc (some j)) with h | h
      · exact h
      · exact absurd h.1 (nash_xz_not_mem_some hε0 ha hc j)
    refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
    rw [Finset.sum_image (fun _ _ _ _ h => by cases h; rfl)]
    rfl
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    rw [(net n ε).stateCost_bayesGame_of_not (prior n) hi]
    exact le_top

/-- Lemma 3.3, complete-information side: `best-eq^C(G) ≥ H(k-1)/2`. -/
theorem half_hnum_le_bestEqC (hε0 : 0 < ε) : 2⁻¹ * (hnum n : ℝ≥0∞) ≤ (game n ε).bestEqC := by
  rw [BayesianGame.bestEqC]
  simp only [Network.bayesGame_prior]
  rw [sum_prior]
  refine le_add_left ?_
  gcongr
  exact le_iInf₂ fun a ha => hnum_le_stateCost hε0 ha

end Nash

/-! ### `opt^C(G) = 1 + ε`: the worst Bayesian equilibrium is globally optimal -/

lemma hnum_two : hnum 2 = 3 / 2 := by
  rw [hnum_succ, hnum_one]; norm_num

/-- Every connecting action profile in either state costs at least `1 + ε` (if `n ≥ 2` and
`ε ≤ 1/2`): either `(x, z)` is bought, or all direct edges are, which cost `H(n) ≥ 3/2`. -/
lemma one_add_le_stateCost {ε : ℝ≥0} (hn : 2 ≤ n) (hε : ε ≤ 1 / 2) (β : Bool)
    (a : Option (Fin n) → Finset (Ex n)) :
    ((1 + ε : ℝ≥0) : ℝ≥0∞) ≤ (game n ε).stateCost (state n β) a := by
  by_cases hc : ∀ i, (net n ε).Connects (a i) (state n β i).1 (state n β i).2
  · rw [(net n ε).stateCost_bayesGame_of_forall (prior n) hc, ENNReal.coe_le_coe,
      Network.totalCost]
    by_cases hxz : Ex.xz ∈ Finset.univ.biUnion a
    · exact Finset.single_le_sum (f := fun e => (net n ε).cost e) (fun _ _ => zero_le) hxz
    · have hsub : Finset.univ.image (Ex.xy (n := n)) ⊆ Finset.univ.biUnion a := by
        intro e he
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 he
        refine Finset.mem_biUnion.2 ⟨some j, Finset.mem_univ _, ?_⟩
        rcases connects_y_iff.1 (hc (some j)) with h | h
        · exact h
        · exact absurd (Finset.mem_biUnion.2 ⟨some j, Finset.mem_univ _, h.1⟩) hxz
      refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
      rw [Finset.sum_image (fun _ _ _ _ h => by cases h; rfl)]
      change 1 + ε ≤ ∑ j : Fin n, ((j : ℝ≥0) + 1)⁻¹
      rw [sum_inv_eq_hnum]
      calc 1 + ε ≤ 1 + 1 / 2 := by gcongr
        _ = hnum 2 := by rw [hnum_two]; norm_num
        _ ≤ hnum n := hnum_mono hn
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    rw [(net n ε).stateCost_bayesGame_of_not (prior n) hi]
    exact le_top

/-- `opt^C(G) ≥ 1 + ε` (for `n ≥ 2`, `ε ≤ 1/2`). -/
theorem one_add_le_optC {ε : ℝ≥0} (hn : 2 ≤ n) (hε : ε ≤ 1 / 2) :
    ((1 + ε : ℝ≥0) : ℝ≥0∞) ≤ (game n ε).optC := by
  rw [BayesianGame.optC]
  simp only [Network.bayesGame_prior]
  rw [sum_prior]
  calc ((1 + ε : ℝ≥0) : ℝ≥0∞) = 2⁻¹ * ((1 + ε : ℝ≥0) : ℝ≥0∞) + 2⁻¹ * ((1 + ε : ℝ≥0) : ℝ≥0∞) := by
        rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    _ ≤ _ := by
        gcongr <;> exact le_iInf fun a => one_add_le_stateCost hn hε _ a

/-- "Ignorance is bliss" (Section 3 and the introduction of the paper): in the game of Lemma 3.3
the worst Bayesian equilibrium costs exactly the expected globally optimal cost,
`worst-eq^P(G) = opt^C(G) = 1 + ε`, while `best-eq^C(G) ≥ H(k-1)/2`. -/
theorem ignorance_is_bliss {ε : ℝ≥0} (hn : 2 ≤ n) (hε0 : 0 < ε)
    (hε : (ε : ℝ) * (2 * n + 1) < 1) :
    (game n ε).worstEqP = (game n ε).optC ∧ (game n ε).optC = ((1 + ε : ℝ≥0) : ℝ≥0∞) ∧
      2⁻¹ * (hnum n : ℝ≥0∞) ≤ (game n ε).bestEqC := by
  have hε2 : ε ≤ 1 / 2 := by
    have : (ε : ℝ) ≤ 1 / 2 := by
      have h5 : (5 : ℝ) ≤ 2 * n + 1 := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      nlinarith [ε.2]
    exact_mod_cast this
  obtain ⟨s, -, hs, -⟩ := exists_isBayesEq (net n ε) (prior n)
  have h1 := worstEqP_le hε
  have h2 := one_add_le_optC hn hε2
  have h3 : (game n ε).optC ≤ (game n ε).worstEqP :=
    ((game n ε).observation_2_2 ⟨s, hs⟩).1.trans
      (((game n ε).observation_2_2 ⟨s, hs⟩).2.1.trans ((game n ε).observation_2_2 ⟨s, hs⟩).2.2)
  refine ⟨le_antisymm (h1.trans h2) h3, le_antisymm (h3.trans h1) h2,
    half_hnum_le_bestEqC hε0⟩

/-- `G_k` has `k + 1` vertices. -/
def vxEquiv : Vx n ≃ Option (Option (Fin n)) where
  toFun
    | .x => none
    | .z => some none
    | .y j => some (some j)
  invFun
    | none => .x
    | some none => .z
    | some (some j) => .y j
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with _ | _ | _ <;> rfl

lemma card_vx : Fintype.card (Vx n) = n + 2 := by
  rw [Fintype.card_congr vxEquiv]; simp

/-- Lemma 3.3 of [Alon–Emek–Feldman–Tennenholtz 2010] ("ignorance is bliss"): for every `k₀` there
are `k ≥ k₀` and a `k`-agent Bayesian NCS game on a directed graph with `k + 1` vertices that has a
pure Bayesian equilibrium, finite `best-eq^C(G)` and satisfies
`worst-eq^P(G) / best-eq^C(G) ≤ 4 / ln k`, i.e. `ln k · worst-eq^P(G) ≤ 4 · best-eq^C(G)`; in particular the ratio is `O(1 / log k)`. -/
theorem lemma_3_3 (k₀ : ℕ) : ∃ k ≥ k₀, ∃ (n : ℕ) (ε : ℝ≥0),
    Fintype.card (Option (Fin n)) = k ∧ Fintype.card (Vx n) = k + 1 ∧
    (∃ s, (game n ε).IsBayesEq s) ∧ (game n ε).bestEqC ≠ ⊤ ∧
    ENNReal.ofReal (Real.log k) * (game n ε).worstEqP ≤ 4 * (game n ε).bestEqC := by
  set n := k₀ + 1
  set ε : ℝ≥0 := (4 * n + 2 : ℝ≥0)⁻¹
  have hε0 : 0 < ε := by positivity
  have hε : (ε : ℝ) * (2 * n + 1) < 1 := by
    simp only [ε, NNReal.coe_inv]
    push_cast
    rw [inv_mul_lt_iff₀ (by positivity)]
    linarith
  have hε1 : ε ≤ 1 := by
    simp only [ε]
    exact inv_le_one_of_one_le₀ (by
      have : (2 : ℝ≥0) ≤ 4 * n + 2 := by simp
      exact le_trans (by norm_num) this)
  obtain ⟨s, -, hs, -⟩ := exists_isBayesEq (net n ε) (prior n)
  have hW : (game n ε).worstEqP ≤ 2 := by
    refine (worstEqP_le hε).trans ?_
    have : (1 + ε : ℝ≥0) ≤ 2 := by
      calc (1 + ε : ℝ≥0) ≤ 1 + 1 := by gcongr
        _ = 2 := by norm_num
    exact_mod_cast this
  have hC : (game n ε).bestEqC ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (bestEqC_le_hnum_mul_bestEqP (net n ε) (prior n))
    refine ENNReal.mul_ne_top ENNReal.coe_ne_top (ne_top_of_le_ne_top (b := 2) (by simp) ?_)
    exact (BayesianGame.bestEqP_le_worstEqP _ hs).trans hW
  refine ⟨n + 1, by omega, n, ε, by simp, by rw [card_vx], ⟨s, hs⟩, hC, ?_⟩
  have hlog : ENNReal.ofReal (Real.log ((n + 1 : ℕ) : ℝ)) ≤ (hnum n : ℝ≥0∞) := by
    refine ENNReal.ofReal_le_of_le_toReal ?_
    rw [ENNReal.coe_toReal, coe_hnum]
    exact log_add_one_le_harmonic n
  calc ENNReal.ofReal (Real.log ((n + 1 : ℕ) : ℝ)) * (game n ε).worstEqP
      ≤ (hnum n : ℝ≥0∞) * 2 := by gcongr
    _ = 4 * (2⁻¹ * (hnum n : ℝ≥0∞)) := by
        rw [← mul_assoc, mul_comm (hnum n : ℝ≥0∞)]
        congr 1
        rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_assoc, ENNReal.mul_inv_cancel (by simp)
          (by simp), mul_one]
    _ ≤ 4 * (game n ε).bestEqC := by gcongr; exact half_hnum_le_bestEqC hε0

end Podc.BayesianIgnorance.Lemma33