import Papers.PODC2018.LocalISApproximation.Basic

/-!
# Boppana's algorithm and the Caro–Wei bound (§1, rule (2))

Boppana's algorithm: order the vertices by a uniformly random permutation and output the vertices
that precede all their neighbours. A permutation is a bijection `σ : V ≃ Fin n` (the rank of each
vertex); the uniform distribution is the counting measure on the `n!` such bijections.

* `boppana G σ`: the output; `boppana_isIndepSet`: it is independent.
* `card_boppana_mem`: `(d(v)+1) · #{σ | v ∈ boppana G σ} = n!` (each vertex of `N[v]` is equally
  likely to be the first one of `N[v]`).
* `expected_card_boppana`: `E[|boppana G σ|] = CaroWei(G)` (the paper's linearity-of-expectation
  argument).
* `caroWei_le_indepNum`: the Caro–Wei bound `α(G) ≥ CaroWei(G)` (eq. (1)), via a permutation whose
  output is at least the average.
-/

open Finset SimpleGraph

namespace Podc.LocalISApproximation

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Boppana's algorithm (rule (2) of the paper) for the ordering `σ`: the set of vertices that
precede all their neighbours. -/
def boppana (σ : V ≃ Fin (Fintype.card V)) : Finset V :=
  univ.filter fun v => ∀ u, G.Adj v u → σ v < σ u

variable {G}

omit [DecidableEq V] in
theorem mem_boppana {σ : V ≃ Fin (Fintype.card V)} {v : V} :
    v ∈ boppana G σ ↔ ∀ u, G.Adj v u → σ v < σ u := by
  simp [boppana]

omit [DecidableEq V] in
/-- The output of Boppana's algorithm is an independent set. -/
theorem boppana_isIndepSet (σ : V ≃ Fin (Fintype.card V)) :
    G.IsIndepSet (boppana G σ : Set V) := by
  intro v hv u hu _ hadj
  simp only [boppana, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv hu
  exact lt_asymm (hv u hadj) (hu v hadj.symm)

/-- In a nonempty finset, exactly one element has the minimal rank. -/
theorem card_filter_isMin {n : ℕ} (σ : V ≃ Fin n) {S : Finset V} (hS : S.Nonempty) :
    #(S.filter fun u => ∀ w ∈ S, w ≠ u → σ u < σ w) = 1 := by
  obtain ⟨u₀, hu₀, hmin⟩ := S.exists_min_image σ hS
  rw [Finset.card_eq_one]
  refine ⟨u₀, ?_⟩
  ext u
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hu, h⟩
    by_contra hne
    exact absurd (hmin u hu) (not_le.2 (h u₀ hu₀ (Ne.symm hne)))
  · rintro rfl
    refine ⟨hu₀, fun w hw hne => lt_of_le_of_ne (hmin w hw) ?_⟩
    intro h
    exact hne (σ.injective h).symm

/-- Swapping two vertices in the ordering. -/
def swapOrder {n : ℕ} (u v : V) : (V ≃ Fin n) ≃ (V ≃ Fin n) where
  toFun σ := (Equiv.swap u v).trans σ
  invFun σ := (Equiv.swap u v).trans σ
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp

/-- Each vertex of `N[v]` is the first one of `N[v]` in the same number of orderings. -/
theorem card_isMin_eq {n : ℕ} {S : Finset V} {u v : V} (hu : u ∈ S) (hv : v ∈ S) :
    #(univ.filter fun σ : V ≃ Fin n => ∀ w ∈ S, w ≠ u → σ u < σ w) =
      #(univ.filter fun σ : V ≃ Fin n => ∀ w ∈ S, w ≠ v → σ v < σ w) := by
  refine Finset.card_bij (fun σ _ => swapOrder u v σ) ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    intro w hw hwv
    simp only [swapOrder, Equiv.coe_fn_mk, Equiv.trans_apply, Equiv.swap_apply_right]
    by_cases hwu : w = u
    · subst hwu
      rw [Equiv.swap_apply_left]
      exact hσ v hv (Ne.symm hwv)
    · rw [Equiv.swap_apply_of_ne_of_ne hwu hwv]
      exact hσ w hw hwu
  · intro σ₁ _ σ₂ _ h
    exact (swapOrder u v).injective h
  · intro τ hτ
    refine ⟨swapOrder u v τ, ?_, (swapOrder u v).right_inv τ⟩
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    intro w hw hwu
    simp only [swapOrder, Equiv.coe_fn_mk, Equiv.trans_apply, Equiv.swap_apply_left]
    by_cases hwv : w = v
    · subst hwv
      rw [Equiv.swap_apply_right]
      exact hτ u hu (Ne.symm hwu)
    · rw [Equiv.swap_apply_of_ne_of_ne hwu hwv]
      exact hτ w hw hwv

/-- `(d(v)+1) · #{σ | v ∈ boppana G σ} = n!`: the probability that `v` is selected is
`1/(d(v)+1)`. -/
theorem card_boppana_mem (v : V) :
    (G.degree v + 1) * #(univ.filter fun σ : V ≃ Fin (Fintype.card V) => v ∈ boppana G σ) =
      (Fintype.card V).factorial := by
  set n := Fintype.card V
  set S := insert v (G.neighborFinset v) with hSdef
  have hvS : v ∈ S := mem_insert_self _ _
  have hS : #S = G.degree v + 1 := by
    rw [hSdef, card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]
  have hmem : ∀ σ : V ≃ Fin n, v ∈ boppana G σ ↔ ∀ w ∈ S, w ≠ v → σ v < σ w := by
    intro σ
    rw [mem_boppana]
    constructor
    · intro h w hw hne
      rcases mem_insert.1 hw with rfl | hw
      · exact absurd rfl hne
      · exact h w ((mem_neighborFinset _ _ _).1 hw)
    · intro h w hadj
      exact h w (mem_insert_of_mem ((mem_neighborFinset _ _ _).2 hadj)) hadj.ne'
  have htot : ∑ u ∈ S, #(univ.filter fun σ : V ≃ Fin n => ∀ w ∈ S, w ≠ u → σ u < σ w) =
      n.factorial := by
    have := Finset.sum_comm (s := S) (t := (univ : Finset (V ≃ Fin n)))
      (f := fun u σ => if ∀ w ∈ S, w ≠ u → σ u < σ w then 1 else 0)
    simp only [Finset.sum_boole, Nat.cast_id] at this
    rw [this]
    have h1 : ∀ σ : V ≃ Fin n, #(S.filter fun u => ∀ w ∈ S, w ≠ u → σ u < σ w) = 1 :=
      fun σ => card_filter_isMin σ ⟨v, hvS⟩
    simp only [h1, sum_const, card_univ, smul_eq_mul, mul_one]
    rw [Fintype.card_equiv (Fintype.equivFin V)]
  rw [Finset.sum_congr rfl fun u hu => card_isMin_eq (n := n) hu hvS, sum_const, smul_eq_mul,
    hS] at htot
  rw [← htot]
  congr 1
  congr 1
  ext σ
  simp [hmem σ]

/-- The expected size of the output of Boppana's algorithm under a uniformly random ordering is
exactly `CaroWei(G)` (§1 of the paper). -/
theorem expected_card_boppana :
    (∑ σ : V ≃ Fin (Fintype.card V), (#(boppana G σ) : ℝ)) / (Fintype.card V).factorial =
      caroWei G := by
  have hf : (0 : ℝ) < (Fintype.card V).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_eq_iff hf.ne', caroWei, Finset.sum_mul]
  have : ∀ σ : V ≃ Fin (Fintype.card V), (#(boppana G σ) : ℝ) =
      ∑ v, if v ∈ boppana G σ then (1 : ℝ) else 0 := by
    intro σ; rw [Finset.sum_boole]; simp
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_boole]
  have h := card_boppana_mem (G := G) v
  have hd : (0 : ℝ) < G.degree v + 1 := by positivity
  have h' : ((G.degree v : ℝ) + 1) *
      #(univ.filter fun σ : V ≃ Fin (Fintype.card V) => v ∈ boppana G σ) =
      (Fintype.card V).factorial := by exact_mod_cast h
  rw [div_mul_eq_mul_div, one_mul, eq_div_iff hd.ne', ← h']
  ring

/-- **Caro–Wei bound** (eq. (1)): `α(G) ≥ CaroWei(G)`. -/
theorem caroWei_le_indepNum : caroWei G ≤ G.indepNum := by
  have hf : (0 : ℝ) < (Fintype.card V).factorial := by exact_mod_cast Nat.factorial_pos _
  obtain ⟨σ, hσ⟩ : ∃ σ : V ≃ Fin (Fintype.card V), caroWei G ≤ #(boppana G σ) := by
    by_contra h
    push Not at h
    have hlt : ∑ σ : V ≃ Fin (Fintype.card V), (#(boppana G σ) : ℝ) <
        ∑ _σ : V ≃ Fin (Fintype.card V), caroWei G :=
      Finset.sum_lt_sum_of_nonempty ⟨Fintype.equivFin V, mem_univ _⟩ fun σ _ => h σ
    rw [sum_const, card_univ, Fintype.card_equiv (Fintype.equivFin V), nsmul_eq_mul,
      ← expected_card_boppana (G := G), mul_div_cancel₀ _ hf.ne'] at hlt
    exact lt_irrefl _ hlt
  exact hσ.trans (by exact_mod_cast (boppana_isIndepSet σ).card_le_indepNum)

end Podc.LocalISApproximation
