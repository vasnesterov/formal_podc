import Papers.PODC2019.CoveringPrimalDual.Compute
import Papers.PODC2019.CoveringPrimalDual.Rounds
import Papers.PODC2019.CoveringPrimalDual.ILP

/-!
# Concrete executions of Algorithm MWHVC and counterexamples

Using the rational mirror (`Compute.lean`) we certify concrete executions by `decide +kernel`:

* `Stuck.lemma_4_7_false`: Lemma 4.7 ("for every vertex `v` and level `ℓ(v)`, the number of
  `v`-stuck iterations is bounded by `α`") fails for the non-integral `α = 29/10`: a vertex is stuck
  three times at level 1. (The correct bound is `⌈α⌉`, `lemma_4_7_ceil`; asymptotically harmless.)
* `Eq1.claim_4_2_eq1_false`: Eq. (1) of Claim 4.2 fails for a vertex that terminated without
  joining `C` (it holds for active vertices, `claim_4_2`).
* `Cor410.corollary_4_10_false`: `ε = 1/(nW)` does not turn the `(f+ε)`-approximation into an
  `f`-approximation (one edge, weights `9, 10`: cost `19 > 2 · 9`).
* `ILPCex.claim_5_7_false`: the covering-ILP algorithm of Section 5 (Claim 5.6 → Lemma 5.2 →
  MWHVC) is not an `(f + ε)`-approximation with `f = f(A)` (the number of variables per
  constraint), as claimed in Claim 5.7 and in the abstract/introduction: on `min x s.t. x ≥ 2`
  (`f(A) = 1`) with `ε = 1/4` it outputs `x = 3`, cost `3 > (1 + 1/4) · 2`. The reduction raises
  the rank to `f(A) · ⌈log₂ M + 1⌉ = 2`, and MWHVC only guarantees that rank `+ ε`.
* `Degree57.claim_5_7_degree_false`: the maximum degree `2^{f(A)} · M · Δ(A)` used in Claim 5.7 is
  exceeded (`x₁ + x₂ ≥ 8`: degree `36 > 32`).
-/

set_option linter.unusedSectionVars false

namespace Podc.CoveringPrimalDual

open Finset Cslib.Hypergraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Two rational states with the same components. -/
def StateQ.Eqv (s t : StateQ V E) : Prop :=
  s.C = t.C ∧ (∀ v, s.level v = t.level v) ∧ (∀ e, s.deal e = t.deal e) ∧ ∀ e, s.δ e = t.δ e

instance (s t : StateQ V E) : Decidable (s.Eqv t) := by unfold StateQ.Eqv; infer_instance

theorem StateQ.Eqv.toReal_eq {s t : StateQ V E} (h : s.Eqv t) : s.toReal = t.toReal := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [StateQ.toReal, h1, funext h2, funext h3, funext h4]

/-- A run certified state by state. -/
theorem run_eq_of_chain (I : InstQ V E) (P : ParamsQ) (S : ℕ → StateQ V E) (n : ℕ)
    (h0 : (initQ I P).Eqv (S 0))
    (hstep : ∀ i < n, FuelOK I P (S i) ∧ (stepQ I P (S i)).Eqv (S (i + 1))) :
    ∀ i ≤ n, run I.toReal P.toReal i = (S i).toReal := by
  intro i hi
  induction i with
  | zero => rw [← h0.toReal_eq]; exact init_castS I P
  | succ i ih =>
    show step _ _ (run _ _ i) = _
    rw [ih (by omega), step_castS I P _ (hstep i (by omega)).1, (hstep i (by omega)).2.toReal_eq]

/-! ### Lemma 4.7 with a non-integral `α` -/

namespace Stuck

/-- Vertices `0, 1` with weights `1, 7`; edges `{1}, {0,1}, {1}, {0,1}, {0,1}`. -/
def I : InstQ (Fin 2) (Fin 5) :=
  ⟨![{1}, {0, 1}, {1}, {0, 1}, {0, 1}], ![1, 7], by decide, by decide⟩

/-- `f = 2`, `ε = 1/2`, `α = 29/10`, `κ = 1`, `c₀ = 1/2` (Section 3). -/
def P : ParamsQ := ⟨2, 1 / 2, 29 / 10, 1, 1 / 2⟩

/-- The states at the end of iterations `0, …, 5`. -/
def S : ℕ → StateQ (Fin 2) (Fin 5)
  | 0 => ⟨∅, ![0, 0], ![7/10, 1/6, 7/10, 1/6, 1/6], ![7/10, 1/6, 7/10, 1/6, 1/6]⟩
  | 1 => ⟨∅, ![0, 0], ![7/10, 1/6, 7/10, 1/6, 1/6], ![7/5, 1/3, 7/5, 1/3, 1/3]⟩
  | 2 => ⟨{0}, ![0, 1], ![7/20, 1/6, 7/20, 1/6, 1/6], ![7/4, 1/3, 7/4, 1/3, 1/3]⟩
  | 3 => ⟨{0}, ![0, 1], ![7/20, 1/6, 7/20, 1/6, 1/6], ![21/10, 1/3, 21/10, 1/3, 1/3]⟩
  | 4 => ⟨{0}, ![0, 1], ![7/20, 1/6, 7/20, 1/6, 1/6], ![49/20, 1/3, 49/20, 1/3, 1/3]⟩
  | _ => ⟨{0, 1}, ![0, 1], ![7/20, 1/6, 7/20, 1/6, 1/6], ![49/20, 1/3, 49/20, 1/3, 1/3]⟩

theorem chain : ∀ i < 5, FuelOK I P (S i) ∧ (stepQ I P (S i)).Eqv (S (i + 1)) := by
  decide +kernel

theorem init_eqv : (initQ I P).Eqv (S 0) := by decide +kernel

theorem run_eq : ∀ i ≤ 5, run I.toReal P.toReal i = (S i).toReal :=
  run_eq_of_chain I P S 5 init_eqv chain

theorem valid : P.toReal.Valid I.toReal where
  f_pos := by norm_num [ParamsQ.toReal, P]
  rank_le := by
    intro e
    simp only [ParamsQ.toReal, P, InstQ.toReal_inc]
    revert e; decide
  ε_pos := by norm_num [ParamsQ.toReal, P]
  one_lt_α := by norm_num [ParamsQ.toReal, P]
  κ_pos := by norm_num [ParamsQ.toReal, P]
  κ_le := by norm_num [ParamsQ.toReal, P]
  c₀_pos := by norm_num [ParamsQ.toReal, P]
  c₀_le := by norm_num [ParamsQ.toReal, P]

theorem stuck_iff {i : ℕ} (hi : i ∈ Icc 1 5) :
    (StuckIter I.toReal P.toReal 1 i ∧ (run I.toReal P.toReal i).level 1 = 1) ↔
      (1 ≤ i ∧ I.toReal.Active (S i).C 1 ∧ ¬ RaiseQ I P (S (i - 1)) 1 ∧ (S i).level 1 = 1) := by
  obtain ⟨h1, h5⟩ := mem_Icc.1 hi
  unfold StuckIter
  rw [run_eq i h5, run_eq (i - 1) (by omega),
    raise_castS I P _ (chain (i - 1) (by omega)).1]
  simp only [StateQ.toReal, and_assoc]

/-- Lemma 4.7 claims at most `α` `v`-stuck iterations per level; with `α = 29/10`, vertex `1` is
stuck in iterations `2, 3, 4`, all at level `1`. -/
theorem lemma_4_7_false :
    P.toReal.Valid I.toReal ∧ P.toReal.α = 29 / 10 ∧ stuckCount I.toReal P.toReal 1 1 5 = 3 := by
  refine ⟨valid, by norm_num [ParamsQ.toReal, P], ?_⟩
  classical
  unfold stuckCount
  rw [filter_congr fun i hi => stuck_iff hi]
  decide +kernel

end Stuck

/-! ### Claim 4.2, Eq. (1) for vertices that terminated without joining `C` -/

namespace Eq1

/-- One edge `{0, 1}`, weights `4, 7`. -/
def I : InstQ (Fin 2) (Fin 1) := ⟨![{0, 1}], ![4, 7], by decide, by decide⟩

/-- `f = 2`, `ε = 1/2`, `α = 2`, `κ = 1`, `c₀ = 1/2`. -/
def P : ParamsQ := ⟨2, 1 / 2, 2, 1, 1 / 2⟩

/-- The states at the end of iterations `0, 1, 2`. -/
def S : ℕ → StateQ (Fin 2) (Fin 1)
  | 0 => ⟨∅, ![0, 0], ![2], ![2]⟩
  | 1 => ⟨∅, ![0, 0], ![2], ![4]⟩
  | _ => ⟨{0}, ![0, 0], ![2], ![4]⟩

theorem chain : ∀ i < 2, FuelOK I P (S i) ∧ (stepQ I P (S i)).Eqv (S (i + 1)) := by
  decide +kernel

theorem run_eq : ∀ i ≤ 2, run I.toReal P.toReal i = (S i).toReal :=
  run_eq_of_chain I P S 2 (by decide +kernel) chain

/-- Claim 4.2 states Eq. (1) "for every `i ≥ 1` and every vertex `v ∉ C`". It fails for a vertex
that terminates without joining `C` (all its edges got covered): here vertex `1` terminates in
iteration `2` with level `0`, but `∑_{e ∈ E(1)} δ_1(e) = 4 > (1 - 2^{-1}) · 7`. (Eq. (1) holds for
the vertices that are still active, `claim_4_2`, which is all the proof uses.) -/
theorem claim_4_2_eq1_false :
    (1 : Fin 2) ∉ (run I.toReal P.toReal 2).C ∧
      ¬ I.toReal.load (run I.toReal P.toReal 1).δ 1 ≤
        (1 - (1 / 2 : ℝ) ^ ((run I.toReal P.toReal 2).level 1 + 1)) * I.toReal.w 1 := by
  rw [run_eq 2 le_rfl, run_eq 1 (by norm_num)]
  refine ⟨by decide, ?_⟩
  simp [StateQ.toReal, S, I, InstQ.toReal, Inst.load, Cslib.Hypergraph.load, edgesAt]
  norm_num

end Eq1

/-! ### Corollary 4.10: `ε = 1/(nW)` does not give an `f`-approximation -/

namespace Cor410

/-- Three parallel edges `{0, 1}` (so `Δ = 3`, the paper's assumption), weights `9, 10`. -/
def I : InstQ (Fin 2) (Fin 3) := ⟨fun _ => {0, 1}, ![9, 10], by decide, by decide⟩

/-- `f = 2`, `ε = 1/(nW) = 1/(2 · 10/9) = 9/20`, `α = 2`, `κ = 1`, `c₀ = 1/2`. -/
def P : ParamsQ := ⟨2, 9 / 20, 2, 1, 1 / 2⟩

/-- The states at the end of iterations `0, 1, 2`. -/
def S : ℕ → StateQ (Fin 2) (Fin 3)
  | 0 => ⟨∅, ![0, 0], ![3/2, 3/2, 3/2], ![3/2, 3/2, 3/2]⟩
  | 1 => ⟨∅, ![0, 0], ![3/2, 3/2, 3/2], ![3, 3, 3]⟩
  | _ => ⟨univ, ![0, 0], ![3/2, 3/2, 3/2], ![3, 3, 3]⟩

theorem chain : ∀ i < 2, FuelOK I P (S i) ∧ (stepQ I P (S i)).Eqv (S (i + 1)) := by
  decide +kernel

theorem run_eq : ∀ i ≤ 2, run I.toReal P.toReal i = (S i).toReal :=
  run_eq_of_chain I P S 2 (by decide +kernel) chain

/-- Corollary 4.10 sets `ε = 1/(nW)` with `W = max w / min w` and concludes that the
`(f+ε)`-approximation is an `f`-approximation. Here `n = 2`, `W = 10/9`, `ε = 9/20`, `f = 2`: the
algorithm terminates after two iterations with `C = {0, 1}` of weight `19 > f · w({0}) = 18`.
(Integrality only gives an `f`-approximation for `ε < 1/(n · max w)`.) -/
theorem corollary_4_10_false :
    P.toReal.ε = 1 / (2 * ((10 : ℝ) / 9)) ∧ Terminated I.toReal P.toReal 2 ∧
      (run I.toReal P.toReal 2).C = univ ∧ IsCover I.toReal.inc {0} ∧
      ∑ v ∈ (run I.toReal P.toReal 2).C, I.toReal.w v = 19 ∧
      (P.toReal.f : ℝ) * ∑ v ∈ ({0} : Finset (Fin 2)), I.toReal.w v = 18 := by
  have hC : (run I.toReal P.toReal 2).C = univ := by rw [run_eq 2 le_rfl]; rfl
  refine ⟨by norm_num [ParamsQ.toReal, P], fun e => ⟨0, by simp [I, InstQ.toReal], by
    rw [hC]; exact mem_univ _⟩, hC, fun e => ⟨0, by simp [I, InstQ.toReal], mem_singleton_self _⟩,
    ?_, ?_⟩
  · rw [hC]; simp [I, InstQ.toReal, Fin.sum_univ_two]; norm_num
  · simp [I, InstQ.toReal, ParamsQ.toReal, P]; norm_num

end Cor410

/-! ### Claim 5.7: the approximation ratio for covering ILPs -/

namespace ILPCex

open ILP

/-- The covering ILP `min x s.t. x ≥ 2`. -/
def A : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
/-- Right-hand side `b = 2`. -/
def b : Fin 1 → ℝ := fun _ => 2
/-- Weight `w = 1`. -/
def w : Fin 1 → ℝ := fun _ => 1

/-- The hypergraph produced by Lemma 5.2 from the binary expansion (Claim 5.6, two bits
`x = x₀ + 2 x₁`): vertices are the bits `(0, ℓ)`, with weights `2^ℓ`; edges `{x₀, x₁}` and `{x₁}`.
-/
def I : InstQ (Fin 1 × Fin 2) (Fin 2) :=
  ⟨![{(0, 0), (0, 1)}, {(0, 1)}], fun p => 2 ^ (p.2 : ℕ), by decide, by decide⟩

/-- `f = 2` (the rank of the hypergraph), `ε = 1/4`, `α = 2`, `κ = 1`, `c₀ = 1/2`. -/
def P : ParamsQ := ⟨2, 1 / 4, 2, 1, 1 / 2⟩

/-- The states at the end of iterations `0, 1, 2`. -/
def S : ℕ → StateQ (Fin 1 × Fin 2) (Fin 2)
  | 0 => ⟨∅, fun _ => 0, ![1/2, 1/2], ![1/2, 1/2]⟩
  | 1 => ⟨∅, fun _ => 0, ![1/2, 1/2], ![1, 1]⟩
  | _ => ⟨univ, fun _ => 0, ![1/2, 1/2], ![1, 1]⟩

theorem chain : ∀ i < 2, FuelOK I P (S i) ∧ (stepQ I P (S i)).Eqv (S (i + 1)) := by
  decide +kernel

theorem run_eq : ∀ i ≤ 2, run I.toReal P.toReal i = (S i).toReal :=
  run_eq_of_chain I P S 2 (by decide +kernel) chain

theorem valid : P.toReal.Valid I.toReal where
  f_pos := by norm_num [ParamsQ.toReal, P]
  rank_le := by
    intro e
    simp only [ParamsQ.toReal, P, InstQ.toReal_inc]
    revert e; decide
  ε_pos := by norm_num [ParamsQ.toReal, P]
  one_lt_α := by norm_num [ParamsQ.toReal, P]
  κ_pos := by norm_num [ParamsQ.toReal, P]
  κ_le := by norm_num [ParamsQ.toReal, P]
  c₀_pos := by norm_num [ParamsQ.toReal, P]
  c₀_le := by norm_num [ParamsQ.toReal, P]

/-- The hypergraph `I` is exactly the reduction of Lemma 5.2 applied to the binary expansion of
Claim 5.6 with `B = 2` bits. -/
theorem edges_eq : univ.image I.inc = redEdges (binExp A 2) b := by
  have hsupp : supp (binExp A 2) 0 = univ := by
    ext p; simp [mem_supp, binExp, A]
  ext e
  rw [mem_redEdges]
  constructor
  · intro he
    obtain ⟨k, -, rfl⟩ := mem_image.1 he
    fin_cases k
    · refine ⟨0, ∅, by norm_num [b], ?_⟩
      rw [hsupp]; decide
    · refine ⟨0, {(0, 0)}, by norm_num [binExp, A, b], ?_⟩
      rw [hsupp]; decide
  · rintro ⟨i, S, hS, rfl⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [hsupp]
    have hS1 : ((0 : Fin 1), (1 : Fin 2)) ∉ S := by
      intro hm
      have := single_le_sum (f := fun p => binExp A 2 0 p) (fun p _ => by
        simp [binExp, A]) hm
      simp only [binExp, A, b, mul_one] at this hS
      norm_num at this
      linarith
    have hsub : S ⊆ {((0 : Fin 1), (0 : Fin 2))} := by
      intro p hp
      rw [mem_singleton]
      obtain ⟨j, ℓ⟩ := p
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      fin_cases ℓ
      · rfl
      · exact absurd hp hS1
    rcases subset_singleton_iff.1 hsub with rfl | rfl
    · exact mem_image.2 ⟨0, mem_univ _, by decide⟩
    · exact mem_image.2 ⟨1, mem_univ _, by decide⟩

/-- The weights of `I` are those of the binary expansion (`w'_{j,ℓ} = 2^ℓ w_j`). -/
theorem weights_eq (p : Fin 1 × Fin 2) : I.toReal.w p = binW w 2 p := by
  simp [I, binW, w, InstQ.toReal]

/-- `M = 2`, `B = ⌈log₂ M + 1⌉ = 2` bits, `f(A) = 1`. -/
theorem params_eq : IsM A b 2 ∧ ⌈Real.logb 2 2 + 1⌉₊ = 2 ∧ fA A = 1 := by
  refine ⟨⟨fun i j _ => by norm_num [A, b], 0, 0, by norm_num [A], by norm_num [A, b]⟩, ?_, ?_⟩
  · rw [Real.logb_self_eq_one (by norm_num)]; norm_num
  · unfold fA
    have : ∀ i, (supp A i).card = 1 := fun i => by
      rw [card_eq_one]; exact ⟨0, by ext j; simp [mem_supp, A, Fin.fin_one_eq_zero j]⟩
    simp [this]

/-- Claim 5.7 (and the abstract/introduction: "an `(f+ε)`-approximate integral solution ... where `f`
bounds the number of variables in a constraint") is false for the paper's algorithm: on
`min x s.t. x ≥ 2` (`f(A) = 1`, optimum `2`), Algorithm MWHVC with `ε = 1/4` on the reduced
hypergraph terminates after two iterations with the cover `{x₀, x₁}`, i.e. `x = 3`, of cost
`3 > (f(A) + ε) · 2 = 5/2`. -/
theorem claim_5_7_false :
    Terminated I.toReal P.toReal 2 ∧ decode (run I.toReal P.toReal 2).C = (fun _ => 3) ∧
      Feasible A b (fun _ => 2) ∧ cost w (fun _ => 2) = 2 ∧
      cost w (decode (run I.toReal P.toReal 2).C) = 3 ∧
      (fA A + P.toReal.ε) * cost w (fun _ => 2) < cost w (decode (run I.toReal P.toReal 2).C) := by
  have hC : (run I.toReal P.toReal 2).C = univ := by rw [run_eq 2 le_rfl]; rfl
  have hdec : decode (run I.toReal P.toReal 2).C = fun _ => 3 := by
    rw [hC]; funext j; revert j; decide
  have hfA := params_eq.2.2
  refine ⟨?_, hdec, fun i => by norm_num [A, b], by norm_num [cost, w], ?_, ?_⟩
  · intro e
    rw [hC]
    obtain ⟨v, hv⟩ := I.inc_nonempty e
    exact ⟨v, hv, mem_univ v⟩
  · rw [hdec]; norm_num [cost, w]
  · rw [hdec, hfA]; norm_num [cost, w, ParamsQ.toReal, P]

end ILPCex

end Podc.CoveringPrimalDual

namespace Podc.CoveringPrimalDual.Degree57

open Finset ILP

variable {R J : Type*} [Fintype R] [Fintype J] [DecidableEq J]

/-- Computable version of the support of a rational row. -/
def suppQ (A : R → J → ℚ) (i : R) : Finset J := univ.filter fun j => A i j ≠ 0

/-- Computable version of the reduction of Lemma 5.2 for rational data. -/
def redEdgesQ (A : R → J → ℚ) (b : R → ℚ) : Finset (Finset J) :=
  univ.biUnion fun i =>
    ((univ : Finset (Finset J)).filter fun S => ∑ j ∈ S, A i j < b i).image fun S => suppQ A i \ S

theorem redEdges_cast (A : R → J → ℚ) (b : R → ℚ) :
    redEdges (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) = redEdgesQ A b := by
  have hs : ∀ i, supp (fun i j => (A i j : ℝ)) i = suppQ A i := fun i => by
    ext j; simp [mem_supp, suppQ]
  ext e
  rw [mem_redEdges]
  simp only [redEdgesQ, mem_biUnion, mem_univ, true_and, mem_image, mem_filter, hs]
  constructor
  · rintro ⟨i, S, h, rfl⟩; exact ⟨i, S, by exact_mod_cast h, rfl⟩
  · rintro ⟨i, S, h, rfl⟩; exact ⟨i, S, by exact_mod_cast h, rfl⟩

/-- The constraint `x₁ + x₂ ≥ 8`. -/
def A : Fin 1 → Fin 2 → ℝ := fun _ _ => 1
/-- Right-hand side `8`. -/
def b : Fin 1 → ℝ := fun _ => 8

/-- The proof of Claim 5.7 computes the degree of the final hypergraph as
`Δ_HVC ≤ 2^{f_ILP (1 + log M)} Δ_ILP = 2^{f_ILP} · 2M · Δ_ILP` and the statement of Claim 5.7 uses
`2^{f(A)} · M · Δ(A)`; both are wrong (`2^{f(1 + log M)} = (2M)^f`). For `x₁ + x₂ ≥ 8`
(`f(A) = 2`, `Δ(A) = 1`, `M = 8`, `B = ⌈log₂ M + 1⌉ = 4` bits), the hypergraph of Lemma 5.2 for
the binary expansion has a vertex (the highest bit of `x₁`) of degree `36 > 2^{f(A)} · M · Δ(A) = 32`.
-/
theorem claim_5_7_degree_false :
    IsM A b 8 ∧ ⌈Real.logb 2 8 + 1⌉₊ = 4 ∧ fA A = 2 ∧ ΔA A = 1 ∧
      ((redEdges (binExp A 4) b).filter (((0 : Fin 2), (3 : Fin 4)) ∈ ·)).card = 36 ∧
      2 ^ fA A * 8 * ΔA A < 36 := by
  have hf : fA A = 2 := by
    unfold fA
    have : ∀ i, (supp A i).card = 2 := fun i => by
      rw [show supp A i = univ by ext j; simp [mem_supp, A]]; rfl
    simp [this]
  have hΔ : ΔA A = 1 := by
    unfold ΔA
    have : ∀ j : Fin 2, (univ.filter fun i : Fin 1 => A i j ≠ 0).card = 1 := fun j => by
      rw [show (univ.filter fun i : Fin 1 => A i j ≠ 0) = univ by ext i; simp [A]]; rfl
    simp only [this]
    exact sup_const univ_nonempty 1
  have hred : redEdges (binExp A 4) b =
      redEdgesQ (fun (_ : Fin 1) (p : Fin 2 × Fin 4) => ((2 : ℚ) ^ (p.2 : ℕ))) (fun _ => 8) := by
    rw [← redEdges_cast]
    congr 1
    funext i p; simp [binExp, A]
  refine ⟨⟨fun i j _ => by norm_num [A, b], 0, 0, by norm_num [A], by norm_num [A, b]⟩, ?_, hf,
    hΔ, ?_, by rw [hf, hΔ]; norm_num⟩
  · rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  · rw [hred]; decide +kernel

end Podc.CoveringPrimalDual.Degree57
