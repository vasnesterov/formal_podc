import Papers.PODC2022.DominatingSetArboricity.Deterministic
import Cslib.Computability.Distributed.Local.Identifiers
import Cslib.Computability.Distributed.Local.OnlineLocalLocality

/-!
# Distributed implementation of the deterministic algorithm (Theorem 1.1, round complexity)

We implement the algorithm of Theorem 1.1 in CSLib's synchronous locally-iterative model
(`Cslib.LocallyIterative.Algorithm`): in every round each node replaces its state by a function of
the round number, its own state and the *set* of states of its neighbours. States carry the node's
identifier, so the set of neighbour states determines the multiset of neighbour values.

Global knowledge (as assumed in the paper): `Δ` (an upper bound used to initialise packing values;
we instantiate it with the maximum degree), `ε`, and the number of iterations `r` (a function of `Δ`,
`α`, `ε`). Local input: the node's weight.

Rounds (`T = 2r + 2` in total):
* round `0`: compute `τ_v` (minimum weight in `N⁺_v`), a node `pick_v ∈ N⁺_v` of weight `τ_v`, and
  `x_v = τ_v/(Δ+1)`;
* rounds `2i+1`, `2i+2` (`i < r`): iteration `i` of Lemma 4.1 — first `X_v` is computed and `v`
  joins `S` if `X_v ≥ w_v/(1+ε)`; then `v` learns whether it is dominated and, if not, multiplies
  `x_v` by `1+ε`;
* round `2r+1`: `v` joins the output if it is in `S` or was picked by an undominated node of `N⁺_v`.

Every message is the sender's state: an identifier, a weight, `τ`, an identifier, a packing value
`x = τ (1+ε)^j/(Δ+1)` with `j ≤ r` (`Inv`), and three bits — i.e. `O(1)` numbers of the input size
(we do not formalize bit complexity).

Main result: `run_out_eq_detDS` — after `2r+2` rounds the set of nodes with `out = True` is exactly
`detDS G α ε w`; together with `theorem_1_1` and `numIter_detLam_le` this gives Theorem 1.1:
a deterministic `(2α+1)(1+ε)`-approximation in `2r+2 = O(log(Δ/α)/ε)` rounds (`distributed_theorem_1_1`).
-/

set_option linter.unusedSectionVars false

namespace DominatingSetArboricity

open Finset SimpleGraph Cslib.LocallyIterative

/-- Local state of a node. -/
structure NState (V : Type*) where
  /-- identifier -/
  id : V
  /-- weight (local input) -/
  w : ℝ
  /-- `τ_v` -/
  tau : ℝ
  /-- a minimum-weight dominator of the node -/
  pick : V
  /-- packing value -/
  x : ℝ
  /-- in the partial dominating set `S` -/
  inS : Prop
  /-- dominated by `S` -/
  dom : Prop
  /-- in the final output -/
  out : Prop

variable {V : Type*}

/-- Round 0: compute `τ`, `pick`, initial packing value. -/
noncomputable def initStep (Δ : ℕ) (s : NState V) (N : Set (NState V)) : NState V :=
  haveI : Nonempty V := ⟨s.id⟩
  let τ := sInf (NState.w '' insert s N)
  { s with tau := τ, pick := Classical.epsilon fun u => ∃ t ∈ insert s N, t.id = u ∧ t.w = τ,
           x := τ / (Δ + 1), inS := False, dom := False, out := False }

/-- First round of an iteration: compute `X_v` and possibly join `S`. -/
noncomputable def stepA (ε : ℝ) (s : NState V) (N : Set (NState V)) : NState V :=
  { s with inS := s.inS ∨ s.w / (1 + ε) ≤ s.x + ∑ᶠ t ∈ N, t.x }

open scoped Classical in
/-- Second round of an iteration: learn domination, raise the packing value if undominated. -/
noncomputable def stepB (ε : ℝ) (s : NState V) (N : Set (NState V)) : NState V :=
  { s with dom := s.inS ∨ ∃ t ∈ N, t.inS,
           x := if s.inS ∨ ∃ t ∈ N, t.inS then s.x else s.x * (1 + ε) }

/-- Final round: join the output if in `S` or picked by an undominated node of `N⁺_v`. -/
def stepC (s : NState V) (N : Set (NState V)) : NState V :=
  { s with out := s.inS ∨ (¬ s.dom ∧ s.pick = s.id) ∨ ∃ t ∈ N, ¬ t.dom ∧ t.pick = s.id }

/-- The distributed algorithm with parameters `Δ`, `ε` and `r` iterations. -/
noncomputable def alg (Δ r : ℕ) (ε : ℝ) : Algorithm (NState V) :=
  ⟨fun t s N =>
    if t = 0 then initStep Δ s N
    else if t ≤ 2 * r then (if t % 2 = 1 then stepA ε s N else stepB ε s N)
    else if t = 2 * r + 1 then stepC s N else s⟩

/-- Initial configuration: identifiers and weights. -/
def c0 (w : V → ℝ) : V → NState V := fun v => ⟨v, w v, 0, v, 0, False, False, False⟩

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The configuration encoding a state of the centralized procedure. -/
noncomputable def enc (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ) (p : PState V) :
    V → NState V :=
  fun v => ⟨v, w v, tau G w v, tauNode G w v, p.x v, v ∈ p.S, v ∈ dom G p.S, False⟩

theorem X_eq (x : V → ℝ) (v : V) : X G x v = x v + ∑ u ∈ G.neighborFinset v, x u := by
  rw [X, cnbr_eq_insert, sum_insert (by simp)]

theorem initStep_c0 (w : V → ℝ) (v : V) :
    initStep G.maxDegree (c0 w v) (nbrColors G (c0 w) v) = enc G w (runP G 0 w 0) v := by
  have hτ : sInf (NState.w '' insert (c0 w v) (nbrColors G (c0 w) v)) = tau G w v := by
    rw [insert_nbrColors, ← coe_cnbr, Set.image_image, tau, Finset.inf'_eq_csInf_image]
    rfl
  simp only [initStep, hτ, enc, runP, Function.iterate_zero, id, init]
  congr 1
  · congr 1
    funext u
    apply propext
    rw [insert_nbrColors, ← coe_cnbr]
    simp only [Set.mem_image, mem_coe]
    constructor
    · rintro ⟨_, ⟨u', hu', rfl⟩, rfl, h⟩; exact ⟨hu', h⟩
    · rintro ⟨hu, h⟩; exact ⟨c0 w u, ⟨u, hu, rfl⟩, rfl, h⟩
  all_goals simp [mem_dom]

theorem stepA_enc {ε : ℝ} (w : V → ℝ) (p : PState V) (v : V) :
    stepA ε (enc G w p v) (nbrColors G (enc G w p) v) =
      { enc G w p v with inS := v ∈ (iter G ε w p).S } := by
  simp only [stepA, enc, iter, finsum_nbrColors (c := enc G w p) NState.id (fun u => rfl), X_eq]
  congr 1
  simp

theorem stepB_half {ε : ℝ} (w : V → ℝ) (p : PState V) (v : V) :
    stepB ε ({ enc G w p v with inS := v ∈ (iter G ε w p).S })
      (nbrColors G (fun u => { enc G w p u with inS := u ∈ (iter G ε w p).S }) v) =
      enc G w (iter G ε w p) v := by
  have hd : (v ∈ (iter G ε w p).S ∨ ∃ t ∈ nbrColors G
      (fun u => { enc G w p u with inS := u ∈ (iter G ε w p).S }) v, t.inS) ↔
      v ∈ dom G (iter G ε w p).S := by
    rw [exists_mem_nbrColors, mem_dom]
    simp only [mem_cnbr]
    constructor
    · rintro (h | ⟨u, hu, h⟩)
      · exact ⟨v, h, Or.inl rfl⟩
      · exact ⟨u, h, Or.inr hu⟩
    · rintro ⟨u, h, rfl | hu⟩
      · exact Or.inl h
      · exact Or.inr ⟨u, hu, h⟩
  simp only [stepB]
  simp only [enc]
  congr 1
  swap
  · exact propext hd
  · show _ = (if v ∈ dom G (iter G ε w p).S then p.x v else p.x v * (1 + ε))
    by_cases h : v ∈ dom G (iter G ε w p).S
    · rw [ite_eq_left h]; exact ite_eq_left (hd.2 h)
    · rw [ite_eq_right h]; exact ite_eq_right (fun h' => h (hd.1 h'))

/-- The run of the distributed algorithm simulates the centralized procedure: after `2i+1` rounds
(`i ≤ r`) the configuration encodes the state after `i` iterations. -/
theorem run_odd (w : V → ℝ) (ε : ℝ) (r : ℕ) :
    ∀ i ≤ r, (alg G.maxDegree r ε).run G (c0 w) (2 * i + 1) = enc G w (runP G ε w i) := by
  intro i
  induction i with
  | zero =>
    intro _
    funext v
    rw [Algorithm.run_succ_apply]
    exact initStep_c0 w v
  | succ i ih =>
    intro hi
    have h1 : (alg G.maxDegree r ε).run G (c0 w) (2 * i + 2) =
        fun u => { enc G w (runP G ε w i) u with inS := u ∈ (iter G ε w (runP G ε w i)).S } := by
      funext v
      rw [Algorithm.run_succ_apply, ih (by omega)]
      simp only [alg, show 2 * i + 1 ≠ 0 by omega, ite_false, show 2 * i + 1 ≤ 2 * r by omega,
        ite_true, show (2 * i + 1) % 2 = 1 by omega]
      exact stepA_enc w _ v
    funext v
    rw [show 2 * (i + 1) + 1 = (2 * i + 2) + 1 by ring, Algorithm.run_succ_apply, h1]
    simp only [alg, show 2 * i + 2 ≠ 0 by omega, ite_false, show 2 * i + 2 ≤ 2 * r by omega,
      ite_true, show (2 * i + 2) % 2 ≠ 1 by omega]
    rw [stepB_half, runP_succ]

/-- After the final round `2r+1`, the nodes with `out` are exactly `S ∪ completion S`. -/
theorem run_final (w : V → ℝ) (ε : ℝ) (r : ℕ) (v : V) :
    ((alg G.maxDegree r ε).run G (c0 w) (2 * r + 2) v).out ↔
      v ∈ (runP G ε w r).S ∪ completion G w (runP G ε w r).S := by
  rw [show 2 * r + 2 = (2 * r + 1) + 1 by ring, Algorithm.run_succ_apply, run_odd w ε r r le_rfl]
  simp only [alg, show 2 * r + 1 ≠ 0 by omega, ite_false, show ¬ 2 * r + 1 ≤ 2 * r by omega,
    ite_true, stepC, enc, exists_mem_nbrColors]
  simp only [mem_union, completion, mem_image, mem_filter, mem_univ, true_and]
  apply or_congr_right
  constructor
  · rintro (⟨h1, h2⟩ | ⟨u, _, h1, h2⟩)
    · exact ⟨v, h1, h2⟩
    · exact ⟨u, h1, h2⟩
  · rintro ⟨u, h1, rfl⟩
    rcases mem_cnbr.1 (tauNode_mem (G := G) w u) with h | h
    · rw [h]; exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨u, h.symm, h1, rfl⟩

open scoped Classical in
/-- The output of the distributed algorithm after `2r+2` rounds (with `r = numIter`) is `detDS`. -/
theorem run_out_eq_detDS (w : V → ℝ) (α : ℕ) (ε : ℝ) :
    (univ.filter fun v => ((alg G.maxDegree (numIter G ε (detLam α ε)) ε).run G (c0 w)
      (2 * numIter G ε (detLam α ε) + 2) v).out) = detDS G α ε w := by
  classical
  ext v
  rw [mem_filter, run_final]
  simp [detDS, partialDS]

/-- The algorithm is a `(2r+2)`-round LOCAL algorithm: the output of a node only depends on the
graph and the initial states (identifiers and weights) within distance `2r+2`. -/
theorem alg_isLocal (Δ r : ℕ) (ε : ℝ) :
    Cslib.Local.IsLocal (2 * r + 2) fun G (s₀ : V → NState V) v =>
      (alg Δ r ε).run G s₀ (2 * r + 2) v :=
  Algorithm.run_isLocal _ _

open scoped Classical in
/-- **Theorem 1.1** (distributed form). On a graph with an orientation of out-degree `≤ α`
(`α ≥ 1`, e.g. arboricity `≤ α`), with nonnegative weights and `0 < ε ≤ 1`, the deterministic
synchronous algorithm `alg Δ r ε` with `r = numIter G ε (detLam α ε)` outputs after
`T = 2r + 2 ≤ 4 + 4 log(max 1 ((Δ+1)/(2α+1)))/ε` rounds a dominating set (`out = True`) whose
weight is at most `(2α+1)(1+ε)` times the weight of any dominating set. -/
theorem distributed_theorem_1_1 {α : ℕ} (o : G.OutOrientation α) (hα : 1 ≤ α) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let r := numIter G ε (detLam α ε)
    let D' := univ.filter fun v => ((alg G.maxDegree r ε).run G (c0 w) (2 * r + 2) v).out
    IsDominating G D' ∧ (∀ D, IsDominating G D → wt w D' ≤ (2 * α + 1) * (1 + ε) * wt w D) ∧
      ((2 * r + 2 : ℕ) : ℝ) ≤ 4 + 4 * Real.log (max 1 ((G.maxDegree + 1) / (2 * α + 1))) / ε := by
  intro r D'
  have hD' : D' = detDS G α ε w := run_out_eq_detDS w α ε
  rw [hD']
  refine ⟨(theorem_1_1 o hα hw hε).1, (theorem_1_1 o hα hw hε).2, ?_⟩
  have := numIter_detLam_le (G := G) (α := α) hε hε1
  have hr : (r : ℝ) = numIter G ε (detLam α ε) := rfl
  have h4 : 4 * Real.log (max 1 ((G.maxDegree + 1) / (2 * α + 1))) / ε =
      2 * (2 * Real.log (max 1 ((G.maxDegree + 1) / (2 * α + 1))) / ε) := by ring
  push_cast
  linarith

end DominatingSetArboricity
