import Papers.PODC2020.MISInapproxCongest.IndepSet
import Podc.Computability.Distributed.Congest.MultiParty

/-!
# Approximate MaxIS in CONGEST and the reduction to promise pairwise disjointness

* Definition 5 (corrected): `IsApprox γ G w I` — `I` is independent and `w(I) ≥ γ · OPT`.
* A randomized CONGEST algorithm (`Cslib.Congest.Algorithm V (ℕ × ρ) σ B`: node input = its weight
  and its private random string; output bit = membership in the independent set) *finds a
  `γ`-approximation with error `≤ ε` in `T` rounds* (`ApproxMIS`) if on every vertex-weighted graph
  on `V` (weights `≤ |V|`) the fraction of random strings on which the output is not a `γ`-approximation is `≤ ε`.
* `corollary1_protocol`: on a `t`-party family of lower bound graphs whose MaxIS value is `≥ lo`
  when the strings share an element and `≤ hi` when they are pairwise disjoint, with
  `hi < γ · lo`, such an algorithm yields a private-coin blackboard protocol for promise pairwise
  disjointness with error `≤ 1/3` and `≤ T · |Ecut| · B + t ⌈log₂ (|V| W + 1)⌉` bits.
* `corollary1`: **Corollary 1**, combining this with the Chakrabarti–Khot–Sun bound (hypothesis).
-/

namespace Podc.MISInapproxCongest

open Finset Cslib.Congest Cslib.CommunicationComplexity

section Defs

variable {V σ ρ : Type*} [Fintype V] [DecidableEq V] {B : ℕ}

/-- **Definition 5** (with the evident correction `w(I) ≥ γ · OPT`; the paper writes
`w(I) ≥ OPT / γ`, which is impossible for `γ < 1` unless `OPT = 0`). -/
def IsApprox (γ : ℝ) (G : SimpleGraph V) (w : V → ℕ) (I : Finset V) : Prop :=
  IsIndep G I ∧ γ * opt G w ≤ wsum w I

/-- The set of nodes that output `true` after `T` rounds, with weights `w` and random strings `r`. -/
def outSet (A : Algorithm V (ℕ × ρ) σ B) (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℕ)
    (r : V → ρ) (T : ℕ) : Finset V :=
  univ.filter fun v => A.out v (A.run G (fun v => (w v, r v)) T v) = true

variable [Fintype ρ]

/-- Number of random strings on which the output is not a `γ`-approximation. -/
noncomputable def failCount (A : Algorithm V (ℕ × ρ) σ B) (γ : ℝ) (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : V → ℕ) (T : ℕ) : ℕ := by
  classical
  exact (univ.filter fun r : V → ρ => ¬IsApprox γ G w (outSet A G w r T)).card

/-- On the weighted graph `(G, w)`, the algorithm outputs a `γ`-approximate MaxIS after `T` rounds
with probability `≥ 1 - ε` (over the uniform random strings of the nodes). -/
def ApproxOn (A : Algorithm V (ℕ × ρ) σ B) (γ : ℝ) (T : ℕ) (ε : ℝ) (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : V → ℕ) : Prop :=
  (failCount A γ G w T : ℝ) ≤ ε * Fintype.card (V → ρ)

/-- The algorithm finds a `γ`-approximation of maximum (vertex-)weighted independent set within
`T` rounds with success probability `≥ 1 - ε`, on every graph with node set `V` and node weights
in `{0, …, n}`, `n = |V|` (weights of `O(log n)` bits, as in the paper's hard instances; with
unbounded weights no algorithm with bounded `T · B` could exist). -/
def ApproxMIS (A : Algorithm V (ℕ × ρ) σ B) (γ : ℝ) (T : ℕ) (ε : ℝ) : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℕ), (∀ v, w v ≤ Fintype.card V) →
    ApproxOn A γ T ε G w

end Defs

section Reduction

variable {V σ ρ : Type*} [Fintype V] [DecidableEq V] [Fintype ρ] [Nonempty ρ] {B t : ℕ}
  {K : Type*} [Fintype K]

/-- **Corollary 1, simulation part.** A randomized algorithm finding `γ`-approximate MaxIS on the
graphs of a `t`-party family (`t ≥ 2`) with a MaxIS gap `[hi, lo]`, `hi < γ lo`, gives a
private-coin blackboard protocol for promise pairwise disjointness with error `≤ 1/3` and
`T · |Ecut| · B + t ⌈log₂ (|V| W + 1)⌉` bits (`W` bounds the weights). -/
theorem corollary1_protocol (F : MPFamily (Fin t) (fun _ => K → Bool) V ℕ)
    [∀ x, DecidableRel (F.G x).Adj] (ht : 2 ≤ t) (lo hi W : ℕ) (γ : ℝ)
    (hlo : ∀ x, CommonElement x → ∃ I, IsIndep (F.G x) I ∧ lo ≤ wsum (F.inp x) I)
    (hhi : ∀ x, PairwiseDisjoint x → ∀ I, IsIndep (F.G x) I → wsum (F.inp x) I ≤ hi)
    (hgap : (hi : ℝ) < γ * lo) (hW : ∀ x v, F.inp x v ≤ W)
    (A : Algorithm V (ℕ × ρ) σ B) (T : ℕ)
    (hA : ∀ x, ApproxOn A γ T (1 / 3) (F.G x) (F.inp x)) :
    ∃ P : BBProtocol (fun i => (K → Bool) × ({v // F.part v = i} → ρ)) Bool,
      P.RandComputes (fun x => PairwiseDisjoint x ∨ UniquelyIntersecting x)
        (fun x => decide (PairwiseDisjoint x)) (1 / 3) ∧
      P.CostLE (T * (F.Ecut.card * B) + t * Nat.clog 2 (Fintype.card V * W + 1)) := by
  classical
  set x₀ : Fin t → K → Bool := fun _ _ => false
  -- player `i`'s summary: the weight of its nodes in the output set
  let sumI : Fin t → (K → Bool) → (V → σ) → ℕ := fun i xi s =>
    ∑ v ∈ (univ.filter fun v => A.out v (s v) = true).filter (fun v => F.part v = i),
      F.inp (Function.update x₀ i xi) v
  have hsum_le : ∀ i xi s, sumI i xi s < Fintype.card V * W + 1 := by
    intro i xi s
    refine Nat.lt_succ_of_le ((sum_le_sum fun v _ => hW _ v).trans ?_)
    rw [sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ ((card_le_card (filter_subset _ _)).trans
      ((card_le_card (filter_subset _ _)).trans (card_le_univ _)))
  let g : ∀ i, (K → Bool) → (V → σ) → Fin (Fintype.card V * W + 1) := fun i xi s =>
    ⟨sumI i xi s, hsum_le i xi s⟩
  have hg : ∀ i xi (s s' : V → σ), (∀ v, F.part v = i → s v = s' v) → g i xi s = g i xi s' := by
    intro i xi s s' h
    refine Fin.ext ?_
    simp only [g, sumI]
    congr 1
    ext v
    simp only [mem_filter, mem_univ, true_and]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by simpa [h v h2] using h1, h2⟩
  obtain ⟨P, hc, hP⟩ := F.rand_simulation (S := Fin (Fintype.card V * W + 1)) A T g
    (fun vals => decide (∑ i, (vals i : ℕ) ≤ hi)) hg
  refine ⟨P, fun x hx => ?_, by simpa using hc⟩
  -- the protocol outputs "the output set weighs `≤ hi`"
  have hΦ : ∀ r, P.eval (fun i => (x i, r i)) =
      decide (wsum (F.inp x) (outSet A (F.G x) (F.inp x) (F.combine r) T) ≤ hi) := by
    intro r
    rw [hP x r]
    congr 2
    simp only [g, sumI, wsum, outSet]
    rw [← sum_fiberwise (univ.filter fun v => A.out v
      (A.run (F.G x) (fun v => (F.inp x v, F.combine r v)) T v) = true) F.part]
    refine sum_congr rfl fun i _ => sum_congr rfl fun v hv => ?_
    refine F.inp_local _ _ v ?_
    rw [(mem_filter.1 hv).2]
    simp
  rw [F.errCount_eq_of_eval P _ x
    (fun r => decide (wsum (F.inp x) (outSet A (F.G x) (F.inp x) r T) ≤ hi)) hΦ]
  rw [Fintype.card_congr (F.combineEquiv (ρ := ρ))]
  refine le_trans ?_ (hA x)
  unfold failCount
  refine Nat.cast_le.2 (card_le_card fun r hr => ?_)
  simp only [mem_filter, mem_univ, true_and] at hr ⊢
  rintro ⟨hind, happ⟩
  apply hr
  rcases hx with hpd | hui
  · simp only [hpd, decide_true, decide_eq_true_eq]
    exact hhi x hpd _ hind
  · have hnpd : ¬PairwiseDisjoint x := by
      obtain ⟨m, hm, -⟩ := hui
      intro h
      have := h ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff]) m (hm _)
      rw [hm] at this
      exact Bool.noConfusion this
    simp only [hnpd, decide_false, decide_eq_false_iff_not, not_le]
    obtain ⟨I, hI, hlI⟩ := hlo x hui.commonElement
    have h1 : (lo : ℝ) ≤ opt (F.G x) (F.inp x) := by exact_mod_cast hlI.trans (le_opt hI)
    have hγ : 0 ≤ γ := by
      by_contra hneg
      push Not at hneg
      have : γ * lo ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le (Nat.cast_nonneg _)
      linarith [Nat.cast_nonneg (α := ℝ) hi]
    have : (hi : ℝ) < wsum (F.inp x) (outSet A (F.G x) (F.inp x) r T) :=
      lt_of_lt_of_le hgap ((mul_le_mul_of_nonneg_left h1 hγ).trans happ)
    exact_mod_cast this

/-- **Corollary 1.** Under the Chakrabarti–Khot–Sun bound `PPDLowerBound c`, if a `t`-party family
(`t ≥ 2`) of lower bound graphs for promise pairwise disjointness of `k`-bit strings has a MaxIS gap
`hi < γ · lo`, then every randomized CONGEST algorithm with `B`-bit messages finding a
`γ`-approximate MaxIS with probability `≥ 2/3` on the graphs of the family within `T` rounds
satisfies `c k / (t log₂ t) ≤ T · |Ecut| · B + t ⌈log₂ (|V| W + 1)⌉`, i.e.
`T = Ω(k / (t log t · |cut| · B))`. -/
theorem corollary1 {V σ ρ : Type} [Fintype V] [DecidableEq V] [Fintype ρ] [Nonempty ρ] {B t : ℕ}
    {K : Type} [Fintype K] {c : ℝ} (hCC : PPDLowerBound c)
    (F : MPFamily (Fin t) (fun _ => K → Bool) V ℕ)
    [∀ x, DecidableRel (F.G x).Adj] (ht : 2 ≤ t) (lo hi W : ℕ) (γ : ℝ)
    (hlo : ∀ x, CommonElement x → ∃ I, IsIndep (F.G x) I ∧ lo ≤ wsum (F.inp x) I)
    (hhi : ∀ x, PairwiseDisjoint x → ∀ I, IsIndep (F.G x) I → wsum (F.inp x) I ≤ hi)
    (hgap : (hi : ℝ) < γ * lo) (hW : ∀ x v, F.inp x v ≤ W)
    (A : Algorithm V (ℕ × ρ) σ B) (T : ℕ)
    (hA : ∀ x, ApproxOn A γ T (1 / 3) (F.G x) (F.inp x)) :
    c * Fintype.card K / (t * Real.logb 2 t) ≤
      ((T * (F.Ecut.card * B) + t * Nat.clog 2 (Fintype.card V * W + 1) : ℕ) : ℝ) := by
  obtain ⟨P, hP, hc⟩ := corollary1_protocol F ht lo hi W γ hlo hhi hgap hW A T hA
  exact hCC t ht K _ P _ hP hc

end Reduction

end Podc.MISInapproxCongest
