import Papers.PODC2018.LocalISApproximation.Basic
import Cslib.Computability.Distributed.PortNumbering.Basic

/-!
# Theorem 4: no 1-round algorithm beats ratio `(Δ+1)/2`

**Model** (§2.4 of the paper). Synchronous message passing in the port-numbering model of CSLib
(`Cslib.PortNumbering`): a node knows its degree, distinguishes its incident edges by port numbers,
and has as local input its unique label `ℓ v ∈ Fin N` and its private random string `r v ∈ R`. The
random strings are independent and identically distributed with an arbitrary distribution `μ` on a
finite set `R` (finite-precision randomness). A 1-round randomized algorithm is a deterministic
CSLib `Algorithm (Fin N × R) Bool` run for one round; the output is the set of nodes that output
`true`. Bandwidth and local computation are unlimited (messages and states of arbitrary types);
`n`, `Δ`, `N` are fixed, hence known to the algorithm.

**The argument.** Instead of the paper's `G₁ = K_{Δ+1}` (which has a different number of nodes
than any `Δ`-regular bipartite graph, and nodes know `n`), we use two graphs on the *same* node
set `V = Fin k × ZMod (Δ+1) × Bool` with the *same* port numbers at both ends of every edge:
port `i < Δ` of `(c, a, s)` leads to `(c, a+i+1, s)` in `G₁ = crown false` (`2k` disjoint copies of
`K_{Δ+1}`) and to `(c, a+i+1, ¬s)` in `G₂ = crown true` (`k` copies of `K_{Δ+1,Δ+1}` minus a perfect
matching, a `Δ`-regular bipartite graph). For each node `v` a permutation `flipOthers v` of the
nodes fixing `v` maps the `G₁`-neighbourhood of `v` onto its `G₂`-neighbourhood port by port, so the
1-round view of `v` in `G₂` under `(ℓ, r)` is its view in `G₁` under `(ℓ, r) ∘ flipOthers v`
(`eval_crown_true`). Averaging over all labelings and random strings (both invariant under
permutations of the nodes) every node joins with the same probability in `G₁` and `G₂`
(`sum_expectedSize_eq`); in `G₁` at most `2k` nodes join (one per clique), while
`α(G₂) ≥ k(Δ+1)`.

* `theorem4`: for every correct 1-round algorithm there are a `Δ`-regular bipartite
  port-numbered graph and a labeling with `(Δ+1) · E[|output|] ≤ 2 α(G)`.
* `theorem4_ratio`: hence a 1-round algorithm with performance ratio `ρ` on simple `Δ`-regular
  graphs has `ρ ≥ (Δ+1)/2` (Theorem 4 as stated).
* `boppanaAlg`, `boppanaAlg_correct`: non-vacuity — Boppana's rule with random ranks and labels as
  tie-breakers is a correct 1-round algorithm in this model.
-/

open Finset SimpleGraph Cslib.PortNumbering

namespace Podc.LocalISApproximation

/-! ### The model -/

section Model

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A simple `Δ`-regular port-numbered graph. -/
def IsRegularPN (G : PNGraph V) (Δ : ℕ) : Prop := G.IsSimple ∧ ∀ v, G.deg v = Δ

/-- The set of nodes that join the independent set when the 1-round algorithm `A` runs on `G`
with labels `ℓ` and random strings `r`. -/
def output {N : ℕ} {R : Type} (A : Algorithm (Fin N × R) Bool) (G : PNGraph V) (ℓ : V ↪ Fin N)
    (r : V → R) : Finset V :=
  univ.filter fun v => A.eval G 1 (fun u => (ℓ u, r u)) v = true

/-- `A` is correct on simple `Δ`-regular graphs with node set `V` when random strings are drawn
from `μ`: for every such graph and labeling it outputs an independent set for every outcome of
positive probability. -/
def IsCorrect {N : ℕ} {R : Type} (A : Algorithm (Fin N × R) Bool) (μ : R → ℝ) (V : Type)
    [Fintype V] [DecidableEq V] (Δ : ℕ) : Prop :=
  ∀ G : PNGraph V, IsRegularPN G Δ → ∀ (ℓ : V ↪ Fin N) (r : V → R), 0 < ∏ v, μ (r v) →
    G.toSimpleGraph.IsIndepSet (output A G ℓ r : Set V)

/-- The expected output size when every node draws its random string independently from the
distribution `μ` on the finite set `R`. -/
noncomputable def expectedSize {N : ℕ} {R : Type} [Fintype R] (μ : R → ℝ)
    (A : Algorithm (Fin N × R) Bool) (G : PNGraph V) (ℓ : V ↪ Fin N) : ℝ :=
  ∑ r : V → R, (∏ v, μ (r v)) * (#(output A G ℓ r) : ℝ)

omit [Fintype V] [DecidableEq V] in
/-- The output of a 1-round algorithm at `v` depends only on the inputs of `v` and its
neighbours, the degrees and the port numbers. -/
theorem eval_one {N : ℕ} {R : Type} (A : Algorithm (Fin N × R) Bool) (G : PNGraph V)
    (x : V → Fin N × R) (v : V) :
    A.eval G 1 x v = A.out (A.recv (A.init (G.deg v) (x v)) fun i =>
      if i < G.deg v then some (A.send (A.init (G.deg (G.nbr v i)) (x (G.nbr v i))) (G.rport v i))
      else none) := rfl

end Model

/-! ### The two graphs -/

/-- Node set of the construction: `k` blocks, each `ZMod (Δ+1) × Bool`. -/
abbrev CV (Δ k : ℕ) := Fin k × ZMod (Δ + 1) × Bool

/-- Port `i < Δ` of `(c, a, s)` leads to `(c, a+i+1, s xor flip)`. -/
def crownNbr (Δ k : ℕ) (flip : Bool) (v : CV Δ k) (i : ℕ) : CV Δ k :=
  if i < Δ then (v.1, v.2.1 + ((i + 1 : ℕ) : ZMod (Δ + 1)), xor v.2.2 flip) else v

theorem natCast_succ_ne_zero {Δ i : ℕ} (hi : i < Δ) : ((i + 1 : ℕ) : ZMod (Δ + 1)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

theorem natCast_succ_inj {Δ i j : ℕ} (hi : i < Δ) (hj : j < Δ)
    (h : ((i + 1 : ℕ) : ZMod (Δ + 1)) = ((j + 1 : ℕ) : ZMod (Δ + 1))) : i = j := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  omega

/-- `G₁ = crown false` (`2k` disjoint `K_{Δ+1}`) and `G₂ = crown true` (a `Δ`-regular bipartite
graph); in both, the edge behind port `i` has port `Δ-1-i` at the other end. -/
def crown (Δ k : ℕ) (flip : Bool) : PNGraph (CV Δ k) where
  deg _ := Δ
  p v i := (crownNbr Δ k flip v i, Δ - 1 - i)
  p_lt := by intro v i hi; dsimp only; omega
  p_p := by
    intro v i hi
    dsimp only at hi ⊢
    have h1 : Δ - 1 - i < Δ := by omega
    simp only [crownNbr, hi, h1, ite_true, Prod.mk.injEq]
    refine ⟨Prod.ext rfl (Prod.ext ?_ ?_), by omega⟩
    · dsimp only
      rw [add_assoc, ← Nat.cast_add, show i + 1 + (Δ - 1 - i + 1) = Δ + 1 by omega,
        ZMod.natCast_self, add_zero]
    · dsimp only; cases v.2.2 <;> cases flip <;> rfl

@[simp] theorem crown_deg (Δ k : ℕ) (flip : Bool) (v : CV Δ k) : (crown Δ k flip).deg v = Δ := rfl

theorem crown_nbr {Δ k : ℕ} {flip : Bool} (v : CV Δ k) {i : ℕ} (hi : i < Δ) :
    (crown Δ k flip).nbr v i = (v.1, v.2.1 + ((i + 1 : ℕ) : ZMod (Δ + 1)), xor v.2.2 flip) := by
  simp [PNGraph.nbr, crown, crownNbr, hi]

theorem crown_rport (Δ k : ℕ) (flip : Bool) (v : CV Δ k) (i : ℕ) :
    (crown Δ k flip).rport v i = Δ - 1 - i := rfl

theorem crown_isRegular (Δ k : ℕ) (flip : Bool) : IsRegularPN (crown Δ k flip) Δ := by
  refine ⟨⟨?_, ?_⟩, fun _ => rfl⟩
  · intro v i hi h
    rw [crown_nbr v hi] at h
    have := congrArg (fun w => w.2.1) h
    simp only [add_eq_left] at this
    exact natCast_succ_ne_zero hi this
  · intro v i j hi hj h
    rw [crown_nbr v hi, crown_nbr v hj] at h
    have := congrArg (fun w => w.2.1) h
    simp only [add_right_inj] at this
    exact natCast_succ_inj hi hj this

theorem crown_adj {Δ k : ℕ} {flip : Bool} {u w : CV Δ k} :
    (crown Δ k flip).toSimpleGraph.Adj u w ↔
      u ≠ w ∧ ∃ i < Δ, (u.1, u.2.1 + ((i + 1 : ℕ) : ZMod (Δ + 1)), xor u.2.2 flip) = w := by
  rw [PNGraph.toSimpleGraph_adj]
  simp only [crown_deg]
  constructor
  · rintro ⟨hne, i, hi, rfl⟩; exact ⟨hne, i, hi, (crown_nbr u hi).symm⟩
  · rintro ⟨hne, i, hi, rfl⟩; exact ⟨hne, i, hi, crown_nbr u hi⟩

/-- `G₂` is bipartite (2-coloured by the last coordinate). -/
theorem crown_true_colorable (Δ k : ℕ) : (crown Δ k true).toSimpleGraph.Colorable 2 := by
  refine ⟨Coloring.mk (fun v => if v.2.2 then (1 : Fin 2) else 0) ?_⟩
  intro u w h
  obtain ⟨-, i, -, rfl⟩ := crown_adj.1 h
  cases u.2.2 <;> simp

/-- `α(G₂) ≥ k(Δ+1)`: one side of the bipartition. -/
theorem crown_true_indepNum (Δ k : ℕ) : k * (Δ + 1) ≤ (crown Δ k true).toSimpleGraph.indepNum := by
  let I : Finset (CV Δ k) := univ.filter fun v => v.2.2 = false
  have hI : (crown Δ k true).toSimpleGraph.IsIndepSet (I : Set (CV Δ k)) := by
    intro u hu w hw _ h
    obtain ⟨-, i, -, rfl⟩ := crown_adj.1 h
    simp only [I, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu hw
    rw [hu] at hw; simp at hw
  have hcard : #I = k * (Δ + 1) := by
    have : I = (univ : Finset (Fin k × ZMod (Δ + 1))).image fun p => (p.1, p.2, false) := by
      ext ⟨c, a, s⟩; cases s <;> simp [I]
    rw [this, card_image_of_injective _ (fun p q h => by simpa [Prod.ext_iff] using h),
      card_univ, Fintype.card_prod, Fintype.card_fin, ZMod.card]
  rw [← hcard]
  exact hI.card_le_indepNum

/-- In `G₁` (disjoint cliques) an independent set has at most one node per clique, so at most
`2k` nodes. -/
theorem crown_false_indep_card {I : Finset (CV Δ k)}
    (hI : (crown Δ k false).toSimpleGraph.IsIndepSet (I : Set (CV Δ k))) : #I ≤ 2 * k := by
  have : #I ≤ #(univ : Finset (Fin k × Bool)) := by
    refine card_le_card_of_injOn (fun v => (v.1, v.2.2)) (fun _ _ => mem_coe.2 (mem_univ _)) ?_
    rintro ⟨c, a, s⟩ hu ⟨c', b, s'⟩ hw h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    by_contra hne
    have hab : a ≠ b := fun h => hne (by rw [h])
    apply hI hu hw hne
    rw [crown_adj]
    have hpos : (b - a).val ≠ 0 := by
      rw [Ne, ZMod.val_eq_zero, sub_eq_zero]; exact Ne.symm hab
    refine ⟨hne, (b - a).val - 1, ?_, ?_⟩
    · have := ZMod.val_lt (b - a); omega
    · rw [show (b - a).val - 1 + 1 = (b - a).val by omega, ZMod.natCast_zmod_val]
      simp
  simpa [Fintype.card_prod, mul_comm] using this

/-! ### Indistinguishability -/

/-- The involution of `CV Δ k` flipping the side of every node in the block of `v` other than the
nodes `(c, a, ·)` of `v`'s own column. It fixes `v`. -/
def flipOthersFun {Δ k : ℕ} (v : CV Δ k) (u : CV Δ k) : CV Δ k :=
  if u.1 = v.1 ∧ u.2.1 ≠ v.2.1 then (u.1, u.2.1, !u.2.2) else u

theorem flipOthersFun_involutive {Δ k : ℕ} (v : CV Δ k) : Function.Involutive (flipOthersFun v) := by
  rintro ⟨c, a, s⟩
  by_cases h : c = v.1 ∧ a ≠ v.2.1
  · simp [flipOthersFun, h]
  · simp [flipOthersFun, h]

/-- `flipOthersFun v` as a permutation. -/
def flipOthers {Δ k : ℕ} (v : CV Δ k) : Equiv.Perm (CV Δ k) :=
  (flipOthersFun_involutive v).toPerm

theorem flipOthers_self {Δ k : ℕ} (v : CV Δ k) : flipOthers v v = v := by
  simp [flipOthers, flipOthersFun]

theorem flipOthers_nbr {Δ k : ℕ} (v : CV Δ k) {i : ℕ} (hi : i < Δ) :
    (crown Δ k true).nbr v i = flipOthers v ((crown Δ k false).nbr v i) := by
  rw [crown_nbr v hi, crown_nbr v hi]
  have := natCast_succ_ne_zero (Δ := Δ) hi
  push_cast at this
  simp [flipOthers, flipOthersFun, this]

/-- **View equality.** The 1-round output of `v` in `G₂` under inputs `x` equals its output in
`G₁` under inputs `x ∘ flipOthers v`. -/
theorem eval_crown_true {Δ k N : ℕ} {R : Type} (A : Algorithm (Fin N × R) Bool)
    (x : CV Δ k → Fin N × R) (v : CV Δ k) :
    A.eval (crown Δ k true) 1 x v = A.eval (crown Δ k false) 1 (x ∘ flipOthers v) v := by
  rw [eval_one, eval_one]
  simp only [crown_deg, crown_rport, Function.comp_apply, flipOthers_self]
  congr 2
  funext i
  by_cases hi : i < Δ
  · simp only [hi, ite_true]; rw [flipOthers_nbr v hi]
  · simp [hi]

/-- Relabeling along a permutation of the nodes. -/
def relabel {V : Type} {N : ℕ} (σ : Equiv.Perm V) : (V ↪ Fin N) ≃ (V ↪ Fin N) where
  toFun ℓ := σ.toEmbedding.trans ℓ
  invFun ℓ := σ.symm.toEmbedding.trans ℓ
  left_inv ℓ := by ext; simp
  right_inv ℓ := by ext; simp

/-- Permuting the random strings along a permutation of the nodes. -/
def rerand {V R : Type} (σ : Equiv.Perm V) : (V → R) ≃ (V → R) where
  toFun r := r ∘ σ
  invFun r := r ∘ σ.symm
  left_inv r := by ext; simp
  right_inv r := by ext; simp

theorem card_output_eq_sum {V : Type} [Fintype V] [DecidableEq V] {N : ℕ} {R : Type}
    (A : Algorithm (Fin N × R) Bool) (G : PNGraph V) (ℓ : V ↪ Fin N) (r : V → R) :
    (#(output A G ℓ r) : ℝ) =
      ∑ v, if A.eval G 1 (fun u => (ℓ u, r u)) v = true then (1 : ℝ) else 0 := by
  simp [output, Finset.sum_boole]

/-- The (unnormalized) probability that `v` joins, summed over all labelings. -/
noncomputable def joinWeight {V : Type} [Fintype V] [DecidableEq V] {N : ℕ} {R : Type} [Fintype R]
    (μ : R → ℝ) (A : Algorithm (Fin N × R) Bool) (G : PNGraph V) (v : V) : ℝ :=
  ∑ ℓ : V ↪ Fin N, ∑ r : V → R, (∏ u, μ (r u)) *
    if A.eval G 1 (fun u => (ℓ u, r u)) v = true then (1 : ℝ) else 0

theorem sum_expectedSize_eq_sum_joinWeight {V : Type} [Fintype V] [DecidableEq V] {N : ℕ}
    {R : Type} [Fintype R] (μ : R → ℝ) (A : Algorithm (Fin N × R) Bool) (G : PNGraph V) :
    ∑ ℓ : V ↪ Fin N, expectedSize μ A G ℓ = ∑ v, joinWeight μ A G v := by
  simp only [expectedSize, card_output_eq_sum, mul_sum, joinWeight]
  exact (sum_congr rfl fun ℓ _ => sum_comm).trans sum_comm

/-- Every node has the same join weight in `G₁` and `G₂`. -/
theorem joinWeight_crown {Δ k N : ℕ} {R : Type} [Fintype R] (μ : R → ℝ)
    (A : Algorithm (Fin N × R) Bool) (v : CV Δ k) :
    joinWeight μ A (crown Δ k true) v = joinWeight μ A (crown Δ k false) v := by
  unfold joinWeight
  set σ := flipOthers v
  have hview : ∀ (ℓ : CV Δ k ↪ Fin N) (r : CV Δ k → R),
      A.eval (crown Δ k true) 1 (fun u => (ℓ u, r u)) v =
        A.eval (crown Δ k false) 1 (fun u => (relabel σ ℓ u, rerand σ r u)) v := by
    intro ℓ r
    rw [eval_crown_true]; rfl
  have hw : ∀ r : CV Δ k → R, ∏ u, μ (rerand σ r u) = ∏ u, μ (r u) := fun r =>
    Equiv.prod_comp σ (fun u => μ (r u))
  calc ∑ ℓ : CV Δ k ↪ Fin N, ∑ r : CV Δ k → R, (∏ u, μ (r u)) *
          (if A.eval (crown Δ k true) 1 (fun u => (ℓ u, r u)) v = true then (1 : ℝ) else 0)
      = ∑ ℓ : CV Δ k ↪ Fin N, ∑ r : CV Δ k → R, (∏ u, μ (rerand σ r u)) *
          (if A.eval (crown Δ k false) 1 (fun u => (relabel σ ℓ u, rerand σ r u)) v = true
            then (1 : ℝ) else 0) := by
        refine sum_congr rfl fun ℓ _ => sum_congr rfl fun r _ => ?_
        rw [hview, hw]
    _ = ∑ ℓ : CV Δ k ↪ Fin N, ∑ r : CV Δ k → R, (∏ u, μ (r u)) *
          (if A.eval (crown Δ k false) 1 (fun u => (relabel σ ℓ u, r u)) v = true
            then (1 : ℝ) else 0) :=
        sum_congr rfl fun ℓ _ => Equiv.sum_comp (rerand σ) (fun r => (∏ u, μ (r u)) *
          (if A.eval (crown Δ k false) 1 (fun u => (relabel σ ℓ u, r u)) v = true
            then (1 : ℝ) else 0))
    _ = _ := Equiv.sum_comp (relabel σ) (fun ℓ => ∑ r : CV Δ k → R, (∏ u, μ (r u)) *
          (if A.eval (crown Δ k false) 1 (fun u => (ℓ u, r u)) v = true then (1 : ℝ) else 0))

/-- Summed over all labelings, the expected output sizes in `G₁` and `G₂` agree. -/
theorem sum_expectedSize_eq {Δ k N : ℕ} {R : Type} [Fintype R] (μ : R → ℝ)
    (A : Algorithm (Fin N × R) Bool) :
    ∑ ℓ : CV Δ k ↪ Fin N, expectedSize μ A (crown Δ k true) ℓ =
      ∑ ℓ : CV Δ k ↪ Fin N, expectedSize μ A (crown Δ k false) ℓ := by
  rw [sum_expectedSize_eq_sum_joinWeight, sum_expectedSize_eq_sum_joinWeight]
  exact sum_congr rfl fun v _ => joinWeight_crown μ A v

/-! ### Theorem 4 -/

theorem sum_weight_eq_one {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] (μ : R → ℝ)
    (hμ1 : ∑ a, μ a = 1) : ∑ r : V → R, ∏ v, μ (r v) = 1 := by
  rw [← Fintype.prod_sum fun _ => μ]; simp [hμ1]

theorem expectedSize_nonneg {V : Type} [Fintype V] [DecidableEq V] {N : ℕ} {R : Type}
    [Fintype R] {μ : R → ℝ} (hμ0 : ∀ a, 0 ≤ μ a) (A : Algorithm (Fin N × R) Bool) (G : PNGraph V)
    (ℓ : V ↪ Fin N) : 0 ≤ expectedSize μ A G ℓ :=
  sum_nonneg fun _ _ => mul_nonneg (prod_nonneg fun _ _ => hμ0 _) (Nat.cast_nonneg _)

/-- In `G₁` a correct algorithm outputs at most `2k` nodes, so its expected output is `≤ 2k`. -/
theorem expectedSize_crown_false_le {Δ k N : ℕ} {R : Type} [Fintype R] {μ : R → ℝ}
    (hμ0 : ∀ a, 0 ≤ μ a) (hμ1 : ∑ a, μ a = 1) {A : Algorithm (Fin N × R) Bool}
    (hA : IsCorrect A μ (CV Δ k) Δ) (ℓ : CV Δ k ↪ Fin N) :
    expectedSize μ A (crown Δ k false) ℓ ≤ 2 * k := by
  calc expectedSize μ A (crown Δ k false) ℓ
      ≤ ∑ r : CV Δ k → R, (∏ v, μ (r v)) * (2 * k : ℝ) := by
        refine sum_le_sum fun r _ => ?_
        rcases (prod_nonneg fun v _ => hμ0 (r v) : (0 : ℝ) ≤ ∏ v, μ (r v)).eq_or_lt with h0 | hpos
        · rw [← h0, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ hpos.le
          exact_mod_cast crown_false_indep_card (hA _ (crown_isRegular Δ k false) ℓ r hpos)
    _ = 2 * k := by rw [← sum_mul, sum_weight_eq_one μ hμ1, one_mul]

/-- **Theorem 4** (lower bound for 1-round algorithms). Let `A` be any 1-round randomized
algorithm (labels from `Fin N`, i.i.d. random strings with distribution `μ` on a finite set) that
outputs an independent set with probability `1` on simple `Δ`-regular port-numbered graphs with
`n = 2k(Δ+1)` nodes, `N ≥ n`. Then on some `Δ`-regular bipartite graph `G` (with
`α(G) ≥ k(Δ+1) = n/2`) and some labeling, `E[|output|] ≤ 2α(G)/(Δ+1)`. -/
theorem theorem4 {Δ k N : ℕ} (hN : 2 * k * (Δ + 1) ≤ N) {R : Type} [Fintype R] (μ : R → ℝ)
    (hμ0 : ∀ a, 0 ≤ μ a) (hμ1 : ∑ a, μ a = 1) (A : Algorithm (Fin N × R) Bool)
    (hA : IsCorrect A μ (CV Δ k) Δ) :
    ∃ G : PNGraph (CV Δ k), IsRegularPN G Δ ∧ G.toSimpleGraph.Colorable 2 ∧
      k * (Δ + 1) ≤ G.toSimpleGraph.indepNum ∧
      ∃ ℓ : CV Δ k ↪ Fin N,
        ((Δ : ℝ) + 1) * expectedSize μ A G ℓ ≤ 2 * G.toSimpleGraph.indepNum := by
  refine ⟨crown Δ k true, crown_isRegular Δ k true, crown_true_colorable Δ k,
    crown_true_indepNum Δ k, ?_⟩
  have hne : Nonempty (CV Δ k ↪ Fin N) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card, Fintype.card_bool]
    linarith
  have hsum : ∑ ℓ : CV Δ k ↪ Fin N, expectedSize μ A (crown Δ k true) ℓ ≤
      ∑ _ℓ : CV Δ k ↪ Fin N, (2 * k : ℝ) := by
    rw [sum_expectedSize_eq]
    exact sum_le_sum fun ℓ _ => expectedSize_crown_false_le hμ0 hμ1 hA ℓ
  obtain ⟨ℓ, -, hℓ⟩ := exists_le_of_sum_le univ_nonempty hsum
  refine ⟨ℓ, ?_⟩
  have hα : ((k * (Δ + 1) : ℕ) : ℝ) ≤ (crown Δ k true).toSimpleGraph.indepNum := by
    exact_mod_cast crown_true_indepNum Δ k
  push_cast at hα
  have : (0 : ℝ) ≤ Δ + 1 := by positivity
  nlinarith

/-- **Theorem 4** as stated: if a correct 1-round algorithm has performance ratio `ρ` on simple
`Δ`-regular graphs with `n = 2k(Δ+1)` nodes (`k ≥ 1`), i.e. `α(G) ≤ ρ · E[|output|]` for every
such port-numbered graph and every labeling, then `ρ ≥ (Δ+1)/2`. -/
theorem theorem4_ratio {Δ k N : ℕ} (hk : 1 ≤ k) (hN : 2 * k * (Δ + 1) ≤ N) {R : Type}
    [Fintype R] (μ : R → ℝ) (hμ0 : ∀ a, 0 ≤ μ a) (hμ1 : ∑ a, μ a = 1)
    (A : Algorithm (Fin N × R) Bool) (hA : IsCorrect A μ (CV Δ k) Δ) (ρ : ℝ)
    (hρ : ∀ G : PNGraph (CV Δ k), IsRegularPN G Δ → ∀ ℓ : CV Δ k ↪ Fin N,
      (G.toSimpleGraph.indepNum : ℝ) ≤ ρ * expectedSize μ A G ℓ) :
    ((Δ : ℝ) + 1) / 2 ≤ ρ := by
  obtain ⟨G, hG, -, hα, ℓ, hE⟩ := theorem4 hN μ hμ0 hμ1 A hA
  have h := hρ G hG ℓ
  have hE0 := expectedSize_nonneg hμ0 A G ℓ
  have hαpos : (0 : ℝ) < G.toSimpleGraph.indepNum := by
    have : 0 < G.toSimpleGraph.indepNum := lt_of_lt_of_le (by positivity) hα
    exact_mod_cast this
  have hρE : 0 < ρ * expectedSize μ A G ℓ := lt_of_lt_of_le hαpos h
  have hρ0 : 0 < ρ := by
    by_contra hneg; push Not at hneg; nlinarith
  rw [div_le_iff₀ (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ Δ + 1)]

/-! ### Non-vacuity: Boppana's rule as a 1-round algorithm -/

/-- Order on (label, random rank): compare random ranks, break ties by labels. -/
def keyLt {N K : ℕ} (y x : Fin N × Fin K) : Bool := decide (y.2 < x.2 ∨ (y.2 = x.2 ∧ y.1 < x.1))

theorem keyLt_asymm {N K : ℕ} (x y : Fin N × Fin K) (h : keyLt x y = true) :
    keyLt y x = false := by
  simp only [keyLt, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
  omega

/-- Boppana's algorithm (rule (3) with finite precision `K` and label tie-breaking) as a CSLib
port-numbering algorithm: every node sends its (label, random rank) to all neighbours and joins iff
its key is larger than all received keys. -/
def boppanaAlg (N K : ℕ) : Algorithm (Fin N × Fin K) Bool where
  State := ℕ × (Fin N × Fin K) × Bool
  Msg := Fin N × Fin K
  init d x := (d, x, false)
  send s _ := s.2.1
  recv s m := (s.1, s.2.1, decide (∀ i < s.1, ∀ y, m i = some y → keyLt y s.2.1 = true))
  out s := s.2.2

theorem boppanaAlg_eval {V : Type} {N K : ℕ} (G : PNGraph V) (x : V → Fin N × Fin K) (v : V) :
    (boppanaAlg N K).eval G 1 x v = true ↔ ∀ i < G.deg v, keyLt (x (G.nbr v i)) (x v) = true := by
  rw [eval_one]
  simp only [boppanaAlg, decide_eq_true_eq]
  constructor
  · intro h i hi; exact h i hi _ (by simp [hi])
  · intro h i hi y hy; simp only [hi, ite_true, Option.some.injEq] at hy; rw [← hy]; exact h i hi

/-- Boppana's rule is a correct 1-round algorithm (on every port-numbered graph, every labeling
and every outcome of the random ranks), so the hypothesis of Theorem 4 is satisfiable. -/
theorem boppanaAlg_correct (V : Type) [Fintype V] [DecidableEq V] (Δ N K : ℕ)
    (μ : Fin K → ℝ) : IsCorrect (boppanaAlg N K) μ V Δ := by
  intro G _ ℓ r _ u hu w hw _ hadj
  simp only [output, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, boppanaAlg_eval] at hu hw
  obtain ⟨-, i, hi, rfl⟩ := hadj
  have h1 := hu i hi
  have h2 := hw (G.rport u i) (G.rport_lt hi)
  rw [G.nbr_nbr hi] at h2
  rw [keyLt_asymm _ _ h1] at h2
  exact Bool.false_ne_true h2

end Podc.LocalISApproximation
