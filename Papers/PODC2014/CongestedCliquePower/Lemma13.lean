import Papers.PODC2014.CongestedCliquePower.LowerBoundGraph
import Podc.Computability.Distributed.CongestedClique.Broadcast
import Cslib.Computability.Distributed.Congest.Randomized

/-!
# Lemma 13: lower bounds for `H`-subgraph detection from `(H, F)`-lower bound graphs

Drucker–Kuhn–Oshman, PODC 2014, Lemma 13. Given an `(H, F)`-lower bound graph `G'` on the node set
`V` (`|V| = n`), Alice's input `x` and Bob's input `y` are subsets of `E_F`; the input graph
`famG x y` is `G'` with the edges `φA(e)`, `e ∉ x`, and `φB(e)`, `e ∉ y`, removed. By
Observation 11, `famG x y` contains `H` iff `x ∩ y ≠ ∅`. Alice simulates every node outside `V_B`,
Bob the nodes of `V_B`.

* `lemma_13_bcast`: a deterministic `T`-round CLIQUE-BCAST algorithm with `b`-bit messages
  detecting `H` gives `|E_F| ≤ T · n · b + 2` (the paper's `Ω(|E_F| / (n b))`), using the proved
  bound `CC(DISJ_K) ≥ K`.
* `lemma_13_bcast_rand`: the same for randomized algorithms with error `ε`, given as hypothesis
  that private-coin protocols for `DISJ_K` with error `ε` need `C` bits (Kalyanasundaram–Schnitger /
  Razborov: `C = Ω(K)` for constant `ε < 1/2`; not formalized).
* `lemma_13_congest`, `lemma_13_congest_rand`: CONGEST-UCAST on the input graph, for a `δ`-sparse
  lower bound graph: `|E_F| ≤ T · 2 · ⌊δ n⌋ · b + 2` (the paper's `Ω(|E_F| / (δ n b))`).

Output convention: "all nodes accept iff the input graph is `H`-free" (equivalently some node
reports a copy of `H` iff there is one).
-/

namespace Podc.CongestedCliquePower

open SimpleGraph Cslib.CommunicationComplexity Cslib.CongestedClique

variable {VH VF V : Type} {H : SimpleGraph VH} {F : SimpleGraph VF} {G' : SimpleGraph V}

/-- Node inputs for the input graph `G`: node `v` knows its incident edges. -/
noncomputable def adjInput (G : SimpleGraph V) : V → V → Bool := by
  classical exact fun v w => decide (G.Adj v w)

namespace LowerBoundGraph

variable (L : LowerBoundGraph H F G')

/-- The input graph for the set-disjointness instance `(x, y)` (subsets of `E_F`): `G'` without
the edges `φA(e)`, `e ∉ x`, and `φB(e)`, `e ∉ y`. -/
def famG (x y : F.edgeSet → Bool) : SimpleGraph V where
  Adj p q := G'.Adj p q ∧
    (∀ u v (h : F.Adj u v), L.φA u = p → L.φA v = q → x ⟨s(u, v), h⟩ = true) ∧
    (∀ u v (h : F.Adj u v), L.φB u = p → L.φB v = q → y ⟨s(u, v), h⟩ = true)
  symm := ⟨fun p q => by
    rintro ⟨h, hA, hB⟩
    refine ⟨h.symm, fun u v huv h1 h2 => ?_, fun u v huv h1 h2 => ?_⟩
    · have := hA v u huv.symm h2 h1
      simpa [Sym2.eq_swap] using this
    · have := hB v u huv.symm h2 h1
      simpa [Sym2.eq_swap] using this⟩
  loopless := ⟨fun p h => G'.loopless.irrefl p h.1⟩

lemma famG_le (x y) : L.famG x y ≤ G' := fun _ _ h => h.1

lemma famG_fixed (x y) (p q : V) (h : G'.Adj p q) (hA : ¬ L.EA p q) (hB : ¬ L.EB p q) :
    (L.famG x y).Adj p q :=
  ⟨h, fun u v huv h1 h2 => absurd ⟨u, v, huv, h1, h2⟩ hA,
    fun u v huv h1 h2 => absurd ⟨u, v, huv, h1, h2⟩ hB⟩

lemma famG_adj_A (x y) {u v : VF} (huv : F.Adj u v) :
    (L.famG x y).Adj (L.φA u) (L.φA v) ↔ x ⟨s(u, v), huv⟩ = true := by
  constructor
  · rintro ⟨-, hA, -⟩
    exact hA u v huv rfl rfl
  · intro hx
    refine ⟨L.φA.toHom.map_adj huv, fun u' v' h' h1 h2 => ?_, fun u' v' h' h1 h2 => ?_⟩
    · obtain rfl := L.φA.injective h1
      obtain rfl := L.φA.injective h2
      exact hx
    · exact absurd h1.symm (L.disjoint u u')

lemma famG_adj_B (x y) {u v : VF} (huv : F.Adj u v) :
    (L.famG x y).Adj (L.φB u) (L.φB v) ↔ y ⟨s(u, v), huv⟩ = true := by
  constructor
  · rintro ⟨-, -, hB⟩
    exact hB u v huv rfl rfl
  · intro hy
    refine ⟨L.φB.toHom.map_adj huv, fun u' v' h' h1 h2 => ?_, fun u' v' h' h1 h2 => ?_⟩
    · exact absurd h1 (L.disjoint u' u)
    · obtain rfl := L.φB.injective h1
      obtain rfl := L.φB.injective h2
      exact hy

/-- The reduction (Observation 11): `famG x y` contains `H` iff `x` and `y` intersect. -/
theorem contains_iff [Fintype VF] [DecidableRel F.Adj] (x y : F.edgeSet → Bool) :
    H ⊑ L.famG x y ↔ Protocol.disj x y = false := by
  rw [L.observation_11 _ (L.famG_le x y) (L.famG_fixed x y)]
  simp only [Protocol.disj, decide_eq_false_iff_not, not_forall, not_not]
  constructor
  · rintro ⟨u, v, huv, hA, hB⟩
    exact ⟨⟨s(u, v), huv⟩, (L.famG_adj_A x y huv).1 hA, (L.famG_adj_B x y huv).1 hB⟩
  · rintro ⟨⟨e, he⟩, hx, hy⟩
    induction e using Sym2.ind with
    | h u v =>
      exact ⟨u, v, he, (L.famG_adj_A x y he).2 hx, (L.famG_adj_B x y he).2 hy⟩

/-- The two-party split: Alice simulates every node outside `V_B`. -/
noncomputable def twoPartySplit : Bcast.Split (F.edgeSet → Bool) (F.edgeSet → Bool) V (V → Bool) where
  inp x y := adjInput (L.famG x y)
  alice v := by classical exact decide (∀ b, L.φB b ≠ v)
  inp_alice x y y' v hv := by
    funext w
    simp only [adjInput]
    congr 1
    apply propext
    simp only [decide_eq_true_eq] at hv
    simp only [famG]
    exact ⟨fun ⟨a, b, _⟩ => ⟨a, b, fun u _ _ h1 _ => absurd h1 (hv u)⟩,
      fun ⟨a, b, _⟩ => ⟨a, b, fun u _ _ h1 _ => absurd h1 (hv u)⟩⟩
  inp_bob x x' y v hv := by
    funext w
    simp only [adjInput]
    congr 1
    apply propext
    simp only [decide_eq_false_iff_not, not_forall, not_not] at hv
    obtain ⟨c, rfl⟩ := hv
    simp only [famG]
    exact ⟨fun ⟨a, _, b⟩ => ⟨a, fun u _ _ h1 _ => absurd h1 (L.disjoint u c), b⟩,
      fun ⟨a, _, b⟩ => ⟨a, fun u _ _ h1 _ => absurd h1 (L.disjoint u c), b⟩⟩

variable [Fintype V] [DecidableEq V] [Fintype VF] [DecidableRel F.Adj]

include L

/-- **Lemma 13 (CLIQUE-BCAST, deterministic).** If `G'` is an `(H, F)`-lower bound graph on `n`
nodes and a deterministic CLIQUE-BCAST algorithm with `b`-bit messages decides in `T` rounds
whether its input graph on these nodes is `H`-free, then `|E_F| ≤ T · n · b + 2`, i.e.
`T ≥ (|E_F| - 2) / (n b)`. -/
theorem lemma_13_bcast {σ : Type} {b : ℕ} (A : Bcast.Algorithm V (V → Bool) σ b) (T : ℕ)
    (hA : ∀ G : SimpleGraph V, A.Accepts (adjInput G) T ↔ H.Free G) :
    Fintype.card F.edgeSet ≤ T * (Fintype.card V * b) + 2 := by
  refine L.twoPartySplit.lowerBound A T Protocol.disj (fun x y => ?_) _
    fun _ _ hP hc => Protocol.disj_lowerBound hP hc
  change A.Accepts (adjInput (L.famG x y)) T ↔ _
  rw [hA, SimpleGraph.Free, L.contains_iff]
  cases Protocol.disj x y <;> simp

/-- The randomized communication-complexity hypothesis for set disjointness on `K` elements:
every private-coin protocol (nonempty coin spaces) computing `DISJ_K` with error `≤ ε` sends at
least `C` bits. For constant `ε < 1/2` this holds with `C = Ω(|K|)`
(Kalyanasundaram–Schnitger, Razborov); this is not formalized. -/
def RandDisjLB (K : Type) [Fintype K] (ε : ℝ) (C : ℕ) : Prop :=
  ∀ (RA RB : Type) [Fintype RA] [Fintype RB] [Nonempty RA] [Nonempty RB]
    (P : Protocol ((K → Bool) × RA) ((K → Bool) × RB) Bool) (c : ℕ),
    P.RandComputes Protocol.disj ε → P.CostLE c → C ≤ c

/-- **Lemma 13 (CLIQUE-BCAST, randomized).** If a randomized CLIQUE-BCAST algorithm (node `v`
gets its incident edges and a private random string `r v ∈ ρ`, uniform) decides `H`-freeness with
error at most `ε` on every input graph within `T` rounds, then `C ≤ T · n · b + 2` for every `C`
satisfying the randomized disjointness bound `RandDisjLB E_F ε C`. -/
theorem lemma_13_bcast_rand {σ ρ : Type} [Fintype ρ] [Nonempty ρ] {b : ℕ}
    (A : Bcast.Algorithm V ((V → Bool) × ρ) σ b) (T : ℕ) (ε : ℝ)
    (hA : ∀ G : SimpleGraph V, (A.randErr (adjInput G) T (by classical exact decide (H.Free G)) : ℝ)
      ≤ ε * Fintype.card (V → ρ))
    (C : ℕ) (hC : RandDisjLB F.edgeSet ε C) :
    C ≤ T * (Fintype.card V * b) + 2 := by
  classical
  refine L.twoPartySplit.rand_lowerBound A T Protocol.disj ε (fun x y => ?_) C
    fun P c hP hc => hC _ _ P c hP hc
  have e : Protocol.disj x y = decide (H.Free (L.famG x y)) := by
    have := L.contains_iff x y
    cases h : Protocol.disj x y <;> simp_all [SimpleGraph.Free]
  rw [e]
  exact hA (L.famG x y)

/-! ### CONGEST-UCAST (the input graph is the network) -/

/-- The cut of a partition `inA` of `V'`, as ordered pairs `(a, b)`, `a ∈ A`, `b ∈ B`. -/
noncomputable def cut (inA : V → Bool) : Finset (V × V) := by
  classical exact Finset.univ.filter fun p : V × V => inA p.1 = true ∧ inA p.2 = false ∧ G'.Adj p.1 p.2

/-- The family of lower bound graphs of CSLib's CONGEST framework given by `famG` and a partition
`(A, B)` with `V_A ⊆ A`, `V_B ⊆ B`. -/
noncomputable def congestFamily (inA : V → Bool) (hA : ∀ a, inA (L.φA a) = true)
    (hB : ∀ b, inA (L.φB b) = false) :
    Cslib.Congest.LBFamily (F.edgeSet → Bool) (F.edgeSet → Bool) V (V → Bool) := by
  classical
  refine Cslib.Congest.LBFamily.ofAdj L.famG inA (cut (G' := G') inA) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact ⟨hp.1, hp.2.1⟩
  · intro x y a b ha hb hab
    simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ha, hb, hab.1⟩
  · intro x y y' a b ha hb
    simp only [famG]
    have : ∀ u, L.φB u ≠ a := fun u h => by rw [← h, hB] at ha; exact absurd ha (by decide)
    exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2, fun u _ _ h _ => absurd h (this u)⟩,
      fun ⟨h1, h2, _⟩ => ⟨h1, h2, fun u _ _ h _ => absurd h (this u)⟩⟩
  · intro x x' y a b ha hb
    simp only [famG]
    have : ∀ u, L.φA u ≠ a := fun u h => by rw [← h, hA] at ha; exact absurd ha (by decide)
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, fun u _ _ h _ => absurd h (this u), h3⟩,
      fun ⟨h1, _, h3⟩ => ⟨h1, fun u _ _ h _ => absurd h (this u), h3⟩⟩
  · intro x x' y y' a b ha hb
    simp only [famG]
    have h1 : ∀ u, L.φA u ≠ b := fun u h => by rw [← h, hA] at hb; exact absurd hb (by decide)
    have h2 : ∀ u, L.φB u ≠ a := fun u h => by rw [← h, hB] at ha; exact absurd ha (by decide)
    exact ⟨fun ⟨g, _, _⟩ => ⟨g, fun _ v _ _ h => absurd h (h1 v), fun u _ _ h _ => absurd h (h2 u)⟩,
      fun ⟨g, _, _⟩ => ⟨g, fun _ v _ _ h => absurd h (h1 v), fun u _ _ h _ => absurd h (h2 u)⟩⟩

omit [DecidableEq V] in
/-- **Lemma 13 (CONGEST-UCAST, deterministic).** Let `(A, B)` be a partition of the nodes with
`V_A ⊆ A`, `V_B ⊆ B`. If a deterministic CONGEST algorithm with `B`-bit messages, run on the input
graph itself, decides `H`-freeness in `T` rounds, then `|E_F| ≤ T · 2 · |cut(A, B)| · B + 2`. -/
theorem lemma_13_congest {σ : Type} {B : ℕ} (A : Cslib.Congest.Algorithm V (V → Bool) σ B) (T : ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      A.Accepts G (fun v w => decide (G.Adj v w)) T ↔ H.Free G)
    (inA : V → Bool) (hVA : ∀ a, inA (L.φA a) = true) (hVB : ∀ b, inA (L.φB b) = false) :
    Fintype.card F.edgeSet ≤ T * (2 * ((cut (G' := G') inA).card * B)) + 2 := by
  classical
  refine (L.congestFamily inA hVA hVB).disj_lowerBound A T (fun x y => ?_)
  have h1 : A.Accepts (L.famG x y) ((L.congestFamily inA hVA hVB).inp x y) T ↔
      H.Free (L.famG x y) := by
    convert hA (L.famG x y) using 3
    simp only [congestFamily, Cslib.Congest.LBFamily.ofAdj]
  change A.Accepts (L.famG x y) ((L.congestFamily inA hVA hVB).inp x y) T ↔ _
  rw [h1, SimpleGraph.Free, L.contains_iff]
  cases Protocol.disj x y <;> simp

omit [DecidableEq V] in
/-- **Lemma 13 (CONGEST-UCAST, `δ`-sparse form).** For a `δ`-sparse `(H, F)`-lower bound graph on
`n` nodes, a deterministic CONGEST algorithm deciding `H`-freeness in `T` rounds with `B`-bit
messages satisfies `|E_F| ≤ 2 T δ n B + 2`, i.e. `T ≥ (|E_F| - 2) / (2 δ n B)`. -/
theorem lemma_13_congest_sparse [DecidableRel G'.Adj] {σ : Type} {B : ℕ}
    (A : Cslib.Congest.Algorithm V (V → Bool) σ B) (T : ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      A.Accepts G (fun v w => decide (G.Adj v w)) T ↔ H.Free G)
    (δ : ℝ) (hS : L.IsSparse δ) :
    (Fintype.card F.edgeSet : ℝ) ≤ 2 * T * δ * Fintype.card V * B + 2 := by
  classical
  obtain ⟨inA, hVA, hVB, hcut⟩ := hS
  have h := L.lemma_13_congest A T hA inA hVA hVB
  have hc : ((cut (G' := G') inA).card : ℝ) ≤ δ * Fintype.card V := by
    refine le_trans (le_of_eq ?_) hcut
    simp only [cut]
    congr 2
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h' : (Fintype.card F.edgeSet : ℝ) ≤ T * (2 * ((cut (G' := G') inA).card * B)) + 2 := by
    exact_mod_cast h
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg hT hB)]

/-- **Lemma 13 (CONGEST-UCAST, randomized).** Randomized version (private coins per node): with
the randomized disjointness bound `RandDisjLB E_F ε C` as hypothesis,
`C ≤ T · 2 · |cut(A, B)| · B + 2`. -/
theorem lemma_13_congest_rand {σ ρ : Type} [Fintype ρ] [Nonempty ρ] {B : ℕ}
    (A : Cslib.Congest.Algorithm V ((V → Bool) × ρ) σ B) (T : ℕ) (ε : ℝ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      (Cslib.Congest.LBFamily.Algorithm.randErr A G (fun v w => decide (G.Adj v w)) T
        (by classical exact decide (H.Free G)) : ℝ) ≤ ε * Fintype.card (V → ρ))
    (inA : V → Bool) (hVA : ∀ a, inA (L.φA a) = true) (hVB : ∀ b, inA (L.φB b) = false)
    (C : ℕ) (hC : RandDisjLB F.edgeSet ε C) :
    C ≤ T * (2 * ((cut (G' := G') inA).card * B)) + 2 := by
  classical
  refine (L.congestFamily inA hVA hVB).rand_lowerBound A T Protocol.disj ε (fun x y => ?_) C
    fun P c hP hc => hC _ _ P c hP hc
  have e : Protocol.disj x y = decide (H.Free (L.famG x y)) := by
    have := L.contains_iff x y
    cases h : Protocol.disj x y <;> simp_all [SimpleGraph.Free]
  rw [e]
  convert hA (L.famG x y) using 3
  · simp only [congestFamily, Cslib.Congest.LBFamily.ofAdj]
  · funext v w
    simp only [congestFamily, Cslib.Congest.LBFamily.ofAdj]

end LowerBoundGraph

end Podc.CongestedCliquePower
