import Papers.PODC2015.RandomizedPLS.GraphTools
import Papers.PODC2015.RandomizedPLS.Acyclicity

/-!
# Vertex biconnectivity: lower bounds of Theorem 5.2

The graph `G` of the proof of Theorem 5.2 (Figure 2a) is the wheel: an `n`-cycle `v₀ … v_{n-1}`
plus the edges `{v₀, v_j}`. We build the slightly more general `Wheel.G n c`: a `c`-cycle
`v₀ … v_{c-1}`, `v₀` adjacent to every other node `v₁ … v_{n-1}` (so `v_c, …, v_{n-1}` are pendant
nodes); `Wheel.G n n` is the graph of Theorem 5.2 and `Wheel.G n c` the graph of Theorem 5.4.
States are the identities `0, …, n-1`. Port numbers are "consistently ordered": a cycle node
`v_x` (`1 ≤ x ≤ c-1`) has its successor at port `0` and its predecessor at port `1`.

The copies are the single edges `H_k = {v_{3k+1}, v_{3k+2}}`, `k < ⌊c/3⌋` (the paper uses
`{v₁, v₂}` and `{v_{3i}, v_{3i+1}}`, `2 ≤ i ≤ ⌊c/3⌋ - 1`, i.e. one copy less; any family of single
cycle edges at distance `≥ 2` works).
Crossing `{v_a, v_{a+1}}` and `{v_b, v_{b+1}}` (`a < b`) replaces them by `{v_a, v_{b+1}}` and
`{v_b, v_{a+1}}`: the cycle splits into `v_{a+1} … v_b` and the rest, which are only joined
through `v₀`.

* `Wheel.cross_adj_val`: the adjacency of the crossing, in terms of indices.
* `thm_5_2_det`, `thm_5_2_rand`: Theorem 5.2 (lower bounds): `log₂ ⌊n/3⌋ ≤ 2 (κ(n) + 1)` for
  every PLS for `(F_con, v2con)`, and `log₂ ⌊n/3⌋ ≤ 2 · 2^(κ(n)+1)` for every one-sided RPLS.
-/

namespace Podc.RandomizedPLS

open Classical

variable {S : Type}

/-- Vertex-biconnectivity (Section 5.2): the graph is connected and remains connected after the
removal of any single node. -/
def V2Con (c : Config S) : Prop :=
  c.graph.Connected ∧ ∀ v : c.V, (c.graph.induce {w | w ≠ v}).Connected

namespace Wheel

/-- Adjacency of the wheel on indices: the `c`-cycle `0 … c-1`, and `0` adjacent to all. -/
def wAdj (c x y : ℕ) : Prop := x ≠ y ∧ (x = 0 ∨ y = 0 ∨ (x < c ∧ y < c ∧ (x + 1 = y ∨ y + 1 = x)))

/-- The first ports of a cycle node `v_x`, `1 ≤ x ≤ c-1`: its successor, then its predecessor. -/
noncomputable def front (n c : ℕ) (x : Fin n) : List (Fin n) :=
  if h : 0 < x.val ∧ x.val < c ∧ c ≤ n ∧ 3 ≤ c then
    [⟨if x.val + 1 = c then 0 else x.val + 1, by split_ifs <;> omega⟩, ⟨x.val - 1, by omega⟩]
  else []

lemma front_spec {n c : ℕ} (x w : Fin n) (hw : w ∈ front n c x) : wAdj c x.val w.val := by
  unfold front at hw
  split_ifs at hw <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hw <;>
    rcases hw with rfl | rfl <;> unfold wAdj <;> (try dsimp only) <;> omega

lemma front_nodup {n c : ℕ} (x : Fin n) : (front n c x).Nodup := by
  unfold front
  split_ifs with h h' <;> simp [Fin.ext_iff] <;> omega

lemma front_succ {n c : ℕ} (x : Fin n) (h0 : 0 < x.val) (h1 : x.val + 1 < c) (hcn : c ≤ n)
    (hc : 3 ≤ c) : front n c x = [⟨x.val + 1, by omega⟩, ⟨x.val - 1, by omega⟩] := by
  unfold front
  rw [dite_eq_left ⟨h0, by omega, hcn, hc⟩]
  congr 2
  rw [ite_eq_right (by omega)]

lemma front_pred {n c : ℕ} (x : Fin n) (h0 : 0 < x.val) (h1 : x.val < c) (hcn : c ≤ n)
    (hc : 3 ≤ c) : ∃ y : Fin n, y.val ≠ x.val - 1 ∧ front n c x = [y, ⟨x.val - 1, by omega⟩] := by
  unfold front
  rw [dite_eq_left ⟨h0, h1, hcn, hc⟩]
  exact ⟨_, by dsimp only; split_ifs <;> omega, rfl⟩

/-- The wheel `G` with a `c`-cycle and `n` nodes (Figure 2a), identities `0, …, n-1`. -/
@[reducible] noncomputable def G (n c : ℕ) : Config ℕ :=
  mkConfig (fun x y : Fin n => wAdj c x.val y.val)
    (fun x y h => by simp only [wAdj] at h ⊢; omega) (fun x h => by simp [wAdj] at h)
    (front n c) front_spec front_nodup (fun x => x.val)

lemma G_adj {n c : ℕ} (x y : Fin n) : (G n c).graph.Adj x y ↔ wAdj c x.val y.val :=
  mkConfig_adj x y

/-- The node `v_{3k+1+b}` (endpoint `b` of the copy `H_k`). -/
def e {n c : ℕ} (hcn : c ≤ n) (k : Fin (c / 3)) (b : Bool) : Fin n :=
  ⟨3 * k.val + 1 + b.toNat, by have := k.2; cases b <;> simp <;> omega⟩

lemma e_val {n c : ℕ} (hcn : c ≤ n) (k : Fin (c / 3)) (b : Bool) :
    (e hcn k b).val = 3 * k.val + 1 + b.toNat := rfl

lemma port_e {n c : ℕ} (hcn : c ≤ n) (k : Fin (c / 3)) (b : Bool) :
    (G n c).port (e hcn k b) (e hcn k !b) = b.toNat := by
  have hk := k.2
  cases b
  · have hf := front_succ (n := n) (c := c) (e hcn k false) (by simp [e_val])
      (by simp [e_val]; omega) hcn (by omega)
    have he : e hcn k true = ⟨(e hcn k false).val + 1, by simp [e_val]; omega⟩ :=
      Fin.ext (by simp [e_val])
    have hmem : e hcn k (!false) ∈ front n c (e hcn k false) := by
      rw [hf, Bool.not_false, he]; simp
    refine (mkConfig_port (st := fun x : Fin n => x.val) hmem).trans ?_
    rw [hf, Bool.not_false, he, List.idxOf_cons_self]; rfl
  · obtain ⟨y, hy, hf⟩ := front_pred (n := n) (c := c) (e hcn k true) (by simp [e_val])
      (by simp [e_val]; omega) hcn (by omega)
    have he : e hcn k false = ⟨(e hcn k true).val - 1, by simp [e_val]; omega⟩ :=
      Fin.ext (by simp [e_val])
    have hmem : e hcn k (!true) ∈ front n c (e hcn k true) := by
      rw [hf, Bool.not_true, he]; simp
    refine (mkConfig_port (st := fun x : Fin n => x.val) hmem).trans ?_
    rw [hf, Bool.not_true, he, List.idxOf_cons_ne _ (fun h => hy (by rw [h])),
      List.idxOf_cons_self]
    rfl

/-- The `⌊c/3⌋` copies `H_k = {v_{3k+1}, v_{3k+2}}` (pairwise independent, port-preserving). -/
@[reducible] noncomputable def K (n c : ℕ) (hcn : c ≤ n) : Copies (G n c) (c / 3) :=
  edgeCopies (G n c) (c / 3) (e hcn)
    (fun i h => by simp [e, Fin.ext_iff] at h)
    (fun i j a b hij h => hij (Fin.ext (by
      rw [Fin.ext_iff, e_val, e_val] at h; cases a <;> cases b <;> simp at h <;> omega)))
    (fun i j a b hij h => hij (Fin.ext (by
      have h' := (G_adj _ _).1 h
      simp only [wAdj, e_val] at h'; cases a <;> cases b <;> simp at h' <;> omega)))
    (fun i => (G_adj _ _).2 (by have := i.2; simp only [wAdj, e_val]; simp; omega))
    (fun i j b => by rw [port_e, port_e])

lemma K_s {n c : ℕ} (hcn : c ≤ n) : (K n c hcn).s = 1 := edgeCopies_s

/-- Arcs of the copies `i` and `j` with left ends `A = 3i+1`, `B = 3j+1`, on indices. -/
def arcN (A B x w : ℕ) : Prop :=
  (x = A ∧ w = A + 1) ∨ (x = A + 1 ∧ w = A) ∨ (x = B ∧ w = B + 1) ∨ (x = B + 1 ∧ w = B)

/-- The swap `σ ∪ σ⁻¹` on indices. -/
def sw (A B y : ℕ) : ℕ :=
  if y = A then B else if y = A + 1 then B + 1 else if y = B then A else if y = B + 1 then A + 1
  else y

variable {n c : ℕ} {hcn : c ≤ n}

lemma isArc_val {i j : Fin (c / 3)} (x w : Fin n) :
    (K n c hcn).IsArc i j x w ↔ arcN (3 * i.val + 1) (3 * j.val + 1) x.val w.val := by
  refine Iff.trans edgeCopies_isArc ?_
  constructor
  · rintro ⟨k, hk, b, rfl, rfl⟩
    simp only [arcN, e_val]
    rcases hk with rfl | rfl <;> cases b <;> simp
  · intro h
    simp only [arcN] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨i, Or.inl rfl, false, Fin.ext (by simp [e_val, h1]), Fin.ext (by simp [e_val, h2])⟩
    · exact ⟨i, Or.inl rfl, true, Fin.ext (by simp [e_val, h1]), Fin.ext (by simp [e_val, h2])⟩
    · exact ⟨j, Or.inr rfl, false, Fin.ext (by simp [e_val, h1]), Fin.ext (by simp [e_val, h2])⟩
    · exact ⟨j, Or.inr rfl, true, Fin.ext (by simp [e_val, h1]), Fin.ext (by simp [e_val, h2])⟩

lemma swap_val {i j : Fin (c / 3)} (hij : i ≠ j) (y : Fin n) :
    ((K n c hcn).swap i j y).val = sw (3 * i.val + 1) (3 * j.val + 1) y.val := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have key : ∀ (k : Fin (c / 3)) (b : Bool), y.val = 3 * k.val + 1 + b.toNat →
      y = (K n c hcn).emb k b := fun k b h => Fin.ext (by rw [h]; rfl)
  by_cases h0 : y.val = 3 * i.val + 1
  · rw [key i false (by simp [h0]), (K n c hcn).swap_emb_left]
    simp only [e_val, sw, Bool.toNat_false]; split_ifs <;> omega
  by_cases h1 : y.val = 3 * i.val + 1 + 1
  · rw [key i true (by simp [h1]), (K n c hcn).swap_emb_left]
    simp only [e_val, sw, Bool.toNat_true]; split_ifs <;> omega
  by_cases h2 : y.val = 3 * j.val + 1
  · rw [key j false (by simp [h2]), (K n c hcn).swap_emb_right hij]
    simp only [e_val, sw, Bool.toNat_false]; split_ifs <;> omega
  by_cases h3 : y.val = 3 * j.val + 1 + 1
  · rw [key j true (by simp [h3]), (K n c hcn).swap_emb_right hij]
    simp only [e_val, sw, Bool.toNat_true]; split_ifs <;> omega
  rw [(K n c hcn).swap_of_not_mem]
  · simp [sw, h0, h1, h2, h3]
  · intro a ha; subst ha; cases a <;> simp [e_val] at h0 h1
  · intro a ha; subst ha; cases a <;> simp [e_val] at h2 h3

/-- **Adjacency in the crossing** of the copies `i ≠ j`, on indices. -/
lemma cross_adj_val {i j : Fin (c / 3)} (hij : i ≠ j) (x y : Fin n) :
    ((K n c hcn).cross i j hij).graph.Adj x y ↔
      (wAdj c x.val y.val ∧ ¬ arcN (3 * i.val + 1) (3 * j.val + 1) x.val y.val) ∨
        arcN (3 * i.val + 1) (3 * j.val + 1) x.val (sw (3 * i.val + 1) (3 * j.val + 1) y.val) := by
  rw [Copies.cross_adj_iff, G_adj, isArc_val, isArc_val, swap_val hij]

/-- The crossings are connected: `v₀` is still adjacent to every node. -/
lemma cross_connected {i j : Fin (c / 3)} (hij : i ≠ j) (hn : 0 < n) :
    ((K n c hcn).cross i j hij).Connected := by
  refine connected_of_descent (G := ((K n c hcn).cross i j hij).graph) (⟨0, hn⟩ : Fin n)
    (fun x : Fin n => x.val) (fun x hx => ⟨⟨0, hn⟩, ?_, ?_⟩)
  · have hx' : x.val ≠ 0 := fun h => hx (Fin.ext h)
    rw [cross_adj_val]
    left
    simp only [wAdj, arcN, true_or, or_true, and_true]
    omega
  · have hx' : x.val ≠ 0 := fun h => hx (Fin.ext h)
    simp only; omega

end Wheel

open Wheel

/-- `v2con(G) = TRUE` for the wheel `G` with `n ≥ 3` nodes. -/
lemma v2con_G {n : ℕ} (hn : 3 ≤ n) : V2Con (G n n) := by
  refine ⟨connected_of_descent (G := (G n n).graph) (⟨0, by omega⟩ : Fin n)
    (fun x : Fin n => x.val) (fun x hx => ⟨⟨0, by omega⟩, ?_, ?_⟩), fun v => ?_⟩
  · have hx' : x.val ≠ 0 := fun h => hx (Fin.ext h)
    rw [G_adj]; simp only [wAdj, true_or, or_true, and_true]; omega
  · have hx' : x.val ≠ 0 := fun h => hx (Fin.ext h)
    simp only; omega
  · by_cases hv : v.val = 0
    · -- `G - v₀` is the path `v₁ … v_{n-1}`
      refine connected_of_descent (⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff, hv] at h⟩ :
        {w : Fin n | w ≠ v}) (fun x => x.1.val) (fun x hx => ?_)
      have h0 : x.1.val ≠ 0 := fun h => x.2 (Fin.ext (by rw [h, hv]))
      have h1 : x.1.val ≠ 1 := fun h => hx (Subtype.ext (Fin.ext h))
      have hx2 := x.1.2
      refine ⟨⟨⟨x.1.val - 1, by omega⟩, fun h => by simp [Fin.ext_iff, hv] at h; omega⟩, ?_, ?_⟩
      · rw [SimpleGraph.induce_adj, G_adj]
        simp only [wAdj]; omega
      · simp only; omega
    · -- `G - v` is connected through `v₀`
      refine connected_of_descent (⟨⟨0, by omega⟩, fun h => hv (by rw [← h])⟩ :
        {w : Fin n | w ≠ v}) (fun x => x.1.val) (fun x hx => ?_)
      have h0 : x.1.val ≠ 0 := fun h => hx (Subtype.ext (Fin.ext h))
      refine ⟨⟨⟨0, by omega⟩, fun h => hv (by rw [← h])⟩, ?_, ?_⟩
      · rw [SimpleGraph.induce_adj, G_adj]
        simp only [wAdj, true_or, or_true, and_true]; omega
      · simp only; omega

/-- The crossings are not vertex-biconnected: `v₀` is an articulation point. -/
lemma not_v2con_cross {n : ℕ} {i j : Fin (n / 3)} (hij : i ≠ j) :
    ¬ V2Con ((K n n le_rfl).cross i j hij) := by
  rintro ⟨-, h⟩
  have hi := i.2
  have hj := j.2
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  set A := 3 * i.val + 1 with hA
  set B := 3 * j.val + 1 with hB
  set lo := min A B
  set hi := max A B
  let z : Fin n := ⟨0, by omega⟩
  have hc := (h z).preconnected
  let u : {w : Fin n | w ≠ z} := ⟨⟨lo + 1, by omega⟩, fun h => by simp [z, Fin.ext_iff] at h⟩
  let w : {w : Fin n | w ≠ z} := ⟨⟨lo, by omega⟩, fun h => by simp [z, Fin.ext_iff] at h; omega⟩
  have := mem_of_reachable_of_closed {x : {w : Fin n | w ≠ z} | lo < x.1.val ∧ x.1.val ≤ hi}
    (fun x y hxy hx => ?_) (hc u w) (by simp [u]; omega)
  · simp [w] at this
  · have hy : y.1.val ≠ 0 := fun h => y.2 (Fin.ext h)
    rw [SimpleGraph.induce_adj, cross_adj_val] at hxy
    simp only [Set.mem_ofPred_eq] at hx ⊢
    simp only [wAdj, arcN, sw] at hxy
    split_ifs at hxy <;> omega

/-- The crossings refute `(F_con, v2con)`. -/
lemma refuted_cross_v2con {n : ℕ} (hn : 3 ≤ n) {i j : Fin (n / 3)} (hij : i ≠ j) :
    Refuted Fcon V2Con ((K n n le_rfl).cross i j hij) :=
  Or.inl ⟨cross_connected hij (by omega), not_v2con_cross hij⟩

lemma card_wheelG (n c : ℕ) : Fintype.card (G n c).V = n := Fintype.card_fin n

lemma wheelG_state_injective (n c : ℕ) : Function.Injective (G n c).state :=
  fun _ _ h => Fin.ext h

/-- **Theorem 5.2 of [BFP15]** (deterministic lower bound). Let `F` be any family containing the
connected configurations with distinct identities (e.g. `F_con` itself). Every proof-labeling
scheme for `(F, v2con)` whose labels on legal `n`-node configurations have at most `κ(n)` bits
satisfies `log₂ ⌊n/3⌋ ≤ 2 (κ(n) + 1)`, i.e. `κ(n) = Ω(log n)`. -/
theorem thm_5_2_det {F : Config ℕ → Prop} (hFF : ∀ c, Fcon c → Function.Injective c.state → F c)
    {ver : Verifier ℕ} {prover : ∀ c : Config ℕ, c.V → List Bool}
    (h : IsPLS ver prover F V2Con) (κ : ℕ → ℕ)
    (hκ : LabelBound prover F V2Con (fun c => κ (Fintype.card c.V))) (n : ℕ) (hn : 3 ≤ n) :
    Real.logb 2 (n / 3 : ℕ) ≤ 2 * (κ n + 1) := by
  have hG := v2con_G hn
  have hFG := hFF _ hG.1 (wheelG_state_injective n n)
  have := thm_4_4_log h hFG hG (K n n le_rfl) (κ n)
    (fun v => by simpa [card_wheelG] using hκ _ hFG hG v)
    (fun i j hij => (refuted_cross_v2con hn hij).mono hFF (wheelG_state_injective n n))
  simpa [K_s] using this

/-- **Theorem 5.2 of [BFP15]** (randomized lower bound, one-sided schemes). Let `F` be any family
containing the connected configurations with distinct identities. Every one-sided RPLS for
`(F, v2con)` whose certificates on legal `n`-node configurations have at most `κ(n)` bits
satisfies `log₂ ⌊n/3⌋ ≤ 2 · 2^(κ(n)+1)`, i.e. `κ(n) = Ω(log log n)`. -/
theorem thm_5_2_rand {F : Config ℕ → Prop} (hFF : ∀ c, Fcon c → Function.Injective c.state → F c)
    {L : Type} {σ : RScheme ℕ L} {prover : ∀ c : Config ℕ, c.V → L}
    (h : IsOneSided σ prover F V2Con) (κ : ℕ → ℕ)
    (hκ : CertBound σ prover F V2Con (fun c => κ (Fintype.card c.V))) (n : ℕ) (hn : 3 ≤ n) :
    Real.logb 2 (n / 3 : ℕ) ≤ 2 * 2 ^ (κ n + 1) := by
  have hG := v2con_G hn
  have hFG := hFF _ hG.1 (wheelG_state_injective n n)
  have := prop_4_8_log h hFG hG (K n n le_rfl) (κ n)
    (fun v ω i hi => by simpa [card_wheelG] using hκ _ hFG hG v ω i hi)
    (fun i j hij => (refuted_cross_v2con hn hij).mono hFF (wheelG_state_injective n n))
  simpa [K_s] using this

end Podc.RandomizedPLS
