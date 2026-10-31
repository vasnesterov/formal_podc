import Papers.PODC2011.LocallyCheckableProofs.Basic

/-!
# The `G₁ ⊛ G₂` construction of Section 6.1 (Göös–Suomela)

For graphs `H₁ H₂` on `Fin k` and a path length `p ≥ 1`, `star p k H₁ H₂` is the unlabelled
instance on the nodes `{1, …, p + 2k}` consisting of

* a copy of `H₁` on `{p+1, …, p+k}` (vertex `a` of `H₁` is the node `p+1+a`),
* a copy of `H₂` on `{p+k+1, …, p+2k}` (vertex `a` of `H₂` is the node `p+k+1+a`),
* the path `(p+1, 1, 2, …, p, p+k+1)` joining the two copies (attached at vertex `0`).

The paper uses `p = k`; a general `p` lets us realise every number of nodes `n`.

Main results:
* `star_conn`: the instance is connected if `H₁`, `H₂` are.
* `glue_accept`: the gluing argument: if all nodes accept `(H₁ ⊛ H₁, P₁)` and `(H₂ ⊛ H₂, P₂)` and
  the proofs agree on the path nodes `1, …, 2r+1`, then all nodes accept `H₁ ⊛ H₂` with the
  glued proof.
* `swap`: `H ⊛ H` has the involutive automorphism reversing the path and swapping the copies.
* `PathEnum`, `PathEnum.rigid`, `PathEnum.end_cases`: automorphisms preserving a set of nodes that
  induces a path are the identity or the reversal on that path.
* `exists_perm_of_iso`, `exists_iso_of_perm`: automorphisms of the induced graph on the nodes vs.
  permutations of `ℕ` preserving the graph.
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset

namespace StarCons

/-- The path part of `H₁ ⊛ H₂`: the path `(p+1, 1, 2, …, p, p+k+1)` (for `p ≥ 1`, `k ≥ 1`). -/
def pathRel (p k x y : ℕ) : Prop :=
  (1 ≤ x ∧ x < p ∧ y = x + 1) ∨ (x = 1 ∧ 1 ≤ p ∧ 0 < k ∧ y = p + 1) ∨
    (x = p ∧ 1 ≤ p ∧ 0 < k ∧ y = p + k + 1)

/-- Shift `Fin k` to `{o, …, o+k-1}`. -/
def sh (k o : ℕ) : Fin k ↪ ℕ := ⟨fun a => o + a, fun a b h => Fin.ext (by simpa using h)⟩

/-- The graph of `H₁ ⊛ H₂`. -/
def graph (p k : ℕ) (H₁ H₂ : SimpleGraph (Fin k)) : SimpleGraph ℕ :=
  fromRel (pathRel p k) ⊔ H₁.map (sh k (p + 1)) ⊔ H₂.map (sh k (p + k + 1))

lemma pathRel_ne {p k x y : ℕ} (h : pathRel p k x y) : x ≠ y := by
  unfold pathRel at h; omega

lemma graph_adj {p k : ℕ} {H₁ H₂ : SimpleGraph (Fin k)} {x y : ℕ} :
    (graph p k H₁ H₂).Adj x y ↔ pathRel p k x y ∨ pathRel p k y x ∨
      (∃ a b : Fin k, H₁.Adj a b ∧ x = p + 1 + a ∧ y = p + 1 + b) ∨
      (∃ a b : Fin k, H₂.Adj a b ∧ x = p + k + 1 + a ∧ y = p + k + 1 + b) := by
  simp only [graph, sup_adj, fromRel_adj, map_adj, sh]
  constructor
  · rintro ((⟨-, h | h⟩ | ⟨a, b, h, rfl, rfl⟩) | ⟨a, b, h, rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, h, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a, b, h, rfl, rfl⟩))
  · rintro (h | h | ⟨a, b, h, rfl, rfl⟩ | ⟨a, b, h, rfl, rfl⟩)
    · exact Or.inl (Or.inl ⟨pathRel_ne h, Or.inl h⟩)
    · exact Or.inl (Or.inl ⟨(pathRel_ne h).symm, Or.inr h⟩)
    · exact Or.inl (Or.inr ⟨a, b, h, rfl, rfl⟩)
    · exact Or.inr ⟨a, b, h, rfl, rfl⟩

lemma graph_adj_mem {p k : ℕ} {H₁ H₂ : SimpleGraph (Fin k)} {x y : ℕ}
    (h : (graph p k H₁ H₂).Adj x y) : 1 ≤ x ∧ x ≤ p + 2 * k := by
  rw [graph_adj] at h
  unfold pathRel at h
  rcases h with h | h | ⟨a, b, -, rfl, rfl⟩ | ⟨a, b, -, rfl, rfl⟩
  · omega
  · omega
  · have := a.isLt; omega
  · have := a.isLt; omega

/-- The instance `H₁ ⊛ H₂` with a connecting path of `p` nodes. -/
def star (p k : ℕ) (H₁ H₂ : SimpleGraph (Fin k)) : Inst Unit where
  V := Icc 1 (p + 2 * k)
  G := graph p k H₁ H₂
  sub := fun _ _ h => by simpa using graph_adj_mem h
  S := ⊥
  S_le := bot_le
  lab := fun _ => ()

variable {p k : ℕ} {H₁ H₂ : SimpleGraph (Fin k)}

@[simp] lemma star_V : (star p k H₁ H₂).V = Icc 1 (p + 2 * k) := rfl
@[simp] lemma star_G : (star p k H₁ H₂).G = graph p k H₁ H₂ := rfl

lemma star_n : (star p k H₁ H₂).n = p + 2 * k := by simp [Inst.n]

lemma star_plain : (star p k H₁ H₂).Plain := rfl

lemma star_idBound : (star p k H₁ H₂).IdBound 1 := by
  intro v hv; simp only [star_V, mem_Icc] at hv; rw [star_n, pow_one]; exact hv

/-! ### Neighbourhoods of path and copy nodes -/

/-- The (at most two) neighbours of a path node. -/
lemma path_nbr {x y : ℕ} (hx1 : 1 ≤ x) (hxp : x ≤ p) (h : (graph p k H₁ H₂).Adj x y) :
    y = (if x = 1 then p + 1 else x - 1) ∨ y = (if x = p then p + k + 1 else x + 1) := by
  rw [graph_adj] at h
  unfold pathRel at h
  rcases h with h | h | ⟨a, b, -, rfl, rfl⟩ | ⟨a, b, -, rfl, rfl⟩
  · split_ifs <;> omega
  · split_ifs <;> omega
  · omega
  · omega

/-- The offset of copy `b` (`false`: the copy of `H₁`, `true`: the copy of `H₂`). -/
def off (p k : ℕ) : Bool → ℕ
  | false => p + 1
  | true => p + k + 1

@[simp] lemma off_false : off p k false = p + 1 := rfl
@[simp] lemma off_true : off p k true = p + k + 1 := rfl

/-- The graph in copy `b`. -/
def hc (H₁ H₂ : SimpleGraph (Fin k)) : Bool → SimpleGraph (Fin k)
  | false => H₁
  | true => H₂

lemma copy_adj (hp : 1 ≤ p) (b : Bool) (a c : Fin k) :
    (graph p k H₁ H₂).Adj (off p k b + a) (off p k b + c) ↔ (hc H₁ H₂ b).Adj a c := by
  rw [graph_adj]
  unfold pathRel
  have := a.isLt; have := c.isLt
  cases b <;> simp only [off, hc]
  · constructor
    · rintro (h | h | ⟨a', c', h, e1, e2⟩ | ⟨a', c', h, e1, e2⟩)
      · omega
      · omega
      · have ha : a = a' := Fin.ext (by omega)
        have hc' : c = c' := Fin.ext (by omega)
        subst ha hc'; exact h
      · omega
    · intro h; exact Or.inr (Or.inr (Or.inl ⟨a, c, h, rfl, rfl⟩))
  · constructor
    · rintro (h | h | ⟨a', c', h, e1, e2⟩ | ⟨a', c', h, e1, e2⟩)
      · omega
      · omega
      · omega
      · have ha : a = a' := Fin.ext (by omega)
        have hc' : c = c' := Fin.ext (by omega)
        subst ha hc'; exact h
    · intro h; exact Or.inr (Or.inr (Or.inr ⟨a, c, h, rfl, rfl⟩))

/-- A non-path neighbour of a node of copy `b` lies in copy `b`. -/
lemma copy_nbr (b : Bool) (a : Fin k) {y : ℕ} (h : (graph p k H₁ H₂).Adj (off p k b + a) y)
    (hy : ¬ (1 ≤ y ∧ y ≤ p)) : ∃ c : Fin k, y = off p k b + c := by
  rw [graph_adj] at h
  unfold pathRel at h
  have := a.isLt
  cases b <;> simp only [off] at h ⊢
  · rcases h with h | h | ⟨a', c', -, e1, rfl⟩ | ⟨a', c', -, e1, rfl⟩
    · omega
    · omega
    · exact ⟨c', rfl⟩
    · omega
  · rcases h with h | h | ⟨a', c', -, e1, rfl⟩ | ⟨a', c', -, e1, rfl⟩
    · omega
    · omega
    · omega
    · exact ⟨c', rfl⟩

/-! ### Connectivity -/

/-- The copy of `H₁` is a subgraph. -/
def hom₁ (p k : ℕ) (H₁ H₂ : SimpleGraph (Fin k)) : H₁ →g graph p k H₁ H₂ :=
  ⟨fun a => p + 1 + a, fun {a b} h => graph_adj.2 (Or.inr (Or.inr (Or.inl ⟨a, b, h, rfl, rfl⟩)))⟩

/-- The copy of `H₂` is a subgraph. -/
def hom₂ (p k : ℕ) (H₁ H₂ : SimpleGraph (Fin k)) : H₂ →g graph p k H₁ H₂ :=
  ⟨fun a => p + k + 1 + a, fun {a b} h =>
    graph_adj.2 (Or.inr (Or.inr (Or.inr ⟨a, b, h, rfl, rfl⟩)))⟩

lemma reach_path : ∀ i, 1 ≤ i → i ≤ p → (graph p k H₁ H₂).Reachable 1 i := by
  intro i
  induction i with
  | zero => omega
  | succ i ih =>
    intro _ hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rfl
    · exact (ih hi0 (by omega)).trans
        (Adj.reachable (graph_adj.2 (Or.inl (Or.inl ⟨hi0, by omega, rfl⟩))))

/-- `H₁ ⊛ H₂` is connected if `H₁` and `H₂` are. -/
lemma star_conn (hp : 1 ≤ p) (hk : 0 < k) (h₁ : H₁.Connected) (h₂ : H₂.Connected) :
    (star p k H₁ H₂).Conn := by
  have key : ∀ v ∈ (star p k H₁ H₂).V, (graph p k H₁ H₂).Reachable 1 v := by
    intro v hv
    simp only [star_V, mem_Icc] at hv
    by_cases hvp : v ≤ p
    · exact reach_path v hv.1 hvp
    by_cases hvk : v ≤ p + k
    · have r1 : (graph p k H₁ H₂).Reachable 1 (p + 1 + (⟨0, hk⟩ : Fin k)) :=
        Adj.reachable (graph_adj.2 (Or.inl (Or.inr (Or.inl ⟨rfl, hp, hk, rfl⟩))))
      have r2 := (h₁.preconnected (⟨0, hk⟩ : Fin k) ⟨v - p - 1, by omega⟩).map (hom₁ p k H₁ H₂)
      have : v = p + 1 + ((⟨v - p - 1, by omega⟩ : Fin k) : ℕ) := by simp; omega
      rw [this]; exact r1.trans r2
    · have r1 : (graph p k H₁ H₂).Reachable 1 (p + k + 1 + (⟨0, hk⟩ : Fin k)) :=
        (reach_path p hp le_rfl).trans
          (Adj.reachable (graph_adj.2 (Or.inl (Or.inr (Or.inr ⟨rfl, hp, hk, rfl⟩)))))
      have r2 := (h₂.preconnected (⟨0, hk⟩ : Fin k) ⟨v - p - k - 1, by omega⟩).map
        (hom₂ p k H₁ H₂)
      have : v = p + k + 1 + ((⟨v - p - k - 1, by omega⟩ : Fin k) : ℕ) := by simp; omega
      rw [this]; exact r1.trans r2
  refine ⟨⟨1, by simp; omega⟩, fun u hu v hv => (key u hu).symm.trans (key v hv)⟩

/-! ### Locality: the position along the path -/

/-- The position of a node along the path: `0` on the copy of `H₁`, `i` on the path node `i`,
`p + 1` on the copy of `H₂`. Adjacent nodes have positions differing by at most one. -/
def pos (p k x : ℕ) : ℕ := if x ≤ p then x else if x ≤ p + k then 0 else p + 1

lemma pos_adj {x y : ℕ} (h : (graph p k H₁ H₂).Adj x y) : pos p k y ≤ pos p k x + 1 := by
  rw [graph_adj] at h
  unfold pathRel at h
  unfold pos
  rcases h with h | h | ⟨a, b, -, rfl, rfl⟩ | ⟨a, b, -, rfl, rfl⟩
  · split_ifs <;> omega
  · split_ifs <;> omega
  · have := a.isLt; have := b.isLt; split_ifs <;> omega
  · have := a.isLt; have := b.isLt; split_ifs <;> omega

lemma pos_walk {x y : ℕ} (w : (graph p k H₁ H₂).Walk x y) :
    pos p k y ≤ pos p k x + w.length ∧ pos p k x ≤ pos p k y + w.length := by
  induction w with
  | nil => simp
  | cons h w ih =>
    have h1 := pos_adj h
    have h2 := pos_adj h.symm
    simp only [Walk.length_cons]
    omega

lemma pos_ball {v x r : ℕ} (h : x ∈ ball (star p k H₁ H₂) v r) :
    pos p k x ≤ pos p k v + r ∧ pos p k v ≤ pos p k x + r := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨h1, h2⟩ := pos_walk (p := p) (k := k) (H₁ := H₁) (H₂ := H₂) w
  exact ⟨h1.trans (Nat.add_le_add_left hw _), h2.trans (Nat.add_le_add_left hw _)⟩

/-- Away from the copy of `H₂`, the graph does not depend on `H₂`. -/
lemma adj_congr_right {x y : ℕ} (hx : x < p + k + 1) (H₂' : SimpleGraph (Fin k)) :
    (graph p k H₁ H₂).Adj x y ↔ (graph p k H₁ H₂').Adj x y := by
  simp only [graph_adj]
  constructor
  · rintro (h | h | h | ⟨a, b, h, rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · omega
  · rintro (h | h | h | ⟨a, b, h, rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · omega

/-- Away from the copy of `H₁`, the graph does not depend on `H₁`. -/
lemma adj_congr_left {x y : ℕ} (hx : x < p + 1 ∨ p + k + 1 ≤ x) (H₁' : SimpleGraph (Fin k)) :
    (graph p k H₁ H₂).Adj x y ↔ (graph p k H₁' H₂).Adj x y := by
  simp only [graph_adj]
  constructor
  · rintro (h | h | ⟨a, b, h, rfl, rfl⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have := a.isLt; omega
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | ⟨a, b, h, rfl, rfl⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have := a.isLt; omega
    · exact Or.inr (Or.inr (Or.inr h))

/-- The glued proof: `P₁` up to position `r + 1`, `P₂` beyond. -/
def gluedProof (p k r : ℕ) (P₁ P₂ : Proof) : Proof :=
  fun x => if pos p k x ≤ r + 1 then P₁ x else P₂ x

/-- **The gluing argument** (proof of Theorem 6.1). If all nodes accept `H₁ ⊛ H₁` with proof
`P₁` and `H₂ ⊛ H₂` with proof `P₂`, and the two proofs agree on the path nodes `1, …, 2r+1`, then
all nodes accept `H₁ ⊛ H₂` with the glued proof. -/
theorem glue_accept {r : ℕ} {A : Verifier Unit} (hA : IsLocal r A) (hp : 2 * r + 1 ≤ p)
    {P₁ P₂ : Proof} (h₁ : AllAccept A (star p k H₁ H₁) P₁) (h₂ : AllAccept A (star p k H₂ H₂) P₂)
    (hag : ∀ i, 1 ≤ i → i ≤ 2 * r + 1 → P₁ i = P₂ i) :
    AllAccept A (star p k H₁ H₂) (gluedProof p k r P₁ P₂) := by
  intro v hv
  by_cases hpv : pos p k v ≤ r + 1
  · rw [hA _ _ (star p k H₁ H₁) P₁ v ?_]
    · exact h₁ v hv
    refine viewEq_of_nbrs (fun x hx y => ?_) (fun x _ y => Iff.rfl) (fun x _ => Iff.rfl)
      (fun x _ => rfl) (fun x hx => ?_)
    · have := pos_ball hx
      have h2 : pos p k x ≤ 2 * r + 1 := by omega
      have hx' : x < p + k + 1 := by unfold pos at h2; split_ifs at h2 <;> omega
      exact adj_congr_right hx' H₁
    · have := pos_ball hx
      have h2 : pos p k x ≤ 2 * r + 1 := by omega
      unfold gluedProof
      split_ifs with h
      · rfl
      · have hxp : x ≤ p := by unfold pos at h h2; split_ifs at h h2 <;> omega
        have : pos p k x = x := by unfold pos; simp [hxp]
        exact (hag x (by omega) (by omega)).symm
  · rw [hA _ _ (star p k H₂ H₂) P₂ v ?_]
    · exact h₂ v hv
    refine viewEq_of_nbrs (fun x hx y => ?_) (fun x _ y => Iff.rfl) (fun x _ => Iff.rfl)
      (fun x _ => rfl) (fun x hx => ?_)
    · have := pos_ball hx
      have h2 : 2 ≤ pos p k x := by omega
      have hx' : x < p + 1 ∨ p + k + 1 ≤ x := by unfold pos at h2; split_ifs at h2 <;> omega
      exact adj_congr_left hx' H₂
    · have := pos_ball hx
      have h2 : 2 ≤ pos p k x := by omega
      unfold gluedProof
      split_ifs with h
      · have hxp : x ≤ p := by unfold pos at h h2; split_ifs at h h2 <;> omega
        have : pos p k x = x := by unfold pos; simp [hxp]
        exact hag x (by omega) (by omega)
      · rfl

/-! ### Automorphisms -/

/-- A permutation of `ℕ` that preserves the graph and the node set of `I` (it restricts to an
automorphism of `I`, see `exists_iso_of_perm`). -/
structure IsAut {L : Type*} (I : Inst L) (ψ : Equiv.Perm ℕ) : Prop where
  adj : ∀ x y, I.G.Adj (ψ x) (ψ y) ↔ I.G.Adj x y
  mem : ∀ x, ψ x ∈ I.V ↔ x ∈ I.V

lemma IsAut.symm {L : Type*} {I : Inst L} {ψ : Equiv.Perm ℕ} (h : IsAut I ψ) : IsAut I ψ.symm :=
  ⟨fun x y => by rw [← h.adj]; simp, fun x => by rw [← h.mem]; simp⟩

/-- An automorphism of the graph induced on the nodes extends (by the identity) to a permutation
of `ℕ` preserving the instance. -/
lemma exists_perm_of_iso {L : Type*} (I : Inst L)
    (φ : I.G.induce (I.V : Set ℕ) ≃g I.G.induce (I.V : Set ℕ)) :
    ∃ ψ : Equiv.Perm ℕ, IsAut I ψ ∧ ∀ v : (I.V : Set ℕ), ψ v = φ v := by
  classical
  let f : (I.G.induce (I.V : Set ℕ) ≃g I.G.induce (I.V : Set ℕ)) → ℕ → ℕ := fun φ x =>
    if h : x ∈ I.V then (φ ⟨x, h⟩ : ℕ) else x
  have hf : ∀ φ : I.G.induce (I.V : Set ℕ) ≃g I.G.induce (I.V : Set ℕ), ∀ x,
      f φ.symm (f φ x) = x := by
    intro φ x
    by_cases hx : x ∈ I.V
    · have : ((φ ⟨x, hx⟩ : (I.V : Set ℕ)) : ℕ) ∈ I.V := (φ ⟨x, hx⟩).2
      simp [f, hx, this]
    · simp [f, hx]
  let ψ : Equiv.Perm ℕ := ⟨f φ, f φ.symm, hf φ, fun x => by simpa using hf φ.symm x⟩
  have hψ : ∀ x, ψ x = f φ x := fun _ => rfl
  have hmem : ∀ x, ψ x ∈ I.V ↔ x ∈ I.V := by
    intro x
    by_cases hx : x ∈ I.V
    · simp only [hψ, f, hx, dite_true, iff_true]; exact (φ ⟨x, hx⟩).2
    · simp [hψ, f, hx]
  refine ⟨ψ, ⟨fun x y => ?_, hmem⟩, fun v => by simp [hψ, f]⟩
  by_cases hx : x ∈ I.V
  · by_cases hy : y ∈ I.V
    · have := φ.map_adj_iff (v := ⟨x, hx⟩) (w := ⟨y, hy⟩)
      simp only [comap_adj, Function.Embedding.coe_subtype] at this
      simpa [hψ, f, hx, hy] using this
    · have h1 : ¬ I.G.Adj x y := fun h => hy (I.sub' h)
      have h2 : ¬ I.G.Adj (ψ x) (ψ y) := fun h => hy ((hmem y).1 (I.sub' h))
      simp [h1, h2]
  · have h1 : ¬ I.G.Adj x y := fun h => hx (I.sub h)
    have h2 : ¬ I.G.Adj (ψ x) (ψ y) := fun h => hx ((hmem x).1 (I.sub h))
    simp [h1, h2]

/-- A permutation of `ℕ` preserving the instance restricts to an automorphism of the graph
induced on the nodes. -/
lemma exists_iso_of_perm {L : Type*} {I : Inst L} {ψ : Equiv.Perm ℕ} (h : IsAut I ψ) :
    ∃ φ : I.G.induce (I.V : Set ℕ) ≃g I.G.induce (I.V : Set ℕ), ∀ v, (φ v : ℕ) = ψ v :=
  ⟨{ toFun := fun v => ⟨ψ v, (h.mem v).2 v.2⟩
     invFun := fun v => ⟨ψ.symm v, (h.symm.mem v).2 v.2⟩
     left_inv := fun v => by simp
     right_inv := fun v => by simp
     map_rel_iff' := by intro a b; simp [h.adj] }, fun v => rfl⟩

/-! ### Rigidity of induced paths -/

/-- `x 0, …, x L` enumerates (without repetition) the nodes satisfying `Q`, and among them the
adjacencies are exactly those of the path `x 0 — x 1 — ⋯ — x L`. -/
structure PathEnum (G : SimpleGraph ℕ) (Q : ℕ → Prop) (L : ℕ) (x : ℕ → ℕ) : Prop where
  mem : ∀ v, Q v ↔ ∃ i ≤ L, x i = v
  inj : ∀ i ≤ L, ∀ j ≤ L, x i = x j → i = j
  adj : ∀ i ≤ L, ∀ j ≤ L, (G.Adj (x i) (x j) ↔ (j = i + 1 ∨ i = j + 1))

section PathEnum

variable {G : SimpleGraph ℕ} {Q : ℕ → Prop} {L : ℕ} {x y : ℕ → ℕ} {ψ : Equiv.Perm ℕ}

lemma PathEnum.rev (h : PathEnum G Q L x) : PathEnum G Q L (fun i => x (L - i)) where
  mem v := by
    rw [h.mem]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨L - i, by omega, by congr 1; omega⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨L - i, by omega, rfl⟩
  inj i hi j hj e := by have := h.inj _ (by omega) _ (by omega) e; omega
  adj i hi j hj := by rw [h.adj _ (by omega) _ (by omega)]; omega

lemma PathEnum.exists_of_q (h : PathEnum G Q L x) {v : ℕ} (hv : Q v) : ∃ j ≤ L, x j = v :=
  (h.mem v).1 hv

/-- An automorphism preserving `Q` that maps `x 0` to `y 0` maps `x i` to `y i`. -/
lemma PathEnum.rigid (hx : PathEnum G Q L x) (hy : PathEnum G Q L y)
    (hadj : ∀ a b, G.Adj (ψ a) (ψ b) ↔ G.Adj a b) (hQ : ∀ a, Q (ψ a) ↔ Q a)
    (h0 : ψ (x 0) = y 0) : ∀ i ≤ L, ψ (x i) = y i := by
  have img : ∀ i ≤ L, ∃ j ≤ L, ψ (x i) = y j := by
    intro i hi
    obtain ⟨j, hj, e⟩ := hy.exists_of_q ((hQ _).2 ((hx.mem _).2 ⟨i, hi, rfl⟩))
    exact ⟨j, hj, e.symm⟩
  have main : ∀ i, i ≤ L → ψ (x i) = y i ∧ (i + 1 ≤ L → ψ (x (i + 1)) = y (i + 1)) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨h0, fun h1 => ?_⟩
      obtain ⟨j, hj, e⟩ := img 1 h1
      have := (hadj (x 0) (x 1)).2 ((hx.adj 0 (by omega) 1 h1).2 (by omega))
      rw [h0, e, hy.adj 0 (by omega) j hj] at this
      rw [e]; congr 1; omega
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      refine ⟨h2 hi, fun hi2 => ?_⟩
      obtain ⟨j, hj, e⟩ := img (i + 2) hi2
      have := (hadj (x (i + 1)) (x (i + 2))).2 ((hx.adj _ hi _ hi2).2 (by omega))
      rw [h2 hi, e, hy.adj _ hi j hj] at this
      rcases this with h | h
      · subst h; exact e
      · exfalso
        have hji : j = i := by omega
        subst hji
        have := hx.inj _ hi2 _ (by omega) (ψ.injective (e.trans h1.symm))
        omega
  exact fun i hi => (main i hi).1

/-- An automorphism preserving `Q` maps the end `x 0` of the path to one of its ends. -/
lemma PathEnum.end_cases (hx : PathEnum G Q L x)
    (hadj : ∀ a b, G.Adj (ψ a) (ψ b) ↔ G.Adj a b) (hQ : ∀ a, Q (ψ a) ↔ Q a) :
    ψ (x 0) = x 0 ∨ ψ (x 0) = x L := by
  obtain ⟨j, hj, e⟩ := hx.exists_of_q ((hQ _).2 ((hx.mem _).2 ⟨0, by omega, rfl⟩))
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact Or.inl e.symm
  rcases eq_or_lt_of_le hj with rfl | hjL
  · exact Or.inr e.symm
  exfalso
  -- the preimages of the two path-neighbours of `x j` are both `x 1`
  have pre : ∀ i ≤ L, (i = j + 1 ∨ j = i + 1) → ψ.symm (x i) = x 1 := by
    intro i hi hij
    obtain ⟨l, hl, el⟩ := hx.exists_of_q ((hQ (ψ.symm (x i))).1
      (by rw [Equiv.apply_symm_apply]; exact (hx.mem _).2 ⟨i, hi, rfl⟩))
    have := (hadj (ψ.symm (x i)) (x 0)).1 (by
      rw [Equiv.apply_symm_apply, ← e, hx.adj _ hi _ hj]; omega)
    rw [← el, hx.adj _ hl _ (by omega)] at this
    rw [← el]; congr 1; omega
  have := ψ.symm.injective ((pre (j - 1) (by omega) (by omega)).trans
    (pre (j + 1) (by omega) (by omega)).symm)
  have := hx.inj _ (by omega) _ (by omega) this
  omega

end PathEnum

/-! ### The swap automorphism of `H ⊛ H` -/

/-- Reverse the path and swap the two copies. -/
def swapFun (p k x : ℕ) : ℕ :=
  if 1 ≤ x ∧ x ≤ p then p + 1 - x else if p < x ∧ x ≤ p + k then x + k
  else if p + k < x ∧ x ≤ p + 2 * k then x - k else x

lemma swapFun_spec (x : ℕ) :
    (1 ≤ x ∧ x ≤ p ∧ swapFun p k x = p + 1 - x) ∨ (p < x ∧ x ≤ p + k ∧ swapFun p k x = x + k) ∨
    (p + k < x ∧ x ≤ p + 2 * k ∧ swapFun p k x = x - k) ∨
    ((x < 1 ∨ p + 2 * k < x) ∧ swapFun p k x = x) := by
  unfold swapFun; split_ifs <;> omega

lemma swapFun_swapFun (x : ℕ) : swapFun p k (swapFun p k x) = x := by
  rcases swapFun_spec (p := p) (k := k) x with h | h | h | h <;>
  rcases swapFun_spec (p := p) (k := k) (swapFun p k x) with h' | h' | h' | h' <;> omega

/-- The involution of `H ⊛ H` reversing the path and swapping the copies. -/
def swap (p k : ℕ) : Equiv.Perm ℕ :=
  Function.Involutive.toPerm _ (swapFun_swapFun (p := p) (k := k))

@[simp] lemma swap_apply (x : ℕ) : swap p k x = swapFun p k x := rfl

lemma swapFun_path {x : ℕ} (h1 : 1 ≤ x) (h2 : x ≤ p) : swapFun p k x = p + 1 - x := by
  unfold swapFun; split_ifs <;> omega

lemma swapFun_c1 {x : ℕ} (h1 : p < x) (h2 : x ≤ p + k) : swapFun p k x = x + k := by
  unfold swapFun; split_ifs <;> omega

lemma swapFun_c2 {x : ℕ} (h1 : p + k < x) (h2 : x ≤ p + 2 * k) : swapFun p k x = x - k := by
  unfold swapFun; split_ifs <;> omega

lemma swap_pathRel {x y : ℕ} (h : pathRel p k x y) :
    pathRel p k (swapFun p k x) (swapFun p k y) ∨ pathRel p k (swapFun p k y) (swapFun p k x) := by
  rcases h with ⟨h1, h2, rfl⟩ | ⟨rfl, h1, h2, rfl⟩ | ⟨rfl, h1, h2, rfl⟩
  · right; rw [swapFun_path h1 h2.le, swapFun_path (by omega) h2]; left; omega
  · left; rw [swapFun_path le_rfl h1, swapFun_c1 (by omega) (by omega)]
    right; right; omega
  · left; rw [swapFun_path h1 le_rfl, swapFun_c2 (by omega) (by omega)]
    right; left; omega

lemma swap_adj_of_adj {H : SimpleGraph (Fin k)} {x y : ℕ} (h : (graph p k H H).Adj x y) :
    (graph p k H H).Adj (swapFun p k x) (swapFun p k y) := by
  rw [graph_adj] at h ⊢
  rcases h with h | h | ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
  · rcases swap_pathRel h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases swap_pathRel h with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inl h'
  · have := a.isLt; have := b.isLt
    refine Or.inr (Or.inr (Or.inr ⟨a, b, hab, ?_, ?_⟩))
    · rw [swapFun_c1 (by omega) (by omega)]; omega
    · rw [swapFun_c1 (by omega) (by omega)]; omega
  · have := a.isLt; have := b.isLt
    refine Or.inr (Or.inr (Or.inl ⟨a, b, hab, ?_, ?_⟩))
    · rw [swapFun_c2 (by omega) (by omega)]; omega
    · rw [swapFun_c2 (by omega) (by omega)]; omega

/-- The swap is an automorphism of `H ⊛ H`. -/
lemma swap_isAut (H : SimpleGraph (Fin k)) : IsAut (star p k H H) (swap p k) where
  adj x y := by
    refine ⟨fun h => ?_, swap_adj_of_adj⟩
    simpa [swapFun_swapFun] using swap_adj_of_adj h
  mem x := by
    have := swapFun_spec (p := p) (k := k) x
    simp only [star_V, mem_Icc, swap_apply]; omega

/-! ### The counting (pigeonhole) part of the argument -/

/-- **Pigeonhole + gluing.** Let `𝒢` be a family of graphs on `Fin k` such that every `H i ⊛ H i`
(`i ∈ 𝒢`) has a proof of size `≤ S` accepted by all nodes, but `H i ⊛ H j` is rejected for every
proof whenever `R i j`. If at most `M` members `j` of `𝒢` fail `R j i` for each `i`, then
`|𝒢| ≤ M · 2^((S+1)(2r+1))`: otherwise two members `i`, `j` with `R i j` have proofs agreeing on the
path nodes `1, …, 2r+1`, and the glued proof is accepted on `H i ⊛ H j` (`glue_accept`). -/
theorem card_le_of_glue {ι : Type*} [DecidableEq ι] (𝒢 : Finset ι) (H : ι → SimpleGraph (Fin k))
    (R : ι → ι → Prop) [DecidableRel R] (M : ℕ)
    (hM : ∀ i ∈ 𝒢, (𝒢.filter (fun j => ¬ R j i)).card ≤ M)
    {r : ℕ} {A : Verifier Unit} (hA : IsLocal r A) (hp : 2 * r + 1 ≤ p) (S : ℕ)
    (hc : ∀ i ∈ 𝒢, ∃ P : Proof, SizeLE (star p k (H i) (H i)) P S ∧
      AllAccept A (star p k (H i) (H i)) P)
    (hs : ∀ i ∈ 𝒢, ∀ j ∈ 𝒢, R i j → ∀ P : Proof,
      ∃ v ∈ (star p k (H i) (H j)).V, A (star p k (H i) (H j)) P v = false) :
    𝒢.card ≤ M * 2 ^ ((S + 1) * (2 * r + 1)) := by
  classical
  choose! P hPS hPA using hc
  let pat : ι → (Fin (2 * r + 1) → List Bool) := fun i t => P i (t + 1)
  let T : Finset (Fin (2 * r + 1) → List Bool) := Fintype.piFinset fun _ => bitStrings S
  have hT : T.card ≤ 2 ^ ((S + 1) * (2 * r + 1)) := by
    simp only [T, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
    rw [pow_mul]
    exact Nat.pow_le_pow_left (card_bitStrings_le S) _
  have hmaps : ∀ i ∈ 𝒢, pat i ∈ T := by
    intro i hi
    simp only [T, Fintype.mem_piFinset, mem_bitStrings]
    intro t
    exact hPS i hi _ (by simp; omega)
  by_contra hlt
  push Not at hlt
  have hlt' : T.card * M < 𝒢.card :=
    lt_of_le_of_lt (by rw [mul_comm]; exact Nat.mul_le_mul_left _ hT) hlt
  obtain ⟨y, -, hy⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt'
  set Φ := 𝒢.filter (fun i => pat i = y)
  have hne : Φ.Nonempty := by
    rw [← card_pos]; omega
  obtain ⟨j, hj⟩ := hne
  have hjG : j ∈ 𝒢 := (mem_filter.1 hj).1
  have : ∃ i ∈ Φ, R i j := by
    by_contra hno
    push Not at hno
    have : Φ ⊆ 𝒢.filter (fun i => ¬ R i j) := by
      intro i hi
      exact mem_filter.2 ⟨(mem_filter.1 hi).1, hno i hi⟩
    have := (card_le_card this).trans (hM j hjG)
    omega
  obtain ⟨i, hi, hij⟩ := this
  have hiG : i ∈ 𝒢 := (mem_filter.1 hi).1
  have hpat : pat i = pat j := (mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm
  have hag : ∀ t, 1 ≤ t → t ≤ 2 * r + 1 → P i t = P j t := by
    intro t h1 h2
    have := congrFun hpat ⟨t - 1, by omega⟩
    simp only [pat] at this
    have e : ((⟨t - 1, by omega⟩ : Fin (2 * r + 1)) : ℕ) + 1 = t := by simp; omega
    rwa [e] at this
  have hacc := glue_accept hA hp (hPA i hiG) (hPA j hjG) hag
  obtain ⟨v, hv, hrej⟩ := hs i hiG j hjG hij (gluedProof p k r (P i) (P j))
  rw [hacc v hv] at hrej
  exact Bool.noConfusion hrej

end StarCons

end Podc.LocallyCheckableProofs
