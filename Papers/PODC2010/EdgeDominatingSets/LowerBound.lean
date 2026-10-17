import Papers.PODC2010.EdgeDominatingSets.Gadget

/-!
# Lower bounds (§3, §4 and Corollary 1 of the paper)

Suomela, *Distributed algorithms for edge dominating sets*, PODC 2010.

* `theorem_1`: for every even `d = 2k`, a `d`-regular simple graph on which every deterministic
  port-numbering algorithm (any running time, no consistency assumption) outputs an edge dominating
  set of size at least `(4 - 2/d)` times the optimum.
* `theorem_2`: the same for odd `d = 2k + 1` with ratio `4 - 6/(d + 1)`.
* `corollary_1`: the bounded-degree consequence `α ≥ 4 - 1/k` for `Δ ≥ 2k`.

Model: deterministic synchronous port-numbering model (`Cslib.PortNumbering.Algorithm`), no
identifiers, no randomness, unbounded messages and running time; the output of a node is a set of
its ports, and the computed edge set is `outEdges` (the union of the selected edges).

The proofs follow the paper: the graphs are 2-factorised (`Gadget.gp`), so they cover a small
multigraph (`loopGraph`, `base2`); all nodes of a fibre produce the same output, and
`card_le_of_fibre` counts the selected edges. Optimality of the explicit edge dominating sets is
proved by the counting bound `|E| ≤ (2Δ - 1)γ'` (`card_edgeFinset_add_le`).
-/

namespace Podc.EdgeDominatingSets

open Cslib.PortNumbering Finset Gadget

/-- In a `d`-regular simple graph on `n` nodes, `n d + 2γ' ≤ 4 d γ'` (i.e. `|E| ≤ (2d - 1)γ'`). -/
theorem card_mul_add_le_edgeDomNum {V : Type*} [Fintype V] [DecidableEq V] (G : PNGraph V)
    (hG : G.IsSimple) {d : ℕ} (hd : ∀ v, G.deg v = d) :
    Fintype.card V * d + 2 * edgeDomNum G.toSimpleGraph ≤
      4 * d * edgeDomNum G.toSimpleGraph := by
  classical
  obtain ⟨D, hD, hDc⟩ := exists_isEDS_card_eq G.toSimpleGraph
  have hdeg : ∀ v, G.toSimpleGraph.degree v = d := fun v => (G.degree_eq hG v).trans (hd v)
  have h1 := card_edgeFinset_add_le G.toSimpleGraph (Δ := d) (fun v => (hdeg v).le) hD
  have h2 := G.toSimpleGraph.sum_degrees_eq_twice_card_edges
  simp only [hdeg, sum_const, card_univ, smul_eq_mul] at h2
  rw [hDc] at h1
  nlinarith

/-! ### Theorem 1 -/

/-- The one-node multigraph of §3.3: `2k` ports, loops `(·, 2j) ↔ (·, 2j + 1)`. -/
def loopGraph (k : ℕ) : PNGraph Unit where
  deg _ := 2 * k
  p _ t := ((), fl t)
  p_lt _ _ h := fl_lt h
  p_p _ t _ := by simp [fl_fl]

/-- The graph of Theorem 1 (§3.1): `K_{2k,2k-1}` plus a perfect matching on the side of size `2k`,
with a port numbering that is a 2-factorisation. -/
def graph1 (k : ℕ) : PNGraph (Node (2 * k)) where
  deg _ := 2 * k
  p := gp 0
  p_lt v i h := by rw [gp_snd]; exact fl_lt h
  p_p v i _ := gp_gp 0 v i

theorem graph1_isSimple (k : ℕ) : (graph1 k).IsSimple :=
  ⟨fun v _ hi => gp_ne 0 le_rfl hi v, fun v _ _ hi hj h => gp_inj 0 le_rfl hi hj v h⟩

theorem graph1_covering (k : ℕ) : (graph1 k).IsCovering (loopGraph k) (fun _ => ()) :=
  ⟨fun _ => rfl, fun v i _ => by
    show ((), fl i) = ((), (gp 0 v i).2)
    rw [gp_snd]⟩

/-- The matching `S` of §3.2 is an edge dominating set of size `≤ k`. -/
theorem graph1_eds (k : ℕ) (hk : 0 < k) :
    ∃ S, IsEDS (graph1 k).toSimpleGraph S ∧ S.card ≤ k := by
  have : NeZero (2 * k) := ⟨by omega⟩
  classical
  refine ⟨(range k).image fun j =>
    (graph1 k).edge (.inl (-0 - ((2 * j : ℕ) : ZMod (2 * k)))) (2 * j), ?_, ?_⟩
  · refine isEDS_of_cover ?_ (Set.range Sum.inl) ?_ ?_
    · intro e he
      obtain ⟨j, hj, rfl⟩ := mem_image.1 he
      exact (graph1 k).edge_mem_edgeSet (graph1_isSimple k)
        (show 2 * j < 2 * k by simp at hj; omega)
    · rintro _ ⟨x, rfl⟩
      obtain ⟨j, hj, hx | hx⟩ := exists_match (k := k) (0 : ZMod (2 * k)) x (ZMod.val_lt _)
      · exact ⟨_, mem_image.2 ⟨j, mem_range.2 hj, rfl⟩, by rw [hx]; exact Sym2.mem_mk_left _ _⟩
      · refine ⟨_, mem_image.2 ⟨j, mem_range.2 hj, rfl⟩, ?_⟩
        rw [hx]
        show _ ∈ s(_, (gp 0 _ _).1)
        rw [gp_match']
        exact Sym2.mem_mk_right _ _
    · rintro u v ⟨-, i, -, rfl⟩
      rcases u with x | y
      · exact Or.inl ⟨x, rfl⟩
      · exact Or.inr ⟨_, rfl⟩
  · exact card_image_le.trans (card_range k).le

theorem graph1_edgeDomNum (k : ℕ) (hk : 0 < k) : edgeDomNum (graph1 k).toSimpleGraph = k := by
  have : NeZero (2 * k) := ⟨by omega⟩
  obtain ⟨S, hS, hSc⟩ := graph1_eds k hk
  have h1 := card_mul_add_le_edgeDomNum (graph1 k) (graph1_isSimple k) (d := 2 * k)
    (fun _ => rfl)
  rw [card_node] at h1
  have h2 := edgeDomNum_le hS
  set γ := edgeDomNum (graph1 k).toSimpleGraph
  -- `(4k - 1) · 2k + 2γ ≤ 8kγ`, hence `k ≤ γ`
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have : (4 * n + 3) * (n + 1) ≤ (4 * n + 3) * γ := by
    have e : 2 * (n + 1) + (2 * (n + 1) - 1) = 4 * n + 3 := by omega
    rw [e] at h1
    nlinarith
  have := Nat.le_of_mul_le_mul_left this (by omega)
  omega

/-- The lower bound of Theorem 1 on the concrete graph `graph1 k`. -/
theorem graph1_lower (k : ℕ) [NeZero (2 * k)] (hk : 0 < k) (A : Algorithm Unit (Set ℕ))
    (T : ℕ) (hE : IsEDS (graph1 k).toSimpleGraph (outEdges (graph1 k) (A.eval (graph1 k) T fun _ => ()))) :
    (4 - 2 / (2 * k : ℝ)) * edgeDomNum (graph1 k).toSimpleGraph ≤
      (outEdges (graph1 k) (A.eval (graph1 k) T fun _ => ())).card := by
  set X := A.eval (graph1 k) T fun _ => ()
  have hX : ∀ v, X v = A.eval (loopGraph k) T (fun _ => ()) () := fun v =>
    A.eval_covering (graph1_covering k) T (fun _ => ()) v
  -- some edge is selected
  have he0 := (graph1 k).edge_mem_edgeSet (graph1_isSimple k) (v := .inl 0) (i := 0)
    (show 0 < 2 * k by omega)
  obtain ⟨e', he', -⟩ := hE.2 _ he0
  obtain ⟨v, q, hq, hqX, -⟩ := mem_outEdges.1 he'
  -- hence every node selects port `q`, and these edges are distinct
  have hc := card_le_of_fibre (graph1_isSimple k) (graph1_covering k) (x := ()) (q := q) hq
    (by simp [loopGraph, fl_ne]) univ (fun _ _ => rfl) (outEdges (graph1 k) X)
    (fun w _ => edge_mem_outEdges hq (by rw [hX w, ← hX v]; exact hqX))
  rw [card_univ, card_node] at hc
  rw [graph1_edgeDomNum k hk]
  have hc' : (4 * k : ℝ) ≤ (outEdges (graph1 k) X).card + 1 := by
    have : 4 * k ≤ (outEdges (graph1 k) X).card + 1 := by omega
    exact_mod_cast this
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have : (4 - 2 / (2 * k : ℝ)) * k = 4 * k - 1 := by field_simp
  rw [this]
  linarith

/-- **Theorem 1** of [Suomela, PODC'10]. For each even `d = 2k ≥ 2` there is a `d`-regular
simple port-numbered graph `G` such that every deterministic algorithm in the port-numbering model
(with any running time `T`) that outputs an edge dominating set of `G` outputs one of size at least
`(4 - 2/d)` times the optimum. -/
theorem theorem_1 (k : ℕ) (hk : 0 < k) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : PNGraph V),
      G.IsSimple ∧ (∀ v, G.deg v = 2 * k) ∧ edgeDomNum G.toSimpleGraph = k ∧
      ∀ (A : Algorithm Unit (Set ℕ)) (T : ℕ),
        IsEDS G.toSimpleGraph (outEdges G (A.eval G T fun _ => ())) →
        (4 - 2 / (2 * k : ℝ)) * edgeDomNum G.toSimpleGraph ≤
          (outEdges G (A.eval G T fun _ => ())).card := by
  have : NeZero (2 * k) := ⟨by omega⟩
  exact ⟨Node (2 * k), inferInstance, inferInstance, graph1 k, graph1_isSimple k, fun _ => rfl,
    graph1_edgeDomNum k hk, fun A T hE => graph1_lower k hk A T hE⟩

/-! ### Theorem 2 -/

section Theorem2

variable (k : ℕ)

/-- The outer node attached (through port `2k`) to node `u` of copy `ℓ` (§4.1). The outer nodes
are `P_i = inl i` and `Q_x = inr x` (`x ≠ 0`): in copy `ℓ`, `c = a_0 ↦ P_ℓ`, `a_x ↦ Q_x`,
`b_y ↦ P_{y+ℓ}`. -/
def outer (ℓ : ZMod (2 * k + 1)) : Node (2 * k + 1) → Node (2 * k + 1)
  | .inl x => if h : x = 0 then .inl ℓ else .inr ⟨x, h⟩
  | .inr y => .inl (y.1 + ℓ)

/-- The inverse of `outer k ℓ`: the node of copy `ℓ` attached to an outer node. -/
def inner (ℓ : ZMod (2 * k + 1)) : Node (2 * k + 1) → Node (2 * k + 1)
  | .inl j => if h : j = ℓ then .inl 0 else .inr ⟨j - ℓ, sub_ne_zero.2 h⟩
  | .inr x => .inl x.1

theorem inner_outer (ℓ : ZMod (2 * k + 1)) (u : Node (2 * k + 1)) :
    inner k ℓ (outer k ℓ u) = u := by
  rcases u with x | ⟨y, hy⟩
  · by_cases hx : x = 0
    · subst hx; simp [outer, inner]
    · simp [outer, inner, hx]
  · have : y + ℓ ≠ ℓ := by simpa using hy
    simp [outer, inner, this]

theorem outer_inner (ℓ : ZMod (2 * k + 1)) (o : Node (2 * k + 1)) :
    outer k ℓ (inner k ℓ o) = o := by
  rcases o with j | ⟨x, hx⟩
  · by_cases hj : j = ℓ
    · subst hj; simp [outer, inner]
    · simp [outer, inner, hj]
  · simp [outer, inner, hx]

/-- Nodes of the graph of Theorem 2: `d = 2k + 1` copies of the gadget `H(ℓ)` and the outer nodes. -/
abbrev V2 := (ZMod (2 * k + 1) × Node (2 * k + 1)) ⊕ Node (2 * k + 1)

/-- The graph of Theorem 2 (§4.1). Inside copy `ℓ` ports `0, …, 2k - 1` follow the gadget with
`s = 1` (this is the paper's `H(ℓ)`, with `c = a_0`); port `2k` of a node of copy `ℓ` is joined to
port `ℓ` of an outer node. -/
def graph2 : PNGraph (V2 k) where
  deg _ := 2 * k + 1
  p
    | .inl (ℓ, u), t =>
      if t < 2 * k then (.inl (ℓ, (gp 1 u t).1), fl t) else (.inr (outer k ℓ u), ℓ.val)
    | .inr o, i => (.inl ((i : ZMod (2 * k + 1)), inner k i o), 2 * k)
  p_lt v i h := by
    rcases v with ⟨ℓ, u⟩ | o
    · dsimp only
      split_ifs with hi
      · exact (fl_lt hi).trans (by omega)
      · exact ZMod.val_lt ℓ
    · dsimp only; omega
  p_p v i h := by
    rcases v with ⟨ℓ, u⟩ | o
    · by_cases hi : i < 2 * k
      · have := gp_gp 1 u i
        rw [gp_snd] at this
        simp [hi, fl_lt hi, this, fl_fl]
      · have : i = 2 * k := by simp at h; omega
        simp [inner_outer, this]
    · have hi : i < 2 * k + 1 := h
      simp [outer_inner, ZMod.val_cast_of_lt hi]

theorem graph2_nbr_lt {ℓ : ZMod (2 * k + 1)} {u : Node (2 * k + 1)} {i : ℕ} (hi : i < 2 * k) :
    (graph2 k).nbr (.inl (ℓ, u)) i = .inl (ℓ, (gp 1 u i).1) := by
  simp [PNGraph.nbr, graph2, hi]

theorem graph2_nbr_two_mul (ℓ : ZMod (2 * k + 1)) (u : Node (2 * k + 1)) :
    (graph2 k).nbr (.inl (ℓ, u)) (2 * k) = .inr (outer k ℓ u) := by
  simp [PNGraph.nbr, graph2]

theorem graph2_nbr_inr (o : Node (2 * k + 1)) (i : ℕ) :
    (graph2 k).nbr (.inr o) i = .inl ((i : ZMod (2 * k + 1)), inner k i o) := rfl

theorem graph2_isSimple : (graph2 k).IsSimple := by
  have hm : 2 * k ≤ 2 * k + 1 := by omega
  refine ⟨fun v i hi => ?_, fun v i j hi hj h => ?_⟩
  · rcases v with ⟨ℓ, u⟩ | o
    · by_cases hi' : i < 2 * k
      · rw [graph2_nbr_lt k hi']
        intro h
        exact gp_ne 1 hm hi' u (congrArg Prod.snd (Sum.inl.inj h))
      · have : i = 2 * k := by simp [graph2] at hi; omega
        subst this
        rw [graph2_nbr_two_mul]; simp
    · rw [graph2_nbr_inr]; simp
  · have hi1 : i < 2 * k + 1 := hi
    have hj1 : j < 2 * k + 1 := hj
    rcases v with ⟨ℓ, u⟩ | o
    · by_cases hi' : i < 2 * k <;> by_cases hj' : j < 2 * k
      · rw [graph2_nbr_lt k hi', graph2_nbr_lt k hj'] at h
        exact gp_inj 1 hm hi' hj' u (congrArg Prod.snd (Sum.inl.inj h))
      · obtain rfl : j = 2 * k := by omega
        rw [graph2_nbr_lt k hi', graph2_nbr_two_mul] at h; simp at h
      · obtain rfl : i = 2 * k := by omega
        rw [graph2_nbr_lt k hj', graph2_nbr_two_mul] at h; simp at h
      · omega
    · rw [graph2_nbr_inr, graph2_nbr_inr] at h
      exact CharP.natCast_injOn_Iio (ZMod _) _ hi1 hj1 (congrArg Prod.fst (Sum.inl.inj h))

/-- The base multigraph of §4.3: nodes `x_ℓ = some ℓ` (loops `(x_ℓ, 2j) ↔ (x_ℓ, 2j + 1)`) and
`y = none`, with `(x_ℓ, 2k) ↔ (y, ℓ)`. -/
def base2 : PNGraph (Option (ZMod (2 * k + 1))) where
  deg _ := 2 * k + 1
  p
    | some ℓ, t => if t < 2 * k then (some ℓ, fl t) else (none, ℓ.val)
    | none, i => (some (i : ZMod (2 * k + 1)), 2 * k)
  p_lt v i h := by
    rcases v with _ | ℓ
    · dsimp only; omega
    · dsimp only
      split_ifs with hi
      · exact (fl_lt hi).trans (by omega)
      · exact ZMod.val_lt ℓ
  p_p v i h := by
    rcases v with _ | ℓ
    · have hi : i < 2 * k + 1 := h
      simp [ZMod.val_cast_of_lt hi]
    · by_cases hi : i < 2 * k
      · simp [hi, fl_lt hi, fl_fl]
      · have : i = 2 * k := by simp at h; omega
        simp [this]

/-- The covering map: copy `ℓ` ↦ `x_ℓ`, outer nodes ↦ `y`. -/
def proj : V2 k → Option (ZMod (2 * k + 1))
  | .inl (ℓ, _) => some ℓ
  | .inr _ => none

theorem graph2_covering : (graph2 k).IsCovering (base2 k) (proj k) := by
  refine ⟨fun _ => rfl, fun v i hi => ?_⟩
  rcases v with ⟨ℓ, u⟩ | o
  · by_cases hi' : i < 2 * k
    · simp [base2, graph2, proj, PNGraph.nbr, PNGraph.rport, hi']
    · simp [base2, graph2, proj, PNGraph.nbr, PNGraph.rport, hi']
  · simp [base2, graph2, proj, PNGraph.nbr, PNGraph.rport]

theorem card_V2 : Fintype.card (V2 k) = (2 * k + 2) * (4 * k + 1) := by
  rw [Fintype.card_sum, Fintype.card_prod, ZMod.card, card_node]
  have : 2 * k + 1 + (2 * k + 1 - 1) = 4 * k + 1 := by omega
  rw [this]; ring

/-- The edge dominating set `D*` of §4.2: the edges `P_ℓ c_ℓ` and the matchings `S(ℓ)`. -/
theorem graph2_eds :
    ∃ S, IsEDS (graph2 k).toSimpleGraph S ∧ S.card ≤ (k + 1) * (2 * k + 1) := by
  classical
  set G := graph2 k
  refine ⟨(univ.image fun ℓ => G.edge (.inl (ℓ, .inl 0)) (2 * k)) ∪
    ((univ ×ˢ range k).image fun p =>
      G.edge (.inl (p.1, .inl (-1 - ((2 * p.2 : ℕ) : ZMod (2 * k + 1))))) (2 * p.2)), ?_, ?_⟩
  · refine isEDS_of_cover ?_
      (Set.range (fun p : ZMod (2 * k + 1) × ZMod (2 * k + 1) => (.inl (p.1, .inl p.2) : V2 k)) ∪
        Set.range (fun ℓ => (.inr (.inl ℓ) : V2 k))) ?_ ?_
    · intro e he
      rcases mem_union.1 he with he | he
      · obtain ⟨ℓ, -, rfl⟩ := mem_image.1 he
        exact G.edge_mem_edgeSet (graph2_isSimple k) (show 2 * k < 2 * k + 1 by omega)
      · obtain ⟨⟨ℓ, j⟩, hj, rfl⟩ := mem_image.1 he
        simp only [mem_product, mem_univ, mem_range, true_and] at hj
        exact G.edge_mem_edgeSet (graph2_isSimple k) (show 2 * j < 2 * k + 1 by omega)
    · rintro _ (⟨⟨ℓ, x⟩, rfl⟩ | ⟨ℓ, rfl⟩)
      · by_cases hx : x = 0
        · subst hx
          exact ⟨_, mem_union_left _ (mem_image.2 ⟨ℓ, mem_univ _, rfl⟩), Sym2.mem_mk_left _ _⟩
        · have hval : (-x - 1).val < 2 * k := by
            have h1 := ZMod.val_lt (-x - 1)
            have h2 : (-x - 1).val ≠ 2 * k := by
              intro h
              have h3 : (((-x - 1).val : ℕ) : ZMod (2 * k + 1)) = ((2 * k : ℕ) : ZMod (2 * k + 1)) :=
                by rw [h]
              rw [ZMod.natCast_zmod_val] at h3
              have h4 : ((2 * k + 1 : ℕ) : ZMod (2 * k + 1)) = 0 := ZMod.natCast_self _
              push_cast at h3 h4
              exact hx (by linear_combination -h3 - h4)
            omega
          obtain ⟨j, hj, hx' | hx'⟩ := exists_match (k := k) (1 : ZMod (2 * k + 1)) x hval
          · refine ⟨_, mem_union_right _ (mem_image.2 ⟨(ℓ, j), by simp [hj], rfl⟩), ?_⟩
            rw [hx']
            exact Sym2.mem_mk_left _ _
          · refine ⟨_, mem_union_right _ (mem_image.2 ⟨(ℓ, j), by simp [hj], rfl⟩), ?_⟩
            show _ ∈ s(_, G.nbr _ _)
            rw [graph2_nbr_lt k (by omega), gp_match', hx']
            exact Sym2.mem_mk_right _ _
      · refine ⟨_, mem_union_left _ (mem_image.2 ⟨ℓ, mem_univ _, rfl⟩), ?_⟩
        show _ ∈ s(_, G.nbr _ _)
        rw [graph2_nbr_two_mul]
        simp [outer]
    · rintro u v ⟨-, i, hi, rfl⟩
      have hi1 : i < 2 * k + 1 := hi
      rcases u with ⟨ℓ, x | y⟩ | (j | x)
      · exact Or.inl (Or.inl ⟨(ℓ, x), rfl⟩)
      · right
        by_cases hi' : i < 2 * k
        · rw [graph2_nbr_lt k hi']
          exact Or.inl ⟨(ℓ, _), rfl⟩
        · obtain rfl : i = 2 * k := by omega
          rw [graph2_nbr_two_mul]
          exact Or.inr ⟨_, rfl⟩
      · exact Or.inl (Or.inr ⟨j, rfl⟩)
      · right
        rw [graph2_nbr_inr]
        exact Or.inl ⟨(_, x.1), rfl⟩
  · refine (card_union_le _ _).trans ?_
    refine (add_le_add card_image_le card_image_le).trans ?_
    simp only [card_univ, ZMod.card, card_product, card_range]
    ring_nf; rfl

theorem graph2_edgeDomNum :
    edgeDomNum (graph2 k).toSimpleGraph = (k + 1) * (2 * k + 1) := by
  obtain ⟨S, hS, hSc⟩ := graph2_eds k
  have h1 := card_mul_add_le_edgeDomNum (graph2 k) (graph2_isSimple k) (d := 2 * k + 1)
    (fun _ => rfl)
  rw [card_V2] at h1
  have h2 := edgeDomNum_le hS
  set γ := edgeDomNum (graph2 k).toSimpleGraph
  have : (4 * k + 1) * ((k + 1) * (2 * k + 1)) ≤ (4 * k + 1) * γ := by nlinarith
  have := Nat.le_of_mul_le_mul_left this (by omega)
  omega

end Theorem2

/-- The node sets of the copies are not joined to each other: an edge has endpoints in at most one
copy. -/
theorem proj_nbr_eq {v : V2 k} {i : ℕ} (hi : i < 2 * k + 1) {a b : ZMod (2 * k + 1)}
    (ha : proj k v = some a) (hb : proj k ((graph2 k).nbr v i) = some b) : a = b := by
  rcases v with ⟨ℓ, u⟩ | o
  · simp only [proj, Option.some.injEq] at ha
    subst ha
    by_cases hi' : i < 2 * k
    · rw [graph2_nbr_lt k hi'] at hb; simpa [proj] using hb
    · obtain rfl : i = 2 * k := by omega
      rw [graph2_nbr_two_mul] at hb; simp [proj] at hb
  · simp [proj] at ha

/-- The lower-bound core of §4.4: an edge dominating set computed by a port-numbering algorithm
contains at least `|H(ℓ)| = 2d - 1` edges incident to each copy `H(ℓ)`. -/
theorem card_filter_copy (hk : 0 < k) (A : Algorithm Unit (Set ℕ)) (T : ℕ)
    (hE : IsEDS (graph2 k).toSimpleGraph (outEdges (graph2 k) (A.eval (graph2 k) T fun _ => ())))
    (ℓ : ZMod (2 * k + 1)) [DecidablePred fun e : Sym2 (V2 k) => ∃ v, proj k v = some ℓ ∧ v ∈ e] :
    4 * k + 1 ≤ ((outEdges (graph2 k) (A.eval (graph2 k) T fun _ => ())).filter
      fun e => ∃ v, proj k v = some ℓ ∧ v ∈ e).card := by
  set G := graph2 k
  set X := A.eval G T fun _ => ()
  set D := outEdges G X
  have hG := graph2_isSimple k
  have hf := graph2_covering k
  have hX : ∀ v, X v = A.eval (base2 k) T (fun _ => ()) (proj k v) := fun v =>
    A.eval_covering hf T (fun _ => ()) v
  have hcard : ∀ (g : Node (2 * k + 1) → V2 k), Function.Injective g →
      (univ.image g).card = 4 * k + 1 := by
    intro g hg
    rw [card_image_of_injective _ hg, card_univ, card_node]; omega
  -- case A: a node of copy `ℓ` selects a port `q`
  have caseA : ∀ v i, proj k v = some ℓ → i < 2 * k + 1 → i ∈ X v →
      4 * k + 1 ≤ (D.filter fun e => ∃ v, proj k v = some ℓ ∧ v ∈ e).card := by
    intro v i hv hi hiX
    have hloop : (base2 k).p (some ℓ) i ≠ (some ℓ, i) := by
      simp only [base2]
      split_ifs
      · simp [fl_ne]
      · simp
    rw [← hcard (fun u => .inl (ℓ, u)) (fun u u' h => by simpa using h)]
    refine card_le_of_fibre hG hf (x := some ℓ) hi hloop _ ?_ _ ?_
    · intro w hw; obtain ⟨u, -, rfl⟩ := mem_image.1 hw; rfl
    · intro w hw
      have hw' : proj k w = some ℓ := by obtain ⟨u, -, rfl⟩ := mem_image.1 hw; rfl
      exact mem_filter.2 ⟨edge_mem_outEdges hi (by rw [hX, hw', ← hv, ← hX]; exact hiX),
        w, hw', Sym2.mem_mk_left _ _⟩
  -- case B: an outer node selects port `ℓ`
  have caseB : ∀ v i, proj k v = none → i < 2 * k + 1 → (i : ZMod (2 * k + 1)) = ℓ → i ∈ X v →
      4 * k + 1 ≤ (D.filter fun e => ∃ v, proj k v = some ℓ ∧ v ∈ e).card := by
    intro v i hv hi hiℓ hiX
    have hloop : (base2 k).p none i ≠ (none, i) := by simp [base2]
    rw [← hcard (fun o => .inr o) Sum.inr_injective]
    refine card_le_of_fibre hG hf (x := none) hi hloop _ ?_ _ ?_
    · intro w hw; obtain ⟨u, -, rfl⟩ := mem_image.1 hw; rfl
    · intro w hw
      obtain ⟨o, -, rfl⟩ := mem_image.1 hw
      refine mem_filter.2 ⟨edge_mem_outEdges hi
        (by rw [hX, show proj k (Sum.inr o) = none from rfl, ← hv, ← hX]; exact hiX), _, ?_,
        Sym2.mem_mk_right _ _⟩
      rw [graph2_nbr_inr, proj, hiℓ]
  -- some edge of `D` touches the edge `e₀` inside copy `ℓ`
  have h0 : 0 < 2 * k := by omega
  have he0 := G.edge_mem_edgeSet hG (v := .inl (ℓ, .inl 0)) (i := 0) (by simp [G, graph2])
  obtain ⟨e', he', w, hw0, hw'⟩ := hE.2 _ he0
  have hfw : proj k w = some ℓ := by
    rcases Sym2.mem_iff.1 hw0 with rfl | rfl
    · rfl
    · rw [graph2_nbr_lt k h0]; rfl
  obtain ⟨v, i, hi, hiX, rfl⟩ := mem_outEdges.1 he'
  have hi1 : i < 2 * k + 1 := hi
  rcases Sym2.mem_iff.1 hw' with rfl | rfl
  · exact caseA w i hfw hi1 hiX
  · rcases hv : proj k v with _ | ℓ'
    · rcases v with ⟨ℓ', u⟩ | o
      · simp [proj] at hv
      · rw [graph2_nbr_inr] at hfw
        exact caseB _ i hv hi1 (by simpa [proj] using hfw) hiX
    · obtain rfl := proj_nbr_eq (k := k) hi1 hv hfw
      exact caseA v i hv hi1 hiX

/-- The lower bound of Theorem 2 on the concrete graph `graph2 k`. -/
theorem graph2_lower (k : ℕ) (A : Algorithm Unit (Set ℕ)) (T : ℕ)
    (hE : IsEDS (graph2 k).toSimpleGraph (outEdges (graph2 k) (A.eval (graph2 k) T fun _ => ()))) :
    (4 - 6 / ((2 * k + 1 : ℕ) + 1 : ℝ)) * edgeDomNum (graph2 k).toSimpleGraph ≤
      (outEdges (graph2 k) (A.eval (graph2 k) T fun _ => ())).card := by
  classical
  rw [graph2_edgeDomNum k]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `d = 1`: the bound is `γ' ≤ |D|`
    have := edgeDomNum_le hE
    rw [graph2_edgeDomNum] at this
    have e : (4 - 6 / ((2 * 0 + 1 : ℕ) + 1 : ℝ)) = 1 := by norm_num
    rw [e, one_mul]
    exact_mod_cast this
  set D := outEdges (graph2 k) (A.eval (graph2 k) T fun _ => ())
  set P : ZMod (2 * k + 1) → Sym2 (V2 k) → Prop := fun ℓ e => ∃ v, proj k v = some ℓ ∧ v ∈ e
  -- the sets `D ∩ E_ℓ` are pairwise disjoint
  have hdisj : ((univ : Finset (ZMod (2 * k + 1))) : Set (ZMod (2 * k + 1))).PairwiseDisjoint
      fun ℓ => D.filter (P ℓ) := by
    intro ℓ _ ℓ' _ hne
    refine disjoint_filter.2 fun e he ⟨v, hv, hve⟩ ⟨w, hw, hwe⟩ => hne ?_
    obtain ⟨u, i, hi, -, rfl⟩ := mem_outEdges.1 he
    have hi1 : i < 2 * k + 1 := hi
    rcases Sym2.mem_iff.1 hve with rfl | rfl <;> rcases Sym2.mem_iff.1 hwe with rfl | rfl
    · simpa [hv] using hw
    · exact proj_nbr_eq (k := k) hi1 hv hw
    · exact (proj_nbr_eq (k := k) hi1 hw hv).symm
    · simpa [hv] using hw
  have hsum : (2 * k + 1) * (4 * k + 1) ≤ D.card := by
    calc (2 * k + 1) * (4 * k + 1) = ∑ _ℓ : ZMod (2 * k + 1), (4 * k + 1) := by
          simp [ZMod.card]
      _ ≤ ∑ ℓ : ZMod (2 * k + 1), (D.filter (P ℓ)).card :=
          sum_le_sum fun ℓ _ => card_filter_copy hk A T hE ℓ
      _ = (univ.biUnion fun ℓ => D.filter (P ℓ)).card := (card_biUnion hdisj).symm
      _ ≤ D.card := card_le_card (biUnion_subset.2 fun ℓ _ => filter_subset _ _)
  have : (((2 * k + 1) * (4 * k + 1) : ℕ) : ℝ) ≤ D.card := by exact_mod_cast hsum
  have e : (4 - 6 / ((2 * k + 1 : ℕ) + 1 : ℝ)) * (((k + 1) * (2 * k + 1) : ℕ) : ℝ) =
      (((2 * k + 1) * (4 * k + 1) : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [e]
  exact this

/-! ### Corollary 1 -/

/-- **Theorem 2** of [Suomela, PODC'10]. For each odd `d = 2k + 1` there is a `d`-regular simple
port-numbered graph `G` such that every deterministic algorithm in the port-numbering model (with
any running time `T`) that outputs an edge dominating set of `G` outputs one of size at least
`4 - 6/(d + 1)` times the optimum. (The optimum is `(k + 1) d = d (d + 1) / 2`.) -/
theorem theorem_2 (k : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : PNGraph V),
      G.IsSimple ∧ (∀ v, G.deg v = 2 * k + 1) ∧
      edgeDomNum G.toSimpleGraph = (k + 1) * (2 * k + 1) ∧
      ∀ (A : Algorithm Unit (Set ℕ)) (T : ℕ),
        IsEDS G.toSimpleGraph (outEdges G (A.eval G T fun _ => ())) →
        (4 - 6 / ((2 * k + 1 : ℕ) + 1 : ℝ)) * edgeDomNum G.toSimpleGraph ≤
          (outEdges G (A.eval G T fun _ => ())).card := by
  exact ⟨V2 k, inferInstance, inferInstance, graph2 k, graph2_isSimple k, fun _ => rfl,
    graph2_edgeDomNum k, fun A T hE => graph2_lower k A T hE⟩

/-- **Corollary 1** of [Suomela, PODC'10] (the lower-bound half). If a deterministic
port-numbering algorithm `A` (running time `T`) finds an `α`-approximation of a minimum edge
dominating set in every simple graph of maximum degree `≤ Δ`, where `Δ ≥ 2k`, then
`α ≥ 4 - 1/k`. -/
theorem corollary_1 (k Δ : ℕ) (hk : 0 < k) (hΔ : 2 * k ≤ Δ) (A : Algorithm Unit (Set ℕ)) (T : ℕ)
    (α : ℝ)
    (hA : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : PNGraph V), G.IsSimple →
      (∀ v, G.deg v ≤ Δ) →
      IsEDS G.toSimpleGraph (outEdges G (A.eval G T fun _ => ())) ∧
      ((outEdges G (A.eval G T fun _ => ())).card : ℝ) ≤ α * edgeDomNum G.toSimpleGraph) :
    4 - 1 / (k : ℝ) ≤ α := by
  obtain ⟨V, _, _, G, hG, hdeg, hγ, hlow⟩ := theorem_1 k hk
  obtain ⟨hE, hα⟩ := hA V G hG fun v => (hdeg v).le.trans hΔ
  have h := (hlow A T hE).trans hα
  rw [hγ] at h
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have e : (2 / (2 * k : ℝ)) = 1 / k := by field_simp
  rw [e] at h
  exact le_of_mul_le_mul_right h hk'

end Podc.EdgeDominatingSets
