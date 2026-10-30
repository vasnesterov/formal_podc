import Papers.PODC2020.PowerGraphApproximation.CKP17
import Papers.PODC2020.PowerGraphApproximation.PathGadget
import Cslib.Computability.Distributed.Congest.LowerBound

/-!
# The lower-bound graphs `H_{x,y}` of Theorems 20 and 22

Bar-Yehuda, Censor-Hillel, Maus, Pai, Pemmaraju, *Distributed Approximation on Power Graphs*,
PODC 2020 (arXiv:2006.03746), Sections 5.2 and 5.3 (Figures 2 and 3).

Starting from `G_{x,y}` (`CKP17.lean`):
* every edge incident to a bit-gadget vertex is replaced by a path gadget: `PE.rb s ℓ i h` for the
  row–bit edge `row s ℓ i – bit s ℓ h (i h)`, `PE.cyc ℓ h s s'` for the 4-cycle edge
  `bit s ℓ h 1 – bit s' ℓ h 0`;
* the clique edges are kept (`core`);
* for every row `a^i_1` (resp. `b^i_1`) a shared gadget `PE.sh s i` is joined to `a^i_1` and to
  every `a^j_2` with `x(i, j) = 0` (resp. `y`).

A gadget is a path of `m` new vertices whose first vertex is joined to the endpoints
(`attach`, `PathGadget.lean`): `m = 1` is the weight-`0` vertex `p_e` of Section 5.2, `m = 3` the
dangling path `DP_e[1..3]` of Section 5.3. `H x y m` is the resulting graph on
`HV L m = GV L ⊕ PE L × Fin m`. The number of gadgets is `g = 2k + 4k log k + 8 log k`
(`card_PE`).

Partition (proofs of Theorems 20 and 22): `V'_A` = Alice's vertices of `G_{x,y}`, the gadgets
both of whose endpoints are in `V_A`, and the shared gadgets `p^i_a`. The cut consists of the
`4 log k` edges `bit_A – DP_e[1]` for the 4-cycle edges `e` between `A` and `B` (`hCut`).
-/

namespace Podc.PowerGraphApproximation.LowerBound

open Finset SimpleGraph Cslib.Congest

variable {L : ℕ}

/-- The path gadgets of `H_{x,y}`. -/
inductive PE (L : ℕ) where
  /-- The gadget replacing the edge `row s ℓ i – bit s ℓ h (i h)`. -/
  | rb (s ℓ : Bool) (i : Idx L) (h : Fin L)
  /-- The gadget replacing the 4-cycle edge `bit s ℓ h true – bit s' ℓ h false`. -/
  | cyc (ℓ : Bool) (h : Fin L) (s s' : Bool)
  /-- The shared gadget `p^i_a` (`s = false`) or `p^i_b` (`s = true`) of row `i`. -/
  | sh (s : Bool) (i : Idx L)
  deriving DecidableEq, Fintype

/-- The kept edges of `G_{x,y}`: the clique edges among rows. -/
def CoreAdj : GV L → GV L → Prop
  | .row s ℓ i, .row s' ℓ' i' => s = s' ∧ ℓ = ℓ' ∧ i ≠ i'
  | _, _ => False

instance : DecidableRel (CoreAdj (L := L)) := fun a b =>
  match a, b with
  | .row s ℓ i, .row s' ℓ' i' => inferInstanceAs (Decidable (s = s' ∧ ℓ = ℓ' ∧ i ≠ i'))
  | .row _ _ _, .bit _ _ _ _ => instDecidableFalse
  | .bit _ _ _ _, .row _ _ _ => instDecidableFalse
  | .bit _ _ _ _, .bit _ _ _ _ => instDecidableFalse

/-- The clique edges of `G_{x,y}` (kept in `H_{x,y}`). -/
def core (L : ℕ) : SimpleGraph (GV L) where
  Adj := CoreAdj
  symm := ⟨fun a b h => by cases a <;> cases b <;> simp only [CoreAdj] at h ⊢; grind⟩
  loopless := ⟨fun a h => by cases a <;> simp [CoreAdj] at h⟩

instance : DecidableRel (core L).Adj := inferInstanceAs (DecidableRel CoreAdj)

@[simp] lemma core_row_row {s ℓ s' ℓ' : Bool} {i i' : Idx L} :
    (core L).Adj (.row s ℓ i) (.row s' ℓ' i') ↔ s = s' ∧ ℓ = ℓ' ∧ i ≠ i' := Iff.rfl

@[simp] lemma not_core_bit_left {s ℓ b : Bool} {h : Fin L} {v : GV L} :
    ¬(core L).Adj (.bit s ℓ h b) v := by cases v <;> exact id

@[simp] lemma not_core_bit_right {s ℓ b : Bool} {h : Fin L} {v : GV L} :
    ¬(core L).Adj v (.bit s ℓ h b) := by cases v <;> exact id

/-- Attachment of the first gadget vertex: the endpoints of the replaced edge, or (shared
gadget `sh s i`) the row `i` of layer 1 and the rows `j` of layer 2 with `M_s(i, j) = 0`. -/
def att (x y : Idx L × Idx L → Bool) : PE L → GV L → Bool
  | .rb s ℓ i _, .row s' ℓ' i' => decide (s' = s ∧ ℓ' = ℓ ∧ i' = i)
  | .rb s ℓ i h, .bit s' ℓ' h' b => decide (s' = s ∧ ℓ' = ℓ ∧ h' = h ∧ b = i h)
  | .cyc _ _ _ _, .row _ _ _ => false
  | .cyc ℓ h s s', .bit t ℓ' h' b => decide (ℓ' = ℓ ∧ h' = h ∧ (if b then t = s else t = s'))
  | .sh s i, .row t ℓ j => decide (t = s ∧ (if ℓ then mat x y s (i, j) = false else j = i))
  | .sh _ _, .bit _ _ _ _ => false

/-- The graph `H_{x,y}` with gadgets of `m` vertices (`m = 1`: Section 5.2, `m = 3`:
Section 5.3). -/
abbrev HV (L m : ℕ) := GV L ⊕ PE L × Fin m

/-- The lower-bound graph `H_{x,y}` (Figures 2 and 3). -/
def H (x y : Idx L × Idx L → Bool) (m : ℕ) [NeZero m] : SimpleGraph (HV L m) :=
  attach (core L) (att x y) m

instance (x y : Idx L × Idx L → Bool) (m : ℕ) [NeZero m] : DecidableRel (H x y m).Adj :=
  inferInstanceAs (DecidableRel (attach _ _ _).Adj)

/-- `H²_{x,y}` restricted to the vertices of `G_{x,y}` is `G_{x,y}`. -/
theorem isSquareTrace (x y : Idx L × Idx L → Bool) :
    IsSquareTrace (G x y) (core L) (att x y) := by
  intro u v
  constructor
  · intro huv
    refine ⟨huv.ne, ?_⟩
    cases u with
    | row s ℓ i =>
      cases v with
      | row s' ℓ' i' =>
        obtain ⟨rfl, ⟨rfl, hi⟩ | ⟨rfl, rfl, hm⟩ | ⟨rfl, rfl, hm⟩⟩ := huv
        · exact Or.inl ⟨rfl, rfl, hi⟩
        · exact Or.inr (Or.inr ⟨.sh s i, by simp [att], by simp [att, hm]⟩)
        · exact Or.inr (Or.inr ⟨.sh s i', by simp [att, hm], by simp [att]⟩)
      | bit s' ℓ' h b =>
        obtain ⟨rfl, rfl, rfl⟩ := huv
        exact Or.inr (Or.inr ⟨.rb s ℓ i h, by simp [att], by simp [att]⟩)
    | bit s ℓ h b =>
      cases v with
      | row s' ℓ' i =>
        obtain ⟨rfl, rfl, rfl⟩ := huv
        exact Or.inr (Or.inr ⟨.rb s ℓ i h, by simp [att], by simp [att]⟩)
      | bit s' ℓ' h' b' =>
        obtain ⟨rfl, rfl, hb⟩ := huv
        cases b <;> cases b' <;> simp at hb
        · exact Or.inr (Or.inr ⟨.cyc ℓ h s' s, by simp [att], by simp [att]⟩)
        · exact Or.inr (Or.inr ⟨.cyc ℓ h s s', by simp [att], by simp [att]⟩)
  · rintro ⟨hne, h | ⟨w, h1, h2⟩ | ⟨e, h1, h2⟩⟩
    · cases u <;> cases v <;> simp at h
      obtain ⟨rfl, rfl, hi⟩ := h
      exact G_row_row.2 ⟨rfl, Or.inl ⟨rfl, hi⟩⟩
    · cases u <;> cases v <;> cases w <;> simp at h1 h2
      obtain ⟨rfl, rfl, -⟩ := h1
      obtain ⟨rfl, rfl, -⟩ := h2
      exact G_row_row.2 ⟨rfl, Or.inl ⟨rfl, fun h => hne (by rw [h])⟩⟩
    · cases e <;> cases u <;> cases v <;> simp [att] at h1 h2 hne ⊢ <;> grind


/-! ### Lemmas 21, 23, 24 -/

/-- **Lemma 21 of [BCMPP20].** `H²_{x,y}` (gadgets of one vertex `p_e` of weight `0`, original
vertices of weight `1`) has a vertex cover of weight at most `W` iff `G_{x,y}` has a vertex cover
of size at most `W`. -/
theorem lemma_21 (x y : Idx L × Idx L → Bool) (W : ℕ) :
    (∃ C : Finset (HV L 1), ((H x y 1).power 2).IsVertexCover ↑C ∧ ∑ v ∈ C, wt v ≤ W) ↔
      ∃ C : Finset (GV L), (G x y).IsVertexCover ↑C ∧ C.card ≤ W :=
  weighted_iff (isSquareTrace x y) W

/-- **Lemma 23 of [BCMPP20].** Every vertex cover of `H²_{x,y}` (dangling paths of three vertices)
can be modified into a vertex cover that is not larger, agrees with it on the vertices of
`G_{x,y}`, and contains `P[1], P[2]` but not the leaf `P[3]` of every dangling or shared path
gadget `P` (positions `0, 1, 2` here). -/
theorem lemma_23 (x y : Idx L × Idx L → Bool) {C : Finset (HV L 3)}
    (hC : ((H x y 3).power 2).IsVertexCover ↑C) :
    ∃ C' : Finset (HV L 3), ((H x y 3).power 2).IsVertexCover ↑C' ∧
      C'.card ≤ C.card ∧ C'.toLeft = C.toLeft ∧
      ∀ e, Sum.inr (e, 0) ∈ C' ∧ Sum.inr (e, 1) ∈ C' ∧ Sum.inr (e, 2) ∉ C' :=
  normalize (isSquareTrace x y) hC

/-- The number of path gadgets: `g = 2k + 4k log k + 8 log k`. -/
lemma card_PE : Fintype.card (PE L) = 2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L := by
  let e : PE L ≃ (Bool × Bool × Idx L × Fin L) ⊕ (Bool × Fin L × Bool × Bool) ⊕ (Bool × Idx L) :=
    { toFun := fun v => match v with
        | .rb s ℓ i h => .inl (s, ℓ, i, h)
        | .cyc ℓ h s s' => .inr (.inl (ℓ, h, s, s'))
        | .sh s i => .inr (.inr (s, i))
      invFun := fun p => match p with
        | .inl (s, ℓ, i, h) => .rb s ℓ i h
        | .inr (.inl (ℓ, h, s, s')) => .cyc ℓ h s s'
        | .inr (.inr (s, i)) => .sh s i
      left_inv := fun v => by cases v <;> rfl
      right_inv := fun p => by rcases p with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;> rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_sum, Fintype.card_prod]
  ring

/-- The number of vertices of `H_{x,y}`: `n = 4k + 8 log k + m · g`. -/
lemma card_HV (m : ℕ) : Fintype.card (HV L m) =
    4 * 2 ^ L + 8 * L + m * (2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L) := by
  simp only [HV, Fintype.card_sum, Fintype.card_prod, card_GV, card_PE, Fintype.card_fin]
  ring

/-- **Lemma 24 of [BCMPP20]** (threshold form). `H²_{x,y}` has a vertex cover of size at most
`W + 2(2k + 4k log k + 8 log k)` iff `G_{x,y}` has a vertex cover of size at most `W`. -/
theorem lemma_24 (x y : Idx L × Idx L → Bool) (W : ℕ) :
    (∃ C : Finset (HV L 3), ((H x y 3).power 2).IsVertexCover ↑C ∧
        C.card ≤ W + 2 * (2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L)) ↔
      ∃ C : Finset (GV L), (G x y).IsVertexCover ↑C ∧ C.card ≤ W := by
  rw [← card_PE]
  exact unweighted_iff (isSquareTrace x y) W

/-- **Lemma 24 of [BCMPP20].** `τ(H²_{x,y}) = τ(G_{x,y}) + 2(2k + 4k log k + 8 log k)`. -/
theorem lemma_24_vertexCoverNum (x y : Idx L × Idx L → Bool) :
    ((H x y 3).power 2).vertexCoverNum =
      (G x y).vertexCoverNum + 2 * (2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L) := by
  have := vertexCoverNum_sq (E := PE L) (isSquareTrace x y)
  rw [card_PE] at this
  exact_mod_cast this

/-! ### The family of lower bound graphs -/

/-- The side of a vertex of `G_{x,y}` (`false` = Alice). -/
def GV.side : GV L → Bool
  | .row s _ _ => s
  | .bit s _ _ _ => s

/-- The side of a gadget: Alice's iff both endpoints of the replaced edge are Alice's (for shared
gadgets: the side of the rows). -/
def PE.side : PE L → Bool
  | .rb s _ _ _ => s
  | .cyc _ _ s s' => s || s'
  | .sh s _ => s

/-- The side of a vertex of `H_{x,y}` (`false` = `V'_A`). -/
def hside {m : ℕ} : HV L m → Bool := Sum.elim GV.side (fun p => p.1.side)

section Sides

variable (x y : Idx L × Idx L → Bool)

lemma att_x (x' : Idx L × Idx L → Bool) {e : PE L} {u : GV L}
    (h : e.side = true ∨ u.side = true) : att x y e u = att x' y e u := by
  rcases e with ⟨s, ℓ, i, h⟩ | ⟨ℓ, h, s, s'⟩ | ⟨s, i⟩ <;>
    rcases u with ⟨t, ℓ', j⟩ | ⟨t, ℓ', h', b⟩ <;> simp only [att]
  rcases s <;> rcases t <;> simp_all [PE.side, GV.side, mat]

lemma att_y (y' : Idx L × Idx L → Bool) {e : PE L} {u : GV L}
    (h : e.side = false ∨ u.side = false) : att x y e u = att x y' e u := by
  rcases e with ⟨s, ℓ, i, h⟩ | ⟨ℓ, h, s, s'⟩ | ⟨s, i⟩ <;>
    rcases u with ⟨t, ℓ', j⟩ | ⟨t, ℓ', h', b⟩ <;> simp only [att]
  rcases s <;> rcases t <;> simp_all [PE.side, GV.side, mat]

variable {x y}

lemma att_side_alice {e : PE L} {u : GV L} (ha : att x y e u = true) (he : e.side = false) :
    u.side = false := by
  rcases e with ⟨s, ℓ, i, h⟩ | ⟨ℓ, h, s, s'⟩ | ⟨s, i⟩ <;>
    rcases u with ⟨t, ℓ', j⟩ | ⟨t, ℓ', h', b⟩ <;> simp [att, PE.side, GV.side] at ha he ⊢ <;>
    grind

lemma att_cross {e : PE L} {u : GV L} (ha : att x y e u = true) (hu : u.side = false)
    (he : e.side = true) : ∃ ℓ h b, u = .bit false ℓ h b ∧ e = .cyc ℓ h (!b) b := by
  rcases e with ⟨s, ℓ, i, h⟩ | ⟨ℓ, h, s, s'⟩ | ⟨s, i⟩ <;>
    rcases u with ⟨t, ℓ', j⟩ | ⟨t, ℓ', h', b⟩ <;> simp [att, PE.side, GV.side] at ha hu he
  all_goals try grind
  obtain ⟨rfl, rfl, hb⟩ := ha
  subst hu
  refine ⟨ℓ', h', b, rfl, ?_⟩
  cases b <;> cases s <;> cases s' <;> simp_all

lemma core_side {u v : GV L} (h : (core L).Adj u v) : u.side = v.side := by
  cases u <;> cases v <;> simp at h
  simp [GV.side, h.1]

end Sides

/-- The cut edges: `(bit_{A_ℓ}^h(b), DP_e[1])` for the two 4-cycle edges `e` of gadget `(ℓ, h)`
between `A` and `B`. -/
def hCut (L m : ℕ) [NeZero m] : Finset (HV L m × HV L m) :=
  (univ : Finset (Bool × Fin L × Bool)).image fun p =>
    (.inl (.bit false p.1 p.2.1 p.2.2), .inr (.cyc p.1 p.2.1 (!p.2.2) p.2.2, 0))

lemma card_hCut (m : ℕ) [NeZero m] : (hCut L m).card = 4 * L := by
  rw [hCut, card_image_of_injective]
  · simp [card_univ, Fintype.card_prod]; ring
  · rintro ⟨ℓ, h, b⟩ ⟨ℓ', h', b'⟩ he
    simp only [Prod.mk.injEq, Sum.inl.injEq, GV.bit.injEq] at he
    obtain ⟨⟨-, rfl, rfl, rfl⟩, -⟩ := he
    rfl

section Family

variable {m : ℕ} [NeZero m] {x y : Idx L × Idx L → Bool}

lemma h_adj_cut {a b : HV L m} (ha : hside a = false) (hb : hside b = true)
    (hab : (H x y m).Adj a b) : (a, b) ∈ hCut L m := by
  rcases a with u | ⟨e, p⟩ <;> rcases b with v | ⟨e', q⟩ <;> simp only [hside, Sum.elim_inl,
    Sum.elim_inr] at ha hb
  · have := core_side hab; simp_all
  · obtain ⟨rfl, hatt⟩ := hab
    obtain ⟨ℓ, h, b, rfl, rfl⟩ := att_cross hatt ha hb
    exact mem_image.2 ⟨(ℓ, h, b), mem_univ _, rfl⟩
  · obtain ⟨rfl, hatt⟩ := hab
    have := att_side_alice hatt ha; simp_all
  · obtain ⟨rfl, -⟩ := hab; simp_all

lemma h_adj_alice (y' : Idx L × Idx L → Bool) {a b : HV L m} (ha : hside a = false)
    (hb : hside b = false) : (H x y m).Adj a b ↔ (H x y' m).Adj a b := by
  rcases a with u | ⟨e, p⟩ <;> rcases b with v | ⟨e', q⟩ <;> simp only [hside, Sum.elim_inl,
    Sum.elim_inr] at ha hb <;> simp only [H, attach_inl_inl, attach_inl_inr, attach_inr_inl,
    attach_inr_inr]
  · rw [att_y x y y' (Or.inl hb)]
  · rw [att_y x y y' (Or.inl ha)]

lemma h_adj_bob (x' : Idx L × Idx L → Bool) {a b : HV L m} (ha : hside a = true)
    (hb : hside b = true) : (H x y m).Adj a b ↔ (H x' y m).Adj a b := by
  rcases a with u | ⟨e, p⟩ <;> rcases b with v | ⟨e', q⟩ <;> simp only [hside, Sum.elim_inl,
    Sum.elim_inr] at ha hb <;> simp only [H, attach_inl_inl, attach_inl_inr, attach_inr_inl,
    attach_inr_inr]
  · rw [att_x x y x' (Or.inl hb)]
  · rw [att_x x y x' (Or.inl ha)]

lemma h_adj_fixed (x' y' : Idx L × Idx L → Bool) {a b : HV L m} (ha : hside a = false)
    (hb : hside b = true) : (H x y m).Adj a b ↔ (H x' y' m).Adj a b := by
  rcases a with u | ⟨e, p⟩ <;> rcases b with v | ⟨e', q⟩ <;> simp only [hside, Sum.elim_inl,
    Sum.elim_inr] at ha hb <;> simp only [H, attach_inl_inl, attach_inl_inr, attach_inr_inl,
    attach_inr_inr]
  · rw [att_x x y x' (Or.inl hb), att_y x' y y' (Or.inr ha)]
  · rw [att_x x y x' (Or.inr hb), att_y x' y y' (Or.inl ha)]

end Family

/-- `H_{x,y}` as a family of lower bound graphs for `DISJ_{k²}` (nodes know their
neighbourhoods), with partition `V'_A, V'_B` and `4 log k` cut edges. -/
def hFamily (L m : ℕ) [NeZero m] :
    LBFamily (Idx L × Idx L → Bool) (Idx L × Idx L → Bool) (HV L m) (HV L m → Bool) :=
  LBFamily.ofAdj (fun x y => H x y m) (fun v => !hside v) (hCut L m)
    (by
      intro p hp
      obtain ⟨q, -, rfl⟩ := mem_image.1 hp
      simp [hside, GV.side, PE.side])
    (fun x y a b ha hb hab => h_adj_cut (by simpa using ha) (by simpa using hb) hab)
    (fun x y y' a b ha hb => h_adj_alice y' (by simpa using ha) (by simpa using hb))
    (fun x x' y a b ha hb => h_adj_bob x' (by simpa using ha) (by simpa using hb))
    (fun x x' y y' a b ha hb => h_adj_fixed x' y' (by simpa using ha) (by simpa using hb))

instance (m : ℕ) [NeZero m] (x y : Idx L × Idx L → Bool) :
    DecidableRel ((hFamily L m).G x y).Adj :=
  inferInstanceAs (DecidableRel (H x y m).Adj)

lemma hFamily_Ecut (m : ℕ) [NeZero m] : (hFamily L m).Ecut = hCut L m := rfl

end Podc.PowerGraphApproximation.LowerBound
