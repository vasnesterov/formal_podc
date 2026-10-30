import Mathlib

/-!
# 3-colourings of the toroidal grid and the auxiliary graph `H`

Section 9 of Brandt et al., *LCL problems on grids* (PODC 2017).

Nodes of the toroidal `n × n` grid are `Pos n = ZMod n × ZMod n`; `sh v a b` is the node at offset
`(a, b)` from `v` (`a` to the east, `b` to the north). A colouring is `c : Pos n → Col` with the
three colours `1, 2, 3` of the paper.

Given a colouring, the paper builds a directed graph `H` on the colour-3 nodes: two colour-3 nodes
`u, v` sharing two neighbours `w, w'` with `c w = 1`, `c w' = 2` are joined by an edge, directed
so that the colour-1 common neighbour is on the *left* of the edge. On a torus with `n ≥ 5` two
nodes share two neighbours iff they are diagonal neighbours, so the edges of `H` are diagonal
steps `d : Diag`; the common neighbours of `u` and `u + d` are `u + d.left` (obtained from `d` by
a 45° counter-clockwise rotation) and `u + d.right`. This gives `HEdge c u d`.

The label `ell c v ∈ {-1, 0, 1}` of Lemma 14 is `1` if `v` is a northbound intersection (it has
in- and out-degree `1` in `H`, the in-neighbour is on the row below and the out-neighbour on the
row above), `-1` if it is southbound, and `0` otherwise.

## Main results

* `indeg_eq_outdeg`: in a proper colouring every node has equal in- and out-degree in `H`;
* `ell_eq`: `ell c v = inBelow c v - outBelow c v` (the in-edges from the row below minus the
  out-edges to the row below);
* `ell_ne_zero_iff`: a colour-3 node has `ell ≠ 0` iff its west and east neighbours have
  different colours.

All three are local facts about the `3 × 3` block around `v`, checked by `decide`.
-/

namespace Podc.LCLGrids

/-- The three colours `1, 2, 3` of the paper. -/
inductive Col
  | one
  | two
  | three
  deriving DecidableEq, Repr

instance : Fintype Col := ⟨{.one, .two, .three}, fun x => by cases x <;> simp⟩

/-- Nodes of the toroidal `n × n` grid: `(x, y)` with `x, y ∈ ℤ/n` (`x` grows to the east,
`y` to the north). -/
abbrev Pos (n : ℕ) := ZMod n × ZMod n

variable {n : ℕ}

/-- The node at offset `(a, b)` from `v`. -/
def sh (v : Pos n) (a b : ℤ) : Pos n := (v.1 + a, v.2 + b)

@[simp] lemma sh_sh (v : Pos n) (a b a' b' : ℤ) :
    sh (sh v a b) a' b' = sh v (a + a') (b + b') := by
  simp [sh, add_assoc]

@[simp] lemma sh_zero (v : Pos n) : sh v 0 0 = v := by simp [sh]

/-- A proper colouring of the toroidal grid: the two endpoints of every horizontal and every
vertical edge have different colours. -/
def IsProper (c : Pos n → Col) : Prop :=
  ∀ v, c v ≠ c (sh v 1 0) ∧ c v ≠ c (sh v 0 1)

/-- The four diagonal directions. -/
inductive Diag
  | ne
  | nw
  | sw
  | se
  deriving DecidableEq, Repr

instance : Fintype Diag := ⟨{.ne, .nw, .sw, .se}, fun x => by cases x <;> simp⟩

namespace Diag

/-- East offset of a diagonal direction. -/
def dx : Diag → ℤ
  | ne => 1 | nw => -1 | sw => -1 | se => 1

/-- North offset of a diagonal direction. -/
def dy : Diag → ℤ
  | ne => 1 | nw => 1 | sw => -1 | se => -1

/-- The opposite direction. -/
def neg : Diag → Diag
  | ne => sw | nw => se | sw => ne | se => nw

/-- Offset of the common neighbour on the left of the step `d` (rotate `d` by 45°
counter-clockwise). -/
def left : Diag → ℤ × ℤ
  | ne => (0, 1) | nw => (-1, 0) | sw => (0, -1) | se => (1, 0)

/-- Offset of the common neighbour on the right of the step `d`. -/
def right : Diag → ℤ × ℤ
  | ne => (1, 0) | nw => (0, 1) | sw => (-1, 0) | se => (0, -1)

/-- The step goes to the row below. -/
def IsDown (d : Diag) : Prop := d.dy = -1

instance : DecidablePred IsDown := fun d => inferInstanceAs (Decidable (d.dy = -1))

end Diag

/-- The node `u + d`. -/
def step (u : Pos n) (d : Diag) : Pos n := sh u d.dx d.dy

/-- Edge `u → u + d` of the auxiliary graph `H`: both endpoints have colour `3`, the common
neighbour on the left of the edge has colour `1` and the one on the right has colour `2`. -/
def HEdge (c : Pos n → Col) (u : Pos n) (d : Diag) : Prop :=
  c u = .three ∧ c (step u d) = .three ∧ c (sh u d.left.1 d.left.2) = .one ∧
    c (sh u d.right.1 d.right.2) = .two

instance (c : Pos n → Col) (u : Pos n) (d : Diag) : Decidable (HEdge c u d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Out-degree of `v` in `H`. -/
def outdeg (c : Pos n → Col) (v : Pos n) : ℕ :=
  (Finset.univ.filter fun d : Diag => HEdge c v d).card

/-- In-degree of `v` in `H` (the edge from `v + d` back to `v` has direction `d.neg`). -/
def indeg (c : Pos n → Col) (v : Pos n) : ℕ :=
  (Finset.univ.filter fun d : Diag => HEdge c (step v d) d.neg).card

/-- Out-edges of `v` going to the row below. -/
def outBelow (c : Pos n → Col) (v : Pos n) : ℕ :=
  (Finset.univ.filter fun d : Diag => d.IsDown ∧ HEdge c v d).card

/-- Out-edges of `v` going to the row above. -/
def outAbove (c : Pos n → Col) (v : Pos n) : ℕ :=
  (Finset.univ.filter fun d : Diag => ¬ d.IsDown ∧ HEdge c v d).card

/-- In-edges of `v` coming from the row below. -/
def inBelow (c : Pos n → Col) (v : Pos n) : ℕ :=
  (Finset.univ.filter fun d : Diag => d.IsDown ∧ HEdge c (step v d) d.neg).card

/-- In-edges of `v` coming from the row above. -/
def inAbove (c : Pos n → Col) (v : Pos n) : ℕ :=
  (Finset.univ.filter fun d : Diag => ¬ d.IsDown ∧ HEdge c (step v d) d.neg).card

/-- The label `ℓ(v)` of the proof of Lemma 14: for a colour-3 node with in- and out-degree `1`
in `H`, `1` if the in-neighbour is on the row below and the out-neighbour on the row above
(northbound intersection), `-1` in the opposite case (southbound intersection), `0` if both are
on the same row; `0` in all other cases. -/
def ell (c : Pos n → Col) (v : Pos n) : ℤ :=
  if c v = .three ∧ indeg c v = 1 ∧ outdeg c v = 1 then
    if inBelow c v = 1 ∧ outAbove c v = 1 then 1
    else if inAbove c v = 1 ∧ outBelow c v = 1 then -1 else 0
  else 0

/-! ### Reduction to the `3 × 3` block -/

/-- The colours of the `3 × 3` block around a node. -/
structure Block where
  nw : Col
  n : Col
  ne : Col
  w : Col
  c : Col
  e : Col
  sw : Col
  s : Col
  se : Col
  deriving DecidableEq

/-- The `3 × 3` block of `c` around `v`. -/
def block (c : Pos n → Col) (v : Pos n) : Block :=
  ⟨c (sh v (-1) 1), c (sh v 0 1), c (sh v 1 1), c (sh v (-1) 0), c v, c (sh v 1 0),
    c (sh v (-1) (-1)), c (sh v 0 (-1)), c (sh v 1 (-1))⟩

namespace Block

variable (B : Block)

/-- Out-edges at the centre, read from the block (`d ↦ ` whether `centre → centre + d`). -/
def outE : Diag → Bool
  | .ne => B.c = .three ∧ B.ne = .three ∧ B.n = .one ∧ B.e = .two
  | .nw => B.c = .three ∧ B.nw = .three ∧ B.w = .one ∧ B.n = .two
  | .sw => B.c = .three ∧ B.sw = .three ∧ B.s = .one ∧ B.w = .two
  | .se => B.c = .three ∧ B.se = .three ∧ B.e = .one ∧ B.s = .two

/-- In-edges at the centre, read from the block (`d ↦ ` whether `centre + d → centre`). -/
def inE : Diag → Bool
  | .ne => B.ne = .three ∧ B.c = .three ∧ B.e = .one ∧ B.n = .two
  | .nw => B.nw = .three ∧ B.c = .three ∧ B.n = .one ∧ B.w = .two
  | .sw => B.sw = .three ∧ B.c = .three ∧ B.w = .one ∧ B.s = .two
  | .se => B.se = .three ∧ B.c = .three ∧ B.s = .one ∧ B.e = .two

/-- Count of the directions in a list satisfying a Boolean test. -/
def cnt (p : Diag → Bool) (l : List Diag) : ℕ := l.countP p

/-- Block version of `outdeg`. -/
def outdeg : ℕ := cnt B.outE [.ne, .nw, .sw, .se]
/-- Block version of `indeg`. -/
def indeg : ℕ := cnt B.inE [.ne, .nw, .sw, .se]
/-- Block version of `outBelow`. -/
def outBelow : ℕ := cnt B.outE [.sw, .se]
/-- Block version of `outAbove`. -/
def outAbove : ℕ := cnt B.outE [.ne, .nw]
/-- Block version of `inBelow`. -/
def inBelow : ℕ := cnt B.inE [.sw, .se]
/-- Block version of `inAbove`. -/
def inAbove : ℕ := cnt B.inE [.ne, .nw]

/-- Block version of `ell`. -/
def ell : ℤ :=
  if B.c = .three ∧ B.indeg = 1 ∧ B.outdeg = 1 then
    if B.inBelow = 1 ∧ B.outAbove = 1 then 1
    else if B.inAbove = 1 ∧ B.outBelow = 1 then -1 else 0
  else 0

/-- The block is properly coloured (the twelve edges inside it are bichromatic). -/
def Proper : Prop :=
  B.nw ≠ B.n ∧ B.n ≠ B.ne ∧ B.w ≠ B.c ∧ B.c ≠ B.e ∧ B.sw ≠ B.s ∧ B.s ≠ B.se ∧
  B.nw ≠ B.w ∧ B.w ≠ B.sw ∧ B.n ≠ B.c ∧ B.c ≠ B.s ∧ B.ne ≠ B.e ∧ B.e ≠ B.se

instance : DecidablePred Proper := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The three local facts, checked on all blocks. -/
theorem key : ∀ nw n ne w c e sw s se : Col, (Block.mk nw n ne w c e sw s se).Proper →
    (Block.mk nw n ne w c e sw s se).indeg = (Block.mk nw n ne w c e sw s se).outdeg ∧
    (Block.mk nw n ne w c e sw s se).ell =
      ((Block.mk nw n ne w c e sw s se).inBelow : ℤ) - (Block.mk nw n ne w c e sw s se).outBelow ∧
      (c = .three → ((Block.mk nw n ne w c e sw s se).ell ≠ 0 ↔ w ≠ e)) := by
  decide

end Block

lemma Diag.card_filter (p : Diag → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = [Diag.ne, .nw, .sw, .se].countP (fun d => decide (p d)) := by
  rw [show (Finset.univ : Finset Diag) = {.ne, .nw, .sw, .se} from rfl]
  by_cases h1 : p .ne <;> by_cases h2 : p .nw <;> by_cases h3 : p .sw <;> by_cases h4 : p .se <;>
    simp [Finset.filter_insert, Finset.filter_singleton, h1, h2, h3, h4]

section bridge

variable (c : Pos n → Col) (v : Pos n)

lemma hEdge_iff_outE (d : Diag) : HEdge c v d ↔ (block c v).outE d = true := by
  cases d <;>
    simp only [HEdge, step, block, Block.outE, Diag.dx, Diag.dy, Diag.left, Diag.right] <;>
    exact decide_eq_true_iff.symm

lemma hEdge_step_neg_iff_inE (d : Diag) :
    HEdge c (step v d) d.neg ↔ (block c v).inE d = true := by
  cases d <;>
    simp [HEdge, step, block, Block.inE, Diag.dx, Diag.dy, Diag.left, Diag.right, Diag.neg,
      and_comm, and_assoc]

private lemma countP_eq (l : List Diag) (p : Diag → Prop) [DecidablePred p] (q : Diag → Bool)
    (h : ∀ d, p d ↔ q d = true) : l.countP (fun d => decide (p d)) = l.countP q :=
  List.countP_congr (fun d _ => by simp [h d])

lemma outdeg_eq : outdeg c v = (block c v).outdeg := by
  rw [outdeg, Diag.card_filter, Block.outdeg, Block.cnt]
  exact countP_eq _ _ _ (hEdge_iff_outE c v)

lemma indeg_eq : indeg c v = (block c v).indeg := by
  rw [indeg, Diag.card_filter, Block.indeg, Block.cnt]
  exact countP_eq _ _ _ (hEdge_step_neg_iff_inE c v)

lemma outBelow_eq : outBelow c v = (block c v).outBelow := by
  rw [outBelow, Diag.card_filter, Block.outBelow, Block.cnt]
  simp [List.countP_cons, Diag.IsDown, Diag.dy, hEdge_iff_outE]

lemma outAbove_eq : outAbove c v = (block c v).outAbove := by
  rw [outAbove, Diag.card_filter, Block.outAbove, Block.cnt]
  simp [List.countP_cons, Diag.IsDown, Diag.dy, hEdge_iff_outE]

lemma inBelow_eq : inBelow c v = (block c v).inBelow := by
  rw [inBelow, Diag.card_filter, Block.inBelow, Block.cnt]
  simp [List.countP_cons, Diag.IsDown, Diag.dy, hEdge_step_neg_iff_inE]

lemma inAbove_eq : inAbove c v = (block c v).inAbove := by
  rw [inAbove, Diag.card_filter, Block.inAbove, Block.cnt]
  simp [List.countP_cons, Diag.IsDown, Diag.dy, hEdge_step_neg_iff_inE]

lemma ell_eq_block : ell c v = (block c v).ell := by
  simp only [ell, Block.ell, indeg_eq, outdeg_eq, inBelow_eq, outAbove_eq, inAbove_eq,
    outBelow_eq]
  rfl

variable {c}

lemma block_proper (hc : IsProper c) : (block c v).Proper := by
  have h := fun a b => hc (sh v a b)
  simp only [sh_sh] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [block]
  · simpa using (h (-1) 1).1
  · simpa using (h 0 1).1
  · simpa using (h (-1) 0).1
  · simpa using (h 0 0).1
  · simpa using (h (-1) (-1)).1
  · simpa using (h 0 (-1)).1
  · exact fun e => (h (-1) 0).2 (by simpa using e.symm)
  · exact fun e => (h (-1) (-1)).2 (by simpa using e.symm)
  · exact fun e => (h 0 0).2 (by simpa using e.symm)
  · exact fun e => (h 0 (-1)).2 (by simpa using e.symm)
  · exact fun e => (h 1 0).2 (by simpa using e.symm)
  · exact fun e => (h 1 (-1)).2 (by simpa using e.symm)

/-- In a proper colouring, every node has the same in- and out-degree in `H`. -/
theorem indeg_eq_outdeg (hc : IsProper c) : indeg c v = outdeg c v := by
  have := Block.key _ _ _ _ _ _ _ _ _ (block_proper v hc)
  rw [indeg_eq, outdeg_eq]; exact this.1

/-- In a proper colouring, `ℓ(v)` is the number of in-edges of `v` from the row below minus the
number of out-edges of `v` to the row below. -/
theorem ell_eq (hc : IsProper c) : ell c v = (inBelow c v : ℤ) - outBelow c v := by
  have := Block.key _ _ _ _ _ _ _ _ _ (block_proper v hc)
  rw [ell_eq_block, inBelow_eq, outBelow_eq]; exact this.2.1

/-- In a proper colouring, a colour-3 node has `ℓ(v) ≠ 0` iff its west and east neighbours have
different colours. -/
theorem ell_ne_zero_iff (hc : IsProper c) (h3 : c v = .three) :
    ell c v ≠ 0 ↔ c (sh v (-1) 0) ≠ c (sh v 1 0) := by
  have := Block.key _ _ _ _ _ _ _ _ _ (block_proper v hc)
  rw [ell_eq_block]; exact this.2.2 h3

lemma ell_eq_zero_of_ne_three (h : c v ≠ .three) : ell c v = 0 := by
  simp [ell, h]

lemma ell_mem (v : Pos n) : ell c v = -1 ∨ ell c v = 0 ∨ ell c v = 1 := by
  unfold ell; split_ifs <;> simp

end bridge

end Podc.LCLGrids
