import Papers.PODC2019.HardnessOptimization.MDSGraph

/-!
# The directed Hamiltonian path lower-bound graphs (Section 2.2.1)

Bachrach, Censor-Hillel, Dory, Efron, Leitersdorf, Paz. *Hardness of Distributed Optimization.*
PODC 2019 (arXiv:1905.10284), Section 2.2.1.

`k = 2 ^ L` (positions `Fin (2 ^ L)`), `2 log k = 2 L` boxes (`Fin (2 * L)`). A row index is a bit
string `i : Fin L → Bool`.

* `start`, `stop` (the paper's `end`), `sA1 = s¹₁`, `sA2 = s²₁`, `sB1 = s¹₂`, `sB2 = s²₂`.
* Rows: `row s ℓ i` is `a^i_1` (`s = false`, `ℓ = false`), `a^i_2` (`s = false`, `ℓ = true`),
  `b^i_1`, `b^i_2` (`s = true`).
* Box `c` (`0 ≤ c < 2L`): `g c`, `r c`, and per line `q : Bool` (`true = t`, `false = f`) and
  position `d`: launch `la c q d` (`ℓ^{c,d}_q`), skip `si c q d` (`σ`), burn `be c q d` (`β`).
  Box `c < L` handles bit `c` of the layer-1 rows, box `c ≥ L` bit `c - L` of the layer-2 rows
  (`layer c`, `bit c`).
* The wheel vertex `wheel^{c,d}_q` is a row: `W c q d = (side, index)` and the row is
  `row side (layer c) index` (`wrow`). The construction is stated for an abstract wheel assignment
  `W`; the properties needed are stated as hypotheses in the claims and a concrete `W` is given in
  `HamPathWheel.lean`.

Arcs (`baseArc`, listed by out-neighbourhood) are exactly those of the paper, **plus**
`r c → ℓ^{c,k-1}_q` for both `q`, which are drawn in the paper's Figure 2 and used in the proof of
Claim 2.1 but missing from the textual construction (without them `r c` has out-degree `0` and no
`D_{x,y}` has a Hamiltonian path).
Input arcs: `a^i_1 → a^j_2` iff `x i j`, `b^i_1 → b^j_2` iff `y i j`.
-/

namespace HardnessOptimization.HamPath

/-! `Idx L = Fin L → Bool` (row indices) is shared with the MDS construction. -/

/-- Vertices of the directed Hamiltonian path lower-bound graph. -/
inductive HV (L : ℕ) where
  | start
  | stop
  | sA1
  | sA2
  | sB1
  | sB2
  | row (side layer : Bool) (i : Idx L)
  | g (c : Fin (2 * L))
  | r (c : Fin (2 * L))
  | la (c : Fin (2 * L)) (q : Bool) (d : Fin (2 ^ L))
  | si (c : Fin (2 * L)) (q : Bool) (d : Fin (2 ^ L))
  | be (c : Fin (2 * L)) (q : Bool) (d : Fin (2 ^ L))
  deriving DecidableEq, Fintype

namespace HV

variable {L : ℕ}

/-- The layer of the rows handled by box `c` (`false`: `A₁, B₁`; `true`: `A₂, B₂`). -/
def layer (c : Fin (2 * L)) : Bool := decide (L ≤ c.val)

/-- The bit handled by box `c`. -/
def bit (c : Fin (2 * L)) : Fin L :=
  if h : L ≤ c.val then ⟨c.val - L, by omega⟩ else ⟨c.val, by omega⟩

/-- The box handling bit `h` of layer `ℓ`. -/
def boxOf (ℓ : Bool) (h : Fin L) : Fin (2 * L) :=
  ⟨if ℓ then L + h.val else h.val, by split <;> omega⟩

@[simp] lemma layer_boxOf (ℓ : Bool) (h : Fin L) : layer (boxOf ℓ h) = ℓ := by
  cases ℓ <;> simp [layer, boxOf]

@[simp] lemma bit_boxOf (ℓ : Bool) (h : Fin L) : bit (boxOf ℓ h) = h := by
  cases ℓ <;> simp [bit, boxOf]

lemma box_ext {c c' : Fin (2 * L)} (h1 : layer c = layer c') (h2 : bit c = bit c') : c = c' := by
  simp only [layer, bit, decide_eq_decide] at h1 h2
  ext
  split_ifs at h2 with ha hb hb <;> simp [Fin.ext_iff] at h2 <;> omega

@[simp] lemma boxOf_layer_bit (c : Fin (2 * L)) : boxOf (layer c) (bit c) = c :=
  box_ext (by simp) (by simp)

end HV

open HV

/-- A wheel assignment: line `q` of box `c` at position `d` visits the row
`row (W c q d).1 (layer c) (W c q d).2`. -/
abbrev Wheel (L : ℕ) := Fin (2 * L) → Bool → Fin (2 ^ L) → Bool × Idx L

variable {L : ℕ}

/-- The row vertex `wheel^{c,d}_q`. -/
def wrow (W : Wheel L) (c : Fin (2 * L)) (q : Bool) (d : Fin (2 ^ L)) : HV L :=
  .row (W c q d).1 (layer c) (W c q d).2

/-- `v` is the forward target of position `(c, q, d)`: `ℓ^{c,d+1}_q`, `g_{c+1}`, or
`r_{2L-1}` (for the last position of the last box). -/
def IsFwd (c : Fin (2 * L)) (q : Bool) (d : Fin (2 ^ L)) : HV L → Prop
  | .la c' q' d' => c' = c ∧ q' = q ∧ d'.val = d.val + 1
  | .g c' => d.val + 1 = 2 ^ L ∧ c'.val = c.val + 1
  | .r c' => d.val + 1 = 2 ^ L ∧ c.val + 1 = 2 * L ∧ c' = c
  | _ => False

/-- `v` is the backward target of position `(c, q, d)`: `ℓ^{c,d-1}_q`, `r_{c-1}`, or `s¹₁`. -/
def IsBwd (c : Fin (2 * L)) (q : Bool) (d : Fin (2 ^ L)) : HV L → Prop
  | .la c' q' d' => c' = c ∧ q' = q ∧ d.val = d'.val + 1
  | .r c' => d.val = 0 ∧ c.val = c'.val + 1
  | .sA1 => d.val = 0 ∧ c.val = 0
  | _ => False

instance (c : Fin (2 * L)) (q : Bool) (d : Fin (2 ^ L)) : DecidablePred (IsFwd c q d) :=
  fun v => by cases v <;> unfold IsFwd <;> infer_instance

instance (c : Fin (2 * L)) (q : Bool) (d : Fin (2 ^ L)) : DecidablePred (IsBwd c q d) :=
  fun v => by cases v <;> unfold IsBwd <;> infer_instance

/-- The input-independent arcs of `D_{x,y}`, listed by out-neighbourhood. -/
def baseArc (W : Wheel L) : HV L → HV L → Prop
  | .start, v => ∃ c : Fin (2 * L), c.val = 0 ∧ v = .g c
  | .stop, _ => False
  | .sA1, v => ∃ i, v = .row false false i
  | .sA2, v => v = .sB1
  | .sB1, v => ∃ i, v = .row true false i
  | .sB2, v => v = .stop
  | .row s ℓ i, v => (ℓ = true ∧ v = (if s then .sB2 else .sA2)) ∨
      ∃ c q d, v = .be c q d ∧ wrow W c q d = .row s ℓ i
  | .g c, v => ∃ q d, d.val = 0 ∧ v = .la c q d
  | .r c, v => ∃ q d, d.val + 1 = 2 ^ L ∧ v = .la c q d
  | .la c q d, v => v = .si c q d ∨ v = wrow W c q d
  | .si c q d, v => v = .be c q d ∨ IsFwd c q d v
  | .be c q d, v => v = .si c q d ∨ IsFwd c q d v ∨ IsBwd c q d v

instance (W : Wheel L) : DecidableRel (baseArc W) :=
  fun u v => by cases u <;> unfold baseArc <;> infer_instance

/-- Alice's input arcs `a^i_1 → a^j_2` (`x i j = 1`). -/
def xArc (x : Idx L → Idx L → Bool) (u v : HV L) : Prop :=
  ∃ i j, u = .row false false i ∧ v = .row false true j ∧ x i j = true

/-- Bob's input arcs `b^i_1 → b^j_2` (`y i j = 1`). -/
def yArc (y : Idx L → Idx L → Bool) (u v : HV L) : Prop :=
  ∃ i j, u = .row true false i ∧ v = .row true true j ∧ y i j = true

instance (x : Idx L → Idx L → Bool) : DecidableRel (xArc (L := L) x) :=
  fun u v => by unfold xArc; infer_instance

instance (y : Idx L → Idx L → Bool) : DecidableRel (yArc (L := L) y) :=
  fun u v => by unfold yArc; infer_instance

/-- The arcs of the digraph `D_{x,y}` (the paper's `G_{x,y}`). -/
def Arc (W : Wheel L) (x y : Idx L → Idx L → Bool) (u v : HV L) : Prop :=
  baseArc W u v ∨ xArc x u v ∨ yArc y u v

instance (W : Wheel L) (x y : Idx L → Idx L → Bool) : DecidableRel (Arc W x y) :=
  fun u v => by unfold Arc; infer_instance

/-- A directed Hamiltonian path of the digraph with arc relation `R`: a list of all vertices,
without repetitions, in which consecutive vertices are joined by arcs. -/
def HasHamPath {V : Type*} (R : V → V → Prop) : Prop :=
  ∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain R

/-! ### Basic facts about the arcs -/

section Arcs

variable {W : Wheel L} {x y : Idx L → Idx L → Bool}

lemma isFwd_unique {c : Fin (2 * L)} {q : Bool} {d : Fin (2 ^ L)} {v v' : HV L}
    (h : IsFwd c q d v) (h' : IsFwd c q d v') : v = v' := by
  cases v <;> cases v' <;> simp only [IsFwd] at h h'
  case la.la c1 q1 d1 c2 q2 d2 =>
    obtain ⟨rfl, rfl, h1⟩ := h; obtain ⟨rfl, rfl, h2⟩ := h'
    congr 1; ext; omega
  case g.g c1 c2 => simp only [HV.g.injEq, Fin.ext_iff]; omega
  case r.r c1 c2 => obtain ⟨_, _, rfl⟩ := h; obtain ⟨_, _, rfl⟩ := h'; rfl
  all_goals omega

lemma isBwd_unique {c : Fin (2 * L)} {q : Bool} {d : Fin (2 ^ L)} {v v' : HV L}
    (h : IsBwd c q d v) (h' : IsBwd c q d v') : v = v' := by
  cases v <;> cases v' <;> simp only [IsBwd] at h h'
  case la.la c1 q1 d1 c2 q2 d2 =>
    obtain ⟨rfl, rfl, h1⟩ := h; obtain ⟨rfl, rfl, h2⟩ := h'
    congr 1; ext; omega
  case r.r c1 c2 => simp only [HV.r.injEq, Fin.ext_iff]; omega
  all_goals first | rfl | omega

lemma not_isFwd_isBwd {c : Fin (2 * L)} {q : Bool} {d : Fin (2 ^ L)} {v : HV L}
    (h : IsFwd c q d v) (h' : IsBwd c q d v) : False := by
  cases v <;> simp only [IsFwd, IsBwd] at h h' <;> omega

lemma xArc_row {u v : HV L} (h : xArc x u v) :
    ∃ i j, u = .row false false i ∧ v = .row false true j := by
  obtain ⟨i, j, rfl, rfl, -⟩ := h; exact ⟨i, j, rfl, rfl⟩

lemma yArc_row {u v : HV L} (h : yArc y u v) :
    ∃ i j, u = .row true false i ∧ v = .row true true j := by
  obtain ⟨i, j, rfl, rfl, -⟩ := h; exact ⟨i, j, rfl, rfl⟩

/-- `u` is not a row vertex. -/
def NotRow (u : HV L) : Prop := ∀ s ℓ i, u ≠ .row s ℓ i

lemma arc_iff_base_left {u v : HV L} (hu : NotRow u) : Arc W x y u v ↔ baseArc W u v := by
  unfold Arc
  constructor
  · rintro (h | h | h)
    · exact h
    · obtain ⟨i, j, rfl, -⟩ := xArc_row h; exact absurd rfl (hu _ _ _)
    · obtain ⟨i, j, rfl, -⟩ := yArc_row h; exact absurd rfl (hu _ _ _)
  · exact Or.inl

lemma arc_iff_base_right {u v : HV L} (hv : NotRow v) : Arc W x y u v ↔ baseArc W u v := by
  unfold Arc
  constructor
  · rintro (h | h | h)
    · exact h
    · obtain ⟨i, j, -, rfl⟩ := xArc_row h; exact absurd rfl (hv _ _ _)
    · obtain ⟨i, j, -, rfl⟩ := yArc_row h; exact absurd rfl (hv _ _ _)
  · exact Or.inl

@[simp] lemma notRow_start : NotRow (L := L) .start := fun _ _ _ h => by cases h
@[simp] lemma notRow_stop : NotRow (L := L) .stop := fun _ _ _ h => by cases h
@[simp] lemma notRow_sA1 : NotRow (L := L) .sA1 := fun _ _ _ h => by cases h
@[simp] lemma notRow_sA2 : NotRow (L := L) .sA2 := fun _ _ _ h => by cases h
@[simp] lemma notRow_sB1 : NotRow (L := L) .sB1 := fun _ _ _ h => by cases h
@[simp] lemma notRow_sB2 : NotRow (L := L) .sB2 := fun _ _ _ h => by cases h
@[simp] lemma notRow_g (c) : NotRow (L := L) (.g c) := fun _ _ _ h => by cases h
@[simp] lemma notRow_r (c) : NotRow (L := L) (.r c) := fun _ _ _ h => by cases h
@[simp] lemma notRow_la (c q d) : NotRow (L := L) (.la c q d) := fun _ _ _ h => by cases h
@[simp] lemma notRow_si (c q d) : NotRow (L := L) (.si c q d) := fun _ _ _ h => by cases h
@[simp] lemma notRow_be (c q d) : NotRow (L := L) (.be c q d) := fun _ _ _ h => by cases h

lemma not_arc_into_start (u : HV L) : ¬ Arc W x y u .start := by
  rw [arc_iff_base_right (by simp)]
  cases u <;> simp [baseArc, IsFwd, IsBwd, wrow]
  case row s ℓ i => cases s <;> simp

lemma not_arc_from_stop (v : HV L) : ¬ Arc W x y .stop v := by
  rw [arc_iff_base_left (by simp)]; simp [baseArc]

lemma arc_into_si {u : HV L} {c q d} :
    Arc W x y u (.si c q d) ↔ u = .la c q d ∨ u = .be c q d := by
  rw [arc_iff_base_right (by simp)]
  cases u <;> simp [baseArc, IsFwd, IsBwd, wrow] <;> try tauto
  case row s ℓ i => cases s <;> simp

lemma arc_into_be {u : HV L} {c q d} :
    Arc W x y u (.be c q d) ↔ u = .si c q d ∨ u = wrow W c q d := by
  rw [arc_iff_base_right (by simp)]
  cases u
  case row s ℓ i =>
    simp only [baseArc]
    constructor
    · rintro (⟨_, h⟩ | ⟨c', q', d', h1, h2⟩)
      · cases s <;> simp at h
      · simp only [HV.be.injEq] at h1
        obtain ⟨rfl, rfl, rfl⟩ := h1
        exact Or.inr h2.symm
    · rintro (h | h)
      · cases h
      · exact Or.inr ⟨c, q, d, rfl, h.symm⟩
  all_goals simp [baseArc, IsFwd, IsBwd, wrow]
  all_goals tauto

lemma arc_into_la {u : HV L} {c q d} :
    Arc W x y u (.la c q d) ↔ (u = .g c ∧ d.val = 0) ∨ (u = .r c ∧ d.val + 1 = 2 ^ L) ∨
      (∃ d' : Fin (2 ^ L), d.val = d'.val + 1 ∧ (u = .si c q d' ∨ u = .be c q d')) ∨
      (∃ d' : Fin (2 ^ L), d'.val = d.val + 1 ∧ u = .be c q d') := by
  rw [arc_iff_base_right (by simp)]
  cases u <;> simp [baseArc, IsFwd, IsBwd, wrow]
  case row s ℓ i => cases s <;> simp
  all_goals aesop

lemma arc_from_la {v : HV L} {c q d} :
    Arc W x y (.la c q d) v ↔ v = .si c q d ∨ v = wrow W c q d := by
  rw [arc_iff_base_left (by simp)]; rfl

lemma arc_from_si {v : HV L} {c q d} :
    Arc W x y (.si c q d) v ↔ v = .be c q d ∨ IsFwd c q d v := by
  rw [arc_iff_base_left (by simp)]; rfl

lemma arc_from_be {v : HV L} {c q d} :
    Arc W x y (.be c q d) v ↔ v = .si c q d ∨ IsFwd c q d v ∨ IsBwd c q d v := by
  rw [arc_iff_base_left (by simp)]; rfl

lemma arc_from_g {v : HV L} {c} :
    Arc W x y (.g c) v ↔ ∃ q d, d.val = 0 ∧ v = .la c q d := by
  rw [arc_iff_base_left (by simp)]; rfl

lemma arc_from_r {v : HV L} {c} :
    Arc W x y (.r c) v ↔ ∃ q d, d.val + 1 = 2 ^ L ∧ v = .la c q d := by
  rw [arc_iff_base_left (by simp)]; rfl

lemma arc_from_start {v : HV L} :
    Arc W x y .start v ↔ ∃ c : Fin (2 * L), c.val = 0 ∧ v = .g c := by
  rw [arc_iff_base_left (by simp)]; rfl

lemma arc_from_sA1 {v : HV L} : Arc W x y .sA1 v ↔ ∃ i, v = .row false false i := by
  rw [arc_iff_base_left (by simp)]; rfl

lemma arc_from_sA2 {v : HV L} : Arc W x y .sA2 v ↔ v = .sB1 := by
  rw [arc_iff_base_left (by simp)]; rfl

lemma arc_from_sB1 {v : HV L} : Arc W x y .sB1 v ↔ ∃ i, v = .row true false i := by
  rw [arc_iff_base_left (by simp)]; rfl

lemma arc_from_sB2 {v : HV L} : Arc W x y .sB2 v ↔ v = .stop := by
  rw [arc_iff_base_left (by simp)]; rfl

lemma arc_into_row {u : HV L} {s ℓ i} (h : Arc W x y u (.row s ℓ i)) :
    (s = false ∧ ℓ = false ∧ u = .sA1) ∨ (s = true ∧ ℓ = false ∧ u = .sB1) ∨
      (∃ c q d, u = .la c q d ∧ wrow W c q d = .row s ℓ i) ∨
      (ℓ = true ∧ ∃ i', u = .row s false i') := by
  rcases h with h | h | h
  · cases u <;> simp [baseArc, IsFwd, IsBwd] at h
    · simp_all
    · simp_all
    · rename_i s' ℓ' i'
      cases s' <;> simp at h
    · rename_i c q d
      exact Or.inr (Or.inr (Or.inl ⟨c, q, d, rfl, h.symm⟩))
  · obtain ⟨i', j, rfl, h2, -⟩ := h
    simp only [HV.row.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp
  · obtain ⟨i', j, rfl, h2, -⟩ := h
    simp only [HV.row.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp

lemma arc_from_row {v : HV L} {s ℓ i} (h : Arc W x y (.row s ℓ i) v) :
    (ℓ = true ∧ v = (if s then .sB2 else .sA2)) ∨
      (∃ c q d, v = .be c q d ∧ wrow W c q d = .row s ℓ i) ∨
      (ℓ = false ∧ ∃ j, v = .row s true j ∧ (if s then y else x) i j = true) := by
  rcases h with h | h | h
  · simp only [baseArc] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · obtain ⟨i', j, h1, rfl, hx⟩ := h
    simp only [HV.row.injEq] at h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    simp [hx]
  · obtain ⟨i', j, h1, rfl, hy⟩ := h
    simp only [HV.row.injEq] at h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    simp [hy]

end Arcs

end HardnessOptimization.HamPath
