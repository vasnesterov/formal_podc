import Papers.PODC2026.LCLDefinitions.Local

/-!
# Gadgeted graphs (Section 5.1 of the paper)

Definitions for Section 5 of *It does not matter how you define locally checkable labelings*
(Cruciani, Das, Raevskaya, Suomela; PODC 2026 brief announcement, full version arXiv:2602.18188).

* `Base`: a base graph `G` given by an edge type `E` with endpoint maps `src tgt : E → V` and the edge
  colouring `len : E → ℕ` (the paper's `x`). `Base.G0` is the underlying simple graph.
* `Base.Vert`, `Base.graph`: the gadgeted graph `gadget(G, x)`: every edge `e` is replaced by an
  *expanded edge*, a chain of `len e` A-gadgets. The vertices of the chain of `e` are `gad e k`,
  `k < 6 * len e`; the `i`-th gadget consists of positions `6i, …, 6i+5`.
  We number the six vertices of an A-gadget so that the chain is a path `k — k+1` plus the chords
  `6i — 6i+2`, `6i+1 — 6i+4`, `6i+3 — 6i+5`. In the paper's numbering `1, …, 6` of Figure 1a the
  positions `0, …, 5` are the paper's vertices `1, 2, 3, 5, 4, 6` (paper edges `{1,2}, {1,3}, {2,3},
  {2,4}, {3,5}, {4,5}, {4,6}, {5,6}` become `01, 02, 12, 14, 23, 34, 45, 35`). With this numbering the
  reflection of an A-gadget is `j ↦ 5 - j`, so reading a chain backwards is `k ↦ 6 * len e - 1 - k`.
* Gadgeted distance: the paper's weight `w` is `1/2` on edges at an original vertex and `0`
  otherwise. We use the doubled weight `wt ∈ {0, 1}`, so `gd2 u v = 2 * gdist(u, v)` and
  `gball r v = {u | gd2 v u ≤ 2 r}` is the paper's `r`-gball.
* The hypotheses of Theorem 5.1: `IsDist2Coloring` (condition 1), `IsEdgeConsistentIn` (condition 2,
  literally: for every edge `{v, u}` and every `v' ∈ gball_r(v)` with `χ v' = χ v` there is a
  neighbour `u'` of `v'` with `χ u' = χ u`) and `IsDistEdgeColoring` (`x` is a distance-`k` edge
  colouring: edges at distance `≤ k` in the line graph get different colours).
-/

namespace Podc.LCLDefinitions

open SimpleGraph

/-- A base graph with an edge colouring: vertices `V`, edges `E` with endpoints `src e`, `tgt e`
(the orientation is only used to lay out the expanded edge), and colours `len e` (the number of
A-gadgets on the expanded edge). -/
structure Base where
  /-- Vertices of the base graph. -/
  V : Type
  /-- Edges of the base graph. -/
  E : Type
  /-- First endpoint. -/
  src : E → V
  /-- Second endpoint. -/
  tgt : E → V
  /-- The edge colouring `x`: the length of the expanded edge. -/
  len : E → ℕ

namespace Base

variable (B : Base)

/-- The underlying simple graph of the base graph. -/
def G0 : SimpleGraph B.V where
  Adj a b := a ≠ b ∧ ∃ e, (B.src e = a ∧ B.tgt e = b) ∨ (B.src e = b ∧ B.tgt e = a)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _ h => h.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The base graph is simple: no loops and no parallel edges. -/
def IsSimple : Prop :=
  (∀ e, B.src e ≠ B.tgt e) ∧
    ∀ e e', s(B.src e, B.tgt e) = s(B.src e', B.tgt e') → e = e'

/-- The base graph is 3-regular: every vertex is an endpoint of exactly three edges. -/
def IsCubic : Prop := ∀ v, {e | B.src e = v ∨ B.tgt e = v}.ncard = 3

/-- The endpoints of an edge. -/
def ends (e : B.E) : Set B.V := {B.src e, B.tgt e}

/-- `len` is a distance-`k` edge colouring: two distinct edges at distance `≤ k` in the line graph
(i.e. with endpoints at distance `≤ k - 1` in the base graph) have different colours. -/
def IsDistEdgeColoring (k : ℕ) : Prop :=
  ∀ e e', e ≠ e' → (∃ a ∈ B.ends e, ∃ b ∈ B.ends e', B.G0.edist a b + 1 ≤ k) → B.len e ≠ B.len e'

/-- Vertices of the gadgeted graph: original vertices and gadget vertices. -/
inductive Vert
  | /-- An original vertex. -/ orig (v : B.V)
  | /-- Position `k` on the expanded edge `e`. -/ gad (e : B.E) (k : Fin (6 * B.len e))

/-- Internal edges of an A-gadget, in our numbering of its vertices. -/
def InnerAdj (a b : ℕ) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨
  (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) ∨
  (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) ∨
  (a = 3 ∧ b = 5) ∨ (a = 5 ∧ b = 3) ∨ (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4)

/-- Adjacency of two positions on an expanded edge. -/
def CAdj (a b : ℕ) : Prop :=
  (a / 6 = b / 6 ∧ InnerAdj (a % 6) (b % 6)) ∨ (a % 6 = 5 ∧ b = a + 1) ∨ (b % 6 = 5 ∧ a = b + 1)

lemma innerAdj_symm {a b : ℕ} (h : InnerAdj a b) : InnerAdj b a := by
  unfold InnerAdj at *
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

lemma innerAdj_irrefl (a : ℕ) : ¬ InnerAdj a a := by
  unfold InnerAdj
  rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩) <;> simp at h

lemma cadj_symm {a b : ℕ} (h : CAdj a b) : CAdj b a := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, innerAdj_symm h2⟩
  · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)

lemma cadj_irrefl (a : ℕ) : ¬ CAdj a a := by
  rintro (⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩)
  · exact innerAdj_irrefl _ h
  · omega
  · omega

/-- Adjacency in the gadgeted graph. -/
def Adj : B.Vert → B.Vert → Prop
  | .orig _, .orig _ => False
  | .orig v, .gad e k => (v = B.src e ∧ k.val = 0) ∨ (v = B.tgt e ∧ k.val + 1 = 6 * B.len e)
  | .gad e k, .orig v => (v = B.src e ∧ k.val = 0) ∨ (v = B.tgt e ∧ k.val + 1 = 6 * B.len e)
  | .gad e k, .gad e' k' => e = e' ∧ CAdj k.val k'.val

/-- The gadgeted graph `gadget(G, x)` (Section 5.1). -/
def graph : SimpleGraph B.Vert where
  Adj := B.Adj
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp only [Adj] at h ⊢
    · exact h
    · exact h
    · exact ⟨h.1.symm, cadj_symm h.2⟩⟩
  loopless := ⟨by
    intro a h
    cases a <;> simp only [Adj] at h
    exact cadj_irrefl _ h.2⟩

/-- Doubled weight of a pair of vertices: `1` if one of them is original, else `0`
(the paper's weight `w` is half of it). -/
def wt : B.Vert → B.Vert → ℕ
  | .orig _, _ => 1
  | _, .orig _ => 1
  | _, _ => 0

/-- Doubled weight of a walk. -/
def walkWt : {u v : B.Vert} → B.graph.Walk u v → ℕ
  | _, _, .nil => 0
  | u, _, .cons (v := w) _ p => B.wt u w + walkWt p

/-- Doubled gadgeted distance: `gd2 u v = 2 * gdist(u, v)`. -/
noncomputable def gd2 (u v : B.Vert) : ℕ∞ := ⨅ p : B.graph.Walk u v, (B.walkWt p : ℕ∞)

/-- The `r`-gball of `v`: all vertices at gadgeted distance `≤ r`. -/
def gball (r : ℕ) (v : B.Vert) : Set B.Vert := {u | B.gd2 v u ≤ 2 * r}

/-- Condition 1 of Theorem 5.1: `χ` is a distance-2 colouring (injective on every closed
neighbourhood). -/
def IsDist2Coloring {C : Type*} (χ : B.Vert → C) : Prop := IsDist2 B.graph χ

/-- Condition 2 of Theorem 5.1, as stated in the paper: `χ` is edge-consistent in every `r`-gball:
for every edge `{v, u}` and every `v' ∈ gball_r(v)` with `χ v' = χ v` there is a neighbour `u'` of
`v'` with `χ u' = χ u`. -/
def IsEdgeConsistentIn {C : Type*} (r : ℕ) (χ : B.Vert → C) : Prop :=
  ∀ v u, B.graph.Adj v u → ∀ v' ∈ B.gball r v, χ v' = χ v → ∃ u', B.graph.Adj v' u' ∧ χ u' = χ u

/-- Global edge-consistency (the hypothesis of our repaired Theorem 5.1): for every edge `{v, u}`
and every `v'` with `χ v' = χ v` there is a neighbour `u'` of `v'` with `χ u' = χ u`. -/
def IsEdgeConsistent {C : Type*} (χ : B.Vert → C) : Prop := IsCons B.graph χ

/-- The conclusion of Theorem 5.1: `χ` is a correct gdistance-`2r` original colouring, i.e. for
every original vertex `v`, all vertices of `gball_r(v)` have distinct colours. -/
def IsGDistOrigColoring {C : Type*} (r : ℕ) (χ : B.Vert → C) : Prop :=
  ∀ v, Set.InjOn χ (B.gball r (.orig v))

/-! ### Arithmetic of positions on an expanded edge -/

lemma cadj_iff {p q s t : ℕ} (hs : s < 6) (ht : t < 6) :
    CAdj (6 * p + s) (6 * q + t) ↔
      (p = q ∧ InnerAdj s t) ∨ (s = 5 ∧ t = 0 ∧ q = p + 1) ∨ (t = 5 ∧ s = 0 ∧ p = q + 1) := by
  have h1 : (6 * p + s) / 6 = p := by omega
  have h2 : (6 * q + t) / 6 = q := by omega
  have h3 : (6 * p + s) % 6 = s := by omega
  have h4 : (6 * q + t) % 6 = t := by omega
  unfold CAdj
  rw [h1, h2, h3, h4]
  constructor
  · rintro (h | ⟨h5, h6⟩ | ⟨h5, h6⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h5, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨h5, by omega, by omega⟩)
  · rintro (h | ⟨h5, h6, h7⟩ | ⟨h5, h6, h7⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h5, by omega⟩)
    · exact Or.inr (Or.inr ⟨h5, by omega⟩)

lemma innerAdj_rev {s t : ℕ} (hs : s < 6) (ht : t < 6) : InnerAdj (5 - s) (5 - t) ↔ InnerAdj s t := by
  unfold InnerAdj
  interval_cases s <;> interval_cases t <;> simp

lemma innerAdj_lt {s t : ℕ} (h : InnerAdj s t) : s < 6 ∧ t < 6 := by
  unfold InnerAdj at h; omega

/-- Adjacency of positions is invariant under reading the chain backwards. -/
lemma cadj_rev {L a b : ℕ} (ha : a < 6 * L) (hb : b < 6 * L) :
    CAdj (6 * L - 1 - a) (6 * L - 1 - b) ↔ CAdj a b := by
  obtain ⟨p, s, hs, rfl⟩ : ∃ p s, s < 6 ∧ a = 6 * p + s := ⟨a / 6, a % 6, by omega, by omega⟩
  obtain ⟨q, t, ht, rfl⟩ : ∃ q t, t < 6 ∧ b = 6 * q + t := ⟨b / 6, b % 6, by omega, by omega⟩
  have e1 : 6 * L - 1 - (6 * p + s) = 6 * (L - 1 - p) + (5 - s) := by omega
  have e2 : 6 * L - 1 - (6 * q + t) = 6 * (L - 1 - q) + (5 - t) := by omega
  rw [e1, e2, cadj_iff (by omega) (by omega), cadj_iff hs ht, innerAdj_rev hs ht]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨by omega, h2⟩
    · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨by omega, h2⟩
    · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)

/-! ### Directions along expanded edges -/

/-- A direction along an expanded edge: `(e, true)` reads the chain of `e` starting from `src e`,
`(e, false)` starting from `tgt e`. -/
abbrev Dir := B.E × Bool

variable {B}

/-- The original vertex where a direction starts. -/
def start (d : B.Dir) : B.V := if d.2 then B.src d.1 else B.tgt d.1

/-- The original vertex where a direction ends. -/
def stop (d : B.Dir) : B.V := if d.2 then B.tgt d.1 else B.src d.1

/-- The reversed direction. -/
def rev (d : B.Dir) : B.Dir := (d.1, !d.2)

/-- The vertex at position `k` (counted from `start d`) of the expanded edge of `d`; junk
(`orig (src e)`) if `k ≥ 6 * len e`. -/
def pos (d : B.Dir) (k : ℕ) : B.Vert :=
  if h : k < 6 * B.len d.1 then
    if d.2 then .gad d.1 ⟨k, h⟩ else .gad d.1 ⟨6 * B.len d.1 - 1 - k, by omega⟩
  else .orig (B.src d.1)

@[simp] lemma start_rev (d : B.Dir) : start (rev d) = stop d := by
  unfold start stop rev; cases d.2 <;> simp

@[simp] lemma stop_rev (d : B.Dir) : stop (rev d) = start d := by
  unfold start stop rev; cases d.2 <;> simp

@[simp] lemma rev_fst (d : B.Dir) : (rev d).1 = d.1 := rfl

lemma pos_rev (d : B.Dir) {k : ℕ} (hk : k < 6 * B.len d.1) : pos (rev d) k = pos d (6 * B.len d.1 - 1 - k) := by
  obtain ⟨e, b⟩ := d
  dsimp only at hk ⊢
  cases b <;> simp [pos, rev, hk, show 6 * B.len e - 1 - k < 6 * B.len e by omega] <;>
    exact Fin.ext (by simp; omega)

lemma pos_ne_orig (d : B.Dir) {k : ℕ} (hk : k < 6 * B.len d.1) (v : B.V) : pos d k ≠ .orig v := by
  unfold pos; split_ifs <;> simp

lemma pos_eq_gad (d : B.Dir) {k : ℕ} (hk : k < 6 * B.len d.1) :
    ∃ m : Fin (6 * B.len d.1), pos d k = .gad d.1 m := by
  unfold pos; split_ifs <;> exact ⟨_, rfl⟩

lemma pos_inj (d : B.Dir) {k k' : ℕ} (hk : k < 6 * B.len d.1) (hk' : k' < 6 * B.len d.1) :
    pos d k = pos d k' ↔ k = k' := by
  obtain ⟨e, b⟩ := d
  dsimp only at hk hk' ⊢
  cases b <;> simp [pos, hk, hk'] <;> omega

lemma gad_eq_pos (e : B.E) (k : Fin (6 * B.len e)) : Vert.gad e k = pos (e, true) k.val := by
  simp [pos, k.isLt]

lemma adj_pos_pos (d : B.Dir) {k k' : ℕ} (hk : k < 6 * B.len d.1) (hk' : k' < 6 * B.len d.1) :
    B.graph.Adj (pos d k) (pos d k') ↔ CAdj k k' := by
  obtain ⟨e, b⟩ := d
  cases b
  · simp only [pos, hk, hk', dite_true, Bool.false_eq_true, ite_false]
    show (e = e ∧ _) ↔ _
    simp only [true_and]
    exact cadj_rev hk hk'
  · simp only [pos, hk, hk', dite_true, ite_true]
    show (e = e ∧ _) ↔ _
    simp

lemma adj_orig_pos (d : B.Dir) {k : ℕ} (hk : k < 6 * B.len d.1) (v : B.V) :
    B.graph.Adj (.orig v) (pos d k) ↔ (k = 0 ∧ v = start d) ∨ (k + 1 = 6 * B.len d.1 ∧ v = stop d) := by
  obtain ⟨e, b⟩ := d
  cases b
  · simp only [pos, hk, dite_true, Bool.false_eq_true, ite_false, start, stop]
    show (_ ∨ _) ↔ _
    simp only [] at hk ⊢
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inr ⟨by omega, h1⟩
      · exact Or.inl ⟨by omega, h1⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inr ⟨h2, by omega⟩
      · exact Or.inl ⟨h2, by omega⟩
  · simp only [pos, hk, dite_true, ite_true, start, stop]
    show (_ ∨ _) ↔ _
    simp only [] at hk ⊢
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr ⟨h2, h1⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr ⟨h2, h1⟩

/-- The neighbours of an original vertex are the first vertices of the expanded edges leaving it. -/
lemma adj_orig_iff (v : B.V) (y : B.Vert) :
    B.graph.Adj (.orig v) y ↔ ∃ d : B.Dir, start d = v ∧ 0 < B.len d.1 ∧ y = pos d 0 := by
  constructor
  · intro h
    cases y with
    | orig w => exact absurd h id
    | gad e k =>
      have hk := k.isLt
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨(e, true), by simp [start, h1], by simp only; omega, ?_⟩
        simp [pos, hk.trans_le' (le_refl _), show 0 < 6 * B.len e by omega]
        exact Fin.ext h2
      · refine ⟨(e, false), by simp [start, h1], by simp only; omega, ?_⟩
        simp [pos, show 0 < 6 * B.len e by omega]
        exact Fin.ext (by simp; omega)
  · rintro ⟨d, rfl, hL, rfl⟩
    exact (adj_orig_pos d (by omega) _).2 (Or.inl ⟨rfl, rfl⟩)

/-- Characterisation of the neighbours of a gadget vertex. -/
lemma adj_pos_iff (d : B.Dir) {k : ℕ} (hk : k < 6 * B.len d.1) (y : B.Vert) :
    B.graph.Adj (pos d k) y ↔
      (∃ k', k' < 6 * B.len d.1 ∧ CAdj k k' ∧ y = pos d k') ∨
        (k = 0 ∧ y = .orig (start d)) ∨ (k + 1 = 6 * B.len d.1 ∧ y = .orig (stop d)) := by
  constructor
  · intro h
    cases y with
    | orig w =>
      have := (adj_orig_pos d hk w).1 (h.symm)
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1, by rw [h2]⟩)
      · exact Or.inr (Or.inr ⟨h1, by rw [h2]⟩)
    | gad e m =>
      obtain ⟨m0, hm0⟩ := pos_eq_gad d hk
      have he : e = d.1 := by
        rw [hm0] at h; exact h.1.symm
      subst he
      -- `gad d.1 m` is some position of `d`
      obtain ⟨k', hk', hk'e⟩ : ∃ k', k' < 6 * B.len d.1 ∧ pos d k' = .gad d.1 m := by
        obtain ⟨e, b⟩ := d
        dsimp only at m hk ⊢
        cases b
        · refine ⟨6 * B.len e - 1 - m.val, by have := m.isLt; omega, ?_⟩
          have := m.isLt
          simp [pos, show 6 * B.len e - 1 - m.val < 6 * B.len e by omega]
          exact Fin.ext (by simp; omega)
        · exact ⟨m.val, m.isLt, by simp [pos, m.isLt]⟩
      rw [← hk'e] at h ⊢
      exact Or.inl ⟨k', hk', (adj_pos_pos d hk hk').1 h, rfl⟩
  · rintro (⟨k', hk', hc, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, rfl⟩)
    · exact (adj_pos_pos d hk hk').2 hc
    · exact ((adj_orig_pos d hk _).2 (Or.inl ⟨rfl, rfl⟩)).symm
    · exact ((adj_orig_pos d hk _).2 (Or.inr ⟨h1, rfl⟩)).symm

/-- The vertex before position `k` along `d`. -/
def prevV (d : B.Dir) (k : ℕ) : B.Vert := if k = 0 then .orig (start d) else pos d (k - 1)

/-- The vertex after position `k` along `d`. -/
def nextV (d : B.Dir) (k : ℕ) : B.Vert :=
  if k + 1 = 6 * B.len d.1 then .orig (stop d) else pos d (k + 1)

lemma adj_pp (d : B.Dir) {k k' : ℕ} (hk : k < 6 * B.len d.1) (hk' : k' < 6 * B.len d.1)
    (h : CAdj k k') : B.graph.Adj (pos d k) (pos d k') := (adj_pos_pos d hk hk').2 h

/-- Consecutive positions are adjacent. -/
lemma cadj_succ (k : ℕ) : CAdj k (k + 1) := by
  obtain ⟨p, s, hs, rfl⟩ : ∃ p s, s < 6 ∧ k = 6 * p + s := ⟨k / 6, k % 6, by omega, by omega⟩
  by_cases h5 : s = 5
  · subst h5
    rw [show 6 * p + 5 + 1 = 6 * (p + 1) + 0 by ring, cadj_iff (by norm_num) (by norm_num)]
    exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · rw [show 6 * p + s + 1 = 6 * p + (s + 1) by ring, cadj_iff hs (by omega)]
    left; refine ⟨rfl, ?_⟩
    unfold InnerAdj
    interval_cases s <;> simp_all

/-- Explicit form of `CAdj k k'`. -/
lemma cadj_cases {k k' : ℕ} (hc : CAdj k k') :
    (k % 6 = 0 ∧ (k' + 1 = k ∨ k' = k + 1 ∨ k' = k + 2)) ∨
    (k % 6 = 1 ∧ (k' = k - 1 ∨ k' = k + 1 ∨ k' = k + 3)) ∨
    (k % 6 = 2 ∧ (k' = k - 2 ∨ k' = k - 1 ∨ k' = k + 1)) ∨
    (k % 6 = 3 ∧ (k' = k - 1 ∨ k' = k + 1 ∨ k' = k + 2)) ∨
    (k % 6 = 4 ∧ (k' = k - 3 ∨ k' = k - 1 ∨ k' = k + 1)) ∨
    (k % 6 = 5 ∧ (k' = k - 2 ∨ k' = k - 1 ∨ k' = k + 1)) := by
  obtain ⟨p, s, hs, rfl⟩ : ∃ p s, s < 6 ∧ k = 6 * p + s := ⟨k / 6, k % 6, by omega, by omega⟩
  obtain ⟨q, t, ht, rfl⟩ : ∃ q t, t < 6 ∧ k' = 6 * q + t := ⟨k' / 6, k' % 6, by omega, by omega⟩
  rw [cadj_iff hs ht] at hc
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · unfold InnerAdj at h2
    rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · omega
  · omega

lemma adj_prevV (d : B.Dir) {k : ℕ} (hk : k < 6 * B.len d.1) :
    B.graph.Adj (prevV d k) (pos d k) := by
  unfold prevV
  split_ifs with h
  · subst h; exact (adj_orig_pos d hk _).2 (Or.inl ⟨rfl, rfl⟩)
  · have := adj_pp d (k := k - 1) (by omega) hk (by have := cadj_succ (k - 1); rwa [Nat.sub_add_cancel (by omega)] at this)
    exact this

lemma adj_nextV (d : B.Dir) {k : ℕ} (hk : k < 6 * B.len d.1) :
    B.graph.Adj (pos d k) (nextV d k) := by
  unfold nextV
  split_ifs with h
  · exact ((adj_orig_pos d hk _).2 (Or.inr ⟨h, rfl⟩)).symm
  · exact adj_pp d hk (by omega) (cadj_succ k)

lemma prevV_ne (d : B.Dir) {k k' : ℕ} (hk : k < 6 * B.len d.1) (hk' : k' < 6 * B.len d.1)
    (h : k' + 1 ≠ k) : prevV d k ≠ pos d k' := by
  unfold prevV
  split_ifs with h0
  · exact (pos_ne_orig d hk' _).symm
  · rw [Ne, pos_inj d (by omega) hk']; omega

lemma nextV_ne (d : B.Dir) {k k' : ℕ} (hk : k < 6 * B.len d.1) (hk' : k' < 6 * B.len d.1)
    (h : k + 1 ≠ k') : nextV d k ≠ pos d k' := by
  unfold nextV
  split_ifs with h0
  · exact (pos_ne_orig d hk' _).symm
  · rw [Ne, pos_inj d (by omega) hk']; omega

/-- The neighbours of position `k` along `d`, as an explicit triple depending on `k mod 6`. -/
lemma adj_pos_cases (d : B.Dir) {k : ℕ} (hk : k < 6 * B.len d.1) (hL : 6 ∣ 6 * B.len d.1)
    {y : B.Vert} (h : B.graph.Adj (pos d k) y) :
    (k % 6 = 0 ∧ (y = prevV d k ∨ y = pos d (k + 1) ∨ y = pos d (k + 2))) ∨
    (k % 6 = 1 ∧ (y = pos d (k - 1) ∨ y = pos d (k + 1) ∨ y = pos d (k + 3))) ∨
    (k % 6 = 2 ∧ (y = pos d (k - 2) ∨ y = pos d (k - 1) ∨ y = pos d (k + 1))) ∨
    (k % 6 = 3 ∧ (y = pos d (k - 1) ∨ y = pos d (k + 1) ∨ y = pos d (k + 2))) ∨
    (k % 6 = 4 ∧ (y = pos d (k - 3) ∨ y = pos d (k - 1) ∨ y = pos d (k + 1))) ∨
    (k % 6 = 5 ∧ (y = pos d (k - 2) ∨ y = pos d (k - 1) ∨ y = nextV d k)) := by
  rcases (adj_pos_iff d hk y).1 h with ⟨k', hk', hc, rfl⟩ | ⟨h0, rfl⟩ | ⟨h1, rfl⟩
  · have key := cadj_cases hc
    have pv : k' + 1 = k → pos d k' = prevV d k := by
      intro h; unfold prevV; rw [if_neg (by omega)]; congr 1; omega
    have nx : k' = k + 1 → pos d k' = nextV d k := by
      intro h; unfold nextV; rw [if_neg (by omega)]; congr 1
    rcases key with ⟨a, b | b | b⟩ | ⟨a, b | b | b⟩ | ⟨a, b | b | b⟩ | ⟨a, b | b | b⟩ |
      ⟨a, b | b | b⟩ | ⟨a, b | b | b⟩
    all_goals first
      | exact Or.inl ⟨a, Or.inl (pv b)⟩
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, Or.inr (Or.inr (nx b))⟩))))
      | (subst b; simp [a]; done)
  · subst h0
    left; refine ⟨rfl, Or.inl ?_⟩; simp [prevV]
  · right; right; right; right; right
    obtain ⟨m, hm⟩ := hL
    refine ⟨by omega, Or.inr (Or.inr ?_)⟩
    simp [nextV, h1]

lemma cadj_in (i : ℕ) {s t : ℕ} (h : InnerAdj s t) : CAdj (6 * i + s) (6 * i + t) := by
  obtain ⟨hs, ht⟩ := innerAdj_lt h
  exact (cadj_iff hs ht).2 (Or.inl ⟨rfl, h⟩)

/-- The `i`-th A-gadget along `d`, with the vertices before and after it, has the local structure
recorded in `BlockFacts`. -/
lemma blockFacts (d : B.Dir) {i : ℕ} (hi : i < B.len d.1) :
    BlockFacts B.graph (prevV d (6 * i)) (pos d (6 * i)) (pos d (6 * i + 1)) (pos d (6 * i + 2))
      (pos d (6 * i + 3)) (pos d (6 * i + 4)) (pos d (6 * i + 5)) (nextV d (6 * i + 5)) := by
  have hL : 6 ∣ 6 * B.len d.1 := dvd_mul_right _ _
  have h5 : 6 * i + 5 < 6 * B.len d.1 := by omega
  have e0 : pos d (6 * i) = pos d (6 * i + 0) := rfl
  have A : ∀ s t, InnerAdj s t → B.graph.Adj (pos d (6 * i + s)) (pos d (6 * i + t)) :=
    fun s t h => adj_pp d (by have := innerAdj_lt h; omega) (by have := innerAdj_lt h; omega)
      (cadj_in i h)
  refine
    { a0 := adj_prevV d (by omega)
      a01 := by rw [e0]; exact A 0 1 (by simp [InnerAdj])
      a02 := by rw [e0]; exact A 0 2 (by simp [InnerAdj])
      a12 := A 1 2 (by simp [InnerAdj])
      a14 := A 1 4 (by simp [InnerAdj])
      a23 := A 2 3 (by simp [InnerAdj])
      a34 := A 3 4 (by simp [InnerAdj])
      a35 := A 3 5 (by simp [InnerAdj])
      a45 := A 4 5 (by simp [InnerAdj])
      a5 := adj_nextV d h5
      n0 := ?_, n1 := ?_, n2 := ?_, n3 := ?_, n4 := ?_, n5 := ?_
      d03 := by rw [Ne, pos_inj d (by omega) (by omega)]; omega
      d04 := by rw [Ne, pos_inj d (by omega) (by omega)]; omega
      d13 := by rw [Ne, pos_inj d (by omega) (by omega)]; omega
      d24 := by rw [Ne, pos_inj d (by omega) (by omega)]; omega
      d25 := by rw [Ne, pos_inj d (by omega) (by omega)]; omega
      dv1 := prevV_ne d (by omega) (by omega) (by omega)
      dv2 := prevV_ne d (by omega) (by omega) (by omega)
      dn3 := nextV_ne d h5 (by omega) (by omega)
      dn4 := nextV_ne d h5 (by omega) (by omega) }
  all_goals
    intro y hy
    rcases adj_pos_cases d (Nat.lt_of_le_of_lt (by omega) h5) hL hy with ⟨hm, rfl | rfl | rfl⟩ | ⟨hm, rfl | rfl | rfl⟩ |
      ⟨hm, rfl | rfl | rfl⟩ | ⟨hm, rfl | rfl | rfl⟩ | ⟨hm, rfl | rfl | rfl⟩ | ⟨hm, rfl | rfl | rfl⟩
    all_goals first
      | omega
      | (left; first | rfl | (congr 1; omega))
      | (right; left; first | rfl | (congr 1; omega))
      | (right; right; first | rfl | (congr 1; omega))

end Base

end Podc.LCLDefinitions
