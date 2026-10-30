import Mathlib
import Cslib.Computability.Distributed.Local.OnlineLocalLocality

/-!
# Binary labeling problems: definitions and Observation 3.2

Basic notions of *Classification of Distributed Binary Labeling Problems* (Balliu, Brandt, Efron,
Hirvonen, Maus, Olivetti, Suomela; PODC 2020 brief announcement, full version arXiv:1911.13294v3).

* `Problem`: a binary labeling problem `Π = (d, δ, W, B)` (§3.1).
* An instance is a graph `G` with a proper 2-colouring `f : V → Bool` (`true` = white).
* A candidate solution `X ⊆ E` is given as an edge labelling `x : V → V → Bool`: `x v w` is the
  label of the edge `{v, w}`; it has to be symmetric on edges (`IsSolution`).
* Model of computing (§5): deterministic LOCAL with unique identifiers. Nodes are the elements of
  the type `V` (the identifiers), so a `T`-round algorithm is a function of the radius-`T` view
  (`Cslib.Local.IsLocal`). A *white algorithm* `A G f u w` gives the label that the white node `u`
  writes on its edge to `w` (`whiteOut`); a *black algorithm* is the same with black nodes deciding
  (`blackOut`). `WhiteSolvable Π V T`: some `T`-round white algorithm solves `Π` on every tree on
  `V` with every proper 2-colouring.
* Observation 3.2 (combinatorial part: `isSolution_compl_iff`, `isSolution_swap_iff`; complexity
  part: `observation_3_2_compl`, `observation_3_2_swap`), Observations 3.4, 5.1, 5.2.
-/

namespace Podc.BinaryLabeling

open SimpleGraph Cslib.Local

variable {V : Type*}

/-- A binary labeling problem `Π = (d, δ, W, B)` (§3.1): white degree `d ≥ 2`, black degree
`δ ≥ 2`, white constraint `W ⊆ {0, …, d}`, black constraint `B ⊆ {0, …, δ}`. -/
structure Problem where
  /-- White degree. -/
  d : ℕ
  /-- Black degree. -/
  δ : ℕ
  /-- White constraint. -/
  W : Set ℕ
  /-- Black constraint. -/
  B : Set ℕ
  two_le_d : 2 ≤ d
  two_le_δ : 2 ≤ δ
  W_le : ∀ x ∈ W, x ≤ d
  B_le : ∀ x ∈ B, x ≤ δ

/-- `a − A = {a − x : x ∈ A}` (§3.2). -/
def rsub (a : ℕ) (A : Set ℕ) : Set ℕ := (fun x => a - x) '' A

lemma mem_rsub {a : ℕ} {A : Set ℕ} (hA : ∀ x ∈ A, x ≤ a) {y : ℕ} (hy : y ≤ a) :
    y ∈ rsub a A ↔ a - y ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := hA x hx
    rwa [Nat.sub_sub_self this]
  · intro h
    exact ⟨a - y, h, Nat.sub_sub_self hy⟩

lemma rsub_le {a : ℕ} {A : Set ℕ} : ∀ y ∈ rsub a A, y ≤ a := by
  rintro _ ⟨x, -, rfl⟩
  exact Nat.sub_le a x

namespace Problem

/-- Exchanging the roles of white and black: `Π₀₁ = (δ, d, B, W)`. -/
def swap (P : Problem) : Problem where
  d := P.δ
  δ := P.d
  W := P.B
  B := P.W
  two_le_d := P.two_le_δ
  two_le_δ := P.two_le_d
  W_le := P.B_le
  B_le := P.W_le

/-- Complementing the solution: `Π₁₀ = (d, δ, d − W, δ − B)`. -/
def compl (P : Problem) : Problem where
  d := P.d
  δ := P.δ
  W := rsub P.d P.W
  B := rsub P.δ P.B
  two_le_d := P.two_le_d
  two_le_δ := P.two_le_δ
  W_le := rsub_le
  B_le := rsub_le

/-- `Π' ⊆ Π`: `Π'` is a restriction of `Π` (Definition 3.3). -/
def IsRestriction (P' P : Problem) : Prop :=
  P'.d = P.d ∧ P'.δ = P.δ ∧ P'.W ⊆ P.W ∧ P'.B ⊆ P.B

@[simp] lemma swap_swap (P : Problem) : P.swap.swap = P := rfl

@[simp] lemma compl_d (P : Problem) : P.compl.d = P.d := rfl
@[simp] lemma compl_δ (P : Problem) : P.compl.δ = P.δ := rfl
@[simp] lemma compl_W (P : Problem) : P.compl.W = rsub P.d P.W := rfl
@[simp] lemma compl_B (P : Problem) : P.compl.B = rsub P.δ P.B := rfl
@[simp] lemma swap_d (P : Problem) : P.swap.d = P.δ := rfl
@[simp] lemma swap_δ (P : Problem) : P.swap.δ = P.d := rfl
@[simp] lemma swap_W (P : Problem) : P.swap.W = P.B := rfl
@[simp] lemma swap_B (P : Problem) : P.swap.B = P.W := rfl

end Problem

/-! ### Instances and solutions -/

/-- The degree of `v` in `G` (instance-free). -/
noncomputable def deg (G : SimpleGraph V) (v : V) : ℕ := (G.neighborSet v).ncard

/-- The `X`-degree of `v`: the number of edges at `v` labelled `true`. -/
noncomputable def degX (G : SimpleGraph V) (x : V → V → Bool) (v : V) : ℕ :=
  {w | G.Adj v w ∧ x v w = true}.ncard

/-- A proper 2-colouring (`true` = white, `false` = black). -/
def IsProper (G : SimpleGraph V) (f : V → Bool) : Prop := ∀ ⦃u v⦄, G.Adj u v → f u ≠ f v

/-- `x` is a solution of `Π` on `(G, f)` (§3.1): it is an edge labelling (symmetric on edges), white
nodes of degree `d` have `X`-degree in `W`, and black nodes of degree `δ` have `X`-degree in `B`. -/
def IsSolution (P : Problem) (G : SimpleGraph V) (f : V → Bool) (x : V → V → Bool) : Prop :=
  (∀ ⦃v w⦄, G.Adj v w → x v w = x w v) ∧
  (∀ v, f v = true → deg G v = P.d → degX G x v ∈ P.W) ∧
  (∀ v, f v = false → deg G v = P.δ → degX G x v ∈ P.B)

/-- The complementary labelling `E ∖ X`. -/
def complLabel (x : V → V → Bool) : V → V → Bool := fun v w => !x v w

lemma degX_compl [Finite V] (G : SimpleGraph V) (x : V → V → Bool) (v : V) :
    degX G (complLabel x) v = deg G v - degX G x v := by
  classical
  have hfin : (G.neighborSet v).Finite := (G.neighborSet v).toFinite
  have h1 : {w | G.Adj v w ∧ complLabel x v w = true} =
      G.neighborSet v \ {w | G.Adj v w ∧ x v w = true} := by
    ext w; simp only [complLabel, Set.mem_setOf_eq, Bool.not_eq_true', Set.mem_diff,
      mem_neighborSet, not_and, Bool.not_eq_true]
    constructor
    · rintro ⟨h, h'⟩; exact ⟨h, fun _ => h'⟩
    · rintro ⟨h, h'⟩; exact ⟨h, h' h⟩
  have h2 : {w | G.Adj v w ∧ x v w = true} ⊆ G.neighborSet v := fun w hw => hw.1
  rw [degX, h1, Set.ncard_sdiff h2, deg, degX]

lemma degX_le_deg [Finite V] (G : SimpleGraph V) (x : V → V → Bool) (v : V) :
    degX G x v ≤ deg G v :=
  Set.ncard_le_ncard (fun w hw => hw.1) (G.neighborSet v).toFinite

/-- Observation 3.2, complement part: `X` solves `Π` iff `E ∖ X` solves `Π₁₀`. -/
theorem isSolution_compl_iff [Finite V] (P : Problem) (G : SimpleGraph V)
    (f : V → Bool) (x : V → V → Bool) :
    IsSolution P.compl G f (complLabel x) ↔ IsSolution P G f x := by
  have key : ∀ (a : ℕ) (A : Set ℕ) (hA : ∀ y ∈ A, y ≤ a) v, deg G v = a →
      (degX G (complLabel x) v ∈ rsub a A ↔ degX G x v ∈ A) := by
    intro a A hA v hv
    rw [degX_compl, hv, mem_rsub hA (Nat.sub_le _ _),
      Nat.sub_sub_self (hv ▸ degX_le_deg G x v)]
  refine ⟨fun ⟨hs, hw, hb⟩ => ⟨?_, ?_, ?_⟩, fun ⟨hs, hw, hb⟩ => ⟨?_, ?_, ?_⟩⟩
  · intro v w h; simpa [complLabel] using hs h
  · intro v hv hd; exact (key _ _ P.W_le v hd).1 (hw v hv hd)
  · intro v hv hd; exact (key _ _ P.B_le v hd).1 (hb v hv hd)
  · intro v w h; simp [complLabel, hs h]
  · intro v hv hd; exact (key _ _ P.W_le v hd).2 (hw v hv hd)
  · intro v hv hd; exact (key _ _ P.B_le v hd).2 (hb v hv hd)

/-- Observation 3.2, colour-swap part: `X` solves `Π` on `(G, f)` iff it solves `Π₀₁` on
`(G, ¬f)`. -/
theorem isSolution_swap_iff (P : Problem) (G : SimpleGraph V) (f : V → Bool)
    (x : V → V → Bool) :
    IsSolution P.swap G (fun v => !f v) x ↔ IsSolution P G f x := by
  simp only [IsSolution, Problem.swap, Bool.not_eq_true', Bool.not_eq_false']
  tauto

/-- Observation 3.4: a solution of a restriction is a solution of the relaxation. -/
theorem IsSolution.of_restriction {P P' : Problem} (h : P'.IsRestriction P) {G : SimpleGraph V}
    {f : V → Bool} {x : V → V → Bool} (hx : IsSolution P' G f x) : IsSolution P G f x := by
  obtain ⟨hd, hδ, hW, hB⟩ := h
  refine ⟨hx.1, fun v hv hdv => hW (hx.2.1 v hv (hd ▸ hdv)),
    fun v hv hdv => hB (hx.2.2 v hv (hδ ▸ hdv))⟩

/-! ### White and black algorithms in the LOCAL model -/

/-- An algorithm: `A G f u w` is the label that `u` writes on its edge to `w`. Since nodes are
the elements of `V` (the identifiers), the algorithm may use identifiers. -/
abbrev Algorithm (V : Type*) := SimpleGraph V → (V → Bool) → V → V → Bool

/-- The labelling produced by a *white* algorithm: every edge gets the label written by its
white endpoint. -/
def whiteOut (A : Algorithm V) (G : SimpleGraph V) (f : V → Bool) : V → V → Bool :=
  fun v w => if f v then A G f v w else A G f w v

/-- The labelling produced by a *black* algorithm. -/
def blackOut (A : Algorithm V) (G : SimpleGraph V) (f : V → Bool) : V → V → Bool :=
  fun v w => if f v then A G f w v else A G f v w

/-- Trees on `V` with a proper 2-colouring: the instances of §3.6. -/
def IsInstance (G : SimpleGraph V) (f : V → Bool) : Prop := G.IsTree ∧ IsProper G f

/-- `Π` can be solved by a `T`-round white algorithm on all trees on `V` (§5; `|V| = n`). -/
def WhiteSolvable (P : Problem) (V : Type*) (T : ℕ) : Prop :=
  ∃ A : Algorithm V, IsLocal T A ∧
    ∀ G f, IsInstance G f → IsSolution P G f (whiteOut A G f)

/-- `Π` can be solved by a `T`-round black algorithm on all trees on `V`. -/
def BlackSolvable (P : Problem) (V : Type*) (T : ℕ) : Prop :=
  ∃ A : Algorithm V, IsLocal T A ∧
    ∀ G f, IsInstance G f → IsSolution P G f (blackOut A G f)

lemma IsInstance.swap {G : SimpleGraph V} {f : V → Bool} (h : IsInstance G f) :
    IsInstance G (fun v => !f v) :=
  ⟨h.1, fun u v huv => by simpa using h.2 huv⟩

/-- Observation 5.1: a black algorithm for `Π` is a white algorithm for `Π₀₁` (run on the swapped
colouring), and conversely. -/
theorem observation_5_1 (P : Problem) (T : ℕ) :
    BlackSolvable P V T ↔ WhiteSolvable P.swap V T := by
  constructor
  · rintro ⟨A, hA, hs⟩
    refine ⟨fun G f => A G (fun v => !f v), ?_, fun G f hGf => ?_⟩
    · intro G f G' f' v hv
      exact hA _ _ _ _ _ ⟨hv.1, fun u hu => by simp [hv.2 u hu]⟩
    · have := hs G (fun v => !f v) hGf.swap
      rw [← isSolution_swap_iff] at this
      have hf : (fun v => !!f v) = f := by funext v; simp
      simp only [Bool.not_not] at this
      convert this using 2
      funext v w
      cases h : f v <;> simp [h, whiteOut, blackOut]
  · rintro ⟨A, hA, hs⟩
    refine ⟨fun G f => A G (fun v => !f v), ?_, fun G f hGf => ?_⟩
    · intro G f G' f' v hv
      exact hA _ _ _ _ _ ⟨hv.1, fun u hu => by simp [hv.2 u hu]⟩
    · have := hs G (fun v => !f v) hGf.swap
      rw [isSolution_swap_iff] at this
      convert this using 2
      funext v w
      cases h : f v <;> simp [h, whiteOut, blackOut]

/-- Shifting an algorithm to the neighbours: `u` writes on the edge to `w` what `w` would write
on the edge to `u`. If `A` is `T`-local, this is `(T + 1)`-local. -/
noncomputable def neighbourShift (A : Algorithm V) : Algorithm V :=
  fun G f u w => open scoped Classical in if G.Adj u w then A G f w u else false

lemma isLocal_neighbourShift {A : Algorithm V} {T : ℕ} (hA : IsLocal T A) :
    IsLocal (T + 1) (neighbourShift A) := by
  classical
  intro G f G' f' u hv
  funext w
  have hadj : G.Adj u w ↔ G'.Adj u w := hv.1.adj_iff (Nat.succ_pos _) w
  simp only [neighbourShift]
  by_cases h : G.Adj u w
  · simp only [h, hadj.1 h, ↓reduceIte]
    have hw : G.edist u w ≤ 1 := by rw [edist_eq_one_iff_adj.2 h]
    have hT : ViewEq T G f G' f' w := by
      refine ⟨hv.1.mono hw (by omega), fun z hz => hv.2 z ?_⟩
      calc G.edist u z ≤ G.edist u w + G.edist w z := G.edist_triangle
        _ ≤ 1 + T := add_le_add hw hz
        _ = ((T + 1 : ℕ) : ℕ∞) := by push_cast; ring
    rw [hA _ _ _ _ _ hT]
  · have h' : ¬ G'.Adj u w := fun h' => h (hadj.2 h')
    simp only [h, h', ↓reduceIte]

/-- Observation 5.2 (one direction): a `T`-round white algorithm gives a `(T + 1)`-round black
algorithm (white nodes tell their black neighbours their output). -/
theorem white_to_black {P : Problem} {T : ℕ} (h : WhiteSolvable P V T) :
    BlackSolvable P V (T + 1) := by
  classical
  obtain ⟨A, hA, hs⟩ := h
  refine ⟨neighbourShift A, isLocal_neighbourShift hA, fun G f hGf => ?_⟩
  have hsol := hs G f hGf
  -- the two labellings agree on edges
  have heq : ∀ v w, G.Adj v w → blackOut (neighbourShift A) G f v w = whiteOut A G f v w := by
    intro v w hvw
    have hne := hGf.2 hvw
    simp only [blackOut, whiteOut, neighbourShift, hvw, hvw.symm, ↓reduceIte]
  have hdeg : ∀ v, degX G (blackOut (neighbourShift A) G f) v = degX G (whiteOut A G f) v := by
    intro v
    unfold degX
    congr 1
    ext w
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (heq v w h1) ▸ h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (heq v w h1).symm ▸ h2⟩
  refine ⟨fun v w hvw => ?_, fun v hv hd => ?_, fun v hv hd => ?_⟩
  · rw [heq v w hvw, heq w v hvw.symm]; exact hsol.1 hvw
  · rw [hdeg]; exact hsol.2.1 v hv hd
  · rw [hdeg]; exact hsol.2.2 v hv hd

/-- Observation 5.2 (other direction): a `T`-round black algorithm gives a `(T + 1)`-round white
algorithm. -/
theorem black_to_white {P : Problem} {T : ℕ} (h : BlackSolvable P V T) :
    WhiteSolvable P V (T + 1) := by
  rw [observation_5_1] at h
  have := white_to_black h
  rw [observation_5_1] at this
  simpa using this

/-- Observation 3.2, complement part, for complexities: `Π` and `Π₁₀` have the same white
complexity. -/
theorem observation_3_2_compl [Finite V] {P : Problem} {T : ℕ} (h : WhiteSolvable P V T) :
    WhiteSolvable P.compl V T := by
  obtain ⟨A, hA, hs⟩ := h
  refine ⟨fun G f u w => !A G f u w, fun G f G' f' v hv => ?_, fun G f hGf => ?_⟩
  · simp only [hA _ _ _ _ _ hv]
  · have := (isSolution_compl_iff P G f (whiteOut A G f)).2 (hs G f hGf)
    convert this using 2
    funext v w
    simp only [whiteOut, complLabel]
    split_ifs <;> rfl

/-- Observation 3.2, swap part, for complexities: a `T`-round white algorithm for `Π` gives a
`(T + 1)`-round white algorithm for `Π₀₁` (via a black algorithm for `Π`). -/
theorem observation_3_2_swap {P : Problem} {T : ℕ} (h : WhiteSolvable P V T) :
    WhiteSolvable P.swap V (T + 1) :=
  (observation_5_1 P (T + 1)).1 (white_to_black h)

end Podc.BinaryLabeling
