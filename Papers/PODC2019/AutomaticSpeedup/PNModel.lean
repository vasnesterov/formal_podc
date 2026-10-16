import Papers.PODC2019.AutomaticSpeedup.Abstract
import Cslib.Computability.Distributed.PortNumbering.Basic

/-!
# The port-numbering model with input labels (Brandt, PODC 2019, §3)

* `LGraph I n`: a port-numbered graph on `n` nodes (CSLib's `PNGraph (Fin n)`) with an input label
  in `I` at every port, i.e. at every pair `(v, e) ∈ B(G)` (the paper's `Σ`-input-labelled graphs).
* `ViewT I t`, `LGraph.view`: the radius-`t` neighbourhood `N^t(v)`, defined as the information a
  node can gather in `t` rounds of the port-numbering model (its full-information state): own input
  labels, and for each port the neighbour's radius-`(t-1)` view together with the port number at
  the neighbour.
* `LGraph.eview`: the radius-`t` view `N^t(e)` of the edge behind port `i` of `v`, seen from `v`:
  the radius-`(t-1)` views of both endpoints and the port numbers of `e` at both endpoints. This is
  the information both endpoints have after `t` rounds.
* `SolvableIn 𝒢 P Δ t`: some deterministic CSLib port-numbering algorithm solves `P` on every graph
  of the class `𝒢` within `t` rounds.
* `IsIndependent 𝒢 t`: `t`-independence (§3), literally: clauses 1 and 2 with views as above.

`solvableIn_iff_view`: a problem is solvable in `t` rounds iff some function of radius-`t` views
solves it. This is the standard fact used in §3 ("a `T`-round algorithm can be equivalently
described as a function that maps each possible radius-`T` neighbourhood to outputs").
-/

-- CSLib candidate (full-information views of port-numbered graphs, `solvableIn_iff_view`)
namespace AutomaticSpeedup

open Cslib.PortNumbering Problem

/-- A port-numbered graph on `n` nodes with an input label from `I` at every port. -/
structure LGraph (I : Type) (n : ℕ) where
  /-- The underlying port-numbered graph. -/
  G : PNGraph (Fin n)
  /-- `inp v i`: the input label of `(v, e)`, where `e` is the edge behind port `i` of `v`. -/
  inp : Fin n → ℕ → I

/-- Radius-`t` views (full-information states). A radius-0 view is the list of the node's input
labels (one per port, so its length is the degree). A radius-`(t+1)` view additionally lists, for
every port, the neighbour's radius-`t` view and the port number at the neighbour. -/
def ViewT (I : Type) : ℕ → Type
  | 0 => List I
  | t + 1 => List I × List (ViewT I t × ℕ)

instance (I : Type) : (t : ℕ) → Inhabited (ViewT I t)
  | 0 => ⟨([] : List I)⟩
  | _ + 1 => ⟨(([] : List I), [])⟩

namespace ViewT

variable {I : Type}

/-- The node's own input labels. -/
def inputs : {t : ℕ} → ViewT I t → List I
  | 0, w => w
  | _ + 1, w => w.1

/-- The degree of the centre. -/
def deg {t : ℕ} (w : ViewT I t) : ℕ := w.inputs.length

/-- Forget the outermost layer: radius `t + 1` to radius `t`. -/
def restrict : {t : ℕ} → ViewT I (t + 1) → ViewT I t
  | 0, w => w.1
  | _ + 1, w => (w.1, w.2.map fun c => (restrict c.1, c.2))

/-- The `i`-th child of a view (neighbour's view and the port number at the neighbour). -/
def child {t : ℕ} (w : ViewT I (t + 1)) (i : ℕ) : ViewT I t × ℕ := w.2.getD i default

end ViewT

namespace LGraph

variable {I : Type} {n : ℕ} (G : LGraph I n)

/-- Degree. -/
abbrev deg (v : Fin n) : ℕ := G.G.deg v
/-- The neighbour behind port `i` of `v`. -/
abbrev nbr (v : Fin n) (i : ℕ) : Fin n := G.G.nbr v i
/-- The port number at the other end of port `i` of `v`. -/
abbrev rport (v : Fin n) (i : ℕ) : ℕ := G.G.rport v i

/-- The local input of `v` as seen by a port-numbering algorithm: its input labels, one per port. -/
def inputs (v : Fin n) : List I := (List.range (G.deg v)).map (G.inp v)

/-- The radius-`t` view `N^t(v)` of `v`. -/
def view : (t : ℕ) → Fin n → ViewT I t
  | 0, v => G.inputs v
  | t + 1, v => (G.inputs v, (List.range (G.deg v)).map fun i => (view t (G.nbr v i), G.rport v i))

/-- The radius-`(s+1)` view of the edge behind port `i` of `v`, seen from `v`. -/
def eview (s : ℕ) (v : Fin n) (i : ℕ) : ViewT I s × ℕ × ViewT I s × ℕ :=
  (G.view s v, i, G.view s (G.nbr v i), G.rport v i)

@[simp] theorem length_inputs (v : Fin n) : (G.inputs v).length = G.deg v := by simp [inputs]

@[simp] theorem inputs_view (t : ℕ) (v : Fin n) : (G.view t v).inputs = G.inputs v := by
  cases t <;> rfl

@[simp] theorem deg_view (t : ℕ) (v : Fin n) : (G.view t v).deg = G.deg v := by
  simp [ViewT.deg]

@[simp] theorem restrict_view (t : ℕ) (v : Fin n) : (G.view (t + 1) v).restrict = G.view t v := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    show (G.inputs v, ((List.range (G.deg v)).map _).map _) = (G.inputs v, _)
    simp only [List.map_map]
    congr 2
    funext i
    simp [ih]

theorem child_view (t : ℕ) (v : Fin n) {i : ℕ} (hi : i < G.deg v) :
    (G.view (t + 1) v).child i = (G.view t (G.nbr v i), G.rport v i) := by
  simp [ViewT.child, view, List.getD_eq_getElem?_getD, hi]

theorem getElem?_view (t : ℕ) (v : Fin n) {i : ℕ} (hi : i < G.deg v) :
    (G.view (t + 1) v).2[i]? = some (G.view t (G.nbr v i), G.rport v i) := by
  simp [view, hi]

end LGraph

/-! ### Correctness and solvability -/

variable {I : Type} {n : ℕ} {L : Type}

/-- `out` is a correct solution of `P` on `G` (for maximum degree `Δ`, §3): labels in `f Δ`, every
edge configuration (for each edge, from both sides) in `g Δ`, every node configuration in `h Δ`. -/
def Solves (P : Problem L) (Δ : ℕ) (G : LGraph I n) (out : Fin n → ℕ → L) : Prop :=
  (∀ v, ∀ i < G.deg v, out v i ∈ P.f Δ) ∧
  (∀ v, ∀ i < G.deg v, ({out v i, out (G.nbr v i) (G.rport v i)} : Multiset L) ∈ P.g Δ) ∧
  (∀ v, (Multiset.range (G.deg v)).map (out v) ∈ P.h Δ)

/-- Some deterministic port-numbering algorithm (CSLib `Algorithm`, local input = the node's input
labels, output = one label per port) solves `P` on every graph of `𝒢` in `t` rounds. The algorithm
may depend on `n`, `Δ` and `t` (they are fixed in the statement), as in the paper. -/
def SolvableIn (𝒢 : Set (LGraph I n)) (P : Problem L) (Δ t : ℕ) : Prop :=
  ∃ A : Algorithm (List I) (ℕ → L), ∀ G ∈ 𝒢, Solves P Δ G (A.eval G.G t G.inputs)

/-! ### Algorithms are functions of views -/

namespace ViewT

/-- The state of an algorithm after `t` rounds, computed from the radius-`t` view. -/
def stOf {O : Type} (A : Algorithm (List I) O) : (t : ℕ) → ViewT I t → A.State
  | 0, w => A.init w.length w
  | t + 1, w => A.recv (stOf A t w.restrict)
      (fun i => if i < w.1.length then (w.2[i]?).map fun c => A.send (stOf A t c.1) c.2 else none)

/-- Extract a radius-`r` view from a view of unknown radius. -/
def getV (r : ℕ) (c : (r' : ℕ) × ViewT I r') : ViewT I r :=
  if h : c.1 = r then h ▸ c.2 else default

@[simp] theorem getV_mk (r : ℕ) (w : ViewT I r) : getV r ⟨r, w⟩ = w := by simp [getV]

end ViewT

theorem state_eq_stOf {O : Type} (A : Algorithm (List I) O) (G : LGraph I n) (t : ℕ) (v : Fin n) :
    A.state G.G G.inputs t v = ViewT.stOf A t (G.view t v) := by
  induction t generalizing v with
  | zero => simp [ViewT.stOf, LGraph.view]
  | succ t ih =>
    rw [Algorithm.state_succ, ih]
    show _ = A.recv (ViewT.stOf A t (G.view (t + 1) v).restrict) _
    rw [LGraph.restrict_view]
    congr 1
    funext i
    simp only [Algorithm.inbox]
    show _ = if i < (G.inputs v).length then _ else _
    rw [LGraph.length_inputs]
    split_ifs with hi
    · rw [LGraph.getElem?_view _ _ _ hi, Option.map_some, ih]
    · rfl

/-- The full-information algorithm: after `t` rounds every node knows its radius-`t` view. -/
def fullInfo (I : Type) : Algorithm (List I) ((r : ℕ) × ViewT I r) where
  State := (r : ℕ) × ViewT I r
  Msg := ((r : ℕ) × ViewT I r) × ℕ
  init _ x := ⟨0, x⟩
  send s i := (s, i)
  recv s m := ⟨s.1 + 1, (s.2.inputs, (List.range s.2.inputs.length).map fun i =>
    match m i with
    | some (c, j) => (ViewT.getV s.1 c, j)
    | none => (default, 0))⟩
  out s := s

theorem fullInfo_state (G : LGraph I n) (t : ℕ) (v : Fin n) :
    (fullInfo I).state G.G G.inputs t v = ⟨t, G.view t v⟩ := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    rw [Algorithm.state_succ, ih]
    show (⟨t + 1, ((G.view t v).inputs, _)⟩ : (r : ℕ) × ViewT I r) = ⟨t + 1, (G.inputs v, _)⟩
    simp only [LGraph.inputs_view, LGraph.length_inputs]
    have e : ∀ i ∈ List.range (G.deg v),
        (match (fullInfo I).inbox G.G ((fullInfo I).state G.G G.inputs t) v i with
          | some (c, j) => (ViewT.getV t c, j)
          | none => ((default : ViewT I t), 0)) = (G.view t (G.nbr v i), G.rport v i) := by
      intro i hi
      rw [List.mem_range] at hi
      simp only [Algorithm.inbox, hi, ite_true, ih]
      show (ViewT.getV t ⟨t, _⟩, _) = _
      simp
    exact congrArg (fun l => (⟨t + 1, (G.inputs v, l)⟩ : (r : ℕ) × ViewT I r))
      (List.map_congr_left e)

/-- The algorithm that gathers the radius-`t` view and applies `F` to it. -/
def ofView {O : Type} (t : ℕ) (F : ViewT I t → O) : Algorithm (List I) O :=
  { fullInfo I with out := fun s => F (ViewT.getV t s) }

theorem eval_ofView {O : Type} (t : ℕ) (F : ViewT I t → O) (G : LGraph I n) (v : Fin n) :
    (ofView t F).eval G.G t G.inputs v = F (G.view t v) := by
  have : ∀ t', (ofView t F).state G.G G.inputs t' v = (fullInfo I).state G.G G.inputs t' v := by
    intro t'
    induction t' generalizing v with
    | zero => rfl
    | succ t' ih =>
      rw [Algorithm.state_succ, Algorithm.state_succ, ih]
      congr 1
      funext i
      simp only [Algorithm.inbox, ih]
      rfl
  show (ofView t F).out _ = _
  rw [this, fullInfo_state]
  simp [ofView]

/-- `t`-round algorithms are exactly functions of radius-`t` views. -/
theorem solvableIn_iff_view (𝒢 : Set (LGraph I n)) (P : Problem L) (Δ t : ℕ) :
    SolvableIn 𝒢 P Δ t ↔
      ∃ F : ViewT I t → ℕ → L, ∀ G ∈ 𝒢, Solves P Δ G fun v i => F (G.view t v) i := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨fun w => A.out (ViewT.stOf A t w), fun G hG => ?_⟩
    have e : A.eval G.G t G.inputs = fun v i => A.out (ViewT.stOf A t (G.view t v)) i := by
      funext v; simp [Algorithm.eval, state_eq_stOf]
    rw [← e]; exact hA G hG
  · rintro ⟨F, hF⟩
    refine ⟨ofView t F, fun G hG => ?_⟩
    have := hF G hG
    simpa only [funext (eval_ofView t F G)] using this

/-! ### Relaxations -/

/-- **Local post-processing** (0 extra rounds): if a node-local map `F` (from the node's input
labels and its outputs at all ports to new outputs at all ports) turns every solution of `P` on
graphs of `𝒢` into a solution of `Q`, then `Q` is solvable as fast as `P`. This is how relaxations
are used in the paper (e.g. Lemma 3). -/
theorem SolvableIn.post {L' : Type} {𝒢 : Set (LGraph I n)} {P : Problem L} {Q : Problem L'}
    {Δ t : ℕ} (F : List I → (ℕ → L) → ℕ → L')
    (hF : ∀ G ∈ 𝒢, ∀ out, Solves P Δ G out → Solves Q Δ G fun v => F (G.inputs v) (out v))
    (h : SolvableIn 𝒢 P Δ t) : SolvableIn 𝒢 Q Δ t := by
  rw [solvableIn_iff_view] at h ⊢
  obtain ⟨A, hA⟩ := h
  refine ⟨fun w => F w.inputs (A w), fun G hG => ?_⟩
  have := hF G hG _ (hA G hG)
  simpa only [LGraph.inputs_view] using this

/-- A label map `φ` sending allowed labels/edge/node configurations of `P` to allowed ones of `Q`
(so `Q` is a relaxation of `P`, "at most as hard"). -/
structure LabelHom {L' : Type} (P : Problem L) (Q : Problem L') (Δ : ℕ) where
  φ : L → L'
  map_f : ∀ x ∈ P.f Δ, φ x ∈ Q.f Δ
  map_g : ∀ m ∈ P.g Δ, m.map φ ∈ Q.g Δ
  map_h : ∀ m ∈ P.h Δ, m.map φ ∈ Q.h Δ

theorem SolvableIn.of_labelHom {L' : Type} {𝒢 : Set (LGraph I n)} {P : Problem L}
    {Q : Problem L'} {Δ t : ℕ} (φ : LabelHom P Q Δ) (h : SolvableIn 𝒢 P Δ t) :
    SolvableIn 𝒢 Q Δ t := by
  refine h.post (fun _ y i => φ.φ (y i)) fun G _ out hout => ⟨fun v i hi => φ.map_f _
    (hout.1 v i hi), fun v i hi => ?_, fun v => ?_⟩
  · have := φ.map_g _ (hout.2.1 v i hi); simpa using this
  · have := φ.map_h _ (hout.2.2 v); simpa [Multiset.map_map] using this

end AutomaticSpeedup
