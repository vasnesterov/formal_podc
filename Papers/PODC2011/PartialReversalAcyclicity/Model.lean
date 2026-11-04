import Mathlib

/-!
# Partial Reversal Acyclicity — the model

Radeva, Lynch. *Partial Reversal Acyclicity.* PODC 2011 (brief announcement); full version
MIT-CSAIL-TR-2011-022.

Section 2 of the paper: an undirected graph `G = (V, E)` with a destination `D`, and an initial
acyclic orientation `G'init`. We take `G'init` as the primitive datum (`Network.init u v` means
"initially the edge `{u,v}` is directed from `u` to `v`", i.e. `u` is to the left of `v`) and
define `G` as its underlying undirected graph. `in-nbrsᵤ`, `out-nbrsᵤ` and `nbrsᵤ` are defined
from it.

The three automata of the paper:

* `PR` (Algorithm 1): action `reverse(S)` for a nonempty set `S` of sinks with `D ∉ S`; state:
  the direction variables `dir[u,v]` and the lists `list[u]`;
* `OneStepPR` (Algorithm 3): the same with `S = {u}`;
* `NewPR` (Algorithm 2): action `reverse(u)`; state: `dir[u,v]` and the step counters `count[u]`.

The effect of `reverse(S)` is given in closed form (`PR.effect`): every node of `S` reverses the
edges in `PR.revSet` (its edges not in `list[u]`, or all edges if `list[u] = nbrsᵤ`), adds
itself to the lists of the corresponding neighbours, and empties its own list. The paper writes
it as a `for each u ∈ S` loop; the two agree whenever the nodes of `S` are pairwise
non-adjacent, which holds in every reachable state (two neighbours are never both sinks,
Invariant 3.1).

The directed graph `s.G'` of a state is `arcs N s.dir`: there is an arc `u → v` iff `{u,v} ∈ E`
and `dir[u,v] = out`.
-/

noncomputable section
open Classical

namespace Podc.PartialReversalAcyclicity

/-- The value of a direction variable `dir[u,v]`: the edge `{u,v}` is incoming (`inc`, the
paper's `in`) or outgoing (`out`) from the point of view of `u`. -/
inductive Dir
  | inc
  | out
  deriving DecidableEq

/-- The fixed data of the paper's Section 2: the initial directed graph `G'init`, which is a DAG,
and the destination `D`. `init u v` means that initially the edge `{u,v}` is directed from `u`
to `v` (`u` is "to the left of" `v`, `v ∈ out-nbrsᵤ`, `u ∈ in-nbrsᵥ`). -/
structure Network (V : Type*) where
  /-- The arcs of the initial directed graph `G'init`. -/
  init : V → V → Prop
  /-- `G'init` is a DAG. -/
  acyclic : ∀ u, ¬ Relation.TransGen init u u
  /-- The destination node `D`; it never takes a step. -/
  dest : V

variable {V : Type*} (N : Network V)

namespace Network

/-- `{u, v} ∈ E`: the undirected graph `G` underlying `G'init`. -/
def Adj (u v : V) : Prop := N.init u v ∨ N.init v u

/-- `nbrsᵤ`. -/
def nbrs (u : V) : Set V := {v | N.Adj u v}

/-- `in-nbrsᵤ`: the nodes with an incoming edge to `u` in `G'init` (to the left of `u`). -/
def inNbrs (u : V) : Set V := {v | N.init v u}

/-- `out-nbrsᵤ`: the nodes with an edge from `u` in `G'init` (to the right of `u`). -/
def outNbrs (u : V) : Set V := {v | N.init u v}

/-- The initial value of `dir[u,v]`: `in` if `v ∈ in-nbrsᵤ`, otherwise `out`. -/
def initDir (u v : V) : Dir := if N.init v u then .inc else .out

variable {N}

theorem init_irrefl (u : V) : ¬ N.init u u := fun h => N.acyclic u (.single h)

theorem init_asymm {u v : V} (h : N.init u v) : ¬ N.init v u := fun h' =>
  N.acyclic u (.tail (.single h) h')

theorem adj_comm {u v : V} : N.Adj u v ↔ N.Adj v u := Or.comm

theorem adj_irrefl (u : V) : ¬ N.Adj u u := by
  rintro (h | h) <;> exact init_irrefl u h

theorem ne_of_adj {u v : V} (h : N.Adj u v) : u ≠ v := by
  rintro rfl; exact adj_irrefl u h

@[simp] theorem mem_nbrs {u v : V} : v ∈ N.nbrs u ↔ N.Adj u v := Iff.rfl
@[simp] theorem mem_inNbrs {u v : V} : v ∈ N.inNbrs u ↔ N.init v u := Iff.rfl
@[simp] theorem mem_outNbrs {u v : V} : v ∈ N.outNbrs u ↔ N.init u v := Iff.rfl

theorem nbrs_eq_union (u : V) : N.nbrs u = N.inNbrs u ∪ N.outNbrs u := by
  ext v; simp [Adj, or_comm]

theorem inNbrs_subset_nbrs (u : V) : N.inNbrs u ⊆ N.nbrs u := fun _ h => Or.inr h
theorem outNbrs_subset_nbrs (u : V) : N.outNbrs u ⊆ N.nbrs u := fun _ h => Or.inl h

theorem not_mem_outNbrs_of_mem_inNbrs {u v : V} (h : v ∈ N.inNbrs u) : v ∉ N.outNbrs u :=
  init_asymm h

theorem not_mem_inNbrs_of_mem_outNbrs {u v : V} (h : v ∈ N.outNbrs u) : v ∉ N.inNbrs u :=
  init_asymm h

theorem nbrs_diff_outNbrs (u : V) : N.nbrs u \ N.outNbrs u = N.inNbrs u := by
  ext v; simp only [Set.mem_sdiff, mem_nbrs, mem_outNbrs, mem_inNbrs, Adj]
  constructor
  · rintro ⟨h | h, h'⟩
    · exact absurd h h'
    · exact h
  · intro h; exact ⟨Or.inr h, init_asymm h⟩

theorem nbrs_diff_inNbrs (u : V) : N.nbrs u \ N.inNbrs u = N.outNbrs u := by
  ext v; simp only [Set.mem_sdiff, mem_nbrs, mem_outNbrs, mem_inNbrs, Adj]
  constructor
  · rintro ⟨h | h, h'⟩
    · exact h
    · exact absurd h h'
  · intro h; exact ⟨Or.inl h, init_asymm h⟩

@[simp] theorem initDir_eq_inc {u v : V} : N.initDir u v = .inc ↔ N.init v u := by
  unfold initDir; split_ifs with h <;> simp [h]

@[simp] theorem initDir_eq_out {u v : V} : N.initDir u v = .out ↔ ¬ N.init v u := by
  unfold initDir; split_ifs with h <;> simp [h]

end Network

/-- The directed graph `G'` determined by direction variables: an arc `u → v` iff
`{u,v} ∈ E` and `dir[u,v] = out`. -/
def arcs (dir : V → V → Dir) (u v : V) : Prop := N.Adj u v ∧ dir u v = .out

/-- A directed graph (as a relation) is acyclic: no node reaches itself by a nonempty path. -/
def IsAcyclic (r : V → V → Prop) : Prop := ∀ u, ¬ Relation.TransGen r u u

/-- `u` is a sink w.r.t. the direction variables `dir`: `dir[u,v] = in` for all `v ∈ nbrsᵤ`. -/
def IsSink (dir : V → V → Dir) (u : V) : Prop := ∀ v ∈ N.nbrs u, dir u v = .inc

/-- Invariant 3.1 (and its analogue for `NewPR`): `dir[u,v] = in ↔ dir[v,u] = out` for every
edge `{u,v}`. -/
def DirConsistent (dir : V → V → Dir) : Prop :=
  ∀ u v, N.Adj u v → (dir u v = .inc ↔ dir v u = .out)

/-- `w` reverses the edges to the nodes of `X`: `dir[w,v] := out`, `dir[v,w] := in` for
`v ∈ X`. -/
def flipAt (dir : V → V → Dir) (w : V) (X : Set V) : V → V → Dir :=
  fun x y => if x = w ∧ y ∈ X then .out else if y = w ∧ x ∈ X then .inc else dir x y

/-! ### `PR` (Algorithm 1) and `OneStepPR` (Algorithm 3) -/

/-- A state of `PR` / `OneStepPR`: direction variables and lists. -/
@[ext] structure PRState (V : Type*) where
  /-- `dir[u,v]`. -/
  dir : V → V → Dir
  /-- `list[u]`. -/
  list : V → Set V

namespace PR

/-- The unique initial state of `PR` (and of `OneStepPR`). -/
def init : PRState V := ⟨N.initDir, fun _ => ∅⟩

/-- The set of neighbours whose edges `u` reverses in a step of `PR`: `nbrsᵤ \ list[u]` if
`list[u] ≠ nbrsᵤ`, else `nbrsᵤ`. -/
def revSet (s : PRState V) (u : V) : Set V :=
  if s.list u ≠ N.nbrs u then N.nbrs u \ s.list u else N.nbrs u

/-- The effect of `reverse(S)` (closed form of the paper's loop). -/
def effect (S : Set V) (s : PRState V) : PRState V :=
  { dir := fun x y =>
      if x ∈ S ∧ y ∈ revSet N s x then .out
      else if y ∈ S ∧ x ∈ revSet N s y then .inc else s.dir x y
    list := fun x => if x ∈ S then ∅ else s.list x ∪ {y | y ∈ S ∧ x ∈ revSet N s y} }

/-- A step `reverse(S)` of `PR`: `S ≠ ∅`, `D ∉ S`, every node of `S` is a sink. -/
def Step (s s' : PRState V) : Prop :=
  ∃ S : Set V, S.Nonempty ∧ N.dest ∉ S ∧ (∀ u ∈ S, IsSink N s.dir u) ∧ s' = effect N S s

/-- Reachable states of `PR`. -/
def Reachable (s : PRState V) : Prop := Relation.ReflTransGen (Step N) (init N) s

end PR

namespace OneStepPR

/-- A step `reverse(u)` of `OneStepPR` (Algorithm 3): `u ≠ D` is a sink; the effect is that of
`reverse({u})` in `PR`. -/
def Step (s s' : PRState V) : Prop :=
  ∃ u, u ≠ N.dest ∧ IsSink N s.dir u ∧ s' = PR.effect N {u} s

/-- Reachable states of `OneStepPR` (same initial state as `PR`). -/
def Reachable (s : PRState V) : Prop := Relation.ReflTransGen (Step N) (PR.init N) s

end OneStepPR

/-! ### `NewPR` (Algorithm 2) -/

/-- A state of `NewPR`: direction variables and step counters (`parity[u]` is derived). -/
@[ext] structure NewPRState (V : Type*) where
  /-- `dir[u,v]`. -/
  dir : V → V → Dir
  /-- `count[u]`: the number of steps taken by `u`. -/
  count : V → ℕ

namespace NewPR

/-- The unique initial state of `NewPR`. -/
def init : NewPRState V := ⟨N.initDir, fun _ => 0⟩

/-- The set reversed by `u`: `in-nbrsᵤ` if `parity[u] = even`, `out-nbrsᵤ` if odd. -/
def revSet (t : NewPRState V) (u : V) : Set V :=
  if Even (t.count u) then N.inNbrs u else N.outNbrs u

/-- The effect of `reverse(u)`. -/
def effect (u : V) (t : NewPRState V) : NewPRState V :=
  ⟨flipAt t.dir u (revSet N t u), Function.update t.count u (t.count u + 1)⟩

/-- A step `reverse(u)` of `NewPR`: `u ≠ D` is a sink. -/
def Step (t t' : NewPRState V) : Prop :=
  ∃ u, u ≠ N.dest ∧ IsSink N t.dir u ∧ t' = effect N u t

/-- Reachable states of `NewPR`. -/
def Reachable (t : NewPRState V) : Prop := Relation.ReflTransGen (Step N) (init N) t

end NewPR

/-! ### Basic lemmas -/

variable {N}

theorem Dir.eq_out_of_ne_inc {d : Dir} (h : d ≠ .inc) : d = .out := by cases d <;> simp_all
theorem Dir.eq_inc_of_ne_out {d : Dir} (h : d ≠ .out) : d = .inc := by cases d <;> simp_all
@[simp] theorem Dir.ne_inc_iff {d : Dir} : d ≠ .inc ↔ d = .out := by cases d <;> simp
@[simp] theorem Dir.ne_out_iff {d : Dir} : d ≠ .out ↔ d = .inc := by cases d <;> simp

theorem DirConsistent.out_iff {dir : V → V → Dir} (h : DirConsistent N dir) {u v : V}
    (huv : N.Adj u v) : dir u v = .out ↔ dir v u = .inc := by
  have := h u v huv
  cases hu : dir u v <;> cases hv : dir v u <;> simp_all

theorem DirConsistent.not_both_sinks {dir : V → V → Dir} (h : DirConsistent N dir) {u v : V}
    (huv : N.Adj u v) (hu : IsSink N dir u) : ¬ IsSink N dir v := fun hv => by
  have h1 := hu v huv
  have h2 := hv u (Network.adj_comm.mp huv)
  have := (h u v huv).mp h1
  simp_all

theorem initDir_consistent : DirConsistent N N.initDir := by
  intro u v huv
  rcases huv with h | h
  · simp [h, Network.init_asymm h]
  · simp [h, Network.init_asymm h]

theorem PR.revSet_subset (s : PRState V) (u : V) : PR.revSet N s u ⊆ N.nbrs u := by
  unfold PR.revSet; split_ifs
  · exact Set.sdiff_subset
  · exact le_rfl

theorem NewPR.revSet_subset (t : NewPRState V) (u : V) : NewPR.revSet N t u ⊆ N.nbrs u := by
  unfold NewPR.revSet; split_ifs
  · exact Network.inNbrs_subset_nbrs u
  · exact Network.outNbrs_subset_nbrs u

@[simp] theorem flipAt_empty (dir : V → V → Dir) (w : V) : flipAt dir w ∅ = dir := by
  funext x y; simp [flipAt]

theorem flipAt_apply (dir : V → V → Dir) (w : V) (X : Set V) (x y : V) :
    flipAt dir w X x y =
      if x = w ∧ y ∈ X then .out else if y = w ∧ x ∈ X then .inc else dir x y := rfl

theorem PR.effect_singleton_dir (u : V) (s : PRState V) :
    (PR.effect N {u} s).dir = flipAt s.dir u (PR.revSet N s u) := by
  funext x y
  rw [flipAt_apply]; simp only [PR.effect, Set.mem_singleton_iff]
  by_cases hx : x = u <;> by_cases hy : y = u <;> subst_vars <;> simp_all

/-- Direction variables that induce the same `G'` agree on all edges. -/
theorem dir_eq_of_arcs_eq {d₁ d₂ : V → V → Dir} (h : arcs N d₁ = arcs N d₂) {x y : V}
    (hxy : N.Adj x y) : d₁ x y = d₂ x y := by
  have := congrFun (congrFun h x) y
  simp only [arcs, eq_iff_iff] at this
  cases h1 : d₁ x y <;> cases h2 : d₂ x y <;> simp_all

theorem arcs_eq_of_dir_eq {d₁ d₂ : V → V → Dir} (h : ∀ x y, N.Adj x y → d₁ x y = d₂ x y) :
    arcs N d₁ = arcs N d₂ := by
  funext x y; simp only [arcs, eq_iff_iff]
  constructor
  · rintro ⟨hxy, h1⟩; exact ⟨hxy, (h x y hxy) ▸ h1⟩
  · rintro ⟨hxy, h1⟩; exact ⟨hxy, (h x y hxy).symm ▸ h1⟩

theorem arcs_flipAt_congr {d₁ d₂ : V → V → Dir} (h : arcs N d₁ = arcs N d₂) (w : V)
    (X : Set V) : arcs N (flipAt d₁ w X) = arcs N (flipAt d₂ w X) := by
  apply arcs_eq_of_dir_eq
  intro x y hxy
  rw [flipAt_apply, flipAt_apply, dir_eq_of_arcs_eq h hxy]

theorem flipAt_flipAt_empty (dir : V → V → Dir) (w : V) (X : Set V) :
    flipAt (flipAt dir w ∅) w X = flipAt dir w X := by simp

theorem isSink_congr {d₁ d₂ : V → V → Dir} (h : arcs N d₁ = arcs N d₂) {u : V} :
    IsSink N d₁ u ↔ IsSink N d₂ u := by
  unfold IsSink
  constructor
  · intro hs v hv; rw [← dir_eq_of_arcs_eq h hv]; exact hs v hv
  · intro hs v hv; rw [dir_eq_of_arcs_eq h hv]; exact hs v hv

end Podc.PartialReversalAcyclicity

end
