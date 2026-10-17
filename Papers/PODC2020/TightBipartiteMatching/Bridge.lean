import Papers.PODC2020.TightBipartiteMatching.Views
import Cslib.Computability.Distributed.PortNumbering.Basic

/-!
# Views versus genuine port-numbering algorithms

We connect the view model of `Views.lean` (algorithms are functions of radius-`t` views) with
CSLib's message-passing algorithms in the port-numbering model (`Cslib.PortNumbering.Algorithm`),
with local input the colour (`true` = white = active) and output a label per port (`ℕ → L`).

* `viewOf G v t`: the radius-`t` (universal-cover) view of `v` in a `(d+1)`-regular `PNGraph`;
  `restrict_viewOf`, `port_viewOf`, `nbrView_viewOf` (re-rooting agrees with moving to a
  neighbour).
* `stOf A c t V`: the state of a node of colour `c` with view `V` after `t` rounds;
  `state_eq`: in every `(d+1)`-regular properly 2-coloured `PNGraph`, the state of `v` after `t`
  rounds is `stOf A (col v) t (viewOf G v t)`.
* `treeGraph d arr`: the infinite `(d+1)`-regular tree with port numbering determined by the
  "arrival port" function `arr`, with the 2-colouring `treeCol d c`; `viewOf_treeGraph_root`:
  every view is realized at the root of some such tree; `treeGraph_isSimple`.
* `solves_of_solvesOn_trees`: a CSLib algorithm that is correct on all these trees yields a
  view-based algorithm `f` with `Solves f Act Pas`.
-/

-- CSLib candidate (bipartite round elimination infrastructure)
namespace TightBipartiteMatching

open Cslib.PortNumbering

/-- A natural number as a port of a `(d+1)`-regular graph (reduced mod `d + 1`). -/
def finPort (d n : ℕ) : Fin (d + 1) := ⟨n % (d + 1), Nat.mod_lt _ d.succ_pos⟩

@[simp] theorem val_finPort_of_lt {d n : ℕ} (h : n < d + 1) : (finPort d n : ℕ) = n :=
  Nat.mod_eq_of_lt h

@[simp] theorem finPort_val {d : ℕ} (k : Fin (d + 1)) : finPort d k = k :=
  Fin.ext (Nat.mod_eq_of_lt k.2)

/-! ### Views in a port-numbered graph -/

section Views

variable {d : ℕ} {V : Type*} (G : PNGraph V)

/-- `brOf G s v k`: the depth-`s` branch behind port `k` of `v` in the universal cover of `G`.
Behind port `k` lies `w = G.nbr v k`, entered through its port `j = G.rport v k`; the sub-branches
are those behind the ports `j.succAbove c` of `w`. -/
def brOf : (s : ℕ) → V → ℕ → Br d s
  | 0, _, _ => ()
  | s + 1, v, k => Br.mk (finPort d (G.rport v k)) fun c =>
      brOf s (G.nbr v k) ((finPort d (G.rport v k)).succAbove c)

theorem brOf_succ (s : ℕ) (v : V) (k : ℕ) :
    brOf (d := d) G (s + 1) v k = Br.mk (finPort d (G.rport v k)) fun c =>
      brOf G s (G.nbr v k) ((finPort d (G.rport v k)).succAbove c) := rfl

/-- The radius-`t` view of `v` in the port-numbered graph `G` (the radius-`t` ball of the
universal cover, i.e. the information `v` can gather in `t` rounds). -/
def viewOf (v : V) (t : ℕ) : View d t := fun k => brOf G t v k

theorem viewOf_apply (v : V) (t : ℕ) (k : Fin (d + 1)) : viewOf G v t k = brOf G t v k := rfl

theorem restrict_brOf : ∀ (s : ℕ) (v : V) (k : ℕ),
    Br.restrict s (brOf (d := d) G (s + 1) v k) = brOf G s v k
  | 0, _, _ => Subsingleton.elim _ _
  | s + 1, v, k => by
    rw [brOf_succ, Br.restrict_mk, brOf_succ]
    congr 1
    funext c
    exact restrict_brOf s _ _

/-- Truncating the radius-`(t+1)` view gives the radius-`t` view. -/
@[simp] theorem restrict_viewOf (v : V) (t : ℕ) :
    View.restrict (viewOf (d := d) G v (t + 1)) = viewOf G v t := by
  funext k
  exact restrict_brOf G t v k

/-- The far port of the branch behind port `k` is `G.rport v k`. -/
theorem port_viewOf (hG : ∀ v, G.deg v = d + 1) (v : V) (t : ℕ) (k : Fin (d + 1)) :
    ((viewOf G v (t + 1) k).port : ℕ) = G.rport v k := by
  have hk : (k : ℕ) < G.deg v := by rw [hG]; exact k.2
  have := G.rport_lt hk
  rw [hG] at this
  exact val_finPort_of_lt this

/-- Re-rooting the view of `v` at port `k` gives the view of the neighbour behind port `k`. -/
theorem nbrView_viewOf (hG : ∀ v, G.deg v = d + 1) (v : V) :
    ∀ (t : ℕ) (k : Fin (d + 1)), nbrView t (viewOf G v (t + 1)) k = viewOf G (G.nbr v k) t
  | 0, _ => Subsingleton.elim _ _
  | t + 1, k => by
    have hk : (k : ℕ) < G.deg v := by rw [hG]; exact k.2
    have hj : ((finPort d (G.rport v k) : Fin (d + 1)) : ℕ) = G.rport v k := by
      have := G.rport_lt hk
      rw [hG] at this
      exact val_finPort_of_lt this
    funext p
    rcases eq_or_ne p (finPort d (G.rport v k)) with rfl | hp
    · have := nbrView_succ_apply_port (viewOf G v (t + 2)) k
      refine this.trans ?_
      rw [viewOf_apply, brOf_succ, hj, G.rport_rport hk, G.nbr_nbr hk, finPort_val]
      congr 1
      funext c
      rw [viewOf_apply, restrict_brOf, restrict_brOf]
    · obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hp
      exact nbrView_succ_apply_succAbove (viewOf G v (t + 2)) k c

end Views

/-! ### States of a message-passing algorithm as functions of views -/

section States

variable {d : ℕ} {O : Type}

/-- `stOf A c t V`: the state, after `t` rounds of `A`, of a node of colour `c` whose radius-`t`
view is `V`, in a `(d+1)`-regular properly 2-coloured graph (its neighbours have colour `!c`). -/
def stOf (A : Algorithm Bool O) : Bool → (t : ℕ) → View d t → A.State
  | c, 0, _ => A.init (d + 1) c
  | c, t + 1, V => A.recv (stOf A c t (View.restrict V)) fun i =>
      if h : i < d + 1 then
        some (A.send (stOf A (!c) t (nbrView t V ⟨i, h⟩)) (V ⟨i, h⟩).port)
      else none

variable {V : Type*} (A : Algorithm Bool O) {G : PNGraph V}

/-- In a `(d+1)`-regular properly 2-coloured port-numbered graph, the state of `v` after `t`
rounds is determined by its colour and its radius-`t` view. -/
theorem state_eq (hG : ∀ v, G.deg v = d + 1) (col : V → Bool)
    (hcol : ∀ v (i : ℕ), i < d + 1 → col (G.nbr v i) = !col v) :
    ∀ (t : ℕ) (v : V), A.state G col t v = stOf (d := d) A (col v) t (viewOf G v t)
  | 0, v => by rw [Algorithm.state_zero, hG]; rfl
  | t + 1, v => by
    rw [Algorithm.state_succ, stOf, restrict_viewOf, state_eq hG col hcol t v]
    congr 1
    funext i
    simp only [Algorithm.inbox, hG]
    split_ifs with h
    · rw [state_eq hG col hcol t, hcol v i h]
      have h1 := nbrView_viewOf G hG v t ⟨i, h⟩
      have h2 := port_viewOf G hG v t ⟨i, h⟩
      simp only at h1 h2
      rw [h1, h2]
    · rfl

/-- The output of `v` after `t` rounds, as a function of its colour and its view. -/
theorem eval_eq (hG : ∀ v, G.deg v = d + 1) (col : V → Bool)
    (hcol : ∀ v (i : ℕ), i < d + 1 → col (G.nbr v i) = !col v) (t : ℕ) (v : V) :
    A.eval G t col v = A.out (stOf (d := d) A (col v) t (viewOf G v t)) := by
  rw [Algorithm.eval, state_eq A hG col hcol]

end States

/-! ### Port-numbered infinite trees -/

section Trees

variable {d : ℕ}

/-- Vertices of the infinite `(d+1)`-regular tree: the root `none`, or `some (j, r)`: the vertex
reached from the root by leaving through root port `j` and then taking the child indices `r`
**in reverse order** (`r.head` is the last step). -/
abbrev TreeVtx (d : ℕ) := Option (Fin (d + 1) × List (Fin d))

/-- The neighbour across the parent edge of `some (j, r)` and the port by which it is reached,
given the arrival ports `arr`. -/
def treeParent (arr : Fin (d + 1) → List (Fin d) → Fin (d + 1)) (j : Fin (d + 1)) :
    List (Fin d) → TreeVtx d × Fin (d + 1)
  | [] => (none, j)
  | c :: r => (some (j, r), (arr j r).succAbove c)

/-- The connection map of the tree. The root's port `k` leads to `some (k, [])`. A vertex
`some (j, r)` reaches its parent through port `arr j r`, and its child `c` (namely
`some (j, c :: r)`) through port `(arr j r).succAbove c`. -/
def treeNbr (arr : Fin (d + 1) → List (Fin d) → Fin (d + 1)) :
    TreeVtx d → Fin (d + 1) → TreeVtx d × Fin (d + 1)
  | none, k => (some (k, []), arr k [])
  | some (j, r), k => Fin.insertNth (α := fun _ => TreeVtx d × Fin (d + 1)) (arr j r)
      (treeParent arr j r) (fun c => (some (j, c :: r), arr j (c :: r))) k

variable (arr : Fin (d + 1) → List (Fin d) → Fin (d + 1))

@[simp] theorem treeNbr_none (k : Fin (d + 1)) : treeNbr arr none k = (some (k, []), arr k []) :=
  rfl

@[simp] theorem treeNbr_some_self (j : Fin (d + 1)) (r : List (Fin d)) :
    treeNbr arr (some (j, r)) (arr j r) = treeParent arr j r := by
  simp [treeNbr]

@[simp] theorem treeNbr_some_succAbove (j : Fin (d + 1)) (r : List (Fin d)) (c : Fin d) :
    treeNbr arr (some (j, r)) ((arr j r).succAbove c) = (some (j, c :: r), arr j (c :: r)) := by
  simp [treeNbr]

theorem treeNbr_treeNbr (x : TreeVtx d) (k : Fin (d + 1)) :
    treeNbr arr (treeNbr arr x k).1 (treeNbr arr x k).2 = (x, k) := by
  rcases x with _ | ⟨j, r⟩
  · simp [treeParent]
  · rcases eq_or_ne k (arr j r) with rfl | hk
    · rw [treeNbr_some_self]
      cases r with
      | nil => simp [treeParent]
      | cons c r => simp [treeParent]
    · obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hk
      simp [treeParent]

/-- The infinite `(d+1)`-regular tree with the port numbering given by the arrival ports `arr`
(a CSLib `PNGraph`). Every port numbering of the infinite tree is of this form up to
isomorphism; the root's ports are numbered by the first step. -/
def treeGraph (d : ℕ) (arr : Fin (d + 1) → List (Fin d) → Fin (d + 1)) : PNGraph (TreeVtx d) where
  deg _ := d + 1
  p x i := if h : i < d + 1 then ((treeNbr arr x ⟨i, h⟩).1, ((treeNbr arr x ⟨i, h⟩).2 : ℕ))
    else (x, i)
  p_lt x i h := by
    simp only [h, dite_true]
    exact (treeNbr arr x ⟨i, h⟩).2.2
  p_p x i h := by
    simp only [h, dite_true, Fin.is_lt, Fin.eta]
    rw [treeNbr_treeNbr]

@[simp] theorem treeGraph_deg (x : TreeVtx d) : (treeGraph d arr).deg x = d + 1 := rfl

@[simp] theorem treeGraph_nbr (x : TreeVtx d) (k : Fin (d + 1)) :
    (treeGraph d arr).nbr x k = (treeNbr arr x k).1 := by
  simp only [PNGraph.nbr, treeGraph, k.2, dite_true, Fin.eta]

@[simp] theorem treeGraph_rport (x : TreeVtx d) (k : Fin (d + 1)) :
    (treeGraph d arr).rport x k = (treeNbr arr x k).2 := by
  simp only [PNGraph.rport, treeGraph, k.2, dite_true, Fin.eta]

/-- Auxiliary for `treeCol`: the colour of `some (j, r)` when the root has colour `c`. -/
def altCol {α : Type*} (c : Bool) : List α → Bool
  | [] => !c
  | _ :: r => !altCol c r

/-- The proper 2-colouring of the tree in which the root has colour `c`. -/
def treeCol (d : ℕ) (c : Bool) : TreeVtx d → Bool
  | none => c
  | some (_, r) => altCol c r

theorem treeCol_treeNbr (c : Bool) (x : TreeVtx d) (k : Fin (d + 1)) :
    treeCol d c (treeNbr arr x k).1 = !treeCol d c x := by
  rcases x with _ | ⟨j, r⟩
  · rfl
  · rcases eq_or_ne k (arr j r) with rfl | hk
    · rw [treeNbr_some_self]
      cases r with
      | nil => simp [treeParent, treeCol, altCol]
      | cons c r => simp [treeParent, treeCol, altCol]
    · obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hk
      simp [treeCol, altCol]

/-- `treeCol d c` is a proper 2-colouring of `treeGraph d arr`. -/
theorem treeCol_nbr (c : Bool) (x : TreeVtx d) (i : ℕ) (hi : i < d + 1) :
    treeCol d c ((treeGraph d arr).nbr x i) = !treeCol d c x := by
  have := treeGraph_nbr arr x ⟨i, hi⟩
  simp only at this
  rw [this, treeCol_treeNbr]

/-- The distance from the root. -/
def treeDepth : TreeVtx d → ℕ
  | none => 0
  | some (_, r) => r.length + 1

theorem treeDepth_treeNbr_self (j : Fin (d + 1)) (r : List (Fin d)) :
    treeDepth (treeNbr arr (some (j, r)) (arr j r)).1 = r.length := by
  rw [treeNbr_some_self]
  cases r <;> rfl

/-- The trees are simple graphs (no loops, no parallel edges). -/
theorem treeGraph_isSimple : (treeGraph d arr).IsSimple := by
  refine ⟨fun x i hi h => ?_, fun x i i' hi hi' h => ?_⟩
  · have e := treeGraph_nbr arr x ⟨i, hi⟩
    simp only at e
    rw [e] at h
    have h' := congrArg treeDepth h
    rcases x with _ | ⟨j, r⟩
    · simp [treeDepth] at h'
    · set k : Fin (d + 1) := ⟨i, hi⟩
      rcases eq_or_ne k (arr j r) with hk | hk
      · rw [hk, treeDepth_treeNbr_self] at h'
        simp [treeDepth] at h'
      · obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hk
        rw [← hc, treeNbr_some_succAbove] at h'
        simp [treeDepth] at h'
  · have e := treeGraph_nbr arr x ⟨i, hi⟩
    have e' := treeGraph_nbr arr x ⟨i', hi'⟩
    simp only at e e'
    rw [e, e'] at h
    suffices (⟨i, hi⟩ : Fin (d + 1)) = ⟨i', hi'⟩ from congrArg Fin.val this
    set k : Fin (d + 1) := ⟨i, hi⟩
    set k' : Fin (d + 1) := ⟨i', hi'⟩
    rcases x with _ | ⟨j, r⟩
    · simpa using h
    · have key : ∀ k k' : Fin (d + 1), k = arr j r → k' ≠ arr j r →
          (treeNbr arr (some (j, r)) k).1 ≠ (treeNbr arr (some (j, r)) k').1 := by
        intro k k' hk hk' h
        obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hk'
        subst hk
        have h' := congrArg treeDepth h
        rw [treeDepth_treeNbr_self, treeNbr_some_succAbove] at h'
        simp [treeDepth] at h'
        omega
      rcases eq_or_ne k (arr j r) with hk | hk <;> rcases eq_or_ne k' (arr j r) with hk' | hk'
      · rw [hk, hk']
      · exact absurd h (key _ _ hk hk')
      · exact absurd h.symm (key _ _ hk' hk)
      · obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hk
        obtain ⟨c', hc'⟩ := Fin.exists_succAbove_eq hk'
        rw [← hc, ← hc', treeNbr_some_succAbove, treeNbr_some_succAbove] at h
        simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, true_and] at h
        rw [← hc, ← hc', h.1]

/-! #### Realizing views -/

/-- The far port of the edge reached by following the path `l` (first step first) into the
branch `b` (or `0` if the path leaves the branch). -/
def portAt : (s : ℕ) → Br d s → List (Fin d) → Fin (d + 1)
  | 0, _, _ => 0
  | _ + 1, b, [] => b.port
  | s + 1, b, c :: l => portAt s (b.child c) l

/-- The arrival ports reproducing the view `V` around the root. -/
def arrOf {t : ℕ} (V : View d t) : Fin (d + 1) → List (Fin d) → Fin (d + 1) :=
  fun j r => portAt t (V j) r.reverse

theorem brOf_treeGraph (j : Fin (d + 1)) : ∀ (s : ℕ) (b : Br d (s + 1)) (r : List (Fin d)),
    (∀ r', arr j (r' ++ r) = portAt (s + 1) b r'.reverse) → ∀ c : Fin d,
      brOf (treeGraph d arr) s (some (j, r)) ((arr j r).succAbove c) = b.child c
  | 0, _, _, _, _ => Subsingleton.elim _ _
  | s + 1, b, r, H, c => by
    rw [brOf_succ, treeGraph_nbr, treeGraph_rport, treeNbr_some_succAbove]
    simp only [finPort_val]
    rw [Br.ext_iff']
    refine ⟨?_, ?_⟩
    · have := H [c]
      simpa [portAt] using this
    · funext c'
      refine brOf_treeGraph j s (b.child c) (c :: r) (fun r' => ?_) c'
      have := H (r' ++ [c])
      simpa [portAt] using this

/-- **Realization.** Every radius-`t` view occurs at the root of some port-numbered tree. -/
theorem viewOf_treeGraph_root {t : ℕ} (V : View d t) :
    viewOf (treeGraph d (arrOf V)) none t = V := by
  funext k
  cases t with
  | zero => exact Subsingleton.elim _ _
  | succ s =>
    rw [viewOf_apply, brOf_succ, treeGraph_nbr, treeGraph_rport, treeNbr_none]
    simp only [finPort_val]
    rw [Br.ext_iff']
    refine ⟨rfl, ?_⟩
    funext c
    exact brOf_treeGraph (arrOf V) k s (V k) [] (fun r' => by simp [arrOf]) c

end Trees

/-! ### Transfer -/

section Transfer

/-- A CSLib algorithm `A` (input: colour, `true` = white = active; output: a label per port)
solves the problem `(Act, Pas)` in `t` rounds on the 2-coloured port-numbered graph `(G, col)`:
every white node's configuration is in `Act`, and every black node's configuration (the labels
its neighbours put on the connecting edges) is in `Pas`. -/
def SolvesOn (d : ℕ) {L : Type} (A : Algorithm Bool (ℕ → L)) (t : ℕ) {V : Type*} (G : PNGraph V)
    (col : V → Bool) (Act Pas : Set (Multiset L)) : Prop :=
  (∀ v, col v = true → mset (fun k : Fin (d + 1) => A.eval G t col v k) ∈ Act) ∧
  (∀ u, col u = false →
    mset (fun k : Fin (d + 1) => A.eval G t col (G.nbr u k) (G.rport u k)) ∈ Pas)

variable {d : ℕ}

/-- **Transfer theorem.** If a `t`-round port-numbering algorithm solves `(Act, Pas)` on every
port numbering of the infinite 2-coloured `(d+1)`-regular tree (with either colour at the root),
then there is a view-based `t`-round algorithm solving it in the sense of `Solves`. Hence the
lower bounds proved for `Solves` apply to genuine message-passing algorithms. -/
theorem solves_of_solvesOn_trees {L : Type} (A : Algorithm Bool (ℕ → L)) (t : ℕ)
    (Act Pas : Set (Multiset L))
    (h : ∀ arr c, SolvesOn d A t (treeGraph d arr) (treeCol d c) Act Pas) :
    ∃ f : View d t → Fin (d + 1) → L, Solves f Act Pas := by
  refine ⟨fun V k => A.out (stOf A true t V) k, fun V => ?_, fun U => ?_⟩
  · have := (h (arrOf V) true).1 none rfl
    simp only [eval_eq A (treeGraph_deg _) _ (treeCol_nbr _ true), viewOf_treeGraph_root] at this
    exact this
  · have := (h (arrOf U) false).2 none rfl
    convert this using 2
    funext k
    have hk : ((k : ℕ)) < d + 1 := k.2
    rw [eval_eq A (treeGraph_deg _) _ (treeCol_nbr _ false), treeCol_nbr _ false _ _ hk,
      ← nbrView_viewOf _ (treeGraph_deg _), ← port_viewOf _ (treeGraph_deg _),
      viewOf_treeGraph_root]
    rfl

/-- Correctness on all `(d+1)`-regular properly 2-coloured port-numbered graphs implies
correctness on all the trees `treeGraph d arr`. -/
theorem solvesOn_trees_of_forall {L : Type} (A : Algorithm Bool (ℕ → L)) (t : ℕ)
    (Act Pas : Set (Multiset L))
    (h : ∀ (V : Type) (G : PNGraph V) (col : V → Bool), (∀ v, G.deg v = d + 1) →
      (∀ v (i : ℕ), i < d + 1 → col (G.nbr v i) = !col v) → SolvesOn d A t G col Act Pas) :
    ∀ arr c, SolvesOn d A t (treeGraph d arr) (treeCol d c) Act Pas :=
  fun arr c => h _ _ _ (treeGraph_deg arr) (treeCol_nbr arr c)

/-- An algorithm correct on all `(d+1)`-regular properly 2-coloured port-numbered graphs yields a
view-based algorithm in the sense of `Solves`. -/
theorem solves_of_solvesOn_all {L : Type} (A : Algorithm Bool (ℕ → L)) (t : ℕ)
    (Act Pas : Set (Multiset L))
    (h : ∀ (V : Type) (G : PNGraph V) (col : V → Bool), (∀ v, G.deg v = d + 1) →
      (∀ v (i : ℕ), i < d + 1 → col (G.nbr v i) = !col v) → SolvesOn d A t G col Act Pas) :
    ∃ f : View d t → Fin (d + 1) → L, Solves f Act Pas :=
  solves_of_solvesOn_trees A t Act Pas (solvesOn_trees_of_forall A t Act Pas h)

end Transfer

end TightBipartiteMatching
