import Papers.PODC2020.TightBipartiteMatching.Config

/-!
# Views in the 2-coloured `Δ`-regular port-numbered tree

We model deterministic `t`-round algorithms in the port-numbering model on 2-coloured `Δ`-regular
trees (no identifiers, no inputs except the colour, which is implicit) as functions of the
radius-`t` view, as is standard for round elimination (§2.2). Throughout `Δ = d + 1`.

* `Br d t` is a *branch of depth `t`*: what a node sees behind one of its ports. A branch of depth
  `t + 1` consists of the port number `j` of the edge at the far endpoint `w` and, for each other
  port of `w` (indexed by `c : Fin d` via `j.succAbove c`), a branch of depth `t`.
* `View d t = Fin (d + 1) → Br d t` is the radius-`t` view of a node: everything within distance
  `t`, including the port numbers of all edges with at least one endpoint at distance `< t`. This
  is exactly the information a node can gather in `t` rounds in a tree (see `Bridge.lean` for the
  connection with CSLib's message-passing algorithms).
* `nbrView t V k : View d t` is the radius-`t` view of the neighbour behind port `k`, computed from
  the radius-`(t + 1)` view `V` (re-rooting).
* `Solves A Act Pas`: the algorithm `A` (run by the nodes of one colour, the *active* side) outputs
  a label on each port; every active node's configuration is in `Act` and every passive node's
  configuration (the labels its `Δ` neighbours put on the connecting edges) is in `Pas`. Since every
  radius-`t` view and every radius-`(t + 1)` view of a passive node occurs in some port numbering of
  the infinite tree, this is correctness on all port numberings of the tree.
-/

-- CSLib candidate (bipartite round elimination infrastructure)
namespace TightBipartiteMatching

/-- Branches of depth `t` of the port-numbered `(d+1)`-regular tree. -/
def Br (d : ℕ) : ℕ → Type
  | 0 => Unit
  | t + 1 => Fin (d + 1) × (Fin d → Br d t)

namespace Br

variable {d : ℕ}

/-- The branch of depth `t + 1` with far port `j` and sub-branches `ch`. -/
def mk {t : ℕ} (j : Fin (d + 1)) (ch : Fin d → Br d t) : Br d (t + 1) := (j, ch)

/-- The port number, at the far endpoint, of the edge leading into the branch. -/
def port {t : ℕ} (b : Br d (t + 1)) : Fin (d + 1) :=
  (show Fin (d + 1) × (Fin d → Br d t) from b).1

/-- The sub-branches of the far endpoint (behind its ports `port.succAbove c`). -/
def child {t : ℕ} (b : Br d (t + 1)) : Fin d → Br d t :=
  (show Fin (d + 1) × (Fin d → Br d t) from b).2

@[simp] theorem port_mk {t : ℕ} (j : Fin (d + 1)) (ch : Fin d → Br d t) : (mk j ch).port = j := rfl
@[simp] theorem child_mk {t : ℕ} (j : Fin (d + 1)) (ch : Fin d → Br d t) :
    (mk j ch).child = ch := rfl
@[simp] theorem mk_port_child {t : ℕ} (b : Br d (t + 1)) : mk b.port b.child = b := rfl

theorem ext_iff' {t : ℕ} {b b' : Br d (t + 1)} : b = b' ↔ b.port = b'.port ∧ b.child = b'.child := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← mk_port_child b, ← mk_port_child b', h1, h2]

instance instInhabited : (t : ℕ) → Inhabited (Br d t)
  | 0 => ⟨()⟩
  | t + 1 => ⟨mk 0 fun _ => (instInhabited t).default⟩

instance instSubsingletonZero : Subsingleton (Br d 0) := inferInstanceAs (Subsingleton Unit)

/-- Truncate a branch by one level. -/
def restrict : (t : ℕ) → Br d (t + 1) → Br d t
  | 0, _ => ()
  | t + 1, b => mk b.port fun c => restrict t (b.child c)

/-- Extend a branch by one level (arbitrarily). -/
def ext : (t : ℕ) → Br d t → Br d (t + 1)
  | 0, _ => mk 0 fun _ => ()
  | t + 1, b => mk b.port fun c => ext t (b.child c)

@[simp] theorem restrict_mk {t : ℕ} (j : Fin (d + 1)) (ch : Fin d → Br d (t + 1)) :
    restrict (t + 1) (mk j ch) = mk j fun c => restrict t (ch c) := rfl

@[simp] theorem port_restrict {t : ℕ} (b : Br d (t + 2)) : (restrict (t + 1) b).port = b.port := rfl

@[simp] theorem child_restrict {t : ℕ} (b : Br d (t + 2)) (c : Fin d) :
    (restrict (t + 1) b).child c = restrict t (b.child c) := rfl

@[simp] theorem restrict_ext : (t : ℕ) → (b : Br d t) → restrict t (ext t b) = b
  | 0, _ => Subsingleton.elim _ _
  | t + 1, b => by
    rw [ext, restrict_mk]
    conv_rhs => rw [← mk_port_child b]
    congr 1
    funext c
    exact restrict_ext t _

end Br

/-- The radius-`t` view of a node of the `(d+1)`-regular tree: one branch per port. -/
abbrev View (d t : ℕ) := Fin (d + 1) → Br d t

namespace View

variable {d : ℕ}

/-- Truncate a view by one level. -/
def restrict {t : ℕ} (V : View d (t + 1)) : View d t := fun k => Br.restrict t (V k)

/-- Extend a view by one level (arbitrarily). -/
def ext {t : ℕ} (V : View d t) : View d (t + 1) := fun k => Br.ext t (V k)

@[simp] theorem restrict_ext {t : ℕ} (V : View d t) : restrict (ext V) = V := by
  funext k; simp [restrict, ext]

@[simp] theorem restrict_apply {t : ℕ} (V : View d (t + 1)) (k : Fin (d + 1)) :
    restrict V k = Br.restrict t (V k) := rfl

instance instSubsingletonZero : Subsingleton (View d 0) :=
  inferInstanceAs (Subsingleton (Fin (d + 1) → Br d 0))

instance instInhabited {t : ℕ} : Inhabited (View d t) := ⟨fun _ => default⟩

end View

variable {d : ℕ}

/-- Re-rooting: the radius-`t` view of the neighbour behind port `k`, computed from the
radius-`(t + 1)` view `V`. The neighbour `w` reaches us through its port `j = (V k).port`; behind
`j` it sees us (our port `k`) and our other branches, truncated to depth `t - 1`; behind its other
ports it sees `(V k).child`. -/
def nbrView : (t : ℕ) → View d (t + 1) → Fin (d + 1) → View d t
  | 0, _, _ => fun _ => ()
  | t + 1, V, k => Fin.insertNth (α := fun _ => Br d (t + 1)) (V k).port
      (Br.mk k fun c => Br.restrict t (Br.restrict (t + 1) (V (k.succAbove c)))) (V k).child

theorem nbrView_succ_apply_port {t : ℕ} (V : View d (t + 2)) (k : Fin (d + 1)) :
    nbrView (t + 1) V k (V k).port =
      Br.mk k fun c => Br.restrict t (Br.restrict (t + 1) (V (k.succAbove c))) := by
  simp [nbrView]

theorem nbrView_succ_apply_succAbove {t : ℕ} (V : View d (t + 2)) (k : Fin (d + 1)) (c : Fin d) :
    nbrView (t + 1) V k ((V k).port.succAbove c) = (V k).child c := by
  simp [nbrView]

/-- The neighbour's view depends only on the branch behind port `k` and on the other branches
truncated by two levels. -/
theorem nbrView_congr {t : ℕ} {V V' : View d (t + 2)} {k : Fin (d + 1)} (hk : V k = V' k)
    (h : ∀ k', Br.restrict t (Br.restrict (t + 1) (V k')) = Br.restrict t (Br.restrict (t + 1) (V' k'))) :
    nbrView (t + 1) V k = nbrView (t + 1) V' k := by
  simp only [nbrView, hk, h]

/-- Truncation commutes with re-rooting. -/
theorem restrict_nbrView {t : ℕ} (V : View d (t + 2)) (k : Fin (d + 1)) :
    View.restrict (nbrView (t + 1) V k) = nbrView t (View.restrict V) k := by
  cases t with
  | zero => exact Subsingleton.elim _ _
  | succ t =>
    funext p
    rcases eq_or_ne p (V k).port with rfl | hp
    · simp [nbrView, View.restrict]
    · obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hp
      simp [nbrView, View.restrict]

/-! ### Algorithms and correctness -/

/-- `A` (a `t`-round algorithm run by the active colour) solves the problem with active constraint
`Act` and passive constraint `Pas` on all port numberings of the 2-coloured `(d+1)`-regular tree.
For a passive node with radius-`(t+1)` view `U`, the neighbour behind port `k` has view
`nbrView t U k` and reaches the passive node through its port `(U k).port`. -/
def Solves {L : Type*} {t : ℕ} (A : View d t → Fin (d + 1) → L) (Act Pas : Set (Multiset L)) :
    Prop :=
  (∀ V, mset (A V) ∈ Act) ∧ ∀ U : View d (t + 1), mset (fun k => A (nbrView t U k) (U k).port) ∈ Pas

/-- An algorithm can always be slowed down: a `t`-round algorithm is also a `(t+1)`-round one. -/
theorem Solves.succ {L : Type*} {t : ℕ} {A : View d t → Fin (d + 1) → L}
    {Act Pas : Set (Multiset L)} (h : Solves A Act Pas) :
    Solves (fun V : View d (t + 1) => A (View.restrict V)) Act Pas := by
  refine ⟨fun V => h.1 _, fun U => ?_⟩
  have := h.2 (View.restrict U)
  simpa [restrict_nbrView] using this

theorem Solves.mono {L : Type*} {t t' : ℕ} (htt : t ≤ t') {Act Pas : Set (Multiset L)}
    (h : ∃ A : View d t → Fin (d + 1) → L, Solves A Act Pas) :
    ∃ A : View d t' → Fin (d + 1) → L, Solves A Act Pas := by
  induction htt with
  | refl => exact h
  | step _ ih => obtain ⟨A, hA⟩ := ih; exact ⟨_, hA.succ⟩

/-- **0-round algorithms.** All nodes have the same radius-0 view, so a 0-round algorithm outputs a
fixed tuple `c`; a passive node may see any combination of its entries. -/
theorem solves_zero_iff {L : Type*} {A : View d 0 → Fin (d + 1) → L}
    {Act Pas : Set (Multiset L)} :
    Solves A Act Pas ↔
      mset (A default) ∈ Act ∧ ∀ j : Fin (d + 1) → Fin (d + 1), mset (fun k => A default (j k)) ∈ Pas := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1 _, fun j => ?_⟩
    have := h2 fun k => Br.mk (j k) fun _ => ()
    have e : (fun k => A (nbrView 0 (fun k => Br.mk (j k) fun _ => ()) k)
        (Br.mk (t := 0) (j k) fun _ => ()).port) = fun k => A default (j k) := by
      funext k; rw [Subsingleton.elim (nbrView 0 _ k) default]; rfl
    rwa [e] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun V => by rwa [Subsingleton.elim V default], fun U => ?_⟩
    have := h2 fun k => (U k).port
    have e : (fun k => A (nbrView 0 U k) (U k).port) = fun k => A default (U k).port := by
      funext k; rw [Subsingleton.elim (nbrView 0 U k) default]
    rwa [e]

/-- A problem is not solvable in 0 rounds if every allowed active configuration contains a label
`ℓ` such that `Δ` copies of `ℓ` are not an allowed passive configuration. -/
theorem not_solves_zero {L : Type*} {Act Pas : Set (Multiset L)}
    (h : ∀ g : Fin (d + 1) → L, mset g ∈ Act → ∃ k, mset (fun _ : Fin (d + 1) => g k) ∉ Pas)
    (A : View d 0 → Fin (d + 1) → L) : ¬ Solves A Act Pas := by
  rw [solves_zero_iff]
  rintro ⟨h1, h2⟩
  obtain ⟨k, hk⟩ := h _ h1
  exact hk (h2 fun _ => k)

end TightBipartiteMatching
