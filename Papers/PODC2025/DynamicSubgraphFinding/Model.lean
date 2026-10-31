import Mathlib

/-!
# Dynamic distributed subgraph finding: the model

Chang–Chen–Chen–Mishra–Yang, *The Complexity Landscape of Dynamic Distributed Subgraph Finding*
(PODC 2025, arXiv 2411.11544v3), Section 1.1–1.2 (model of Bonne and Censor-Hillel).

* `InsNet V`: an insertion-only dynamic network on the identifier set `V`: for every round `r` the
  set of present nodes `pres r` and the graph `adj r`, both monotone in `r`. `G⁰ = (pres 0, adj 0)`.
* Topological changes: `EdgeInsStep D r` (round `r + 1` inserts at most one edge, no node),
  `NodeInsStep D r` (round `r + 1` inserts one new node with an arbitrary set of edges to present
  nodes). The two models of the paper used here: `EdgeIns D` (edge insertions only) and
  `NodeEdgeIns D` (node and edge insertions).
* `Algorithm V M O`: a deterministic synchronous algorithm with message alphabet `M` (bandwidth
  `B` bits ↔ `card M ≤ 2 ^ B`). Every node knows `G⁰` and its identifier, and in every round `r ≥ 1`
  it sees its *local input* `loc D r v` (whether it is present and its current neighbour set),
  sends one message to each neighbour (computed from its state and local input), and updates its
  state from the messages received from its neighbours. The topological change of round `r`
  happens before the communication of round `r`. Round numbers are global knowledge.
* `state A D r v`: the state of `v` after round `r`; `A.out (state A D r v)` is its output for
  `G^r`. A one-round algorithm must be correct after every round (`Solves`).
* Problems: `MemDetectOK`, `DetectOK` (target `K_s`), `MemListOK`, `ListOK` (target `K₃`).

Absent (not yet inserted) nodes run the algorithm with local input `none`; this only gives them
more knowledge (they know the round number and `G⁰`), which makes lower bounds stronger, and their
outputs are ignored.
-/

namespace Podc.DynamicSubgraphFinding

open Classical

-- CSLib candidate: Cslib/Computability/Distributed/DynamicNetworks/Insertion.lean (bandwidth-limited
-- synchronous algorithms on insertion-only dynamic networks, with the locality lemmas below).
/-- An insertion-only dynamic network on the identifier set `V`. -/
structure InsNet (V : Type) where
  /-- `pres r v`: node `v` is present in `G^r`. -/
  pres : ℕ → V → Prop
  /-- `adj r u v`: `{u, v}` is an edge of `G^r`. -/
  adj : ℕ → V → V → Prop
  symm : ∀ r u v, adj r u v → adj r v u
  irrefl : ∀ r v, ¬ adj r v v
  pres_of_adj : ∀ r u v, adj r u v → pres r u
  pres_mono : ∀ r v, pres r v → pres (r + 1) v
  adj_mono : ∀ r u v, adj r u v → adj (r + 1) u v

variable {V : Type}

namespace InsNet

/-- The graph `G^r`. -/
def graph (D : InsNet V) (r : ℕ) : SimpleGraph V where
  Adj := D.adj r
  symm := ⟨fun u v h => D.symm r u v h⟩
  loopless := ⟨fun v h => D.irrefl r v h⟩

/-- Edges inserted in round `r + 1`. -/
def NewEdge (D : InsNet V) (r : ℕ) (u v : V) : Prop := D.adj (r + 1) u v ∧ ¬ D.adj r u v

/-- Round `r + 1` inserts no node and at most one edge. -/
def EdgeInsStep (D : InsNet V) (r : ℕ) : Prop :=
  (∀ v, D.pres (r + 1) v → D.pres r v) ∧
    ∀ u v u' v', D.NewEdge r u v → D.NewEdge r u' v' → s(u, v) = s(u', v')

/-- Round `r + 1` inserts (at most) one new node `x`, with an arbitrary set of incident edges
(towards nodes present before), and nothing else. -/
def NodeInsStep (D : InsNet V) (r : ℕ) : Prop :=
  ∃ x, ¬ D.pres r x ∧ (∀ v, D.pres (r + 1) v → D.pres r v ∨ v = x) ∧
    ∀ u v, D.NewEdge r u v → u = x ∨ v = x

/-- The model "edge insertions only". -/
def EdgeIns (D : InsNet V) : Prop := ∀ r, D.EdgeInsStep r

/-- The model "node insertions and edge insertions". -/
def NodeEdgeIns (D : InsNet V) : Prop := ∀ r, D.EdgeInsStep r ∨ D.NodeInsStep r

/-- Maximum degree at most `Δ` (in every round). -/
def DegLE (D : InsNet V) (Δ : ℕ) : Prop := ∀ r v, Set.ncard {u | D.adj r u v} ≤ Δ

/-- Local input of `v` in round `r`: `none` if absent, otherwise its neighbour set. -/
noncomputable def loc (D : InsNet V) (r : ℕ) (v : V) : Option (Set V) :=
  if D.pres r v then some {u | D.adj r u v} else none

lemma pres_le (D : InsNet V) {r r' : ℕ} (h : r ≤ r') {v : V} (hv : D.pres r v) : D.pres r' v := by
  induction h with
  | refl => exact hv
  | step _ ih => exact D.pres_mono _ _ ih

lemma adj_le (D : InsNet V) {r r' : ℕ} (h : r ≤ r') {u v : V} (huv : D.adj r u v) :
    D.adj r' u v := by
  induction h with
  | refl => exact huv
  | step _ ih => exact D.adj_mono _ _ _ ih

end InsNet

/-- A deterministic synchronous algorithm with message alphabet `M` and outputs in `O`.
`init G⁰ v`: initial state (every node knows `G⁰` and its own identifier);
`send r st x w`: message to neighbour `w` in round `r` (state before the round, local input `x`
of round `r`); `recv r st x inbox`: new state after receiving `inbox u` (`none` for
non-neighbours). -/
structure Algorithm (V M O : Type) where
  State : Type
  init : (V → Prop) → (V → V → Prop) → V → State
  send : ℕ → State → Option (Set V) → V → M
  recv : ℕ → State → Option (Set V) → (V → Option M) → State
  out : State → O

namespace Algorithm

variable {M O : Type} (A : Algorithm V M O) (D : InsNet V)

/-- Messages received by `v` in round `r`, given the states `st` before the round. -/
noncomputable def inbox (st : V → A.State) (r : ℕ) (v : V) : V → Option M :=
  fun u => if D.adj r u v then some (A.send r (st u) (D.loc r u) v) else none

/-- State of every node after round `r` (`r = 0`: initial state). -/
noncomputable def state : ℕ → V → A.State
  | 0 => fun v => A.init (D.pres 0) (D.adj 0) v
  | r + 1 => fun v => A.recv (r + 1) (state r v) (D.loc (r + 1) v) (A.inbox D (state r) (r + 1) v)

/-- Output of `v` after round `r`. -/
noncomputable def output (r : ℕ) (v : V) : O := A.out (A.state D r v)

lemma state_succ (r : ℕ) (v : V) :
    A.state D (r + 1) v =
      A.recv (r + 1) (A.state D r v) (D.loc (r + 1) v) (A.inbox D (A.state D r) (r + 1) v) := rfl

end Algorithm

/-! ### Problems -/

section Problems

variable {M : Type}

/-- `MemDetect(K_s)` is solved correctly after round `r`: every present node outputs `true` iff
it belongs to an `s`-clique of `G^r`. -/
def MemDetectOK (s : ℕ) (A : Algorithm V M Bool) (D : InsNet V) (r : ℕ) : Prop :=
  ∀ v, D.pres r v → (A.output D r v = true ↔ ∃ Q, (D.graph r).IsNClique s Q ∧ v ∈ Q)

/-- `Detect(K_s)` is solved correctly after round `r`: if `G^r` contains no `s`-clique, all
present nodes output `false`; otherwise some present node outputs `true`. -/
def DetectOK (s : ℕ) (A : Algorithm V M Bool) (D : InsNet V) (r : ℕ) : Prop :=
  (∃ Q, (D.graph r).IsNClique s Q) ↔ ∃ v, D.pres r v ∧ A.output D r v = true

/-- `MemList(K₃)`: every present node lists exactly the triangles of `G^r` containing it. -/
def MemListOK (A : Algorithm V M (Set (Finset V))) (D : InsNet V) (r : ℕ) : Prop :=
  ∀ v, D.pres r v → ∀ Q, Q ∈ A.output D r v ↔ (D.graph r).IsNClique 3 Q ∧ v ∈ Q

/-- `List(K₃)`: every triangle of `G^r` is listed by some present node, and present nodes list
only triangles of `G^r`. -/
def ListOK (A : Algorithm V M (Set (Finset V))) (D : InsNet V) (r : ℕ) : Prop :=
  (∀ Q, (D.graph r).IsNClique 3 Q → ∃ v, D.pres r v ∧ Q ∈ A.output D r v) ∧
    ∀ v, D.pres r v → ∀ Q ∈ A.output D r v, (D.graph r).IsNClique 3 Q

/-- A one-round algorithm solves a problem (`OK D r`: correct output after round `r`) in a model
of dynamic networks of maximum degree `≤ Δ`: correct after every round of every such network. -/
def Solves {O : Type} (A : Algorithm V M O) (Model : InsNet V → Prop) (Δ : ℕ)
    (OK : Algorithm V M O → InsNet V → ℕ → Prop) : Prop :=
  ∀ D, Model D → D.DegLE Δ → ∀ r, OK A D r

end Problems

/-! ### Locality -/

namespace Algorithm

variable {M O : Type} (A : Algorithm V M O)

/-- A node whose local inputs and received messages agree in two networks with the same `G⁰`
is in the same state. -/
lemma state_eq_of_inbox {D D' : InsNet V} (h0 : D.pres 0 = D'.pres 0 ∧ D.adj 0 = D'.adj 0)
    (v : V) (r : ℕ) (hloc : ∀ k ≤ r, D.loc k v = D'.loc k v)
    (hin : ∀ k, k + 1 ≤ r → A.inbox D (A.state D k) (k + 1) v = A.inbox D' (A.state D' k) (k + 1) v) :
    A.state D r v = A.state D' r v := by
  induction r with
  | zero => simp [state, h0.1, h0.2]
  | succ r ih =>
    rw [state_succ, state_succ, ih (fun k hk => hloc k (by omega)) (fun k hk => hin k (by omega)),
      hloc (r + 1) le_rfl, hin r le_rfl]

/-- **Closed sets.** If a set `C` of nodes has the same local inputs in `D` and `D'` up to round
`r`, and in every round `≤ r` every neighbour of a member of `C` is in `C` (in both networks),
then the states of the members of `C` agree up to round `r`. -/
lemma state_eq_of_closed {D D' : InsNet V} (h0 : D.pres 0 = D'.pres 0 ∧ D.adj 0 = D'.adj 0)
    (C : V → Prop) (r : ℕ) (hloc : ∀ k ≤ r, ∀ v, C v → D.loc k v = D'.loc k v)
    (hadj : ∀ k ≤ r, ∀ u v, C v → (D.adj k u v ↔ D'.adj k u v))
    (hcl : ∀ k ≤ r, ∀ u v, C v → D.adj k u v → C u) :
    ∀ k ≤ r, ∀ v, C v → A.state D k v = A.state D' k v := by
  intro k hk
  induction k with
  | zero => intro v _; simp [state, h0.1, h0.2]
  | succ k ih =>
    intro v hv
    have ih' := ih (by omega)
    rw [state_succ, state_succ, ih' v hv, hloc (k + 1) hk v hv]
    congr 1
    funext u
    unfold inbox
    by_cases hu : D.adj (k + 1) u v
    · have hu' := (hadj (k + 1) hk u v hv).1 hu
      have hCu := hcl (k + 1) hk u v hv hu
      rw [ite_eq_left hu, ite_eq_left hu', ih' u hCu, hloc (k + 1) hk u hCu]
    · have hu' : ¬ D'.adj (k + 1) u v := fun h => hu ((hadj (k + 1) hk u v hv).2 h)
      rw [ite_eq_right hu, ite_eq_right hu']

/-- Variant of `state_eq_of_inbox`: same neighbourhoods, and the same messages from every
neighbour. -/
lemma state_eq_of_msgs {D D' : InsNet V} (h0 : D.pres 0 = D'.pres 0 ∧ D.adj 0 = D'.adj 0)
    (v : V) (r : ℕ) (hloc : ∀ k ≤ r, D.loc k v = D'.loc k v)
    (hadj : ∀ k ≤ r, ∀ u, D.adj k u v ↔ D'.adj k u v)
    (hmsg : ∀ k, k + 1 ≤ r → ∀ u, D.adj (k + 1) u v →
      A.send (k + 1) (A.state D k u) (D.loc (k + 1) u) v =
        A.send (k + 1) (A.state D' k u) (D'.loc (k + 1) u) v) :
    A.state D r v = A.state D' r v := by
  refine A.state_eq_of_inbox h0 v r hloc (fun k hk => ?_)
  funext u
  unfold inbox
  by_cases hu : D.adj (k + 1) u v
  · rw [ite_eq_left hu, ite_eq_left ((hadj (k + 1) hk u).1 hu), hmsg k hk u hu]
  · rw [ite_eq_right hu, ite_eq_right (fun h => hu ((hadj (k + 1) hk u).2 h))]

end Algorithm

end Podc.DynamicSubgraphFinding
