import Papers.PODC2016.AnalysingSI.Characterisation
import Papers.PODC2016.AnalysingSI.CycleDefs
import Papers.PODC2016.AnalysingSI.TxnLemmas

/-!
# Transaction chopping under SI (Cerone–Gotsman, PODC 2016, §5 and §A.5)

* A *chopped history* lists, for every session `s : ι`, its transactions in session order
  (`Chopped`); its history `C.history` has the session order `SO` of Definition 2, and
  `C.splice` is `splice(H)`: one transaction per session, the concatenation of its transactions
  in session order, and empty session order.
* The dynamic chopping graph `DCG(G)` (`Chopped.dcg`), critical cycles (`Chopped.IsCritical`),
  spliceability (`Chopped.Spliceable`).
* `splice(G)` (equation (2)), Lemma 17, Lemma 26, Lemma 27 and **Theorem 16**.
-/

namespace Podc.AnalysingSI

open Relation

variable {Obj V : Type*} [DecidableEq Obj] {ι : Type*}

/-- A history given by its sessions: `sess s` lists the transactions of session `s` in session
order. Sessions are nonempty. -/
structure Chopped (ι Obj V : Type*) where
  /-- The transactions of each session, in session order. -/
  sess : ι → List (Txn Obj V)
  /-- Every session contains a transaction. -/
  sess_ne : ∀ s, sess s ≠ []

namespace Chopped

variable (C : Chopped ι Obj V)

/-- Transaction identifiers: pairs (session, position in the session). -/
def Tid : Type _ := {p : ι × ℕ // p.2 < (C.sess p.1).length}

/-- The history `(𝒯, SO)` of a chopped program: `T —SO→ S` iff `T` precedes `S` in the same
session. -/
def history : History C.Tid Obj V where
  txn p := (C.sess p.1.1)[p.1.2]'p.2
  SO p q := p.1.1 = q.1.1 ∧ p.1.2 < q.1.2

/-- `splice(H)`: each session becomes a single transaction (the concatenation of its
transactions in session order); the session order is empty. -/
def splice : History ι Obj V where
  txn s := (C.sess s).flatten
  SO _ _ := False

/-- A tuple `(𝒯, SO, WR, WW, RW)` over the history of `C`. -/
def graph (WR WW : Obj → C.Tid → C.Tid → Prop) : DepGraph C.Tid Obj V :=
  { toHistory := C.history, WR := WR, WW := WW }

/-- A dependency graph over `C` is *spliceable* if some graph over `splice(H)` is in
`GraphSI`. -/
def Spliceable : Prop :=
  ∃ WR WW : Obj → ι → ι → Prop, (DepGraph.mk C.splice WR WW).IsSI

/-- Edge labels of the dynamic chopping graph: successor, predecessor, and the three kinds of
conflict edges. -/
inductive CLbl where
  | succ | pred | wr | ww | rw
  deriving DecidableEq

/-- Conflict edges. -/
def CLbl.IsConflict : CLbl → Prop
  | .wr | .ww | .rw => True
  | _ => False

instance : DecidablePred CLbl.IsConflict := fun l => by
  cases l <;> simp [CLbl.IsConflict] <;> infer_instance

variable {C}

/-- The dynamic chopping graph `DCG(G)`: successor edges `SO`, predecessor edges `SO⁻¹`, and
the `WR`, `WW`, `RW` edges between transactions of different sessions. -/
def dcg (G : DepGraph C.Tid Obj V) : CLbl → C.Tid → C.Tid → Prop
  | .succ => G.SO
  | .pred => fun p q => G.SO q p
  | .wr => fun p q => G.WRu p q ∧ p.1.1 ≠ q.1.1
  | .ww => fun p q => G.WWu p q ∧ p.1.1 ≠ q.1.1
  | .rw => fun p q => G.RWu p q ∧ p.1.1 ≠ q.1.1

/-- A critical cycle (§5) of an edge-labelled graph `E` with successor, predecessor and conflict
edges: (i) it does not contain two occurrences of the same vertex; (ii) it contains three
consecutive edges "conflict, predecessor, conflict"; (iii) any two anti-dependency edges on it are
separated by at least one read or write dependency edge. -/
structure IsCriticalIn {β : Type*} (E : CLbl → β → β → Prop) (w : List (CLbl × β)) : Prop where
  cycle : IsCycle E w
  simple : IsSimple w
  cpc : ∃ k c₁ c₂ rest, (labels w).rotate k = c₁ :: .pred :: c₂ :: rest ∧
    c₁.IsConflict ∧ c₂.IsConflict
  sep : ∀ k mid rest, (labels w).rotate k = .rw :: (mid ++ .rw :: rest) →
    ∃ c ∈ mid, c = .wr ∨ c = .ww

/-- A critical cycle of the dynamic chopping graph `DCG(G)`. -/
abbrev IsCritical (G : DepGraph C.Tid Obj V) (w : List (CLbl × C.Tid)) : Prop :=
  IsCriticalIn (dcg G) w

end Chopped

end Podc.AnalysingSI
