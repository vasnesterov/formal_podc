import Mathlib

/-!
# Chained HotStuff (Algorithm 3 of HotStuff, PODC 2019): model

An asynchronous, interleaving model of the replica code of Algorithm 3 ("Chained HotStuff") of
Yin, Malkhi, Reiter, Gueta, Abraham, *HotStuff: BFT Consensus with Linearity and Responsiveness*
(PODC 2019, arXiv 1803.05069v6).

* Replicas `P` (`n = Fintype.card P`), resilience parameter `f`, Byzantine set `F`.
* Nodes form a tree; a node carries its parent, a command and its justify QC `(jv, jn)`.
  The genesis node `gen` carries the hard-coded QC `(0, gen)`.
* Ideal threshold signatures: a QC `(v, x)` is valid iff it is the genesis QC or at least `n - f`
  replicas "signed" it, where every Byzantine replica signs everything (an over-approximation of
  the Byzantine behaviour) and a correct replica signs exactly the votes it cast.
* The leader of a view may be Byzantine, so a replica may receive *any* proposal; the pacemaker
  (`nextView`) is arbitrary. The leader code of Algorithm 3 is therefore not modelled: everything
  a (possibly Byzantine) leader can do is covered.
* Three variants of the replica code (`Variant`): the pseudocode as written (`literal`), with a
  monotone lock update (`monoLock`, as in Algorithm 4), and with a height check
  `b*.height = curView` (`heightCheck`), which the paper assumes ("view-numbers are equated with
  node heights") but never checks.
-/

namespace HotStuff.Chained

/-- Nodes of the tree. `mk parent cmd jv jn` is a node with parent `parent`, command `cmd` and
justify QC `(jv, jn)`. -/
inductive Node (C : Type) where
  | gen : Node C
  | mk (parent : Node C) (cmd : C) (jv : ℕ) (jn : Node C) : Node C
  deriving DecidableEq

namespace Node

variable {C : Type}

/-- The parent of a node (`none` for genesis). -/
def parent? : Node C → Option (Node C)
  | gen => none
  | mk p _ _ _ => some p

/-- View number of the justify QC (the genesis QC has view `0`). -/
def jv : Node C → ℕ
  | gen => 0
  | mk _ _ v _ => v

/-- Node of the justify QC (the genesis QC refers to genesis itself). -/
def jn : Node C → Node C
  | gen => gen
  | mk _ _ _ n => n

/-- The justify QC `b.justify` as a pair (view number, node). -/
def justify (b : Node C) : ℕ × Node C := (b.jv, b.jn)

/-- Height = number of parent links to genesis. -/
def height : Node C → ℕ
  | gen => 0
  | mk p _ _ _ => p.height + 1

/-- `IsAnc a b`: `a` is an ancestor of `b` or equal to it ("`b` extends `a`"). -/
def IsAnc (a : Node C) : Node C → Prop
  | gen => a = gen
  | mk p c v n => a = mk p c v n ∨ IsAnc a p

/-- `StrictAnc a b`: `a` is a strict ancestor of `b`. -/
def StrictAnc (a : Node C) : Node C → Prop
  | gen => False
  | mk p _ _ _ => IsAnc a p

instance decIsAnc [DecidableEq C] (a : Node C) : (b : Node C) → Decidable (IsAnc a b)
  | gen => inferInstanceAs (Decidable (a = gen))
  | mk p c v n =>
    have := decIsAnc a p
    inferInstanceAs (Decidable (a = mk p c v n ∨ IsAnc a p))

instance decStrictAnc [DecidableEq C] (a : Node C) : (b : Node C) → Decidable (StrictAnc a b)
  | gen => inferInstanceAs (Decidable False)
  | mk p _ _ _ => inferInstanceAs (Decidable (IsAnc a p))

/-- Two nodes conflict if neither extends the other. -/
def Conflict (a b : Node C) : Prop := ¬ IsAnc a b ∧ ¬ IsAnc b a

instance [DecidableEq C] (a b : Node C) : Decidable (Conflict a b) :=
  inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

/-- `b` forms a (direct) Two-Chain: `b.parent = b.justify.node` and
`b.justify.node.parent = b.justify.node.justify.node`. -/
def Chain2 (b : Node C) : Prop := b.parent? = some b.jn ∧ b.jn.parent? = some b.jn.jn

instance [DecidableEq C] (b : Node C) : Decidable (Chain2 b) := inferInstanceAs (Decidable (_ ∧ _))

end Node

open Node

/-- Variants of the replica code. -/
inductive Variant where
  /-- Algorithm 3 as written. -/
  | literal
  /-- Lock updated only if the new locked QC has a larger view number (cf. Algorithm 4). -/
  | monoLock
  /-- Algorithm 3 with the additional guard `b*.height = curView`. -/
  | heightCheck
  deriving DecidableEq

variable {P C : Type} [Fintype P] [DecidableEq P] [DecidableEq C]

/-- Local state of a correct replica. -/
structure Local (C : Type) where
  /-- `curView` (starts at 1). -/
  view : ℕ
  /-- `lockedQC` (initially the genesis QC). -/
  lock : ℕ × Node C
  /-- `genericQC` (initially the genesis QC). -/
  gqc : ℕ × Node C
  /-- whether a proposal of the current view was already processed. -/
  done : Bool
  /-- nodes `b` such that "execute new commands through `b`" (Line 22) happened. -/
  committed : Finset (Node C)

/-- Global state: local states and the set of all votes `(replica, view, node)` cast by correct
replicas. -/
structure State (P C : Type) where
  loc : P → Local C
  votes : Finset (P × ℕ × Node C)

/-- Initial state. -/
def init : State P C where
  loc _ := { view := 1, lock := (0, gen), gqc := (0, gen), done := false, committed := ∅ }
  votes := ∅

/-- Signers of a QC: Byzantine replicas (they can sign anything) and correct replicas that voted. -/
def signers (F : Finset P) (V : Finset (P × ℕ × Node C)) (q : ℕ × Node C) : Finset P :=
  Finset.univ.filter fun i => i ∈ F ∨ (i, q.1, q.2) ∈ V

/-- Validity of a QC under ideal threshold signatures with threshold `n - f`. -/
def Valid (f : ℕ) (F : Finset P) (V : Finset (P × ℕ × Node C)) (q : ℕ × Node C) : Prop :=
  (q.1 = 0 ∧ q.2 = gen) ∨ Fintype.card P - f ≤ (signers F V q).card

instance (f : ℕ) (F : Finset P) (V : Finset (P × ℕ × Node C)) (q : ℕ × Node C) :
    Decidable (Valid f F V q) := inferInstanceAs (Decidable (_ ∨ _))

/-- `safeNode(b, b.justify)` (Algorithm 1, Lines 25-27) for a replica with locked QC `lock`. -/
def SafeNode (lock : ℕ × Node C) (b : Node C) : Prop := IsAnc lock.2 b ∨ lock.1 < b.jv

instance (lock : ℕ × Node C) (b : Node C) : Decidable (SafeNode lock b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The new locked QC (Line 20). -/
def newLock : Variant → (ℕ × Node C) → (ℕ × Node C) → ℕ × Node C
  | .monoLock, old, new => if old.1 < new.1 then new else old
  | _, _, new => new

/-- Local effect of processing the proposal `b` (= `b*`), Lines 14-22 of Algorithm 3. -/
def Local.process (var : Variant) (l : Local C) (b : Node C) : Local C where
  view := l.view
  gqc := if b.parent? = some b.jn then b.justify else l.gqc
  lock := if Chain2 b then newLock var l.lock b.jn.justify else l.lock
  done := true
  committed := if Chain2 b ∧ b.jn.jn.parent? = some b.jn.jn.jn then insert b.jn.jn.jn l.committed
    else l.committed

/-- Actions of correct replicas. -/
inductive Action (P C : Type) where
  /-- `nextView` interrupt: the pacemaker moves replica `r` to view `v`. -/
  | nextView (r : P) (v : ℕ)
  /-- Replica `r` receives the proposal `b` from the leader of its current view. -/
  | process (r : P) (b : Node C)

/-- Guards of the actions. -/
def Enabled (var : Variant) (f : ℕ) (F : Finset P) : Action P C → State P C → Prop
  | .nextView r v, s => r ∉ F ∧ (s.loc r).view < v
  | .process r b, s => r ∉ F ∧ (s.loc r).done = false ∧ Valid f F s.votes b.justify ∧
      StrictAnc b.jn b ∧ (var = .heightCheck → b.height = (s.loc r).view)

instance (var : Variant) (f : ℕ) (F : Finset P) (a : Action P C) (s : State P C) :
    Decidable (Enabled var f F a s) := by
  cases a <;> unfold Enabled <;> infer_instance

/-- Effects of the actions. -/
def apply (var : Variant) : Action P C → State P C → State P C
  | .nextView r v, s =>
    { s with loc := Function.update s.loc r { s.loc r with view := v, done := false } }
  | .process r b, s =>
    { loc := Function.update s.loc r ((s.loc r).process var b)
      votes := if SafeNode (s.loc r).lock b then insert (r, (s.loc r).view, b) s.votes
        else s.votes }

/-- One step of a correct replica. -/
def Step (var : Variant) (f : ℕ) (F : Finset P) (s s' : State P C) : Prop :=
  ∃ a, Enabled var f F a s ∧ s' = apply var a s

/-- Reachable states. -/
def Reachable (var : Variant) (f : ℕ) (F : Finset P) (s : State P C) : Prop :=
  Relation.ReflTransGen (Step var f F) init s

/-- Safety (Theorem 5): no two nodes committed by correct replicas conflict. -/
def Safe (P C : Type) [Fintype P] [DecidableEq P] [DecidableEq C] (var : Variant) (f : ℕ)
    (F : Finset P) : Prop :=
  ∀ s : State P C, Reachable var f F s → ∀ r₁ r₂, r₁ ∉ F → r₂ ∉ F →
    ∀ b₁ ∈ (s.loc r₁).committed, ∀ b₂ ∈ (s.loc r₂).committed, ¬ Conflict b₁ b₂

/-! ### Executing a list of actions (for concrete executions) -/

/-- Execute a list of actions (ignoring guards). -/
def exec (var : Variant) : List (Action P C) → State P C → State P C
  | [], s => s
  | a :: as, s => exec var as (apply var a s)

/-- All guards along the list hold. -/
def runOK (var : Variant) (f : ℕ) (F : Finset P) : List (Action P C) → State P C → Bool
  | [], _ => true
  | a :: as, s => decide (Enabled var f F a s) && runOK var f F as (apply var a s)

theorem reach_exec (var : Variant) (f : ℕ) (F : Finset P) :
    ∀ (as : List (Action P C)) (s : State P C), runOK var f F as s = true →
      Relation.ReflTransGen (Step var f F) s (exec var as s)
  | [], _, _ => Relation.ReflTransGen.refl
  | a :: as, s, h => by
    simp only [runOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Relation.ReflTransGen.head ⟨a, h.1, rfl⟩ (reach_exec var f F as _ h.2)

theorem reachable_exec {var : Variant} {f : ℕ} {F : Finset P} {as : List (Action P C)}
    (h : runOK var f F as init = true) : Reachable var f F (exec var as init) :=
  reach_exec var f F as init h

end HotStuff.Chained
