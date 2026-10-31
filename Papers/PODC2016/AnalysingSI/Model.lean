import Papers.PODC2016.AnalysingSI.Relations

/-!
# Abstract executions and dependency graphs (Cerone–Gotsman, PODC 2016, §§2–3)

* Transactions (Definition 1) are lists of read/write operations in program order; `T ⊢ write(x,n)`
  (`Txn.Writes`), `T ⊢ read(x,n)` (`Txn.Reads`) and the internal consistency axiom INT
  (`Txn.Int`).
* Histories (Definition 2) `(𝒯, SO)` over a type `τ` of transaction identifiers.
* Abstract executions and pre-executions (Definitions 3, 11) and the consistency axioms of
  Figure 1; the sets `ExecSI`, `ExecSER`, `PreExecSI`, `ExecPSI`, `HistSI`, `HistSER`, `HistPSI`
  (Definitions 4, 11, 20).
* Dependencies of an execution (Definition 5), dependency graphs (Definition 6), and the sets
  `GraphSER`, `GraphSI`, `GraphPSI` (Theorems 8, 9, 21).
-/

namespace Podc.AnalysingSI

open Relation

/-- Operations `read(x, n)` and `write(x, n)` on objects `Obj` with values `V`. -/
inductive Op (Obj V : Type*) where
  | read (x : Obj) (n : V)
  | write (x : Obj) (n : V)
  deriving DecidableEq

variable {Obj V : Type*}

namespace Op

/-- The object an operation accesses. -/
def obj : Op Obj V → Obj
  | read x _ => x
  | write x _ => x

/-- The value an operation reads or writes. -/
def val : Op Obj V → V
  | read _ n => n
  | write _ n => n

/-- Whether an operation is a write. -/
def isWrite : Op Obj V → Bool
  | read _ _ => false
  | write _ _ => true

@[simp] lemma obj_read (x : Obj) (n : V) : (read x n).obj = x := rfl
@[simp] lemma obj_write (x : Obj) (n : V) : (write x n).obj = x := rfl
@[simp] lemma val_read (x : Obj) (n : V) : (read x n).val = n := rfl
@[simp] lemma val_write (x : Obj) (n : V) : (write x n).val = n := rfl
@[simp] lemma isWrite_read (x : Obj) (n : V) : (read x n).isWrite = false := rfl
@[simp] lemma isWrite_write (x : Obj) (n : V) : (write x n).isWrite = true := rfl

end Op

/-- A transaction (Definition 1): its operations listed in program order `po`. (Events are the
positions of the list, so the events of different transactions are automatically disjoint.) -/
abbrev Txn (Obj V : Type*) := List (Op Obj V)

namespace Txn

variable [DecidableEq Obj]

/-- `T ⊢ write(x, n)`: the last write of `T` to `x` writes `n`. -/
def Writes (T : Txn Obj V) (x : Obj) (n : V) : Prop :=
  (T.filter (fun o => o.isWrite && decide (o.obj = x))).getLast? = some (.write x n)

/-- `T ⊢ read(x, n)`: `T` reads `x` before writing it, and the first such read returns `n`
(the first operation of `T` on `x` is `read(x, n)`). -/
def Reads (T : Txn Obj V) (x : Obj) (n : V) : Prop :=
  T.find? (fun o => decide (o.obj = x)) = some (.read x n)

/-- The internal consistency axiom INT for one transaction: a read of `x` that is preceded in
program order by an operation on `x` returns the value of the last such operation. -/
def Int (T : Txn Obj V) : Prop :=
  ∀ (pre suf : Txn Obj V) (x : Obj) (n : V) (o : Op Obj V),
    T = pre ++ Op.read x n :: suf →
    (pre.filter (fun o => decide (o.obj = x))).getLast? = some o → o.val = n

end Txn

/-- A history `(𝒯, SO)` (Definition 2): `txn T` is the transaction with identifier `T : τ`
and `SO` is the session order. -/
structure History (τ Obj V : Type*) where
  /-- The transactions. -/
  txn : τ → Txn Obj V
  /-- The session order. -/
  SO : τ → τ → Prop

namespace History

variable [DecidableEq Obj] {τ : Type*} (H : History τ Obj V)

/-- `WriteTx_x`: the transactions that write to `x`. -/
def WriteTx (x : Obj) (T : τ) : Prop := ∃ n, (H.txn T).Writes x n

/-- `T ⊢ read(x, _)`. -/
def ReadsObj (x : Obj) (T : τ) : Prop := ∃ n, (H.txn T).Reads x n

/-- `𝒯 ⊨ INT`: every transaction is internally consistent. -/
def IntAll : Prop := ∀ T, (H.txn T).Int

end History

/-- An abstract execution `(𝒯, SO, VIS, CO)` (Definitions 3 and 11; the order-theoretic
conditions are the predicates `IsPreExecution` and `IsExecution`). -/
structure Execution (τ Obj V : Type*) extends History τ Obj V where
  /-- Visibility. -/
  VIS : τ → τ → Prop
  /-- Commit order. -/
  CO : τ → τ → Prop

namespace Execution

variable [DecidableEq Obj] {τ : Type*} (X : Execution τ Obj V)

/-- Pre-execution (Definition 11): `VIS ⊆ CO` and `CO` is a strict partial order. -/
def IsPreExecution : Prop :=
  X.VIS ≤ X.CO ∧ (∀ a b c, X.CO a b → X.CO b c → X.CO a c) ∧ ∀ a, ¬ X.CO a a

/-- Abstract execution (Definition 3): a pre-execution whose commit order is total. -/
def IsExecution : Prop :=
  X.IsPreExecution ∧ ∀ a b, a ≠ b → X.CO a b ∨ X.CO b a

/-- Axiom INT (Figure 1). -/
def Int : Prop := X.IntAll

/-- Axiom EXT (Figure 1): if `T ⊢ read(x, n)` then `max_CO(VIS⁻¹(T) ∩ WriteTx_x)` is defined and
writes `n` to `x`. -/
def Ext : Prop :=
  ∀ T x n, (X.txn T).Reads x n →
    ∃ M, IsMaxBy X.CO (fun S => X.VIS S T ∧ X.WriteTx x S) M ∧ (X.txn M).Writes x n

/-- Axiom SESSION: `SO ⊆ VIS`. -/
def Session : Prop := X.SO ≤ X.VIS

/-- Axiom PREFIX: `CO ; VIS ⊆ VIS`. -/
def Prefix : Prop := ∀ a b c, X.CO a b → X.VIS b c → X.VIS a c

/-- Axiom NOCONFLICT: distinct writers of the same object are related by `VIS`. -/
def NoConflict : Prop :=
  ∀ T S x, X.WriteTx x T → X.WriteTx x S → T ≠ S → X.VIS T S ∨ X.VIS S T

/-- Axiom TOTALVIS: `CO = VIS`. -/
def TotalVis : Prop := X.CO = X.VIS

/-- Axiom TRANSVIS: `VIS` is transitive. -/
def TransVis : Prop := ∀ a b c, X.VIS a b → X.VIS b c → X.VIS a c

/-- `X ∈ ExecSI` (Definition 4). -/
def IsSI : Prop :=
  X.IsExecution ∧ X.Int ∧ X.Ext ∧ X.Session ∧ X.Prefix ∧ X.NoConflict

/-- `X ∈ ExecSER` (Definition 4). -/
def IsSER : Prop :=
  X.IsExecution ∧ X.Int ∧ X.Ext ∧ X.Session ∧ X.TotalVis

/-- `P ∈ PreExecSI` (Definition 11). -/
def IsPreSI : Prop :=
  X.IsPreExecution ∧ X.Int ∧ X.Ext ∧ X.Session ∧ X.Prefix ∧ X.NoConflict

/-- `X ∈ ExecPSI` (Definition 20). -/
def IsPSI : Prop :=
  X.IsExecution ∧ X.Int ∧ X.Ext ∧ X.Session ∧ X.TransVis ∧ X.NoConflict

/-! ### Dependencies of an execution (Definition 5) -/

/-- Read dependency `T —WR_X(x)→ S`: `S ⊢ read(x, _)` and `T = max_CO(VIS⁻¹(S) ∩ WriteTx_x)`. -/
def WR (x : Obj) (T S : τ) : Prop :=
  X.ReadsObj x S ∧ IsMaxBy X.CO (fun U => X.VIS U S ∧ X.WriteTx x U) T

/-- Write dependency `T —WW_X(x)→ S`: `T —CO→ S` and both write `x`. -/
def WW (x : Obj) (T S : τ) : Prop :=
  X.CO T S ∧ X.WriteTx x T ∧ X.WriteTx x S

end Execution

/-- Anti-dependencies derived from read and write dependencies (Definition 5):
`T —RW(x)→ S ⟺ T ≠ S ∧ ∃ T', T' —WR(x)→ T ∧ T' —WW(x)→ S`. -/
def rwOf {τ : Type*} (WR WW : Obj → τ → τ → Prop) (x : Obj) (T S : τ) : Prop :=
  T ≠ S ∧ ∃ T', WR x T' T ∧ WW x T' S

/-- A tuple `(𝒯, SO, WR, WW, RW)`; `RW` is derived from `WR` and `WW` (`DepGraph.RW`). Whether it
is a dependency graph in the sense of Definition 6 is the predicate `DepGraph.IsDepGraph`. -/
structure DepGraph (τ Obj V : Type*) extends History τ Obj V where
  /-- Read dependencies. -/
  WR : Obj → τ → τ → Prop
  /-- Write dependencies. -/
  WW : Obj → τ → τ → Prop

namespace DepGraph

variable [DecidableEq Obj] {τ : Type*} (G : DepGraph τ Obj V)

/-- Anti-dependencies, derived as in Definition 5. -/
def RW : Obj → τ → τ → Prop := rwOf G.WR G.WW

/-- Definition 6: the conditions making `G` a dependency graph. -/
structure IsDepGraph : Prop where
  wr_val : ∀ T S x, G.WR x T S →
    ∃ n, T ≠ S ∧ (G.txn T).Writes x n ∧ (G.txn S).Reads x n
  wr_exists : ∀ S x, G.ReadsObj x S → ∃ T, G.WR x T S
  wr_unique : ∀ T T' S x, G.WR x T S → G.WR x T' S → T = T'
  ww_writeTx : ∀ x T S, G.WW x T S → G.WriteTx x T ∧ G.WriteTx x S
  ww_trans : ∀ x T S U, G.WW x T S → G.WW x S U → G.WW x T U
  ww_irrefl : ∀ x T, ¬ G.WW x T T
  ww_total : ∀ x T S, G.WriteTx x T → G.WriteTx x S → T ≠ S → G.WW x T S ∨ G.WW x S T

/-- `WR = ⋃ₓ WR(x)`. -/
def WRu (T S : τ) : Prop := ∃ x, G.WR x T S
/-- `WW = ⋃ₓ WW(x)`. -/
def WWu (T S : τ) : Prop := ∃ x, G.WW x T S
/-- `RW = ⋃ₓ RW(x)`. -/
def RWu (T S : τ) : Prop := ∃ x, G.RW x T S

/-- `SO ∪ WR ∪ WW`. -/
def B (T S : τ) : Prop := G.SO T S ∨ G.WRu T S ∨ G.WWu T S

/-- `G ∈ GraphSER` (Theorem 8): `𝒯 ⊨ INT` and `SO ∪ WR ∪ WW ∪ RW` is acyclic. -/
def IsSER : Prop :=
  G.IsDepGraph ∧ G.IntAll ∧ Acyclic (fun T S => G.B T S ∨ G.RWu T S)

/-- `G ∈ GraphSI` (Theorem 9): `𝒯 ⊨ INT` and `(SO ∪ WR ∪ WW) ; RW?` is acyclic. -/
def IsSI : Prop :=
  G.IsDepGraph ∧ G.IntAll ∧ Acyclic (Comp G.B (ReflGen G.RWu))

/-- `G ∈ GraphPSI` (Theorem 21): `𝒯 ⊨ INT` and `(SO ∪ WR ∪ WW)⁺ ; RW?` is irreflexive. -/
def IsPSI : Prop :=
  G.IsDepGraph ∧ G.IntAll ∧ ∀ T, ¬ Comp (TransGen G.B) (ReflGen G.RWu) T T

end DepGraph

namespace Execution

variable [DecidableEq Obj] {τ : Type*}

/-- `graph(X) = (𝒯, SO, WR_X, WW_X, RW_X)` (§3). -/
def graph (X : Execution τ Obj V) : DepGraph τ Obj V :=
  { toHistory := X.toHistory, WR := X.WR, WW := X.WW }

end Execution

variable [DecidableEq Obj] {τ : Type*}

/-- `HistSI` (Definition 4). -/
def HistSI : Set (History τ Obj V) :=
  {H | ∃ VIS CO, (Execution.mk H VIS CO).IsSI}

/-- `HistSER` (Definition 4). -/
def HistSER : Set (History τ Obj V) :=
  {H | ∃ VIS CO, (Execution.mk H VIS CO).IsSER}

/-- `HistPSI` (Definition 20, with the evident correction `ExecSI ↦ ExecPSI`). -/
def HistPSI : Set (History τ Obj V) :=
  {H | ∃ VIS CO, (Execution.mk H VIS CO).IsPSI}

end Podc.AnalysingSI
