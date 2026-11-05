import Papers.PODC2011.UnboundedConcurrency.Swap.Tree
import Podc.Computability.Distributed.SharedMemory.Arrival.Basic
import Cslib.Computability.Distributed.SharedMemory.Objects.FetchAdd
import Cslib.Computability.Distributed.SharedMemory.Objects.TestAndSet

/-!
# Algorithm 1 of Afek–Morrison–Wertheim (PODC 2011): unbounded-concurrency swap

The model is `Cslib.SharedMemory.Arrival`: asynchronous shared memory with infinitely many
processes `ℕ`, each a deterministic state machine whose every step is one atomic operation on one
base object (local computation is folded into the continuations). Every process performs exactly
**one** `swap(x p)` operation (in the unbounded-concurrency model of the paper every new invocation
is performed by a new process): its first step is the invocation, entering an output state
(`Act.out`) is the response. A schedule is a list (or sequence) of process ids; *unbounded
concurrency* means that every infinite schedule is admissible (`infArrival`).

Base objects (all atomic; the paper relies on [2], [10] for wait-free implementations of the
unbounded fetch-and-add and the unbounded snapshot from 2-consensus objects / registers, which we
do not formalize):

* `max_depth`: a fetch-and-add object over `ℕ`, initially `1` (`Obj.maxDepth`);
* `accessed`: an unbounded single-writer snapshot (`Obj.accessed`): cell `d` holds the last node
  posted by the process of depth `d` (`update_d(v)`), `scan` returns the whole array
  (a function `ℕ → Option Node`, `none` = never written);
* for every node `v` of the tree: an atomic register `v.reg` (`Obj.reg v`, values `Option V`,
  initially `none`) and a test-and-set object `v.tst` (`Obj.tst v`; the operation sets the bit and
  returns its old value, so the paper's `T&S` "wins" iff it returns `false`).

The local states follow the pseudocode line by line (`Loc`). The output is `Option V`
(`none` = `⊥`).
-/

namespace Podc.UnboundedConcurrency.Swap

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

/-- Operations of the unbounded snapshot object `accessed`. -/
inductive SnapOp where
  /-- `scan()`: returns the whole array. -/
  | scan
  /-- `update_d(v)`: writes `v` to cell `d`. -/
  | update (d : ℕ) (v : Node)

/-- The unbounded snapshot object: an array `ℕ → Option Node`; `update` returns the old array
(a dummy response). -/
abbrev snapObj : ObjSpec where
  State := ℕ → Option Node
  Op := SnapOp
  Resp := ℕ → Option Node
  init := fun _ => none
  δ s o := match o with
    | .scan => (s, s)
    | .update d v => (Function.update s d (some v), s)

/-- The base objects of Algorithm 1. -/
inductive Obj where
  /-- The fetch-and-add object `max_depth`. -/
  | maxDepth
  /-- The snapshot object `accessed`. -/
  | accessed
  /-- The register `v.reg` of node `v`. -/
  | reg (v : Node)
  /-- The test-and-set object `v.tst` of node `v`. -/
  | tst (v : Node)
  deriving DecidableEq

/-- Sequential specifications of the base objects (`V` = values of the swap object). -/
abbrev T (V : Type) : Obj → ObjSpec
  | .maxDepth => faaObj ℕ
  | .accessed => snapObj
  | .reg _ => register (Option V) none
  | .tst _ => tasObj

/-- Local states of a process; the comments give the line of Algorithm 1 the process is about to
execute. `x` is the input value, `d` the depth (`depth`), `c` the node `cap`, `m` the value
`maxdepth` read in Line 7, `r` the node `ret`. -/
inductive Loc (V : Type) where
  /-- Line 1: `depth := F&A(max_depth, 1)`. -/
  | start (x : V)
  /-- Line 2: `cap := NextUnaccessedNodeAtDepth(depth)` (`scan` of `accessed`); `prev` is the
  previous value of `cap` (`none` in the first iteration). If no node is found, the process scans
  again (it is stuck); Lemma 1 shows that this never happens. -/
  | scan (x : V) (d : ℕ) (prev : Option Node)
  /-- Line 3: `cap.reg := value`. -/
  | write (x : V) (d : ℕ) (c : Node)
  /-- Line 4: `win := T&S(cap.tst)`. -/
  | tas (x : V) (d : ℕ) (c : Node)
  /-- Line 5: `update_depth(accessed, cap)`; then Line 6 (`until win`). -/
  | upd (x : V) (d : ℕ) (c : Node) (win : Bool)
  /-- Line 7: `maxdepth := F&A(max_depth, 0)`, then Lines 8–10 (local). -/
  | readMax (d : ℕ) (c : Node)
  /-- Line 11: `T&S(ret.tst)`; on a win continue with Lines 9–10 (local). -/
  | retTas (d : ℕ) (c : Node) (m : ℕ) (r : Node)
  /-- Line 12: `return ret.reg`. -/
  | readReg (d : ℕ) (c : Node) (m : ℕ) (r : Node)
  /-- Returned `o`; `r` is the node `ret` the value was read from (`none` if `⊥` was returned). -/
  | done (d : ℕ) (c : Node) (m : ℕ) (r : Option Node) (o : Option V)

variable {V : Type}

/-- Lines 9–10 after `ret := GetPrevNodeMaxDepth(·, maxdepth)`: return `⊥` if there is no
previous node, otherwise try to return from it (Line 11). -/
def afterPrev (d : ℕ) (c : Node) (m : ℕ) : Option Node → Loc V
  | none => .done d c m none none
  | some r => .retTas d c m r

/-- The next action of a process (Algorithm 1). -/
noncomputable def act : Loc V → Act (T V) (Loc V) (Option V)
  | .start x => .access .maxDepth (1 : ℕ) fun d => .scan x d none
  | .scan x d p => .access .accessed .scan fun s =>
      match next d s with
      | some c => .write x d c
      | none => .scan x d p
  | .write x d c => .access (.reg c) (.write (some x)) fun _ => .tas x d c
  | .tas x d c => .access (.tst c) () fun b => .upd x d c (!b)
  | .upd x d c w => .access .accessed (.update d c) fun _ =>
      if w then .readMax d c else .scan x d (some c)
  | .readMax d c => .access .maxDepth (0 : ℕ) fun m => afterPrev d c m (prev c m)
  | .retTas d c m r => .access (.tst r) () fun b =>
      if b then .readReg d c m r else afterPrev d c m (prev r m)
  | .readReg d c m r => .access (.reg r) .read fun o => .done d c m (some r) o
  | .done _ _ _ _ o => .out o

/-- Algorithm 1: processes `ℕ`, input `x p : V` (the argument of `swap`), output `Option V`
(`none` = `⊥`). -/
noncomputable def alg (V : Type) : Alg (T V) ℕ V (Option V) where
  L := Loc V
  init _ x := .start x
  act := act
  mem₀ i := match i with
    | .maxDepth => (1 : ℕ)
    | .accessed => fun _ => none
    | .reg _ => none
    | .tst _ => false

/-- Configurations of Algorithm 1. -/
abbrev Config (V : Type) := Cfg (alg V)

namespace Cfg'

/-- The value of `max_depth`. -/
def D (C : Config V) : ℕ := C.mem .maxDepth
/-- The array of `accessed`. -/
def S (C : Config V) : ℕ → Option Node := C.mem .accessed
/-- The register `v.reg`. -/
def R (C : Config V) (v : Node) : Option V := C.mem (.reg v)
/-- The test-and-set bit of `v.tst`. -/
def B (C : Config V) (v : Node) : Bool := C.mem (.tst v)

end Cfg'

open Cfg'

/-! ### One step of each kind -/

section Steps

variable {C : Config V} {p : ℕ}

lemma step_start {x : V} (h : C.loc p = .start x) :
    (C.step p).loc p = (.scan x (D C) none) ∧
      (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧ D (C.step p) = D C + 1 ∧
      S (C.step p) = S C ∧ R (C.step p) = R C ∧ B (C.step p) = B C := by
  have hact : (alg V).act (C.loc p) = .access .maxDepth (1 : ℕ) fun d => .scan x d none := by
    rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨Function.update_self _ _ _, fun q hq => Function.update_of_ne hq _ _, ?_, ?_, ?_, ?_⟩
  · simp [D]
  · simp [S]
  · funext v; simp [R]
  · funext v; simp [B]

lemma step_scan {x : V} {d : ℕ} {pr : Option Node} (h : C.loc p = .scan x d pr) :
    (C.step p).loc p = (match next d (S C) with | some c => .write x d c | none => .scan x d pr) ∧
      (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧
      D (C.step p) = D C ∧ S (C.step p) = S C ∧ R (C.step p) = R C ∧ B (C.step p) = B C := by
  have hact : (alg V).act (C.loc p) = .access .accessed .scan fun s =>
      (match next d s with | some c => .write x d c | none => .scan x d pr) := by
    rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨Function.update_self _ _ _, fun q hq => Function.update_of_ne hq _ _, ?_, ?_, ?_, ?_⟩
  · simp [D]
  · simp [S]
  · funext v; simp [R]
  · funext v; simp [B]

lemma step_write {x : V} {d : ℕ} {c : Node} (h : C.loc p = .write x d c) :
    (C.step p).loc p = (.tas x d c) ∧
      (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧
      D (C.step p) = D C ∧ S (C.step p) = S C ∧
      R (C.step p) = Function.update (R C) c (some x) ∧ B (C.step p) = B C := by
  have hact : (alg V).act (C.loc p) = .access (.reg c) (.write (some x)) fun _ => .tas x d c := by
    rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨Function.update_self _ _ _, fun q hq => Function.update_of_ne hq _ _, ?_, ?_, ?_, ?_⟩
  · simp [D]
  · simp [S]
  · funext v
    by_cases hv : v = c
    · subst hv; simp [R]
    · simp [R, Function.update_of_ne hv,
        Function.update_of_ne (show (Obj.reg v : Obj) ≠ Obj.reg c by simpa using hv)]
  · funext v; simp [B]

lemma step_tas {x : V} {d : ℕ} {c : Node} (h : C.loc p = .tas x d c) :
    (C.step p).loc p = (.upd x d c (!B C c)) ∧
      (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧
      D (C.step p) = D C ∧ S (C.step p) = S C ∧ R (C.step p) = R C ∧
      B (C.step p) = Function.update (B C) c true := by
  have hact : (alg V).act (C.loc p) = .access (.tst c) () fun b => .upd x d c (!b) := by
    rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨Function.update_self _ _ _, fun q hq => Function.update_of_ne hq _ _, ?_, ?_, ?_, ?_⟩
  · simp [D]
  · simp [S]
  · funext v; simp [R]
  · funext v
    by_cases hv : v = c
    · subst hv; simp [B]
    · simp [B, Function.update_of_ne hv,
        Function.update_of_ne (show (Obj.tst v : Obj) ≠ Obj.tst c by simpa using hv)]

lemma step_upd {x : V} {d : ℕ} {c : Node} {w : Bool} (h : C.loc p = .upd x d c w) :
    (C.step p).loc p = (if w then .readMax d c else .scan x d (some c)) ∧
      (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧
      D (C.step p) = D C ∧ S (C.step p) = Function.update (S C) d (some c) ∧
      R (C.step p) = R C ∧ B (C.step p) = B C := by
  have hact : (alg V).act (C.loc p) = .access .accessed (.update d c) fun _ =>
      if w then .readMax d c else .scan x d (some c) := by
    rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨Function.update_self _ _ _, fun q hq => Function.update_of_ne hq _ _, ?_, ?_, ?_, ?_⟩
  · simp [D]
  · simp [S]
  · funext v; simp [R]
  · funext v; simp [B]

lemma step_readMax {d : ℕ} {c : Node} (h : C.loc p = .readMax d c) :
    (C.step p).loc p = (afterPrev d c (D C) (prev c (D C))) ∧
      (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧
      D (C.step p) = D C ∧ S (C.step p) = S C ∧ R (C.step p) = R C ∧ B (C.step p) = B C := by
  have hact : (alg V).act (C.loc p) = .access .maxDepth (0 : ℕ) fun m =>
      afterPrev d c m (prev c m) := by
    rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨Function.update_self _ _ _, fun q hq => Function.update_of_ne hq _ _, ?_, ?_, ?_, ?_⟩
  · simp [D]
  · simp [S]
  · funext v; simp [R]
  · funext v; simp [B]

lemma step_retTas {d : ℕ} {c : Node} {m : ℕ} {r : Node} (h : C.loc p = .retTas d c m r) :
    (C.step p).loc p = (if B C r then .readReg d c m r else afterPrev d c m (prev r m)) ∧
      (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧
      D (C.step p) = D C ∧ S (C.step p) = S C ∧ R (C.step p) = R C ∧
      B (C.step p) = Function.update (B C) r true := by
  have hact : (alg V).act (C.loc p) = .access (.tst r) () fun b =>
      if b then .readReg d c m r else afterPrev d c m (prev r m) := by
    rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨Function.update_self _ _ _, fun q hq => Function.update_of_ne hq _ _, ?_, ?_, ?_, ?_⟩
  · simp [D]
  · simp [S]
  · funext v; simp [R]
  · funext v
    by_cases hv : v = r
    · subst hv; simp [B]
    · simp [B, Function.update_of_ne hv,
        Function.update_of_ne (show (Obj.tst v : Obj) ≠ Obj.tst r by simpa using hv)]

lemma step_readReg {d : ℕ} {c : Node} {m : ℕ} {r : Node} (h : C.loc p = .readReg d c m r) :
    (C.step p).loc p = (.done d c m (some r) (R C r)) ∧
      (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧
      D (C.step p) = D C ∧ S (C.step p) = S C ∧ R (C.step p) = R C ∧ B (C.step p) = B C := by
  have hact : (alg V).act (C.loc p) = .access (.reg r) .read fun o => .done d c m (some r) o := by
    rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨Function.update_self _ _ _, fun q hq => Function.update_of_ne hq _ _, ?_, ?_, ?_, ?_⟩
  · simp [D]
  · simp [S]
  · funext v
    by_cases hv : v = r
    · subst hv; simp [R]
    · simp [R, Function.update_of_ne hv]
  · funext v; simp [B]

lemma step_done {d : ℕ} {c : Node} {m : ℕ} {r : Option Node} {o : Option V}
    (h : C.loc p = .done d c m r o) : C.step p = C :=
  Cfg.step_of_out (v := o) (by unfold Cfg.Out; rw [h]; rfl)

end Steps

end Podc.UnboundedConcurrency.Swap
