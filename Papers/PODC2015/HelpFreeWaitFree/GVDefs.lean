import Papers.PODC2015.HelpFreeWaitFree.Defs

/-!
# Global view types (Definitions 4.6.16–4.6.18 of [CPT15])

A global view type has an operation `op`, an infinite sequence of operations `Modifiers` (`M`)
and an infinite sequence of operations `Views` (`V`) such that the result of a view tells how
many of `op` and the next modifier precede it.

Sequential histories over these operations are lists of *tags* (`GVTag`): `op`, `mod k` (the
`k`-th modifier, 0-based, i.e. the paper's `(k+1)`-st) and `view k`. A tag list `x` denotes the
sequence of operations `x.map (GVTag.toOp op M V)`. Tags are needed because the operations
themselves may coincide (for fetch&increment all of them are the same operation).

* `gvSet i j o m` — **Definition 4.6.16**: the histories consisting of the first `i` modifiers
  (and also the `(i+1)`-st if `m`), in their relative order, the first `j` views in their relative
  order, `op` iff `o`, and nothing else, whose last operation is a view. The paper's sets are
  `Set0 = gvSet i j false false`, `Set1 = gvSet i j true false ∪ gvSet i j false true`,
  `Set2 = gvSet i j true true`.
* `gvRes op M V i j o m` — the results of the last (view) operation of the histories in
  `gvSet i j o m`; **Definition 4.6.17**: `RS0`, `RS1`, `RS2`.
* `GlobalView A` — **Definition 4.6.18**: for all `i ≥ 0`, `j ≥ 1`, the sets `RS0`, `RS1`, `RS2`
  are pairwise disjoint.
* `StrongGlobalView A` — the four result sets `gvRes i j o m` (`o m : Bool`) are pairwise
  disjoint: a view also tells *which* of `op` and the next modifier precede it when exactly one
  does. This is what the paper's proof of Claim 4.6.8 actually uses (see `differencies.md`); it
  holds for snapshots (Theorem 4.7) but not for fetch&increment.

Examples: fetch&increment is a global view type (`fetchInc_globalView`) but not a strong one
(`fetchInc_not_strongGlobalView`); a snapshot object with two components is a strong global view
type (`snapshot_strongGlobalView` in `GVSnapshot.lean`).
-/

set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

/-- Names of the operations in modifier–view histories: `op`, the `k`-th modifier, the `k`-th
view (0-based). -/
inductive GVTag where
  | op
  | mod (k : ℕ)
  | view (k : ℕ)
  deriving DecidableEq

namespace GVTag

/-- The tag is `op`. -/
def isOp : GVTag → Bool
  | op => true
  | _ => false

/-- The tag is a modifier. -/
def isMod : GVTag → Bool
  | mod _ => true
  | _ => false

/-- The tag is a view. -/
def isView : GVTag → Bool
  | view _ => true
  | _ => false

/-- The operation named by a tag. -/
def toOp {A : ObjSpec} (o : A.Op) (M V : ℕ → A.Op) : GVTag → A.Op
  | op => o
  | mod k => M k
  | view k => V k

@[simp] lemma isOp_op : isOp op = true := rfl
@[simp] lemma isOp_mod (k : ℕ) : isOp (mod k) = false := rfl
@[simp] lemma isOp_view (k : ℕ) : isOp (view k) = false := rfl
@[simp] lemma isMod_op : isMod op = false := rfl
@[simp] lemma isMod_mod (k : ℕ) : isMod (mod k) = true := rfl
@[simp] lemma isMod_view (k : ℕ) : isMod (view k) = false := rfl
@[simp] lemma isView_op : isView op = false := rfl
@[simp] lemma isView_mod (k : ℕ) : isView (mod k) = false := rfl
@[simp] lemma isView_view (k : ℕ) : isView (view k) = true := rfl

/-- Every list of tags is made of its `op`s, modifiers and views. -/
lemma length_eq_filter (x : List GVTag) :
    x.length = (x.filter isOp).length + (x.filter isMod).length + (x.filter isView).length := by
  induction x with
  | nil => rfl
  | cons t x ih => cases t <;> simp [List.filter_cons, ih] <;> omega

end GVTag

/-- The result of the last operation of a sequential history, executed from the initial state
(`none` for the empty history). -/
def lastResult (A : ObjSpec) (os : List A.Op) : Option A.Resp :=
  os.getLast?.map fun o => (A.δ (A.runOps A.init os.dropLast) o).2

/-- **Definition 4.6.16** (modifiers–views sets). The sequential histories that contain the first
`i` modifiers, and also the `(i+1)`-st one if `m`, in their relative order, the first `j` views in
their relative order, `op` iff `o`, no other operation, and end with a view. -/
def gvSet (i j : ℕ) (o m : Bool) : Set (List GVTag) :=
  {x | x.filter GVTag.isMod = (List.range (i + m.toNat)).map GVTag.mod ∧
    x.filter GVTag.isView = (List.range j).map GVTag.view ∧
    x.filter GVTag.isOp = (if o then [GVTag.op] else []) ∧
    ∃ k, x.getLast? = some (GVTag.view k)}

variable {A : ObjSpec}

/-- The results of the last (view) operation of the histories of `gvSet i j o m`. -/
def gvRes (op : A.Op) (M V : ℕ → A.Op) (i j : ℕ) (o m : Bool) : Set A.Resp :=
  {r | ∃ x ∈ gvSet i j o m, lastResult A (x.map (GVTag.toOp op M V)) = some r}

/-- **Definition 4.6.17**: `RS0` (neither `op` nor the `(i+1)`-st modifier). -/
def RS0 (op : A.Op) (M V : ℕ → A.Op) (i j : ℕ) : Set A.Resp := gvRes op M V i j false false

/-- **Definition 4.6.17**: `RS1` (exactly one of `op` and the `(i+1)`-st modifier). -/
def RS1 (op : A.Op) (M V : ℕ → A.Op) (i j : ℕ) : Set A.Resp :=
  gvRes op M V i j true false ∪ gvRes op M V i j false true

/-- **Definition 4.6.17**: `RS2` (both `op` and the `(i+1)`-st modifier). -/
def RS2 (op : A.Op) (M V : ℕ → A.Op) (i j : ℕ) : Set A.Resp := gvRes op M V i j true true

/-- **Definition 4.6.18** (global view types): there are `op`, `Modifiers` and `Views` such that
for all `i ≥ 0` and `j ≥ 1` the result sets `RS0`, `RS1`, `RS2` are pairwise disjoint. -/
def GlobalView (A : ObjSpec) : Prop :=
  ∃ (op : A.Op) (M V : ℕ → A.Op), ∀ i j, 1 ≤ j →
    Disjoint (RS0 op M V i j) (RS1 op M V i j) ∧ Disjoint (RS0 op M V i j) (RS2 op M V i j) ∧
      Disjoint (RS1 op M V i j) (RS2 op M V i j)

/-- Strong global view types: the four result sets (according to which of `op` and the
`(i+1)`-st modifier occur) are pairwise disjoint, i.e. in `RS1` a view also tells which one of
the two occurred. -/
def StrongGlobalView (A : ObjSpec) : Prop :=
  ∃ (op : A.Op) (M V : ℕ → A.Op), ∀ i j, 1 ≤ j → ∀ o m o' m' : Bool, (o, m) ≠ (o', m') →
    Disjoint (gvRes op M V i j o m) (gvRes op M V i j o' m')

/-- A strong global view type is a global view type. -/
lemma StrongGlobalView.globalView (h : StrongGlobalView A) : GlobalView A := by
  obtain ⟨op, M, V, h⟩ := h
  refine ⟨op, M, V, fun i j hj => ⟨?_, h i j hj _ _ _ _ (by simp), ?_⟩⟩
  · exact Disjoint.union_right (h i j hj _ _ _ _ (by simp)) (h i j hj _ _ _ _ (by simp))
  · exact Disjoint.union_left (h i j hj _ _ _ _ (by simp)) (h i j hj _ _ _ _ (by simp))

/-! ### Fetch&increment -/

/-- The fetch&increment object: a single operation that returns the current value of a counter
(initially `0`) and increments it. -/
abbrev fetchIncSpec : ObjSpec where
  State := ℕ
  Op := Unit
  Resp := ℕ
  init := 0
  δ q _ := (q + 1, q)

lemma fetchInc_runOps (q : ℕ) (os : List Unit) : fetchIncSpec.runOps q os = q + os.length := by
  induction os generalizing q with
  | nil => rfl
  | cons o os ih =>
    have e : fetchIncSpec.runOps q (o :: os) = fetchIncSpec.runOps (q + 1) os := rfl
    rw [e, ih, List.length_cons]
    show (q + 1 + os.length : ℕ) = q + (os.length + 1); omega

lemma fetchInc_lastResult {os : List Unit} (h : os ≠ []) :
    lastResult fetchIncSpec os = some (os.length - 1) := by
  obtain ⟨o, hos⟩ := List.getLast?_isSome.2 h |> Option.isSome_iff_exists.1
  simp only [lastResult, hos, Option.map_some, fetchInc_runOps, List.length_dropLast]
  simp

/-- In the fetch&increment type, every result of `gvRes i j o m` is `i + j + o + m - 1`. -/
lemma fetchInc_gvRes {i j : ℕ} {o m : Bool} {r : ℕ} (hr : r ∈ gvRes (A := fetchIncSpec) () (fun _ => ())
    (fun _ => ()) i j o m) : r = i + m.toNat + j + o.toNat - 1 := by
  obtain ⟨x, ⟨h1, h2, h3, k, h4⟩, hx⟩ := hr
  have hne : x.map (GVTag.toOp (A := fetchIncSpec) () (fun _ => ()) (fun _ => ())) ≠ [] := by
    intro he; simp only [List.map_eq_nil_iff] at he; simp [he] at h4
  rw [fetchInc_lastResult hne] at hx
  have hl := GVTag.length_eq_filter x
  rw [h1, h2, h3] at hl
  cases o <;> simp at hl hx ⊢ <;> omega

/-- The fetch&increment type is a global view type (with `op`, the modifiers and the views all
fetch&increment, as in the paper): the results of `RS0`, `RS1`, `RS2` count `i + j`, `i + j + 1`,
`i + j + 2` operations. -/
theorem fetchInc_globalView : GlobalView fetchIncSpec := by
  refine ⟨(), fun _ => (), fun _ => (), fun i j hj => ⟨?_, ?_, ?_⟩⟩ <;>
    rw [Set.disjoint_left] <;> intro r hr₁ hr₂ <;>
    simp only [RS0, RS1, RS2, Set.mem_union] at hr₁ hr₂
  · rcases hr₂ with hr₂ | hr₂ <;>
      have e1 := fetchInc_gvRes hr₁ <;> have e2 := fetchInc_gvRes hr₂ <;> simp at e1 e2 <;> omega
  · have e1 := fetchInc_gvRes hr₁; have e2 := fetchInc_gvRes hr₂; simp at e1 e2; omega
  · rcases hr₁ with hr₁ | hr₁ <;>
      have e1 := fetchInc_gvRes hr₁ <;> have e2 := fetchInc_gvRes hr₂ <;> simp at e1 e2 <;> omega

/-- Fetch&increment is not a strong global view type: a view cannot tell `op` from a modifier. -/
theorem fetchInc_not_strongGlobalView : ¬ StrongGlobalView fetchIncSpec := by
  rintro ⟨op, M, V, h⟩
  have hd := h 0 1 le_rfl true false false true (by simp)
  rw [Set.disjoint_left] at hd
  refine hd (a := 1) ⟨[GVTag.op, GVTag.view 0], ⟨rfl, rfl, rfl, 0, rfl⟩, ?_⟩
    ⟨[GVTag.mod 0, GVTag.view 0], ⟨rfl, rfl, rfl, 0, rfl⟩, ?_⟩ <;>
  simp [lastResult, GVTag.toOp, fetchInc_runOps]

end Podc.HelpFreeWaitFree
