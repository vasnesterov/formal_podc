import Papers.PODC2015.HelpFreeWaitFree.Theorem48

/-!
# Theorem 4.7: snapshots

The snapshot object with components indexed by `K` (`update k v` writes `v` into component `k`,
`scan` returns all components) is a strong global view type (`snapshot_strongGlobalView`), with
the witnesses of the paper's proof of Theorem 4.7: `op = update k₁ 0`, the modifiers alternate
`update k₂ 0`, `update k₂ 1`, … and the views are scans.

Hence (`theorem_4_7`) there is no wait-free help-free linearizable snapshot implementation from
read/write/cas registers for three processes. The paper states Theorem 4.7 for the
*single-scanner* single-writer snapshot; our implementations must be correct for all executions
(any process may invoke any operation), so this is the theorem for (multi-writer,
multi-scanner) snapshot implementations.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

/-- Operations of a snapshot object with components `K` and values `V`. -/
inductive SnapOp (K V : Type) where
  | update (k : K) (v : V)
  | scan

/-- The snapshot object: `update k v` writes `v` into component `k` (response `none`), `scan`
returns the vector of all components (`none` = never written). -/
abbrev snapshotSpec (K V : Type) [DecidableEq K] : ObjSpec where
  State := K → Option V
  Op := SnapOp K V
  Resp := Option (K → Option V)
  init := fun _ => none
  δ q o := match o with
    | .update k v => (Function.update q k (some v), none)
    | .scan => (q, some q)

section Snapshot

variable {K : Type} [DecidableEq K] (k₁ k₂ : K)

/-- The witnesses: `op = update k₁ true`, modifiers alternate `update k₂ true/false`, views are
scans. -/
def snapOp : SnapOp K Bool := .update k₁ true
/-- The modifiers. -/
def snapMod (n : ℕ) : SnapOp K Bool := .update k₂ (decide (n % 2 = 0))

/-- The snapshot state after a tagged history. -/
def snapState (y : List GVTag) : K → Option Bool := fun k =>
  if k = k₁ then (if y.filter GVTag.isOp = [] then none else some true)
  else if k = k₂ then
    (match (y.filter GVTag.isMod).getLast? with
      | some (GVTag.mod n) => some (decide (n % 2 = 0))
      | _ => none)
  else none

lemma snap_runOps (h12 : k₁ ≠ k₂) (y : List GVTag) :
    (snapshotSpec K Bool).runOps (snapshotSpec K Bool).init
      (y.map (GVTag.toOp (snapOp k₁) (snapMod k₂) (fun _ => .scan))) = snapState k₁ k₂ y := by
  have key : ∀ q o, (snapshotSpec K Bool).runOps q [o] = ((snapshotSpec K Bool).δ q o).1 :=
    fun _ _ => rfl
  induction y using List.reverseRecOn with
  | nil => funext k; show (none : Option Bool) = _; simp [snapState]
  | append_singleton y t ih =>
    rw [List.map_append, ObjSpec.runOps_append, ih, List.map_singleton, key]
    funext k
    cases t with
    | op =>
      show Function.update (snapState k₁ k₂ y) k₁ (some true) k = _
      by_cases hk : k = k₁
      · subst hk; simp [snapState]
      · rw [Function.update_of_ne hk]; simp [snapState, hk, List.filter_append]
    | mod n =>
      show Function.update (snapState k₁ k₂ y) k₂ (some (decide (n % 2 = 0))) k = _
      by_cases hk : k = k₂
      · subst hk; simp [snapState, Ne.symm h12, List.filter_append]
      · rw [Function.update_of_ne hk]; simp [snapState, hk, List.filter_append]
    | view n =>
      show snapState k₁ k₂ y k = _
      simp [snapState, List.filter_append]

lemma getLast?_map_mod_range (N : ℕ) :
    ((List.range N).map GVTag.mod).getLast? = if N = 0 then none else some (GVTag.mod (N - 1)) := by
  cases N with
  | zero => simp
  | succ N => simp [List.range_succ, List.getLast?_append]

/-- The results of the sets `gvSet i j o m` for the snapshot. -/
lemma snap_gvRes (h12 : k₁ ≠ k₂) {i j : ℕ} {o m : Bool} {r : Option (K → Option Bool)}
    (hr : r ∈ gvRes (A := snapshotSpec K Bool) (snapOp k₁) (snapMod k₂) (fun _ => .scan) i j o m) :
    r = some (fun k => if k = k₁ then (if o then some true else none)
      else if k = k₂ then (if i + m.toNat = 0 then none else some (decide ((i + m.toNat - 1) % 2 = 0)))
      else none) := by
  obtain ⟨x, ⟨h1, -, h3, n, h4⟩, hx⟩ := hr
  obtain ⟨y, rfl⟩ : ∃ y, x = y ++ [GVTag.view n] := by
    rw [List.getLast?_eq_some_iff] at h4; exact h4
  have h1' : y.filter GVTag.isMod = (List.range (i + m.toNat)).map GVTag.mod := by
    simpa [List.filter_append] using h1
  have h3' : y.filter GVTag.isOp = (if o then [GVTag.op] else []) := by
    simpa [List.filter_append] using h3
  rw [List.map_append, List.map_singleton, lastResult_append_singleton, snap_runOps k₁ k₂ h12] at hx
  simp only [GVTag.toOp, Option.some.injEq] at hx
  rw [← hx]
  congr 1
  funext k
  by_cases hk1 : k = k₁
  · subst hk1; cases o <;> simp [snapState, h3']
  · by_cases hk2 : k = k₂
    · subst hk2
      simp only [snapState, hk1, ↓reduceIte, h1', getLast?_map_mod_range]
      by_cases hN : i + m.toNat = 0
      · simp only [hN, ↓reduceIte]
      · simp only [hN, ↓reduceIte]
    · simp [snapState, hk1, hk2]

/-- **The snapshot is a strong global view type** (the property behind Theorem 4.7). -/
theorem snapshot_strongGlobalView (h12 : k₁ ≠ k₂) : StrongGlobalView (snapshotSpec K Bool) := by
  refine ⟨snapOp k₁, snapMod k₂, fun _ => .scan, fun i j _ o m o' m' hne => ?_⟩
  rw [Set.disjoint_left]
  intro r hr hr'
  have e := (snap_gvRes k₁ k₂ h12 hr).symm.trans (snap_gvRes k₁ k₂ h12 hr')
  simp only [Option.some.injEq] at e
  have e1 := congrFun e k₁
  have e2 := congrFun e k₂
  simp only [↓reduceIte, Ne.symm h12] at e1 e2
  apply hne
  have ho : o = o' := by cases o <;> cases o' <;> simp at e1 ⊢
  subst ho
  have hm : m = m' := by
    by_contra hmm
    cases m <;> cases m' <;> simp at hmm <;>
      rcases Nat.eq_zero_or_pos i with rfl | hi <;> simp at e2 <;>
      simp [show i ≠ 0 by omega] at e2 <;>
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h] at e2 <;> omega
  rw [hm]

end Snapshot

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {P L : Type} [DecidableEq P]
variable {V : ι → Type} [∀ i, DecidableEq (V i)] {v₀ : ∀ i, V i}

/-- **Theorem 4.7** of [CPT15] (for snapshot implementations correct in all executions): a wait-free
linearizable snapshot implementation from read/write/cas registers, with at least three
processes and two components, cannot be help-free (not even weakly). -/
theorem theorem_4_7 {K : Type} [DecidableEq K] (k₁ k₂ : K) (hk : k₁ ≠ k₂)
    (I : Impl (snapshotSpec K Bool) (fun i => casObject (V i) (v₀ i)) P L)
    (p₁ p₂ p₃ : P) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hall : ∀ p o, I.allowed p o) (hwf : I.WaitFree) : ¬ WeaklyHelpFree I :=
  theorem_4_8 I (snapshot_strongGlobalView k₁ k₂ hk) p₁ p₂ p₃ h12 h13 h23 hall hwf

end Podc.HelpFreeWaitFree
