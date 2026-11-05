import Papers.PODC2012.LimitedUseSnapshots.SnapshotMain
import Cslib.Computability.Distributed.SharedMemory.Linearization
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# The linearization points of Section 4.1 are wrong

Section 4.1 of the paper linearizes an `Update` whose own root pointer is `d` (Line 16 at the
root) at "the first time any process performs `WriteMax(root.mr, ptr)` on Line 18 with
`ptr ≥ d`", and a `Scan` at its `ReadMax(root.mr)`. The proof then claims: "if there is no
`Update` operation by process `j` that is linearized before `op`, `count_j = 0` and
`v_j = leaf_j.view[0]`".

This fails: another process can propagate `j`'s new leaf pointer to the root with a *smaller*
root pointer than `j`'s own. Concretely (three processes, tree `((0, 1), 2)`):

1. process 0 starts `Update(5)`: writes its leaf, propagates to its parent `u`
   (`u.ma = (1, 0)`, `u.view[1]`), and performs `MaxUpdate₀(root.ma, 1)`;
2. process 1 performs a complete `Update(6)`: `u.ma = (1, 1)`, `u.view[2] = (5, 6)`,
   `root.ma = (2, 0)`, `root.view[2] = (5, 6, 0)`, `WriteMax(root.mr, 2)`;
3. process 2 starts `Update(7)` and performs `MaxUpdate₁(root.ma, 1)` (`root.ma = (2, 1)`);
4. process 0 scans `root.ma = (2, 1)`, so its own root pointer is `d = 3`, writes
   `root.view[3]` and is poised at `WriteMax(root.mr, 3)`;
5. process 1 performs a complete `Scan`: `ReadMax(root.mr) = 2`, returns `root.view[2]
   = (5, 6, 0)`.

No `WriteMax` with argument `≥ 3` has happened, so the paper linearizes the `Scan` before process
0's `Update`, yet the `Scan` returns process 0's new value `5`. Every linearization must order
process 0's `Update` before the `Scan` (`paper_linearization_points_fail`). The algorithm is
still linearizable (Theorem 4.2, `theorem_4_2`), with the corrected points of
`SnapshotInv.lean`: an `Update` is linearized as soon as `root.seq[root.mr]` covers its leaf
pointer.
-/

namespace Podc.LimitedUseSnapshots.Snapshot.Counterexample

open Cslib.SharedMemory

/-- The tree `((0, 1), 2)`. -/
abbrev Tex : BTree (Fin 3) := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)

/-- Initial values `0`. -/
abbrev vex : Fin 3 → ℕ := fun _ => 0

/-- The algorithm instance. -/
abbrev Iex := alg3 Tex vex

/-- The argument of a pending `WriteMax(root.mr, ·)`. -/
def wmArg {P V : Type} : PC P V → Option ℕ
  | .wm d => some d
  | _ => none

/-- The execution described in the module docstring. -/
def αex : List (Label (Fin 3) (swSnap (Fin 3) ℕ vex)) :=
  [.inv 0 (.update 0 5)] ++ List.replicate 7 (.tau 0) ++
  [.inv 1 (.update 1 6)] ++ List.replicate 12 (.tau 1) ++ [.ret 1 none] ++
  [.inv 2 (.update 2 7)] ++ List.replicate 2 (.tau 2) ++
  List.replicate 4 (.tau 0) ++
  [.inv 1 .scan] ++ List.replicate 2 (.tau 1) ++ [.ret 1 (some ![5, 6, 0])]

lemma crun_αex : (Iex.crun αex).map (fun C => (C.mem .mr, wmArg (C.loc 0).pc)) =
    some ((2 : ℕ), some 3) := by
  decide +kernel

lemma run_αex : ∃ C, Iex.run αex = some C ∧ C.mem .mr = 2 ∧ (C.loc 0).pc = .wm 3 := by
  have h := crun_αex
  rw [← Iex.run_eq_crun] at h
  cases hC : Iex.run αex with
  | none => rw [hC] at h; cases h
  | some C =>
    rw [hC] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    refine ⟨C, rfl, h.1, ?_⟩
    have h2 := h.2
    revert h2; generalize (C.loc 0).pc = pc
    cases pc <;> simp [wmArg]

lemma respOf_αex : respOf αex (1, 1) = some (some ![5, 6, 0]) := by decide +kernel

lemma opsOf_αex_0 : opsOf αex 0 = [.update 0 5] := by decide +kernel
lemma opsOf_αex_1 : opsOf αex 1 = [.update 1 6, .scan] := by decide +kernel
lemma opsOf_αex_2 : opsOf αex 2 = [.update 2 7] := by decide +kernel

lemma opOf_αex_11 : opOf αex (1, 1) = some .scan := by
  simp [opOf, opsOf_αex_1]

lemma eq_of_opOf_upd0 {x : OpId (Fin 3)} {v : ℕ} (h : opOf αex x = some (.update 0 v)) :
    x = (0, 0) := by
  obtain ⟨p, k⟩ := x
  simp only [opOf] at h
  fin_cases p
  · simp only [Fin.zero_eta, Fin.isValue] at h ⊢
    rw [opsOf_αex_0] at h
    match k, h with
    | 0, _ => rfl
  · simp only [Fin.mk_one, Fin.isValue] at h ⊢
    rw [opsOf_αex_1] at h
    match k, h with
    | 0, h => simp at h
    | 1, h => simp at h
  · simp only [Fin.reduceFinMk, Fin.isValue] at h ⊢
    rw [opsOf_αex_2] at h
    match k, h with
    | 0, h => simp at h

lemma runOps_comp0 (os : List (SOp (Fin 3) ℕ)) (hos : ∀ o ∈ os, ∀ v, o ≠ .update 0 v)
    (q : Fin 3 → ℕ) : (swSnap (Fin 3) ℕ vex).runOps q os 0 = q 0 := by
  induction os generalizing q with
  | nil => rfl
  | cons o os ih =>
    rw [ObjSpec.runOps_cons, ih (fun o' ho' => hos o' (List.mem_cons_of_mem _ ho'))]
    cases o with
    | scan => rfl
    | update i v =>
      have hi : i ≠ 0 := by rintro rfl; exact hos _ List.mem_cons_self v rfl
      simp [Function.update_of_ne (Ne.symm hi)]

/-- **The paper's linearization points are wrong** (Section 4.1). In the execution `αex`,
process 0's `Update(5)` has root pointer `d = 3` (it is poised at `WriteMax(root.mr, 3)`), while
`root.mr = 2`, so no `WriteMax(root.mr, ptr ≥ 3)` has occurred and the paper linearizes it after
the completed `Scan` `(1, 1)` (linearized at its `ReadMax(root.mr)` inside `αex`). But the `Scan`
returns `(5, 6, 0)`, and every linearization of `αex` must place `(0, 0)` before `(1, 1)`. -/
theorem paper_linearization_points_fail :
    ∃ C, Iex.run αex = some C ∧ C.mem .mr = 2 ∧ (C.loc 0).pc = .wm 3 ∧
      opOf αex (0, 0) = some (.update 0 5) ∧ opOf αex (1, 1) = some .scan ∧
      respOf αex (1, 1) = some (some ![5, 6, 0]) ∧
      ∀ L, IsLinearization αex L →
        [((0 : Fin 3), 0), ((1 : Fin 3), 1)].Sublist (L.map Prod.fst) := by
  obtain ⟨C, hC, hmr, hpc⟩ := run_αex
  refine ⟨C, hC, hmr, hpc, by simp [opOf, opsOf_αex_0], opOf_αex_11, respOf_αex, fun L hL => ?_⟩
  have hmem := hL.complete _ (Completed.of_respOf_eq_some respOf_αex)
  obtain ⟨⟨y, o⟩, hy, rfl⟩ := List.mem_map.1 hmem
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hy
  have ho : o = .scan := by
    have := hL.op_eq _ hy; rw [opOf_αex_11] at this; exact (Option.some.inj this).symm
  subst ho
  have hresp := hL.respIn_eq respOf_αex
  rw [ObjSpec.respIn_of_split hL.nodup hsplit] at hresp
  have hst : (swSnap (Fin 3) ℕ vex).runOps vex (L₁.map Prod.snd) 0 = 5 := by
    simp only [swSnap, Option.some.injEq] at hresp
    rw [hresp]; rfl
  have h0 : ((0 : Fin 3), 0) ∈ L₁.map Prod.fst := by
    by_contra h0
    refine absurd hst ?_
    rw [runOps_comp0]
    · decide
    · intro o' ho' v he
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ho'
      have hzL : z ∈ L := by rw [hsplit]; exact List.mem_append_left _ hz
      have := hL.op_eq z hzL
      rw [he] at this
      exact h0 (List.mem_map.2 ⟨z, hz, eq_of_opOf_upd0 this⟩)
  exact sublist_pair_iff.2 ⟨L₁.map Prod.fst, ((((1 : Fin 3), 1), SOp.scan) :: L₂).map Prod.fst,
    by rw [hsplit, List.map_append], h0, by simp⟩

end Podc.LimitedUseSnapshots.Snapshot.Counterexample
