import Papers.PODC2012.LimitedUseSnapshots.Algorithm
import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# Algorithm 2 as published is not linearizable (Theorem 3.4 is false)

The authors' erratum gives the following execution; we check it for `k = 3` (the balanced tree,
`m = ⌈3/2⌉ = 2`), any `h ≥ 2` (we use the value `1` in the second component) and three processes:

1. `p₀` invokes `MaxScan`, reads `r.second = 0` (line 11) and `r.switch = 0` (line 12);
2. `p₁` performs a complete `MaxUpdate1(r, 1)`;
3. `p₂` performs a complete `MaxUpdate0(r, 1)` (it reads `r.switch = 0`, goes left, and sets the
   switch of the left child to `1`);
4. `p₀` finishes: it writes `0` to `r.left.second`, follows the left child's switch to the right
   and returns `(1, 0)`.

`MaxUpdate1(r, 1)` finished before `MaxUpdate0(r, 1)` started, so any linearization that lets the
scan see the first component `1` must also let it see the second component `1`.
-/

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

/-! ### Linearizations of max-array histories -/

section Necessary

variable {P : Type} [DecidableEq P]

lemma maxArr_runOps_fst_le (q : ℕ × ℕ) (os : List MAOp) : q.1 ≤ (maxArrObj.runOps q os).1 := by
  induction os generalizing q with
  | nil => exact le_rfl
  | cons o os ih =>
    rw [ObjSpec.runOps_cons]
    refine le_trans ?_ (ih _)
    cases o <;> simp

lemma maxArr_runOps_snd_le (q : ℕ × ℕ) (os : List MAOp) : q.2 ≤ (maxArrObj.runOps q os).2 := by
  induction os generalizing q with
  | nil => exact le_rfl
  | cons o os ih =>
    rw [ObjSpec.runOps_cons]
    refine le_trans ?_ (ih _)
    cases o <;> simp

lemma maxArr_runOps_snd_ge_of_mem (q : ℕ × ℕ) {os : List MAOp} {v : ℕ} (h : MAOp.upd1 v ∈ os) :
    v ≤ (maxArrObj.runOps q os).2 := by
  induction os generalizing q with
  | nil => simp at h
  | cons o os ih =>
    rw [ObjSpec.runOps_cons]
    rcases List.mem_cons.1 h with rfl | h
    · refine le_trans ?_ (maxArr_runOps_snd_le _ _); simp
    · exact ih _ h

lemma maxArr_runOps_fst_eq_of_forall (q : ℕ × ℕ) {os : List MAOp}
    (h : ∀ v, MAOp.upd0 v ∉ os) : (maxArrObj.runOps q os).1 = q.1 := by
  induction os generalizing q with
  | nil => rfl
  | cons o os ih =>
    rw [ObjSpec.runOps_cons]
    rw [ih _ (fun v hv => h v (List.mem_cons_of_mem _ hv))]
    cases o with
    | upd0 v => exact absurd (List.mem_cons_self) (h v)
    | upd1 v => simp
    | scan => simp

/-- In a linearization, a scan returns the state reached by the operations before it. -/
lemma scan_resp_of_lin {α : List (Label P maxArrObj)} {L : List (OpId P × MAOp)}
    (hL : IsLinearization α L) {x : OpId P} {r : ℕ × ℕ} (hx : (x, MAOp.scan) ∈ L)
    (hr : respOf α x = some r) :
    ∃ L₁ L₂, L = L₁ ++ (x, MAOp.scan) :: L₂ ∧ maxArrObj.runOps (0, 0) (L₁.map Prod.snd) = r := by
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hx
  refine ⟨L₁, L₂, rfl, ?_⟩
  have := ((seqOK_append (α := α) maxArrObj.init L₁ _).1 hL.seq).2
  simp only [SeqOK] at this
  simpa using this.1 r hr

/-- In a duplicate-free list `A ++ B`, an element that precedes an element of `A` is in `A`. -/
lemma mem_left_of_sublist_pair' {X : Type} {a b : X} {A B : List X} (hl : (A ++ B).Nodup)
    (h : [a, b].Sublist (A ++ B)) (hb : b ∈ A) : a ∈ A := by
  obtain ⟨r₁, r₂, hs, ha, hb'⟩ := sublist_pair_iff.1 h
  rcases List.append_eq_append_iff.1 hs.symm with ⟨c, rfl, rfl⟩ | ⟨c, rfl, rfl⟩
  · exact List.mem_append_left _ ha
  · exfalso
    rw [List.nodup_append] at hl
    exact hl.2.2 b hb b (List.mem_append_right _ hb') rfl

end Necessary

/-! ### The execution -/

/-- The tree of `MaxArray_{3×h}`: `m = 2`, the left child has `m = 1`. -/
abbrev T3 : Shape := .node (.node .leaf .leaf) .leaf

/-- `T3` is the paper's balanced tree for `k = 3` (`m = ⌈3/2⌉`). -/
lemma balanced_three : Shape.balanced 3 = T3 := by
  rw [Shape.balanced, Shape.balanced, Shape.balanced, Shape.balanced]

instance (P : Type) (T : Shape) (fix : Bool) (p : P) (o : MAOp) :
    Decidable ((alg P T fix).allowed p o) := by
  cases o <;> simp only [alg] <;> infer_instance

/-- The erratum's execution (processes `0, 1, 2` play `p₁, p₂, p₃`). -/
def badExec : List (Label (Fin 3) maxArrObj) :=
  [.inv 0 .scan, .tau 0, .tau 0,
   .inv 1 (.upd1 1), .tau 1, .ret 1 (0, 0),
   .inv 2 (.upd0 1), .tau 2, .tau 2, .ret 2 (0, 0),
   .tau 0, .tau 0, .tau 0, .tau 0, .tau 0, .tau 0, .ret 0 (1, 0)]

lemma badExec_valid : (alg (Fin 3) T3 false).Valid badExec := by
  apply Impl.valid_of_crun
  decide

lemma opsOf_badExec : opsOf badExec 0 = [.scan] ∧ opsOf badExec 1 = [.upd1 1] ∧
    opsOf badExec 2 = [.upd0 1] := by decide

lemma respsOf_badExec : respsOf badExec 0 = [(1, 0)] ∧ respsOf badExec 1 = [(0, 0)] ∧
    respsOf badExec 2 = [(0, 0)] := by decide

lemma opOf_badExec (y : OpId (Fin 3)) :
    opOf badExec y = if y = (0, 0) then some .scan else if y = (1, 0) then some (.upd1 1)
      else if y = (2, 0) then some (.upd0 1) else none := by
  obtain ⟨p, k⟩ := y
  obtain ⟨h0, h1, h2⟩ := opsOf_badExec
  fin_cases p <;> rcases k with _ | k <;> simp [opOf, h0, h1, h2]

/-- **Theorem 3.4 is false**: Algorithm 2 (as published, without the erratum's line 9.5) is not
linearizable, already for `k = 3` with the balanced tree and three processes. -/
theorem alg2_not_linearizable : ¬ (alg (Fin 3) T3 false).Linearizable := by
  rintro ⟨h, hh⟩
  have hL := hh _ badExec_valid
  set L := h badExec
  -- the scan `(0,0)` returned `(1,0)`
  have hc0 : Completed badExec ((0 : Fin 3), 0) := by simp [Completed, respsOf_badExec.1]
  have hc1 : Completed badExec ((1 : Fin 3), 0) := by simp [Completed, respsOf_badExec.2.1]
  have hc2 : Completed badExec ((2 : Fin 3), 0) := by simp [Completed, respsOf_badExec.2.2]
  have hmem : ∀ y : OpId (Fin 3), y ∈ L.map Prod.fst → ∀ o, (y, o) ∈ L → opOf badExec y = some o :=
    fun y _ o hy => hL.op_eq _ hy
  have hx : ((0 : Fin 3), 0) ∈ L.map Prod.fst := hL.complete _ hc0
  obtain ⟨⟨x', o'⟩, hx', hxeq⟩ := List.mem_map.1 hx
  simp only at hxeq; subst hxeq
  have ho' : o' = .scan := by
    have := hL.op_eq _ hx'; rw [opOf_badExec] at this; simpa [eq_comm] using this
  subst ho'
  have hr : respOf badExec ((0 : Fin 3), 0) = some (1, 0) := by
    simp [respOf, respsOf_badExec.1]
  obtain ⟨L₁, L₂, hLsplit, hstate⟩ := scan_resp_of_lin hL hx' hr
  -- some `MaxUpdate0` is before the scan: it must be `(2,0)`
  have h2 : ((2 : Fin 3), 0) ∈ L₁.map Prod.fst := by
    by_contra hn
    have hno : ∀ v, MAOp.upd0 v ∉ L₁.map Prod.snd := by
      intro v hv
      obtain ⟨⟨y, o⟩, hy, rfl⟩ := List.mem_map.1 hv
      have hyL : (y, MAOp.upd0 v) ∈ L := by rw [hLsplit]; exact List.mem_append_left _ hy
      have := hL.op_eq _ hyL
      rw [opOf_badExec] at this
      simp only at this
      split_ifs at this with h1 h2 h3 <;> simp at this
      subst h3; exact hn (List.mem_map.2 ⟨_, hy, rfl⟩)
    have := maxArr_runOps_fst_eq_of_forall (0, 0) hno
    rw [hstate] at this; simp at this
  -- `(1,0)` precedes `(2,0)` in real time, so it is before the scan too
  have hprec : Precedes badExec ((1 : Fin 3), 0) ((2 : Fin 3), 0) := by
    refine ⟨[.inv 0 .scan, .tau 0, .tau 0, .inv 1 (.upd1 1), .tau 1, .ret 1 (0, 0)], _, rfl,
      ?_, ?_⟩ <;> simp [Completed, Invoked, respsOf, opsOf]
  have hsub := hL.realtime _ _ hprec (hL.complete _ hc2)
  have hnd := hL.nodup
  rw [hLsplit, List.map_append] at hsub hnd
  have h1 := mem_left_of_sublist_pair' hnd hsub h2
  obtain ⟨⟨y, o⟩, hy, hyeq⟩ := List.mem_map.1 h1
  simp only at hyeq; subst hyeq
  have ho : o = .upd1 1 := by
    have := hL.op_eq (((1 : Fin 3), 0), o) (by rw [hLsplit]; exact List.mem_append_left _ hy)
    rw [opOf_badExec] at this; simpa [eq_comm] using this
  subst ho
  have := maxArr_runOps_snd_ge_of_mem (0, 0) (v := 1) (os := L₁.map Prod.snd)
    (List.mem_map.2 ⟨_, hy, rfl⟩)
  rw [hstate] at this; simp at this

end Podc.LimitedUseSnapshots
