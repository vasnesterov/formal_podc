import Papers.PODC2024.MemSnap.Main

/-!
# Lemma 7.2 as printed is false

The third disjunct of the definition of `Q` (Figure 2) admits, for a component `j` with
`B[j].seq ≠ X`, the snapshot value `a_μ` of any process `μ` poised at line 12 with `b_μ = B[j]`,
whatever the value `x_μ` it read from `X`. If `x_μ < X`, the CAS of `μ` would *not* make
`B[j].seq` equal to `X`, and `a_μ` may be an outdated value.

**Execution** (one component, word = read/write register over `ℕ` with initial value `0`,
updaters `ν = 0`, `μ = 1`, scanner `σ = 2`):

1. `ν` invokes `update(write 1)`, finishes `forward` (`B.seq = X = 0`) and is poised at line 7;
2. `μ` invokes `update(write 1)` and reads `b_μ = B = (0, 0)` (line 9);
3. `σ` clicks: `X = 1`;
4. `μ` reads `x_μ = X = 1` (line 10) and `a_μ = A = 0` (line 11): poised at line 12;
5. `ν` writes `A = 1` (line 7) and returns;
6. `σ` clicks again: `X = 2`, `σ` is at line 2.

Now `B = (0, 0) = b_μ`, `B.seq = 0 ≠ X`, and the possibility `p` with `val = 1`, `snap = a_μ = 0`,
`p.σ = ack` and no other process linearized belongs to `Q` (with `S = ∅`, third disjunct with
witness `μ`). But `ν`'s update completed before the second click was invoked, so in every
linearization it precedes that click and the snapshot contains `1`: `p` is realized by no
linearization (`not_tracked`), hence (`tracked_of_mem_PP`) `p ∉ P`, and `Q ⊆ P` fails
(`lemma_7_2_false`).

The corrected `Q` (with `x_μ = X`) does not contain `p`; for it the lemma holds
(`lemma_7_2_fixed`). Whether the third disjunct with `x_μ < X` was intended is clear from the
text preceding Lemma 7.2 ("a successful CAS at Line 12 that will cause `B[j].seq` to become equal
to `X`").
-/

set_option linter.unusedSectionVars false

namespace Podc.MemSnap.Counterexample

open Cslib.SharedMemory

/-- Words: read/write registers over `ℕ`. -/
abbrev Wd : ObjSpec := register ℕ 0

/-- The object: one component, initially `0`. -/
abbrev Obj1 : ObjSpec := checkpointable Wd Unit (fun _ => 0)

/-- MemSnap with updaters `0`, `1` and scanner `2`. -/
noncomputable abbrev I : Impl Obj1 (base Wd Unit (fun _ => 0)) (Fin 3) (Loc Wd Unit) :=
  memSnap Wd Unit (fun _ => 0) (2 : Fin 3)

/-- `update(write 1)`. -/
abbrev w1 : COp Wd Unit := .update () (.write 1)

/-- The execution described in the module docstring. -/
def exec : List (Label (Fin 3) Obj1) :=
  [.inv 0 w1, .tau 0, .tau 0,               -- ν: forward, poised at line 7
   .inv 1 w1, .tau 1,                       -- μ: line 9
   .inv 2 .click, .tau 2, .tau 2,           -- σ: X = 1
   .tau 1, .tau 1,                          -- μ: lines 10, 11: x_μ = 1, a_μ = 0
   .tau 0, .ret 0 (.upd 1),                 -- ν: A = 1, returns
   .ret 2 .ack, .inv 2 .click, .tau 2, .tau 2]  -- σ: X = 2, at line 2

lemma run_exec : (I.run exec).map (fun C => (C.loc 0, C.loc 1, C.loc 2, (C.mem .X : ℕ), (C.mem (.A ()) : ℕ), (C.mem (.B ()) : ℕ × ℕ))) =
    some (.idle, .f12 () (some (.write 1)) false (0, 0) 1 0, .c2, 2, 1, (0, 0)) := by
  simp [exec, Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, I, memSnap, act, invoke, Allowed,
    Function.update, fcont, casOk]


lemma exists_run_exec : ∃ C, I.run exec = some C ∧ C.loc 0 = .idle ∧
    C.loc 1 = .f12 () (some (.write 1)) false (0, 0) 1 0 ∧ C.loc 2 = .c2 ∧ (C.mem .X : ℕ) = 2 ∧
    (C.mem (.A ()) : ℕ) = 1 ∧ (C.mem (.B ()) : ℕ × ℕ) = (0, 0) := by
  have h := run_exec
  cases hr : I.run exec with
  | none => rw [hr] at h; cases h
  | some C =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨C, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- The possibility `val = 1`, `snap = 0`, only the second click linearized. -/
def pbad : CPoss Wd Unit (fun _ => 0) (Fin 3) :=
  ⟨⟨fun _ => 1, fun _ => 0⟩, fun π => if π = 2 then some .ack else none⟩

lemma opsOf_exec_0 : opsOf exec 0 = [w1] := rfl
lemma opsOf_exec_1 : opsOf exec 1 = [w1] := rfl
lemma opsOf_exec_2 : opsOf exec 2 = [.click, .click] := rfl
lemma respsOf_exec_0 : respsOf exec 0 = [.upd 1] := rfl
lemma respsOf_exec_1 : respsOf exec 1 = [] := rfl
lemma respsOf_exec_2 : respsOf exec 2 = [.ack] := rfl


lemma invoked_exec (x : OpId (Fin 3)) (h : Invoked exec x) :
    x = (0, 0) ∨ x = (1, 0) ∨ x = (2, 0) ∨ x = (2, 1) := by
  obtain ⟨p, k⟩ := x
  simp only [Invoked] at h
  fin_cases p <;> simp [opsOf_exec_0, opsOf_exec_1, opsOf_exec_2] at h ⊢ <;> omega

lemma prec_0_21 : Precedes exec (0, 0) (2, 1) :=
  ⟨exec.take 12, exec.drop 12, (List.take_append_drop _ _).symm, by unfold Completed; decide,
    by unfold Invoked; decide⟩

lemma prec_20_21 : Precedes exec (2, 0) (2, 1) :=
  ⟨exec.take 13, exec.drop 13, (List.take_append_drop _ _).symm, by unfold Completed; decide,
    by unfold Invoked; decide⟩

/-- `pbad` is realized by no linearization of `exec`: the update of `ν` completed before the
second click was invoked, so the latest snapshot contains its value `1`. -/
theorem not_tracked : ¬ Poss.Tracked exec pbad := by
  rintro ⟨L, hL, hst, hfl⟩
  have h2 := hfl 2
  have h1 := hfl 1
  have hc2 : curOp exec 2 = (2, 1) := by simp [curOp, respsOf_exec_2]
  have hc1 : curOp exec 1 = (1, 0) := by simp [curOp, respsOf_exec_1]
  rw [hc2] at h2; rw [hc1] at h1
  simp only [pbad] at h1 h2
  simp only [Fin.reduceEq, ↓reduceIte] at h1 h2
  have m21 : ((2 : Fin 3), 1) ∈ L.map Prod.fst := ObjSpec.mem_of_respIn_eq_some h2
  have n10 : ((1 : Fin 3), 0) ∉ L.map Prod.fst := ObjSpec.respIn_eq_none_iff.1 h1
  have hsub : ∀ x ∈ L.map Prod.fst, x = (0, 0) ∨ x = (2, 0) ∨ x = (2, 1) := fun x hx => by
    rcases invoked_exec x (hL.mem_invoked hx) with h | h | h | h
    · exact Or.inl h
    · subst h; exact absurd hx n10
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hs1 := hL.realtime _ _ prec_0_21 m21
  have hs2 := hL.realtime _ _ prec_20_21 m21
  have hsnd : L.map Prod.snd =
      (L.map Prod.fst).map (fun x => if x.1 = 0 then w1 else COp.click) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro y hy
    have := hL.op_eq y hy
    rcases hsub y.1 (List.mem_map_of_mem hy) with h | h | h <;> rw [h] at this <;>
      simp [opOf, opsOf_exec_0, opsOf_exec_2] at this <;> simp [h, this]
  have hst' : (linState L).snap () = 0 := by rw [hst]; rfl
  unfold linState at hst'
  rw [hsnd] at hst'
  have hnd := hL.nodup
  have hlen : (L.map Prod.fst).length = 3 := by
    have m00 : ((0 : Fin 3), 0) ∈ L.map Prod.fst := hL.complete _ (by unfold Completed; decide)
    have m20 : ((2 : Fin 3), 0) ∈ L.map Prod.fst := hL.complete _ (by unfold Completed; decide)
    have hperm : (L.map Prod.fst).Perm [((0 : Fin 3), 0), (2, 0), (2, 1)] := by
      rw [List.perm_ext_iff_of_nodup hnd (by decide)]
      intro x
      constructor
      · intro hx; rcases hsub x hx with rfl | rfl | rfl <;> simp
      · intro hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
    exact hperm.length_eq
  obtain ⟨a, b, c, habc⟩ := List.length_eq_three.1 hlen
  rw [habc] at hs1 hs2 hst' hnd
  rcases hsub a (by simp [habc]) with rfl | rfl | rfl <;>
    rcases hsub b (by simp [habc]) with rfl | rfl | rfl <;>
    rcases hsub c (by simp [habc]) with rfl | rfl | rfl <;>
    simp_all [ObjSpec.runOps] <;> exact absurd hs1 (by decide)

/-- **Lemma 7.2 of [MemSnap], as printed, is false**: in the run of Algorithm 2 along `exec`,
the set `Q` of Figure 2 is not contained in the meta-configuration `P`. -/
theorem lemma_7_2_false : ∃ (α : List (Label (Fin 3) Obj1)) (C : Cfg Wd Unit (fun _ => 0) (Fin 3))
    (G : Ghost Wd Unit (fun _ => 0) (Fin 3)),
    arun (2 : Fin 3) α = some (C, G) ∧ ¬ (QSet (2 : Fin 3) false C G ⊆ G.PP) := by
  obtain ⟨C, hrun, h0, h1, h2, hX, hA, hB⟩ := exists_run_exec
  obtain ⟨G, hG⟩ := exists_arun (σ := (2 : Fin 3)) hrun
  refine ⟨exec, C, G, hG, fun hsub => not_tracked (tracked_of_mem_PP hG pbad (hsub ?_))⟩
  refine ⟨[], List.nodup_nil, by simp, pstar C, ⟨List.nodup_nil, by simp, rfl⟩, ?_, ?_, ?_⟩
  · funext j; simp [pbad, pstar, Cfg.A, hA]
  · intro π; fin_cases π <;> simp [pbad, pstar, h0, h1, h2, Loc.flag]
  · intro j
    right; right
    refine ⟨by simp [Cfg.B, Cfg.X, hB, hX], by simp, 1, some (.write 1), false, (0, 0), 1, 0,
      h1, by simp [Cfg.B, hB], by simp, rfl⟩

end Podc.MemSnap.Counterexample
