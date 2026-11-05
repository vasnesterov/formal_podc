import Papers.PODC2023.WaitFreeQueuePolylog.Defs

/-!
# Counterexamples for the printed pseudocode of Fig. 4

All examples use the tree of height `H = 1` (root `1`, leaves `2` and `3`), two processes
(process `0` owns the left leaf `2`, process `1` the right leaf `3`) and values in `ℕ`.

* **Line 13 (`Variant.paper`).** As printed, `Append` increments `leaf.head` by a plain write
  and never sets `leaf.blocks[h].super`. A solo `Enqueue(7)` of process `0` leaves
  `leaf.head = 2` but `leaf.blocks[1].super = null`, so the third claim of Invariant 3
  ("if `v ≠ root`, `v.blocks[i].super ≠ null` for `0 < i < v.head`") fails
  (`invariant3_false`). This breaks `IndexDequeue`: in the solo sequential execution
  `Dequeue → null; Enqueue(7); Dequeue` the last `Dequeue` reads the null `super` field of its
  leaf block (as `0`), computes a wrong root block, and returns `null` instead of `7`; the
  printed algorithm is therefore not linearizable (`paper_not_linearizable`). With line 13
  replaced by `Advance(leaf, h)` (and line 78 corrected) the same operations behave correctly
  (`fixed_example`).
* **Line 78 (`Variant` `⟨true, false⟩`: leaf `Advance` repaired, line 78 as printed).** Line 78
  reads `v.blocks[…]`, indexed by `endleft` fields, which index the blocks of the *left
  sibling*. Process `0` enqueues `7`; then processes `0` and `1` both invoke `Dequeue`, process
  `1` writes its leaf block, and process `0` runs to completion, propagating both dequeues into
  the same root block (it helps advance leaf `3`). Process `0`'s dequeue precedes process `1`'s
  in that block and correctly returns `7`. Process `1` (a right child) must add the number of
  dequeues from the left child in the root block (line 78), but the printed line 78 takes the
  difference of two `sumdeq` fields of its *own* leaf, misses process `0`'s dequeue, computes
  rank `1` instead of `2` in the root block, and also returns `7`
  (`line78_not_linearizable`). With line 78 corrected it returns `null` (`line78_fixed_example`).

Non-linearizability is reduced to a finite check by `not_isLinearization_of_check`: every
linearization of a history in which all operations completed is a permutation of these
operations, so it suffices to check all permutations.
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

/-! ### A decidable criterion for non-linearizability -/

section Check

variable {P : Type} [DecidableEq P] {A : ObjSpec} [DecidableEq A.Resp]

/-- Boolean version of `SeqOK`. -/
def seqOKb (α : List (Label P A)) : A.State → List (OpId P × A.Op) → Bool
  | _, [] => true
  | q, (x, o) :: L =>
    (match respOf α x with
      | some r => decide ((A.δ q o).2 = r)
      | none => true) && seqOKb α (A.δ q o).1 L

lemma seqOKb_of_seqOK {α : List (Label P A)} {q : A.State} {L : List (OpId P × A.Op)}
    (h : SeqOK α q L) : seqOKb α q L = true := by
  induction L generalizing q with
  | nil => rfl
  | cons y L ih =>
    obtain ⟨x, o⟩ := y
    obtain ⟨h1, h2⟩ := h
    simp only [seqOKb, Bool.and_eq_true]
    refine ⟨?_, ih h2⟩
    cases hr : respOf α x with
    | none => rfl
    | some r => simpa using h1 r hr

/-- A finite, decidable criterion for a history to have no linearization: `S` lists all
invoked operations (all of them completed), `prec` some real-time precedences (each witnessed
by a prefix of `α`), and no permutation of `S` respecting `prec` is legal. -/
-- CSLib candidate
theorem not_isLinearization_of_check (α : List (Label P A)) (S : List (OpId P × A.Op))
    (prec : List (OpId P × OpId P))
    (hS : ∀ p : P, ∀ k (hk : k < (opsOf α p).length), ((p, k), (opsOf α p)[k]) ∈ S)
    (hS' : ∀ y ∈ S, opOf α y.1 = some y.2 ∧ y.1.2 < (respsOf α y.1.1).length)
    (hnd : (S.map Prod.fst).Nodup)
    (hP : ∀ ab ∈ prec, ab.2.2 < (respsOf α ab.2.1).length ∧ ∃ n < α.length + 1,
      ab.1.2 < (respsOf (α.take n) ab.1.1).length ∧ ¬ ab.2.2 < (opsOf (α.take n) ab.2.1).length)
    (hcheck : S.permutations'.all (fun L =>
      !(prec.all fun ab => [ab.1, ab.2].isSublist (L.map Prod.fst)) || !seqOKb α A.init L) = true)
    (L : List (OpId P × A.Op)) : ¬ IsLinearization α L := by
  intro hL
  have hLS : ∀ y ∈ L, y ∈ S := by
    rintro ⟨⟨p, k⟩, o⟩ hy
    have h := hL.op_eq _ hy
    simp only [opOf, List.getElem?_eq_some_iff] at h
    obtain ⟨hk, rfl⟩ := h
    exact hS p k hk
  have hSL : ∀ y ∈ S, y ∈ L := by
    intro y hy
    obtain ⟨h1, h2⟩ := hS' y hy
    obtain ⟨z, hz, hzy⟩ := List.mem_map.1 (hL.complete _ h2)
    have h3 := hL.op_eq z hz
    rw [hzy, h1, Option.some_inj] at h3
    have : z = y := Prod.ext hzy h3.symm
    exact this ▸ hz
  have hperm : L.Perm S :=
    (List.perm_ext_iff_of_nodup (hL.nodup.of_map _) (hnd.of_map _)).2
      fun y => ⟨hLS y, hSL y⟩
  have h := List.all_eq_true.1 hcheck L (List.mem_permutations'.2 hperm)
  have hprec : (prec.all fun ab => [ab.1, ab.2].isSublist (L.map Prod.fst)) = true := by
    refine List.all_eq_true.2 fun ab hab => ?_
    obtain ⟨hc, n, -, h1, h2⟩ := hP ab hab
    have hpre : Precedes α ab.1 ab.2 := ⟨α.take n, α.drop n, (List.take_append_drop n α).symm, h1, h2⟩
    exact List.isSublist_iff_sublist.2 (hL.realtime _ _ hpre (hL.complete _ hc))
  rw [hprec, seqOKb_of_seqOK hL.seq] at h
  exact absurd h (by decide)

end Check

/-! ### The instances -/

/-- The queue of Fig. 4 (variant `var`) for two processes and a tree of height `1`. -/
abbrev Qc (var : Variant) : Impl (queueObj ℕ) (fun _ : Unit => memObj ℕ) (Fin 2) (Loc ℕ) :=
  queueImpl 1 var 2

instance (var : Variant) : ∀ p o, Decidable ((Qc var).allowed p o) := fun _ _ => isTrue trivial

/-- Labels of executions of `Qc var`. -/
abbrev Lbl := Label (Fin 2) (queueObj ℕ)

/-- `n` steps of process `p`. -/
abbrev taus (p : Fin 2) (n : ℕ) : List Lbl := List.replicate n (.tau p)

lemma valid_iff_crun (var : Variant) (α : List Lbl) :
    (Qc var).Valid α ↔ ((Qc var).crun α).isSome = true := by
  rw [Impl.Valid, (Qc var).run_eq_crun α, Option.isSome_iff_exists]

/-! ### Line 13: Invariant 3 fails -/

/-- A solo `Enqueue(7)` of process `0` (`13` shared-memory steps). -/
def enqExec : List Lbl := [.inv 0 (.enq 7)] ++ taus 0 13 ++ [.ret 0 none]

/-- The final configuration of `enqExec` (printed algorithm). -/
def enqCfg := ((Qc Variant.paper).crun enqExec).get (by decide +kernel)

/-- Invariant 3 (third claim) of [Naderibeni–Ruppert] fails for the printed pseudocode: after a
solo `Enqueue`, the left leaf `2` has `head = 2` but `blocks[1].super = null`. -/
theorem invariant3_false : ∃ α C, (queueImpl 1 Variant.paper 2 :
      Impl (queueObj ℕ) (fun _ : Unit => memObj ℕ) (Fin 2) (Loc ℕ)).run α = some C ∧
    C.Quiescent ∧ (C.mem ()).head 2 = 2 ∧ (C.mem ()).sup 2 1 = none :=
  ⟨enqExec, enqCfg, ((Qc Variant.paper).run_eq_crun _).trans (Option.some_get _).symm,
    by unfold Config.Quiescent; decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ### Line 13: the printed algorithm is not linearizable -/

/-- Process `0` runs `Dequeue`, `Enqueue(7)`, `Dequeue` sequentially; the printed algorithm
answers `null` to the last `Dequeue`. -/
def seqExec : List Lbl :=
  [.inv 0 .deq] ++ taus 0 15 ++ [.ret 0 none] ++
  [.inv 0 (.enq 7)] ++ taus 0 13 ++ [.ret 0 none] ++
  [.inv 0 .deq] ++ taus 0 15 ++ [.ret 0 none]

lemma seqExec_valid : (Qc Variant.paper).Valid seqExec :=
  (valid_iff_crun _ _).2 (by decide +kernel)

/-- The printed pseudocode of Fig. 4 (line 13 as printed) is not linearizable, contradicting
Theorem 18 of [Naderibeni–Ruppert]. -/
theorem paper_not_linearizable :
    ¬ (queueImpl 1 Variant.paper 2 :
      Impl (queueObj ℕ) (fun _ : Unit => memObj ℕ) (Fin 2) (Loc ℕ)).Linearizable := by
  rintro ⟨f, hf⟩
  exact not_isLinearization_of_check seqExec
    [((0, 0), .deq), ((0, 1), .enq 7), ((0, 2), .deq)] [((0, 0), (0, 1)), ((0, 1), (0, 2))]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ (hf _ seqExec_valid)

/-- The same operations on the repaired algorithm: the last `Dequeue` returns `7`
(and returning `null` is impossible). -/
def seqExecFixed (r : Option ℕ) : List Lbl :=
  [.inv 0 .deq] ++ taus 0 17 ++ [.ret 0 none] ++
  [.inv 0 (.enq 7)] ++ taus 0 15 ++ [.ret 0 none] ++
  [.inv 0 .deq] ++ taus 0 19 ++ [.ret 0 r]

/-- Sanity check: on the repaired algorithm, `Dequeue → null; Enqueue(7); Dequeue → 7`. -/
theorem fixed_example :
    (Qc Variant.fixed).Valid (seqExecFixed (some 7)) ∧
      ¬ (Qc Variant.fixed).Valid (seqExecFixed none) :=
  ⟨(valid_iff_crun _ _).2 (by decide +kernel),
    by rw [valid_iff_crun]; decide +kernel⟩

/-! ### Line 78 -/

/-- Leaf `Advance` repaired (line 13), line 78 as printed. -/
def Variant.line78 : Variant := ⟨true, false⟩

/-- Process `0` enqueues `7`; then both processes invoke `Dequeue`, process `1` writes its leaf
block (3 steps), process `0` completes its `Dequeue`, then process `1` completes. -/
def concExec (r : Option ℕ) (n : ℕ) : List Lbl :=
  [.inv 0 (.enq 7)] ++ taus 0 15 ++ [.ret 0 none] ++
  [.inv 0 .deq, .inv 1 .deq] ++ taus 1 3 ++ taus 0 22 ++ [.ret 0 (some 7)] ++
  taus 1 n ++ [.ret 1 r]

lemma concExec_valid : (Qc Variant.line78).Valid (concExec (some 7) 14) :=
  (valid_iff_crun _ _).2 (by decide +kernel)

/-- With only the typo of line 78 left (`v.blocks` instead of the left sibling's blocks), the
algorithm is still not linearizable: one `Enqueue(7)` and two `Dequeue`s that both return `7`. -/
theorem line78_not_linearizable :
    ¬ (queueImpl 1 Variant.line78 2 :
      Impl (queueObj ℕ) (fun _ : Unit => memObj ℕ) (Fin 2) (Loc ℕ)).Linearizable := by
  rintro ⟨f, hf⟩
  exact not_isLinearization_of_check (concExec (some 7) 14)
    [((0, 0), .enq 7), ((0, 1), .deq), ((1, 0), .deq)] []
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ (hf _ concExec_valid)

/-- Sanity check: on the repaired algorithm the same schedule lets process `1`'s `Dequeue`
return `null`. -/
theorem line78_fixed_example : (Qc Variant.fixed).Valid (concExec none 12) :=
  (valid_iff_crun _ _).2 (by decide +kernel)

end Podc.WaitFreeQueuePolylog
