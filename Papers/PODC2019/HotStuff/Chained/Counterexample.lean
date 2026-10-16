import Papers.PODC2019.HotStuff.Chained.Model

/-!
# Chained HotStuff: counterexamples to Theorem 5

`n = 4`, `f = 1`, Byzantine replica `3`; QCs need `3` signers, i.e. two correct votes plus the
Byzantine replica. All proposals come from a Byzantine leader (the paper: the choice of `leader()`
does not affect safety). Commands are natural numbers; `g` = genesis.
-/

namespace HotStuff.Chained

open Node

/-- The Byzantine set `{3}`. -/
abbrev F₄ : Finset (Fin 4) := {3}

/-- Replicas `rs` process proposal `b` (in their current view). -/
def procAll (rs : List (Fin 4)) (b : Node ℕ) : List (Action (Fin 4) ℕ) :=
  rs.map fun r => .process r b

/-- Replicas `rs` move to view `v`. -/
def nextAll (rs : List (Fin 4)) (v : ℕ) : List (Action (Fin 4) ℕ) :=
  rs.map fun r => .nextView r v

/-! ## Algorithm 3 as written: the lock can be downgraded -/

namespace Literal

/-- View 1: `y` (cmd 1) on genesis. -/
def y : Node ℕ := .mk .gen 1 0 .gen
/-- View 2: `w` (cmd 2) on genesis, conflicting with `y`. -/
def w : Node ℕ := .mk .gen 2 0 .gen
/-- View 3. -/
def w₁ : Node ℕ := .mk w 3 2 w
/-- View 4. -/
def w₂ : Node ℕ := .mk w₁ 4 3 w₁
/-- View 5: processing it commits `w`. -/
def w₃ : Node ℕ := .mk w₂ 5 4 w₂
/-- View 6: not voted for, but it resets the lock to `y.justify = (0, genesis)`. -/
def x : Node ℕ := .mk y 6 1 y
/-- View 7: voted for (it extends genesis). -/
def u : Node ℕ := .mk y 7 1 y
/-- View 8. -/
def u₁ : Node ℕ := .mk u 8 7 u
/-- View 9: processing it commits `y`. -/
def u₂ : Node ℕ := .mk u₁ 9 8 u₁

/-- The execution: replicas `0` and `1` process every proposal. -/
def trace : List (Action (Fin 4) ℕ) :=
  procAll [0, 1] y ++ nextAll [0, 1] 2 ++ procAll [0, 1] w ++ nextAll [0, 1] 3 ++
  procAll [0, 1] w₁ ++ nextAll [0, 1] 4 ++ procAll [0, 1] w₂ ++ nextAll [0, 1] 5 ++
  procAll [0, 1] w₃ ++ nextAll [0, 1] 6 ++ procAll [0, 1] x ++ nextAll [0, 1] 7 ++
  procAll [0, 1] u ++ nextAll [0, 1] 8 ++ procAll [0, 1] u₁ ++ nextAll [0, 1] 9 ++
  procAll [0, 1] u₂

theorem trace_ok : runOK .literal 1 F₄ trace init = true := by decide

theorem committed_w : w ∈ ((exec .literal trace init).loc 0).committed := by decide

theorem committed_y : y ∈ ((exec .literal trace init).loc 0).committed := by decide

theorem conflict_y_w : Conflict y w := by decide

end Literal

/-- **Theorem 5 is false for Algorithm 3 as written.** With `n = 4`, `f = 1` and one Byzantine
replica, a single correct replica commits two conflicting nodes. The reason: Line 20 sets
`lockedQC ← b''.justify` unconditionally, so a Byzantine leader can *downgrade* the lock of a
correct replica with a proposal the replica does not even vote for (Lines 17-22 run whether or
not `safeNode` holds). -/
theorem theorem5_false :
    3 * 1 < Fintype.card (Fin 4) ∧ F₄.card ≤ 1 ∧ ¬ Safe (Fin 4) ℕ .literal 1 F₄ := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  exact h _ (reachable_exec Literal.trace_ok) 0 0 (by decide) (by decide) _ Literal.committed_w _
    Literal.committed_y (conflict_symm Literal.conflict_y_w)
where
  conflict_symm {a b : Node ℕ} (h : Conflict a b) : Conflict b a := ⟨h.2, h.1⟩

/-! ## Monotone lock update (as in Algorithm 4) without the height check -/

namespace MonoLock

/-- View 1: `w` on genesis. -/
def w : Node ℕ := .mk .gen 1 0 .gen
/-- View 3: `c` on genesis, conflicting with `w`; only replicas 0, 1 vote. -/
def c : Node ℕ := .mk .gen 3 0 .gen
/-- View 5. -/
def w₁ : Node ℕ := .mk w 5 1 w
/-- View 6: replicas lock on `(1, w)`. -/
def w₂ : Node ℕ := .mk w₁ 6 5 w₁
/-- View 7: only replica 2 processes it and commits `w`. -/
def w₃ : Node ℕ := .mk w₂ 7 6 w₂
/-- View 8: replicas 0, 1 (locked on `(1, w)`) vote by the liveness rule: `3 > 1`. -/
def d : Node ℕ := .mk c 8 3 c
/-- View 9. -/
def d₁ : Node ℕ := .mk d 9 8 d
/-- View 10: replicas 0, 1 commit `c`. -/
def d₂ : Node ℕ := .mk d₁ 10 9 d₁

/-- The execution. -/
def trace : List (Action (Fin 4) ℕ) :=
  procAll [0, 1, 2] w ++ nextAll [0, 1, 2] 3 ++ procAll [0, 1] c ++ nextAll [0, 1, 2] 5 ++
  procAll [0, 1, 2] w₁ ++ nextAll [0, 1, 2] 6 ++ procAll [0, 1, 2] w₂ ++ nextAll [2] 7 ++
  procAll [2] w₃ ++ nextAll [0, 1] 8 ++ procAll [0, 1] d ++ nextAll [0, 1] 9 ++
  procAll [0, 1] d₁ ++ nextAll [0, 1] 10 ++ procAll [0, 1] d₂

theorem trace_ok : runOK .monoLock 1 F₄ trace init = true := by decide

theorem committed_w : w ∈ ((exec .monoLock trace init).loc 2).committed := by decide

theorem committed_c : c ∈ ((exec .monoLock trace init).loc 0).committed := by decide

theorem conflict_w_c : Conflict w c := by decide

end MonoLock

/-- **A monotone lock update alone does not repair Theorem 5.** Without the check
`b*.height = curView`, view numbers and heights decouple; a QC on a conflicting node `c` formed
in view `3` (between the QCs on `w` (view 1) and its children (views 5, 6)) later passes the
liveness rule of `safeNode` (`3 > 1`). -/
theorem monoLock_unsafe :
    3 * 1 < Fintype.card (Fin 4) ∧ F₄.card ≤ 1 ∧ ¬ Safe (Fin 4) ℕ .monoLock 1 F₄ := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  exact h _ (reachable_exec MonoLock.trace_ok) 2 0 (by decide) (by decide) _
    MonoLock.committed_w _ MonoLock.committed_c MonoLock.conflict_w_c

/-! ## Non-vacuity of the repaired variant -/

namespace Live

/-- View 1. -/
def a : Node ℕ := .mk .gen 1 0 .gen
/-- View 2. -/
def b : Node ℕ := .mk a 2 1 a
/-- View 3. -/
def c : Node ℕ := .mk b 3 2 b
/-- View 4: processing it commits `a`. -/
def d : Node ℕ := .mk c 4 3 c

/-- A failure-free-looking execution: replicas 0, 1, 2 process every proposal. -/
def trace : List (Action (Fin 4) ℕ) :=
  procAll [0, 1, 2] a ++ nextAll [0, 1, 2] 2 ++ procAll [0, 1, 2] b ++ nextAll [0, 1, 2] 3 ++
  procAll [0, 1, 2] c ++ nextAll [0, 1, 2] 4 ++ procAll [0, 1, 2] d

theorem trace_ok : runOK .heightCheck 1 F₄ trace init = true := by decide

theorem committed_a : a ∈ ((exec .heightCheck trace init).loc 0).committed := by decide

end Live

/-- The repaired variant (`heightCheck`) is not vacuous: a correct replica can commit a
non-genesis node. -/
theorem heightCheck_nonvacuous :
    ∃ s : State (Fin 4) ℕ, Reachable .heightCheck 1 F₄ s ∧
      ∃ r ∉ F₄, ∃ b ∈ (s.loc r).committed, b ≠ .gen :=
  ⟨_, reachable_exec Live.trace_ok, 0, by decide, _, Live.committed_a, by decide⟩

/-! ## Round-robin leaders, one Byzantine replica, synchrony

`leader(v) = v mod 4`; replica `2` is Byzantine and leads only views `2`, `6`, `10`. Every other
proposal is made by a correct leader with `createLeaf` (padded with blank nodes, so its height
equals its view; its justify is the QC formed in the previous view or the highest known QC). All
correct replicas process every proposal in every view (a synchronous execution). The only
deviation from `createLeaf` is the Byzantine proposal `x` of view 6. -/

namespace RoundRobin

/-- The Byzantine set `{2}`. -/
abbrev F₂ : Finset (Fin 4) := {2}

/-- Round-robin leader. -/
def leader (v : ℕ) : Fin 4 := ⟨v % 4, Nat.mod_lt _ (by norm_num)⟩

/-- A blank node (padding of `createLeaf`). -/
def bl (p : Node ℕ) : Node ℕ := .mk p 0 0 .gen

/-- View 1 (correct leader 1): `y` on genesis. -/
def y : Node ℕ := .mk .gen 1 0 .gen
/-- View 2 (Byzantine leader 2): `w`, conflicting with `y`, padded to height 2. -/
def w : Node ℕ := .mk (bl .gen) 2 0 .gen
/-- View 3 (correct leader 3). -/
def w₁ : Node ℕ := .mk w 3 2 w
/-- View 4 (correct leader 0). -/
def w₂ : Node ℕ := .mk w₁ 4 3 w₁
/-- View 5 (correct leader 1): processing it commits `w`. -/
def w₃ : Node ℕ := .mk w₂ 5 4 w₂
/-- View 6 (Byzantine leader 2): child of `y` justified by `QC(y)`; rejected, but it resets the
locks to `y.justify = (0, genesis)` and `genericQC` to `QC(y)`. -/
def x : Node ℕ := .mk y 6 1 y
/-- View 7 (correct leader 3): extends its `genericQC = QC(y)`, padded to height 7. -/
def u : Node ℕ := .mk (bl (bl (bl (bl (bl y))))) 7 1 y
/-- View 8 (correct leader 0). -/
def u₁ : Node ℕ := .mk u 8 7 u
/-- View 9 (correct leader 1). -/
def u₂ : Node ℕ := .mk u₁ 9 8 u₁
/-- View 10 (Byzantine leader 2, behaving correctly): processing it commits `u`. -/
def u₃ : Node ℕ := .mk u₂ 10 9 u₂

/-- Proposals per view. -/
def schedule : List (ℕ × Node ℕ) :=
  [(1, y), (2, w), (3, w₁), (4, w₂), (5, w₃), (6, x), (7, u), (8, u₁), (9, u₂), (10, u₃)]

/-- The correct replicas. -/
def rs : List (Fin 4) := [0, 1, 3]

/-- The synchronous execution: in each view all correct replicas process the proposal, then move
to the next view. -/
def trace : List (Action (Fin 4) ℕ) :=
  procAll rs y ++ nextAll rs 2 ++ procAll rs w ++ nextAll rs 3 ++ procAll rs w₁ ++
  nextAll rs 4 ++ procAll rs w₂ ++ nextAll rs 5 ++ procAll rs w₃ ++ nextAll rs 6 ++
  procAll rs x ++ nextAll rs 7 ++ procAll rs u ++ nextAll rs 8 ++ procAll rs u₁ ++
  nextAll rs 9 ++ procAll rs u₂ ++ nextAll rs 10 ++ procAll rs u₃

theorem trace_ok : runOK .literal 1 F₂ trace init = true := by decide

theorem committed_w : w ∈ ((exec .literal trace init).loc 0).committed := by decide

theorem committed_u : u ∈ ((exec .literal trace init).loc 0).committed := by decide

theorem conflict_w_u : Conflict w u := by decide

/-- Every proposal of a correct leader has height equal to its view (it is built by
`createLeaf`); the only proposal violating this is the Byzantine `x` of view 6. -/
theorem heights : ∀ p ∈ schedule, (leader p.1 ∉ F₂ → p.2.height = p.1) ∧
    (p.2.height ≠ p.1 → p = (6, x)) := by decide

end RoundRobin

/-- **Theorem 5 is false for Algorithm 3, even with round-robin leaders and a synchronous
execution.** `n = 4`, `f = 1`, `leader(v) = v mod 4`, replica `2` Byzantine (it leads views
`2, 6, 10`). All correct replicas process every proposal; correct leaders' proposals are built by
`createLeaf`, and only the Byzantine proposal of view 6 violates `height = view`. The correct
replica `0` commits both `w` (view 5) and the conflicting `u` (view 10). -/
theorem theorem5_false_roundRobin :
    3 * 1 < Fintype.card (Fin 4) ∧ RoundRobin.F₂.card ≤ 1 ∧
    Reachable .literal 1 RoundRobin.F₂ (exec .literal RoundRobin.trace init) ∧
    RoundRobin.w ∈ ((exec .literal RoundRobin.trace init).loc 0).committed ∧
    RoundRobin.u ∈ ((exec .literal RoundRobin.trace init).loc 0).committed ∧
    Conflict RoundRobin.w RoundRobin.u ∧
    (∀ p ∈ RoundRobin.schedule, (RoundRobin.leader p.1 ∉ RoundRobin.F₂ → p.2.height = p.1) ∧
      (p.2.height ≠ p.1 → p = (6, RoundRobin.x))) ∧
    ¬ Safe (Fin 4) ℕ .literal 1 RoundRobin.F₂ :=
  ⟨by decide, by decide, reachable_exec RoundRobin.trace_ok, RoundRobin.committed_w,
    RoundRobin.committed_u, RoundRobin.conflict_w_u, RoundRobin.heights,
    fun h => h _ (reachable_exec RoundRobin.trace_ok) 0 0 (by decide) (by decide) _
      RoundRobin.committed_w _ RoundRobin.committed_u RoundRobin.conflict_w_u⟩

end HotStuff.Chained
