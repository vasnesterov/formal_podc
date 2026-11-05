import Papers.PODC2020.LongLivedSnapshotsPolylog.BoundedIncrement

/-!
# Lemma 3.3 is false: linearization rules (1)–(3) do not respect the max-array semantics

Section 3.1 of the paper linearizes the operations of Algorithm 1 by three rules; Lemma 3.3 claims
that the resulting order "respects the semantics of the 2-max array object". We formalize
rules (1) and (3) for arbitrary executions of `alg1 n m X` (`Rule1Point`, `Rule3Point`) and give an
execution (`n = 4`, `m = 16 = n²`, `4`-bounded-increment, every `X`) in which

* rule (3) linearizes `MaxUpdate(right, 3)` of process `B` at a step `s` (`Q`'s line-16 write
  of the right side of `MA_0`, after `Q` read `MR_right = 3`),
* rule (1) linearizes the `MaxScan` of process `S` at its line-17 step `t > s`,
* but `S` returns `(16, 0)`: its right component `0` is smaller than `3`.

Since in the sequential specification every `MaxScan` that follows a `MaxUpdate(right, 3)` returns
a right component `≥ 3` (`scan_right_ge`), the sequential history given by rules (1)–(3) is not
legal (`lemma_3_3_false`).

The execution (processes `A = 0`, `B = 1`, `Q = 2`, `S = 3`; `αex`):

1. `A` runs `MaxUpdate(left, 4)`, `(left, 8)`, `(left, 12)` solo.
2. `Q` invokes `MaxScan`, reads `MR_right = 0` (line 10) and `MR_left = 12` (line 11).
3. `A` invokes `MaxUpdate(left, 16)` and writes `MR_left := 16` (line 4).
4. `S` invokes `MaxScan`, reads `0`, `16`, `0` (lines 10–12): index `h = 1`.
5. `B` invokes `MaxUpdate(right, 3)` and writes `MR_right := 3` (line 4) — step `w`.
6. `Q` reads `MR_right = 3` (line 12), `h = 0`, writes `MA_0.left := 12`, `MA_0.right := 3`
   (lines 15, 16) — the latter is step `s`.
7. `S` writes `MA_1.left := 0`, `MA_1.right := 0`, `MaxScan(MA_1) = (0, 0)` (line 17, step `t`),
   passes line 18 (`MR_left = 16`, `MR_right = 3` have the same high-order bits as before),
   writes `H[3]` and returns the direct view `(16, 0)` (step `e`).

The flaw: rule (3) linearizes `B`'s update at a write to the *old* array `MA_0` although the active
array is already `MA_1` (`S` committed to `h = 1` before reading `MR_right` changed). Equivalently,
Claim 4 fails after step `s`: the value of `O` (Definition 3.2, active array `MA_1`) is `(16, 0)`,
while a `WriteMax(MR_right, 3)` is already linearized. The history itself is linearizable
(linearize `B`'s update after `S`'s scan); only the paper's rules are wrong.

The concrete facts are checked by kernel evaluation of the computable step function
(`Impl.crun`); as the execution never reaches the failure branch of lines 23–29, the evaluation
does not depend on `X`, which stays a free variable (tactic `kernel_decide_fvar`).
-/

namespace Podc.LongLivedSnapshotsPolylog.Counterexample

open Cslib.SharedMemory
open Podc.LimitedUseSnapshots (maxArrObj MAOp)

/-- Labels of executions of the max array `maxArrObj` with processes `Fin n`. -/
abbrev Lbl (n : ℕ) := Label (Fin n) maxArrObj

/-! ## Linearization rules (1) and (3) -/

section Rules

variable {n : ℕ}

/-- The program counter of the process taking step `t` of `α` (Algorithm 1 with parameters `m`,
`X`), just before step `t`; `none` if `t` is out of range or `α.take t` is not an execution. -/
noncomputable def stepPC (m X : ℕ) (α : List (Lbl n)) (t : ℕ) : Option (PC n) :=
  match α[t]? with
  | some ℓ => ((alg1 n m X).run (α.take t)).map fun C => (C.loc ℓ.proc).pc
  | none => none

/-- Line 4: `WriteMax(MR_sd, ·)` (`sd = false`: left, `true`: right). -/
def isWriteMR (sd : Bool) : PC n → Bool
  | .wm s _ => s == sd
  | _ => false

/-- The read of `MR_sd` whose value is then written to side `sd` of an `MA` object: line 11
(`MR_left`) or line 12 (`MR_right`), as in rule (3). -/
def isReadMR (sd : Bool) : PC n → Bool
  | .rdL .. => !sd
  | .rdR2 .. => sd
  | _ => false

/-- The write to side `sd` of an `MA` object: line 15 (left) or line 16 (right). -/
def isWriteMA (sd : Bool) : PC n → Bool
  | .upL .. => !sd
  | .upR .. => sd
  | _ => false

/-- Line 17, `MaxScan(MA_h)`, in the `CompScan` instance of a `MaxScan` operation. -/
def isScanMA : PC n → Bool
  | .scanMA cs _ _ => !cs.upd
  | _ => false

/-- Lines 20–21: the write of a direct view to the helping array. -/
def isWriteH : PC n → Bool
  | .wH .. => true
  | _ => false

/-- Step `t` of `α` is a base-object access by process `p` from a program counter satisfying
`f`. -/
def StepAt (m X : ℕ) (α : List (Lbl n)) (t : ℕ) (p : Fin n) (f : PC n → Bool) : Prop :=
  (α[t]?.any (Label.isTauOf p)) = true ∧ (stepPC m X α t).any f = true

/-- Process `p` does not return in the open interval `(a, b)` of steps of `α`, i.e. its steps
`a` and `b` belong to the same operation. -/
def SameOp (α : List (Lbl n)) (p : Fin n) (a b : ℕ) : Prop :=
  ∀ u < b, a < u → α[u]?.bind (Label.retOf p) = none

/-- Within one operation, process `p` reads `MR_sd` (line 11/12) at step `r` and writes side `sd`
of an `MA` object (line 15/16) at the later step `s`. -/
def ReadThenWrite (m X : ℕ) (α : List (Lbl n)) (sd : Bool) (p : Fin n) (r s : ℕ) : Prop :=
  r < s ∧ StepAt m X α r p (isReadMR sd) ∧ StepAt m X α s p (isWriteMA sd) ∧ SameOp α p r s

/-- At step `s`, some operation writes side `sd` of an `MA` object after having read `MR_sd`
after step `w`. -/
def Propagates (m X : ℕ) (α : List (Lbl n)) (sd : Bool) (w s : ℕ) : Prop :=
  ∃ p : Fin n, ∃ r < s, w < r ∧ ReadThenWrite m X α sd p r s

/-- **Linearization rule (3).** The `WriteMax(MR_sd, ·)` (line 4) performed at step `w` of `α`
is linearized at step `s`: the first step after `w` at which an operation that read `MR_sd`
after `w` (line 11/12) writes side `sd` of an `MA` object (line 15/16). -/
def Rule3Point (m X : ℕ) (α : List (Lbl n)) (sd : Bool) (w s : ℕ) : Prop :=
  (∃ p, StepAt m X α w p (isWriteMR sd)) ∧ w < s ∧ Propagates m X α sd w s ∧
    ∀ s' < s, w < s' → ¬ Propagates m X α sd w s'

/-- **Linearization rule (1).** The `MaxScan` operation that returns a direct view at step `e`
(a return label) is linearized at step `t`: its last line-17 step before `e`; the view is direct,
i.e. the operation writes it to `H` (lines 20–21) between `t` and `e`. -/
def Rule1Point (m X : ℕ) (α : List (Lbl n)) (t e : ℕ) : Prop :=
  ∃ p : Fin n, (α[e]?.bind (Label.retOf p)).isSome ∧ t < e ∧ StepAt m X α t p isScanMA ∧
    SameOp α p t e ∧ (∀ u < e, t < u → ¬ StepAt m X α u p isScanMA) ∧
    ∃ u < e, t < u ∧ StepAt m X α u p isWriteH

/-! Decision procedures (through the computable `Impl.crun`), used on concrete executions. -/

lemma stepPC_eq_crun (m X : ℕ) (α : List (Lbl n)) (t : ℕ) :
    stepPC m X α t = match α[t]? with
      | some ℓ => ((alg1 n m X).crun (α.take t)).map fun C => (C.loc ℓ.proc).pc
      | none => none := by
  simp only [stepPC, (alg1 n m X).run_eq_crun]

instance (m X : ℕ) (α : List (Lbl n)) (t : ℕ) (p : Fin n) (f : PC n → Bool) :
    Decidable (StepAt m X α t p f) :=
  decidable_of_iff (_ ∧ _) (by rw [StepAt, stepPC_eq_crun])

instance (α : List (Lbl n)) (p : Fin n) (a b : ℕ) : Decidable (SameOp α p a b) :=
  inferInstanceAs (Decidable (∀ u < b, a < u → _))

instance (m X : ℕ) (α : List (Lbl n)) (sd : Bool) (p : Fin n) (r s : ℕ) :
    Decidable (ReadThenWrite m X α sd p r s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance (m X : ℕ) (α : List (Lbl n)) (sd : Bool) (w s : ℕ) :
    Decidable (Propagates m X α sd w s) :=
  inferInstanceAs (Decidable (∃ _p : Fin n, ∃ r < s, w < r ∧ _))

instance (m X : ℕ) (α : List (Lbl n)) (sd : Bool) (w s : ℕ) :
    Decidable (Rule3Point m X α sd w s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ∀ s' < s, w < s' → ¬ Propagates m X α sd w s'))

instance (m X : ℕ) (α : List (Lbl n)) (t e : ℕ) : Decidable (Rule1Point m X α t e) :=
  inferInstanceAs (Decidable (∃ _p : Fin n, _ ∧ _ ∧ _ ∧ _ ∧ (∀ u < e, t < u → _) ∧ ∃ u < e, _))

end Rules

/-! ## The sequential specification -/

/-- Updates and scans never decrease the right component of a max array. -/
lemma right_le_runOps (q : ℕ × ℕ) (os : List MAOp) : q.2 ≤ (maxArrObj.runOps q os).2 := by
  induction os generalizing q with
  | nil => exact le_rfl
  | cons o os ih =>
    refine le_trans ?_ (ih _)
    cases o <;> simp

/-- In the sequential specification of the max array, a `MaxScan` that follows a
`MaxUpdate(right, v)` returns a right component `≥ v`. -/
theorem scan_right_ge (q : ℕ × ℕ) (v : ℕ) (os : List MAOp) :
    v ≤ (maxArrObj.δ (maxArrObj.runOps q (.upd1 v :: os)) .scan).2.2 :=
  le_trans (by simp) (right_le_runOps _ os)

/-! ## Computable write logs -/

section CLog

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L κ : Type} [DecidableEq P]
  [DecidableEq ι] [DecidableEq A.Resp] (I : Impl A B P L) [∀ p o, Decidable (I.allowed p o)]

/-- `wlogFrom` with the computable step function `Impl.cstep`. -/
def cwlogFrom (w : P → L → Option (κ × ℕ)) :
    Config A B P L → List (Label P A) → List (κ × ℕ)
  | _, [] => []
  | C, ℓ :: α =>
    match I.cstep C ℓ with
    | none => []
    | some C' =>
      (match ℓ with
        | .tau p => (w p (C.loc p)).toList
        | _ => []) ++ cwlogFrom w C' α

lemma wlogFrom_eq_cwlogFrom (w : P → L → Option (κ × ℕ)) (C : Config A B P L)
    (α : List (Label P A)) : wlogFrom I w C α = cwlogFrom I w C α := by
  induction α generalizing C with
  | nil => rfl
  | cons ℓ α ih =>
    cases ℓ <;>
    · simp only [wlogFrom, cwlogFrom, Impl.step_eq_cstep]
      split <;> simp_all

lemma writesTo_eq [DecidableEq κ] (w : P → L → Option (κ × ℕ)) (α : List (Label P A)) (k : κ) :
    writesTo I w α k =
      (cwlogFrom I w I.initCfg α).filterMap (fun e => if e.1 = k then some e.2 else none) := by
  rw [writesTo, wlogFrom_eq_cwlogFrom]

end CLog

/-! ## The counterexample -/

open Lean Elab Tactic Meta in
/-- Prove a decidable proposition `P` by `of_decide_eq_true rfl`, where the definitional unfolding
`decide P ≡ true` is checked by the kernel only (as in `decide +kernel`), but `P` may contain free
variables, as long as the evaluation never inspects them. Sound: the kernel checks the proof term
when the declaration is added. -/
elab "kernel_decide_fvar" : tactic => do
  let g ← getMainGoal
  let P ← g.getType
  let inst ← synthInstance (mkApp (mkConst ``Decidable) P)
  g.assign (mkApp3 (mkConst ``of_decide_eq_true) P inst
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)))

/-- A complete `MaxUpdate(left, v)` of process `A = 0` run solo. -/
def soloUpd (v : ℕ) : List (Lbl 4) :=
  [.inv 0 (.upd0 v)] ++ List.replicate 10 (.tau 0) ++ [.ret 0 (0, 0)]

/-- The counterexample execution (see the module docstring); `B`'s `WriteMax(MR_right, 3)` is
step `46`, `Q`'s write of `MA_0.right` step `49`, `S`'s `MaxScan(MA_1)` step `52` and its return
step `56`. -/
def αex : List (Lbl 4) :=
  soloUpd 4 ++ soloUpd 8 ++ soloUpd 12 ++
  [.inv 2 .scan, .tau 2, .tau 2] ++
  [.inv 0 (.upd0 16), .tau 0] ++
  [.inv 3 .scan, .tau 3, .tau 3, .tau 3] ++
  [.inv 1 (.upd1 3), .tau 1] ++
  [.tau 2, .tau 2, .tau 2] ++
  List.replicate 6 (.tau 3) ++ [.ret 3 (16, 0)]

/-- **Lemma 3.3 of the paper is false.** For every helping period `X` there is an execution `α`
of Algorithm 1 (`n = 4`, `m = 16 = n²`), `4`-bounded-increment for `MR_left` and `MR_right`
(Definition 2.1), in which

* step `w` is `B`'s `WriteMax(MR_right, 3)` (line 4 of `MaxUpdate(right, 3)`),
* linearization rule (3) places this `MaxUpdate` at step `s`,
* linearization rule (1) places the `MaxScan` of `S` returning at step `e` at step `t`,
* `S` returns the view `(16, 0)`, and `s < t`.

So rules (1)–(3) order `MaxUpdate(right, 3)` before a `MaxScan` returning right component
`0 < 3`, which the sequential specification forbids (`scan_right_ge`). -/
theorem lemma_3_3_false (X : ℕ) :
    ∃ (α : List (Lbl 4)) (w s t e : ℕ),
      (alg1 4 16 X).Valid α ∧ BIExec 4 16 X 4 α ∧
      StepAt 16 X α w 1 (· == .wm true 3) ∧ Rule3Point 16 X α true w s ∧
      Rule1Point 16 X α t e ∧ α[e]? = some (.ret 3 (16, 0)) ∧ s < t := by
  refine ⟨αex, 46, 49, 52, 56, ?_, ?_, ?_, ?_, ?_, rfl, by decide⟩
  · exact Impl.valid_of_crun _ (by kernel_decide_fvar)
  · intro sd
    rw [writesTo_eq (alg1 4 16 X), boundedIncr_iff_stepBounded]
    unfold StepBounded
    revert sd
    kernel_decide_fvar
  all_goals kernel_decide_fvar

end Podc.LongLivedSnapshotsPolylog.Counterexample
