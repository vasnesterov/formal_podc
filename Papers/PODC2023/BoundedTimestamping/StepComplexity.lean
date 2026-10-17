import Papers.PODC2023.BoundedTimestamping.Alg
import Podc.SharedMemory.Potential

/-!
# Constant step complexity of the MTS algorithm (Lemma 12)

[BJW23]: Bashari, Jamadi, Woelfel, *Efficient Bounded Timestamping from Standard Synchronization
Primitives*, PODC 2023.

Lemma 12 of [BJW23]: `updateTS()` and `isEarlier()` have constant step complexity. We prove
this for the encoding `alg n κ` of Figures 1–2 (`Alg.lean`) with the explicit bound

  `stepBound κ = 2κ + 107`,

independent of `n` (`κ` is the constant of line 23). It is computed from the call graph,
counting one step per shared-memory access:

* `helpUpdateTS`: at most 3 iterations of lines 9, 10, 12, 13, i.e. `≤ 12` steps;
* `helpActiveCluster`: `conditionalReset` makes at most 2 iterations of lines 26, 29, 30, 33
  (`≤ 8` steps), followed by exactly `κ` steps of the `helpMoveTS` coroutine: `≤ 8 + κ`;
* `isEarlier(x, y)`: lines 35–36 (2), possibly `helpUpdateTS(x)` (12), lines 37–38 (2),
  possibly `helpUpdateTS(y)` (12), `helpActiveCluster` (`8 + κ`), lines 40–42 (3), then at most
  6 iterations of lines 44, 45, 46, 50, 51 (30) and lines 55–56 (2), or exit via line 48:
  `≤ 71 + κ` steps (`opCost κ (.ie x y)`);
* `helpSystem`: line 16, possibly a nested `isEarlier` (`71 + κ`) and line 19, then
  `helpActiveCluster` (`8 + κ`): `≤ 81 + 2κ` steps;
* `updateTS()`: lines 2–3 (2), two `helpUpdateTS` calls (24), `helpSystem` (`81 + 2κ`):
  `≤ 107 + 2κ` steps (`opCost κ (.upd p)`).

The proof is a potential `pot κ : Loc → ℕ` (an upper bound on the remaining number of accesses,
determined by the program counter, the loop counters `hit`, `rit`, `eit` and the return
addresses `hret`, `cret`, `enested`; it does not depend on the `helpMoveTS` coroutine state
`mv`, since `PC.K s` performs exactly `s` coroutine steps whatever the coroutine does) that
strictly decreases at every base-object access (`pot_lt`). Consequences: `lemma12` (step
bound) and `alg_waitFree` (wait-freedom).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.BoundedTS

open Cslib.SharedMemory

section StepComplexity

variable {n : ℕ} (κ : ℕ)

/-- Remaining steps after `isEarlier` returns: line 19 and `helpActiveCluster` if nested in
`helpSystem`, nothing otherwise. -/
def retECost (nested : Bool) : ℕ := if nested then 9 + κ else 0

/-- Remaining steps after `helpActiveCluster` returns (to `updateTS` or to line 40). -/
def retCCost (r : CRet) (nested : Bool) : ℕ :=
  match r with
  | .U => 0
  | .E => 35 + retECost κ nested

/-- Steps of `helpSystem` (from line 16), including the following `helpActiveCluster`. -/
def sysCost : ℕ := 81 + 2 * κ

/-- Remaining steps after `helpUpdateTS` returns. -/
def retHCost (r : HRet) (nested : Bool) : ℕ :=
  match r with
  | .U => 12 + sysCost κ
  | .S => sysCost κ
  | .Ex => 57 + κ + retECost κ nested
  | .Ey => 43 + κ + retECost κ nested

/-- The potential: an upper bound on the number of base-object accesses a process still
performs before its current operation returns. -/
def pot (l : Loc) : ℕ :=
  match l.pc with
  | .idle => 0
  | .done _ => 0
  | .U2 => 26 + sysCost κ
  | .U3 => 25 + sysCost κ
  | .H9 => 4 + 4 * (2 - l.hit) + retHCost κ l.hret l.enested
  | .H10 => 3 + 4 * (2 - l.hit) + retHCost κ l.hret l.enested
  | .H12 => 2 + 4 * (2 - l.hit) + retHCost κ l.hret l.enested
  | .H13 => 1 + 4 * (2 - l.hit) + retHCost κ l.hret l.enested
  | .S16 => sysCost κ
  | .S19 => 9 + κ
  | .R26 => 4 + (if l.rit = 0 then 4 else 0) + κ + retCCost κ l.cret l.enested
  | .R29 => 3 + (if l.rit = 0 then 4 else 0) + κ + retCCost κ l.cret l.enested
  | .R30 => 2 + (if l.rit = 0 then 4 else 0) + κ + retCCost κ l.cret l.enested
  | .R33 => 1 + (if l.rit = 0 then 4 else 0) + κ + retCCost κ l.cret l.enested
  | .K s => max s 1 + retCCost κ l.cret l.enested
  | .E35 => 71 + κ + retECost κ l.enested
  | .E36 => 70 + κ + retECost κ l.enested
  | .E37 => 57 + κ + retECost κ l.enested
  | .E38 => 56 + κ + retECost κ l.enested
  | .E40 => 35 + retECost κ l.enested
  | .E41 => 34 + retECost κ l.enested
  | .E42 => 33 + retECost κ l.enested
  | .E44 => 7 + 5 * (5 - l.eit) + retECost κ l.enested
  | .E45 => 6 + 5 * (5 - l.eit) + retECost κ l.enested
  | .E46 => 5 + 5 * (5 - l.eit) + retECost κ l.enested
  | .E50 => 4 + 5 * (5 - l.eit) + retECost κ l.enested
  | .E51 => 3 + 5 * (5 - l.eit) + retECost κ l.enested
  | .E48 => 1 + retECost κ l.enested
  | .E55 => 2 + retECost κ l.enested
  | .E56 => 1 + retECost κ l.enested

/-- Step bound of an operation: `updateTS()` at most `2κ + 107`, `isEarlier` at most
`κ + 71` base-object accesses. -/
def opCost : MOp n → ℕ
  | .upd _ => 107 + 2 * κ
  | .ie _ _ => 71 + κ

/-- **The constant of Lemma 12**: every operation performs at most `2κ + 107` base-object
accesses (independent of `n`). -/
def stepBound : ℕ := 2 * κ + 107

lemma opCost_le (o : MOp n) : opCost κ o ≤ stepBound κ := by
  cases o <;> simp [opCost, stepBound] <;> omega

variable [NeZero n]

@[simp] lemma pot_retH (l : Loc) : pot κ (retH l) = retHCost κ l.hret l.enested := by
  cases h : l.hret <;> simp [retH, h, pot, retHCost, callH, callC, sysCost, retCCost]
  all_goals omega

@[simp] lemma pot_retC (l : Loc) : pot κ (retC l) = retCCost κ l.cret l.enested := by
  cases h : l.cret <;> simp [retC, h, pot, retCCost]

@[simp] lemma pot_startK (l : Loc) : pot κ (startK κ l) = κ + retCCost κ l.cret l.enested := by
  unfold startK; split_ifs with h
  · simp [h]
  · simp [pot]; omega

@[simp] lemma pot_callC (l : Loc) (r : CRet) :
    pot κ (callC l r) = 8 + κ + retCCost κ r l.enested := by
  simp [callC, pot]

@[simp] lemma pot_callH (l : Loc) (i : ℕ) (r : HRet) :
    pot κ (callH l i r) = 12 + retHCost κ r l.enested := by
  simp [callH, pot]

@[simp] lemma pot_afterS (l : Loc) : pot κ (afterS n l) = 8 + κ := by
  simp [afterS, retCCost]

@[simp] lemma pot_retE (l : Loc) (r : Option Bool) : pot κ (retE l r) = retECost κ l.enested := by
  unfold retE; split_ifs with h <;> simp [pot, retECost, h]

/-- Every step of the `helpMoveTS` coroutine continues with `cont` of some coroutine state. -/
lemma moveAct_cont {p : Fin n} {m : MoveSt} {cont : MoveSt → Loc} {i : Obj n}
    {o : (Base n i).Op} {k : (Base n i).Resp → Loc} (h : moveAct n p m cont = .access i o k)
    (x : (Base n i).Resp) : ∃ m', k x = cont m' := by
  unfold moveAct at h
  split at h <;> cases h <;> exact ⟨_, rfl⟩

/-- The potential strictly decreases at every base-object access. -/
lemma pot_lt (p : Fin n) (l : Loc) (i : Obj n) (o : (Base n i).Op) (k : (Base n i).Resp → Loc)
    (hact : act n κ p l = .access i o k) (x : (Base n i).Resp) : pot κ (k x) < pot κ l := by
  cases hpc : l.pc with
  | K s =>
    simp only [act, hpc] at hact
    obtain ⟨m', hm'⟩ := moveAct_cont hact x
    rw [hm']
    split_ifs <;> (try simp only [pot_retC]) <;> simp [pot, hpc]
    all_goals omega
  | _ =>
    simp only [act, hpc, reduceCtorEq] at hact
    try (cases hact; try dsimp only)
    all_goals
      (repeat' split) <;>
      (try simp only [pot_retH, pot_startK, pot_callC, pot_callH, pot_afterS, pot_retE]) <;>
      simp [pot, hpc, retECost, retCCost, retHCost, sysCost] <;> (try split_ifs) <;> omega

/-- The potential right after an invocation is at most the cost of the operation. -/
lemma pot_invoke (l : Loc) (o : MOp n) : pot κ (invoke n l o) ≤ opCost κ o := by
  cases o <;> simp [invoke, pot, opCost, retECost, sysCost]
  all_goals omega

/-- **Lemma 12 of [BJW23]**, per operation: in every execution, after `p` invokes `o`, `p`
performs at most `opCost κ o` base-object accesses before it returns (`κ + 71` for
`isEarlier(x, y)`, `2κ + 107` for `updateTS()`); `γ` is any continuation not containing a
response of `p`. -/
theorem lemma12_opCost {α γ : List (Label (Fin n) (mtsObj n))} {p : Fin n} {o : MOp n}
    (hv : (alg n κ).Valid (α ++ .inv p o :: γ)) (hret : ∀ r, Label.ret p r ∉ γ) :
    γ.countP (Label.isTauOf p) ≤ opCost κ o := by
  obtain ⟨l, h⟩ := (alg n κ).tauSteps_le_potential_invoke (fun _ l => pot κ l)
    (fun p l i o k hact x => pot_lt κ p l i o k hact x) hv hret
  exact h.trans (pot_invoke κ l o)

/-- **Lemma 12 of [BJW23]** (constant step complexity): in every execution, after `p` invokes
an operation `o` (`updateTS()` or `isEarlier(x, y)`), `p` performs at most
`stepBound κ = 2κ + 107` base-object accesses before it returns (`γ` is any continuation
not containing a response of `p`); the bound does not depend on `n`. -/
theorem lemma12 {α γ : List (Label (Fin n) (mtsObj n))} {p : Fin n} {o : MOp n}
    (hv : (alg n κ).Valid (α ++ .inv p o :: γ)) (hret : ∀ r, Label.ret p r ∉ γ) :
    γ.countP (Label.isTauOf p) ≤ stepBound κ :=
  (lemma12_opCost κ hv hret).trans (opCost_le κ o)

/-- **Wait-freedom** of the MTS algorithm (a consequence of Lemma 12 of [BJW23]). -/
theorem alg_waitFree : (alg n κ).WaitFree :=
  (alg n κ).waitFree_of_potential (fun _ l => pot κ l)
    (fun p l i o k hact x => pot_lt κ p l i o k hact x)

end StepComplexity

end Cslib.SharedMemory.BoundedTS
