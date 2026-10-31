import Mathlib
import Podc.Computability.Distributed.SharedMemory.Persistent.Model

/-!
# The endurance-oblivious counter (Figure 1 of Liu–Golab, PODC 2022)

The round-robin fetch-and-increment counter of Figure 1, as an algorithm of the persistent
memory model `Cslib.SharedMemory.Persistent` (words behind a volatile write-back cache).

```
Persistent shared variables: A[0..k-1], each initially 0
Procedure Fetch-And-Increment()
 1 iter ← A[k-1]
 2 Flush(&A[k-1])
 3 index ← 0
 4 while true do
 5   if CAS(&A[index], iter, iter+1) = true then
 6     Flush(&A[index])
 7     return index + iter × k
 8   else
 9     Flush(&A[index])
10     index ← (index + 1) mod k
11     if index = 0 then
12       iter ← A[k-1]
13       Flush(&A[k-1])
```

Local states (`CL k`) are program counters carrying the local variables: `rd` (line 1, also
line 12), `fl iter` (line 2, also line 13; then `index ← 0`), `cas iter idx` (line 5),
`flS iter idx` (line 6), `ret iter idx` (line 7), `flF iter idx` (lines 9–11).

Words hold natural numbers (unbounded words: `b = ∞`); the `b`-bit version is discussed in the
README. The implemented object is `faiObj`, a fetch-and-increment counter over `ℕ` whose only
operation is FAI.

`stair n` is the array state after `n` increments in round-robin order (the representation
invariant of Section 3): `stair n i = ⌈(n - i) / k⌉`, written `(n + k - 1 - i) / k`.
-/

namespace Podc.WearLeveling

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.Persistent

/-- The fetch-and-increment counter (only operation: FAI, returning the old value). -/
abbrev faiObj : ObjSpec where
  State := ℕ
  Op := Unit
  Resp := ℕ
  init := 0
  δ q _ := (q + 1, q)

lemma faiObj_runOps (q : ℕ) (os : List Unit) : faiObj.runOps q os = q + os.length := by
  induction os generalizing q with
  | nil => rfl
  | cons o os ih =>
    show faiObj.runOps (q + 1) os = _
    rw [ih]; simp; omega

variable (k : ℕ) [NeZero k]

lemma k_pos : 0 < k := NeZero.pos k

/-- The last index `k - 1`. -/
def last : Fin k := ⟨k - 1, by have := k_pos k; omega⟩

@[simp] lemma last_val : (last k).val = k - 1 := rfl

/-- Program counters (with local variables) of Figure 1. -/
inductive CL (k : ℕ) where
  /-- Line 1 / line 12: `iter ← A[k-1]`. -/
  | rd
  /-- Line 2 / line 13: `Flush(&A[k-1])`, then `index ← 0`. -/
  | fl (iter : ℕ)
  /-- Line 5: `CAS(&A[index], iter, iter + 1)`. -/
  | cas (iter : ℕ) (idx : Fin k)
  /-- Line 6: `Flush(&A[index])` after a successful CAS. -/
  | flS (iter : ℕ) (idx : Fin k)
  /-- Line 7: `return index + iter × k`. -/
  | ret (iter : ℕ) (idx : Fin k)
  /-- Lines 9–11: `Flush(&A[index])` after a failed CAS, then advance `index`. -/
  | flF (iter : ℕ) (idx : Fin k)

variable {k} in
/-- Lines 10–11: the next program counter after a failed CAS and its flush. -/
def nextPC (it : ℕ) (idx : Fin k) : CL k :=
  if h : idx.val + 1 < k then .cas it ⟨idx.val + 1, h⟩ else .rd

lemma nextPC_of_lt {it : ℕ} {idx : Fin k} (h : idx.val + 1 < k) :
    nextPC it idx = .cas it ⟨idx.val + 1, h⟩ := dite_eq_left h

lemma nextPC_of_not_lt {it : ℕ} {idx : Fin k} (h : ¬ idx.val + 1 < k) :
    nextPC it idx = .rd := dite_eq_right h

/-- The algorithm of Figure 1. -/
@[reducible] def counter : Alg faiObj k ℕ where
  L := CL k
  init := fun _ => 0
  start := fun _ => .rd
  act
    | .rd => .read (last k) .fl
    | .fl it => .flush (last k) (.cas it 0)
    | .cas it idx => .cas idx it (it + 1) (fun b => if b then .flS it idx else .flF it idx)
    | .flS it idx => .flush idx (.ret it idx)
    | .ret it idx => .ret (idx.val + it * k)
    | .flF it idx => .flush idx (nextPC it idx)

/-! ### The staircase (representation invariant) -/

/-- The state of the array after `n` round-robin increments. -/
def stair (n : ℕ) (i : Fin k) : ℕ := (n + k - 1 - i.val) / k

variable {k}

lemma le_stair_iff (c n : ℕ) (i : Fin k) : c ≤ stair k n i ↔ c * k + i.val < n + k := by
  have hk := k_pos k
  have hi := i.isLt
  unfold stair
  rw [Nat.le_div_iff_mul_le hk]
  omega

lemma stair_le_iff (c n : ℕ) (i : Fin k) : stair k n i ≤ c ↔ n ≤ c * k + i.val := by
  have hk := k_pos k
  have hi := i.isLt
  unfold stair
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hk, Nat.succ_mul]
  omega

lemma stair_zero (i : Fin k) : stair k 0 i = 0 := by
  have := (stair_le_iff 0 0 i).2 (by omega); omega

lemma stair_mono {m n : ℕ} (h : m ≤ n) (i : Fin k) : stair k m i ≤ stair k n i := by
  rw [le_stair_iff]
  have := (le_stair_iff (stair k m i) m i).1 le_rfl
  omega

lemma stair_anti (n : ℕ) {i j : Fin k} (h : i ≤ j) : stair k n j ≤ stair k n i := by
  rw [le_stair_iff]
  have := (le_stair_iff (stair k n j) n j).1 le_rfl
  have : i.val ≤ j.val := h
  omega

lemma stair_last (n : ℕ) : stair k n (last k) * k ≤ n := by
  have := (le_stair_iff (stair k n (last k)) n (last k)).1 le_rfl
  simp only [last_val] at this
  have := k_pos k
  omega

lemma stair_pos_self (it : ℕ) (i : Fin k) : stair k (it * k + i.val) i = it := by
  apply le_antisymm
  · rw [stair_le_iff]
  · rw [le_stair_iff]; have := k_pos k; omega

lemma stair_succ_self (it : ℕ) (i : Fin k) : stair k (it * k + i.val + 1) i = it + 1 := by
  have := k_pos k
  apply le_antisymm
  · rw [stair_le_iff, Nat.succ_mul]; omega
  · rw [le_stair_iff, Nat.succ_mul]; omega

lemma stair_succ_ne (it : ℕ) {i j : Fin k} (hj : j ≠ i) :
    stair k (it * k + i.val + 1) j = stair k (it * k + i.val) j := by
  have hk := k_pos k
  have key : ∀ c, c * k + j.val ≠ it * k + i.val + k := by
    intro c hc
    have h1 : (c * k + j.val) % k = j.val := by simp [Nat.mul_add_mod_of_lt j.isLt]
    have h2 : (it * k + i.val + k) % k = i.val := by
      rw [show it * k + i.val + k = (it + 1) * k + i.val by rw [Nat.succ_mul]; omega]
      simp [Nat.mul_add_mod_of_lt i.isLt]
    exact hj (Fin.ext (by rw [← h1, ← h2, hc]))
  apply le_antisymm
  · have := (le_stair_iff (stair k (it * k + i.val + 1) j) _ j).1 le_rfl
    rw [le_stair_iff]
    have := key (stair k (it * k + i.val + 1) j)
    omega
  · have := (le_stair_iff (stair k (it * k + i.val) j) _ j).1 le_rfl
    rw [le_stair_iff]; omega

/-- The staircase after one more increment, at position `it * k + i`. -/
lemma stair_succ (it : ℕ) (i : Fin k) :
    stair k (it * k + i.val + 1) = Function.update (stair k (it * k + i.val)) i (it + 1) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [stair_succ_self]
  · rw [Function.update_of_ne hj, stair_succ_ne it hj]

/-- Every `n` is a position `it * k + i`. -/
lemma exists_pos (n : ℕ) : ∃ it, ∃ i : Fin k, n = it * k + i.val :=
  ⟨n / k, ⟨n % k, Nat.mod_lt _ (k_pos k)⟩, by simp [Nat.div_add_mod']⟩

/-! ### Step equations -/

section StepEqs

variable {P : Type} [DecidableEq P] (W : Wear k ℕ) {C : Cfg (counter k) P} {p : P} {a : ℕ}
  {o : Unit} {it : ℕ} {idx : Fin k}

open Alg

lemma step_rd (hp : C.ts p = .run a o CL.rd) :
    step1 W C (.step p) =
      ({ C with ts := (Function.update C.ts p (.run a o (CL.fl (C.cache (last k))))) }, []) := by
  simp [step1, hp, counter]

lemma step_fl (hp : C.ts p = .run a o (CL.fl it)) :
    step1 W C (.step p) =
      ({ writeBack W C (last k) with ts := (Function.update C.ts p (.run a o (CL.cas it 0))) },
        []) := by
  simp [step1, hp, counter]

lemma step_cas_succ (hp : C.ts p = .run a o (CL.cas it idx)) (hc : C.cache idx = it) :
    step1 W C (.step p) =
      ({ C with cache := Function.update C.cache idx (it + 1),
                dirty := Function.update C.dirty idx true,
                ts := (Function.update C.ts p (.run a o (CL.flS it idx))) }, []) := by
  simp [step1, hp, counter, hc]

lemma step_cas_fail (hp : C.ts p = .run a o (CL.cas it idx)) (hc : C.cache idx ≠ it) :
    step1 W C (.step p) =
      ({ C with ts := (Function.update C.ts p (.run a o (CL.flF it idx))) }, []) := by
  simp [step1, hp, counter, hc]

lemma step_flS (hp : C.ts p = .run a o (CL.flS it idx)) :
    step1 W C (.step p) =
      ({ writeBack W C idx with ts := (Function.update C.ts p (.run a o (CL.ret it idx))) },
        []) := by
  simp [step1, hp, counter]

lemma step_ret (hp : C.ts p = .run a o (CL.ret it idx)) :
    step1 W C (.step p) =
      ({ C with ts := (Function.update C.ts p .idle) }, [.res a (idx.val + it * k)]) := by
  simp [step1, hp, counter]

lemma step_flF (hp : C.ts p = .run a o (CL.flF it idx)) :
    step1 W C (.step p) =
      ({ writeBack W C idx with ts := (Function.update C.ts p (.run a o (nextPC it idx))) },
        []) := by
  simp [step1, hp, counter]

lemma step_idle (hp : C.ts p = .idle) : step1 W C (.step p) = (C, []) := by
  simp [step1, hp]

lemma inv_idle (hp : C.ts p = .idle) (o : Unit) :
    step1 W C (.inv p o) =
      ({ C with ts := Function.update C.ts p (.run C.cnt o CL.rd), cnt := C.cnt + 1 },
        [.inv C.cnt p o]) := by
  simp [step1, hp, counter]

end StepEqs

end Podc.WearLeveling
