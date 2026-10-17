import Papers.PODC2025.UniqueIDsBoundedRegisters.AlgInv

/-!
# Algorithm 1: the bound `n · m` is tight

A single process calling `get()` sequentially `n · m + 1` times receives the identifier `0`
twice (calls number `0` and `n · m`): `alg_not_correctUpTo_succ`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.UniqueIDs

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

namespace Tight

variable {n m : ℕ} [NeZero n] [NeZero m]

/-- The register `R_{i+1}` chosen by the next `get()` (Algorithm 1, `d = n`). -/
def idx (M : Fin (n + 1) → Fin m) : Fin n := ⟨(M 0).val % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- The identifier returned by the next `get()`. -/
def val (M : Fin (n + 1) → Fin m) : ℕ := (idx M).val * m + (M (idx M).succ).val

/-- The memory after the next `get()`. -/
def nxt (M : Fin (n + 1) → Fin m) : Fin (n + 1) → Fin m :=
  Function.update (Function.update M 0 (M 0 + 1)) (idx M).succ (M (idx M).succ + 1)

/-- The memory after `k` sequential `get()`s. -/
def memK : ℕ → Fin (n + 1) → Fin m
  | 0 => 0
  | k + 1 => nxt (memK k)

/-- The configuration after `k` sequential `get()`s. -/
def cfgK (k : ℕ) : ACfg P n m := ⟨fun _ => .idle, fun _ => none, memK k⟩

/-- Labels of the `k`-th `get()` of `p`. -/
def getL (p : P) (k : ℕ) : List (Label P uidObj) :=
  [.inv p (), .tau p, .tau p, .ret p (val (memK (n := n) (m := m) k))]

/-- `k` sequential `get()`s of `p`. -/
def seqL (p : P) : ℕ → List (Label P uidObj)
  | 0 => []
  | k + 1 => seqL p k ++ getL (n := n) (m := m) p k

lemma runFrom_getL (p : P) (k : ℕ) :
    (alg (P := P) n n m).runFrom (cfgK k) (getL (n := n) (m := m) p k) = some (cfgK (k + 1)) := by
  have hlt : (memK (n := n) (m := m) k 0).val % n < n := Nat.mod_lt _ (NeZero.pos n)
  simp [getL, Impl.runFrom, Impl.step, alg, cfgK, memK, nxt, val, idx, hlt]

lemma run_seqL (p : P) (k : ℕ) :
    (alg (P := P) n n m).run (seqL (n := n) (m := m) p k) = some (cfgK k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [seqL, Impl.run_append_of_eq _ ih, runFrom_getL]

lemma respsOf_seqL (p : P) (k : ℕ) :
    respsOf (seqL (n := n) (m := m) p k) p = (List.range k).map (fun j => val (memK (n := n) (m := m) j)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [seqL, ih, getL, List.range_succ]

lemma numInv_seqL (p : P) (k : ℕ) : invCount (seqL (n := n) (m := m) p k) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [seqL, ih, getL, Label.isInv]

lemma memK_spec (hnm : n ∣ m) (k : ℕ) :
    (memK (n := n) (m := m) k 0).val = k % m ∧
      ∀ i : Fin n, (memK (n := n) (m := m) k i.succ).val = Nat.count (fun s => s % n = i) k % m := by
  induction k with
  | zero => simp [memK]
  | succ k ih =>
    obtain ⟨h0, hi⟩ := ih
    have hidx : (idx (memK (n := n) (m := m) k)).val = k % n := by
      simp only [idx, h0, Nat.mod_mod_of_dvd _ hnm]
    refine ⟨?_, fun i => ?_⟩
    · simp only [memK, nxt]
      rw [Function.update_of_ne (Fin.succ_ne_zero _).symm, Function.update_self, Fin.val_add, h0]
      simp [Nat.add_mod]
    · simp only [memK, nxt]
      rw [Nat.count_succ]
      by_cases hj : i = idx (memK (n := n) (m := m) k)
      · subst hj
        rw [Function.update_self, Fin.val_add, hi, ite_eq_left hidx.symm]
        simp [Nat.add_mod]
      · have hne : k % n ≠ i := fun h => hj (Fin.ext (h.symm.trans hidx.symm))
        rw [Function.update_of_ne (fun h => hj (Fin.succ_injective _ h)),
          Function.update_of_ne (Fin.succ_ne_zero _), hi, ite_eq_right hne, add_zero]

lemma val_memK (hnm : n ∣ m) (k : ℕ) :
    val (memK (n := n) (m := m) k) = k % n * m + Nat.count (fun s => s % n = k % n) k % m := by
  obtain ⟨h0, hi⟩ := memK_spec (n := n) (m := m) hnm k
  have hidx : (idx (memK (n := n) (m := m) k)).val = k % n := by
    simp only [idx, h0, Nat.mod_mod_of_dvd _ hnm]
  simp only [val, hi, hidx]

end Tight

open Tight in
/-- **Tightness** of the bound `n · m` for Algorithm 1 (`d = n`, `n ∣ m`): with `n · m + 1`
calls, two `get()`s of the same process return the same identifier `0`. -/
theorem alg_not_correctUpTo_succ [Nonempty P] (n m : ℕ) [NeZero m] (hn : 1 ≤ n) (hnm : n ∣ m) :
    ¬ CorrectUpTo (alg (P := P) n n m) (n * m + 1) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨p⟩ := ‹Nonempty P›
  intro h
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hnm1 : 1 ≤ n * m := Nat.mul_pos (by omega) hm
  have hresp : ∀ j < n * m + 1, respOf (seqL (n := n) (m := m) p (n * m + 1)) (p, j) =
      some (val (memK (n := n) (m := m) j)) := by
    intro j hj
    simp [respOf, respsOf_seqL, hj]
  have hc : ∀ j < n * m + 1, Completed (seqL (n := n) (m := m) p (n * m + 1)) (p, j) := by
    intro j hj; simp [Completed, respsOf_seqL, hj]
  apply h (seqL (n := n) (m := m) p (n * m + 1)) ⟨_, run_seqL p _⟩ (by rw [numInv_seqL])
    (p, 0) (p, n * m) (hc 0 (by omega)) (hc _ (by omega)) (by simp; omega)
  rw [hresp 0 (by omega), hresp _ (by omega), val_memK hnm, val_memK hnm]
  have hcount : Nat.count (fun s => s % n = 0) (n * m) = m := by
    have := count_mod (fun s => s = 0) n m 0 (Nat.zero_le _)
    rw [add_zero, count_eq_self, count_eq_self, ite_eq_left (by omega),
      ite_eq_right (lt_irrefl 0)] at this
    simpa using this
  rw [Nat.count_zero, Nat.mul_mod_right, hcount]; simp

end Cslib.SharedMemory.UniqueIDs
