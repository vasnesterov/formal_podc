import Papers.PODC2016.ComplexityHierarchy.RacingCounters
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# `n`-consensus from one location with `read` and `set-bit` (Theorem 3.3 of [EGSZ16])

A single memory location storing a natural number (a bit string), initially `0`, supporting
`read()` and `set-bit(x)` (set bit `x` to `1`), simulates an unbounded `m`-component counter for
processes `Fin N`: the location is partitioned into blocks of `m · N` bits; process `i` increments
`c_v` by setting bit `v · N + i` of block `b + 1`, where `b` is the number of times it previously
incremented `c_v` (`bitIdx`). The count of `c_v` is the number of set bits belonging to `v`
(`bitCnt`), so a single `read()` is a scan. This is the paper's construction with `n² = m · N`
(the paper has `m = N = n`).

Deviation: `set-bit(x)` returns the dummy acknowledgement `0`.
-/

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory

/-- Operations of a location supporting `read` and `set-bit`. -/
inductive BitOp where
  /-- Return the stored value. -/
  | read
  /-- Set bit `x` of the stored value to `1`. -/
  | setBit (x : ℕ)

/-- A memory location storing a natural number (bit string), supporting `read()` and
`set-bit(x)` (the latter acknowledged by the dummy response `0`). -/
abbrev bitLoc : ObjSpec where
  State := ℕ
  Op := BitOp
  Resp := ℕ
  init := 0
  δ s o := match o with
    | .read => (s, s)
    | .setBit x => (s ||| 2 ^ x, 0)

variable {m N : ℕ}

/-- The bit set by process `i` for its `(k+1)`-st increment of `c_v`: bit `v · N + i` of block
`k + 1` (blocks of `m · N` bits). -/
def bitIdx (m N : ℕ) (k : ℕ) (v : Fin m) (i : Fin N) : ℕ := (k + 1) * (m * N) + (v * N + i)

lemma lt_block (v : Fin m) (i : Fin N) : (v : ℕ) * N + i < m * N := by
  have := v.2; have := i.2
  calc (v : ℕ) * N + i < v * N + N := by omega
    _ = (v + 1) * N := (Nat.succ_mul _ _).symm
    _ ≤ m * N := Nat.mul_le_mul_right _ (by omega)

lemma divmod_inj {M a b r r' : ℕ} (hr : r < M) (hr' : r' < M) (h : a * M + r = b * M + r') :
    a = b ∧ r = r' := by
  have h1 : (a * M + r) / M = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr]; simp
  have h2 : (b * M + r') / M = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr']; simp
  rw [h] at h1; rw [h1] at h2; subst h2; omega

lemma bitIdx_inj {k k' : ℕ} {v v' : Fin m} {i i' : Fin N}
    (h : bitIdx m N k v i = bitIdx m N k' v' i') : k = k' ∧ v = v' ∧ i = i' := by
  obtain ⟨h1, h2⟩ := divmod_inj (lt_block v i) (lt_block v' i') h
  obtain ⟨h3, h4⟩ := divmod_inj i.2 i'.2 h2
  exact ⟨by omega, Fin.ext h3, Fin.ext h4⟩

lemma lt_bitIdx (k : ℕ) (v : Fin m) (i : Fin N) : k < bitIdx m N k v i := by
  have : 1 ≤ m * N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := v.2; omega)
    (by have := i.2; omega))
  have := Nat.le_mul_of_pos_right (k + 1) this
  unfold bitIdx
  omega

/-- The count of `c_v` represented by the bit string `s`: the number of set bits belonging to
`v`. -/
def bitCnt (N : ℕ) (s : ℕ) (v : Fin m) : ℕ :=
  ∑ i : Fin N, ((Finset.range s).filter (fun k => s.testBit (bitIdx m N k v i))).card

/-- Representation invariant: the set bits are exactly those of the increments performed so far
(`c i v` = number of increments of `c_v` by process `i`). -/
def BitInv (s : ℕ) (c : Fin N → Fin m → ℕ) : Prop :=
  ∀ j, s.testBit j = true ↔ ∃ k v i, j = bitIdx m N k v i ∧ k < c i v

lemma bitCnt_eq {s : ℕ} {c : Fin N → Fin m → ℕ} (h : BitInv s c) (v : Fin m) :
    bitCnt N s v = ∑ i, c i v := by
  unfold bitCnt
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Finset.range s).filter (fun k => s.testBit (bitIdx m N k v i)) =
      Finset.range (c i v) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hb⟩
      obtain ⟨k', v', i', he, hk⟩ := (h _).1 hb
      obtain ⟨rfl, rfl, rfl⟩ := bitIdx_inj he
      exact hk
    · intro hk
      have hb : s.testBit (bitIdx m N k v i) = true := (h _).2 ⟨k, v, i, rfl, hk⟩
      refine ⟨?_, hb⟩
      have h1 := Nat.ge_two_pow_of_testBit hb
      have h2 := Nat.lt_two_pow_self (n := bitIdx m N k v i)
      have h3 := lt_bitIdx k v i
      omega
  rw [this, Finset.card_range]

lemma bitInv_inc {s : ℕ} {c : Fin N → Fin m → ℕ} (h : BitInv s c) (p : Fin N) (v : Fin m) :
    BitInv (s ||| 2 ^ bitIdx m N (c p v) v p)
      (Function.update c p (Function.update (c p) v (c p v + 1))) := by
  intro j
  simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, h j]
  constructor
  · rintro (⟨k, v', i, rfl, hk⟩ | rfl)
    · refine ⟨k, v', i, rfl, ?_⟩
      by_cases hi : i = p
      · subst hi; by_cases hv : v' = v
        · subst hv; simp; omega
        · simp [Function.update_of_ne hv]; exact hk
      · simp [Function.update_of_ne hi]; exact hk
    · exact ⟨c p v, v, p, rfl, by simp⟩
  · rintro ⟨k, v', i, rfl, hk⟩
    by_cases hi : i = p
    · subst hi
      by_cases hv : v' = v
      · subst hv
        simp only [Function.update_self] at hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
        · exact Or.inl ⟨k, v', i, rfl, hk⟩
        · exact Or.inr (by rw [hk])
      · simp only [Function.update_self, Function.update_of_ne hv] at hk
        exact Or.inl ⟨k, v', i, rfl, hk⟩
    · simp only [Function.update_of_ne hi] at hk
      exact Or.inl ⟨k, v', i, rfl, hk⟩

/-- The counter simulation of Theorem 3.3 (`set-bit`) for processes `Fin N`. -/
def bitSim (m N : ℕ) : CounterSim m (Fin N) where
  B := bitLoc
  init := 0
  incOp i v k := .setBit (bitIdx m N k v i)
  scanOp := .read
  decode := bitCnt N
  cnt := bitCnt N
  Inv := BitInv
  inv_init j := by simp
  cnt_init := by funext v; simp [bitCnt]
  inv_inc _ _ p v h := bitInv_inc h p v
  cnt_inc s c p v h := by
    funext u
    change bitCnt N (s ||| 2 ^ bitIdx m N (c p v) v p) u = _
    rw [bitCnt_eq (bitInv_inc h p v)]
    rw [show bitCnt N s = fun u => ∑ i, c i u from funext (bitCnt_eq h)]
    have hterm : ∀ i, Function.update c p (Function.update (c p) v (c p v + 1)) i u =
        c i u + if i = p ∧ u = v then 1 else 0 := by
      intro i
      by_cases hi : i = p
      · subst hi; by_cases hu : u = v
        · subst hu; simp
        · simp [hu]
      · simp [hi]
    simp only [hterm, Finset.sum_add_distrib]
    by_cases hu : u = v
    · subst hu; simp [Finset.sum_ite_eq']
    · simp [hu]
  scan_state _ := rfl
  scan_resp _ _ _ := rfl

/-- Theorem 3.3 of [EGSZ16] (`set-bit`, general form): obstruction-free `m`-valued consensus among
`N` processes can be solved with a single location supporting only `read()` and `set-bit(x)`,
initially `0`. -/
theorem theorem_3_3_setBit_general (m : ℕ) [NeZero m] (N : ℕ) :
    ∃ (L : Type) (I : Impl (taskObj (Fin m) (Fin m)) (fun _ : Unit => bitLoc) (Fin N) L),
      I.memInit () = 0 ∧ (∀ p v, I.allowed p v) ∧ I.Solves (consensus (Fin N) (Fin m)) ∧
        I.ObstructionFree :=
  ⟨RacingLoc m, racing (bitSim m N) N, rfl, fun _ _ => trivial,
    racing_solves (by simp), racing_obstructionFree (by simp)⟩

/-- Theorem 3.3 of [EGSZ16] (`set-bit`): `n`-consensus (obstruction-free `n`-valued consensus
among `n` processes) can be solved using a single memory location that supports only `read()` and
`set-bit(x)`, initially `0`. -/
theorem theorem_3_3_setBit (n : ℕ) [NeZero n] :
    ∃ (L : Type) (I : Impl (taskObj (Fin n) (Fin n)) (fun _ : Unit => bitLoc) (Fin n) L),
      I.memInit () = 0 ∧ (∀ p v, I.allowed p v) ∧ I.Solves (consensus (Fin n) (Fin n)) ∧
        I.ObstructionFree :=
  theorem_3_3_setBit_general n n

end Cslib.SharedMemory.ComplexityHierarchy
