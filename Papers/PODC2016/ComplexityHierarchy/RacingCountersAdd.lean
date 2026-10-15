import Papers.PODC2016.ComplexityHierarchy.RacingCountersBounded
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# `n`-consensus from one location with `read` and `add` (Theorem 3.3 of [EGSZ16])

A single memory location storing an integer, initially `0`, supporting `read()` and `add(x)`
(`x ∈ ℤ`), simulates an `m`-component bounded counter with components in `{0, …, K-1}`: the stored
value is read in base `K` and its `i`-th least significant digit is the count of `c_i`; `add(K^i)`
increments `c_i`, `add(-K^i)` decrements it, and `read()` is a scan. As long as all counts stay in
`{0, …, K-1}` (which the algorithm of Lemma 3.2 guarantees, see `racing2_inv`), the value is
`∑ c_i K^i ≥ 0` (`AddInv`). With `K = 3n` and Lemma 3.2 this gives `n`-consensus.

Deviation: `add(x)` returns the dummy acknowledgement `0`.
-/

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory Finset

/-- Operations of a location supporting `read` and `add`. -/
inductive AddOp where
  /-- Return the stored value. -/
  | read
  /-- Add `x` to the stored value. -/
  | add (x : ℤ)

/-- A memory location storing an integer, supporting `read()` and `add(x)` (the latter
acknowledged by the dummy response `0`). -/
abbrev addLoc : ObjSpec where
  State := ℤ
  Op := AddOp
  Resp := ℤ
  init := 0
  δ s o := match o with
    | .read => (s, s)
    | .add x => (s + x, 0)

/-! ### Base-`K` digits -/

lemma sum_range_lt_pow {K : ℕ} {d : ℕ → ℕ} (hd : ∀ i, d i < K) (j : ℕ) :
    ∑ i ∈ range j, d i * K ^ i < K ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, pow_succ]
    have h1 : d j * K ^ j ≤ (K - 1) * K ^ j := Nat.mul_le_mul_right _ (by have := hd j; omega)
    have h2 : (K - 1) * K ^ j + K ^ j = K ^ j * K := by
      have : 1 ≤ K := by have := hd 0; omega
      rw [Nat.mul_comm (K ^ j) K]
      calc (K - 1) * K ^ j + K ^ j = (K - 1 + 1) * K ^ j := by rw [Nat.succ_mul]
        _ = K * K ^ j := by rw [Nat.sub_add_cancel this]
    omega

/-- Digit extraction: the `j`-th base-`K` digit of `∑_{i<m} d_i K^i` is `d_j`. -/
lemma digit_eq {K : ℕ} {d : ℕ → ℕ} (hd : ∀ i, d i < K) {m j : ℕ} (hj : j < m) :
    (∑ i ∈ range m, d i * K ^ i) / K ^ j % K = d j := by
  have hK : 0 < K := by have := hd 0; omega
  have hKj : 0 < K ^ j := Nat.pow_pos hK
  rw [← sum_range_add_sum_Ico _ (show j + 1 ≤ m by omega), sum_range_succ]
  have hdvd : K ^ (j + 1) ∣ ∑ i ∈ Ico (j + 1) m, d i * K ^ i :=
    dvd_sum fun i hi => Dvd.dvd.mul_left (pow_dvd_pow K (mem_Ico.1 hi).1) _
  obtain ⟨H, hH⟩ := hdvd
  rw [hH, pow_succ]
  have hlow := sum_range_lt_pow hd j
  have : ∑ i ∈ range j, d i * K ^ i + d j * K ^ j + K ^ j * K * H =
      ∑ i ∈ range j, d i * K ^ i + K ^ j * (d j + K * H) := by ring
  rw [this, Nat.add_mul_div_left _ _ hKj, Nat.div_eq_of_lt hlow, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd j)]

variable {m : ℕ}

/-- Extend `c : Fin m → ℕ` by `0`. -/
def extZ (c : Fin m → ℕ) (i : ℕ) : ℕ := if h : i < m then c ⟨i, h⟩ else 0

/-- The value encoding the counts `c` in base `K`. -/
def encode (K : ℕ) (c : Fin m → ℕ) : ℕ := ∑ i : Fin m, c i * K ^ (i : ℕ)

lemma encode_eq_range (K : ℕ) (c : Fin m → ℕ) :
    encode K c = ∑ i ∈ range m, extZ c i * K ^ i := by
  rw [encode, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun i _ => ?_
  simp [extZ]

lemma digit_encode {K : ℕ} {c : Fin m → ℕ} (hc : ∀ i, c i < K) (hK : 0 < K) (v : Fin m) :
    encode K c / K ^ (v : ℕ) % K = c v := by
  rw [encode_eq_range]
  have hd : ∀ i, extZ c i < K := by
    intro i; unfold extZ; split_ifs
    · exact hc _
    · exact hK
  rw [digit_eq hd v.2]
  simp [extZ]

lemma encode_inc (K : ℕ) (c : Fin m → ℕ) (v : Fin m) :
    encode K (Function.update c v (c v + 1)) = encode K c + K ^ (v : ℕ) := by
  unfold encode
  have : ∀ i, Function.update c v (c v + 1) i * K ^ (i : ℕ) =
      c i * K ^ (i : ℕ) + if i = v then K ^ (v : ℕ) else 0 := by
    intro i
    by_cases hi : i = v
    · subst hi; simp [Nat.succ_mul]
    · simp [hi]
  simp only [this, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte]

lemma encode_dec (K : ℕ) (c : Fin m → ℕ) (v : Fin m) (hv : 0 < c v) :
    encode K (Function.update c v (c v - 1)) + K ^ (v : ℕ) = encode K c := by
  have := encode_inc K (Function.update c v (c v - 1)) v
  simp only [Function.update_self, Function.update_idem] at this
  rw [Nat.sub_add_cancel hv, Function.update_eq_self] at this
  exact this.symm

/-! ### The simulation -/

/-- Representation invariant: the value is the base-`K` encoding of counts in `{0, …, K-1}`. -/
def AddInv (K : ℕ) (s : ℤ) : Prop := ∃ c : Fin m → ℕ, (∀ i, c i < K) ∧ s = (encode K c : ℤ)

/-- The counts represented by a value: its base-`K` digits. -/
def addCnt (K : ℕ) (s : ℤ) (v : Fin m) : ℕ := s.toNat / K ^ (v : ℕ) % K

lemma addCnt_encode {K : ℕ} {c : Fin m → ℕ} (hc : ∀ i, c i < K) (hK : 0 < K) :
    addCnt K (encode K c : ℤ) = c := by
  funext v; simp [addCnt, digit_encode hc hK]

/-- The bounded-counter simulation of Theorem 3.3 (`add`), base `K ≥ 1`. -/
def addSim (m K : ℕ) (hK : 0 < K) : BCounterSim m K where
  B := addLoc
  init := 0
  incOp v := .add ((K : ℤ) ^ (v : ℕ))
  decOp v := .add (-(K : ℤ) ^ (v : ℕ))
  scanOp := .read
  decode := addCnt K
  cnt := addCnt K
  Inv := AddInv K
  inv_init := ⟨0, fun _ => hK, by simp [encode]⟩
  cnt_init := by funext v; simp [addCnt]
  inc_ok s v hs hv := by
    obtain ⟨c, hc, rfl⟩ := hs
    rw [addCnt_encode hc hK] at hv ⊢
    have hc' : ∀ i, Function.update c v (c v + 1) i < K := by
      intro i; by_cases hi : i = v
      · subst hi; simpa using hv
      · simp [hi, hc i]
    have he : (encode K c : ℤ) + (K : ℤ) ^ (v : ℕ) = (encode K (Function.update c v (c v + 1)) : ℤ) := by
      rw [encode_inc]; push_cast; ring
    refine ⟨⟨_, hc', he⟩, ?_⟩
    change addCnt K ((encode K c : ℤ) + (K : ℤ) ^ (v : ℕ)) = _
    rw [he, addCnt_encode hc' hK]
  dec_ok s v hs hv := by
    obtain ⟨c, hc, rfl⟩ := hs
    rw [addCnt_encode hc hK] at hv ⊢
    have hc' : ∀ i, Function.update c v (c v - 1) i < K := by
      intro i; by_cases hi : i = v
      · subst hi; simp; have := hc i; omega
      · simp [hi, hc i]
    have he : (encode K c : ℤ) + -(K : ℤ) ^ (v : ℕ) =
        (encode K (Function.update c v (c v - 1)) : ℤ) := by
      rw [← encode_dec K c v hv]; push_cast; ring
    refine ⟨⟨_, hc', he⟩, ?_⟩
    change addCnt K ((encode K c : ℤ) + -(K : ℤ) ^ (v : ℕ)) = _
    rw [he, addCnt_encode hc' hK]
  scan_state _ := rfl
  scan_resp _ _ := rfl

/-- Theorem 3.3 of [EGSZ16] (`add`, general form): obstruction-free `m`-valued consensus among (at
most) `n ≥ 1` processes can be solved with a single location supporting only `read()` and
`add(x)`, initially `0`. Moreover the stored value always encodes counts in `{0, …, 3n-1}`. -/
theorem theorem_3_3_add_general (m : ℕ) [NeZero m] (n : ℕ) (P : Type) [DecidableEq P]
    [Fintype P] (hn : Fintype.card P ≤ n) (hn1 : 1 ≤ n) :
    ∃ (L : Type) (I : Impl (taskObj (Fin m) (Fin m)) (fun _ : Unit => addLoc) P L),
      I.memInit () = 0 ∧ (∀ p v, I.allowed p v) ∧ I.Solves (consensus P (Fin m)) ∧
        I.ObstructionFree :=
  ⟨Phase2 m, racing2 (addSim m (3 * n) (by omega)) n, rfl, fun _ _ => trivial,
    racing2_solves hn hn1, racing2_obstructionFree hn hn1⟩

/-- Theorem 3.3 of [EGSZ16] (`add`): `n`-consensus (obstruction-free `n`-valued consensus among
`n` processes) can be solved using a single memory location that supports only `read()` and
`add(x)`, initially `0`. -/
theorem theorem_3_3_add (n : ℕ) [NeZero n] :
    ∃ (L : Type) (I : Impl (taskObj (Fin n) (Fin n)) (fun _ : Unit => addLoc) (Fin n) L),
      I.memInit () = 0 ∧ (∀ p v, I.allowed p v) ∧ I.Solves (consensus (Fin n) (Fin n)) ∧
        I.ObstructionFree :=
  theorem_3_3_add_general n n (Fin n) (by simp) (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))

end Cslib.SharedMemory.ComplexityHierarchy
