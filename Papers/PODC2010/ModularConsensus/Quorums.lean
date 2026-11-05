import Papers.PODC2010.ModularConsensus.AdoptCommit
import Podc.Foundations.Combinatorics.SetPairs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset

/-!
# Choice of quorums (Section 6.2, Theorems 9 and 10)

Three choices of write/read quorums satisfying the hypothesis `W v ∩ R v' = ∅ ↔ v = v'` of
Theorem 8:

1. binary values, `W v = {r_v}`, `R v = {r_¬v}` (`binW`, `binR`): 3 registers, at most 4
   operations (`binary_registers`, `binary_steps`);
2. `m` values, `k` registers with `C(k, ⌊k/2⌋) ≥ m`, `W v` = distinct `⌊k/2⌋`-subsets and
   `R v = (W v)ᶜ` (`midW`, `midR`): `k + 1` registers, at most `k + 2` operations
   (`mid_steps`); such a `k` exists with `k ≤ ⌈lg m⌉ + ⌈lg (2⌈lg m⌉ + 2)⌉`
   (`exists_k_le`, i.e. `k = lg m + O(log log m)`); this choice is optimal by Bollobás's theorem
   (Theorem 9, `Cslib.SetPairs.sum_inv_choose_le_one`): `card_le_choose_of_quorums`;
3. `m` values written in binary with `c = ⌈lg m⌉` bits, registers `r_{i,b}`, `W v = {r_{i,v_i}}`,
   `R v = {r_{i,¬v_i}}` (`bitW`, `bitR`): `2c + 1` registers, at most `2c + 2` operations.

`theorem10` — **Theorem 10**: for any `m ≥ 1`, an `m`-valued adopt-commit object for any set of
processes, deterministic, with `2⌈lg m⌉ + 1` registers and at most `2⌈lg m⌉ + 2` operations
per process.
-/

namespace Podc.ModularConsensus.AC

open Cslib.SharedMemory Finset

/-! ### 1. Binary adopt-commit -/

/-- Binary write quorums: `W v = {r_v}`. -/
def binW (v : Bool) : Finset Bool := {v}

/-- Binary read quorums: `R v = {r_¬v}`. -/
def binR (v : Bool) : Finset Bool := {!v}

lemma bin_hWR : ∀ v v', Disjoint (binW v) (binR v') ↔ v = v' := by
  decide

/-- The binary adopt-commit object uses 3 registers: `r₀`, `r₁` and `proposal`. -/
lemma binary_registers : Fintype.card (Option Bool) = 3 := rfl

/-- The binary adopt-commit object satisfies the adopt-commit specification and is wait-free. -/
theorem binary_adoptCommit (P : Type) [DecidableEq P] :
    (acImpl P binW binR).Solves (adoptCommitTask P Bool) ∧ (acImpl P binW binR).WaitFree :=
  ⟨theorem8_solves bin_hWR, theorem8_waitFree 1 (by intro v; simp [binR])⟩

/-- Binary adopt-commit: at most 4 register operations per process. -/
theorem binary_steps {P : Type} [DecidableEq P] {α γ : List (Label P (acObj Bool))} {p : P}
    {v : Bool} (hv : (acImpl P binW binR).Valid (α ++ .inv p v :: γ))
    (hret : ∀ r, .ret p r ∉ γ) : γ.countP (Label.isTauOf p) ≤ 4 := by
  have := steps_le 1 (by intro v; simp [binR]) hv hret
  simpa [binW] using this

/-- Non-vacuity: a solo execution of the binary adopt-commit object in which the (only) process
writes `r_true`, reads `⊥` from `proposal`, writes `proposal`, reads `r_false = 0` and commits. -/
example : (acImpl Unit binW binR).Valid
    [.inv () true, .tau (), .tau (), .tau (), .tau (), .ret () (.commit, true)] := by
  apply Option.isSome_iff_exists.1
  simp [Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, acImpl, binW, binR, Loc.pref]

/-- Non-vacuity: with two processes, process `1` (input `false`) runs after process `0` (input
`true`) has committed; it adopts `true`. -/
example : (acImpl Bool binW binR).Valid
    [.inv false true, .tau false, .tau false, .tau false, .tau false, .ret false (.commit, true),
     .inv true false, .tau true, .tau true, .tau true, .ret true (.adopt, true)] := by
  apply Option.isSome_iff_exists.1
  simp [Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, acImpl, binW, binR, Loc.pref]

/-! ### 3. Bit-vector quorums -/

section Bits

variable {m : ℕ}

/-- Bit-vector write quorums: `W v = {r_{i, v_i} | i < ⌈lg m⌉}`. -/
def bitW (m : ℕ) (v : Fin m) : Finset (Fin (Nat.clog 2 m) × Bool) :=
  univ.image fun i => (i, v.val.testBit i)

/-- Bit-vector read quorums: `R v = {r_{i, ¬v_i} | i < ⌈lg m⌉}`. -/
def bitR (m : ℕ) (v : Fin m) : Finset (Fin (Nat.clog 2 m) × Bool) :=
  univ.image fun i => (i, !v.val.testBit i)

lemma card_bitW (v : Fin m) : (bitW m v).card = Nat.clog 2 m := by
  rw [bitW, card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h)]
  simp

lemma card_bitR (v : Fin m) : (bitR m v).card = Nat.clog 2 m := by
  rw [bitR, card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h)]
  simp

lemma bit_hWR : ∀ v v' : Fin m, Disjoint (bitW m v) (bitR m v') ↔ v = v' := by
  intro v v'
  constructor
  · intro h
    by_contra hne
    have hne' : v.val ≠ v'.val := fun h' => hne (Fin.ext h')
    obtain ⟨i, hi⟩ : ∃ i, v.val.testBit i ≠ v'.val.testBit i := by
      by_contra hall
      push Not at hall
      exact hne' (Nat.eq_of_testBit_eq hall)
    have hic : i < Nat.clog 2 m := by
      by_contra hic
      push Not at hic
      have hpow : m ≤ 2 ^ i :=
        (Nat.le_pow_clog (by norm_num) m).trans (Nat.pow_le_pow_right (by norm_num) hic)
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le v.isLt hpow),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le v'.isLt hpow)] at hi
      exact hi rfl
    refine Finset.disjoint_left.1 h
      (show ((⟨i, hic⟩ : Fin (Nat.clog 2 m)), v.val.testBit i) ∈ bitW m v by simp [bitW]) ?_
    · simp only [bitR, mem_image, mem_univ, true_and, Prod.mk.injEq]
      refine ⟨⟨i, hic⟩, rfl, ?_⟩
      revert hi; cases v.val.testBit i <;> cases v'.val.testBit i <;> simp
  · rintro rfl
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [bitW, bitR, mem_image, mem_univ, true_and] at hx hx'
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := hx'
    simp only [Prod.mk.injEq] at hj
    obtain ⟨rfl, h2⟩ := hj
    cases h : v.val.testBit j <;> simp [h] at h2

/-- The bit-vector adopt-commit object uses `2⌈lg m⌉ + 1` registers. -/
lemma bit_registers : Fintype.card (Option (Fin (Nat.clog 2 m) × Bool)) = 2 * Nat.clog 2 m + 1 := by
  simp [Fintype.card_option, Fintype.card_prod]; ring

end Bits

/-- **Theorem 10.** For any `m ≥ 1`, an `m`-valued adopt-commit object can be implemented
deterministically for any number of processes using `2⌈lg m⌉ + 1 = O(log m)` atomic registers
and at most `2⌈lg m⌉ + 2 = O(log m)` register operations per process (bit-vector quorums with
Procedure AdoptCommit). -/
theorem theorem10 (m : ℕ) [NeZero m] (P : Type) [DecidableEq P] :
    Fintype.card (Option (Fin (Nat.clog 2 m) × Bool)) = 2 * Nat.clog 2 m + 1 ∧
    (acImpl P (bitW m) (bitR m)).Solves (adoptCommitTask P (Fin m)) ∧
    (acImpl P (bitW m) (bitR m)).WaitFree ∧
    ∀ {α γ : List (Label P (acObj (Fin m)))} {p : P} {v : Fin m},
      (acImpl P (bitW m) (bitR m)).Valid (α ++ .inv p v :: γ) → (∀ r, .ret p r ∉ γ) →
        γ.countP (Label.isTauOf p) ≤ 2 * Nat.clog 2 m + 2 := by
  refine ⟨bit_registers, theorem8_solves bit_hWR,
    theorem8_waitFree (Nat.clog 2 m) (fun v => (card_bitR v).le), ?_⟩
  intro α γ p v hv hret
  have := steps_le (Nat.clog 2 m) (fun v => (card_bitR v).le) hv hret
  rw [card_bitW] at this
  omega

/-! ### 2. Middle-layer quorums and their optimality -/

section Mid

variable {m k : ℕ}

/-- `⌊k/2⌋`-subsets of `k` registers, indexed by `m ≤ C(k, ⌊k/2⌋)` values. -/
noncomputable def midEmb (h : m ≤ k.choose (k / 2)) : Fin m ↪ Finset (Fin k) :=
  (Fin.castLEEmb (by simpa [Finset.card_powersetCard] using h)).trans
    ((powersetCard (k / 2) (univ : Finset (Fin k))).equivFin.symm.toEmbedding.trans
      (Function.Embedding.subtype _))

lemma midEmb_card (h : m ≤ k.choose (k / 2)) (v : Fin m) : (midEmb h v).card = k / 2 := by
  have := ((powersetCard (k / 2) (univ : Finset (Fin k))).equivFin.symm
    (Fin.castLE (by simpa [Finset.card_powersetCard] using h) v)).2
  simp only [mem_powersetCard] at this
  exact this.2

/-- Write quorums: distinct `⌊k/2⌋`-subsets. -/
noncomputable def midW (h : m ≤ k.choose (k / 2)) (v : Fin m) : Finset (Fin k) := midEmb h v

/-- Read quorums: the complements of the write quorums. -/
noncomputable def midR (h : m ≤ k.choose (k / 2)) (v : Fin m) : Finset (Fin k) := (midEmb h v)ᶜ

lemma mid_hWR (h : m ≤ k.choose (k / 2)) :
    ∀ v v', Disjoint (midW h v) (midR h v') ↔ v = v' := by
  intro v v'
  rw [midW, midR, disjoint_compl_right_iff]
  constructor
  · intro hs
    exact (midEmb h).injective
      (Finset.eq_of_subset_of_card_le hs (by rw [midEmb_card, midEmb_card]))
  · rintro rfl; exact subset_rfl

/-- The middle-layer adopt-commit object: at most `k + 2` register operations per process
(`k + 1` registers: `k` binary ones and `proposal`). -/
theorem mid_steps (h : m ≤ k.choose (k / 2)) [NeZero m] {P : Type} [DecidableEq P]
    {α γ : List (Label P (acObj (Fin m)))} {p : P} {v : Fin m}
    (hv : (acImpl P (midW h) (midR h)).Valid (α ++ .inv p v :: γ))
    (hret : ∀ r, .ret p r ∉ γ) : γ.countP (Label.isTauOf p) ≤ k + 2 := by
  have hR : ∀ v, (midR h v).card ≤ k - k / 2 := by
    intro v; rw [midR, card_compl, Fintype.card_fin, midEmb_card]
  have := steps_le (k - k / 2) hR hv hret
  rw [midW, midEmb_card] at this
  omega

/-- `2^k ≤ (k + 1) C(k, ⌊k/2⌋)`. -/
lemma two_pow_le_mul_choose (k : ℕ) : 2 ^ k ≤ (k + 1) * k.choose (k / 2) := by
  rw [← Nat.sum_range_choose]
  calc ∑ i ∈ Finset.range (k + 1), k.choose i ≤ ∑ _i ∈ Finset.range (k + 1), k.choose (k / 2) :=
        Finset.sum_le_sum fun i _ => Nat.choose_le_middle i k
    _ = (k + 1) * k.choose (k / 2) := by simp

/-- A number of registers `k = lg m + O(log log m)` suffices: with `c = ⌈lg m⌉`,
`k = c + ⌈lg (2c + 2)⌉` satisfies `C(k, ⌊k/2⌋) ≥ m`. -/
theorem exists_k_le (m : ℕ) :
    ∃ k, k ≤ Nat.clog 2 m + Nat.clog 2 (2 * Nat.clog 2 m + 2) ∧ m ≤ k.choose (k / 2) := by
  set c := Nat.clog 2 m
  set d := Nat.clog 2 (2 * c + 2)
  refine ⟨c + d, le_rfl, ?_⟩
  have hm : m ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) m
  have hd : 2 * c + 2 ≤ 2 ^ d := Nat.le_pow_clog (by norm_num) _
  -- `d ≤ c + 1`
  have hdc : d ≤ c + 1 := by
    apply Nat.clog_le_of_le_pow
    calc 2 * c + 2 = 2 * (c + 1) := by ring
      _ ≤ 2 * 2 ^ c := by
        have : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
        omega
      _ = 2 ^ (c + 1) := by ring
  have key := two_pow_le_mul_choose (c + d)
  have h1 : 2 ^ c * (c + d + 1) ≤ 2 ^ (c + d) := by
    rw [pow_add]; exact Nat.mul_le_mul_left _ (by omega)
  have hpos : 0 < c + d + 1 := by omega
  by_contra hlt
  push Not at hlt
  have : 2 ^ c * (c + d + 1) < m * (c + d + 1) := by
    calc 2 ^ c * (c + d + 1) ≤ 2 ^ (c + d) := h1
      _ ≤ (c + d + 1) * (c + d).choose ((c + d) / 2) := key
      _ < (c + d + 1) * m := Nat.mul_lt_mul_of_pos_left hlt hpos
      _ = m * (c + d + 1) := by ring
  have := lt_of_mul_lt_mul_right this
  omega

/-- **Optimality of the middle-layer quorums** (consequence of Theorem 9, Bollobás's theorem):
any quorum system for `V` satisfying the hypothesis of Theorem 8 with `|W v| + |R v| ≤ k` for
all `v` has at most `C(k, ⌊k/2⌋)` values. -/
theorem card_le_choose_of_quorums {V ι : Type} [Fintype V] [DecidableEq ι] (W R : V → Finset ι)
    (hWR : ∀ v v', Disjoint (W v) (R v') ↔ v = v') (k : ℕ) (hk : ∀ v, (W v).card + (R v).card ≤ k) :
    Fintype.card V ≤ k.choose (k / 2) :=
  Cslib.SetPairs.card_le_choose_half k univ W R (fun i _ j _ => hWR i j) (fun i _ => hk i)

end Mid

end Podc.ModularConsensus.AC
