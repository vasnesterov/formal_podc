import Papers.PODC2011.RobustAtomicStorage.Blocks
import Cslib.Foundations.Combinatorics.Labelling

/-!
# Arithmetic of the lower bounds (§4)

* The closed form of `t_k` and the inversion `t_k ≤ t ↔ k ≤ ⌊log ⌈(3t+1)/2⌉⌋` (proof of Lemma 2).
* Existence of a block assignment that `Fits` the write lower-bound construction of Lemma 1
  for every `t` and `S ≤ 3t + ⌊t / t_k⌋` objects (`exists_fits`); the paper's instance
  `t = t_k`, `S = 3 t_k + 1` (`exists_fits_paper`) with the paper's block sizes (equations (1)–(3)).
* The partition into four blocks of at most `t` objects used by the read lower bound.
-/

namespace Podc.RobustAtomicStorage

open Finset Blk

/-! ## The sequence `t_k` -/

theorem tseq_rec (m : ℕ) : tseq (m + 1) = tseq m + 2 * tseq (m - 1) + 1 := by
  cases m <;> simp [tseq]

theorem tseq_lt_succ (k : ℕ) : tseq k < tseq (k + 1) := by
  cases k <;> simp [tseq]

theorem tseq_strictMono : StrictMono tseq := strictMono_nat_of_lt_succ tseq_lt_succ

theorem tseq_mono : Monotone tseq := tseq_strictMono.monotone

theorem tseq_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ tseq k := by
  simpa [tseq] using tseq_mono hk

/-- Closed form `t_k = (2^{k+2} - (-1)^k - 3) / 6` (proof of Lemma 2 of [Dobre et al.]). -/
theorem tseq_closed (k : ℕ) : (6 * tseq k : ℤ) + (-1) ^ k + 3 = 2 ^ (k + 2) := by
  suffices h : ∀ k, (6 * tseq k : ℤ) + (-1) ^ k + 3 = 2 ^ (k + 2) ∧
      (6 * tseq (k + 1) : ℤ) + (-1) ^ (k + 1) + 3 = 2 ^ (k + 1 + 2) from (h k).1
  intro k
  induction k with
  | zero => norm_num [tseq]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    obtain ⟨h0, h1⟩ := ih
    have : tseq (k + 1 + 1) = tseq (k + 1) + 2 * tseq k + 1 := rfl
    rw [this]; push_cast
    linear_combination h1 + 2 * h0

/-- `2^{k+1} ≤ 3 t_k + 2 ≤ 2^{k+1} + 1`. -/
theorem tseq_bounds (k : ℕ) : 2 ^ (k + 1) ≤ 3 * tseq k + 2 ∧ 3 * tseq k + 1 ≤ 2 ^ (k + 1) := by
  have h := tseq_closed k
  have hp : (2 : ℤ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
  rw [hp] at h
  constructor <;> zify <;> rcases neg_one_pow_eq_or ℤ k with h' | h' <;> rw [h'] at h <;> linarith

/-- "Solving for `k`" in the proof of Lemma 2: `t_k ≤ t ↔ k ≤ ⌊log ⌈(3t+1)/2⌉⌋`
(note `⌈(3t+1)/2⌉ = (3t+2)/2` in `ℕ`). -/
theorem tseq_le_iff (k t : ℕ) : tseq k ≤ t ↔ k ≤ Nat.log 2 ((3 * t + 2) / 2) := by
  rw [Nat.le_log_iff_pow_le (by norm_num) (by omega), Nat.le_div_iff_mul_le (by norm_num),
    ← pow_succ]
  obtain ⟨h1, h2⟩ := tseq_bounds k
  generalize 2 ^ (k + 1) = P at *
  constructor
  · intro h; omega
  · intro h; by_contra h'; omega

/-- `⌊log ⌈(3 t_k + 1)/2⌉⌋ = k` (proof of Lemma 2). -/
theorem log_tseq (k : ℕ) : Nat.log 2 ((3 * tseq k + 2) / 2) = k := by
  refine le_antisymm ?_ ((tseq_le_iff k _).1 le_rfl)
  by_contra h
  have := (tseq_le_iff (k + 1) (tseq k)).2 (by omega)
  have := tseq_lt_succ k
  omega

/-! ## Sums of block sizes over sets of blocks -/

/-- The valid blocks `B₀, …, B_{k+1}, C₁, …, C_k`. -/
def validBlks (k : ℕ) : Finset Blk := (range (k + 2)).image B ∪ (Icc 1 k).image C

theorem mem_validBlks {k : ℕ} {b : Blk} : b ∈ validBlks k ↔ Valid k b := by
  cases b <;> simp [validBlks, Valid] <;> omega

open Classical in
/-- `bsum k f p = ∑_{valid b, p b} f b`. -/
noncomputable def bsum (k : ℕ) (f : Blk → ℕ) (p : Blk → Prop) : ℕ :=
  ∑ b ∈ validBlks k, if p b then f b else 0

theorem bsum_congr {k : ℕ} {f : Blk → ℕ} {p q : Blk → Prop}
    (h : ∀ b, Valid k b → (p b ↔ q b)) : bsum k f p = bsum k f q := by
  unfold bsum
  refine Finset.sum_congr rfl fun b hb => ?_
  have := h b (mem_validBlks.1 hb)
  by_cases hp : p b
  · simp [hp, this.1 hp]
  · simp [hp, show ¬ q b from fun hq => hp (this.2 hq)]

theorem bsum_false {k : ℕ} {f : Blk → ℕ} {p : Blk → Prop}
    (h : ∀ b, Valid k b → ¬ p b) : bsum k f p = 0 := by
  unfold bsum
  exact Finset.sum_eq_zero fun b hb => by simp [h b (mem_validBlks.1 hb)]

theorem bsum_or {k : ℕ} {f : Blk → ℕ} {p q : Blk → Prop}
    (h : ∀ b, Valid k b → ¬ (p b ∧ q b)) :
    bsum k f (fun b => p b ∨ q b) = bsum k f p + bsum k f q := by
  unfold bsum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b hb => ?_
  have := h b (mem_validBlks.1 hb)
  by_cases hp : p b <;> by_cases hq : q b <;> simp_all

theorem bsum_eq {k : ℕ} {f : Blk → ℕ} {b₀ : Blk} (h : Valid k b₀) :
    bsum k f (· = b₀) = f b₀ := by
  unfold bsum
  rw [Finset.sum_eq_single b₀ (fun b _ hb => by simp [hb]) (fun h' => absurd
    (mem_validBlks.2 h) h')]
  simp

/-- Adding one block to a set of blocks. -/
theorem bsum_step {k : ℕ} {f : Blk → ℕ} {p q : Blk → Prop} {b₀ : Blk} (h₀ : Valid k b₀)
    (hp : ¬ p b₀) (h : ∀ b, Valid k b → (q b ↔ p b ∨ b = b₀)) :
    bsum k f q = bsum k f p + f b₀ := by
  rw [bsum_congr h, bsum_or (p := p) (q := (· = b₀))
    (fun b _ hb => hp (by obtain ⟨h1, rfl⟩ := hb; exact h1)), bsum_eq h₀]

/-- If all blocks are valid and the fibre of each block `b` has at most `f b` objects, then the
number of objects in a set of blocks is at most the sum of `f` over it. -/
theorem nBlk_le_bsum {Obj : Type} [Fintype Obj] {k : ℕ} {blk : Obj → Blk} {f : Blk → ℕ}
    (hv : ∀ s, Valid k (blk s)) (hf : ∀ b, (univ.filter fun s => blk s = b).card ≤ f b)
    (p : Blk → Prop) [DecidablePred p] : nBlk blk p ≤ bsum k f p := by
  classical
  unfold nBlk bsum
  rw [card_eq_sum_card_fiberwise (f := blk) (t := (validBlks k).filter p)
    (fun s hs => by simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hs ⊢
                    exact ⟨mem_validBlks.2 (hv s), hs⟩), Finset.sum_filter]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hb : p b
  · simp only [hb, ite_true]
    exact (card_le_card fun s hs => by simp at hs ⊢; exact hs.2).trans (hf b)
  · simp [hb]

/-- Realizing fibre sizes: if `card Obj ≤ ∑_{b ∈ V} f b`, then the objects can be assigned to
blocks of `V` so that block `b` gets at most `f b` objects. -/
theorem exists_assign {Obj : Type} [Fintype Obj] (V : Finset Blk) (f : Blk → ℕ)
    (h : Fintype.card Obj ≤ ∑ b ∈ V, f b) :
    ∃ blk : Obj → Blk, (∀ s, blk s ∈ V) ∧
      ∀ b, (univ.filter fun s => blk s = b).card ≤ f b := by
  classical
  let e := V.equivFin
  obtain ⟨g, hg⟩ := Fintype.exists_fin_labelling (α := Obj) (fun _ => 0)
    (fun i => f (e.symm i)) (fun _ => Nat.zero_le _) (by simp)
    (by rw [Equiv.sum_comp e.symm (fun x : V => f x), Finset.sum_coe_sort]; exact h)
  refine ⟨fun s => (e.symm (g s)).1, fun s => (e.symm (g s)).2, fun b => ?_⟩
  by_cases hb : b ∈ V
  · have : (univ.filter fun s => (e.symm (g s)).1 = b) = univ.filter fun s => g s = e ⟨b, hb⟩ := by
      ext s; simp [← Equiv.symm_apply_eq, Subtype.ext_iff]
    rw [this]
    simpa using (hg (e ⟨b, hb⟩)).2
  · have : (univ.filter fun s => (e.symm (g s)).1 = b) = ∅ := by
      ext s; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h'; exact hb (h' ▸ (e.symm (g s)).2)
    simp [this]

/-! ## Block sizes -/

/-- Block sizes for `k` rounds, scaled by `c`, plus `d` on the three blocks `B_k`, `C_k`,
`B_{k+1}`. With `c = 1`, `d = 0` these are the paper's sizes: `|B₀| = 1`,
`|B_l| = t_l - t_{l-2}` (`1 ≤ l ≤ k`), `|B_{k+1}| = t_k - t_{k-1}`, `|C_l| = t_{l-1} - t_{l-2}`
(`1 ≤ l ≤ k-1`), `|C_k| = t_k - t_{k-2}` (with `t_{-1} = 0`). -/
def blkSize (k c d : ℕ) : Blk → ℕ
  | B x => if x = 0 then c else if x < k then c * (tseq x - tseq (x - 2))
      else if x = k then c * (tseq k - tseq (k - 2)) + d else c * (tseq k - tseq (k - 1)) + d
  | C x => if x < k then c * (tseq (x - 1) - tseq (x - 2)) else c * (tseq k - tseq (k - 2)) + d

section Sizes

variable {k c d : ℕ}

/-- `|M_{m-1}| = c · t_m` (paper equation (1), scaled). -/
theorem bsum_Mlt (hk : 1 ≤ k) : ∀ m, m ≤ k → bsum k (blkSize k c d) (Mlt m) = c * tseq m := by
  intro m
  induction m with
  | zero => intro _; rw [bsum_false (by intro b _; cases b <;> simp [Mlt])]; simp [tseq]
  | succ m ih =>
    intro hm
    rcases m with _ | j
    · rw [bsum_step (p := Mlt 0) (b₀ := B 0) (by simp [Valid]) (by simp [Mlt])
        (by intro b _; cases b <;> simp [Mlt] <;> omega), ih (by omega)]
      simp [blkSize, tseq]
    · rw [bsum_step (p := fun b => Mlt (j + 1) b ∨ b = B (j + 1)) (b₀ := C (j + 1))
        (by simp [Valid]; omega) (by simp [Mlt])
        (by intro b _; cases b <;> simp [Mlt] <;> omega)]
      rw [bsum_step (p := Mlt (j + 1)) (b₀ := B (j + 1)) (by simp [Valid]; omega) (by simp [Mlt])
        (fun b _ => Iff.rfl), ih (by omega)]
      have h1 := tseq_rec j
      have h2 : tseq (j + 1 + 1) = tseq (j + 1) + 2 * tseq j + 1 := rfl
      have h3 := tseq_mono (Nat.sub_le j 1)
      have h4 := tseq_mono (show j ≤ j + 1 by omega)
      simp only [blkSize, show j + 1 ≠ 0 by omega, show j + 1 < k by omega, ite_false, ite_true,
        show j + 1 - 2 = j - 1 by omega, Nat.add_sub_cancel]
      rw [← mul_add, ← mul_add]
      congr 1
      omega

/-- `|P_l| = c (t_k - t_{l-2}) + d` for `1 ≤ l ≤ k+1` (paper equation (2), scaled). -/
theorem bsum_P (hk : 1 ≤ k) (l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k + 1) :
    bsum k (blkSize k c d) (P k l) = c * (tseq k - tseq (l - 2)) + d := by
  suffices H : ∀ j, (∀ l, l + j = k + 1 → 1 ≤ l →
      bsum k (blkSize k c d) (P k l) = c * (tseq k - tseq (l - 2)) + d) ∧
      (∀ l, l + (j + 1) = k + 1 → 1 ≤ l →
      bsum k (blkSize k c d) (P k l) = c * (tseq k - tseq (l - 2)) + d) from
    (H (k + 1 - l)).1 l (by omega) hl
  intro j
  induction j with
  | zero =>
    constructor
    · intro l hl _
      obtain rfl : l = k + 1 := by omega
      rw [bsum_step (p := fun _ => False) (b₀ := B (k + 1)) (by simp [Valid]) id
        (by intro b _; cases b <;> simp [P] <;> omega), bsum_false (fun _ _ h => h)]
      simp [blkSize, show k + 1 - 2 = k - 1 by omega]
    · intro l hl _
      obtain rfl : l = k := by omega
      rw [bsum_step (p := fun _ => False) (b₀ := B l) (by simp [Valid]) id
        (by intro b hb; cases b <;> simp [P, Valid] at hb ⊢ <;> omega), bsum_false (fun _ _ h => h)]
      simp [blkSize, show l ≠ 0 by omega]
  | succ j ih =>
    refine ⟨ih.2, fun l hl hl1 => ?_⟩
    rw [bsum_step (p := P k (l + 2)) (b₀ := B l) (by simp [Valid]; omega) (by simp [P])
      (by intro b _; cases b <;> simp [P] <;> omega), ih.1 (l + 2) (by omega) (by omega)]
    have h3 := tseq_mono (show l - 2 ≤ l by omega)
    have h4 := tseq_mono (show l ≤ k by omega)
    simp only [blkSize, show l ≠ 0 by omega, show l < k by omega, ite_false, ite_true,
      Nat.add_sub_cancel]
    rw [add_right_comm, ← mul_add]
    congr 2
    omega

/-- `|𝒞_{l+1}| = c (t_k - t_{l-1}) + d` for `l + 1 ≤ k` (paper equation (3), scaled). -/
theorem bsum_CC (hk : 1 ≤ k) (l : ℕ) (hlk : l + 1 ≤ k) :
    bsum k (blkSize k c d) (CC k (l + 1)) = c * (tseq k - tseq (l - 1)) + d := by
  suffices H : ∀ j, ∀ l, l + 1 + j = k →
      bsum k (blkSize k c d) (CC k (l + 1)) = c * (tseq k - tseq (l - 1)) + d from
    H (k - (l + 1)) l (by omega)
  intro j
  induction j with
  | zero =>
    intro l hl
    obtain rfl : k = l + 1 := by omega
    rw [bsum_step (p := fun _ => False) (b₀ := C (l + 1)) (by simp [Valid]) id
      (by intro b hb; cases b <;> simp [CC, Valid] at hb ⊢ <;> omega), bsum_false (fun _ _ h => h)]
    simp [blkSize, show l + 1 - 2 = l - 1 by omega]
  | succ j ih =>
    intro l hl
    rw [bsum_step (p := CC k (l + 2)) (b₀ := C (l + 1)) (by simp [Valid]; omega) (by simp [CC])
      (by intro b _; cases b <;> simp [CC] <;> omega), ih (l + 1) (by omega)]
    have h3 := tseq_mono (show l - 1 ≤ l by omega)
    have h4 := tseq_mono (show l ≤ k by omega)
    simp only [blkSize, show l + 1 < k by omega, ite_true, Nat.add_sub_cancel,
      show l + 1 - 2 = l - 1 by omega]
    rw [add_right_comm, ← mul_add]
    congr 2
    omega

/-- The sizes sum to `c (3 t_k + 1) + 3 d`. -/
theorem bsum_total (hk : 1 ≤ k) :
    bsum k (blkSize k c d) (fun _ => True) = c * (3 * tseq k + 1) + 3 * d := by
  rw [bsum_step (p := fun b => (Mlt k b ∨ b = B k) ∨ b = B (k + 1)) (b₀ := C k)
      (by simp [Valid]; omega) (by simp [Mlt])
      (by intro b hb; cases b <;> simp [Mlt, Valid] at hb ⊢ <;> omega),
    bsum_step (p := fun b => Mlt k b ∨ b = B k) (b₀ := B (k + 1)) (by simp [Valid])
      (by simp [Mlt]) (fun _ _ => Iff.rfl),
    bsum_step (p := Mlt k) (b₀ := B k) (by simp [Valid]) (by simp [Mlt]) (fun _ _ => Iff.rfl),
    bsum_Mlt hk k le_rfl]
  have h1 : tseq k = tseq (k - 1) + 2 * tseq (k - 2) + 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simpa using tseq_rec j
  have h3 := tseq_mono (show k - 2 ≤ k - 1 by omega)
  have h4 := tseq_mono (show k - 1 ≤ k by omega)
  simp only [blkSize, show k ≠ 0 by omega, lt_irrefl, ite_false, ite_true,
    show k + 1 ≠ k by omega, show ¬ k + 1 < k by omega, show k + 1 ≠ 0 by omega]
  have : tseq k + (tseq k - tseq (k - 2)) + (tseq k - tseq (k - 1)) + (tseq k - tseq (k - 2)) =
      3 * tseq k + 1 := by omega
  rw [← this]
  ring

/-- With the scaled sizes, every set in `Fits` has `c t_k + d` objects. -/
theorem fits_of_sizes {Obj : Type} [Fintype Obj] (hk : 1 ≤ k) {blk : Obj → Blk}
    (hv : ∀ s, Valid k (blk s))
    (hf : ∀ b, (univ.filter fun s => blk s = b).card ≤ blkSize k c d b) :
    Fits k (c * tseq k + d) blk := by
  refine ⟨hv, ?_, ?_, ?_⟩
  · refine (nBlk_le_bsum hv hf _).trans ?_
    rw [bsum_Mlt hk k le_rfl]; omega
  · intro l hl hlk
    refine (nBlk_le_bsum hv hf _).trans_eq ?_
    rw [bsum_or (by intro b _; cases b <;> simp [Mlt, P] <;> omega), bsum_Mlt hk _ (by omega),
      bsum_P hk l hl hlk, ← add_assoc, ← mul_add,
      Nat.add_sub_cancel' (tseq_mono (by omega))]
  · intro l hl
    refine (nBlk_le_bsum hv hf _).trans_eq ?_
    rw [bsum_or (by intro b _; cases b <;> simp [Mlt, CC] <;> omega), bsum_Mlt hk _ (by omega),
      bsum_CC hk l hl, ← add_assoc, ← mul_add,
      Nat.add_sub_cancel' (tseq_mono (by omega))]

end Sizes

/-- The write lower-bound construction of Lemma 1 can be carried out with `k ≥ 1` write rounds,
`t` malicious objects and any number `S ≤ 3t + ⌊t / t_k⌋` of objects. (The paper only uses
`t = t_k`, `S = 3 t_k + 1`; see `exists_fits_paper`.) -/
theorem exists_fits {Obj : Type} [Fintype Obj] (k t : ℕ) (hk : 1 ≤ k)
    (hS : Fintype.card Obj ≤ 3 * t + t / tseq k) : ∃ blk : Obj → Blk, Fits k t blk := by
  set c := t / tseq k
  set d := t % tseq k
  have ht : c * tseq k + d = t := by rw [mul_comm]; exact Nat.div_add_mod t (tseq k)
  have htot : ∑ b ∈ validBlks k, blkSize k c d b = 3 * t + c := by
    have := bsum_total (c := c) (d := d) hk
    simp only [bsum, ite_true] at this
    rw [this, ← ht]; ring
  obtain ⟨blk, hv, hf⟩ := exists_assign (Obj := Obj) (validBlks k) (blkSize k c d) (htot ▸ hS)
  exact ⟨blk, ht ▸ fits_of_sizes hk (fun s => mem_validBlks.1 (hv s)) hf⟩

/-- Lemma 1 setting of [Dobre et al.]: with `S = 3 t_k + 1` objects and `t = t_k` malicious
objects the block construction exists. -/
theorem exists_fits_paper {Obj : Type} [Fintype Obj] (k : ℕ) (hk : 1 ≤ k)
    (hS : Fintype.card Obj = 3 * tseq k + 1) : ∃ blk : Obj → Blk, Fits k (tseq k) blk :=
  exists_fits k (tseq k) hk (by rw [Nat.div_self (tseq_pos hk)]; omega)

/-- The paper's block sizes (`c = 1`, `d = 0`) satisfy equations (1)–(3) of the proof of
Lemma 1: `|M_m| = t_{m+1}` (`m ≤ k - 1`), `|P_l| = t_k - t_{l-2}` (`1 ≤ l ≤ k + 1`),
`|𝒞_l| = t_k - t_{l-2}` (`2 ≤ l ≤ k`), and they sum to `3 t_k + 1`. -/
theorem paper_sizes {k : ℕ} (hk : 1 ≤ k) :
    (∀ m, m + 1 ≤ k → bsum k (blkSize k 1 0) (Mlt (m + 1)) = tseq (m + 1)) ∧
    (∀ l, 1 ≤ l → l ≤ k + 1 → bsum k (blkSize k 1 0) (P k l) = tseq k - tseq (l - 2)) ∧
    (∀ l, 2 ≤ l → l ≤ k → bsum k (blkSize k 1 0) (CC k l) = tseq k - tseq (l - 2)) ∧
    bsum k (blkSize k 1 0) (fun _ => True) = 3 * tseq k + 1 := by
  refine ⟨fun m hm => by simpa using bsum_Mlt (c := 1) (d := 0) hk (m + 1) hm,
    fun l hl hlk => by simpa using bsum_P (c := 1) (d := 0) hk l hl hlk,
    fun l hl hlk => ?_, by simpa using bsum_total (c := 1) (d := 0) hk⟩
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  rw [show l + 1 - 2 = l - 1 by omega]
  simpa using bsum_CC (c := 1) (d := 0) hk l hlk

/-! ## Read lower bound -/

/-- The objects can be split into four blocks of at most `t` objects each when `S ≤ 4t`
(read lower bound, §5). -/
theorem exists_four_blocks {Obj : Type} [Fintype Obj] (t : ℕ) (h : Fintype.card Obj ≤ 4 * t) :
    ∃ blk : Obj → Fin 4, ∀ i, (Finset.univ.filter fun s => blk s = i).card ≤ t := by
  obtain ⟨g, -, hg⟩ := Fintype.exists_fin_labelling_le (α := Obj) (k := 4) (t := t) ∅
    (by simp) h
  exact ⟨g, hg⟩

end Podc.RobustAtomicStorage
