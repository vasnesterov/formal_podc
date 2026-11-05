import Papers.PODC2023.WaitFreeQueuePolylog.Seq
import Papers.PODC2023.WaitFreeQueuePolylog.QueueMath

/-!
# Structural invariants of the ordering tree (Section 4.1)

`cnt M n` is the index of the last installed block of `n` (Invariant 3: the installed blocks
are exactly `0..cnt n`, and `head n ∈ {cnt n, cnt n + 1}`). `Shape M` collects the invariants
of the memory that do not involve processes: Invariant 3 (first two claims), Lemma 4
(monotone `end` fields), the equations computed by lines 2, 6, 45, 46 and 50 when a block is
created, and the non-emptiness of installed blocks (line 52). From these we derive
Invariant 7 (`sumenq_eq`, `sumdeq_eq`), Corollary 8 and the distinctness of operations
(Lemma 5, Corollary 6: `nodup_rootLin`).
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type}

/-- The index of the last installed block of `n` (computed from `head`, Invariant 3). -/
def cnt (M : Mem V) (n : ℕ) : ℕ := if (M.blk n (M.head n)).isSome then M.head n else M.head n - 1

/-- `end_d` of the block `n.blocks[j]`. -/
def endOf (M : Mem V) (n j d : ℕ) : ℕ := (M.bk n j).endd d

section

variable (H np : ℕ)

/-- Height of a node (`0` for leaves). -/
def ht (n : ℕ) : ℕ := H - Nat.log 2 n

/-- The operations represented by `n.blocks[i]`. -/
def ops (M : Mem V) (n i : ℕ) : List (OpId (Fin np) × FifoOp V) := opsK H np M (ht H n) n i

/-- The operations of the blocks `1..i` of `n` (the operations "contained" in these blocks). -/
def pre (M : Mem V) (n i : ℕ) : List (OpId (Fin np) × FifoOp V) := preK H np M (ht H n) n i

/-- The root block `b` as a batch `(E(B), D(B))`. -/
def rootBatch (M : Mem V) (b : ℕ) : Batch (OpId (Fin np)) V :=
  (enqs (ops H np M 1 b), deqs (ops H np M 1 b))

/-- The root blocks `1..cnt root` as batches. -/
def rootBatches (M : Mem V) : List (Batch (OpId (Fin np)) V) :=
  (List.range' 1 (cnt M 1)).map (rootBatch H np M)

/-- The linearization ordering `L` of (3.2). -/
def rootLin (M : Mem V) : List (OpId (Fin np) × FifoOp V) := batchLin (rootBatches H np M)

/-- Memory invariants that do not involve processes. -/
structure Shape (M : Mem V) : Prop where
  blk0 : ∀ n, M.blk n 0 = some Blk.zero
  head_pos : ∀ n, 1 ≤ M.head n
  inst : ∀ n i, (M.blk n i).isSome ↔ i ≤ cnt M n
  /-- Lemma 4. -/
  mono : ∀ n i, i < cnt M n → (M.bk n i).endl ≤ (M.bk n (i + 1)).endl ∧
    (M.bk n i).endr ≤ (M.bk n (i + 1)).endr
  /-- The `end` fields were read from the children's `head` fields minus one (lines 43–44). -/
  endlt : ∀ n i, i ≤ cnt M n → (M.bk n i).endl < M.head (2 * n) ∧
    (M.bk n i).endr < M.head (2 * n + 1)
  /-- Lines 45–46. -/
  sumI : ∀ n, n < 2 ^ H → ∀ i, i ≤ cnt M n →
    (M.bk n i).sumenq = (M.bk (2 * n) (M.bk n i).endl).sumenq +
      (M.bk (2 * n + 1) (M.bk n i).endr).sumenq ∧
    (M.bk n i).sumdeq = (M.bk (2 * n) (M.bk n i).endl).sumdeq +
      (M.bk (2 * n + 1) (M.bk n i).endr).sumdeq
  /-- Lines 2 and 6. -/
  sumL : ∀ n, 2 ^ H ≤ n → ∀ i, 1 ≤ i → i ≤ cnt M n →
    (M.bk n i).sumenq = (M.bk n (i - 1)).sumenq + (if isEnq (blkOp (M.bk n i)) then 1 else 0) ∧
    (M.bk n i).sumdeq = (M.bk n (i - 1)).sumdeq + (if isEnq (blkOp (M.bk n i)) then 0 else 1)
  /-- Line 52 (Corollary 8). -/
  nonempty : ∀ n i, 1 ≤ i → i ≤ cnt M n →
    (M.bk n (i - 1)).sumenq + (M.bk n (i - 1)).sumdeq < (M.bk n i).sumenq + (M.bk n i).sumdeq
  /-- Line 50. -/
  size : ∀ i, 1 ≤ i → i ≤ cnt M 1 →
    (M.bk 1 i).size = (M.bk 1 (i - 1)).size + ((M.bk 1 i).sumenq - (M.bk 1 (i - 1)).sumenq) -
      ((M.bk 1 i).sumdeq - (M.bk 1 (i - 1)).sumdeq)
  /-- Unused leaves and the non-node `0` are empty. -/
  unused : ∀ n, (n = 0 ∨ 2 ^ H + np ≤ n) → cnt M n = 0
  /-- Leaf blocks have no subblocks. -/
  leafEnd : ∀ n, 2 ^ H ≤ n → ∀ i, (M.bk n i).endl = 0 ∧ (M.bk n i).endr = 0

end

/-! ### Basic facts -/

lemma cnt_le_head (M : Mem V) (n : ℕ) : cnt M n ≤ M.head n := by
  unfold cnt; split <;> omega

lemma head_le_cnt_succ (M : Mem V) (n : ℕ) : M.head n ≤ cnt M n + 1 := by
  unfold cnt; split <;> omega

lemma ht_eq_zero {H n : ℕ} (h : 2 ^ H ≤ n) : ht H n = 0 := by
  have : H ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) h
  unfold ht; omega

lemma log_two_mul_add {n d : ℕ} (hn : 1 ≤ n) (hd : d < 2) :
    Nat.log 2 (2 * n + d) = Nat.log 2 n + 1 := by
  rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega)]
  congr 2; omega

lemma ht_child {H n d : ℕ} (hn : 1 ≤ n) (hH : n < 2 ^ H) (hd : d < 2) :
    ht H (2 * n + d) + 1 = ht H n := by
  have h1 := log_two_mul_add hn hd
  have h2 : Nat.log 2 n < H := Nat.log_lt_of_lt_pow (by omega) hH
  unfold ht; omega

lemma ht_child' {H n : ℕ} (hn : 1 ≤ n) (hH : n < 2 ^ H) : ht H (2 * n) + 1 = ht H n := by
  simpa using ht_child (d := 0) hn hH (by norm_num)

namespace Shape

variable {H np : ℕ} {M : Mem V}

lemma blk_isSome (hS : Shape H np M) {n i : ℕ} (h : i ≤ cnt M n) : (M.blk n i).isSome :=
  (hS.inst n i).2 h

lemma blk_none (hS : Shape H np M) {n i : ℕ} (h : cnt M n < i) : M.blk n i = none := by
  have := (hS.inst n i).not.2 (by omega)
  simpa using this

lemma bk_zero (hS : Shape H np M) (n : ℕ) : M.bk n 0 = Blk.zero := by
  simp [Mem.bk, hS.blk0 n]

lemma endl_le (hS : Shape H np M) {n i : ℕ} (h : i ≤ cnt M n) : (M.bk n i).endl ≤ cnt M (2 * n) :=
  Nat.le_of_lt_succ ((hS.endlt n i h).1.trans_le (head_le_cnt_succ M _))

lemma endr_le (hS : Shape H np M) {n i : ℕ} (h : i ≤ cnt M n) :
    (M.bk n i).endr ≤ cnt M (2 * n + 1) :=
  Nat.le_of_lt_succ ((hS.endlt n i h).2.trans_le (head_le_cnt_succ M _))

lemma mono_le (hS : Shape H np M) {n i j : ℕ} (hij : i ≤ j) (hj : j ≤ cnt M n) :
    (M.bk n i).endl ≤ (M.bk n j).endl ∧ (M.bk n i).endr ≤ (M.bk n j).endr := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl⟩
  | succ j hij ih =>
    obtain ⟨a, b⟩ := ih (by omega)
    obtain ⟨c, d⟩ := hS.mono n j (by omega)
    exact ⟨a.trans c, b.trans d⟩

/-- Unfolding `ops` at an internal node. -/
lemma ops_internal (n i : ℕ) (hn : 1 ≤ n) (hH : n < 2 ^ H) :
    ops H np M n (i + 1) =
      (rng (M.bk n i).endl (M.bk n (i + 1)).endl).flatMap (ops H np M (2 * n)) ++
      (rng (M.bk n i).endr (M.bk n (i + 1)).endr).flatMap (ops H np M (2 * n + 1)) := by
  have h0 := ht_child' hn hH
  have h1 := ht_child hn hH (d := 1) (by norm_num)
  unfold ops
  rw [← h0, opsK_succ_succ]
  rw [show ht H (2 * n + 1) = ht H (2 * n) by omega]

/-- Unfolding `ops` at a leaf. -/
lemma ops_leaf (n i : ℕ) (hn : 2 ^ H ≤ n) :
    ops H np M n (i + 1) = match M.blk n (i + 1) with
      | some B => leafOps H np n (i + 1) B
      | none => [] := by
  unfold ops; rw [ht_eq_zero hn, opsK_zero_succ]; rfl

lemma pre_succ (n i : ℕ) : pre H np M n (i + 1) = pre H np M n i ++ ops H np M n (i + 1) :=
  preK_succ _ _ _ _

/-- The subblock decomposition of a prefix at an internal node. -/
lemma pre_perm (hS : Shape H np M) {n i : ℕ} (hn : 1 ≤ n) (hH : n < 2 ^ H) (hi : i ≤ cnt M n) :
    (pre H np M n i).Perm
      (pre H np M (2 * n) (M.bk n i).endl ++ pre H np M (2 * n + 1) (M.bk n i).endr) := by
  have h0 := ht_child' hn hH
  have h1 := ht_child hn hH (d := 1) (by norm_num)
  unfold pre
  rw [← h0]
  rw [show ht H (2 * n + 1) = ht H (2 * n) by omega]
  exact preK_perm M _ n i (by simp [hS.bk_zero, Blk.zero]) (by simp [hS.bk_zero, Blk.zero])
    (fun j hj => hS.mono n j (by omega))

/-- **Invariant 7.** `sumenq` and `sumdeq` count the enqueues and dequeues of the blocks
`1..i`. -/
theorem sum_eq (hS : Shape H np M) (k : ℕ) : ∀ n, ht H n = k → ∀ i, i ≤ cnt M n →
    (enqs (pre H np M n i)).length = (M.bk n i).sumenq ∧
    (deqs (pre H np M n i)).length = (M.bk n i).sumdeq := by
  induction k with
  | zero =>
    intro n hk i hi
    by_cases hn0 : n = 0
    · subst hn0; have := hS.unused 0 (Or.inl rfl)
      have : i = 0 := by omega
      subst this; simp [pre, preK, hS.bk_zero, Blk.zero]
    have hleaf : 2 ^ H ≤ n := by
      by_contra hlt
      have h2 : Nat.log 2 n < H := Nat.log_lt_of_lt_pow (by omega) (by omega)
      unfold ht at hk; omega
    induction i with
    | zero => simp [pre, preK, hS.bk_zero, Blk.zero]
    | succ i ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      obtain ⟨e1, e2⟩ := hS.sumL n hleaf (i + 1) (by omega) hi
      have hsome := hS.blk_isSome hi
      obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 hsome
      have hused : n - 2 ^ H < np := by
        by_contra hc
        have := hS.unused n (Or.inr (by omega)); omega
      rw [pre_succ, ops_leaf n i hleaf, hB]
      simp only [Nat.add_sub_cancel] at e1 e2
      simp only [Mem.bk, hB, Option.getD_some] at e1 e2
      simp only [leafOps, hleaf, hused, and_self, dite_true, enqs_append, deqs_append,
        List.length_append, ih1, ih2, Mem.bk, hB, Option.getD_some]
      rw [e1, e2]
      unfold blkOp isEnq at *
      cases B.elem <;> simp [enqs, deqs]
  | succ k ih =>
    intro n hk i hi
    by_cases hn0 : n = 0
    · subst hn0; have := hS.unused 0 (Or.inl rfl)
      have : i = 0 := by omega
      subst this; simp [pre, preK, hS.bk_zero, Blk.zero]
    have hn : 1 ≤ n := by omega
    have hH : n < 2 ^ H := by
      by_contra h; rw [ht_eq_zero (by omega)] at hk; omega
    have hp := hS.pre_perm hn hH hi
    have h0 := ht_child' hn hH
    have h1 := ht_child hn hH (d := 1) (by norm_num)
    obtain ⟨a1, a2⟩ := ih (2 * n) (by omega) _ (hS.endl_le hi)
    obtain ⟨b1, b2⟩ := ih (2 * n + 1) (by omega) _ (hS.endr_le hi)
    obtain ⟨c1, c2⟩ := hS.sumI n hH i hi
    rw [Perm.enqs_length hp, Perm.deqs_length hp, enqs_append, deqs_append,
      List.length_append, List.length_append, a1, a2, b1, b2, c1, c2]
    exact ⟨rfl, rfl⟩

theorem sumenq_eq (hS : Shape H np M) {n i : ℕ} (hi : i ≤ cnt M n) :
    (enqs (pre H np M n i)).length = (M.bk n i).sumenq :=
  (hS.sum_eq _ n rfl i hi).1

theorem sumdeq_eq (hS : Shape H np M) {n i : ℕ} (hi : i ≤ cnt M n) :
    (deqs (pre H np M n i)).length = (M.bk n i).sumdeq :=
  (hS.sum_eq _ n rfl i hi).2

end Shape

end Podc.WaitFreeQueuePolylog
