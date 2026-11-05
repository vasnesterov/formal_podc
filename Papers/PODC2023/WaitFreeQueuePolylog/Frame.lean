import Papers.PODC2023.WaitFreeQueuePolylog.Shape

/-!
# Frame lemmas: blocks are immutable once installed

The operations represented by installed blocks depend only on installed blocks, so they do not
change when new blocks are installed (`ops_congr`, `pre_congr`); the linearization `L` only
grows (`rootLin_eq`, `rootLin_succ`). Also: provenance of the operations of a block
(`mem_ops_prov`), containment through subblocks (`mem_pre_of_child`), distinctness of the
operations of `L` (Lemma 5 / Corollary 6, `nodup_rootLin`).
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ}

lemma flatMap_congr_mem {X Y : Type} {l : List X} {f g : X → List Y} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

lemma mem_rng {a b j : ℕ} : j ∈ rng a b ↔ a < j ∧ j ≤ b := by
  simp only [rng, List.mem_range']; constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨j - (a + 1), by omega, by omega⟩

lemma not_internal_ht {n : ℕ} (k : ℕ) (hk : ht H n = k + 1) (hn0 : n ≠ 0) :
    1 ≤ n ∧ n < 2 ^ H := by
  refine ⟨by omega, ?_⟩
  by_contra h; rw [ht_eq_zero (by omega)] at hk; omega

lemma leaf_of_ht {n : ℕ} (hk : ht H n = 0) (hn0 : n ≠ 0) : 2 ^ H ≤ n := by
  by_contra hlt
  have h2 : Nat.log 2 n < H := Nat.log_lt_of_lt_pow (by omega) (by omega)
  unfold ht at hk; omega

/-- The operations of installed blocks only depend on installed blocks. -/
theorem ops_congr {M M' : Mem V} (hS : Shape H np M)
    (hag : ∀ m j, j ≤ cnt M m → M'.blk m j = M.blk m j) :
    ∀ n i, i ≤ cnt M n → ops H np M' n i = ops H np M n i := by
  suffices ∀ k n, ht H n = k → ∀ i, i ≤ cnt M n → ops H np M' n i = ops H np M n i from
    fun n => this _ n rfl
  intro k
  induction k with
  | zero =>
    intro n hk i hi
    by_cases hn0 : n = 0
    · subst hn0; have := hS.unused 0 (Or.inl rfl)
      have : i = 0 := by omega
      subst this; simp [ops]
    have hleaf := leaf_of_ht hk hn0
    cases i with
    | zero => simp [ops]
    | succ i => rw [Shape.ops_leaf (M := M') n i hleaf, Shape.ops_leaf (M := M) n i hleaf,
        hag n (i + 1) hi]
  | succ k ih =>
    intro n hk i hi
    by_cases hn0 : n = 0
    · subst hn0; have := hS.unused 0 (Or.inl rfl)
      have : i = 0 := by omega
      subst this; simp [ops]
    obtain ⟨hn, hH⟩ := not_internal_ht k hk hn0
    have h0 := ht_child' hn hH
    have h1 := ht_child hn hH (d := 1) (by norm_num)
    cases i with
    | zero => simp [ops]
    | succ i =>
      have e1 : M'.bk n i = M.bk n i := by simp [Mem.bk, hag n i (by omega)]
      have e2 : M'.bk n (i + 1) = M.bk n (i + 1) := by simp [Mem.bk, hag n (i + 1) hi]
      rw [Shape.ops_internal (M := M') n i hn hH, Shape.ops_internal (M := M) n i hn hH, e1, e2]
      have hl := hS.endl_le hi
      have hr := hS.endr_le hi
      congr 1
      · refine flatMap_congr_mem (fun j hj => ih _ (by omega) _ ?_)
        have := mem_rng.1 hj; omega
      · refine flatMap_congr_mem (fun j hj => ih _ (by omega) _ ?_)
        have := mem_rng.1 hj; omega

theorem pre_congr {M M' : Mem V} (hS : Shape H np M)
    (hag : ∀ m j, j ≤ cnt M m → M'.blk m j = M.blk m j) {n i : ℕ} (hi : i ≤ cnt M n) :
    pre H np M' n i = pre H np M n i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Shape.pre_succ, Shape.pre_succ, ih (by omega), ops_congr hS hag n _ hi]

lemma pre_prefix (M : Mem V) (n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    pre H np M n b = pre H np M n a ++ (rng a b).flatMap (ops H np M n) := by
  simp only [pre, preK]
  rw [← flatMap_range'_split (opsK H np M (ht H n) n) (a := 0) (Nat.zero_le _) hab]; rfl

lemma mem_pre_mono {M : Mem V} {n a b : ℕ} (hab : a ≤ b) {y : OpId (Fin np) × FifoOp V}
    (hy : y ∈ pre H np M n a) : y ∈ pre H np M n b := by
  rw [pre_prefix M n hab]; exact List.mem_append_left _ hy

lemma mem_pre_iff (M : Mem V) (n i : ℕ) (y : OpId (Fin np) × FifoOp V) :
    y ∈ pre H np M n i ↔ ∃ j, 1 ≤ j ∧ j ≤ i ∧ y ∈ ops H np M n j := by
  simp only [pre, preK, List.mem_flatMap, List.mem_range', ops]
  constructor
  · rintro ⟨j, ⟨a, ha, rfl⟩, hj⟩; exact ⟨1 + 1 * a, by omega, by omega, hj⟩
  · rintro ⟨j, h1, h2, hj⟩; exact ⟨j, ⟨j - 1, by omega, by omega⟩, hj⟩

/-- Containment through subblocks: an operation in the blocks `1..g` of a child is in the
blocks `1..j` of the parent if `end_d(j) ≥ g`. -/
lemma mem_pre_of_child {M : Mem V} (hS : Shape H np M) {v j d g : ℕ} (hv : 1 ≤ v)
    (hH : v < 2 ^ H) (hj : j ≤ cnt M v) (hd : d < 2) (hg : g ≤ endOf M v j d)
    {y : OpId (Fin np) × FifoOp V} (hy : y ∈ pre H np M (2 * v + d) g) :
    y ∈ pre H np M v j := by
  refine (hS.pre_perm hv hH hj).mem_iff.2 ?_
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
  · simp only [endOf, Blk.endd] at hg
    exact List.mem_append_left _ (mem_pre_mono hg (by simpa using hy))
  · simp only [endOf, Blk.endd, one_ne_zero, ite_false] at hg
    exact List.mem_append_right _ (mem_pre_mono hg hy)

/-- Provenance: an operation `((p, j), o)` of an installed block of any node is represented by
the installed leaf block `leaf(p).blocks[j + 1]`, and `o` is that block's operation. -/
theorem mem_ops_prov {M : Mem V} (hS : Shape H np M) :
    ∀ n i, i ≤ cnt M n → ∀ y ∈ ops H np M n i,
      y.1.2 + 1 ≤ cnt M (2 ^ H + y.1.1) ∧ y.2 = blkOp (M.bk (2 ^ H + y.1.1) (y.1.2 + 1)) := by
  suffices ∀ k n, ht H n = k → ∀ i, i ≤ cnt M n → ∀ y ∈ ops H np M n i,
      y.1.2 + 1 ≤ cnt M (2 ^ H + y.1.1) ∧ y.2 = blkOp (M.bk (2 ^ H + y.1.1) (y.1.2 + 1)) from
    fun n => this _ n rfl
  intro k
  induction k with
  | zero =>
    intro n hk i hi y hy
    by_cases hn0 : n = 0
    · subst hn0; have := hS.unused 0 (Or.inl rfl)
      have : i = 0 := by omega
      subst this; simp [ops] at hy
    have hleaf := leaf_of_ht hk hn0
    cases i with
    | zero => simp [ops] at hy
    | succ i =>
      rw [Shape.ops_leaf (M := M) n i hleaf] at hy
      split at hy
      · rename_i B hB
        simp only [leafOps] at hy
        split_ifs at hy with h
        · simp only [List.mem_singleton] at hy; subst hy
          simp only [Nat.add_sub_cancel]
          rw [show 2 ^ H + (n - 2 ^ H) = n by omega]
          exact ⟨hi, by simp [Mem.bk, hB]⟩
        · simp at hy
      · simp at hy
  | succ k ih =>
    intro n hk i hi y hy
    by_cases hn0 : n = 0
    · subst hn0; have := hS.unused 0 (Or.inl rfl)
      have : i = 0 := by omega
      subst this; simp [ops] at hy
    obtain ⟨hn, hH⟩ := not_internal_ht k hk hn0
    have h0 := ht_child' hn hH
    have h1 := ht_child hn hH (d := 1) (by norm_num)
    cases i with
    | zero => simp [ops] at hy
    | succ i =>
      rw [Shape.ops_internal (M := M) n i hn hH] at hy
      have hl := hS.endl_le hi
      have hr := hS.endr_le hi
      simp only [List.mem_append, List.mem_flatMap] at hy
      rcases hy with ⟨j, hj, hy⟩ | ⟨j, hj, hy⟩
      · exact ih _ (by omega) j (by have := mem_rng.1 hj; omega) y hy
      · exact ih _ (by omega) j (by have := mem_rng.1 hj; omega) y hy

theorem mem_pre_prov {M : Mem V} (hS : Shape H np M) {n i : ℕ} (hi : i ≤ cnt M n)
    {y : OpId (Fin np) × FifoOp V} (hy : y ∈ pre H np M n i) :
    y.1.2 + 1 ≤ cnt M (2 ^ H + y.1.1) ∧ y.2 = blkOp (M.bk (2 ^ H + y.1.1) (y.1.2 + 1)) := by
  obtain ⟨j, h1, h2, hj⟩ := (mem_pre_iff M n i y).1 hy
  exact mem_ops_prov hS n j (by omega) y hj

/-- The keys of a list of operations are those of its enqueues followed by its dequeues, up
to order. -/
lemma keys_enqs_deqs_perm {K : Type} (l : List (K × FifoOp V)) :
    ((enqs l).map Prod.fst ++ deqs l).Perm (l.map Prod.fst) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨x, o⟩ := a
    cases o with
    | enq v => simpa [enqs, deqs] using ih
    | deq =>
      simp only [enqs, deqs, List.filterMap_cons, List.map_cons] at ih ⊢
      exact (List.perm_middle).trans (List.Perm.cons _ ih)

lemma keys_batchLin_perm {K : Type} (bs : List (List (K × FifoOp V))) :
    ((batchLin (bs.map fun l => (enqs l, deqs l))).map Prod.fst).Perm
      ((bs.flatMap id).map Prod.fst) := by
  induction bs with
  | nil => simp [batchLin]
  | cons l bs ih =>
    simp only [List.map_cons, batchLin, List.flatMap_cons, List.map_append, List.map_map,
      Function.comp_def, id] at ih ⊢
    refine List.Perm.append ?_ ih
    simpa [Function.comp_def] using keys_enqs_deqs_perm l

lemma rootLin_keys_perm (M : Mem V) :
    ((rootLin H np M).map Prod.fst).Perm ((pre H np M 1 (cnt M 1)).map Prod.fst) := by
  have := keys_batchLin_perm ((List.range' 1 (cnt M 1)).map (ops H np M 1))
  have e : rootBatch H np M = fun b => (enqs (ops H np M 1 b), deqs (ops H np M 1 b)) := rfl
  simp only [List.map_map] at this
  simp only [rootLin, rootBatches, e, pre, preK]
  simpa [Function.comp_def, List.flatMap_map, ops] using this

/-- **Lemma 5 / Corollary 6.** No operation appears twice in `L`. -/
theorem nodup_rootLin {M : Mem V} (hS : Shape H np M) :
    ((rootLin H np M).map Prod.fst).Nodup := by
  refine (rootLin_keys_perm M).nodup_iff.2 ?_
  exact nodup_keys_preK M (cnt M) (fun m => by simp [hS.bk_zero, Blk.zero])
    (fun m j hj => hS.mono m j hj) (fun m j hj => ⟨hS.endl_le hj, hS.endr_le hj⟩) _ 1 _ le_rfl

lemma mem_rootLin_iff (M : Mem V) (x : OpId (Fin np)) :
    x ∈ (rootLin H np M).map Prod.fst ↔ x ∈ (pre H np M 1 (cnt M 1)).map Prod.fst :=
  (rootLin_keys_perm M).mem_iff

lemma rootLin_eq {M M' : Mem V} (hS : Shape H np M)
    (hag : ∀ m j, j ≤ cnt M m → M'.blk m j = M.blk m j) (hc : cnt M' 1 = cnt M 1) :
    rootLin H np M' = rootLin H np M := by
  simp only [rootLin, rootBatches, hc]
  congr 1
  refine List.map_congr_left (fun b hb => ?_)
  simp only [rootBatch]
  rw [ops_congr hS hag 1 b (by simp [List.mem_range'] at hb; omega)]

lemma rootLin_succ {M M' : Mem V} (hS : Shape H np M)
    (hag : ∀ m j, j ≤ cnt M m → M'.blk m j = M.blk m j) (hc : cnt M' 1 = cnt M 1 + 1) :
    rootLin H np M' = rootLin H np M ++ batchLin [rootBatch H np M' (cnt M' 1)] := by
  have e : rootBatches H np M' = rootBatches H np M ++ [rootBatch H np M' (cnt M' 1)] := by
    simp only [rootBatches, hc]
    rw [List.range'_1_concat, List.map_append]
    simp only [List.map_cons, List.map_nil]
    congr 1
    · refine List.map_congr_left (fun b hb => ?_)
      simp only [rootBatch]
      rw [ops_congr hS hag 1 b (by simp [List.mem_range'] at hb; omega)]
    · rw [Nat.add_comm]
  rw [rootLin, e, batchLin_append]; rfl

end Podc.WaitFreeQueuePolylog
