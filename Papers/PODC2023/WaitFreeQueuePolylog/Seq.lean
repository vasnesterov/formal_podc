import Papers.PODC2023.WaitFreeQueuePolylog.Defs

/-!
# The operation sequences represented by blocks (Section 3.2)

`opsK M k n i` is the sequence of operations represented by the block `n.blocks[i]` of a node
`n` at height `k` (leaves have height `0`), in subblock order: the operations of the direct
subblocks in the left child, then those in the right child (3.3). The enqueue sequence `E(B)`
and the dequeue sequence `D(B)` of (3.1) are its enqueues and dequeues (`enqs`, `deqs`):
filtering commutes with concatenation, so this is exactly (3.1).

An operation is identified by its CSLib instance `(p, j)` (the `j`-th operation of `p`); it is
represented by the leaf block `leaf(p).blocks[j + 1]`.

The main facts here are purely structural (they hold for every memory whose `end` fields are
monotone): `preK_perm` (the blocks `1..i` of `n` represent exactly the blocks
`1..endl` of the left child and `1..endr` of the right child), `nodup_keys_preK` and
`count_preK` (the counting behind Invariant 7).
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type}

/-- The enqueues (with their values) of a sequence of operations. -/
def enqs {K : Type} (l : List (K × FifoOp V)) : List (K × V) :=
  l.filterMap fun e => match e.2 with
    | .enq v => some (e.1, v)
    | .deq => none

/-- The dequeues of a sequence of operations. -/
def deqs {K : Type} (l : List (K × FifoOp V)) : List K :=
  l.filterMap fun e => match e.2 with
    | .enq _ => none
    | .deq => some e.1

/-- Is the operation an enqueue? -/
def isEnq : FifoOp V → Bool
  | .enq _ => true
  | .deq => false

@[simp] lemma enqs_nil {K : Type} : enqs ([] : List (K × FifoOp V)) = [] := rfl
@[simp] lemma deqs_nil {K : Type} : deqs ([] : List (K × FifoOp V)) = [] := rfl
@[simp] lemma enqs_append {K : Type} (l l' : List (K × FifoOp V)) :
    enqs (l ++ l') = enqs l ++ enqs l' := by simp [enqs]
@[simp] lemma deqs_append {K : Type} (l l' : List (K × FifoOp V)) :
    deqs (l ++ l') = deqs l ++ deqs l' := by simp [deqs]

lemma enqs_flatMap {K X : Type} (s : List X) (f : X → List (K × FifoOp V)) :
    enqs (s.flatMap f) = s.flatMap (fun x => enqs (f x)) := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [List.flatMap_cons, ih]

lemma deqs_flatMap {K X : Type} (s : List X) (f : X → List (K × FifoOp V)) :
    deqs (s.flatMap f) = s.flatMap (fun x => deqs (f x)) := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [List.flatMap_cons, ih]

lemma length_enqs_add_length_deqs {K : Type} (l : List (K × FifoOp V)) :
    (enqs l).length + (deqs l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨x, o⟩ := a
    cases o <;> simp [enqs, deqs] at ih ⊢ <;> omega

lemma Perm.enqs_length {K : Type} {l l' : List (K × FifoOp V)} (h : l.Perm l') :
    (enqs l).length = (enqs l').length := (h.filterMap _).length_eq

lemma Perm.deqs_length {K : Type} {l l' : List (K × FifoOp V)} (h : l.Perm l') :
    (deqs l).length = (deqs l').length := (h.filterMap _).length_eq

/-- The operation represented by a leaf block. -/
def blkOp (B : Blk V) : FifoOp V :=
  match B.elem with
  | some x => .enq x
  | none => .deq

/-- The block indices `a+1, …, b` (the subblocks between two consecutive `end` values). -/
def rng (a b : ℕ) : List ℕ := List.range' (a + 1) (b - a)

section Ops

variable (H np : ℕ)

/-- The operation of the leaf block `n.blocks[i]` (`i ≥ 1`) of the leaf `n = 2^H + p`: the
`(i-1)`-th operation of `p`. -/
def leafOps (n i : ℕ) (B : Blk V) : List (OpId (Fin np) × FifoOp V) :=
  if h : 2 ^ H ≤ n ∧ n - 2 ^ H < np then [((⟨n - 2 ^ H, h.2⟩, i - 1), blkOp B)] else []

/-- The operations represented by `n.blocks[i]`, `n` at height `k`, in subblock order. -/
def opsK (M : Mem V) : ℕ → ℕ → ℕ → List (OpId (Fin np) × FifoOp V)
  | _, _, 0 => []
  | 0, n, i + 1 => match M.blk n (i + 1) with
    | some B => leafOps H np n (i + 1) B
    | none => []
  | k + 1, n, i + 1 =>
    (rng (M.bk n i).endl (M.bk n (i + 1)).endl).flatMap (opsK M k (2 * n)) ++
    (rng (M.bk n i).endr (M.bk n (i + 1)).endr).flatMap (opsK M k (2 * n + 1))

/-- The operations of the blocks `1..i` of `n`. -/
def preK (M : Mem V) (k n i : ℕ) : List (OpId (Fin np) × FifoOp V) :=
  (List.range' 1 i).flatMap (opsK H np M k n)

variable {H np}

@[simp] lemma opsK_zero_right (M : Mem V) (k n : ℕ) : opsK H np M k n 0 = [] := by
  cases k <;> rfl

lemma opsK_succ_succ (M : Mem V) (k n i : ℕ) : opsK H np M (k + 1) n (i + 1) =
    (rng (M.bk n i).endl (M.bk n (i + 1)).endl).flatMap (opsK H np M k (2 * n)) ++
    (rng (M.bk n i).endr (M.bk n (i + 1)).endr).flatMap (opsK H np M k (2 * n + 1)) := rfl

lemma opsK_zero_succ (M : Mem V) (n i : ℕ) : opsK H np M 0 n (i + 1) =
    match M.blk n (i + 1) with
    | some B => leafOps H np n (i + 1) B
    | none => [] := rfl

@[simp] lemma preK_zero (M : Mem V) (k n : ℕ) : preK H np M k n 0 = [] := rfl

lemma preK_succ (M : Mem V) (k n i : ℕ) :
    preK H np M k n (i + 1) = preK H np M k n i ++ opsK H np M k n (i + 1) := by
  simp [preK, List.range'_1_concat, List.flatMap_append, Nat.add_comm 1 i]

lemma flatMap_range'_split {X : Type} (f : ℕ → List X) {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
    (List.range' 1 b).flatMap f ++ (rng b c).flatMap f = (List.range' 1 c).flatMap f := by
  have : List.range' 1 c = List.range' 1 b ++ List.range' (1 + b) (c - b) := by
    have := List.range'_append (s := 1) (m := b) (n := c - b) (step := 1)
    simp only [Nat.one_mul] at this
    rw [this]; congr 1; omega
  rw [this, List.flatMap_append, rng, Nat.add_comm b 1]

/-- **Subblocks of a prefix (3.3).** If the `end` fields of the blocks `0..i` of `n` are
monotone and start at `0`, the blocks `1..i` of `n` represent the blocks `1..endl` of the left
child and `1..endr` of the right child (up to order). -/
lemma preK_perm (M : Mem V) (k n i : ℕ) (h0l : (M.bk n 0).endl = 0) (h0r : (M.bk n 0).endr = 0)
    (hmono : ∀ j, j < i → (M.bk n j).endl ≤ (M.bk n (j + 1)).endl ∧
      (M.bk n j).endr ≤ (M.bk n (j + 1)).endr) :
    (preK H np M (k + 1) n i).Perm
      (preK H np M k (2 * n) (M.bk n i).endl ++ preK H np M k (2 * n + 1) (M.bk n i).endr) := by
  induction i with
  | zero => simp [h0l, h0r, preK]
  | succ i ih =>
    have ih := ih (fun j hj => hmono j (by omega))
    obtain ⟨hl, hr⟩ := hmono i (by omega)
    rw [preK_succ, opsK_succ_succ]
    have e1 := flatMap_range'_split (opsK H np M k (2 * n)) (a := 0) (Nat.zero_le _) hl
    have e2 := flatMap_range'_split (opsK H np M k (2 * n + 1)) (a := 0) (Nat.zero_le _) hr
    simp only [preK] at ih ⊢
    rw [← e1, ← e2]
    refine (ih.append_right _).trans ?_
    simp only [List.append_assoc]
    refine List.Perm.append_left _ ?_
    simp only [← List.append_assoc]
    refine List.Perm.append_right _ ?_
    exact List.perm_append_comm

/-- Keys of the operations of `n.blocks[i]`: instances `(p, j)` of processes whose leaf is
below `n` (`(2^H + p) / 2^k = n`). -/
lemma mem_opsK (M : Mem V) (k n i : ℕ) {x : OpId (Fin np) × FifoOp V}
    (hx : x ∈ opsK H np M k n i) : (2 ^ H + x.1.1) / 2 ^ k = n := by
  induction k generalizing n i with
  | zero =>
    cases i with
    | zero => simp at hx
    | succ i =>
      rw [opsK_zero_succ] at hx
      split at hx
      · simp only [leafOps] at hx
        split_ifs at hx with h
        · simp at hx; subst hx; simp; omega
        · simp at hx
      · simp at hx
  | succ k ih =>
    cases i with
    | zero => simp at hx
    | succ i =>
      rw [opsK_succ_succ] at hx
      simp only [List.mem_append, List.mem_flatMap] at hx
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
      rcases hx with ⟨j, -, hj⟩ | ⟨j, -, hj⟩
      · rw [ih _ _ hj]; omega
      · rw [ih _ _ hj]; omega

lemma mem_preK (M : Mem V) (k n i : ℕ) {x : OpId (Fin np) × FifoOp V}
    (hx : x ∈ preK H np M k n i) : (2 ^ H + x.1.1) / 2 ^ k = n := by
  simp only [preK, List.mem_flatMap] at hx
  obtain ⟨j, -, hj⟩ := hx
  exact mem_opsK M k n j hj

/-- The leaf-level keys: the operations of the blocks `1..i` of a leaf are instances with
index `< i`. -/
lemma mem_preK_zero (M : Mem V) (n i : ℕ) {x : OpId (Fin np) × FifoOp V}
    (hx : x ∈ preK H np M 0 n i) : x.1.2 < i := by
  simp only [preK, List.mem_flatMap, List.mem_range'] at hx
  obtain ⟨j, ⟨a, ha, rfl⟩, hj⟩ := hx
  rw [show 1 + 1 * a = a + 1 by omega, opsK_zero_succ] at hj
  split at hj
  · simp only [leafOps] at hj; split_ifs at hj <;> simp at hj; subst hj; simp; omega
  · simp at hj

/-- The keys of the operations of the blocks `1..i` of a node are distinct (given monotone
`end` fields along the used prefixes). -/
lemma nodup_keys_preK (M : Mem V) (c : ℕ → ℕ)
    (h0 : ∀ m, (M.bk m 0).endl = 0 ∧ (M.bk m 0).endr = 0)
    (hmono : ∀ m j, j < c m → (M.bk m j).endl ≤ (M.bk m (j + 1)).endl ∧
      (M.bk m j).endr ≤ (M.bk m (j + 1)).endr)
    (hend : ∀ m j, j ≤ c m → (M.bk m j).endl ≤ c (2 * m) ∧ (M.bk m j).endr ≤ c (2 * m + 1))
    (k n i : ℕ) (hi : i ≤ c n) :
    ((preK H np M k n i).map Prod.fst).Nodup := by
  induction k generalizing n i with
  | zero =>
    clear hi
    induction i with
    | zero => simp
    | succ i ih =>
      rw [preK_succ, List.map_append, List.nodup_append]
      refine ⟨ih, ?_, ?_⟩
      · rw [opsK_zero_succ]; split
        · simp only [leafOps]; split_ifs <;> simp
        · simp
      · intro a ha b hb hab
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hb
        have h1 := mem_preK_zero M n i hy
        rw [opsK_zero_succ] at hz
        split at hz
        · simp only [leafOps] at hz; split_ifs at hz <;> simp at hz; subst hz
          rw [hab] at h1; simp at h1
        · simp at hz
  | succ k ih =>
    have hp := preK_perm (H := H) (np := np) M k n i (h0 n).1 (h0 n).2
      (fun j hj => hmono n j (by omega))
    refine (hp.map Prod.fst).nodup_iff.2 ?_
    rw [List.map_append, List.nodup_append]
    refine ⟨ih _ _ (hend n i hi).1, ih _ _ (hend n i hi).2, ?_⟩
    intro a ha b hb hab
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hb
    have h1 := mem_preK M k _ _ hy
    have h2 := mem_preK M k _ _ hz
    rw [hab] at h1; omega

end Ops

end Podc.WaitFreeQueuePolylog
