import Mathlib

/-!
# Blocks of the write lower bound (§4)

The proof of Lemma 1 partitions the objects into blocks `B₀, …, B_{k+1}` and `C₁, …, C_k` and uses
the superblocks
* `M_l = {B_j | 0 ≤ j ≤ l} ∪ {C_j | 1 ≤ j ≤ l}` ("malicious"), here `Mlt m = M_{m-1}`;
* `P_l = {B_j | l ≤ j ≤ k+1, j ≡ l (mod 2)}` ("parity");
* `𝒞_l = {C_j | l ≤ j ≤ k}` ("correct"), here `CC k l`.

The construction only needs *upper* bounds on the number of objects in the sets that are
malicious in some run or skipped by some terminated round (`Fits`); the paper's block sizes
(`|B_l| = t_l - t_{l-2}` etc.) are one solution with `t = t_k` and `S = 3 t_k + 1`.
-/

namespace Podc.RobustAtomicStorage

/-- Block names. Only `B x` with `x ≤ k + 1` and `C x` with `1 ≤ x ≤ k` are used. -/
inductive Blk where
  | B (x : ℕ)
  | C (x : ℕ)
  deriving DecidableEq

namespace Blk

/-- The block is one of `B₀, …, B_{k+1}, C₁, …, C_k`. -/
def Valid (k : ℕ) : Blk → Prop
  | B x => x ≤ k + 1
  | C x => 1 ≤ x ∧ x ≤ k

/-- `Mlt m b`: `b ∈ M_{m-1}`, i.e. `b = B x` with `x < m` or `b = C x` with `1 ≤ x < m`. -/
def Mlt (m : ℕ) : Blk → Prop
  | B x => x < m
  | C x => 1 ≤ x ∧ x < m

/-- `P k l b`: `b ∈ P_l = {B_j | l ≤ j ≤ k+1, j ≡ l (mod 2)}`. -/
def P (k l : ℕ) : Blk → Prop
  | B x => l ≤ x ∧ x ≤ k + 1 ∧ x % 2 = l % 2
  | C _ => False

/-- `CC k l b`: `b ∈ 𝒞_l = {C_j | l ≤ j ≤ k}`. -/
def CC (k l : ℕ) : Blk → Prop
  | B _ => False
  | C x => l ≤ x ∧ x ≤ k

instance (k : ℕ) (b : Blk) : Decidable (Valid k b) := by cases b <;> unfold Valid <;> infer_instance
instance (m : ℕ) (b : Blk) : Decidable (Mlt m b) := by cases b <;> unfold Mlt <;> infer_instance
instance (k l : ℕ) (b : Blk) : Decidable (P k l b) := by cases b <;> unfold P <;> infer_instance
instance (k l : ℕ) (b : Blk) : Decidable (CC k l b) := by cases b <;> unfold CC <;> infer_instance

end Blk

open Blk

/-- Number of objects whose block satisfies `p`. -/
def nBlk {Obj : Type} [Fintype Obj] (blk : Obj → Blk) (p : Blk → Prop) [DecidablePred p] : ℕ :=
  (Finset.univ.filter fun s => p (blk s)).card

/-- The block assignment `blk` fits the write lower-bound construction for `k` write rounds and
`t` malicious objects: every block is valid, and every set of objects that is malicious in some
run, or skipped by some terminated round, has at most `t` objects:
* (a) `M_{k-1}`;
* (b) `M_{l-3} ∪ P_l` for `1 ≤ l ≤ k + 1` (this covers `P_1`, `M_{l-2} ∪ P_{l+1}` and
  `M_{k-2} ∪ P_{k+1}`);
* (c) `M_{l-2} ∪ 𝒞_{l+1}` for `0 ≤ l ≤ k - 1` (this covers `𝒞_1`). -/
structure Fits {Obj : Type} [Fintype Obj] (k t : ℕ) (blk : Obj → Blk) : Prop where
  valid : ∀ s, Valid k (blk s)
  a : nBlk blk (Mlt k) ≤ t
  b : ∀ l, 1 ≤ l → l ≤ k + 1 → nBlk blk (fun b => Mlt (l - 2) b ∨ P k l b) ≤ t
  c : ∀ l, l + 1 ≤ k → nBlk blk (fun b => Mlt (l - 1) b ∨ CC k (l + 1) b) ≤ t

/-- The sequence `t₋₁ = t₀ = 0`, `t_k = t_{k-1} + 2 t_{k-2} + 1` (Lemma 1); `tseq k = t_k`. -/
def tseq : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (k + 2) => tseq (k + 1) + 2 * tseq k + 1

end Podc.RobustAtomicStorage
