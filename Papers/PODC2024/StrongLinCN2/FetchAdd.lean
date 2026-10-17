import Podc.StrongLin.OneAccess
import Podc.SharedMemory.Objects
import Papers.PODC2024.StrongLinCN2.Packing

/-!
# Max register and atomic snapshot from `fetch&add` (Theorems 1 and 2)

Attiya, Castañeda and Enea, *Strong Linearizability using Primitives with Consensus Number 2*,
PODC 2024, Sections 3.1 and 3.2.

`n` processes `Fin n` share one unbounded `fetch&add` register `R`; bit `j` of process `i` is
bit `j * n + i` of `R` (`Packing.lean`).

* **Max register (Theorem 1).** Process `i` stores the largest value it has written in unary
  (bits `1, …, prevLocalMax`). `WriteMax(K)`: if `K ≤ prevLocalMax` then `fetch&add(R, 0)`;
  otherwise `fetch&add(R, ∑_{j = prevLocalMax+1}^{K} 2^{j n + i})` and `prevLocalMax := K`.
  `ReadMax`: `fetch&add(R, 0)`, reconstruct each process's maximum (the number of its set bits)
  and return the largest. Register values are natural numbers.
* **Snapshot (Theorem 2).** Process `i`'s component (a natural number) is stored in binary in its
  bits. `update(v)`: if `v = prevVal` then `fetch&add(R, 0)`; otherwise
  `fetch&add(R, posAdj − negAdj)` (bits to set minus bits to clear) and `prevVal := v`.
  `scan`: `fetch&add(R, 0)` and decode. The adjustment may be negative, so `R` is an integer
  `fetch&add` register.

Both are single-access implementations (`Podc/StrongLin/OneAccess.lean`), hence wait-free and
strongly linearizable, with linearization point at the unique `fetch&add`.
-/

namespace StrongLinCN2

open Cslib.SharedMemory Finset

/-! ## Theorem 1: max register -/

section MaxReg

variable (n : ℕ)

/-- The unary bit set of a local maximum `m`: bits `1, …, m`. -/
def unary (m : ℕ) : Finset ℕ := Icc 1 m

/-- `ReadMax`'s decoding: the largest of the reconstructed individual maxima. -/
def decodeMax (R : ℕ) : ℕ := univ.sup (fun i : Fin n => (comp n R i).card)

/-- The `fetch&add` argument of `WriteMax(K)` by process `i` with local maximum `prev`. -/
def wmArg (i : Fin n) (prev K : ℕ) : ℕ :=
  if K ≤ prev then 0 else ∑ j ∈ Ioc prev K, 2 ^ pos n i j

/-- The max-register implementation of Section 3.1 as a single-access scheme. -/
def maxRegScheme : OneAccess maxRegObj (fun _ : Unit => faaObj ℕ) (Fin n) ℕ where
  memInit _ := 0
  dInit _ := 0
  obj _ _ _ := ()
  prim i prev
    | .writeMax K => wmArg n i prev K
    | .readMax => 0
  upd _ prev
    | .writeMax K => fun _ => if K ≤ prev then prev else K
    | .readMax => fun _ => prev
  out _ _
    | .writeMax _ => fun _ => 0
    | .readMax => fun R => decodeMax n R

/-- The max-register implementation (`Impl`). -/
noncomputable def maxRegImpl : Impl maxRegObj (fun _ : Unit => faaObj ℕ) (Fin n) (OALoc ℕ maxRegObj) :=
  (maxRegScheme n).impl 0

/-- The abstraction relation: `R` packs every process's local maximum in unary, and the
abstract value is the largest local maximum. -/
def maxAbs (m : (_ : Unit) → ℕ) (ds : Fin n → ℕ) (s : ℕ) : Prop :=
  m () = pack n (fun i => unary (ds i)) ∧ s = univ.sup ds

lemma decodeMax_pack (ds : Fin n → ℕ) : decodeMax n (pack n (fun i => unary (ds i))) = univ.sup ds := by
  simp [decodeMax, comp_pack, unary]

lemma sup_update_le (ds : Fin n → ℕ) (i : Fin n) (K : ℕ) (h : ds i ≤ K) :
    univ.sup (Function.update ds i K) = max (univ.sup ds) K := by
  apply le_antisymm
  · refine Finset.sup_le (fun j _ => ?_)
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]; exact le_max_of_le_left (le_sup (mem_univ j))
  · refine max_le (Finset.sup_le (fun j _ => ?_)) ?_
    · by_cases hj : j = i
      · subst hj; exact h.trans (by simpa using le_sup (f := Function.update ds j K) (mem_univ j))
      · have := le_sup (f := Function.update ds i K) (mem_univ j)
        rwa [Function.update_of_ne hj] at this
    · simpa using le_sup (f := Function.update ds i K) (mem_univ i)

lemma maxSim : (maxRegScheme n).Sim (maxAbs n) where
  init := ⟨by simp [maxRegScheme, pack, unary], (Finset.sup_bot _).symm⟩
  step := by
    intro m ds s p d o hd ⟨hm, hs⟩ _
    subst hd hs
    cases o with
    | readMax =>
      simp only [maxRegScheme, maxAbs, Function.update_eq_self]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [hm, decodeMax_pack]
    | writeMax K =>
      simp only [maxRegScheme, maxAbs]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      rotate_left 2
      · trivial
      · simp only [Function.update_self, wmArg]
        split_ifs with hK
        · rw [Function.update_eq_self, hm, add_zero]
        · push Not at hK
          have : (fun i => unary (Function.update ds p K i)) =
              Function.update (fun i => unary (ds i)) p (unary K) := by
            funext i; by_cases hi : i = p
            · subst hi; simp
            · simp [Function.update_of_ne hi]
          rw [this, pack_update_of_subset _ _ _ _ (Icc_subset_Icc le_rfl hK.le), hm]
          congr 1
          refine sum_congr ?_ (fun _ _ => rfl)
          ext j; simp [unary]; omega
      · split_ifs with hK
        · rw [Function.update_eq_self]
          exact max_eq_left (hK.trans (le_sup (f := ds) (mem_univ p)))
        · push Not at hK
          rw [sup_update_le n ds p K hK.le]

/-- **Theorem 1** (Attiya–Castañeda–Enea, PODC 2024): the max register of Section 3.1 is a
wait-free strongly-linearizable implementation of a max register from `fetch&add`. -/
theorem theorem1 : (maxRegImpl n).WaitFree ∧ (maxRegImpl n).StronglyLinearizable :=
  ⟨(maxRegScheme n).waitFree 0, (maxRegScheme n).stronglyLinearizable (maxSim n) 0⟩

end MaxReg

/-! ## Theorem 2: atomic snapshot -/

section Snapshot

variable (n : ℕ)

/-- The binary bit set of a value. -/
def binBits (v : ℕ) : Finset ℕ := v.bitIndices.toFinset

/-- `scan`'s decoding of the register value. -/
def decodeView (R : ℤ) : Fin n → ℕ := fun i => ∑ j ∈ comp n R.toNat i, 2 ^ j

/-- `posAdj − negAdj` for process `i` changing its component from `prev` to `v`. -/
def updArg (i : Fin n) (prev v : ℕ) : ℤ :=
  if v = prev then 0 else
    ((∑ j ∈ binBits v \ binBits prev, 2 ^ pos n i j : ℕ) : ℤ) -
      ((∑ j ∈ binBits prev \ binBits v, 2 ^ pos n i j : ℕ) : ℤ)

/-- The snapshot implementation of Section 3.2 as a single-access scheme. Process `i` may only
update component `i`. -/
def snapScheme : OneAccess (snapObj n) (fun _ : Unit => faaObj ℤ) (Fin n) ℕ where
  memInit _ := 0
  dInit _ := 0
  obj _ _ _ := ()
  prim i prev
    | .update _ v => updArg n i prev v
    | .scan => 0
  upd _ prev
    | .update _ v => fun _ => v
    | .scan => fun _ => prev
  out _ _
    | .update _ _ => fun _ => fun _ => 0
    | .scan => fun R => decodeView n R
  allowed i
    | .update j _ => j = i
    | .scan => True

/-- The snapshot implementation (`Impl`). -/
noncomputable def snapImpl :
    Impl (snapObj n) (fun _ : Unit => faaObj ℤ) (Fin n) (OALoc ℕ (snapObj n)) :=
  (snapScheme n).impl (fun _ => 0)

/-- The abstraction relation: `R` packs every process's current component in binary (the
local `prevVal`s), and the abstract view is the vector of the `prevVal`s. -/
def snapAbs (m : (_ : Unit) → ℤ) (ds : Fin n → ℕ) (s : Fin n → ℕ) : Prop :=
  m () = (pack n (fun i => binBits (ds i)) : ℤ) ∧ s = ds

lemma decodeView_pack (ds : Fin n → ℕ) :
    decodeView n (pack n (fun i => binBits (ds i)) : ℤ) = ds := by
  funext i
  simp [decodeView, comp_pack, binBits]

lemma snapSim : (snapScheme n).Sim (snapAbs n) where
  init := ⟨by simp [snapScheme, pack, binBits], rfl⟩
  step := by
    intro m ds s p d o hd ⟨hm, hs⟩ hal
    subst hd s
    cases o with
    | scan =>
      simp only [snapScheme, snapAbs, Function.update_eq_self]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [hm, decodeView_pack]
    | update j v =>
      simp only [snapScheme] at hal
      subst hal
      simp only [snapScheme, snapAbs]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      rotate_left 1
      · trivial
      · trivial
      simp only [Function.update_self, updArg]
      have : (fun i => binBits (Function.update ds j v i)) =
          Function.update (fun i => binBits (ds i)) j (binBits v) := by
        funext i; by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      rw [this, pack_update_int, hm]
      split_ifs with hv
      · subst hv; simp
      · rfl

/-- **Theorem 2** (Attiya–Castañeda–Enea, PODC 2024): the snapshot of Section 3.2 is a wait-free
strongly-linearizable implementation of an `n`-component single-writer atomic snapshot from
`fetch&add`. -/
theorem theorem2 : (snapImpl n).WaitFree ∧ (snapImpl n).StronglyLinearizable :=
  ⟨(snapScheme n).waitFree _, (snapScheme n).stronglyLinearizable (snapSim n) _⟩

end Snapshot

end StrongLinCN2
