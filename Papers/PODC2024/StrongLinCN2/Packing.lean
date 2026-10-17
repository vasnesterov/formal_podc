import Mathlib

/-!
# Interleaved bit packing

Attiya, Castañeda and Enea (PODC 2024, Sections 3.1–3.2) store an `n`-component vector in a single
unbounded `fetch&add` register `R` by *interleaving* the bits of the processes: bit `j` of
process `i` is bit `j * n + i` of `R`. Here a component is described by its set of bits
`E i : Finset ℕ`; `pack n E = ∑ i, ∑ j ∈ E i, 2 ^ (j * n + i)`.

* `comp_pack`: the bits of component `i` can be read back from `pack n E`;
* `pack_update_of_subset`, `pack_update_int`: changing component `i` changes `pack` by the sum of
  the bits set minus the sum of the bits cleared (the `fetch&add` argument).
-/

namespace StrongLinCN2

open Finset

/-- Position of bit `j` of component `i`. -/
def pos (n : ℕ) (i : Fin n) (j : ℕ) : ℕ := j * n + i

lemma pos_mod (n : ℕ) (i : Fin n) (j : ℕ) : pos n i j % n = i := by
  simp [pos, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

lemma pos_div (n : ℕ) (i : Fin n) (j : ℕ) : pos n i j / n = j := by
  have hn : 0 < n := Fin.pos i
  simp only [pos]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt i.isLt, Nat.zero_add]

lemma pos_injective (n : ℕ) (i : Fin n) : Function.Injective (pos n i) := by
  intro j j' h
  have := congrArg (· / n) h
  simpa [pos_div] using this

/-- All bit positions used by the vector `E`. -/
def bits (n : ℕ) (E : Fin n → Finset ℕ) : Finset ℕ := univ.biUnion (fun i => (E i).image (pos n i))

/-- The packed register value. -/
def pack (n : ℕ) (E : Fin n → Finset ℕ) : ℕ := ∑ i, ∑ j ∈ E i, 2 ^ pos n i j

lemma pack_eq (n : ℕ) (E : Fin n → Finset ℕ) : pack n E = ∑ b ∈ bits n E, 2 ^ b := by
  rw [bits, sum_biUnion]
  · refine sum_congr rfl (fun i _ => ?_)
    rw [sum_image (fun j _ j' _ h => pos_injective n i h)]
  · intro i _ i' _ hii'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro b hb hb'
    obtain ⟨j, -, rfl⟩ := mem_image.1 hb
    obtain ⟨j', -, h⟩ := mem_image.1 hb'
    have := congrArg (· % n) h
    simp only [pos_mod] at this
    exact hii' (Fin.ext this).symm

/-- The bits of component `i` read back from a register value `R`. -/
def comp (n : ℕ) (R : ℕ) (i : Fin n) : Finset ℕ :=
  ((R.bitIndices.toFinset).filter (fun b => b % n = i)).image (· / n)

lemma comp_pack (n : ℕ) (E : Fin n → Finset ℕ) (i : Fin n) : comp n (pack n E) i = E i := by
  rw [comp, pack_eq, Finset.toFinset_bitIndices_sum_two_pow]
  ext j
  simp only [mem_image, mem_filter, bits, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨b, ⟨⟨i', j', hj', rfl⟩, hmod⟩, rfl⟩
    rw [pos_mod] at hmod
    have : i' = i := Fin.ext hmod
    subst this
    rwa [pos_div]
  · intro hj
    exact ⟨pos n i j, ⟨⟨i, j, hj, rfl⟩, pos_mod n i j⟩, pos_div n i j⟩

lemma pack_update (n : ℕ) (E : Fin n → Finset ℕ) (i : Fin n) (F : Finset ℕ) :
    pack n (Function.update E i F) + ∑ j ∈ E i, 2 ^ pos n i j =
      pack n E + ∑ j ∈ F, 2 ^ pos n i j := by
  simp only [pack]
  rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_univ i)]
  have : ∑ x ∈ univ.erase i, ∑ j ∈ Function.update E i F x, 2 ^ pos n x j =
      ∑ x ∈ univ.erase i, ∑ j ∈ E x, 2 ^ pos n x j := by
    refine sum_congr rfl (fun x hx => ?_)
    rw [Function.update_of_ne (ne_of_mem_erase hx)]
  rw [this, Function.update_self]
  ring

/-- Setting bits (component `i` grows from `E i` to `F ⊇ E i`). -/
lemma pack_update_of_subset (n : ℕ) (E : Fin n → Finset ℕ) (i : Fin n) (F : Finset ℕ)
    (h : E i ⊆ F) :
    pack n (Function.update E i F) = pack n E + ∑ j ∈ F \ E i, 2 ^ pos n i j := by
  have h1 := pack_update n E i F
  rw [← sum_sdiff h] at h1
  omega

/-- Setting and clearing bits (as an integer `fetch&add` argument). -/
lemma pack_update_int (n : ℕ) (E : Fin n → Finset ℕ) (i : Fin n) (F : Finset ℕ) :
    (pack n (Function.update E i F) : ℤ) =
      pack n E + ((∑ j ∈ F \ E i, 2 ^ pos n i j : ℕ) - (∑ j ∈ E i \ F, 2 ^ pos n i j : ℕ)) := by
  have h1 := pack_update n E i F
  have h2 := sum_sdiff (f := fun j => 2 ^ pos n i j) (inter_subset_left (s₁ := F) (s₂ := E i))
  have h3 := sum_sdiff (f := fun j => 2 ^ pos n i j) (inter_subset_left (s₁ := E i) (s₂ := F))
  rw [sdiff_inter_self_left] at h2 h3
  rw [inter_comm] at h3
  have h4 : (pack n (Function.update E i F) : ℤ) + (∑ j ∈ E i, 2 ^ pos n i j : ℕ) =
      pack n E + (∑ j ∈ F, 2 ^ pos n i j : ℕ) := by exact_mod_cast h1
  rw [← h2, ← h3] at h4
  push_cast at h4 ⊢
  linarith

end StrongLinCN2
