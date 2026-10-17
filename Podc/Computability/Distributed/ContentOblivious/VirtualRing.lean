import Cslib.Computability.Distributed.ContentOblivious.VirtualRing

-- CSLib candidate: Cslib/Computability/Distributed/ContentOblivious/VirtualRing.lean (append to the
-- existing file)

/-!
# The virtual ring: characterization by clockwise distance

Additions to `Cslib/Computability/Distributed/ContentOblivious/VirtualRing.lean`: the virtual
neighbours `vnext act v` / `vprev act v` are `v + k` / `v - k` for the least `k ≥ 1` such that this
node is active, and `vprev` is the mirror image of `vnext`.

## Main statements

* `vnext_spec`, `vprev_spec`: characterization by the least active distance.
* `vprev_eq_neg_vnext_neg`: reflecting the ring `v ↦ -v` exchanges `vnext` and `vprev`.
-/

namespace Cslib.ContentOblivious

variable {n : ℕ}

/-- Reflecting the ring `v ↦ -v` exchanges the virtual successor and predecessor. -/
theorem vprev_eq_neg_vnext_neg (act : ZMod n → Bool) (v : ZMod n) :
    vprev act v = -vnext (fun w => act (-w)) (-v) := by
  have e : ∀ k : ℕ, -(-v + (k : ZMod n)) = v - k := fun k => by ring
  simp only [vprev, vnext, e]
  split_ifs <;> simp only [neg_add, neg_neg, sub_eq_add_neg]

variable {act : ZMod n → Bool} [NeZero n]

/-- The virtual successor of `v` is `v + k` for the least `k ≥ 1` such that `v + k` is active
(`k ≤ n`; `k = n` iff `v` is the only active node), provided some node is active. -/
theorem vnext_spec {u : ZMod n} (hu : act u = true) (v : ZMod n) :
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ vnext act v = v + k ∧ act (v + k) = true ∧
      ∀ j : ℕ, 0 < j → j < k → act (v + j) = false := by
  have h := exists_next_active hu v
  refine ⟨Nat.find h + 1, Nat.succ_pos _, (Nat.find_spec h).1, ?_, (Nat.find_spec h).2,
    fun j hj hjk => ?_⟩
  · rw [vnext, dite_eq_left h]
  · have := Nat.find_min h (show j - 1 < Nat.find h by omega)
    rw [show j - 1 + 1 = j by omega] at this
    simpa [show j - 1 < n by have := (Nat.find_spec h).1; omega] using this

/-- The virtual predecessor of `v` is `v - k` for the least `k ≥ 1` such that `v - k` is active
(`k ≤ n`), provided some node is active. -/
theorem vprev_spec {u : ZMod n} (hu : act u = true) (v : ZMod n) :
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ vprev act v = v - k ∧ act (v - k) = true ∧
      ∀ j : ℕ, 0 < j → j < k → act (v - j) = false := by
  have h := exists_prev_active hu v
  refine ⟨Nat.find h + 1, Nat.succ_pos _, (Nat.find_spec h).1, ?_, (Nat.find_spec h).2,
    fun j hj hjk => ?_⟩
  · rw [vprev, dite_eq_left h]
  · have := Nat.find_min h (show j - 1 < Nat.find h by omega)
    rw [show j - 1 + 1 = j by omega] at this
    simpa [show j - 1 < n by have := (Nat.find_spec h).1; omega] using this

end Cslib.ContentOblivious
