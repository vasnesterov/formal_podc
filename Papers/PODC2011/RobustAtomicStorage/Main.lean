import Papers.PODC2011.RobustAtomicStorage.ReadLB
import Papers.PODC2011.RobustAtomicStorage.WriteLB
import Papers.PODC2011.RobustAtomicStorage.Arith

/-!
# Main results of "The Complexity of Robust Atomic Storage" (PODC 2011)

Dan Dobre, Rachid Guerraoui, Matthias Majuntke, Neeraj Suri, Marko Vukolić.

Model (`Model.lean`): asynchronous message passing between one writer, `R = card Rd` readers and
`S = card Obj` storage objects, at most `t` of which are malicious; no authentication; round-based
operations (a round terminates once `S - t` objects replied); deterministic protocols with a fixed
number `K` of write rounds and `N` of read rounds; atomicity of the SWMR register (§2.2).

* `proposition1`: if `S ≤ 4t` and `R > 3`, no implementation has two-round reads.
* `lemma1`: with `3 t_k + 1` objects, `t_k` faults and `k` readers there is no implementation with
  `k`-round writes and three-round reads (`t_{-1} = t_0 = 0`, `t_k = t_{k-1} + 2 t_{k-2} + 1`).
* `lemma2`: optimal resilience `S ≤ 3t + 1`: with three-round reads, writes need more than
  `min {R, ⌊log ⌈(3t+1)/2⌉⌋}` rounds.
* `proposition2`: `S ≤ 3t + ⌊t / t_k⌋`: with three-round reads, writes need more than
  `min {R, ⌊log ⌈(3t_k+1)/2⌉⌋} = min {R, k}` rounds.
* `tseq_closed_form`: `t_k = (2^{k+2} - (-1)^k - 3) / 6`.
-/

namespace Podc.RobustAtomicStorage

open Classical

variable {Obj Rd V Msg Rep : Type} [Fintype Obj] [DecidableEq Obj] [Fintype Rd] [DecidableEq Rd]
  [DecidableEq V]

/-- An injection of `Fin n` into the readers when `n ≤ R`. -/
lemma exists_readers {n : ℕ} (h : n ≤ Fintype.card Rd) : ∃ rd : Fin n → Rd, Function.Injective rd :=
  ⟨fun i => (Fintype.equivFin Rd).symm (Fin.castLE h i),
    fun _ _ hij => Fin.castLE_injective h ((Fintype.equivFin Rd).symm.injective hij)⟩

/-- **Proposition 1** of [DGMSV11] (read lower bound): if `S ≤ 4t` and `R > 3`, then no
implementation of a SWMR atomic register (with writes of any number `K ≥ 1` of rounds) has all
reads complete in two rounds. -/
theorem proposition1 (P : Proto Obj Rd V Msg Rep) (t : ℕ) (hS : Fintype.card Obj ≤ 4 * t)
    (hR : 3 < Fintype.card Rd) (hK : 1 ≤ P.K) (hN : P.N = 2) (bot : V) (hV : ∃ v : V, v ≠ bot) :
    ¬ P.Atomic t bot := by
  obtain ⟨blk, hblk⟩ := exists_four_blocks t hS
  obtain ⟨rd, hrd⟩ := exists_readers (n := 4) hR
  obtain ⟨v₁, hv⟩ := hV
  exact ReadLB.read_lb P hK hN t Finset.univ.toList (Finset.nodup_toList _)
    (fun s => Finset.mem_toList.2 (Finset.mem_univ s)) blk hblk rd hrd v₁ bot hv

/-- Readers `rd 1, …, rd k` (distinct) from `k ≤ R`. -/
lemma exists_readers' {k : ℕ} (hk : 1 ≤ k) (h : k ≤ Fintype.card Rd) :
    ∃ rd : ℕ → Rd, ∀ i j, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → rd i = rd j → i = j := by
  obtain ⟨e, he⟩ := exists_readers h
  refine ⟨fun i => e ⟨(i - 1) % k, Nat.mod_lt _ (by omega)⟩, fun i j hi hik hj hjk hij => ?_⟩
  have := congrArg Fin.val (he hij)
  simp only at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- **Lemma 1** of [DGMSV11] (write lower bound): with `S = 3 t_k + 1` objects, `t_k` malicious
objects and `R ≥ k` readers, no SWMR atomic register implementation has writes completing in
`k ≥ 1` rounds and reads completing in three rounds. (The paper proves `k ≥ 2` and cites [1] for
`k = 1`; the same construction covers `k = 1`.) -/
theorem lemma1 (k : ℕ) (hk : 1 ≤ k) (hS : Fintype.card Obj = 3 * tseq k + 1)
    (hR : k ≤ Fintype.card Rd) (P : Proto Obj Rd V Msg Rep) (hK : P.K = k) (hN : P.N = 3)
    (bot : V) (hV : ∃ v : V, v ≠ bot) : ¬ P.Atomic (tseq k) bot := by
  obtain ⟨blk, hfit⟩ := exists_fits_paper k hk hS
  obtain ⟨rd, hrd⟩ := exists_readers' hk hR
  obtain ⟨v₁, hv⟩ := hV
  exact WriteLB.write_lb P k hk hK hN (tseq k) Finset.univ.toList (Finset.nodup_toList _)
    (fun s => Finset.mem_toList.2 (Finset.mem_univ s)) blk hfit rd hrd v₁ bot hv

/-- The block form behind Lemmas 1, 2 and Proposition 2: `S ≤ 3t + ⌊t / t_k⌋`, `R ≥ k`. -/
theorem write_lb_general (k t : ℕ) (hk : 1 ≤ k) (hS : Fintype.card Obj ≤ 3 * t + t / tseq k)
    (hR : k ≤ Fintype.card Rd) (P : Proto Obj Rd V Msg Rep) (hK : P.K = k) (hN : P.N = 3)
    (bot : V) (hV : ∃ v : V, v ≠ bot) : ¬ P.Atomic t bot := by
  obtain ⟨blk, hfit⟩ := exists_fits k t hk hS
  obtain ⟨rd, hrd⟩ := exists_readers' hk hR
  obtain ⟨v₁, hv⟩ := hV
  exact WriteLB.write_lb P k hk hK hN t Finset.univ.toList (Finset.nodup_toList _)
    (fun s => Finset.mem_toList.2 (Finset.mem_univ s)) blk hfit rd hrd v₁ bot hv

/-- **Lemma 2** of [DGMSV11]: with optimal resilience `S ≤ 3t + 1`, if every read completes in
three rounds then no write implementation completes in (at most)
`min {R, ⌊log₂ ⌈(3t+1)/2⌉⌋}` rounds; i.e. writes need `Ω(log t)` rounds. -/
theorem lemma2 (t : ℕ) (hS : Fintype.card Obj ≤ 3 * t + 1) (P : Proto Obj Rd V Msg Rep)
    (hN : P.N = 3) (hK1 : 1 ≤ P.K)
    (hK : P.K ≤ min (Fintype.card Rd) (Nat.log 2 ((3 * t + 2) / 2)))
    (bot : V) (hV : ∃ v : V, v ≠ bot) : ¬ P.Atomic t bot := by
  have h1 : P.K ≤ Fintype.card Rd := le_trans hK (min_le_left _ _)
  have h2 : tseq P.K ≤ t := (tseq_le_iff _ _).2 (le_trans hK (min_le_right _ _))
  have h3 : 1 ≤ t / tseq P.K := (Nat.one_le_div_iff (tseq_pos hK1)).2 h2
  exact write_lb_general P.K t hK1 (by omega) h1 P rfl hN bot hV

/-- **Proposition 2** of [DGMSV11]: if `S ≤ 3t + ⌊t / t_k⌋` and every read completes in three
rounds, then no write implementation completes in (at most) `min {R, ⌊log₂ ⌈(3t_k+1)/2⌉⌋}` rounds.
The paper's proof multiplies the blocks of Lemma 1 by `c = t / t_k`, which needs `t_k ∣ t`; the
general case needs extra objects in three blocks (`exists_fits`). -/
theorem proposition2 (k t : ℕ) (hk : 1 ≤ k) (hS : Fintype.card Obj ≤ 3 * t + t / tseq k)
    (P : Proto Obj Rd V Msg Rep) (hN : P.N = 3) (hK1 : 1 ≤ P.K)
    (hK : P.K ≤ min (Fintype.card Rd) (Nat.log 2 ((3 * tseq k + 2) / 2)))
    (bot : V) (hV : ∃ v : V, v ≠ bot) : ¬ P.Atomic t bot := by
  rw [log_tseq] at hK
  have h1 : P.K ≤ Fintype.card Rd := le_trans hK (min_le_left _ _)
  have h2 : P.K ≤ k := le_trans hK (min_le_right _ _)
  have h3 : t / tseq k ≤ t / tseq P.K := Nat.div_le_div_left (tseq_mono h2) (tseq_pos hK1)
  exact write_lb_general P.K t hK1 (by omega) h1 P rfl hN bot hV

/-- The closed form `t_k = (2^{k+2} - (-1)^k - 3) / 6` (proof of Lemma 2). -/
theorem tseq_closed_form (k : ℕ) : (6 * tseq k : ℤ) = 2 ^ (k + 2) - (-1) ^ k - 3 := by
  have := tseq_closed k; linarith

end Podc.RobustAtomicStorage
