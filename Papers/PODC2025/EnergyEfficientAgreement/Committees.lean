import Mathlib
import Cslib.Foundations.Data.Nat.ModCount

/-!
# Static committees (`JoinCommittees`)

Procedure `JoinCommittees(a, b)` of the full version of Mirault–Robinson (Algorithm 1 of
arXiv:2506.12282v1; the brief announcement only states its properties): the slots
`i = 1, …, a·b` are dealt round-robin to the players `p_{i mod n}`, and slot `i` belongs to committee
`C_⌈i/b⌉`. So `C_d` consists of the players of the `b` consecutive slots `(d-1)b+1, …, db`.

* `card_joinCommittees`: each committee has exactly `b` members if `b ≤ n`;
* `card_filter_mem_joinCommittees_le`: each player is in at most `⌈a·b/n⌉` committees (the
  property the brief announcement requires of `JoinCommittees`).
-/

namespace Podc.EnergyEfficientAgreement

open Finset

/-- `JoinCommittees(a, b)` on the players `Fin n`: committee `C_d` (`1 ≤ d ≤ a`) consists of the
players `i mod n` for the slots `i ∈ ((d-1)b, db]`; `C_d = ∅` for other `d`. -/
def joinCommittees (n a b : ℕ) [NeZero n] (d : ℕ) : Finset (Fin n) :=
  if 1 ≤ d ∧ d ≤ a then (Ioc ((d - 1) * b) (d * b)).image (fun i : ℕ => Fin.ofNat n i) else ∅

variable {n a b : ℕ} [NeZero n]

lemma mem_joinCommittees {d : ℕ} {p : Fin n} :
    p ∈ joinCommittees n a b d ↔
      1 ≤ d ∧ d ≤ a ∧ ∃ i : ℕ, (d - 1) * b < i ∧ i ≤ d * b ∧ Fin.ofNat n i = p := by
  unfold joinCommittees
  split_ifs with h
  · simp [h, and_assoc]
  · simp only [notMem_empty, false_iff]
    rintro ⟨h1, h2, -⟩
    exact h ⟨h1, h2⟩

/-- Committees have exactly `b` members when `b ≤ n`. -/
theorem card_joinCommittees (hb : b ≤ n) {d : ℕ} (hd : 1 ≤ d) (hda : d ≤ a) :
    (joinCommittees n a b d).card = b := by
  unfold joinCommittees
  split_ifs with hc
  swap
  · exact absurd ⟨hd, hda⟩ hc
  rw [card_image_of_injOn]
  · have : d * b = (d - 1) * b + b := by
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      simp [add_mul]
    rw [Nat.card_Ioc, this]; omega
  · intro i hi j hj hij
    simp only [coe_Ioc, Set.mem_Ioc] at hi hj
    have h : i % n = j % n := by simpa [Fin.ext_iff] using hij
    have hd' : d * b = (d - 1) * b + b := by
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      simp [add_mul]
    -- `i ≡ j [MOD n]` and `|i - j| < b ≤ n`
    rcases le_total i j with hij' | hij'
    · have h1 : n ∣ j - i := (Nat.modEq_iff_dvd' hij').1 h
      have := Nat.eq_zero_of_dvd_of_lt h1 (by omega)
      omega
    · have h1 : n ∣ i - j := (Nat.modEq_iff_dvd' hij').1 h.symm
      have := Nat.eq_zero_of_dvd_of_lt h1 (by omega)
      omega

/-- Every player is a member of at most `⌈a·b/n⌉` of the committees `C_1, …, C_a`. -/
theorem card_filter_mem_joinCommittees_le (hb : 0 < b) (p : Fin n) :
    ((Icc 1 a).filter (fun d => p ∈ joinCommittees n a b d)).card ≤ (a * b) ⌈/⌉ n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  calc _ ≤ (((Ico 1 (a * b + 1)).filter (fun i => i ≡ p.val [MOD n])).image
          (fun i => (i + b - 1) / b)).card := by
        refine card_le_card fun d hd => ?_
        simp only [mem_filter, mem_Icc] at hd
        obtain ⟨-, -, i, hi1, hi2, hip⟩ := mem_joinCommittees.1 hd.2
        simp only [mem_image, mem_filter, mem_Ico]
        refine ⟨i, ⟨⟨by nlinarith [Nat.zero_le ((d - 1) * b)], ?_⟩, ?_⟩, ?_⟩
        · have : d * b ≤ a * b := Nat.mul_le_mul_right b hd.1.2
          omega
        · have : i % n = p.val := by simpa [Fin.ext_iff] using hip
          rw [Nat.ModEq, this, Nat.mod_eq_of_lt p.2]
        · have hd' : d * b = (d - 1) * b + b := by
            obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
            simp [add_mul]
          obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at hi1 hd' ⊢
          refine Nat.div_eq_of_lt_le ?_ ?_
          · rw [hd'] ; omega
          · have : (k + 1 + 1) * b = (k + 1) * b + b := by ring
            rw [this]; omega
    _ ≤ ((Ico 1 (a * b + 1)).filter (fun i => i ≡ p.val [MOD n])).card := card_image_le
    _ ≤ (a * b + 1 - 1) ⌈/⌉ n := Nat.card_Ico_filter_modEq_le hn _ _ _
    _ = (a * b) ⌈/⌉ n := by simp

end Podc.EnergyEfficientAgreement
