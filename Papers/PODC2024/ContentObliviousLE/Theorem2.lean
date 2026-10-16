import Papers.PODC2024.ContentObliviousLE.Alg3

/-!
# Theorem 2 and Proposition 14: leader election and orientation on non-oriented rings

Frei, Gelles, Ghazy, Nolin, *Content-Oblivious Leader Election on Rings*, arXiv 2405.03646,
Section 4. Algorithm 3 with virtual IDs `ID + i` (Theorem 2) and `2·ID − 1 + i` (Proposition 14).

Model: ring `ZMod n` (`n ≥ 1`) with arbitrary port assignment `flip`, distinct positive IDs,
adversarial asynchronous scheduler. "Quiescently stabilizing" = every execution is finite and
every final configuration is quiescent with correct outputs (nodes do not terminate explicitly).
-/

namespace Podc.ContentOblivious.Alg3

open Podc.ContentOblivious Finset

variable {n : ℕ} [NeZero n] {flip : ZMod n → Bool} {id : ZMod n → ℕ} {ℓ : ZMod n}

/-- Generic output analysis: with `M (!flip ℓ) = M (flip ℓ) + 1`, the counters at quiescence are
`ρ_0 = M (!flip v)` and `ρ_1 = M (flip v)`. -/
lemma final_r {vid : ℕ → Bool → ℕ} {M : Bool → ℕ} (hpos : ∀ v p, 0 < vid (id v) p)
    (hB : Bounds flip vid id M) (hM : ∀ d, ∃ v p, xor p (flip v) = d ∧ vid (id v) p = M d)
    {c : Config (ZMod n) S} (hr : Reach (flipped n flip) (alg vid) id c)
    (hfin : Final (flipped n flip) (alg vid) c) (v : ZMod n) :
    (c.st v).id = id v ∧ (c.st v).r false = M (!flip v) ∧ (c.st v).r true = M (flip v) := by
  have h := reach_inv hpos hB hr v
  have hc := (final_counts hpos hB hM hr hfin).2 v
  refine ⟨h.1, ?_, ?_⟩
  · have := (hc true).1; simp only [Bool.not_true, Bool.true_xor] at this; rw [h.2.1, this]
  · have := (hc false).1; simp only [Bool.not_false, Bool.false_xor] at this; rw [h.2.1, this]

/-- Virtual IDs of Theorem 2: `ID^(i) = ID + i`. -/
def vid2 (i : ℕ) (b : Bool) : ℕ := i + if b then 1 else 0

/-- Maximal virtual ID per direction for Theorem 2 (`true` = towards `v + 1`). -/
def M2 (id : ZMod n → ℕ) (flip : ZMod n → Bool) (ℓ : ZMod n) (d : Bool) : ℕ :=
  id ℓ + if d = !flip ℓ then 1 else 0

variable (hid : Function.Injective id) (hpos : ∀ v, 0 < id v) (hℓ : ∀ v, id v ≤ id ℓ)
include hid hpos hℓ

lemma lt_of_ne {v : ZMod n} (hv : v ≠ ℓ) : id v < id ℓ :=
  lt_of_le_of_ne (hℓ v) fun h => hv (hid h)

lemma bounds2 : Bounds flip vid2 id (M2 id flip ℓ) := by
  intro v p
  by_cases hv : v = ℓ
  · subst hv; cases p <;> cases hfv : flip v <;> simp [vid2, M2, hfv]
  · have := lt_of_ne hid hpos hℓ hv
    simp only [vid2, M2]; split_ifs <;> omega

lemma attained2 : ∀ d, ∃ v p, xor p (flip v) = d ∧ vid2 (id v) p = M2 id flip ℓ d := by
  intro d
  refine ⟨ℓ, xor d (flip ℓ), by simp, ?_⟩
  cases d <;> cases hfl : flip ℓ <;> simp [vid2, M2, hfl]

/-- **Theorem 2.** Algorithm 3 with virtual IDs `ID + i` is a quiescently stabilizing
content-oblivious algorithm on non-oriented rings with unique IDs: every execution is finite and
sends at most `n(2·IDmax + 1)` pulses; in every final configuration the network is quiescent,
exactly `n(2·IDmax + 1)` pulses were sent, exactly the node `ℓ` of maximal ID outputs `Leader`, and
the ports named clockwise all point in the same direction around the ring (that of `ℓ`'s `Port1`). -/
theorem theorem_2 :
    (¬ ∃ f : ℕ → Config (ZMod n) S, f 0 = initCfg (alg vid2) id ∧
        ∀ k, Step (flipped n flip) (alg vid2) (f k) (f (k + 1))) ∧
    (∀ c, Reach (flipped n flip) (alg vid2) id c → totalSent c ≤ n * (2 * id ℓ + 1)) ∧
    (∀ c, Reach (flipped n flip) (alg vid2) id c → Final (flipped n flip) (alg vid2) c →
      Quiescent (flipped n flip) (alg vid2) c ∧ totalSent c = n * (2 * id ℓ + 1) ∧
      (∀ v, (alg vid2).leader (c.st v) = true ↔ v = ℓ) ∧
      cwPort (c.st ℓ) = true ∧ ∀ v, xor (cwPort (c.st v)) (flip v) = !flip ℓ) := by
  have hp : ∀ v p, 0 < vid2 (id v) p := fun v p => by simp [vid2, hpos v]
  have hB := bounds2 (flip := flip) hid hpos hℓ
  have hM := attained2 (flip := flip) hid hpos hℓ
  have hsum : M2 id flip ℓ true + M2 id flip ℓ false = 2 * id ℓ + 1 := by
    cases hfl : flip ℓ <;> simp [M2, hfl] <;> ring
  have hle : ∀ c, Reach (flipped n flip) (alg vid2) id c → totalSent c ≤ n * (2 * id ℓ + 1) :=
    fun c hr => hsum ▸ totalSent_le hp hB hr
  refine ⟨no_infinite_execution hle, hle, fun c hr hfin => ⟨(final_counts hp hB hM hr hfin).1,
    hsum ▸ totalSent_final hp hB hM hr hfin, fun v => ?_, ?_, fun v => ?_⟩⟩
  · obtain ⟨e1, e2, e3⟩ := final_r hp hB hM hr hfin v
    simp only [alg, e1, e2, e3, vid2, M2, decide_eq_true_eq]
    by_cases hv : v = ℓ
    · subst hv; cases hfv : flip v <;> simp [hfv]
    · have := lt_of_ne hid hpos hℓ hv
      simp only [hv, iff_false]
      cases hfv : flip v <;> cases hfl : flip ℓ <;> simp [hfv, hfl] <;> omega
  · obtain ⟨-, e2, e3⟩ := final_r hp hB hM hr hfin ℓ
    simp only [cwPort, e2, e3, M2]; cases hfl : flip ℓ <;> simp [hfl]
  · obtain ⟨-, e2, e3⟩ := final_r hp hB hM hr hfin v
    simp only [cwPort, e2, e3, M2]
    cases hfv : flip v <;> cases hfl : flip ℓ <;> simp [hfv, hfl]

/-- Virtual IDs of Proposition 14: `ID^(i) = 2·ID − 1 + i`. -/
def vid14 (i : ℕ) (b : Bool) : ℕ := 2 * i - 1 + if b then 1 else 0

/-- Maximal virtual ID per direction for Proposition 14. -/
def M14 (id : ZMod n → ℕ) (flip : ZMod n → Bool) (ℓ : ZMod n) (d : Bool) : ℕ :=
  2 * id ℓ - 1 + if d = !flip ℓ then 1 else 0

/-- **Proposition 14.** Algorithm 3 with virtual IDs `2·ID − 1 + i` elects the node of maximal ID
and consistently orients the ring with at most (and, at the end, exactly) `n(4·IDmax − 1)` pulses;
it reaches quiescence (every execution is finite) but does not terminate. -/
theorem proposition_14 :
    (¬ ∃ f : ℕ → Config (ZMod n) S, f 0 = initCfg (alg vid14) id ∧
        ∀ k, Step (flipped n flip) (alg vid14) (f k) (f (k + 1))) ∧
    (∀ c, Reach (flipped n flip) (alg vid14) id c → totalSent c ≤ n * (4 * id ℓ - 1)) ∧
    (∀ c, Reach (flipped n flip) (alg vid14) id c → Final (flipped n flip) (alg vid14) c →
      Quiescent (flipped n flip) (alg vid14) c ∧ totalSent c = n * (4 * id ℓ - 1) ∧
      (∀ v, (alg vid14).leader (c.st v) = true ↔ v = ℓ) ∧
      cwPort (c.st ℓ) = true ∧ ∀ v, xor (cwPort (c.st v)) (flip v) = !flip ℓ) := by
  have hl := hpos ℓ
  have hp : ∀ v p, 0 < vid14 (id v) p := fun v p => by
    have := hpos v; simp only [vid14]; split_ifs <;> omega
  have hB : Bounds flip vid14 id (M14 id flip ℓ) := by
    intro v p
    by_cases hv : v = ℓ
    · subst hv; cases p <;> cases hfv : flip v <;> simp [vid14, M14, hfv] <;> omega
    · have := lt_of_ne hid hpos hℓ hv
      simp only [vid14, M14]; split_ifs <;> omega
  have hM : ∀ d, ∃ v p, xor p (flip v) = d ∧ vid14 (id v) p = M14 id flip ℓ d := by
    intro d
    refine ⟨ℓ, xor d (flip ℓ), by simp, ?_⟩
    cases d <;> cases hfl : flip ℓ <;> simp [vid14, M14, hfl]
  have hsum : M14 id flip ℓ true + M14 id flip ℓ false = 4 * id ℓ - 1 := by
    cases hfl : flip ℓ <;> simp [M14, hfl] <;> omega
  have hle : ∀ c, Reach (flipped n flip) (alg vid14) id c → totalSent c ≤ n * (4 * id ℓ - 1) :=
    fun c hr => hsum ▸ totalSent_le hp hB hr
  refine ⟨no_infinite_execution hle, hle, fun c hr hfin => ⟨(final_counts hp hB hM hr hfin).1,
    hsum ▸ totalSent_final hp hB hM hr hfin, fun v => ?_, ?_, fun v => ?_⟩⟩
  · obtain ⟨e1, e2, e3⟩ := final_r hp hB hM hr hfin v
    simp only [alg, e1, e2, e3, vid14, M14, decide_eq_true_eq]
    have := hpos v
    by_cases hv : v = ℓ
    · subst hv; cases hfv : flip v <;> simp [hfv] <;> omega
    · have := lt_of_ne hid hpos hℓ hv
      simp only [hv, iff_false]
      cases hfv : flip v <;> cases hfl : flip ℓ <;> simp [hfv, hfl] <;> omega
  · obtain ⟨-, e2, e3⟩ := final_r hp hB hM hr hfin ℓ
    simp only [cwPort, e2, e3, M14]; cases hfl : flip ℓ <;> simp [hfl] <;> omega
  · obtain ⟨-, e2, e3⟩ := final_r hp hB hM hr hfin v
    simp only [cwPort, e2, e3, M14]
    cases hfv : flip v <;> cases hfl : flip ℓ <;> simp [hfv, hfl] <;> omega

end Podc.ContentOblivious.Alg3
