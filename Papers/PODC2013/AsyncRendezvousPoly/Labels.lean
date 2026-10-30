import Papers.PODC2013.AsyncRendezvousPoly.Algorithm

/-!
# Modified labels

`M(x) = (c₁c₁ … c_r c_r 0 1)`: "for any `x` and `y`, the sequence `M(x)` is never a prefix of
`M(y)`; also `M(x) ≠ M(y)` for `x ≠ y`" (§3.1). We prove the form used in the proof of
Theorem 3.1: two distinct positive labels have modified labels that differ at some (0-indexed)
position `d` with `1 ≤ d < min(|M(L₁)|, |M(L₂)|)` (the paper's `1 < λ ≤ l`).
-/

namespace Podc.AsyncRendezvousPoly

theorem getD_double (l t : List Bool) (i : ℕ) (hi : i < l.length) (e : ℕ) (he : e < 2) :
    ((l.flatMap fun c => [c, c]) ++ t).getD (2 * i + e) false = l.getD i false := by
  induction l generalizing i with
  | nil => simp at hi
  | cons c l ih =>
    rcases i with _ | i
    · interval_cases e <;> simp
    · simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getD_cons_succ]
      rw [show 2 * (i + 1) + e = (2 * i + e) + 1 + 1 by ring]
      simp only [List.getD_cons_succ]
      exact ih i (by simpa using hi)

theorem getD_double_end (l t : List Bool) (j : ℕ) :
    ((l.flatMap fun c => [c, c]) ++ t).getD (2 * l.length + j) false = t.getD j false := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons]
    rw [show 2 * (l.length + 1) + j = (2 * l.length + j) + 1 + 1 by ring]
    simpa using ih

theorem binDigits_length (L : ℕ) : (binDigits L).length = binLen L := by
  simp [binDigits, binLen]

theorem modLabel_length (L : ℕ) : (modLabel L).length = 2 * binLen L + 2 := by
  simp [modLabel, binDigits_length, List.length_flatMap]; ring

theorem modLabel_ne_nil (L : ℕ) : modLabel L ≠ [] := by
  intro h; have := modLabel_length L; rw [h] at this; simp at this

theorem bit_modLabel (L i : ℕ) (hi : i < binLen L) (e : ℕ) (he : e < 2) :
    bit (modLabel L) (2 * i + e) = (binDigits L).getD i false := by
  unfold bit modLabel; exact getD_double _ _ i (by rwa [binDigits_length]) e he

theorem bit_modLabel_end (L j : ℕ) :
    bit (modLabel L) (2 * binLen L + j) = [false, true].getD j false := by
  unfold bit modLabel; rw [← binDigits_length]; exact getD_double_end _ _ j

theorem binDigits_injective : Function.Injective binDigits := by
  intro L1 L2 h
  have key : ∀ L, (((Nat.digits 2 L).map (fun d => decide (d = 1))).map
      (fun b : Bool => if b then 1 else 0)) = Nat.digits 2 L := by
    intro L
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (Nat.digits 2 L)]
    apply List.map_congr_left
    intro d hd
    have := Nat.digits_lt_base (by norm_num) hd
    interval_cases d <;> simp
  have h' : (Nat.digits 2 L1).map (fun d => decide (d = 1)) =
      (Nat.digits 2 L2).map (fun d => decide (d = 1)) := List.reverse_injective h
  have := congrArg (List.map (fun b : Bool => if b then 1 else 0)) h'
  rw [key, key] at this
  exact Nat.digits.injective 2 this

theorem binLen_pos {L : ℕ} (hL : 0 < L) : 1 ≤ binLen L := by
  unfold binLen
  rw [Nat.digits_def' (by norm_num) hL]; simp

/-- Modified labels of distinct positive labels differ at some position `1 ≤ d < l`. -/
theorem exists_bit_ne {L1 L2 : ℕ} (h1 : 0 < L1) (h2 : 0 < L2) (hne : L1 ≠ L2) :
    ∃ d, 1 ≤ d ∧ d < min (modLabel L1).length (modLabel L2).length ∧
      bit (modLabel L1) d ≠ bit (modLabel L2) d := by
  rw [modLabel_length, modLabel_length]
  have hb1 := binLen_pos h1
  have hb2 := binLen_pos h2
  -- the case of shorter first label
  have shorter : ∀ L L', 0 < L → binLen L < binLen L' →
      ∃ d, 1 ≤ d ∧ d < 2 * binLen L + 2 ∧ bit (modLabel L) d ≠ bit (modLabel L') d := by
    intro L L' hL hlt
    have hb := binLen_pos hL
    have e0 := bit_modLabel_end L 0
    have e1 := bit_modLabel_end L 1
    have f0 := bit_modLabel L' (binLen L) hlt 0 (by norm_num)
    have f1 := bit_modLabel L' (binLen L) hlt 1 (by norm_num)
    simp only [add_zero, List.getD_cons_zero, List.getD_cons_succ] at e0 e1 f0
    cases hc : (binDigits L').getD (binLen L) false
    · refine ⟨2 * binLen L + 1, by omega, by omega, ?_⟩
      rw [e1, f1, hc]; simp
    · refine ⟨2 * binLen L, by omega, by omega, ?_⟩
      rw [e0, f0, hc]; simp
  rcases lt_trichotomy (binLen L1) (binLen L2) with h | h | h
  · obtain ⟨d, hd1, hd2, hd⟩ := shorter L1 L2 h1 h
    exact ⟨d, hd1, by omega, hd⟩
  · have hne' : binDigits L1 ≠ binDigits L2 := fun h' => hne (binDigits_injective h')
    have hlen : (binDigits L1).length = (binDigits L2).length := by
      rw [binDigits_length, binDigits_length, h]
    obtain ⟨i, hi, hdiff⟩ : ∃ i, i < binLen L1 ∧
        (binDigits L1).getD i false ≠ (binDigits L2).getD i false := by
      by_contra hcon
      push Not at hcon
      apply hne'
      apply List.ext_getElem hlen
      intro i hi1 hi2
      have := hcon i (by rwa [binDigits_length] at hi1)
      rwa [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2] at this
    refine ⟨2 * i + 1, by omega, by omega, ?_⟩
    rw [bit_modLabel L1 i hi 1 (by norm_num), bit_modLabel L2 i (by omega) 1 (by norm_num)]
    exact hdiff
  · obtain ⟨d, hd1, hd2, hd⟩ := shorter L2 L1 h2 h
    exact ⟨d, hd1, by omega, fun h' => hd h'.symm⟩

end Podc.AsyncRendezvousPoly
