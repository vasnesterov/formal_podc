import Papers.PODC2010.KShotRadioBroadcast.Model


-- CSLib candidate: lines of the affine plane over ZMod p
/-!
# Lines of the affine plane `ℤ_p²` (Section 4 of the paper)

A label `i < p²` is mapped to the point `⟨i div p, i mod p⟩ ∈ ℤ_p²`. The line `L_{a,b}` with
direction `a ∈ {0, …, p}` and offset `b ∈ {0, …, p - 1}` is `{⟨x, y⟩ : x ≡ b}` if `a = p` and
`{⟨x, y⟩ : y ≡ a x + b}` otherwise.

We prove the two facts used in the analysis of algorithm *Oblivious k-Shot*:
* every point lies on exactly one line of each direction (`exists_onLine`, `onLine_unique`);
* two distinct points lie on common lines of at most one direction (`eq_of_onLine_two_dirs`).
-/

namespace Podc.KShotRadioBroadcast

/-- The `x`-coordinate `i div p` of label `i`, as an element of `ℤ_p`. -/
def px (p i : ℕ) : ZMod p := ((i / p : ℕ) : ZMod p)

/-- The `y`-coordinate `i mod p` of label `i`, as an element of `ℤ_p`. -/
def py (p i : ℕ) : ZMod p := ((i % p : ℕ) : ZMod p)

/-- Label `i` lies on the line `L_{a,b}`. -/
def OnLine (p a b i : ℕ) : Prop :=
  if a = p then px p i = (b : ZMod p) else py p i = (a : ZMod p) * px p i + (b : ZMod p)

instance (p a b i : ℕ) : Decidable (OnLine p a b i) := by
  unfold OnLine; infer_instance

/-- The offset of the line of direction `a` through label `i`. -/
def lineOffset (p a i : ℕ) : ℕ :=
  if a = p then (px p i).val else (py p i - (a : ZMod p) * px p i).val

theorem lineOffset_lt {p : ℕ} (hp : 0 < p) (a i : ℕ) : lineOffset p a i < p := by
  have : NeZero p := ⟨hp.ne'⟩
  unfold lineOffset; split_ifs <;> exact ZMod.val_lt _

/-- Every label lies on the line of direction `a` with offset `lineOffset p a i`. -/
theorem onLine_lineOffset {p : ℕ} (hp : 0 < p) (a i : ℕ) : OnLine p a (lineOffset p a i) i := by
  have : NeZero p := ⟨hp.ne'⟩
  unfold OnLine lineOffset
  split_ifs with h
  · simp
  · simp

/-- Each label lies on at most one line of each direction. -/
theorem onLine_unique {p a b b' i : ℕ} (hb : b < p) (hb' : b' < p) (h : OnLine p a b i)
    (h' : OnLine p a b' i) : b = b' := by
  have hc : (b : ZMod p) = (b' : ZMod p) := by
    unfold OnLine at h h'
    split_ifs at h h' with ha
    · exact h.symm.trans h'
    · exact add_left_cancel (h.symm.trans h')
  rw [ZMod.natCast_eq_natCast_iff'] at hc
  rwa [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at hc

/-- Every label lies on exactly one line of each direction. -/
theorem exists_onLine {p : ℕ} (hp : 0 < p) (a i : ℕ) : ∃! b, b < p ∧ OnLine p a b i :=
  ⟨lineOffset p a i, ⟨lineOffset_lt hp a i, onLine_lineOffset hp a i⟩,
    fun _ hb => onLine_unique hb.1 (lineOffset_lt hp a i) hb.2 (onLine_lineOffset hp a i)⟩

/-- Labels below `p²` are determined by their coordinates. -/
theorem eq_of_px_py {p i j : ℕ} (hi : i < p * p) (hj : j < p * p) (hx : px p i = px p j)
    (hy : py p i = py p j) : i = j := by
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp at hi
    · exact h
  unfold px at hx; unfold py at hy
  rw [ZMod.natCast_eq_natCast_iff'] at hx hy
  have hi' : i / p < p := Nat.div_lt_of_lt_mul hi
  have hj' : j / p < p := Nat.div_lt_of_lt_mul hj
  rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at hx
  rw [Nat.mod_mod, Nat.mod_mod] at hy
  rw [← Nat.div_add_mod i p, ← Nat.div_add_mod j p, hx, hy]

/-- Two distinct labels below `p²` lie on common lines of at most one direction: if `i` and `j`
lie on a common line of direction `a` and on a common line of direction `a'` (with `a, a' ≤ p`)
and `a ≠ a'`, then `i = j`. -/
theorem eq_of_onLine_two_dirs {p a a' b b' i j : ℕ} (hp : p.Prime) (ha : a ≤ p) (ha' : a' ≤ p)
    (haa : a ≠ a') (hi : i < p * p) (hj : j < p * p) (h1 : OnLine p a b i) (h2 : OnLine p a b j)
    (h3 : OnLine p a' b' i) (h4 : OnLine p a' b' j) : i = j := by
  have : Fact p.Prime := ⟨hp⟩
  -- the slopes of two non-vertical directions are distinct in `ℤ_p`
  have slope_ne : ∀ {c c' : ℕ}, c < p → c' < p → c ≠ c' → (c : ZMod p) ≠ (c' : ZMod p) := by
    intro c c' hc hc' hne heq
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at heq
    exact hne heq
  -- a vertical and a non-vertical direction, or two non-vertical ones: `px` agrees
  have key : ∀ {c c' e e' : ℕ}, c' < p → c ≠ c' → c ≤ p → OnLine p c e i → OnLine p c e j →
      OnLine p c' e' i → OnLine p c' e' j → i = j := by
    intro c c' e e' hc' hne hc g1 g2 g3 g4
    unfold OnLine at g1 g2 g3 g4
    rw [ite_eq_right (Nat.ne_of_lt hc')] at g3 g4
    have hx : px p i = px p j := by
      by_cases hcp : c = p
      · rw [ite_eq_left hcp] at g1 g2; rw [g1, g2]
      · rw [ite_eq_right hcp] at g1 g2
        have hcl : c < p := lt_of_le_of_ne hc hcp
        have h5 : ((c : ZMod p) - c') * (px p i - px p j) = 0 := by
          have e1 : py p i - py p j = (c : ZMod p) * (px p i - px p j) := by rw [g1, g2]; ring
          have e2 : py p i - py p j = (c' : ZMod p) * (px p i - px p j) := by rw [g3, g4]; ring
          linear_combination e1.symm.trans e2
        rcases mul_eq_zero.1 h5 with h | h
        · exact absurd (sub_eq_zero.1 h) (slope_ne hcl hc' hne)
        · exact sub_eq_zero.1 h
    have hy : py p i = py p j := by rw [g3, g4, hx]
    exact eq_of_px_py hi hj hx hy
  rcases Nat.lt_or_ge a' p with h | h
  · exact key h haa ha h1 h2 h3 h4
  · have ha'p : a' = p := le_antisymm ha' h
    have hap : a < p := lt_of_le_of_ne ha (by omega)
    exact key hap (Ne.symm haa) ha' h3 h4 h1 h2

end Podc.KShotRadioBroadcast
