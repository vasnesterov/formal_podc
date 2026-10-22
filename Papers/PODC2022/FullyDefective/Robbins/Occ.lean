import Papers.PODC2022.FullyDefective.Robbins

/-!
# Occurrences of a node on a Robbins cycle

Combinatorics of the positions `ZMod L` of a Robbins cycle `C` used by Algorithm 3 of [CCGS22]
(`Robbins/Model.lean`). A node `u` occurs at the positions `j` with `C j = u` (its *occurrences*);
`k_u = occ u` is their number.

* `firstOcc u a` — the first occurrence of `u` at or after position `a` (clockwise);
* `lastOcc u a` — the first occurrence of `u` at or before position `a` (counterclockwise);
* `nextOcc p`, `prevOcc p` — the next / previous occurrence of the node `C p` after / before `p`;
* `mult x y` — the number of times the cycle traverses the edge `x → y` (the multiplicity of the
  physical channel `x → y` as a link of `C`);
* `cntF u a n` — the number of occurrences of `u` among the positions `a + 1, …, a + n`;
* `dist a p` — the clockwise distance from `a` to `p`.

The orientation property of a Robbins cycle gives `mult_eq_zero_of_pos`: a physical channel is used
by the cycle in at most one direction.
-/

set_option linter.unusedSectionVars false

namespace Podc.FullyDefective.RobbinsSim

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} (R : RobbinsCycle G)

/-- Clockwise distance from `a` to `p`. -/
def dist {L : ℕ} (a p : ZMod L) : ℕ := (p - a).val

lemma exists_fwd (u : V) (a : ZMod R.L) : ∃ n : ℕ, R.C (a + n) = u := by
  obtain ⟨j, hj⟩ := R.surj u
  exact ⟨(j - a).val, by simp [hj]⟩

lemma exists_bwd (u : V) (a : ZMod R.L) : ∃ n : ℕ, R.C (a - n) = u := by
  obtain ⟨j, hj⟩ := R.surj u
  exact ⟨(a - j).val, by simp [hj]⟩

/-- The first occurrence of `u` at or after `a` (clockwise). -/
def firstOcc (u : V) (a : ZMod R.L) : ZMod R.L := a + Nat.find (exists_fwd R u a)

/-- The first occurrence of `u` at or before `a` (counterclockwise). -/
def lastOcc (u : V) (a : ZMod R.L) : ZMod R.L := a - Nat.find (exists_bwd R u a)

/-- The next occurrence (clockwise, strictly after `p`) of the node at position `p`. -/
def nextOcc (p : ZMod R.L) : ZMod R.L := firstOcc R (R.C p) (p + 1)

/-- The previous occurrence (counterclockwise, strictly before `p`) of the node at position `p`. -/
def prevOcc (p : ZMod R.L) : ZMod R.L := lastOcc R (R.C p) (p - 1)

/-- The number of links `j → j + 1` of the cycle with `C j = x` and `C (j + 1) = y`. -/
def mult (x y : V) : ℕ := (Finset.univ.filter fun j : ZMod R.L => R.C j = x ∧ R.C (j + 1) = y).card

/-- The number `k_u` of occurrences of `u` on the cycle. -/
def occ (u : V) : ℕ := (Finset.univ.filter fun j : ZMod R.L => R.C j = u).card

/-- The number of occurrences of `u` among the positions `a + 1, …, a + n`. -/
def cntF (u : V) (a : ZMod R.L) (n : ℕ) : ℕ := Nat.count (fun i => R.C (a + i + 1) = u) n

variable {R}

/-! ### Distances -/

lemma dist_lt {L : ℕ} [NeZero L] (a p : ZMod L) : dist a p < L := ZMod.val_lt _

lemma dist_add_natCast {L : ℕ} (a : ZMod L) {n : ℕ} (h : n < L) : dist a (a + n) = n := by
  simp [dist, ZMod.val_natCast_of_lt h]

lemma dist_inj {L : ℕ} [NeZero L] {a p q : ZMod L} (h : dist a p = dist a q) : p = q := by
  have := ZMod.val_injective L h; simpa using this

lemma dist_self {L : ℕ} (a : ZMod L) : dist a a = 0 := by simp [dist]

lemma dist_eq_zero {L : ℕ} [NeZero L] {a p : ZMod L} : dist a p = 0 ↔ p = a := by
  simp [dist, ZMod.val_eq_zero, sub_eq_zero]

lemma eq_add_dist {L : ℕ} [NeZero L] (a p : ZMod L) : p = a + (dist a p : ℕ) := by
  simp [dist]

lemma dist_sub_one {L : ℕ} [NeZero L] {a p : ZMod L} (h : p ≠ a) : dist a (p - 1) = dist a p - 1 := by
  have h0 : dist a p ≠ 0 := fun h' => h (dist_eq_zero.1 h')
  have hl := dist_lt a p
  have e : p - 1 = a + ((dist a p - 1 : ℕ) : ZMod L) := by
    conv_lhs => rw [eq_add_dist a p]
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e, dist_add_natCast _ (by omega)]

/-- Forward and backward distances: `dist a p + dist p (a - 1) = L - 1`. -/
lemma dist_add_dist_pred {L : ℕ} [NeZero L] (a p : ZMod L) : dist a p + dist p (a - 1) = L - 1 := by
  have h1 := dist_lt a p
  have h2 := dist_lt p (a - 1)
  have hL : 0 < L := Nat.pos_of_neZero L
  have e : ((dist a p + dist p (a - 1) : ℕ) : ZMod L) = ((L - 1 : ℕ) : ZMod L) := by
    rw [Nat.cast_sub hL]; simp [dist]
  rw [ZMod.natCast_eq_natCast_iff'] at e
  rw [Nat.mod_eq_of_lt (show L - 1 < L by omega)] at e
  by_cases h : dist a p + dist p (a - 1) < L
  · rwa [Nat.mod_eq_of_lt h] at e
  · have : (dist a p + dist p (a - 1)) % L = dist a p + dist p (a - 1) - L := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-! ### First and last occurrences -/

lemma C_firstOcc (u : V) (a : ZMod R.L) : R.C (firstOcc R u a) = u :=
  Nat.find_spec (exists_fwd R u a)

lemma C_lastOcc (u : V) (a : ZMod R.L) : R.C (lastOcc R u a) = u :=
  Nat.find_spec (exists_bwd R u a)

lemma firstOcc_eq {u : V} {a : ZMod R.L} {n : ℕ} (hn : ∀ i < n, R.C (a + i) ≠ u)
    (h : R.C (a + n) = u) : firstOcc R u a = a + n := by
  have : Nat.find (exists_fwd R u a) = n := (Nat.find_eq_iff _).2 ⟨h, fun i hi => hn i hi⟩
  rw [firstOcc, this]

lemma lastOcc_eq {u : V} {a : ZMod R.L} {n : ℕ} (hn : ∀ i < n, R.C (a - i) ≠ u)
    (h : R.C (a - n) = u) : lastOcc R u a = a - n := by
  have : Nat.find (exists_bwd R u a) = n := (Nat.find_eq_iff _).2 ⟨h, fun i hi => hn i hi⟩
  rw [lastOcc, this]

lemma firstOcc_self {u : V} {a : ZMod R.L} (h : R.C a = u) : firstOcc R u a = a := by
  simpa using firstOcc_eq (n := 0) (by simp) (by simpa using h)

lemma lastOcc_self {u : V} {a : ZMod R.L} (h : R.C a = u) : lastOcc R u a = a := by
  simpa using lastOcc_eq (n := 0) (by simp) (by simpa using h)

lemma firstOcc_of_ne {u : V} {a : ZMod R.L} (h : R.C a ≠ u) :
    firstOcc R u a = firstOcc R u (a + 1) := by
  set N := Nat.find (exists_fwd R u (a + 1)) with hN
  have hs : R.C (a + 1 + N) = u := Nat.find_spec (exists_fwd R u (a + 1))
  have hm : ∀ i < N, R.C (a + 1 + i) ≠ u := fun i hi => Nat.find_min (exists_fwd R u (a + 1)) hi
  have e1 : firstOcc R u (a + 1) = a + 1 + N := rfl
  rw [e1, firstOcc_eq (n := N + 1) (fun i hi => ?_) (by push_cast; rwa [add_comm (N : ZMod R.L), ← add_assoc])]
  · push_cast; ring
  · rcases i with _ | i
    · simpa using h
    · have := hm i (by omega); push_cast
      rwa [add_comm (i : ZMod R.L), ← add_assoc]

lemma lastOcc_of_ne {u : V} {a : ZMod R.L} (h : R.C a ≠ u) :
    lastOcc R u a = lastOcc R u (a - 1) := by
  set N := Nat.find (exists_bwd R u (a - 1)) with hN
  have hs : R.C (a - 1 - N) = u := Nat.find_spec (exists_bwd R u (a - 1))
  have hm : ∀ i < N, R.C (a - 1 - i) ≠ u := fun i hi => Nat.find_min (exists_bwd R u (a - 1)) hi
  have e1 : lastOcc R u (a - 1) = a - 1 - N := rfl
  rw [e1, lastOcc_eq (n := N + 1) (fun i hi => ?_) (by push_cast; rwa [sub_add_eq_sub_sub,
    sub_right_comm])]
  · push_cast; ring
  · rcases i with _ | i
    · simpa using h
    · have := hm i (by omega); push_cast; rwa [sub_add_eq_sub_sub, sub_right_comm]

/-- The first occurrence at or after `a` is the closest occurrence clockwise. -/
lemma dist_firstOcc_le {u : V} (a : ZMod R.L) {p : ZMod R.L} (h : R.C p = u) :
    dist a (firstOcc R u a) ≤ dist a p := by
  have hle : Nat.find (exists_fwd R u a) ≤ dist a p :=
    Nat.find_min' _ (by rw [← eq_add_dist]; exact h)
  rw [firstOcc, dist_add_natCast _ (lt_of_le_of_lt hle (dist_lt a p))]; exact hle

/-- The first occurrence at or before `a` is the closest occurrence counterclockwise. -/
lemma dist_lastOcc_le {u : V} (a : ZMod R.L) {p : ZMod R.L} (h : R.C p = u) :
    dist (lastOcc R u a) a ≤ dist p a := by
  have e : ∀ q : ZMod R.L, q = a - (dist q a : ℕ) := fun q => by simp [dist]
  have hle : Nat.find (exists_bwd R u a) ≤ dist p a :=
    Nat.find_min' _ (by rw [← e]; exact h)
  have hlt := lt_of_le_of_lt hle (dist_lt p a)
  rw [lastOcc]; simp only [dist, sub_sub_cancel, ZMod.val_natCast_of_lt hlt]; exact hle

/-- `lastOcc u (a - 1)` is the occurrence of `u` farthest clockwise from `a` (for occurrences other
than `a` itself). -/
lemma dist_le_lastOcc {u : V} (a : ZMod R.L) {p : ZMod R.L} (h : R.C p = u) :
    dist a p ≤ dist a (lastOcc R u (a - 1)) := by
  have h1 := dist_lastOcc_le (a - 1) h
  have h2 := dist_add_dist_pred a p
  have h3 := dist_add_dist_pred a (lastOcc R u (a - 1))
  omega

lemma firstOcc_add_cntF {u : V} {a : ZMod R.L} {n : ℕ} (h : cntF R u a n = 0) :
    firstOcc R u (a + 1) = firstOcc R u (a + n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cntF, Nat.count_succ] at h
    have h1 : cntF R u a n = 0 := by rw [cntF]; omega
    have h2 : R.C (a + n + 1) ≠ u := by intro h'; simp [h'] at h
    rw [ih h1, firstOcc_of_ne h2]; push_cast; ring_nf

lemma lastOcc_add_sub_one {u : V} {a : ZMod R.L} :
    ∀ n : ℕ, (∀ i < n, R.C (a + i) ≠ u) → lastOcc R u (a + n - 1) = lastOcc R u (a - 1)
  | 0, _ => by simp
  | n + 1, hm => by
    rw [← lastOcc_add_sub_one n (fun i hi => hm i (by omega)), Nat.cast_succ, ← add_assoc,
      add_sub_cancel_right, lastOcc_of_ne (hm n (by omega))]

/-- The previous occurrence of the first occurrence after `a` is the last occurrence before `a`. -/
lemma lastOcc_firstOcc_sub_one (u : V) (a : ZMod R.L) :
    lastOcc R u (firstOcc R u a - 1) = lastOcc R u (a - 1) :=
  lastOcc_add_sub_one _ fun i hi => Nat.find_min (exists_fwd R u a) hi

lemma nextOcc_eq (p : ZMod R.L) : nextOcc R p = firstOcc R (R.C p) (p + 1) := rfl
lemma prevOcc_eq (p : ZMod R.L) : prevOcc R p = lastOcc R (R.C p) (p - 1) := rfl

/-! ### Counting -/

lemma cntF_succ (u : V) (a : ZMod R.L) (n : ℕ) :
    cntF R u a (n + 1) = cntF R u a n + if R.C (a + n + 1) = u then 1 else 0 := by
  simp [cntF, Nat.count_succ]

lemma cntF_L (u : V) (a : ZMod R.L) : cntF R u a R.L = occ R u := by
  rw [cntF, Nat.count_eq_card_filter_range, occ]
  refine Finset.card_bij' (fun i _ => a + i + 1) (fun j _ => (j - a - 1).val) ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.2
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hj ⊢
    refine ⟨ZMod.val_lt _, ?_⟩
    rw [ZMod.natCast_zmod_val, show a + (j - a - 1) + 1 = j by ring]; exact hj
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    rw [show a + (i : ZMod R.L) + 1 - a - 1 = (i : ZMod R.L) by ring, ZMod.val_natCast_of_lt hi.1]
  · intro j _; rw [ZMod.natCast_zmod_val]; ring

lemma cntF_add_mul (u : V) (a : ZMod R.L) (n t : ℕ) :
    cntF R u a (n + t * R.L) = cntF R u a n + t * occ R u := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show n + (t + 1) * R.L = (n + t * R.L) + R.L by ring, cntF, Nat.count_add, ← cntF, ih]
    have h2 : Nat.count (fun k => R.C (a + ((n + t * R.L + k : ℕ) : ZMod R.L) + 1) = u) R.L =
        occ R u := by
      rw [← cntF_L u (a + (n : ZMod R.L)), cntF]
      congr 1; funext k; push_cast; simp only [CharP.cast_eq_zero, mul_zero, add_zero]; ring_nf
    rw [h2]; ring

lemma cntF_mul (u : V) (a : ZMod R.L) (t : ℕ) : cntF R u a (t * R.L) = t * occ R u := by
  simpa [cntF] using cntF_add_mul u a 0 t

lemma occ_pos (u : V) : 0 < occ R u := by
  obtain ⟨j, hj⟩ := R.surj u
  exact Finset.card_pos.2 ⟨j, by simp [hj]⟩

/-! ### Links and orientation -/

lemma mult_pos {x y : V} : 0 < mult R x y ↔ ∃ j, R.C j = x ∧ R.C (j + 1) = y := by
  simp [mult, Finset.card_pos, Finset.Nonempty]

lemma mult_pos_of (j : ZMod R.L) : 0 < mult R (R.C j) (R.C (j + 1)) := mult_pos.2 ⟨j, rfl, rfl⟩

lemma mult_pos_of' (j : ZMod R.L) : 0 < mult R (R.C (j - 1)) (R.C j) :=
  mult_pos.2 ⟨j - 1, rfl, by simp⟩

/-- A Robbins cycle never traverses an edge in both directions. -/
lemma mult_eq_zero_of_pos {x y : V} (h : 0 < mult R x y) : mult R y x = 0 := by
  obtain ⟨i, hi1, hi2⟩ := mult_pos.1 h
  by_contra h'
  obtain ⟨j, hj1, hj2⟩ := mult_pos.1 (Nat.pos_of_ne_zero h')
  exact R.oriented j i (hj1.trans hi2.symm) (hj2.trans hi1.symm)

lemma C_ne_succ (j : ZMod R.L) : R.C j ≠ R.C (j + 1) := (R.adj j).ne

lemma C_ne_pred (j : ZMod R.L) : R.C j ≠ R.C (j - 1) := by
  have := (R.adj (j - 1)).ne; simp at this; exact Ne.symm this

lemma mult_self (x : V) : mult R x x = 0 := by
  by_contra h
  obtain ⟨j, h1, h2⟩ := mult_pos.1 (Nat.pos_of_ne_zero h)
  exact C_ne_succ j (h1.trans h2.symm)

lemma ne_of_mult_pos {x y : V} (h : 0 < mult R x y) : x ≠ y := by
  rintro rfl; rw [mult_self] at h; exact lt_irrefl _ h

end Podc.FullyDefective.RobbinsSim
