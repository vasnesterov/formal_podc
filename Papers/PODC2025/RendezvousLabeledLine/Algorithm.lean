import Papers.PODC2025.RendezvousLabeledLine.Rule

/-!
# Algorithm 5 (with ZWalk, Algorithm 4, and SearchingWalk, Algorithm 6)

All positions are in the agent's own frame (start node `0`, "first direction" `+1`).

* `zw L s`: position after `s ≤ 4L` rounds of `ZWalk(L)`.
* `sw L R r c u`: position after `u ≤ 24 L` rounds of `SearchingWalk(R, L, r, c)`: go to `r`, wait
  until round `L`, `ZWalk(8R)`, then for each bit `i < 5` of `c` either `ZWalk(8R)` twice or wait
  `64 R`, wait until round `24L - |r|`, go back to `0`.
* Iteration `k` (`L = 2^k`) of the main loop starts in round `iterStart k = 28 (2^k - 1)`:
  discovery phase `ZWalk(L)` (rounds `[0, 4L)`), then the searching phase (`24 L` rounds),
  according to `plan μ L`, which is `none` (wait at the start node) or `some (R*, r, χ(r))`.
* `plan`: `R* ` is the largest power of `4` with `16 R* ≤ L` such that some node `u` within
  distance `R*` of the start has its whole `κ R* log* ℓ(u)`-ball inside the explored interval
  `[-L, L]` (Algorithm 5, lines 4–6); `r` is the known ruling-set node closest to the start, ties
  broken by labels (line 8).
-/

namespace Podc.RendezvousLabeledLine

open Function Classical

/-! ### Walks -/

/-- `ZWalk(L)` (Algorithm 4): position after `s` rounds (`s ≤ 4 L`). -/
def zw (L s : ℕ) : ℤ :=
  if s ≤ L then (s : ℤ) else if s ≤ 3 * L then 2 * (L : ℤ) - s else (s : ℤ) - 4 * L

/-- Walking from `0` towards `r` (and staying there): position after `u` rounds. -/
def moveTo (r : ℤ) (u : ℕ) : ℤ := if 0 ≤ r then min (u : ℤ) r else max (-(u : ℤ)) r

/-- `SearchingWalk(R, L, r, c)` (Algorithm 6): position after `u` rounds (`u ≤ 24 L`). -/
def sw (L R : ℕ) (r : ℤ) (c : ℕ) (u : ℕ) : ℤ :=
  if u ≤ L then moveTo r u
  else if u ≤ L + 32 * R then r + zw (8 * R) (u - L)
  else if u < L + 352 * R then
    (if c.testBit ((u - (L + 32 * R)) / (64 * R)) then
      r + zw (8 * R) ((u - (L + 32 * R)) % (32 * R)) else r)
  else moveTo r (24 * L - u)

/-! ### The plan computed after the discovery phase -/

/-- `R` is a power of `4`. -/
def IsPow4 (R : ℕ) : Prop := ∃ j, R = 4 ^ j

section Plan

variable {κ : ℕ} (Rl : ColRuling κ)

/-- `u ∈ S_R` (Algorithm 5, line 4), in the frame: `u` is within distance `R` and its
`κ R log* ℓ(u)`-ball lies in the explored interval `[-L, L]`. -/
def Known (κ : ℕ) (μ : ℤ → ℕ) (L R : ℕ) (u : ℤ) : Prop :=
  |u| ≤ R ∧ |u| + ((κ * R * lstar (μ u) : ℕ) : ℤ) ≤ L

/-- Admissible values of `R` (Algorithm 5, line 5). -/
def Good (κ : ℕ) (μ : ℤ → ℕ) (L R : ℕ) : Prop := IsPow4 R ∧ 16 * R ≤ L ∧ ∃ u, Known κ μ L R u

/-- `R*` (Algorithm 5, line 6), `0` if there is none. -/
noncomputable def Rstar (κ : ℕ) (μ : ℤ → ℕ) (L : ℕ) : ℕ := Nat.findGreatest (Good κ μ L) L

/-- Ruling-set nodes known to the agent: known (when it commits) to some node of `S_R`. -/
def KnownMem (μ : ℤ → ℕ) (L R : ℕ) (w : ℤ) : Prop :=
  ∃ u, Known κ μ L R u ∧ Rl.knows R μ u w

/-- `r` (Algorithm 5, line 8): the known ruling-set node closest to the start, ties broken by
labels. -/
noncomputable def rsel (μ : ℤ → ℕ) (L R : ℕ) : ℤ :=
  Classical.epsilon fun w => KnownMem Rl μ L R w ∧
    ∀ w', KnownMem Rl μ L R w' → toLex (w.natAbs, μ w) ≤ toLex (w'.natAbs, μ w')

/-- The searching-phase parameters `(R*, r, χ(r))`, or `none` (Algorithm 5, lines 5–11). -/
noncomputable def plan (μ : ℤ → ℕ) (L : ℕ) : Option (ℕ × ℤ × ℕ) :=
  if Rstar κ μ L = 0 then none
  else some (Rstar κ μ L, rsel Rl μ L (Rstar κ μ L), Rl.col (Rstar κ μ L) μ (rsel Rl μ L (Rstar κ μ L)))

end Plan

/-! ### The whole algorithm -/

/-- Start of iteration `k` (parameter `L = 2^k`) of the main loop. -/
def iterStart (k : ℕ) : ℕ := 28 * (2 ^ k - 1)

/-- The iteration containing round `t`. -/
def iterOf (t : ℕ) : ℕ := Nat.log 2 (t / 28 + 1)

/-- Position in round `s < 28 L` of the iteration with parameter `L`, given the plan. -/
def phasePos (L : ℕ) (p : Option (ℕ × ℤ × ℕ)) (s : ℕ) : ℤ :=
  if s < 4 * L then zw L s
  else match p with
    | none => 0
    | some (R, r, c) => sw L R r c (s - 4 * L)

variable {κ : ℕ} (Rl : ColRuling κ)

/-- Algorithm 5 in the agent's frame. -/
noncomputable def pos5 (μ : ℤ → ℕ) (t : ℕ) : ℤ :=
  phasePos (2 ^ iterOf t) (plan Rl μ (2 ^ iterOf t)) (t - iterStart (iterOf t))

/-! ### Basic facts -/

lemma iterStart_succ (k : ℕ) : iterStart (k + 1) = iterStart k + 28 * 2 ^ k := by
  simp only [iterStart, pow_succ]
  have := Nat.one_le_two_pow (n := k)
  omega

lemma iterOf_spec (t : ℕ) : iterStart (iterOf t) ≤ t ∧ t < iterStart (iterOf t + 1) := by
  have h1 : 2 ^ iterOf t ≤ t / 28 + 1 := Nat.pow_log_le_self 2 (by omega)
  have h2 : t / 28 + 1 < 2 ^ (iterOf t + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  simp only [iterStart]
  constructor
  · have := Nat.one_le_two_pow (n := iterOf t); omega
  · omega

lemma iterOf_eq {t k : ℕ} (h1 : iterStart k ≤ t) (h2 : t < iterStart (k + 1)) : iterOf t = k := by
  simp only [iterStart] at h1 h2
  have := Nat.one_le_two_pow (n := k)
  have := Nat.one_le_two_pow (n := k + 1)
  unfold iterOf
  rw [Nat.log_eq_iff (by simp)]
  constructor <;> omega

lemma pos5_iter (μ : ℤ → ℕ) (k s : ℕ) (hs : s < 28 * 2 ^ k) :
    pos5 Rl μ (iterStart k + s) = phasePos (2 ^ k) (plan Rl μ (2 ^ k)) s := by
  have : iterOf (iterStart k + s) = k :=
    iterOf_eq (by omega) (by rw [iterStart_succ]; omega)
  simp only [pos5, this, Nat.add_sub_cancel_left]

/-! ### Walk lemmas -/

lemma zw_zero (L : ℕ) : zw L 0 = 0 := by simp [zw]

lemma zw_four (L : ℕ) : zw L (4 * L) = 0 := by
  unfold zw; split_ifs <;> push_cast <;> omega

lemma zw_L (L : ℕ) : zw L L = L := by simp [zw]

lemma zw_three (L : ℕ) : zw L (3 * L) = -L := by
  unfold zw; split_ifs <;> push_cast <;> omega

lemma zw_step (L s : ℕ) : |zw L (s + 1) - zw L s| ≤ 1 := by
  unfold zw; rw [abs_le]; split_ifs <;> push_cast <;> omega

lemma abs_zw_le (L s : ℕ) (hs : s ≤ 4 * L) : |zw L s| ≤ L := by
  unfold zw; rw [abs_le]; split_ifs <;> push_cast <;> omega

lemma zw_small (L s : ℕ) (hs : s ≤ L) : zw L s = s := by simp [zw, hs]

/-- `ZWalk(L)` reaches every node of `[-L, L]` within its first `3L` rounds. -/
lemma zw_surj (L : ℕ) (z : ℤ) (hz : |z| ≤ L) : ∃ s ≤ 3 * L, zw L s = z := by
  rw [abs_le] at hz
  rcases le_or_gt 0 z with h | h
  · exact ⟨z.toNat, by omega, by unfold zw; split_ifs <;> omega⟩
  · exact ⟨(2 * L - z).toNat, by omega, by unfold zw; split_ifs <;> omega⟩

lemma moveTo_zero (r : ℤ) : moveTo r 0 = 0 := by
  unfold moveTo; split_ifs <;> simp <;> omega

lemma moveTo_step (r : ℤ) (u : ℕ) : |moveTo r (u + 1) - moveTo r u| ≤ 1 := by
  unfold moveTo; rw [abs_le]; split_ifs <;> push_cast <;> omega

lemma moveTo_step' (r : ℤ) (u : ℕ) : |moveTo r u - moveTo r (u + 1)| ≤ 1 := by
  rw [abs_sub_comm]; exact moveTo_step r u

lemma abs_moveTo_le (r : ℤ) (u : ℕ) : |moveTo r u| ≤ |r| := by
  unfold moveTo; rw [abs_le]; split_ifs <;> rcases abs_cases r with h | h <;> omega

lemma moveTo_of_le (r : ℤ) (u : ℕ) (h : |r| ≤ u) : moveTo r u = r := by
  unfold moveTo; split_ifs <;> rcases abs_cases r with h' | h' <;> omega

private lemma divmod_succ (o m : ℕ) (hm : 0 < m) :
    ((o + 1) / m = o / m ∧ (o + 1) % m = o % m + 1) ∨ ((o + 1) % m = 0 ∧ o % m + 1 = m) := by
  have h1 := Nat.div_add_mod o m
  have h2 := Nat.mod_lt o hm
  rcases Nat.lt_or_ge (o % m + 1) m with h | h
  · left
    have e : o + 1 = (o % m + 1) + m * (o / m) := by omega
    rw [e, Nat.add_mul_div_left _ _ hm, Nat.add_mul_mod_self_left, Nat.div_eq_of_lt h,
      Nat.mod_eq_of_lt h]
    simp
  · right
    have e : o + 1 = m * (o / m + 1) := by rw [Nat.mul_add]; omega
    refine ⟨?_, by omega⟩
    rw [e, Nat.mul_mod_right]

section swRegions

variable {L R : ℕ} {r : ℤ} {c u : ℕ}

lemma sw_of_le (h : u ≤ L) : sw L R r c u = moveTo r u := by simp [sw, h]

lemma sw_of_zwalk (h1 : L < u) (h2 : u ≤ L + 32 * R) : sw L R r c u = r + zw (8 * R) (u - L) := by
  simp [sw, h2, show ¬ u ≤ L by omega]

lemma sw_of_bits (h1 : L + 32 * R < u) (h2 : u < L + 352 * R) :
    sw L R r c u = if c.testBit ((u - (L + 32 * R)) / (64 * R)) then
      r + zw (8 * R) ((u - (L + 32 * R)) % (32 * R)) else r := by
  simp only [sw]; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]

lemma sw_of_back (h1 : L + 32 * R < u) (h2 : L + 352 * R ≤ u) :
    sw L R r c u = moveTo r (24 * L - u) := by
  simp only [sw]; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

end swRegions

private lemma zw_pred (R : ℕ) (hR : 1 ≤ R) : zw (8 * R) (32 * R - 1) = -1 := by
  unfold zw; split_ifs <;> push_cast <;> omega

lemma sw_step (L R : ℕ) (r : ℤ) (c u : ℕ) (hR : 1 ≤ R) (hL : 16 * R ≤ L) (hr : |r| ≤ L)
    (hu : u + 1 ≤ 24 * L) : |sw L R r c (u + 1) - sw L R r c u| ≤ 1 := by
  by_cases h1 : u + 1 ≤ L
  · rw [sw_of_le h1, sw_of_le (by omega)]; exact moveTo_step r u
  by_cases h2 : u ≤ L
  · -- `u = L`: `r` and the first step of ZWalk
    have hu : u = L := by omega
    subst hu
    rw [sw_of_le h2, sw_of_zwalk (by omega) (by omega), moveTo_of_le r _ hr,
      show u + 1 - u = 1 by omega]
    have := zw_small (8 * R) 1 (by omega); push_cast at this; rw [this]; simp
  by_cases h3 : u + 1 ≤ L + 32 * R
  · rw [sw_of_zwalk (by omega) h3, sw_of_zwalk (by omega) (by omega),
      show u + 1 - L = (u - L) + 1 by omega]
    rw [show r + zw (8 * R) (u - L + 1) - (r + zw (8 * R) (u - L)) =
      zw (8 * R) (u - L + 1) - zw (8 * R) (u - L) by ring]
    exact zw_step _ _
  by_cases h4 : u ≤ L + 32 * R
  · -- end of the first ZWalk: at `r`
    have hu : u = L + 32 * R := by omega
    rw [sw_of_zwalk (by omega) h4, sw_of_bits (by omega) (by omega), hu,
      show L + 32 * R - L = 4 * (8 * R) by omega, zw_four]
    simp only [show L + 32 * R + 1 - (L + 32 * R) = 1 by omega,
      Nat.div_eq_of_lt (show 1 < 64 * R by omega), Nat.mod_eq_of_lt (show 1 < 32 * R by omega)]
    have := zw_small (8 * R) 1 (by omega); push_cast at this; rw [this]
    split_ifs <;> simp
  by_cases h5 : u + 1 < L + 352 * R
  · rw [sw_of_bits (by omega) h5, sw_of_bits (by omega) (by omega),
      show u + 1 - (L + 32 * R) = (u - (L + 32 * R)) + 1 by omega]
    generalize u - (L + 32 * R) = o
    rcases divmod_succ o (64 * R) (by omega) with ⟨hd, -⟩ | ⟨-, hm⟩
    · rw [hd]
      rcases divmod_succ o (32 * R) (by omega) with ⟨-, hm'⟩ | ⟨hm', hm''⟩
      · rw [hm']; split_ifs
        · rw [show r + zw (8 * R) (o % (32 * R) + 1) - (r + zw (8 * R) (o % (32 * R))) =
            zw (8 * R) (o % (32 * R) + 1) - zw (8 * R) (o % (32 * R)) by ring]
          exact zw_step _ _
        · simp
      · rw [hm', show o % (32 * R) = 32 * R - 1 by omega, zw_pred R hR]
        split_ifs <;> simp [zw_zero]
    · -- crossing a multiple of `64 R`: both positions are `r` or adjacent to it
      have hm2 : o % (32 * R) = 32 * R - 1 := by
        have := Nat.mod_mod_of_dvd o (show 32 * R ∣ 64 * R from ⟨2, by ring⟩)
        rw [← this, show o % (64 * R) = 64 * R - 1 by omega]
        have : 64 * R - 1 = (32 * R - 1) + 32 * R * 1 := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      have hm3 : (o + 1) % (32 * R) = 0 := by
        have := Nat.mod_mod_of_dvd (o + 1) (show 32 * R ∣ 64 * R from ⟨2, by ring⟩)
        rcases divmod_succ o (64 * R) (by omega) with ⟨-, h⟩ | ⟨h, -⟩
        · have := Nat.mod_lt (o + 1) (show 0 < 64 * R by omega); omega
        · rw [← this, h, Nat.zero_mod]
      rw [hm3, zw_zero, hm2, zw_pred R hR]
      split_ifs <;> simp
  by_cases h6 : u < L + 352 * R
  · -- end of the bit phase: at `r` or next to it
    have hu : u + 1 = L + 352 * R := by omega
    have hm : (u - (L + 32 * R)) % (32 * R) = 32 * R - 1 := by
      have : u - (L + 32 * R) = (32 * R - 1) + 32 * R * 9 := by omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [sw_of_back (by omega) (by omega), sw_of_bits (by omega) h6, moveTo_of_le r _ (by omega),
      hm, zw_pred R hR]
    split_ifs <;> simp
  · rw [sw_of_back (by omega) (by omega), sw_of_back (by omega) (by omega),
      show 24 * L - u = (24 * L - (u + 1)) + 1 by omega]
    exact moveTo_step' r _

lemma sw_zero (L R : ℕ) (r : ℤ) (c : ℕ) : sw L R r c 0 = 0 := by
  simp [sw, moveTo_zero]

lemma sw_end (L R : ℕ) (r : ℤ) (c : ℕ) (hR : 1 ≤ R) (hL : 16 * R ≤ L) :
    sw L R r c (24 * L) = 0 := by
  unfold sw
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), Nat.sub_self, moveTo_zero]

lemma sw_last (L R : ℕ) (r : ℤ) (c : ℕ) (hR : 1 ≤ R) (hL : 16 * R ≤ L) :
    |sw L R r c (24 * L - 1)| ≤ 1 := by
  unfold sw
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    show 24 * L - (24 * L - 1) = 0 + 1 by omega]
  have := moveTo_step r 0; rwa [moveTo_zero, sub_zero] at this

/-- During `SearchingWalk`, the agent stays within `8R` of `r` once it is there, and within `|r|`
of the start otherwise. -/
lemma abs_sw_le (L R : ℕ) (r : ℤ) (c u : ℕ) (hR : 1 ≤ R) :
    |sw L R r c u| ≤ |r| + 8 * R := by
  have hz := fun s (hs : s ≤ 4 * (8 * R)) => abs_le.1 (abs_zw_le (8 * R) s hs)
  have hm := abs_moveTo_le r
  have hr := abs_nonneg r
  have key : ∀ s, s ≤ 4 * (8 * R) → |r + zw (8 * R) s| ≤ |r| + 8 * R := fun s hs => by
    have := hz s hs; push_cast at this
    calc |r + zw (8 * R) s| ≤ |r| + |zw (8 * R) s| := abs_add_le _ _
      _ ≤ |r| + 8 * R := by gcongr; exact abs_le.2 this
  unfold sw
  split_ifs with h1 h2 h3 h4
  · have := hm u; omega
  · exact key _ (by omega)
  · exact key _ (by have := Nat.mod_lt (u - (L + 32 * R)) (show 0 < 32 * R by omega); omega)
  · omega
  · have := hm (24 * L - u); omega

/-! ### The plan -/

section PlanFacts

variable {μ μ' : ℤ → ℕ} {L R : ℕ}

lemma IsPow4.one_le {R : ℕ} (h : IsPow4 R) : 1 ≤ R := by
  obtain ⟨j, rfl⟩ := h; exact Nat.one_le_pow _ _ (by norm_num)

/-- Two distinct powers of `4`: the larger is at least four times the smaller. -/
lemma IsPow4.four_mul_le {R R' : ℕ} (h : IsPow4 R) (h' : IsPow4 R') (hlt : R < R') :
    4 * R ≤ R' := by
  obtain ⟨i, rfl⟩ := h; obtain ⟨j, rfl⟩ := h'
  have : i < j := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  calc 4 * 4 ^ i = 4 ^ (i + 1) := by ring
    _ ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) this

lemma Known.abs_le_L {u : ℤ} (h : Known κ μ L R u) : |u| ≤ L := by
  have := h.2; omega

lemma Known.ball {u : ℤ} (h : Known κ μ L R u) (x : ℤ)
    (hx : |x - u| ≤ ((κ * R * lstar (μ u) : ℕ) : ℤ)) : |x| ≤ L := by
  have := h.2
  calc |x| = |(x - u) + u| := by ring_nf
    _ ≤ |x - u| + |u| := abs_add_le _ _
    _ ≤ L := by omega

lemma KnownMem.spec (hμ : Injective μ) (hR : 1 ≤ R) {w : ℤ} (h : KnownMem Rl μ L R w) :
    ∃ u, Known κ μ L R u ∧ |w - u| ≤ (R : ℤ) - 1 ∧ Rl.inS R μ w := by
  obtain ⟨u, hu, hk⟩ := h
  exact ⟨u, hu, Rl.knows_spec R hR μ hμ u w hk⟩

lemma KnownMem.abs_le (hμ : Injective μ) (hR : 1 ≤ R) {w : ℤ} (h : KnownMem Rl μ L R w) :
    |w| ≤ 2 * (R : ℤ) - 1 := by
  obtain ⟨u, hu, hw, -⟩ := h.spec Rl hμ hR
  have := hu.1
  calc |w| = |(w - u) + u| := by ring_nf
    _ ≤ |w - u| + |u| := abs_add_le _ _
    _ ≤ 2 * (R : ℤ) - 1 := by omega

lemma Rstar_good (h : Rstar κ μ L ≠ 0) : Good κ μ L (Rstar κ μ L) :=
  Nat.findGreatest_of_ne_zero rfl h

lemma le_Rstar (h : Good κ μ L R) : R ≤ Rstar κ μ L :=
  Nat.le_findGreatest (by have := h.2.1; omega) h

lemma exists_knownMem (hμ : Injective μ) (h : Good κ μ L R) : ∃ w, KnownMem Rl μ L R w := by
  obtain ⟨hp, -, u, hu⟩ := h
  obtain ⟨w, hw⟩ := Rl.knows_exists R hp.one_le μ hμ u
  exact ⟨w, u, hu, hw⟩

lemma rsel_spec (hμ : Injective μ) (h : Good κ μ L R) : KnownMem Rl μ L R (rsel Rl μ L R) := by
  obtain ⟨w₀, hw₀⟩ := exists_knownMem Rl hμ h
  let S : Finset ℤ := (Finset.Icc (-(2 * R : ℤ)) (2 * R)).filter (KnownMem Rl μ L R)
  have hS : ∀ w, w ∈ S ↔ KnownMem Rl μ L R w := fun w => by
    simp only [S, Finset.mem_filter, Finset.mem_Icc, and_iff_right_iff_imp]
    intro hw; have := abs_le.1 (hw.abs_le Rl hμ h.1.one_le); omega
  obtain ⟨w, hwS, hmin⟩ := Finset.exists_min_image S (fun w => toLex (w.natAbs, μ w))
    ⟨w₀, (hS w₀).2 hw₀⟩
  exact (Classical.epsilon_spec (p := fun w => KnownMem Rl μ L R w ∧
    ∀ w', KnownMem Rl μ L R w' → toLex (w.natAbs, μ w) ≤ toLex (w'.natAbs, μ w'))
    ⟨w, (hS w).1 hwS, fun w' hw' => hmin w' ((hS w').2 hw')⟩).1

/-- What the plan guarantees (for an injective labelling). -/
lemma plan_some (hμ : Injective μ) {r : ℤ} {c : ℕ} (h : plan Rl μ L = some (R, r, c)) :
    Good κ μ L R ∧ (∀ R', Good κ μ L R' → R' ≤ R) ∧ KnownMem Rl μ L R r ∧ c = Rl.col R μ r := by
  unfold plan at h
  split_ifs at h with h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨Rstar_good h0, fun R' h' => le_Rstar h', rsel_spec Rl hμ (Rstar_good h0), rfl⟩

lemma plan_none (h : plan Rl μ L = none) (R : ℕ) : ¬ Good κ μ L R := by
  unfold plan at h
  split_ifs at h with h0
  intro hg; have := le_Rstar hg; have := hg.1.one_le; omega

lemma plan_some_bounds (hμ : Injective μ) {r : ℤ} {c : ℕ} (h : plan Rl μ L = some (R, r, c)) :
    1 ≤ R ∧ 16 * R ≤ L ∧ |r| ≤ 2 * (R : ℤ) - 1 := by
  obtain ⟨hg, -, hr, -⟩ := plan_some Rl hμ h
  exact ⟨hg.1.one_le, hg.2.1, hr.abs_le Rl hμ hg.1.one_le⟩

/-! #### The plan depends only on the explored interval `[-L, L]` -/

variable (hμ : Injective μ) (hμ' : Injective μ') (hag : ∀ x : ℤ, |x| ≤ L → μ' x = μ x)
include hag

lemma known_congr (u : ℤ) : Known κ μ' L R u ↔ Known κ μ L R u := by
  constructor
  · intro h; have := hag u h.abs_le_L; unfold Known at *; rwa [← this]
  · intro h; have := hag u h.abs_le_L; unfold Known at *; rwa [this]

lemma good_congr : Good κ μ' L = Good κ μ L := by
  funext R; simp only [Good, known_congr hag]

lemma Rstar_congr : Rstar κ μ' L = Rstar κ μ L := by simp only [Rstar, good_congr hag]

include hμ hμ'

lemma knownMem_congr (hR : 1 ≤ R) (w : ℤ) : KnownMem Rl μ' L R w ↔ KnownMem Rl μ L R w := by
  unfold KnownMem
  refine exists_congr fun u => ?_
  rw [known_congr hag]
  constructor
  · rintro ⟨hu, hk⟩
    exact ⟨hu, (Rl.local_ R hR μ μ' hμ hμ' u (fun x hx => hag x (hu.ball x hx)) w).1.1 hk⟩
  · rintro ⟨hu, hk⟩
    exact ⟨hu, (Rl.local_ R hR μ μ' hμ hμ' u (fun x hx => hag x (hu.ball x hx)) w).1.2 hk⟩

lemma rsel_congr (hR : 1 ≤ R) (hRL : 2 * R ≤ L) : rsel Rl μ' L R = rsel Rl μ L R := by
  unfold rsel
  congr 1
  funext w
  have hkm := knownMem_congr Rl hμ hμ' hag hR
  have hlab : ∀ w, KnownMem Rl μ L R w → μ' w = μ w := fun w hw =>
    hag w (by have := hw.abs_le Rl hμ hR; omega)
  apply propext
  simp only [hkm]
  constructor
  · rintro ⟨hw, hmin⟩; refine ⟨hw, fun w' hw' => ?_⟩
    have := hmin w' hw'; rwa [hlab w hw, hlab w' hw'] at this
  · rintro ⟨hw, hmin⟩; refine ⟨hw, fun w' hw' => ?_⟩
    rw [hlab w hw, hlab w' hw']; exact hmin w' hw'

lemma plan_congr : plan Rl μ' L = plan Rl μ L := by
  unfold plan
  rw [Rstar_congr hag]
  split_ifs with h0
  · rfl
  have hg := Rstar_good (μ := μ) (L := L) h0
  have hR := hg.1.one_le
  rw [rsel_congr Rl hμ hμ' hag hR (by have := hg.2.1; omega)]
  congr 3
  obtain ⟨u, hu, hk⟩ := rsel_spec Rl hμ hg
  exact (Rl.local_ _ hR μ μ' hμ hμ' u (fun x hx => hag x (hu.ball x hx)) _).2 hk

end PlanFacts

/-! ### Algorithm 5 as an agent algorithm -/

lemma phasePos_lt (L : ℕ) (p : Option (ℕ × ℤ × ℕ)) {s : ℕ} (hs : s < 4 * L) :
    phasePos L p s = zw L s := by simp [phasePos, hs]

lemma phasePos_none (L s : ℕ) (hs : 4 * L ≤ s) : phasePos L none s = 0 := by
  simp [phasePos, not_lt.2 hs]

lemma phasePos_some (L R : ℕ) (r : ℤ) (c s : ℕ) (hs : 4 * L ≤ s) :
    phasePos L (some (R, r, c)) s = sw L R r c (s - 4 * L) := by
  simp [phasePos, not_lt.2 hs]

lemma iterOf_zero : iterOf 0 = 0 := by simp [iterOf]

lemma pos5_zero (μ : ℤ → ℕ) : pos5 Rl μ 0 = 0 := by
  simp [pos5, iterOf_zero, iterStart, phasePos, zw]

/-- One step of Algorithm 5 inside an iteration (`s + 1 < 28 L`) or across an iteration
boundary. -/
lemma phasePos_step {μ : ℤ → ℕ} (hμ : Injective μ) (k s : ℕ) (hs : s + 1 < 28 * 2 ^ k) :
    |phasePos (2 ^ k) (plan Rl μ (2 ^ k)) (s + 1) - phasePos (2 ^ k) (plan Rl μ (2 ^ k)) s| ≤ 1 := by
  set L := 2 ^ k
  by_cases h1 : s + 1 < 4 * L
  · rw [phasePos_lt _ _ h1, phasePos_lt _ _ (by omega)]; exact zw_step _ _
  have hz : s < 4 * L → |zw L s| ≤ 1 := fun h2 => by
    have h2 : s + 1 = 4 * L := by omega
    have := zw_step L s; rwa [h2, zw_four, zero_sub, abs_neg] at this
  rcases hp : plan Rl μ L with _ | ⟨R, r, c⟩
  · by_cases h2 : 4 * L ≤ s
    · rw [phasePos_none _ _ (by omega), phasePos_none _ _ h2]; simp
    · rw [phasePos_none _ _ (by omega), phasePos_lt _ _ (by omega)]
      rw [zero_sub, abs_neg]; exact hz (by omega)
  · obtain ⟨hR, hL, hr⟩ := plan_some_bounds Rl hμ hp
    by_cases h2 : 4 * L ≤ s
    · rw [phasePos_some _ _ _ _ _ (by omega), phasePos_some _ _ _ _ _ h2,
        show s + 1 - 4 * L = (s - 4 * L) + 1 by omega]
      exact sw_step _ _ _ _ _ hR hL (by omega) (by omega)
    · rw [phasePos_some _ _ _ _ _ (by omega), phasePos_lt _ _ (by omega),
        show s + 1 - 4 * L = 0 by omega, sw_zero]
      rw [zero_sub, abs_neg]; exact hz (by omega)

lemma pos5_step {μ : ℤ → ℕ} (hμ : Injective μ) (t : ℕ) :
    |pos5 Rl μ (t + 1) - pos5 Rl μ t| ≤ 1 := by
  obtain ⟨h1, h2⟩ := iterOf_spec t
  generalize iterOf t = k at h1 h2
  obtain ⟨s, rfl⟩ : ∃ s, t = iterStart k + s := ⟨t - iterStart k, by omega⟩
  rw [iterStart_succ] at h2
  by_cases hs : s + 1 < 28 * 2 ^ k
  · rw [pos5_iter Rl μ k s (by omega), show iterStart k + s + 1 = iterStart k + (s + 1) by ring,
      pos5_iter Rl μ k (s + 1) hs]
    exact phasePos_step Rl hμ k s hs
  · -- last round of an iteration
    have hs' : s + 1 = 28 * 2 ^ k := by omega
    rw [pos5_iter Rl μ k s (by omega), show iterStart k + s + 1 = iterStart (k + 1) + 0 by
      rw [iterStart_succ]; omega, pos5_iter Rl μ (k + 1) 0 (by positivity),
      phasePos_lt _ _ (by positivity), zw_zero, zero_sub, abs_neg]
    rcases hp : plan Rl μ (2 ^ k) with _ | ⟨R, r, c⟩
    · rw [phasePos_none _ _ (by omega)]; simp
    · obtain ⟨hR, hL, hr⟩ := plan_some_bounds Rl hμ hp
      rw [phasePos_some _ _ _ _ _ (by omega), show s - 4 * 2 ^ k = 24 * 2 ^ k - 1 by omega]
      exact sw_last _ _ _ _ hR hL

lemma pos5_causal (μ μ' : ℤ → ℕ) (hμ : Injective μ) (hμ' : Injective μ') (t : ℕ)
    (h : ∀ s ≤ t, μ' (pos5 Rl μ s) = μ (pos5 Rl μ s)) : pos5 Rl μ' (t + 1) = pos5 Rl μ (t + 1) := by
  obtain ⟨h1, h2⟩ := iterOf_spec (t + 1)
  generalize iterOf (t + 1) = k at h1 h2
  obtain ⟨s, hs⟩ : ∃ s, t + 1 = iterStart k + s := ⟨t + 1 - iterStart k, by omega⟩
  rw [iterStart_succ] at h2
  rw [hs, pos5_iter Rl μ k s (by omega), pos5_iter Rl μ' k s (by omega)]
  by_cases hs4 : s < 4 * 2 ^ k
  · rw [phasePos_lt _ _ hs4, phasePos_lt _ _ hs4]
  · rw [plan_congr Rl hμ hμ' (L := 2 ^ k)]
    intro x hx
    obtain ⟨s', hs', hzs⟩ := zw_surj (2 ^ k) x (by exact_mod_cast hx)
    have := h (iterStart k + s') (by omega)
    rwa [pos5_iter Rl μ k s' (by omega), phasePos_lt _ _ (by omega), hzs] at this

/-- **Algorithm 5** (in the model with simultaneous edge-crossing detection), as an agent
algorithm. -/
noncomputable def alg5 : Algo where
  pos := pos5 Rl
  pos_zero := pos5_zero Rl
  step _ hμ := pos5_step Rl hμ
  causal := pos5_causal Rl

/-- The final algorithm: `care(Algorithm 5)` (Theorem 3.1 applied to Algorithm 5). -/
noncomputable def algFinal : Algo := (alg5 Rl).care

end Podc.RendezvousLabeledLine
