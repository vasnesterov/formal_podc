import Papers.PODC2016.UniformDeploymentRings.Defs

/-!
# Algorithm 1: the target nodes form a uniform deployment

For a set `H` of `k ≥ 1` home nodes in the ring `ZMod n`, the agent of Algorithm 1 whose home is
`h` ends its deployment phase at node `h + moves1 (distSeq H h)` (it first walks once around the
ring, which adds `n ≡ 0`). We prove (Section 3.1 and 3.1.1 of the paper):

* `alg1_targets` (`alg1_targets_injOn`, `alg1_targets_uniform`) : the target map `alg1Target H`
  is injective on `H` and its image is a uniform deployment;
* `alg1_targets_injOn` : different agents choose different target nodes;
* `alg1_targets_uniform` : the set of target nodes is a uniform deployment;
* `moves1_lt` : the deployment phase takes fewer than `2n` moves.

The proof unrolls the ring: for `h ∈ H`, `pos H h j` is the position (counted from `h` on the
infinite unrolled line) of the `j`-th home node after `h`; `pos H h (j + k) = pos H h j + n`.
The distance sequence of the `i`-th home node after `h` is `(distSeq H h).rotate i`. Choosing `h`
with lexicographically minimal distance sequence, the rotations equal to it are exactly the
multiples of the period `p`, so the agent `i` has rank `x < p` with `p ∣ i + x`, and its target is
`h + (i + x) / p * N + offset x N p` where `N` is the length of a period. These targets are
`h + G t`, `t < k`, for an explicit strictly increasing `G` with steps `⌊n/k⌋` or `⌈n/k⌉`.
-/

namespace Podc.UniformDeploymentRings

variable {n : ℕ}

/-! ### Basic facts about `gap`, `next` and `distSeq` -/

theorem gap_pos (H : Finset (ZMod n)) (h : ZMod n) : 0 < gap H h :=
  (Nat.find_spec (⟨max n 1, by omega, Or.inr (le_max_left _ _)⟩ :
    ∃ d : ℕ, 0 < d ∧ (h + (d : ZMod n) ∈ H ∨ n ≤ d))).1

@[simp] theorem length_distSeq (H : Finset (ZMod n)) (h : ZMod n) :
    (distSeq H h).length = H.card := by
  simp [distSeq]

/-- All entries of a distance sequence are positive. -/
theorem pos_of_mem_distSeq {H : Finset (ZMod n)} {h : ZMod n} {d : ℕ} (hd : d ∈ distSeq H h) :
    0 < d := by
  simp only [distSeq, List.mem_map] at hd
  obtain ⟨j, -, rfl⟩ := hd
  exact gap_pos _ _

theorem iterate_next_eq_add_sum_take (H : Finset (ZMod n)) (h : ZMod n) {j : ℕ}
    (hj : j ≤ H.card) : (next H)^[j] h = h + (((distSeq H h).take j).sum : ℕ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hD : (distSeq H h)[j]'(by simp; omega) = gap H ((next H)^[j] h) := by simp [distSeq]
    rw [List.sum_take_succ _ _ (by simp; omega), hD, Function.iterate_succ_apply', next,
      ih (by omega)]
    push_cast; ring

/-! ### The unrolled ring -/

/-- The predicate "`h + m` is a home node". -/
abbrev IsHomeAt (H : Finset (ZMod n)) (h : ZMod n) (m : ℕ) : Prop := h + (m : ZMod n) ∈ H

/-- Position, on the unrolled ring starting at `h`, of the `j`-th home node after `h`. -/
noncomputable def pos (H : Finset (ZMod n)) (h : ZMod n) (j : ℕ) : ℕ := Nat.nth (IsHomeAt H h) j

section Pos

variable [NeZero n] {H : Finset (ZMod n)} {h : ZMod n}

omit [NeZero n] in
theorem isHomeAt_add_n (m : ℕ) : IsHomeAt H h (m + n) ↔ IsHomeAt H h m := by
  simp [IsHomeAt]

theorem infinite_isHomeAt (hh : h ∈ H) : (Set.ofPred (IsHomeAt H h)).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨(a + 1) * n, ?_, ?_⟩
  · show IsHomeAt H h ((a + 1) * n); simp [IsHomeAt, hh]
  · have : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    nlinarith

theorem pos_mem (hh : h ∈ H) (j : ℕ) : h + (pos H h j : ZMod n) ∈ H :=
  Nat.nth_mem_of_infinite (infinite_isHomeAt hh) j

theorem pos_strictMono (hh : h ∈ H) : StrictMono (pos H h) :=
  Nat.nth_strictMono (infinite_isHomeAt hh)

omit [NeZero n] in
theorem pos_zero (hh : h ∈ H) : pos H h 0 = 0 :=
  Nat.nth_zero_of_zero (by simpa [IsHomeAt] using hh)

omit [NeZero n] in
theorem not_isHomeAt_of_lt_pos_succ (j m : ℕ) (h1 : pos H h j < m) (h2 : m < pos H h (j + 1)) :
    ¬ IsHomeAt H h m := fun hm =>
  absurd (Nat.le_nth_of_lt_nth_succ h2 hm) (by unfold pos at h1; omega)

theorem count_add_n (hk : H.card = k) (m : ℕ) :
    Nat.count (IsHomeAt H h) (m + n) = Nat.count (IsHomeAt H h) m + k := by
  rw [Nat.count_add]
  congr 1
  rw [Nat.count_eq_card_filter_range, ← hk]
  refine Finset.card_nbij (fun i => h + ((m + i : ℕ) : ZMod n)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi
    exact hi.2
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj
    simp only [add_right_inj] at hij
    push_cast at hij
    have := congrArg ZMod.val (add_left_cancel hij)
    rwa [ZMod.val_natCast_of_lt hi.1, ZMod.val_natCast_of_lt hj.1] at this
  · intro x hx
    refine ⟨(x - h - m).val, ?_, ?_⟩
    · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, IsHomeAt]
      refine ⟨ZMod.val_lt _, ?_⟩
      push_cast
      simpa using hx
    · simp

theorem pos_add_card (hh : h ∈ H) (hk : H.card = k) (j : ℕ) :
    pos H h (j + k) = pos H h j + n := by
  have hinf := infinite_isHomeAt hh
  have hm : IsHomeAt H h (pos H h j + n) :=
    (isHomeAt_add_n _).2 (Nat.nth_mem_of_infinite hinf j)
  have := Nat.nth_count hm
  rw [count_add_n hk, show Nat.count (IsHomeAt H h) (pos H h j) = j from
    Nat.count_nth_of_infinite hinf j] at this
  exact this

theorem pos_card (hh : h ∈ H) (hk : H.card = k) : pos H h k = n := by
  simpa [pos_zero hh] using pos_add_card hh hk 0

theorem gap_pos_eq (hh : h ∈ H) (j : ℕ) :
    gap H (h + (pos H h j : ZMod n)) = pos H h (j + 1) - pos H h j := by
  have hmono := pos_strictMono hh
  have hlt : pos H h j < pos H h (j + 1) := hmono (Nat.lt_succ_self j)
  have hle : pos H h (j + 1) ≤ pos H h j + n := by
    by_contra hcon
    exact not_isHomeAt_of_lt_pos_succ (H := H) (h := h) j (pos H h j + n)
      (by have := Nat.pos_of_ne_zero (NeZero.ne n); omega) (by omega)
      ((isHomeAt_add_n _).2 (pos_mem hh j))
  unfold gap
  rw [Nat.find_eq_iff]
  refine ⟨⟨by omega, Or.inl ?_⟩, ?_⟩
  · rw [Nat.cast_sub hlt.le, add_assoc, add_sub_cancel]; exact pos_mem hh _
  · rintro e he ⟨he0, he1 | he1⟩
    · exact not_isHomeAt_of_lt_pos_succ (H := H) (h := h) j (pos H h j + e) (by omega) (by omega)
        (by simpa [IsHomeAt, add_assoc] using he1)
    · omega

theorem iterate_next_eq_pos (hh : h ∈ H) (j : ℕ) :
    (next H)^[j] h = h + (pos H h j : ZMod n) := by
  induction j with
  | zero => simp [pos_zero hh]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, next, gap_pos_eq hh,
      Nat.cast_sub (pos_strictMono hh (Nat.lt_succ_self j)).le]
    ring

/-- The steps of the unrolled ring. -/
noncomputable def homeGap (H : Finset (ZMod n)) (h : ZMod n) (j : ℕ) : ℕ :=
  pos H h (j + 1) - pos H h j

theorem pos_succ (hh : h ∈ H) (j : ℕ) : pos H h (j + 1) = pos H h j + homeGap H h j := by
  have := pos_strictMono hh (by omega : j < j + 1)
  unfold homeGap; omega

theorem step_add_card (hh : h ∈ H) (hk : H.card = k) (j : ℕ) : homeGap H h (j + k) = homeGap H h j := by
  unfold homeGap
  rw [show j + k + 1 = (j + 1) + k by omega, pos_add_card hh hk, pos_add_card hh hk]
  omega

/-- The distance sequence of the `i`-th home node after `h`, in terms of `homeGap`. -/
theorem distSeq_iterate (hh : h ∈ H) (i : ℕ) :
    distSeq H ((next H)^[i] h) = (List.range H.card).map fun j => homeGap H h (i + j) := by
  unfold distSeq
  congr 1
  funext j
  rw [← Function.iterate_add_apply, iterate_next_eq_pos hh, gap_pos_eq hh, homeGap, add_comm j i]

theorem step_add_mul_card (hh : h ∈ H) (hk : H.card = k) (r q : ℕ) :
    homeGap H h (r + q * k) = homeGap H h r := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, ← add_assoc, step_add_card hh hk, ih]

theorem step_mod_card (hh : h ∈ H) (hk : H.card = k) (a : ℕ) :
    homeGap H h (a % k) = homeGap H h a := by
  conv_rhs => rw [← Nat.mod_add_div' a k]
  rw [step_add_mul_card hh hk]

theorem pos_add_mul_card (hh : h ∈ H) (hk : H.card = k) (r q : ℕ) :
    pos H h (r + q * k) = pos H h r + q * n := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, ← add_assoc, pos_add_card hh hk, ih, Nat.succ_mul, add_assoc]

/-- Positions on the unrolled ring only matter modulo `n`, so only their index modulo `k`. -/
theorem cast_pos_mod_card (hh : h ∈ H) (hk : H.card = k) (a : ℕ) :
    (pos H h (a % k) : ZMod n) = pos H h a := by
  conv_rhs => rw [← Nat.mod_add_div' a k]
  rw [pos_add_mul_card hh hk]
  push_cast
  simp

theorem distSeq_eq_map_step (hh : h ∈ H) :
    distSeq H h = (List.range H.card).map fun j => homeGap H h j := by
  simpa using distSeq_iterate hh 0

theorem sum_take_distSeq_iterate (hh : h ∈ H) (i : ℕ) {m : ℕ} (hm : m ≤ H.card) :
    ((distSeq H ((next H)^[i] h)).take m).sum = pos H h (i + m) - pos H h i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.sum_take_succ _ _ (by simp; omega), ih (by omega)]
    have h1 := pos_succ hh (i + m)
    have h2 := (pos_strictMono hh).monotone (Nat.le_add_right i m)
    simp only [distSeq_iterate hh, List.getElem_map, List.getElem_range]
    rw [← add_assoc]; omega

/-- The distance sequence observed from `(next H)^[i] h` is the `i`-th rotation of the one
observed from `h`. -/
theorem distSeq_iterate_eq_rotate (hh : h ∈ H) (i : ℕ) :
    distSeq H ((next H)^[i] h) = (distSeq H h).rotate i := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_rotate, distSeq_iterate hh, distSeq_eq_map_step hh, List.getElem_map,
    List.getElem_range, List.length_map, List.length_range]
  rw [step_mod_card hh rfl, add_comm]

end Pos

section Facts

variable [NeZero n] {H : Finset (ZMod n)} {h : ZMod n}

/-- The distances of `D(h)` sum up to `n`. -/
theorem sum_distSeq (hh : h ∈ H) : (distSeq H h).sum = n := by
  have := sum_take_distSeq_iterate hh 0 (le_refl H.card)
  rw [List.take_of_length_le (by simp)] at this
  simpa [pos_card hh rfl, pos_zero hh] using this

/-- Walking `k` home nodes ahead brings the agent back home. -/
theorem iterate_next_card (hh : h ∈ H) : (next H)^[H.card] h = h := by
  rw [iterate_next_eq_pos hh, pos_card hh rfl]; simp

theorem iterate_next_mem (hh : h ∈ H) (j : ℕ) : (next H)^[j] h ∈ H := by
  rw [iterate_next_eq_pos hh]; exact pos_mem hh j

theorem next_mem (hh : h ∈ H) : next H h ∈ H := iterate_next_mem hh 1

theorem distSeq_next (hh : h ∈ H) : distSeq H (next H h) = (distSeq H h).rotate 1 :=
  distSeq_iterate_eq_rotate hh 1

/-- Every home node is reached from `h` within `k` steps. -/
theorem exists_iterate_next_eq (hh : h ∈ H) {x : ZMod n} (hx : x ∈ H) :
    ∃ i < H.card, (next H)^[i] h = x := by
  have hinf := infinite_isHomeAt hh
  have hpx : IsHomeAt H h (x - h).val := by simp [IsHomeAt, hx]
  refine ⟨Nat.count (IsHomeAt H h) (x - h).val, ?_, ?_⟩
  · have h1 : pos H h (Nat.count (IsHomeAt H h) (x - h).val) < pos H h H.card := by
      rw [pos, Nat.nth_count hpx, pos_card hh rfl]; exact ZMod.val_lt _
    exact (pos_strictMono hh).lt_iff_lt.1 h1
  · rw [iterate_next_eq_pos hh, pos, Nat.nth_count hpx]; simp

end Facts

/-! ### Rotations, period and rank of a list -/

section Lists

theorem period_spec (D : List ℕ) : 0 < period D ∧ D.rotate (period D) = D :=
  Nat.find_spec (⟨max D.length 1, by omega, by
    rcases Nat.eq_zero_or_pos D.length with h | h
    · simp [List.length_eq_zero_iff.mp h]
    · rw [max_eq_left h]; exact List.rotate_length D⟩ : ∃ p, 0 < p ∧ D.rotate p = D)

theorem period_pos (D : List ℕ) : 0 < period D := (period_spec D).1

theorem rotate_period_mul (D : List ℕ) (q : ℕ) : D.rotate (period D * q) = D := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← List.rotate_rotate, ih, (period_spec D).2]

/-- The rotations of `D` fixing `D` are exactly the multiples of its period. -/
theorem rotate_eq_self_iff (D : List ℕ) (m : ℕ) : D.rotate m = D ↔ period D ∣ m := by
  constructor
  · intro hm
    have h1 : D.rotate (m % period D) = D := by
      have := hm
      rwa [← Nat.div_add_mod m (period D), ← List.rotate_rotate, rotate_period_mul] at this
    by_contra hd
    have h2 : 0 < m % period D := Nat.pos_of_ne_zero (fun h0 => hd (Nat.dvd_of_mod_eq_zero h0))
    exact Nat.find_min _ (Nat.mod_lt m (period_pos D)) ⟨h2, h1⟩
  · rintro ⟨q, rfl⟩; exact rotate_period_mul D q

theorem period_dvd_length (D : List ℕ) : period D ∣ D.length :=
  (rotate_eq_self_iff D _).1 (List.rotate_length D)

theorem period_rotate (D : List ℕ) (i : ℕ) : period (D.rotate i) = period D := by
  have key : ∀ m, period (D.rotate i) ∣ m ↔ period D ∣ m := by
    intro m
    rw [← rotate_eq_self_iff, ← rotate_eq_self_iff, List.rotate_rotate, add_comm,
      ← List.rotate_rotate, List.rotate_eq_rotate]
  exact Nat.dvd_antisymm ((key _).2 dvd_rfl) ((key _).1 dvd_rfl)

theorem isMinRot_iff (D : List ℕ) (x : ℕ) : IsMinRot D x ↔ ∀ z, D.rotate x ≤ D.rotate z := by
  refine ⟨fun h z => ?_, fun h z _ => h z⟩
  rcases Nat.eq_zero_or_pos D.length with h0 | h0
  · simp [List.length_eq_zero_iff.mp h0]
  · rw [← List.rotate_mod D z]; exact h (z % D.length) (Nat.mod_lt _ h0)

theorem rank_spec (D : List ℕ) : IsMinRot D (rank D) := Nat.find_spec (exists_isMinRot D)

theorem rank_lt_period (D : List ℕ) : rank D < period D := by
  by_contra hlt
  rw [not_lt] at hlt
  have : IsMinRot D (rank D - period D) := by
    have h := rank_spec D
    rwa [isMinRot_iff, show rank D = period D + (rank D - period D) by omega, ← List.rotate_rotate,
      (period_spec D).2, ← isMinRot_iff] at h
  exact Nat.find_min (exists_isMinRot D) (by have := period_pos D; omega : rank D - period D < rank D)
    this

/-- If `D` is its own minimum rotation, then `D.rotate i` is minimal at rotation index `y` iff
`period D ∣ i + y`. -/
theorem isMinRot_rotate_iff {D : List ℕ} (hD : IsMinRot D 0) (i y : ℕ) :
    IsMinRot (D.rotate i) y ↔ period D ∣ i + y := by
  rw [isMinRot_iff] at hD ⊢
  simp only [List.rotate_rotate]
  rw [← rotate_eq_self_iff]
  simp only [List.rotate_zero] at hD
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos D.length with h0 | h0
    · simp [List.length_eq_zero_iff.mp h0]
    have h1 := h ((D.length - 1) * i)
    have he : i + (D.length - 1) * i = D.length * i := by
      obtain ⟨l, hl⟩ : ∃ l, D.length = l + 1 := ⟨D.length - 1, by omega⟩
      rw [hl, Nat.add_sub_cancel]; ring
    rw [he, List.rotate_length_mul] at h1
    exact le_antisymm h1 (hD _)
  · intro h z; rw [h]; exact hD _

/-- The rank of `D.rotate i`, when `D` is its own minimum rotation. -/
theorem rank_rotate {D : List ℕ} (hD : IsMinRot D 0) {i x : ℕ} (hx : x < period D)
    (hdvd : period D ∣ i + x) : rank (D.rotate i) = x := by
  unfold rank
  rw [Nat.find_eq_iff]
  refine ⟨(isMinRot_rotate_iff hD i x).2 hdvd, fun y hy hmin => ?_⟩
  rw [isMinRot_rotate_iff hD] at hmin
  have := Nat.dvd_sub hdvd hmin
  rw [show i + x - (i + y) = x - y by omega] at this
  exact absurd (Nat.le_of_dvd (by omega) this) (by omega)

end Lists

/-! ### The offsets of Section 3.1.1 -/

section Offset

theorem offset_zero (N p : ℕ) : offset 0 N p = 0 := by simp [offset]

theorem offset_succ (x N p : ℕ) :
    offset (x + 1) N p = offset x N p + N / p + if x < N % p then 1 else 0 := by
  unfold offset
  rw [add_mul, one_mul]
  split_ifs <;> omega

theorem offset_period {N p : ℕ} (hp : 0 < p) : offset p N p = N := by
  unfold offset
  rw [min_eq_right (Nat.mod_lt N hp).le]; exact Nat.div_add_mod N p

theorem offset_mono {N p x y : ℕ} (hxy : x ≤ y) : offset x N p ≤ offset y N p := by
  unfold offset
  have := Nat.mul_le_mul_right (N / p) hxy
  have := min_le_min_right (N % p) hxy
  omega

theorem offset_lt {x N p : ℕ} (hx : x < p) (hpN : p ≤ N) : offset x N p < N := by
  have hp : 0 < p := by omega
  have ha := Nat.div_pos hpN hp
  have h1 := offset_mono (N := N) (p := p) (Nat.succ_le_of_lt hx)
  rw [offset_succ, offset_period hp] at h1
  split_ifs at h1 <;> omega

end Offset

/-! ### Uniform deployment from a homeGap function -/

section Steps

theorem lt_of_steps {k : ℕ} {G : ℕ → ℕ} (hmono : ∀ t < k, G t < G (t + 1)) {s t : ℕ}
    (hst : s < t) (ht : t ≤ k) : G s < G t := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hst with h | rfl
    · exact (ih h (by omega)).trans (hmono t (by omega))
    · exact hmono s (by omega)

theorem le_of_steps {k : ℕ} {G : ℕ → ℕ} (hmono : ∀ t < k, G t < G (t + 1)) {s t : ℕ}
    (hst : s ≤ t) (ht : t ≤ k) : G s ≤ G t := by
  rcases hst.lt_or_eq with h | rfl
  · exact (lt_of_steps hmono h ht).le
  · exact le_rfl

/-- If `0 = G 0 < G 1 < ⋯ < G k = n` and every homeGap `G (t + 1) - G t` is `⌊n/k⌋` or `⌈n/k⌉`, then
the `k` nodes `c + G t` (`t < k`) are distinct and form a uniform deployment. -/
theorem isUniformSet_of_steps [NeZero n] {k : ℕ} (hk : 0 < k) (G : ℕ → ℕ) (c : ZMod n)
    (hG0 : G 0 = 0) (hGk : G k = n) (hmono : ∀ t < k, G t < G (t + 1))
    (hstep : ∀ t < k, G (t + 1) - G t = n / k ∨ G (t + 1) - G t = (n + k - 1) / k) :
    IsUniformSet n k ((Finset.range k).image fun t => c + (G t : ZMod n)) ∧
      ((Finset.range k).image fun t => c + (G t : ZMod n)).card = k := by
  set S := (Finset.range k).image fun t => c + (G t : ZMod n) with hS
  have hlt : ∀ t < k, G t < n := fun t ht => hGk ▸ lt_of_steps hmono ht le_rfl
  have hinj : ∀ s < k, ∀ t < k, (G s : ZMod n) = G t → s = t := by
    intro s hs t ht hst
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt s hs),
      Nat.mod_eq_of_lt (hlt t ht)] at hst
    rcases lt_trichotomy s t with h | h | h
    · exact absurd hst (lt_of_steps hmono h ht.le).ne
    · exact h
    · exact absurd hst (lt_of_steps hmono h hs.le).ne'
  refine ⟨⟨fun v => by dsimp only; split_ifs <;> simp, ?_⟩, ?_⟩
  · intro v hv
    have hvS : v ∈ S := by by_contra h; simp [h] at hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hvS
    rw [Finset.mem_range] at ht
    have hm := hmono t ht
    have hGt1 : G (t + 1) ≤ n := hGk ▸ le_of_steps hmono (by omega) le_rfl
    refine ⟨G (t + 1) - G t, hstep t ht, by omega, ?_, ?_⟩
    · have : c + (G t : ZMod n) + ((G (t + 1) - G t : ℕ) : ZMod n) = c + G (t + 1) := by
        rw [Nat.cast_sub hm.le]; ring
      dsimp only
      rw [this]
      simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
      rcases (by omega : t + 1 < k ∨ t + 1 = k) with h | h
      · exact Finset.mem_image.2 ⟨t + 1, Finset.mem_range.2 h, rfl⟩
      · exact Finset.mem_image.2 ⟨0, Finset.mem_range.2 hk, by rw [h, hGk, hG0]; simp⟩
    · intro e he0 he
      simp only [ite_eq_right_iff, one_ne_zero, imp_false]
      intro hmem
      obtain ⟨s, hs, hse⟩ := Finset.mem_image.1 hmem
      rw [Finset.mem_range] at hs
      rw [add_assoc, add_right_inj, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff',
        Nat.mod_eq_of_lt (hlt s hs), Nat.mod_eq_of_lt (by omega)] at hse
      rcases le_or_gt s t with h | h
      · have := le_of_steps hmono h ht.le; omega
      · have := le_of_steps hmono (show t + 1 ≤ s by omega) hs.le; omega
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro s hs t ht hst
    exact hinj s (by simpa using hs) t (by simpa using ht) (add_left_cancel hst)

/-- If `G 0 = 0`, `G k = n` and every homeGap of `G` is `a` or `a + 1`, then every homeGap is
`⌊n/k⌋` or `⌈n/k⌉`. -/
theorem steps_floor_ceil {k a : ℕ} {G : ℕ → ℕ} (hG0 : G 0 = 0) (hGk : G k = n)
    (hstep : ∀ t < k, G (t + 1) = G t + a ∨ G (t + 1) = G t + a + 1) :
    ∀ t < k, G (t + 1) - G t = n / k ∨ G (t + 1) - G t = (n + k - 1) / k := by
  have bounds : ∀ s j, s + j ≤ k → G s + j * a ≤ G (s + j) ∧ G (s + j) ≤ G s + j * a + j := by
    intro s j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have := ih (by omega)
      rw [show s + (j + 1) = s + j + 1 by omega, Nat.succ_mul]
      rcases hstep (s + j) (by omega) with h | h <;> omega
  intro t ht
  obtain ⟨j, rfl⟩ : ∃ j, k = t + 1 + j := ⟨k - t - 1, by omega⟩
  have b1 := bounds 0 t (by omega)
  have b2 := bounds (t + 1) j le_rfl
  simp only [hG0, zero_add] at b1
  have r1 : a * (t + 1 + j) = t * a + a + j * a := by ring
  have r2 : (a + 1) * (t + 1 + j) = t * a + a + j * a + (t + 1 + j) := by ring
  have r3 : (a + 1 + 1) * (t + 1 + j) = t * a + a + j * a + 2 * (t + 1 + j) := by ring
  rcases hstep t ht with h | h
  · left
    rw [h, Nat.add_sub_cancel_left, eq_comm]
    apply Nat.div_eq_of_lt_le <;> omega
  · rcases (by omega : n = t * a + a + j * a + (t + 1 + j) ∨ n < t * a + a + j * a + (t + 1 + j))
      with hn | hn
    · left
      rw [h, show G t + a + 1 - G t = a + 1 by omega, eq_comm]
      apply Nat.div_eq_of_lt_le <;> omega
    · right
      rw [h, show G t + a + 1 - G t = a + 1 by omega, eq_comm]
      apply Nat.div_eq_of_lt_le <;> omega

end Steps

/-! ### The targets of Algorithm 1 -/

/-- The target node of the agent with home `h` in Algorithm 1: after a full circuit (`n` moves,
which bring it back to `h`) it moves `moves1 (distSeq H h)` further. -/
def alg1Target (H : Finset (ZMod n)) (h : ZMod n) : ZMod n :=
  h + (moves1 (distSeq H h) : ZMod n)

section Targets

variable [NeZero n] {H : Finset (ZMod n)} {h : ZMod n}

omit [NeZero n] in
theorem period_distSeq_dvd_card (h : ZMod n) : period (distSeq H h) ∣ H.card := by
  simpa using period_dvd_length (distSeq H h)

omit [NeZero n] in
theorem card_pos_of_mem (hh : h ∈ H) : 0 < H.card := Finset.card_pos.2 ⟨h, hh⟩

omit [NeZero n] in
theorem period_distSeq_le_card (hh : h ∈ H) : period (distSeq H h) ≤ H.card :=
  Nat.le_of_dvd (card_pos_of_mem hh) (period_distSeq_dvd_card h)

theorem step_add_period (hh : h ∈ H) (i : ℕ) :
    homeGap H h (i + period (distSeq H h)) = homeGap H h i := by
  have heq : distSeq H ((next H)^[period (distSeq H h) + i] h) = distSeq H ((next H)^[i] h) := by
    rw [distSeq_iterate_eq_rotate hh, distSeq_iterate_eq_rotate hh, ← List.rotate_rotate,
      (period_spec _).2]
  have := congrArg (fun L : List ℕ => L[0]?) heq
  simp [distSeq_iterate hh, card_pos_of_mem hh] at this
  rwa [add_comm] at this

theorem pos_add_period (hh : h ∈ H) (i : ℕ) :
    pos H h (i + period (distSeq H h)) = pos H h i + pos H h (period (distSeq H h)) := by
  induction i with
  | zero => simp [pos_zero hh]
  | succ i ih =>
    rw [show i + 1 + period (distSeq H h) = i + period (distSeq H h) + 1 by omega, pos_succ hh,
      ih, step_add_period hh, pos_succ hh]
    omega

theorem pos_mul_period (hh : h ∈ H) (q : ℕ) :
    pos H h (q * period (distSeq H h)) = q * pos H h (period (distSeq H h)) := by
  induction q with
  | zero => simp [pos_zero hh]
  | succ q ih => rw [Nat.succ_mul, pos_add_period hh, ih, Nat.succ_mul]

theorem period_le_pos (hh : h ∈ H) : period (distSeq H h) ≤ pos H h (period (distSeq H h)) :=
  (pos_strictMono hh).id_le _

/-- The number of moves of the agent `(next H)^[i] h`, when `h` has the minimum distance
sequence: it walks `x` home nodes ahead (`p ∣ i + x`) and then `offset x N p`. -/
theorem moves1_iterate (hh : h ∈ H) (hmin : IsMinRot (distSeq H h) 0) (i : ℕ) {x : ℕ}
    (hx : x < period (distSeq H h)) (hdvd : period (distSeq H h) ∣ i + x) :
    moves1 (distSeq H ((next H)^[i] h)) = (pos H h (i + x) - pos H h i) +
      offset x (pos H h (period (distSeq H h))) (period (distSeq H h)) := by
  have hp := period_distSeq_le_card hh
  have hrank : rank (distSeq H ((next H)^[i] h)) = x := by
    rw [distSeq_iterate_eq_rotate hh]; exact rank_rotate hmin hx hdvd
  have hper : period (distSeq H ((next H)^[i] h)) = period (distSeq H h) := by
    rw [distSeq_iterate_eq_rotate hh, period_rotate]
  rw [moves1, hrank, hper, sum_take_distSeq_iterate hh i (by omega),
    sum_take_distSeq_iterate hh i hp, pos_add_period hh, Nat.add_sub_cancel_left]

/-- The explicit target positions (relative to a home node with minimum distance sequence). -/
noncomputable def targetPos (H : Finset (ZMod n)) (h : ZMod n) (t : ℕ) : ℕ :=
  t / period (distSeq H h) * pos H h (period (distSeq H h)) +
    offset (t % period (distSeq H h)) (pos H h (period (distSeq H h))) (period (distSeq H h))

omit [NeZero n] in
theorem targetPos_spec (q x : ℕ) (hx : x < period (distSeq H h)) :
    targetPos H h (q * period (distSeq H h) + x) =
      q * pos H h (period (distSeq H h)) +
        offset x (pos H h (period (distSeq H h))) (period (distSeq H h)) := by
  have hp := period_pos (distSeq H h)
  unfold targetPos
  rw [Nat.add_comm (q * _) x, Nat.add_mul_div_right _ _ hp, Nat.add_mul_mod_self_right,
    Nat.div_eq_of_lt hx, Nat.mod_eq_of_lt hx, zero_add]

omit [NeZero n] in
theorem targetPos_succ (t : ℕ) :
    targetPos H h (t + 1) = t / period (distSeq H h) * pos H h (period (distSeq H h)) +
      offset (t % period (distSeq H h) + 1) (pos H h (period (distSeq H h)))
        (period (distSeq H h)) := by
  set p := period (distSeq H h)
  have hp : 0 < p := period_pos _
  have hx : t % p < p := Nat.mod_lt t hp
  have ht : t + 1 = t / p * p + (t % p + 1) := by have := Nat.div_add_mod' t p; omega
  rcases (by omega : t % p + 1 < p ∨ t % p + 1 = p) with h1 | h1
  · rw [ht, targetPos_spec _ _ h1]
  · rw [ht, h1, show t / p * p + p = (t / p + 1) * p + 0 by ring, targetPos_spec _ _ hp,
      offset_zero, offset_period hp, Nat.succ_mul]
    rfl

omit [NeZero n] in
theorem targetPos_zero : targetPos H h 0 = 0 := by simp [targetPos, offset_zero]

theorem targetPos_card (hh : h ∈ H) : targetPos H h H.card = n := by
  obtain ⟨q, hq⟩ := period_distSeq_dvd_card (H := H) h
  have := targetPos_spec (H := H) (h := h) q 0 (period_pos _)
  rw [add_zero, offset_zero, add_zero, ← pos_mul_period hh] at this
  rw [hq, Nat.mul_comm (period _) q, this, Nat.mul_comm q, ← hq, pos_card hh rfl]

omit [NeZero n] in
theorem targetPos_step (t : ℕ) :
    targetPos H h (t + 1) = targetPos H h t + pos H h (period (distSeq H h)) / period (distSeq H h)
      ∨ targetPos H h (t + 1) = targetPos H h t +
        pos H h (period (distSeq H h)) / period (distSeq H h) + 1 := by
  rw [targetPos_succ, offset_succ, targetPos]
  split_ifs <;> omega

theorem targetPos_lt_succ (hh : h ∈ H) (t : ℕ) : targetPos H h t < targetPos H h (t + 1) := by
  have := Nat.div_pos (period_le_pos hh) (period_pos _)
  rcases targetPos_step (H := H) (h := h) t with h1 | h1 <;> omega

/-- The target set (relative to a home node `h` with minimum distance sequence) is a uniform
deployment of `k` distinct nodes. -/
theorem targetSet_uniform (hh : h ∈ H) :
    IsUniformSet n H.card ((Finset.range H.card).image fun t => h + (targetPos H h t : ZMod n)) ∧
      ((Finset.range H.card).image fun t => h + (targetPos H h t : ZMod n)).card = H.card :=
  isUniformSet_of_steps (card_pos_of_mem hh) _ h targetPos_zero (targetPos_card hh)
    (fun t _ => targetPos_lt_succ hh t)
    (steps_floor_ceil targetPos_zero (targetPos_card hh) (fun t _ => targetPos_step t))

/-- Every explicit target position is the target of some agent. -/
theorem targetPos_mem_image (hh : h ∈ H) (hmin : IsMinRot (distSeq H h) 0) (t : ℕ) : h + (targetPos H h t : ZMod n) ∈ H.image (alg1Target H) := by
  set p := period (distSeq H h)
  set k := H.card
  have hp : 0 < p := period_pos _
  have hpk : p ≤ k := period_distSeq_le_card hh
  have hpdvd : p ∣ k := period_distSeq_dvd_card h
  set q := t / p
  set x := t % p
  have hx : x < p := Nat.mod_lt t hp
  set i := (q * p + k - x) % k
  have hmod : i + x ≡ q * p [MOD k] := by
    have h1 : i + x ≡ (q * p + k - x) + x [MOD k] := Nat.ModEq.add_right x (Nat.mod_modEq _ k)
    rw [show q * p + k - x + x = q * p + k by omega] at h1
    exact h1.trans (Nat.add_modEq_right)
  have hdvd : p ∣ i + x := by
    have := Nat.ModEq.of_dvd hpdvd hmod
    exact (Nat.modEq_zero_iff_dvd).1 (this.trans (Nat.modEq_zero_iff_dvd.2 (dvd_mul_left p q)))
  refine Finset.mem_image.2 ⟨(next H)^[i] h, iterate_next_mem hh i, ?_⟩
  rw [alg1Target, moves1_iterate hh hmin i hx hdvd, iterate_next_eq_pos hh]
  have hle : pos H h i ≤ pos H h (i + x) := (pos_strictMono hh).monotone (Nat.le_add_right _ _)
  have hcast : (pos H h (i + x) : ZMod n) = (q * pos H h p : ℕ) := by
    rw [← cast_pos_mod_card hh rfl, hmod, cast_pos_mod_card hh rfl, pos_mul_period hh]
  have e : pos H h i + ((pos H h (i + x) - pos H h i) + offset x (pos H h p) p) =
      pos H h (i + x) + offset x (pos H h p) p := by omega
  rw [add_assoc, ← Nat.cast_add, e, Nat.cast_add, hcast, ← Nat.cast_add]
  rfl

/-- If `h` has the minimum distance sequence, the targets of Algorithm 1 are exactly the nodes
`h + targetPos H h t`, `t < k`. -/
theorem image_alg1Target_eq (hh : h ∈ H) (hmin : IsMinRot (distSeq H h) 0) :
    H.image (alg1Target H) =
      (Finset.range H.card).image fun t => h + (targetPos H h t : ZMod n) := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hv
    exact targetPos_mem_image hh hmin t
  · rw [(targetSet_uniform hh).2]; exact Finset.card_image_le

/-- There is a home node whose distance sequence is its own minimum rotation (a base node). -/
theorem exists_base (hH : H.Nonempty) : ∃ h ∈ H, IsMinRot (distSeq H h) 0 := by
  obtain ⟨h₀, h₀H⟩ := hH
  refine ⟨(next H)^[rank (distSeq H h₀)] h₀, iterate_next_mem h₀H _, ?_⟩
  rw [distSeq_iterate_eq_rotate h₀H, isMinRot_iff]
  intro z
  rw [List.rotate_zero, List.rotate_rotate]
  exact (isMinRot_iff _ _).1 (rank_spec _) _

/-- **Algorithm 1, correctness of the targets (Section 3.1, 3.1.1).** Different agents choose
different target nodes. -/
theorem alg1_targets_injOn (hH : H.Nonempty) : Set.InjOn (alg1Target H) H := by
  obtain ⟨h, hh, hmin⟩ := exists_base hH
  have := (targetSet_uniform hh).2
  rw [← image_alg1Target_eq hh hmin] at this
  exact Finset.injOn_of_card_image_eq this

/-- **Algorithm 1, correctness of the targets (Section 3.1, 3.1.1).** The target nodes of the `k`
agents form a uniform deployment. -/
theorem alg1_targets_uniform (hH : H.Nonempty) (hk : H.card = k) :
    IsUniformSet n k (H.image (alg1Target H)) := by
  obtain ⟨h, hh, hmin⟩ := exists_base hH
  rw [image_alg1Target_eq hh hmin, ← hk]
  exact (targetSet_uniform hh).1

/-- **Algorithm 1 (Section 3.1, 3.1.1).** For `k = |H| ≥ 1` home nodes, the map from homes to
target nodes is injective and its image is a uniform deployment. -/
theorem alg1_targets (hH : H.Nonempty) (hk : H.card = k) :
    Set.InjOn (alg1Target H) H ∧ IsUniformSet n k (H.image (alg1Target H)) :=
  ⟨alg1_targets_injOn hH, alg1_targets_uniform hH hk⟩

/-- The deployment phase of Algorithm 1 takes fewer than `2n` moves (Section 3.1: in total each
agent moves fewer than `3n` times). -/
theorem moves1_lt (hh : h ∈ H) : moves1 (distSeq H h) < 2 * n := by
  set D := distSeq H h
  have hp : 0 < period D := period_pos D
  have hpk : period D ≤ H.card := period_distSeq_le_card hh
  have hx : rank D < period D := rank_lt_period D
  have h1 : (D.take (rank D)).sum = pos H h (rank D) := by
    simpa [pos_zero hh] using sum_take_distSeq_iterate hh 0 (m := rank D) (by omega)
  have h2 : (D.take (period D)).sum = pos H h (period D) := by
    simpa [pos_zero hh] using sum_take_distSeq_iterate hh 0 (m := period D) hpk
  have h3 : pos H h (rank D) < pos H h (period D) := pos_strictMono hh hx
  have h4 : pos H h (period D) ≤ n := by
    have := (pos_strictMono hh).monotone hpk
    rwa [pos_card hh rfl] at this
  have h5 : offset (rank D) (pos H h (period D)) (period D) < pos H h (period D) :=
    offset_lt hx (period_le_pos hh)
  rw [moves1, h1, h2]
  omega

end Targets

end Podc.UniformDeploymentRings
