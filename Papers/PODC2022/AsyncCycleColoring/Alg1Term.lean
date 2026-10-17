import Papers.PODC2022.AsyncCycleColoring.Alg1
import Papers.PODC2022.AsyncCycleColoring.Activations

/-!
# Algorithm 1: basic dynamics and the bound for non-extremal processes (Lemma 3.9)

Throughout, `X : ZMod n → ι` is a proper colouring of the cycle (`X p ≠ X (p + 1)`).

**Proof idea (cleaner than the paper's).** A failed round changes the colour `(a_p, b_p)` of `p`
(Lemma 3.2), so the number of failed rounds is at most the number of changes of `a_p` plus the
number of changes of `b_p`. The value `a_p` only depends on the registers of the *larger*
neighbours. For a process `p` with exactly one larger neighbour `q`, `a_p` follows
`min ℕ ∖ {â_q}`, whose number of changes is at most one more than the number of changes of `a_q`
(the extra change is `⊥ ↦ 0`); for a local maximum `a ≡ 0`. Hence `a_p` changes at most `ℓ`
times, `ℓ` the monotone distance from `p` to the local maximum above it (`upDist`), and
symmetrically `b_p` changes at most `ℓ'` times. So a non-extremal process returns after at most
`ℓ + ℓ' + 1` activations (`lemma_3_9`), which is at most `n`.
-/

namespace AsyncCycle

variable {ι : Type*} [LinearOrder ι] {n : ℕ}

section Dynamics

variable (X : ZMod n → ι) (σ : ℕ → Finset (ZMod n))

local notation "R" => run (alg1 ι) (init1 X) σ

/-- The identifier stored in the local state never changes. -/
lemma alg1_loc_X (t : ℕ) (p : ZMod n) : ((R t).loc p).X = X p := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [loc_succ]
    split_ifs with h
    · rcases hr : resAt (alg1 ι) (init1 X) σ t p with s | o
      · simp only [Sum.elim_inl, id]
        simp only [resAt, alg1, alg1Step] at hr
        split_ifs at hr
        cases hr; exact ih
      · exact ih
    · exact ih

/-- Registers hold the owner's identifier. -/
lemma alg1_reg_X (t : ℕ) (p : ZMod n) (x : St1 ι) (h : (R t).reg p = some x) : x.X = X p := by
  induction t with
  | zero => simp at h
  | succ t ih =>
    rw [reg_succ] at h
    split_ifs at h
    · cases h; exact alg1_loc_X X σ t p
    · exact ih h

/-- What a failing activation computes. -/
lemma alg1_fail_eq {t : ℕ} {p : ZMod n} {s : St1 ι}
    (hs : resAt (alg1 ι) (init1 X) σ t p = Sum.inl s) :
    ((R t).loc p).col ∈ (awake ((R (t + 1)).reg (p - 1)) ((R (t + 1)).reg (p + 1))).map St1.col ∧
      s = ⟨X p, upA (X p) ((R (t + 1)).reg (p - 1)) ((R (t + 1)).reg (p + 1)),
        downB (X p) ((R (t + 1)).reg (p - 1)) ((R (t + 1)).reg (p + 1))⟩ := by
  have hX := alg1_loc_X X σ t p
  change alg1Step ((R t).loc p) ((R (t + 1)).reg (p - 1)) ((R (t + 1)).reg (p + 1)) = _ at hs
  unfold alg1Step at hs
  split_ifs at hs with h
  cases hs
  exact ⟨h, by rw [hX]⟩

lemma mem_awake_left {α : Type*} {l r : Option α} {x : α} (h : l = some x) : x ∈ awake l r := by
  subst h; simp [awake]

lemma mem_awake_right {α : Type*} {l r : Option α} {x : α} (h : r = some x) :
    x ∈ awake l r := by
  subst h; cases l <;> simp [awake]

lemma mem_awake {α : Type*} {l r : Option α} {x : α} : x ∈ awake l r ↔ l = some x ∨ r = some x := by
  cases l <;> cases r <;> simp [awake, eq_comm]

lemma upA_ne {x : ι} {l r : Option (St1 ι)} {u : St1 ι} (hu : u ∈ awake l r) (hx : x < u.X) :
    upA x l r ≠ u.a :=
  mex_ne_of_mem (List.mem_map.2 ⟨u, List.mem_filter.2 ⟨hu, by simpa using hx⟩, rfl⟩)

lemma downB_ne {x : ι} {l r : Option (St1 ι)} {u : St1 ι} (hu : u ∈ awake l r) (hx : u.X < x) :
    downB x l r ≠ u.b :=
  mex_ne_of_mem (List.mem_map.2 ⟨u, List.mem_filter.2 ⟨hu, by simpa using hx⟩, rfl⟩)

/-- Lemma 3.2 (first half): after a failed round, the new colour differs from the colours in the
registers of both neighbours. -/
lemma lemma_3_2 (hX : ∀ p, X p ≠ X (p + 1)) {t : ℕ} {p : ZMod n} {s : St1 ι}
    (hs : resAt (alg1 ι) (init1 X) σ t p = Sum.inl s) {u : St1 ι}
    (hu : u ∈ awake ((R (t + 1)).reg (p - 1)) ((R (t + 1)).reg (p + 1))) : s.col ≠ u.col := by
  obtain ⟨-, rfl⟩ := alg1_fail_eq X σ hs
  have huX : u.X ≠ X p := by
    rcases mem_awake.1 hu with h | h
    · rw [alg1_reg_X X σ _ _ _ h]
      have := hX (p - 1); rw [sub_add_cancel] at this; exact this
    · rw [alg1_reg_X X σ _ _ _ h]; exact (hX p).symm
  intro hc
  simp only [St1.col, Prod.mk.injEq] at hc
  rcases lt_or_gt_of_ne huX with h | h
  · exact downB_ne hu h hc.2
  · exact upA_ne hu h hc.1

/-- Lemma 3.2 (second half): a failed round changes the colour. -/
lemma col_change_of_fails (hX : ∀ p, X p ≠ X (p + 1)) {t : ℕ} {p : ZMod n}
    (h : FailsAt (alg1 ι) (init1 X) σ t p) :
    ((R (t + 1)).loc p).col ≠ ((R t).loc p).col := by
  obtain ⟨ha, s, hs⟩ := h
  rw [loc_succ_of_inl _ _ _ ha hs]
  obtain ⟨hmem, -⟩ := alg1_fail_eq X σ hs
  obtain ⟨u, hu, hcol⟩ := List.mem_map.1 hmem
  rw [← hcol]
  exact lemma_3_2 X σ hX hs hu

open Classical in
/-- The number of failed rounds is at most the number of changes of `a` plus that of `b`. -/
lemma fails_le_chg (hX : ∀ p, X p ≠ X (p + 1)) (p : ZMod n) (T : ℕ) :
    ((Finset.range T).filter (fun t => FailsAt (alg1 ι) (init1 X) σ t p)).card ≤
      chg (fun t => ((R t).loc p).a) T + chg (fun t => ((R t).loc p).b) T := by
  refine le_trans ?_ (chg_pair_le _ _ T)
  unfold chg
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter] at ht ⊢
  refine ⟨ht.1, ?_⟩
  have := col_change_of_fails X σ hX ht.2
  simpa [St1.col] using this

/-! ### The `a`-component -/

/-- The value of `a` a process would compute from the registers at time `t`. -/
def gA (t : ℕ) (p : ZMod n) : ℕ := upA (X p) ((R t).reg (p - 1)) ((R t).reg (p + 1))

lemma a_follow (t : ℕ) (p : ZMod n) :
    ((R (t + 1)).loc p).a = ((R t).loc p).a ∨ ((R (t + 1)).loc p).a = gA X σ (t + 1) p := by
  by_cases ha : ActsAt (alg1 ι) (init1 X) σ t p
  · rcases hr : resAt (alg1 ι) (init1 X) σ t p with s | o
    · right
      rw [loc_succ_of_inl _ _ _ ha hr, (alg1_fail_eq X σ hr).2]; rfl
    · left; rw [loc_succ_of_inr _ _ _ ha hr]
  · left; rw [loc_succ_of_not_acts _ _ _ ha]

lemma gA_zero (p : ZMod n) : gA X σ 0 p = 0 := by
  simp [gA, upA, awake]

lemma chg_a_le_chg_gA (p : ZMod n) (T : ℕ) :
    chg (fun t => ((R t).loc p).a) T ≤ chg (fun t => gA X σ t p) T :=
  chg_follow (by simp [init1, gA_zero]) (fun t => a_follow X σ t p) T

/-- At a local maximum, `a ≡ 0`. -/
lemma gA_of_max {p : ZMod n} (h1 : X (p - 1) < X p) (h2 : X (p + 1) < X p) (t : ℕ) :
    gA X σ t p = 0 := by
  unfold gA upA
  rw [List.filter_eq_nil_iff.2, List.map_nil, mex_nil]
  intro u hu
  rcases mem_awake.1 hu with h | h <;> rw [alg1_reg_X X σ _ _ _ h] <;> simpa using le_of_lt (by
    first | exact h1 | exact h2)

lemma a_of_max {p : ZMod n} (h1 : X (p - 1) < X p) (h2 : X (p + 1) < X p) (t : ℕ) :
    ((R t).loc p).a = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rcases a_follow X σ t p with h | h
    · rw [h, ih]
    · rw [h, gA_of_max X σ h1 h2]

/-- For a process with exactly one larger neighbour `q`, `gA` is `min ℕ ∖ {â_q}`. -/
lemma gA_of_one_up {p q q' : ZMod n} (hq : (q = p - 1 ∧ q' = p + 1) ∨ (q = p + 1 ∧ q' = p - 1))
    (hpq : X p < X q) (hq' : X q' < X p) (t : ℕ) :
    gA X σ t p = mex ((((R t).reg q).map St1.a).toList) := by
  unfold gA upA
  congr 1
  have hreg : ∀ x, (R t).reg q' = some x → ¬ X p < x.X := fun x h => by
    rw [alg1_reg_X X σ _ _ _ h]; exact not_lt.2 hq'.le
  have hreg' : ∀ x, (R t).reg q = some x → X p < x.X := fun x h => by
    rw [alg1_reg_X X σ _ _ _ h]; exact hpq
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases h1 : (R t).reg (p - 1) <;> cases h2 : (R t).reg (p + 1) <;>
      simp_all [awake]
  · cases h1 : (R t).reg (p - 1) <;> cases h2 : (R t).reg (p + 1) <;>
      simp_all [awake]

/-- `â_q` lags behind `a_q`: the register shows the previous local value. -/
lemma regA_lag (q : ZMod n) (t : ℕ) :
    mex ((((R (t + 1)).reg q).map St1.a).toList) = mex ((((R t).reg q).map St1.a).toList) ∨
      mex ((((R (t + 1)).reg q).map St1.a).toList) = mex [((R t).loc q).a] := by
  rw [reg_succ]
  split_ifs
  · right; rfl
  · left; rfl

lemma chg_a_step {p q q' : ZMod n} (hq : (q = p - 1 ∧ q' = p + 1) ∨ (q = p + 1 ∧ q' = p - 1))
    (hpq : X p < X q) (hq' : X q' < X p) (T : ℕ) :
    chg (fun t => ((R t).loc p).a) T ≤ 1 + chg (fun t => ((R t).loc q).a) T := by
  refine (chg_a_le_chg_gA X σ p T).trans ?_
  rw [show (fun t => gA X σ t p) = fun t => mex ((((R t).reg q).map St1.a).toList) from
    funext fun t => gA_of_one_up X σ hq hpq hq' t]
  refine (chg_lag (h := fun t => mex [((R t).loc q).a]) (fun t => regA_lag X σ q t) T).trans ?_
  have := chg_comp_le (fun k => mex [k]) (fun t => ((R t).loc q).a) T
  omega

end Dynamics

/-! ### Monotone distances -/

section Dist

lemma card_up_lt [NeZero n] (X : ZMod n → ι) {p q : ZMod n} (h : X p < X q) :
    (Finset.univ.filter (fun u => X q < X u)).card <
      (Finset.univ.filter (fun u => X p < X u)).card := by
  apply Finset.card_lt_card
  refine ⟨fun u hu => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢; exact h.trans hu
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ q, h⟩)
    simp at this

/-- The monotone distance `ℓ` from `p` to the local maximum reached by following increasing
identifiers (`0` if `p` is a local maximum or a local minimum). -/
def upDist [NeZero n] (X : ZMod n → ι) (p : ZMod n) : ℕ :=
  if h : X p < X (p + 1) ∧ X (p - 1) < X p then upDist X (p + 1) + 1
  else if h' : X p < X (p - 1) ∧ X (p + 1) < X p then upDist X (p - 1) + 1
  else 0
termination_by (Finset.univ.filter (fun u => X p < X u)).card
decreasing_by
  · exact card_up_lt X h.1
  · exact card_up_lt X h'.1

/-- The monotone distance `ℓ'` from `p` to the local minimum reached by following decreasing
identifiers. -/
def downDist [NeZero n] (X : ZMod n → ι) (p : ZMod n) : ℕ := upDist (fun q => OrderDual.toDual (X q)) p

lemma upDist_le_card [NeZero n] (X : ZMod n → ι) (p : ZMod n) :
    upDist X p ≤ (Finset.univ.filter (fun u => X p < X u)).card := by
  induction h : (Finset.univ.filter (fun u => X p < X u)).card using Nat.strong_induction_on
    generalizing p with
  | _ m ih =>
    rw [upDist]
    split_ifs with h1 h2
    · have := card_up_lt X h1.1
      have := ih _ (h ▸ this) (p + 1) rfl
      omega
    · have := card_up_lt X h2.1
      have := ih _ (h ▸ this) (p - 1) rfl
      omega
    · exact Nat.zero_le _

end Dist

end AsyncCycle
