import Papers.PODC2022.AsyncCycleColoring.Alg3

/-!
# Algorithm 3: the evolving identifiers stay a proper colouring (Lemma 4.5)

In Algorithm 3 every process `p` keeps reducing its identifier `X_p` à la Cole–Vishkin. Lemma 4.5 of
the paper states that the identifiers written in neighbouring registers always differ. The paper
proves the stronger claim `X_p(t) ∉ {X_q(t), X̂_q(t)}` for neighbours `p, q` (here `X̂_q` is the
value in the register `R_q`) by a case analysis on who moves at time `T + 1`; the case where a
neighbour's register is stale is handled through the counters `r`.

We prove (for every cycle length, every schedule and every proper input colouring):

* `alg3_X_proper`: `X_p(t) ≠ X_{p+1}(t)`;
* `alg3_X_ne_reg`: `X_p(t) ≠ X̂_q(t)` for both neighbours `q` of `p`;
* `lemma_4_5`: `X̂_p(t) ≠ X̂_{p+1}(t)` (Lemma 4.5).

## The invariant

Call a step of `p` *changing* if it changes `X_p`. A changing step of `p` from `x` to `x'`, having
read the values `a`, `b` in its neighbours' registers, is of one of two kinds (`StepChange`):

* (M, line 15) `min a b < x < max a b` and `x' = f(x, min a b) < min a b`;
* (L, line 19) `x < a, b` and `x' = mex {f(a, x), f(b, x)} < x`.

In both cases `x'` is below both values read. Besides the three claims above, the invariant
`Alg3Proper.Inv` contains:

* (`reg_r`) the register of `p` holds an earlier state of `p`: `r̂_p ≤ r_p`, and `r̂_p = r_p`
  implies `X̂_p = X_p` (`X` changes only together with `r`, and `r` only increases);
* (`last`) if the last step of `q` was changing (`X_q ≠ X̂_q`) then, for each neighbour `p` of `q`,
  `R_p ≠ ⊥`, `r̂_q ≤ r̂_p` (the gate of line 11), and, **if `r̂_q = r_p`, then that step was a
  changing step from `X̂_q` in which `q` read the current value `X_p` in `R_p`.**

The key step: when `p` makes a changing step at counter `k` and reads `X̂_q`, the gate gives
`k ≤ r̂_q`; if the last step of `q` was changing then `r̂_q ≤ r̂_p ≤ r_p = k` by `last` and `reg_r`,
so `r̂_q = k` and `q` computed its current `X_q` from `X̂_q` while seeing exactly `X_p`. A short case
analysis (`StepChange.ne`) using Lemma 4.3 (`f(x, y) ≠ f(y, z)` for `x > y > z`) then shows that
the new values of `p` and `q` differ. Simultaneous moves of `p` and `q` are the special case where
each reads the other's current state.

The proof does not need `n ≥ 3`, nor the termination part of the algorithm (lines 6–10).
-/

namespace AsyncCycle

namespace Alg3Proper

/-! ### Lemma 4.3 (Cole–Vishkin property of `f`) -/

lemma lowDiff_spec (x y : ℕ) : ∀ m, lowDiff x y m ≤ m ∧
    (∀ k < lowDiff x y m, x.testBit k = y.testBit k) ∧
    (lowDiff x y m < m → x.testBit (lowDiff x y m) ≠ y.testBit (lowDiff x y m)) := by
  intro m
  induction m with
  | zero => simp [lowDiff]
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [lowDiff]
    split_ifs with hl hb
    · exact ⟨by omega, h2, fun _ => h3 hl⟩
    · have hm : lowDiff x y m = m := by omega
      rw [hm] at h2
      exact ⟨by omega, h2, fun _ => hb⟩
    · have hm : lowDiff x y m = m := by omega
      rw [hm] at h2
      refine ⟨le_rfl, fun k hk => ?_, fun h => absurd h (lt_irrefl _)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h2 k hk
      · exact not_not.1 hb

lemma toNat_inj_aux : ∀ (b c : Bool) (i j : ℕ), 2 * i + b.toNat = 2 * j + c.toNat → i = j ∧ b = c := by
  intro b c i j h
  cases b <;> cases c <;> simp at h ⊢ <;> omega

/-- Lemma 4.3 of the paper: if `x > y > z` then `f(x, y) ≠ f(y, z)`. (Local copy.) -/
lemma cvF_ne_aux {x y z : ℕ} (hxy : y < x) (hyz : z < y) : cvF x y ≠ cvF y z := by
  intro h
  have hsxy : y.size ≤ x.size := Nat.size_le_size hxy.le
  have hszy : z.size ≤ y.size := Nat.size_le_size hyz.le
  have ei : cvIdx x y = lowDiff x y y.size := by
    rw [cvIdx, min_eq_right hsxy]
  have ej : cvIdx y z = lowDiff y z z.size := by
    rw [cvIdx, min_eq_right hszy]
  unfold cvF at h
  rw [ei, ej] at h
  obtain ⟨hij, hb⟩ := toNat_inj_aux _ _ _ _ h
  obtain ⟨hi1, -, hi3⟩ := lowDiff_spec x y y.size
  obtain ⟨hj1, hj2, -⟩ := lowDiff_spec y z z.size
  have hi : lowDiff x y y.size = y.size := by
    have : ¬ lowDiff x y y.size < y.size := fun hlt => hi3 hlt (by rw [hb, hij])
    omega
  have hzs : z.size = y.size := by omega
  have hyz' : y = z := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < y.size
    · exact hj2 k (by omega)
    · rw [Nat.testBit_eq_false_of_lt (Nat.size_le.1 (by omega)),
        Nat.testBit_eq_false_of_lt (Nat.size_le.1 (by omega))]
  omega

/-! ### Changing steps -/

/-- A step changing the identifier from `x` to `x'` after reading `a` and `b` in the neighbours'
registers: either line 15 (`p` in the middle) or line 19 (`p` a local minimum). -/
def StepChange (x a b x' : ℕ) : Prop :=
  (min a b < x ∧ x < max a b ∧ x' = cvF x (min a b) ∧ x' < min a b) ∨
  (x < a ∧ x < b ∧ x' = mex [cvF a x, cvF b x] ∧ x' < x)

lemma StepChange.symm {x a b x' : ℕ} (h : StepChange x a b x') : StepChange x b a x' := by
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left; rw [min_comm, max_comm]; exact ⟨h1, h2, h3, h4⟩
  · right
    refine ⟨h2, h1, h3.trans (mex_congr fun k => ?_), h4⟩
    simp [or_comm]

/-- The new value is below the values read. -/
lemma StepChange.lt_left {x a b x' : ℕ} (h : StepChange x a b x') : x' < a := by
  rcases h with ⟨-, -, -, h4⟩ | ⟨h1, -, -, h4⟩
  · exact lt_of_lt_of_le h4 (min_le_left _ _)
  · omega

/-- The core of the proof of Lemma 4.5: `p` changes `x ↦ x'` after reading `a` from `q`; `q`'s
current value `x''` either equals `a`, or was obtained from `a` by a changing step in which `q`
read `x`. Then `x' ≠ x''` (by Lemma 4.3). -/
lemma StepChange.ne {x a b x' x'' : ℕ} (hx : StepChange x a b x')
    (hq : x'' = a ∨ ∃ w, StepChange a x w x'') : x' ≠ x'' := by
  rcases hq with rfl | ⟨w, hw⟩
  · exact hx.lt_left.ne
  rcases hx with ⟨h1, h2, rfl, -⟩ | ⟨h1, h2, rfl, -⟩ <;>
    rcases hw with ⟨k1, k2, rfl, -⟩ | ⟨k1, k2, rfl, -⟩
  · -- both in the middle
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab] at h1 ⊢
      rw [max_eq_right hab] at h2
      rcases le_total x w with hxw | hxw
      · rw [min_eq_left hxw] at k1; omega
      · rw [min_eq_right hxw] at k1 ⊢
        exact cvF_ne_aux h1 k1
    · rw [min_eq_right hab] at h1 ⊢
      rw [max_eq_left hab] at h2
      rcases le_total x w with hxw | hxw
      · rw [min_eq_left hxw] at k1 ⊢
        exact (cvF_ne_aux h2 h1).symm
      · rw [max_eq_left hxw] at k2; omega
  · -- `p` in the middle, `q` a local minimum
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab]
      exact (mex_ne_of_mem (by simp)).symm
    · rw [max_eq_left hab] at h2; omega
  · -- `p` a local minimum, `q` in the middle
    rcases le_total x w with hxw | hxw
    · rw [min_eq_left hxw]
      exact mex_ne_of_mem (by simp)
    · rw [max_eq_left hxw] at k2; omega
  · omega

/-! ### Lines 11–19 -/

lemma alg3XR_mono (X : ℕ) (r : WithTop ℕ) (l r' : Option St3) :
    r ≤ (alg3XR X r l r').2 ∧ ((alg3XR X r l r').2 = r → (alg3XR X r l r').1 = X) := by
  unfold alg3XR
  rcases l with _ | u <;> rcases r' with _ | v
  · simp
  · simp
  · simp
  · simp only
    split_ifs with h1 <;> dsimp only <;>
      first
      | exact ⟨le_rfl, fun _ => rfl⟩
      | exact ⟨le_top, fun h => absurd h.symm h1.1.ne⟩
      | (obtain ⟨k, rfl⟩ := WithTop.ne_top_iff_exists.1 h1.1.ne
         have hk : ((k : WithTop ℕ)) < k + 1 := by exact_mod_cast Nat.lt_succ_self k
         exact ⟨hk.le, fun h => absurd h hk.ne'⟩)

lemma alg3XR_change (X : ℕ) (r : WithTop ℕ) (l r' : Option St3)
    (h : (alg3XR X r l r').1 ≠ X) :
    ∃ u v, l = some u ∧ r' = some v ∧ r ≤ u.r ∧ r ≤ v.r ∧
      StepChange X u.X v.X (alg3XR X r l r').1 := by
  unfold alg3XR at h ⊢
  rcases l with _ | u <;> rcases r' with _ | v
  · simp at h
  · simp at h
  · simp at h
  · simp only at h ⊢
    refine ⟨u, v, rfl, rfl, ?_⟩
    split_ifs at h ⊢ with h1 h2 h3 h4
    · exact ⟨h1.2.1, h1.2.2, Or.inl ⟨h2.1, h2.2, rfl, h3⟩⟩
    · exact absurd rfl h
    · have hm : mex [cvF u.X X, cvF v.X X] < X := by
        by_contra hc; exact h (min_eq_left (not_lt.1 hc))
      refine ⟨h1.2.1, h1.2.2, Or.inr ⟨(lt_min_iff.1 h4).1, (lt_min_iff.1 h4).2, ?_, ?_⟩⟩
      · exact min_eq_right hm.le
      · rw [min_eq_right hm.le]; exact hm
    · exact absurd rfl h
    · exact absurd rfl h

lemma alg3Step_inl {s : St3} {l r : Option St3} {s' : St3} (h : alg3Step s l r = Sum.inl s') :
    s'.X = (alg3XR s.X s.r l r).1 ∧ s'.r = (alg3XR s.X s.r l r).2 := by
  simp only [alg3Step] at h
  split_ifs at h
  cases h
  exact ⟨rfl, rfl⟩

/-! ### The invariant, on abstract configurations -/

/-- Neighbourhood in the cycle. -/
def Adj {n : ℕ} (p q : ZMod n) : Prop := q = p + 1 ∨ q = p - 1

lemma Adj.symm {n : ℕ} {p q : ZMod n} (h : Adj p q) : Adj q p := by
  rcases h with rfl | rfl
  · right; simp
  · left; simp

variable {n : ℕ}

/-- What one time step does, as far as identifiers and counters are concerned. -/
structure StepFacts (c c' : Config n St3 ℕ) : Prop where
  /-- Counters only increase, and `X` changes only together with `r`. -/
  mono : ∀ p, (c.loc p).r ≤ (c'.loc p).r ∧
    ((c'.loc p).r = (c.loc p).r → (c'.loc p).X = (c.loc p).X)
  /-- A changing step passed the gate of line 11 and is described by `StepChange`. -/
  change : ∀ p q, Adj p q → (c'.loc p).X ≠ (c.loc p).X →
    ∃ u, c'.reg q = some u ∧ (c.loc p).r ≤ u.r ∧ ∃ b, StepChange (c.loc p).X u.X b (c'.loc p).X
  /-- A process either writes its old state, or neither its register nor its state changes. -/
  regs : ∀ p, c'.reg p = some (c.loc p) ∨ (c'.reg p = c.reg p ∧ c'.loc p = c.loc p)

/-- The inductive invariant behind Lemma 4.5 (see the module docstring). -/
structure Inv (c : Config n St3 ℕ) : Prop where
  reg_r : ∀ p x, c.reg p = some x → x.r ≤ (c.loc p).r ∧ (x.r = (c.loc p).r → x.X = (c.loc p).X)
  locX : ∀ p q, Adj p q → (c.loc p).X ≠ (c.loc q).X
  locReg : ∀ p q x, Adj p q → c.reg q = some x → (c.loc p).X ≠ x.X
  regReg : ∀ p q x y, Adj p q → c.reg p = some x → c.reg q = some y → x.X ≠ y.X
  last : ∀ q p x, Adj q p → c.reg q = some x → x.X ≠ (c.loc q).X →
    ∃ y, c.reg p = some y ∧ x.r ≤ y.r ∧
      (x.r = (c.loc p).r → ∃ w, StepChange x.X (c.loc p).X w (c.loc q).X)

section Preservation

variable {c c' : Config n St3 ℕ} (hI : Inv c) (hS : StepFacts c c')
include hI hS

lemma Inv.reg_r' : ∀ p x, c'.reg p = some x →
    x.r ≤ (c'.loc p).r ∧ (x.r = (c'.loc p).r → x.X = (c'.loc p).X) := by
  intro p x hx
  rcases hS.regs p with h | ⟨h1, h2⟩
  · rw [h] at hx; obtain rfl := Option.some.inj hx
    exact ⟨(hS.mono p).1, fun h => ((hS.mono p).2 h.symm).symm⟩
  · rw [h1] at hx; rw [h2]; exact hI.reg_r p x hx

/-- The key step: a changing step of `p` avoids the new value of each neighbour. -/
lemma Inv.key {p q : ZMod n} (hpq : Adj p q) (hp : (c'.loc p).X ≠ (c.loc p).X) :
    (c'.loc p).X ≠ (c'.loc q).X := by
  obtain ⟨u, hu, hru, b, hb⟩ := hS.change p q hpq hp
  apply hb.ne
  by_cases hqu : (c'.loc q).X = u.X
  · exact Or.inl hqu
  right
  rcases hS.regs q with h | ⟨h1, h2⟩
  · -- `q` acted now (simultaneous step): it read the state `p` just wrote
    rw [h] at hu; obtain rfl := Option.some.inj hu
    obtain ⟨u', hu', -, w, hw⟩ := hS.change q p hpq.symm hqu
    have hp' : c'.reg p = some (c.loc p) := by
      rcases hS.regs p with h' | ⟨-, h'⟩
      · exact h'
      · exact absurd (congrArg St3.X h') hp
    rw [hp'] at hu'; obtain rfl := Option.some.inj hu'
    exact ⟨w, hw⟩
  · -- `q` did not act: its last step was changing; the counters force `r̂_q = r_p`
    rw [h1] at hu; rw [h2] at hqu ⊢
    obtain ⟨y, hy, hxy, hst⟩ := hI.last q p u hpq.symm hu (Ne.symm hqu)
    exact hst (le_antisymm (hxy.trans (hI.reg_r p y hy).1) hru)

lemma Inv.step : Inv c' where
  reg_r := hI.reg_r' hS
  locX := by
    intro p q hpq
    by_cases hp : (c'.loc p).X = (c.loc p).X
    · by_cases hq : (c'.loc q).X = (c.loc q).X
      · rw [hp, hq]; exact hI.locX p q hpq
      · exact (hI.key hS hpq.symm hq).symm
    · exact hI.key hS hpq hp
  locReg := by
    intro p q x hpq hx
    by_cases hp : (c'.loc p).X = (c.loc p).X
    · rw [hp]
      rcases hS.regs q with h | ⟨h1, -⟩
      · rw [h] at hx; obtain rfl := Option.some.inj hx; exact hI.locX p q hpq
      · rw [h1] at hx; exact hI.locReg p q x hpq hx
    · obtain ⟨u, hu, -, b, hb⟩ := hS.change p q hpq hp
      rw [hu] at hx; obtain rfl := Option.some.inj hx
      exact hb.lt_left.ne
  regReg := by
    intro p q x y hpq hx hy
    rcases hS.regs p with h | ⟨h1, -⟩ <;> rcases hS.regs q with h' | ⟨h1', -⟩
    · rw [h] at hx; rw [h'] at hy
      obtain rfl := Option.some.inj hx; obtain rfl := Option.some.inj hy
      exact hI.locX p q hpq
    · rw [h] at hx; rw [h1'] at hy
      obtain rfl := Option.some.inj hx
      exact hI.locReg p q y hpq hy
    · rw [h1] at hx; rw [h'] at hy
      obtain rfl := Option.some.inj hy
      exact (hI.locReg q p x hpq.symm hx).symm
    · rw [h1] at hx; rw [h1'] at hy
      exact hI.regReg p q x y hpq hx hy
  last := by
    intro q p x hqp hx hne
    rcases hS.regs q with h | ⟨h1, h2⟩
    · rw [h] at hx; obtain rfl := Option.some.inj hx
      obtain ⟨y, hy, hry, w, hw⟩ := hS.change q p hqp (Ne.symm hne)
      refine ⟨y, hy, hry, fun heq => ⟨w, ?_⟩⟩
      have hy' := hI.reg_r' hS p y hy
      have hyX : y.X = (c'.loc p).X :=
        hy'.2 (le_antisymm hy'.1 (by rw [← heq]; exact hry))
      rwa [← hyX]
    · rw [h1] at hx; rw [h2] at hne ⊢
      obtain ⟨y, hy, hxy, hst⟩ := hI.last q p x hqp hx hne
      have hyr := (hI.reg_r p y hy).1
      rcases hS.regs p with hp | ⟨hp1, hp2⟩
      · refine ⟨c.loc p, hp, hxy.trans hyr, fun heq => ?_⟩
        have hm := hS.mono p
        have hr : (c'.loc p).r = (c.loc p).r :=
          le_antisymm (heq ▸ hxy.trans hyr) hm.1
        rw [hm.2 hr]
        exact hst (heq.trans hr)
      · exact ⟨y, hp1 ▸ hy, hxy, by rw [hp2]; exact hst⟩

end Preservation

/-! ### Executions of Algorithm 3 -/

variable (X : ZMod n → ℕ) (σ : ℕ → Finset (ZMod n))

lemma loc_cases (t : ℕ) (p : ZMod n) :
    (run alg3 (init3 X) σ (t + 1)).loc p = (run alg3 (init3 X) σ t).loc p ∨
    ∃ s', alg3Step ((run alg3 (init3 X) σ t).loc p) ((run alg3 (init3 X) σ (t + 1)).reg (p - 1))
      ((run alg3 (init3 X) σ (t + 1)).reg (p + 1)) = Sum.inl s' ∧
      (run alg3 (init3 X) σ (t + 1)).loc p = s' := by
  by_cases hp : ActsAt alg3 (init3 X) σ t p
  · rcases hr : resAt alg3 (init3 X) σ t p with s | o
    · exact Or.inr ⟨s, hr, loc_succ_of_inl _ _ _ hp hr⟩
    · exact Or.inl (loc_succ_of_inr _ _ _ hp hr)
  · exact Or.inl (loc_succ_of_not_acts _ _ _ hp)

lemma stepFacts (t : ℕ) : StepFacts (run alg3 (init3 X) σ t) (run alg3 (init3 X) σ (t + 1)) where
  mono := by
    intro p
    rcases loc_cases X σ t p with h | ⟨s', hs, h⟩
    · rw [h]; exact ⟨le_rfl, fun _ => rfl⟩
    · rw [h]
      obtain ⟨hX, hr⟩ := alg3Step_inl hs
      rw [hX, hr]
      exact alg3XR_mono _ _ _ _
  change := by
    intro p q hpq hne
    rcases loc_cases X σ t p with h | ⟨s', hs, h⟩
    · exact absurd (congrArg St3.X h) hne
    · rw [h] at hne ⊢
      obtain ⟨hX, -⟩ := alg3Step_inl hs
      rw [hX] at hne ⊢
      obtain ⟨u, v, hu, hv, hru, hrv, hst⟩ := alg3XR_change _ _ _ _ hne
      rcases hpq with rfl | rfl
      · exact ⟨v, hv, hrv, u.X, hst.symm⟩
      · exact ⟨u, hu, hru, v.X, hst⟩
  regs := by
    intro p
    by_cases hp : ActsAt alg3 (init3 X) σ t p
    · exact Or.inl (reg_succ_of_acts _ _ _ hp)
    · exact Or.inr ⟨reg_succ_of_not_acts _ _ _ hp, loc_succ_of_not_acts _ _ _ hp⟩

lemma inv_zero (hX : ∀ p, X p ≠ X (p + 1)) : Inv (run alg3 (init3 X) σ 0) where
  reg_r := by intro p x h; simp at h
  locX := by
    intro p q hpq
    simp only [run_zero_loc, init3]
    rcases hpq with rfl | rfl
    · exact hX p
    · have := hX (p - 1)
      rw [sub_add_cancel] at this
      exact this.symm
  locReg := by intro p q x _ h; simp at h
  regReg := by intro p q x y _ h; simp at h
  last := by intro q p x _ h; simp at h

lemma inv_run (hX : ∀ p, X p ≠ X (p + 1)) (t : ℕ) : Inv (run alg3 (init3 X) σ t) := by
  induction t with
  | zero => exact inv_zero X σ hX
  | succ t ih => exact ih.step (stepFacts X σ t)

end Alg3Proper

open Alg3Proper

variable {n : ℕ}

/-- Algorithm 3: at every time, the current identifiers of neighbours differ (part of the
induction claim in the proof of Lemma 4.5 of [paper]). -/
theorem alg3_X_proper (X : ZMod n → ℕ) (hX : ∀ p, X p ≠ X (p + 1))
    (σ : ℕ → Finset (ZMod n)) (t : ℕ) (p : ZMod n) :
    ((run alg3 (init3 X) σ t).loc p).X ≠ ((run alg3 (init3 X) σ t).loc (p + 1)).X :=
  (inv_run X σ hX t).locX p (p + 1) (Or.inl rfl)

/-- Algorithm 3: the current identifier of `p` differs from the identifier written in the register
of each neighbour: `X_p(t) ∉ {X_q(t), X̂_q(t)}` (the induction claim in the proof of Lemma 4.5
of [paper]). -/
theorem alg3_X_ne_reg (X : ZMod n → ℕ) (hX : ∀ p, X p ≠ X (p + 1))
    (σ : ℕ → Finset (ZMod n)) (t : ℕ) (p q : ZMod n) (hq : q = p - 1 ∨ q = p + 1) (x : St3)
    (hx : (run alg3 (init3 X) σ t).reg q = some x) :
    ((run alg3 (init3 X) σ t).loc p).X ≠ x.X :=
  (inv_run X σ hX t).locReg p q x hq.symm hx

/-- **Lemma 4.5 of [paper]**: in every execution of Algorithm 3 from a proper colouring by the
identifiers, the identifiers written in the registers of two neighbours always differ:
`X̂_p(t) ≠ X̂_{p+1}(t)` whenever both registers are written.

Proof: by induction on `t` with the invariant `Alg3Proper.Inv` (see the module docstring), which
records, besides `X_p ∉ {X_q, X̂_q}`, that a process's register holds an earlier state with a
smaller-or-equal counter `r`, and that if the last step of `q` changed `X_q` and `r_p = r̂_q`, then
`q` computed `X_q` from `X̂_q` while reading exactly the current `X_p`. The gate of line 11
forces `r̂_q = r_p` whenever `p` changes its identifier after `q` did, and Lemma 4.3 concludes. -/
theorem lemma_4_5 (X : ZMod n → ℕ) (hX : ∀ p, X p ≠ X (p + 1))
    (σ : ℕ → Finset (ZMod n)) (t : ℕ) (p : ZMod n) (x y : St3)
    (hx : (run alg3 (init3 X) σ t).reg p = some x)
    (hy : (run alg3 (init3 X) σ t).reg (p + 1) = some y) : x.X ≠ y.X :=
  (inv_run X σ hX t).regReg p (p + 1) x y (Or.inl rfl) hx hy

end AsyncCycle
