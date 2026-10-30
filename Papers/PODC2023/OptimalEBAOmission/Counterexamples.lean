import Papers.PODC2023.OptimalEBAOmission.MinCtx

/-!
# Counterexamples to Proposition 6.4 (literal 0-chains) and Corollary 6.7 (`t = n - 1`)

* `prop_6_4_lit_false`: with the paper's literal definition of 0-chains (condition (c): "`a k`
  knows that `a (k - 1)` has just decided `0`", `IsZeroChainLit`), `P0` is **not** safe in
  `γ_min,3,0`, contradicting Proposition 6.4. In the failure-free run with preferences `0, 1, 1`,
  agent `2` hears agent `0`'s `0`-decision in round 1, so it has not got the same local state as in
  any all-`1` run; but it does not know *who* decided `0` (agent `1` might have had preference `0`
  instead), so it has not received a literal 0-chain. With the repaired notion
  (`ReceivedChain`, "`a k` knows that *some* agent has just decided `0`") it has
  (`receivedChain_at_counterexample`): the difference is exactly the definition.
  `prop_6_4_lit_false_gen`: the same failure-free example in `γ_min,n,t` for every `n ≥ 3`,
  `t ≤ n - 2`.
* `cor_6_7_min_false`: for `t = n - 1` the paper's `P^min` (deciding `1` at time `t + 1 = n`) is
  not optimal: `P^min_{n-1}` (deciding `1` at time `n - 1`) implements `P0`, is an EBA decision
  protocol and strictly dominates it. Corollary 6.7 omits the hypothesis `t ≤ n - 2` of
  Theorems 6.5 and 6.6.
-/

namespace Podc.OptimalEBAOmission

open Context

namespace Counterexamples

variable {n t : ℕ}

/-- The failure-free configuration of `γ_min,n,t` with initial preferences `v`. -/
def ffCfg (v : Fin n → Val) : (minCtx n t).Config :=
  ⟨⟨Finset.univ, fun _ _ _ => true⟩, v, fun _ => ()⟩

theorem ffCfg_valid (v : Fin n → Val) : (ffCfg (t := t) v).Valid :=
  ⟨⟨by simp [ffCfg], fun _ _ _ h => by cases h⟩, fun _ => trivial⟩

theorem ffCfg_N (v : Fin n → Val) (i : Fin n) : i ∈ (ffCfg (t := t) v).pat.N := by
  simp [ffCfg]

/-! ### Proposition 6.4 with literal 0-chains -/

section Prop64

variable {v : Fin n → Val}

theorem act_zero_pmin1 {T : ℕ} (hT : T ≠ 0) (i : Fin n) :
    pmin T i ((minCtx n t).state (pmin T) (ffCfg v) 0 i) =
      if v i = 0 then .decide 0 else .noop := by
  rw [Min.act_eq]
  simp [dec_zero, jd_zero, ffCfg, Ne.symm hT]

theorem dec_one_pmin1 {T : ℕ} (hT : T ≠ 0) {i : Fin n} (hi : v i = 1) :
    dec (pmin T) (ffCfg (t := t) v) 1 i = none := by
  rw [dec_succ, act_zero_pmin1 hT, if_neg (by rw [hi]; decide)]
  rfl

theorem jd_one_pmin1 {T : ℕ} (hT : T ≠ 0) {j : Fin n} (hj : v j = 0) (i : Fin n) :
    ((minCtx n t).state (pmin T) (ffCfg v) 1 i).1.jd = some 0 :=
  (jd_succ_eq_zero_iff _ _ 0 i).2 ⟨j, rfl, by rw [act_zero_pmin1 hT, if_pos hj]⟩

theorem state_one_pmin1 {T : ℕ} (hT : T ≠ 0) {i j : Fin n} (hi : v i = 1) (hj : v j = 0) :
    (minCtx n t).state (pmin T) (ffCfg v) 1 i = Min.st ⟨1, 1, none, some 0⟩ := by
  rw [Min.state_core, dec_one_pmin1 hT hi, jd_one_pmin1 hT hj]
  simp [ffCfg, hi]

/-- The run of the counterexample: `γ_min,3,0`, no failures, preferences `0, 1, 1`. -/
abbrev c64 : (minCtx 3 0).Config := ffCfg ![0, 1, 1]

/-- The companion run: no failures, preferences `1, 0, 1`. -/
abbrev c64' : (minCtx 3 0).Config := ffCfg ![1, 0, 1]

theorem pmin1_implements : Implements (pmin (n := 3) (t := 0) 1) :=
  Min.pmin_implements (by omega) (by omega) (by omega) (Or.inl le_rfl)

theorem state_c64 : (minCtx 3 0).state (pmin 1) c64 1 2 = Min.st ⟨1, 1, none, some 0⟩ :=
  state_one_pmin1 one_ne_zero (j := 0) rfl rfl

theorem state_c64' : (minCtx 3 0).state (pmin 1) c64' 1 2 = Min.st ⟨1, 1, none, some 0⟩ :=
  state_one_pmin1 one_ne_zero (j := 1) rfl rfl

/-- Agent `2` does not know at `(c64, 1)` that agent `0` has just decided `0`: in `c64'` it has
the same local state, but agent `0` has not decided. -/
theorem not_knows_c64 :
    ¬ Knows (pmin 1) 2 ((minCtx 3 0).state (pmin 1) c64 1 2)
      (fun c' m' => JDecided (pmin 1) c' m' 0 0) := by
  intro hK
  have := hK c64' (ffCfg_valid _) 1 (state_c64'.trans state_c64.symm)
  have h := this.2.1
  rw [dec_one_pmin1 one_ne_zero (i := 0) rfl] at h
  cases h

/-- Agent `2` has not received a 0-chain (paper's definition) by `(c64, 1)`. -/
theorem not_receivedChainLit_c64 : ¬ ReceivedChainLit (pmin 1) c64 1 2 := by
  rintro ⟨m', hm', a, ⟨-, ha0, -, hkn⟩, ham⟩
  interval_cases m'
  · rw [ham] at ha0; exact absurd ha0 (by decide)
  · have h0 : a 0 = 0 := by
      revert ha0; generalize a 0 = x; fin_cases x <;> simp [ffCfg]
    have := hkn 1 le_rfl le_rfl
    rw [ham, h0] at this
    exact not_knows_c64 this

/-- **Proposition 6.4 is false with the paper's definition of 0-chains** (Definition 6.2 with
`IsZeroChainLit`). In `γ_min,3,0`, the implementation `P^min_1` of `P0` violates safety
condition (1) at the point `(c64, 1)` for agent `2`. -/
theorem prop_6_4_lit_false : ¬ SafeLit (minCtx 3 0) := by
  intro hS
  obtain ⟨c', hc', h1, hs⟩ :=
    (hS _ pmin1_implements).one c64 (ffCfg_valid _) 1 2 not_receivedChainLit_c64
  have hjd : ((minCtx 3 0).state (pmin 1) c' 1 2).1.jd = some 0 := by
    rw [hs, state_c64]; rfl
  obtain ⟨j, -, ha⟩ := (jd_succ_eq_zero_iff _ _ 0 2).1 hjd
  have := Min.start hc' (deciding_of_act Min.oneShot.oneShotOn hc' ha)
  rw [h1 j] at this
  exact absurd this (by decide)

/-- With the repaired notion of 0-chains (`ReceivedChain`), agent `2` *has* received a 0-chain
by `(c64, 1)` (it is deciding `0` at time `1`): the failure of Proposition 6.4 in
`prop_6_4_lit_false` is due exactly to the literal definition of 0-chains. -/
theorem receivedChain_at_counterexample : ReceivedChain (pmin 1) c64 1 2 := by
  refine (pmin1_implements.receivedChain_iff (ffCfg_valid _)).2 ?_
  rw [dec_succ, Min.act_eq, dec_one_pmin1 one_ne_zero (i := 2) rfl, jd_one_pmin1 one_ne_zero (j := 0) rfl]
  simp [newDec]

/-- Initial preferences: agent `k` prefers `0`, all others `1`. -/
def onlyZero (k : Fin n) : Fin n → Val := fun i => if i = k then 0 else 1

/-- **Proposition 6.4 is false with the paper's definition of 0-chains, for every `n ≥ 3` and
`t ≤ n - 2`** (the whole range of Proposition 6.4 with `n ≥ 3`; the counterexample uses
failure-free runs only). In `γ_min,n,t`, at time `1` of the failure-free run where only agent `0`
prefers `0`, agent `2` has the same local state as in the failure-free run where only agent `1`
prefers `0`; so it does not know that agent `0` has just decided, has no literal 0-chain, and yet
is in no all-`1` run with this local state. -/
theorem prop_6_4_lit_false_gen (hn : 3 ≤ n) (ht : t + 2 ≤ n) : ¬ SafeLit (minCtx n t) := by
  intro hS
  have hn0 : 0 < n := by omega
  have hn1 : 1 < n := by omega
  have hn2 : 2 < n := by omega
  have hP : Implements (pmin (n := n) (t := t) (t + 1)) :=
    Min.pmin_implements (by omega) le_rfl (by omega) (Or.inl le_rfl)
  have hT : t + 1 ≠ 0 := by omega
  have h01 : (⟨0, hn0⟩ : Fin n) ≠ ⟨1, hn1⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, hn0⟩ : Fin n) ≠ ⟨2, hn2⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, hn1⟩ : Fin n) ≠ ⟨2, hn2⟩ := by simp [Fin.ext_iff]
  have hs : (minCtx n t).state (pmin (t + 1)) (ffCfg (onlyZero ⟨0, hn0⟩)) 1 ⟨2, hn2⟩ =
      Min.st ⟨1, 1, none, some 0⟩ :=
    state_one_pmin1 hT (j := ⟨0, hn0⟩) (by simp [onlyZero, h02.symm]) (by simp [onlyZero])
  have hs' : (minCtx n t).state (pmin (t + 1)) (ffCfg (onlyZero ⟨1, hn1⟩)) 1 ⟨2, hn2⟩ =
      Min.st ⟨1, 1, none, some 0⟩ :=
    state_one_pmin1 hT (j := ⟨1, hn1⟩) (by simp [onlyZero, h12.symm]) (by simp [onlyZero])
  have hnr : ¬ ReceivedChainLit (pmin (t + 1)) (ffCfg (t := t) (onlyZero ⟨0, hn0⟩)) 1
      ⟨2, hn2⟩ := by
    rintro ⟨m', hm', a, ⟨-, ha0, -, hkn⟩, ham⟩
    interval_cases m'
    · rw [ham] at ha0; simp [ffCfg, onlyZero, h02.symm] at ha0
    · have h0 : a 0 = ⟨0, hn0⟩ := by
        by_contra h; simp [ffCfg, onlyZero, h] at ha0
      have hK := hkn 1 le_rfl le_rfl
      rw [ham, h0] at hK
      have := (hK _ (ffCfg_valid (onlyZero ⟨1, hn1⟩)) 1 (hs'.trans hs.symm)).2.1
      rw [dec_one_pmin1 hT (by simp [onlyZero, h01])] at this
      cases this
  obtain ⟨c', hc', h1, hs''⟩ := (hS _ hP).one _ (ffCfg_valid _) 1 _ hnr
  have hjd : ((minCtx n t).state (pmin (t + 1)) c' 1 ⟨2, hn2⟩).1.jd = some 0 := by
    rw [hs'', hs]; rfl
  obtain ⟨j, -, ha⟩ := (jd_succ_eq_zero_iff _ _ 0 _).1 hjd
  have := Min.start hc' (deciding_of_act Min.oneShot.oneShotOn hc' ha)
  rw [h1 j] at this
  exact absurd this (by decide)

end Prop64

/-! ### Corollary 6.7 for `t = n - 1` -/

section Cor67

theorem pmin_eq_of_time {T T' : ℕ} (i : Fin n) (s : (minCtx n t).L) (h : s.1.time ≠ T)
    (h' : s.1.time ≠ T') : pmin T i s = pmin T' i s := by
  simp only [pmin, if_neg h, if_neg h']

/-- `P^min_T` and `P^min_{T'}` generate the same runs up to time `T ≤ T'`. -/
theorem state_pmin_eq {T T' : ℕ} (hTT : T ≤ T') (c : (minCtx n t).Config) :
    ∀ k ≤ T, (minCtx n t).state (pmin T) c k = (minCtx n t).state (pmin T') c k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have e := ih (by omega)
    have ha : ∀ j, pmin T j ((minCtx n t).state (pmin T') c k j) =
        pmin T' j ((minCtx n t).state (pmin T') c k j) := fun j =>
      pmin_eq_of_time j _ (by simp; omega) (by simp; omega)
    funext i
    have hr : rcv (pmin T) c k i = rcv (pmin T') c k i := by
      funext j; simp only [rcv, e, ha]
    simp only [state_succ, hr, e, ha]

/-- In an all-`1` run, `P^min_T` decides `1` at time `T` (when it is `0`-biased). -/
theorem act_T_allOnes {T : ℕ} (hT3 : t + 1 ≤ T ∨ n - 1 ≤ T) {c : (minCtx n t).Config}
    (hc : c.Valid) (h1 : ∀ j, c.init j = 1) (i : Fin n) :
    pmin T i ((minCtx n t).state (pmin T) c T i) = .decide 1 := by
  have hZ := Min.zeroBiased (n := n) (t := t) hT3
  have hd : dec (pmin T) c T i = none := by
    by_contra hne
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hne
    obtain ⟨d, hdT, hD⟩ := exists_deciding Min.oneShot.oneShotOn hc hw
    rcases val_cases w with rfl | rfl
    · exact hZ.not_deciding_zero hc h1 hD
    · have := (Min.deciding_one hc hD).1; omega
  have hjd : ((minCtx n t).state (pmin T) c T i).1.jd ≠ some 0 := by
    intro hj
    cases T with
    | zero => rw [jd_zero] at hj; cases hj
    | succ k =>
      obtain ⟨j, -, ha⟩ := (jd_succ_eq_zero_iff _ _ k i).1 hj
      exact hZ.not_deciding_zero hc h1 (deciding_of_act Min.oneShot.oneShotOn hc ha)
  rw [Min.act_eq, if_neg (by simpa using hd), if_neg (by simp [h1 i, hjd]), if_pos rfl]

variable (hn : 2 ≤ n)
include hn

theorem pmin_pred_implements : Implements (pmin (n := n) (t := n - 1) (n - 1)) :=
  Min.pmin_implements hn (by omega) le_rfl (Or.inr le_rfl)

omit hn in
/-- `P^min_{n-1}` dominates `P^min_n` in `γ_min,n,n-1`. -/
theorem dominates_pred :
    Dominates (pmin (n := n) (t := n - 1) (n - 1)) (pmin (n := n) (t := n - 1) (n - 1 + 1)) := by
  intro c hc i _ m v hv m' hm' w hw
  have hOS := (Min.oneShot (n := n) (t := n - 1) (T := n - 1)).oneShotOn
  have hD := deciding_of_act hOS hc hv
  have hm := Min.le_of_undecided hc hD.1
  have hw' : pmin (n - 1) i ((minCtx n (n - 1)).state (pmin (n - 1)) c m' i) = .decide w := by
    rw [state_pmin_eq (T := n - 1) (T' := n - 1 + 1) (by omega) c m' (by omega),
      pmin_eq_of_time (T := n - 1) (T' := n - 1 + 1) i _ (by simp; omega) (by simp; omega)]
    exact hw
  have := (deciding_unique hOS hc hD (deciding_of_act hOS hc hw')).1
  omega

/-- `P^min_n` does not dominate `P^min_{n-1}`: in the failure-free all-`1` run, `P^min_{n-1}`
decides at time `n - 1`, `P^min_n` only at time `n`. -/
theorem not_dominates_succ :
    ¬ Dominates (pmin (n := n) (t := n - 1) (n - 1 + 1)) (pmin (n := n) (t := n - 1) (n - 1)) := by
  intro hD
  let i : Fin n := ⟨0, by omega⟩
  have hc := ffCfg_valid (n := n) (t := n - 1) (fun _ => 1)
  exact hD _ hc i (ffCfg_N _ i) (n - 1 + 1) 1 (act_T_allOnes (Or.inl le_rfl) hc (fun _ => rfl) i)
    (n - 1) (by omega) 1 (act_T_allOnes (Or.inr le_rfl) hc (fun _ => rfl) i)

/-- **Corollary 6.7 is false for `t = n - 1`** (the paper omits the hypothesis `t ≤ n - 2` of
Theorems 6.5 and 6.6): in `γ_min,n,n-1` with `n ≥ 2`, the protocol `P^min` (deciding `1` at time
`t + 1 = n`) is not optimal, even among one-shot competitors: `P^min_{n-1}` is a one-shot EBA
decision protocol (it implements `P0`) that strictly dominates it. -/
theorem cor_6_7_min_false : ¬ OptimalOneShot (pmin (n := n) (t := n - 1) (n - 1 + 1)) := by
  rintro ⟨-, hopt⟩
  exact hopt _ (prop_6_1 subset_rfl (pmin_pred_implements hn)).1 Min.oneShot
    ⟨dominates_pred, not_dominates_succ hn⟩

end Cor67

end Counterexamples

end Podc.OptimalEBAOmission
