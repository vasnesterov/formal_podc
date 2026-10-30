import Papers.PODC2023.OptimalEBAOmission.AllOnes

/-!
# The minimal context `γ_min,n,t` and the protocol `P^min` (Theorem 6.5)

`E_min(n)`: local states `⟨time, init, decided, jd⟩` (no extra component), messages `{0, 1}`; an
agent sends `v` to everybody when it decides `v` and nothing otherwise. Failure model `SO(t)`.

`P^min_T` decides `0` on `init = 0 ∨ jd = 0` and `1` at time `T`; the paper's `P^min` is `T = t + 1`.

* `pmin_implements`: `P^min_T` implements `P0` whenever `T ≤ t + 1`, `T ≤ n - 1` and
  (`t + 1 ≤ T` or `n - 1 ≤ T`). For `t ≤ n - 2` this is **Theorem 6.5** (`thm_6_5`, `T = t + 1`);
  for `t = n - 1` the implementation is `T = n - 1 = t`, not `P^min`.
* `chainCfg`: the runs with a chain of faulty agents relaying a `0` used throughout.
-/

namespace Podc.OptimalEBAOmission

open Context

/-- The minimal EBA context `γ_min,n,t = (E_min(n), SO(t))`. -/
def minCtx (n t : ℕ) : Context n where
  X := Unit
  M := Val
  tag := some
  initX _ _ := Set.univ
  initX_nonempty _ _ := ⟨(), trivial⟩
  μ _ _ a _ := match a with
    | .decide v => some v
    | .noop => none
  μ_decide _ _ v _ := ⟨v, rfl, rfl⟩
  μ_noop _ _ _ _ h := by cases h
  δX _ _ _ _ := ()
  FM := SO n t

/-- The protocol `P^min` with the time of the `1`-decision as a parameter `T`:
```
if decided_i ≠ ⊥ then noop
else if init_i = 0 ∨ jd_i = 0 then decide_i(0)
else if time_i = T then decide_i(1)
else noop
``` -/
def pmin {n t : ℕ} (T : ℕ) : (minCtx n t).Protocol := fun _ s =>
  if s.1.decided ≠ none then .noop
  else if s.1.init = 0 ∨ s.1.jd = some 0 then .decide 0
  else if s.1.time = T then .decide 1 else .noop

namespace Min

variable {n t T : ℕ}

theorem oneShot : OneShot (pmin (n := n) (t := t) T) := fun _ s h => by
  simp only [pmin, if_pos h]

theorem silent : SilentAfterDecide (minCtx n t) := fun _ _ _ _ => rfl

theorem initIndep : InitIndep (minCtx n t) := fun _ _ => Iff.rfl

theorem state_eq_iff {s s' : (minCtx n t).L} : s = s' ↔ s.1 = s'.1 :=
  ⟨fun h => h ▸ rfl, fun h => Prod.ext h rfl⟩

/-- The local state of `γ_min` with EBA part `cr`. -/
def st (cr : Core) : (minCtx n t).L := (cr, ())

theorem act_eq (c : (minCtx n t).Config) (m : ℕ) (i : Fin n) :
    pmin T i ((minCtx n t).state (pmin T) c m i) =
      if dec (pmin T) c m i ≠ none then .noop
      else if c.init i = 0 ∨ ((minCtx n t).state (pmin T) c m i).1.jd = some 0 then .decide 0
      else if m = T then .decide 1 else .noop := by
  simp only [pmin, time_state, init_state, dec]

section Run

variable {c : (minCtx n t).Config} (hc : c.Valid)
include hc

theorem deciding_iff' {m : ℕ} {i : Fin n} {v : Val} :
    Deciding (pmin T) c m i v ↔ dec (pmin T) c m i = none ∧
      pmin T i ((minCtx n t).state (pmin T) c m i) = .decide v :=
  deciding_iff oneShot.oneShotOn hc

theorem deciding_one {d : ℕ} {i : Fin n} (h : Deciding (pmin T) c d i 1) :
    d = T ∧ c.init i = 1 ∧ ((minCtx n t).state (pmin T) c d i).1.jd ≠ some 0 := by
  obtain ⟨hd, ha⟩ := (deciding_iff' hc).1 h
  rw [act_eq, if_neg (by simpa using hd)] at ha
  split_ifs at ha with h1 h2
  · cases ha
  · push_neg at h1
    exact ⟨h2, by rcases val_cases (c.init i) with h | h; exact absurd h h1.1; exact h, h1.2⟩

theorem jd_ne_one {m : ℕ} {i : Fin n} (hm : m ≤ T) :
    ((minCtx n t).state (pmin T) c m i).1.jd ≠ some 1 := by
  intro h
  cases m with
  | zero => rw [jd_zero] at h; cases h
  | succ k =>
    obtain ⟨j, -, ha⟩ := exists_of_jd_succ_eq_one _ c k i h
    have := (deciding_one hc (deciding_of_act oneShot.oneShotOn hc ha)).1
    omega

theorem le_of_undecided {m : ℕ} {i : Fin n} (hd : dec (pmin T) c m i = none) : m ≤ T := by
  by_contra hlt
  have hT : dec (pmin T) c T i = none := dec_none_of_le oneShot.oneShotOn hc hd (by omega)
  have hT1 : dec (pmin T) c (T + 1) i = none := dec_none_of_le oneShot.oneShotOn hc hd (by omega)
  rw [dec_succ, act_eq, if_neg (by simpa using hT)] at hT1
  split_ifs at hT1 with h1 h2 <;> simp_all [newDec]

theorem prev {m : ℕ} {j : Fin n} (h : Deciding (pmin T) c (m + 1) j 0) :
    ∃ l, Deciding (pmin T) c m l 0 := by
  obtain ⟨hd, ha⟩ := (deciding_iff' hc).1 h
  have hinit : c.init j ≠ 0 := by
    intro h0
    have hD : Deciding (pmin T) c 0 j 0 := (deciding_iff' hc).2 ⟨rfl, by
      rw [act_eq, if_neg (by simp [dec_zero]), if_pos (Or.inl h0)]⟩
    exact absurd (deciding_unique oneShot.oneShotOn hc h hD).1 (by omega)
  rw [act_eq, if_neg (by simpa using hd)] at ha
  split_ifs at ha with h1 h2
  · rcases h1 with h1 | h1
    · exact absurd h1 hinit
    · obtain ⟨l, -, hl⟩ := (jd_succ_eq_zero_iff _ c m j).1 h1
      exact ⟨l, deciding_of_act oneShot.oneShotOn hc hl⟩
  · cases ha

theorem start {j : Fin n} (h : Deciding (pmin T) c 0 j 0) : c.init j = 0 := by
  obtain ⟨-, ha⟩ := (deciding_iff' hc).1 h
  rw [act_eq, if_neg (by simp [dec_zero])] at ha
  split_ifs at ha with h1 h2
  · rcases h1 with h1 | h1
    · exact h1
    · rw [jd_zero] at h1; cases h1
  · cases ha

/-- With `t + 1 ≤ T` or `n - 1 ≤ T`, nobody decides `0` at time `T` if some undecided agent with
preference `1` has not heard of a `0` by then. -/
theorem no_zero_at_T (hT3 : t + 1 ≤ T ∨ n - 1 ≤ T) {i : Fin n}
    (hd : dec (pmin T) c T i = none) (h1 : c.init i = 1)
    (hj : ((minCtx n t).state (pmin T) c T i).1.jd ≠ some 0) (l : Fin n) :
    ¬ Deciding (pmin T) c T l 0 := by
  intro hl
  have hOS := (oneShot (n := n) (t := t) (T := T)).oneShotOn
  obtain ⟨a, haT, hdec, hinj⟩ := exists_chain_of_prev hOS (fun m j h => prev hc h) hc hl
  -- `i` is not on the chain
  have hai : ∀ k ≤ T, a k ≠ i := by
    intro k hk he
    by_cases hkT : k = T
    · subst hkT
      have := ((deciding_iff' hc).1 (he ▸ hdec k le_rfl)).2
      rw [act_eq, if_neg (by simpa using hd), if_neg (by simp [h1, hj])] at this
      split_ifs at this; cases this
    · have := dec_stable hOS hc (he ▸ hdec k hk).2 T (by omega)
      rw [hd] at this; cases this
  rcases hT3 with hT3 | hT3
  · obtain ⟨k, hk, hkN⟩ := exists_nonfaulty_of_inj (hc.1).1
      (fun k hk l hl he => hinj k (by omega) l (by omega) he)
    have hjd : ((minCtx n t).state (pmin T) c (k + 1) i).1.jd = some 0 := by
      refine (jd_succ_eq_zero_iff _ c k i).2 ⟨a k, ?_, ((deciding_iff' hc).1 (hdec k (by omega))).2⟩
      by_contra hF; exact (hc.1).2 k (a k) i (by simpa using hF) hkN
    by_cases hkT : k + 1 = T
    · subst hkT; exact hj hjd
    · have hu : dec (pmin T) c (k + 1) i = none := dec_none_of_le hOS hc hd (by omega)
      have hD : Deciding (pmin T) c (k + 1) i 0 := (deciding_iff' hc).2 ⟨hu, by
        rw [act_eq, if_neg (by simpa using hu), if_pos (Or.inr hjd)]⟩
      have := dec_stable hOS hc hD.2 T (by omega)
      rw [hd] at this; cases this
  · have hsub : (Finset.range (T + 1)).image a ⊆ Finset.univ.erase i := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      simp only [Finset.mem_range] at hk
      exact Finset.mem_erase.2 ⟨hai k (by omega), Finset.mem_univ _⟩
    have hcard : ((Finset.range (T + 1)).image a).card = T + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro k hk l hl he
      simp only [Finset.coe_range, Set.mem_Iio] at hk hl
      exact hinj k (by omega) l (by omega) he
    have := Finset.card_le_card hsub
    rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin] at this
    omega

end Run

/-- `P^min_T` is `0`-biased (when the `1`-decision time is safe). -/
theorem zeroBiased (hT3 : t + 1 ≤ T ∨ n - 1 ≤ T) : ZeroBiased (pmin (n := n) (t := t) T) where
  oneShot := oneShot.oneShotOn
  init0 c hc m i hd h0 := (deciding_iff' hc).2 ⟨hd, by
    rw [act_eq, if_neg (by simpa using hd), if_pos (Or.inl h0)]⟩
  jd0 c hc m i hd hj := (deciding_iff' hc).2 ⟨hd, by
    rw [act_eq, if_neg (by simpa using hd), if_pos (Or.inr hj)]⟩
  zeroBeforeOne c hc d d' i j h1 h0 := by
    obtain ⟨hdT, hi1, hjd⟩ := deciding_one hc h1
    subst hdT
    by_contra hle
    obtain ⟨a, -, hdec, -⟩ := exists_chain_of_prev oneShot.oneShotOn (fun m j h => prev hc h) hc h0
    exact no_zero_at_T hc hT3 h1.1 hi1 hjd (a d) (hdec d (by omega))
  prev c hc m j h := prev hc h
  start c hc j h := start hc h

/-! ### Chain runs -/

/-- The run with a chain `a 0, …, a L`: `a 0` has preference `0`, all others `1`; the agents
`a 0, …, a (L - 1)` are faulty and `a k` delivers only to `a (k + 1)`; everybody else (in
particular `a L`) is nonfaulty. -/
def chainCfg (a : ℕ → Fin n) (L : ℕ) : (minCtx n t).Config :=
  ⟨⟨Finset.univ \ (Finset.range L).image a,
    fun k l r => decide (l ∉ (Finset.range L).image a) || (decide (l = a k) && decide (r = a (k + 1)))⟩,
    fun l => if l = a 0 then 0 else 1, fun _ => ()⟩

variable {a : ℕ → Fin n} {L : ℕ}

theorem mem_image_range_iff (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l) {k : ℕ} (hk : k ≤ L) :
    a k ∈ (Finset.range L).image a ↔ k < L := by
  constructor
  · intro h
    obtain ⟨k', hk', he⟩ := Finset.mem_image.1 h
    simp only [Finset.mem_range] at hk'
    have := hinj k' (by omega) k hk he
    omega
  · intro h; exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 h, rfl⟩

theorem chainCfg_valid (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l) (hL : L ≤ t) :
    (chainCfg (t := t) a L).Valid := by
  refine ⟨⟨?_, ?_⟩, fun _ => trivial⟩
  · simp only [chainCfg]
    rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
    refine (Finset.card_image_le).trans ?_
    simpa using hL
  · intro k l r hF
    simp only [chainCfg, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not] at hF
    simp only [chainCfg, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    exact hF.1

theorem chainCfg_N {l : Fin n} : l ∈ (chainCfg (t := t) a L).pat.N ↔ l ∉ (Finset.range L).image a := by
  simp [chainCfg]

/-- The run of `P^min_T` on a chain configuration, up to time `L + 1`. -/
theorem chain_inv (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l) :
    ∀ k ≤ L + 1, k ≤ T → ∀ l,
      dec (pmin T) (chainCfg (t := t) a L) k l =
        (if ∃ k' < k, a k' = l then some 0 else none) ∧
      ((minCtx n t).state (pmin T) (chainCfg (t := t) a L) k l).1.jd =
        (if (1 ≤ k ∧ k ≤ L ∧ a k = l) ∨ k = L + 1 then some 0 else none) := by
  intro k
  induction k with
  | zero => intro _ _ l; simp [dec_zero, jd_zero]
  | succ k ih =>
    intro hk hkT
    have IH := ih (by omega) (by omega)
    -- actions at time `k`
    have hact : ∀ l, pmin T l ((minCtx n t).state (pmin T) (chainCfg (t := t) a L) k l) =
        if l = a k then .decide 0 else .noop := by
      intro l
      obtain ⟨hdl, hjl⟩ := IH l
      rw [act_eq]
      by_cases hl : l = a k
      · subst hl
        have hund : ¬ ∃ k' < k, a k' = a k := fun ⟨k', hk', he⟩ => by
          have := hinj k' (by omega) k (by omega) he; omega
        rw [hdl, if_neg hund, if_pos rfl]
        simp only [ne_eq, not_true_eq_false, if_false]
        rw [if_pos]
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · left; subst h0; simp [chainCfg]
        · right; rw [hjl, if_pos (Or.inl ⟨h0, by omega, rfl⟩)]
      · rw [if_neg hl]
        by_cases hd : ∃ k' < k, a k' = l
        · rw [hdl, if_pos hd]; simp
        · rw [hdl, if_neg hd]
          simp only [ne_eq, not_true_eq_false, if_false]
          have hinit : (chainCfg (t := t) a L).init l ≠ 0 := by
            simp only [chainCfg]
            split_ifs with h
            · exfalso; rcases Nat.eq_zero_or_pos k with h0 | h0
              · subst h0; exact hl h
              · exact hd ⟨0, h0, h.symm⟩
            · decide
          have hjd : ((minCtx n t).state (pmin T) (chainCfg (t := t) a L) k l).1.jd ≠ some 0 := by
            rw [hjl]
            split_ifs with h
            · exfalso; rcases h with h | h
              · exact hl h.2.2.symm
              · omega
            · simp
          rw [if_neg (by tauto), if_neg (by omega)]
    refine fun l => ⟨?_, ?_⟩
    · rw [dec_succ, hact, (IH l).1]
      by_cases hl : l = a k
      · subst hl
        have hund : ¬ ∃ k' < k, a k' = a k := fun ⟨k', hk', he⟩ => by
          have := hinj k' (by omega) k (by omega) he; omega
        rw [if_pos rfl, if_neg hund, if_pos ⟨k, by omega, rfl⟩]; rfl
      · rw [if_neg hl]
        simp only [newDec]
        congr 1
        apply propext
        constructor
        · rintro ⟨k', hk', he⟩; exact ⟨k', by omega, he⟩
        · rintro ⟨k', hk', he⟩
          refine ⟨k', ?_, he⟩
          by_contra hne
          exact hl (by rw [← he]; congr 1; omega)
    · have hF : (chainCfg (t := t) a L).pat.F k (a k) l = (decide (k = L) || decide (l = a (k + 1))) := by
        simp only [chainCfg, mem_image_range_iff hinj (show k ≤ L by omega)]
        simp only [not_lt, decide_eq_decide, true_and, decide_true, Bool.true_and]
        congr 1
        exact decide_eq_decide.2 ⟨fun h => by omega, fun h => by omega⟩
      by_cases hcond : k = L ∨ l = a (k + 1)
      · have : ((minCtx n t).state (pmin T) (chainCfg (t := t) a L) (k + 1) l).1.jd = some 0 := by
          refine (jd_succ_eq_zero_iff _ _ k l).2 ⟨a k, ?_, by rw [hact, if_pos rfl]⟩
          rw [hF]; rcases hcond with h | h <;> simp [h]
        rw [this, if_pos]
        rcases hcond with h | h
        · right; omega
        · by_cases hkL : k = L
          · right; omega
          · left; exact ⟨by omega, by omega, h.symm⟩
      · push_neg at hcond
        have : ((minCtx n t).state (pmin T) (chainCfg (t := t) a L) (k + 1) l).1.jd = none := by
          refine (jd_succ_eq_none_iff _ _ k l).2 fun j hj => ?_
          rw [hact]
          split_ifs with h
          · subst h; rw [hF] at hj; simp [hcond.1, hcond.2] at hj
          · rfl
        rw [this, if_neg]
        rintro (h | h)
        · exact hcond.2 h.2.2.symm
        · omega

/-- Local states of `γ_min` are their EBA part. -/
theorem state_core (P : (minCtx n t).Protocol) (c : (minCtx n t).Config) (m : ℕ) (i : Fin n) :
    (minCtx n t).state P c m i =
      st ⟨m, c.init i, dec P c m i, ((minCtx n t).state P c m i).1.jd⟩ := by
  rw [state_eq_iff]; ext <;> simp [dec, st]

theorem chain_state_other (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l) (hLT : L ≤ T) {l : Fin n}
    (hl : ∀ k ≤ L, a k ≠ l) :
    (minCtx n t).state (pmin T) (chainCfg (t := t) a L) L l = st ⟨L, 1, none, none⟩ := by
  obtain ⟨hd, hj⟩ := chain_inv (t := t) hinj L (by omega) hLT l
  rw [state_core, hd, hj, if_neg, if_neg]
  · simp only [chainCfg, if_neg (Ne.symm (hl 0 (Nat.zero_le _)))]
  · rintro (h | h)
    · exact hl L le_rfl h.2.2
    · omega
  · rintro ⟨k', hk', he⟩; exact hl k' (by omega) he

theorem chain_state_end (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l) (hLT : L ≤ T) (hL1 : 1 ≤ L) :
    (minCtx n t).state (pmin T) (chainCfg (t := t) a L) L (a L) = st ⟨L, 1, none, some 0⟩ := by
  obtain ⟨hd, hj⟩ := chain_inv (t := t) hinj L (by omega) hLT (a L)
  rw [state_core, hd, hj, if_pos (Or.inl ⟨hL1, le_rfl, rfl⟩), if_neg]
  · have : a L ≠ a 0 := fun h => by have := hinj L le_rfl 0 (Nat.zero_le _) h; omega
    simp only [chainCfg, if_neg this]
  · rintro ⟨k', hk', he⟩; have := hinj k' (by omega) L le_rfl he; omega

theorem chain_state_next (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l) (hLT : L + 1 ≤ T)
    {l : Fin n} (hl : ∀ k ≤ L, a k ≠ l) :
    (minCtx n t).state (pmin T) (chainCfg (t := t) a L) (L + 1) l =
      st ⟨L + 1, 1, none, some 0⟩ := by
  obtain ⟨hd, hj⟩ := chain_inv (t := t) hinj (L + 1) le_rfl hLT l
  rw [state_core, hd, hj, if_pos (Or.inr rfl), if_neg]
  · simp only [chainCfg, if_neg (Ne.symm (hl 0 (Nat.zero_le _)))]
  · rintro ⟨k', hk', he⟩; exact hl k' (by omega) he

theorem chain_deciding (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l) (hL : L ≤ t) (hLT : L ≤ T) :
    Deciding (pmin T) (chainCfg (t := t) a L) L (a L) 0 := by
  obtain ⟨hd, hj⟩ := chain_inv (t := t) hinj L (by omega) hLT (a L)
  have hund : dec (pmin T) (chainCfg (t := t) a L) L (a L) = none := by
    rw [hd, if_neg]; rintro ⟨k', hk', he⟩; have := hinj k' (by omega) L le_rfl he; omega
  refine (deciding_iff' (chainCfg_valid hinj hL)).2 ⟨hund, ?_⟩
  rw [act_eq, if_neg (by simpa using hund), if_pos]
  rcases Nat.eq_zero_or_pos L with h0 | h0
  · left; subst h0; simp [chainCfg]
  · right; rw [hj, if_pos (Or.inl ⟨h0, le_rfl, rfl⟩)]

theorem chain_N_of (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l) {l : Fin n}
    (hl : ∀ k < L, a k ≠ l) : l ∈ (chainCfg (t := t) a L).pat.N := by
  rw [chainCfg_N]
  intro h
  obtain ⟨k, hk, he⟩ := Finset.mem_image.1 h
  exact hl k (Finset.mem_range.1 hk) he

section Impl

variable (hn : 2 ≤ n) (hT1 : T ≤ t + 1) (hT2 : T ≤ n - 1) (hT3 : t + 1 ≤ T ∨ n - 1 ≤ T)

/-- An undecided agent at time `m ≤ T` that has not heard of a `0` has local state
`⟨m, 1, ⊥, ⊥⟩`. -/
theorem state_of_undecided {c : (minCtx n t).Config} (hc : c.Valid) {m : ℕ} {i : Fin n}
    (hd : dec (pmin T) c m i = none) (h0 : ¬ (c.init i = 0 ∨
      ((minCtx n t).state (pmin T) c m i).1.jd = some 0)) (hm : m ≤ T) :
    (minCtx n t).state (pmin T) c m i = st ⟨m, 1, none, none⟩ := by
  push_neg at h0
  rw [state_core, hd]
  have h1 : c.init i = 1 := by rcases val_cases (c.init i) with h | h; exact absurd h h0.1; exact h
  have hj : ((minCtx n t).state (pmin T) c m i).1.jd = none := by
    cases h : ((minCtx n t).state (pmin T) c m i).1.jd with
    | none => rfl
    | some v =>
      rcases val_cases v with rfl | rfl
      · exact absurd h h0.2
      · exact absurd h (jd_ne_one hc hm)
  rw [h1, hj]

include hT3 in
/-- At time `T`, an undecided agent that has not heard of a `0` knows that nobody decides `0`. -/
theorem otest_at_T {c : (minCtx n t).Config} (hc : c.Valid) {i : Fin n}
    (hd : dec (pmin T) c T i = none) (h0 : ¬ (c.init i = 0 ∨
      ((minCtx n t).state (pmin T) c T i).1.jd = some 0)) :
    OTest (pmin T) i ((minCtx n t).state (pmin T) c T i) := by
  push_neg at h0
  intro c' hc' m' hs j
  have hm := time_eq_of_state_eq hs
  rw [hm] at hs
  have hd' : dec (pmin T) c' T i = none := by simp only [dec, hs]; exact hd
  have h1 : c'.init i = 1 := by
    rw [init_eq_of_state_eq hs]
    rcases val_cases (c.init i) with h | h; exact absurd h h0.1; exact h
  rw [hm]
  exact no_zero_at_T hc' hT3 hd' h1 (by rw [hs]; exact h0.2) j

include hn hT1 hT2 hT3 in
/-- **`P^min_T` implements `P0`** in `γ_min,n,t` when `T ≤ t + 1`, `T ≤ n - 1` and
(`t + 1 ≤ T` or `n - 1 ≤ T`). -/
theorem pmin_implements : Implements (pmin (n := n) (t := t) T) := by
  have hZ := zeroBiased (n := n) (t := t) hT3
  intro c hc m i
  by_cases hd : dec (pmin T) c m i ≠ none
  · rw [oneShot i _ hd, P0, if_pos hd]
  push_neg at hd
  rw [P0_of_undecided _ _ _ hd, act_eq, if_neg (by simpa using hd)]
  by_cases h0 : c.init i = 0 ∨ ((minCtx n t).state (pmin T) c m i).1.jd = some 0
  · rw [if_pos h0, if_pos]
    rcases h0 with h0 | h0
    · left; simpa using h0
    · right; exact knows_of_jd oneShot.oneShotOn h0
  have hZf : ¬ ZTest (pmin T) i ((minCtx n t).state (pmin T) c m i) := by
    rintro (h | h)
    · exact h0 (Or.inl (by simpa using h))
    · refine hZ.not_knows_jDecided (t := t) rfl silent initIndep hc ?_ h
      rw [dec_succ, act_eq, if_neg (by simpa using hd), if_neg h0]
      split_ifs <;> simp [newDec, hd]
  rw [if_neg h0, if_neg hZf]
  by_cases hmT : m = T
  · rw [if_pos hmT, if_pos]
    subst hmT; exact otest_at_T hT3 hc hd h0
  · rw [if_neg hmT, if_neg]
    have hm : m < T := lt_of_le_of_ne (le_of_undecided hc hd) hmT
    obtain ⟨a, hai, hinj⟩ := exists_seq_avoid i
    have hinj' : ∀ k ≤ m, ∀ l ≤ m, a k = a l → k = l :=
      fun k hk l hl he => hinj k (by omega) l (by omega) he
    intro hK
    refine hK (chainCfg (t := t) a m) (chainCfg_valid hinj' (by omega)) m ?_ (a m)
      (chain_deciding hinj' (by omega) (by omega))
    rw [chain_state_other hinj' (by omega) (fun k hk => hai k (by omega)),
      state_of_undecided hc hd h0 (by omega)]

include hn hT1 hT2 hT3 in
/-- **Safety condition (2)** for `P^min_T` (and hence for every implementation of `P0`). -/
theorem pmin_safe : SafeWrt (ReceivedChain (pmin (n := n) (t := t) T)) (pmin T) := by
  have hP := pmin_implements hn hT1 hT2 hT3
  have hZ := zeroBiased (n := n) (t := t) hT3
  refine ⟨hP.safe_one rfl silent initIndep, ?_⟩
  intro c hc m i hK hd
  have hmT := le_of_undecided hc hd
  by_cases h0 : c.init i = 0 ∨ ((minCtx n t).state (pmin T) c m i).1.jd = some 0
  · -- `i` is deciding `0`
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      have hi0 : c.init i = 0 := by
        rcases h0 with h | h
        · exact h
        · rw [jd_zero] at h; cases h
      have hinj : ∀ k ≤ 0, ∀ l ≤ 0, (fun _ => i) k = (fun _ : ℕ => i) l → k = l :=
        fun k hk l hl _ => by omega
      refine ⟨chainCfg (t := t) (fun _ => i) 0, chainCfg_valid hinj (Nat.zero_le _), ?_,
        chain_N_of hinj (fun k hk => by omega), i, chain_N_of hinj (fun k hk => by omega),
        chain_deciding (a := fun _ => i) hinj (Nat.zero_le _) (Nat.zero_le _), fun h => by omega⟩
      rw [state_eq_iff]
      simp [state_zero, chainCfg, hi0]
    · have hi1 : c.init i ≠ 0 := by
        intro h
        have := dec_stable oneShot.oneShotOn hc (hZ.init0 c hc 0 i rfl h).2 m (by omega)
        rw [hd] at this; cases this
      have hj : ((minCtx n t).state (pmin T) c m i).1.jd = some 0 := by tauto
      obtain ⟨b, hbi, hinj⟩ := exists_seq_avoid i
      have hinj' : ∀ k ≤ m - 1, ∀ l ≤ m - 1, b k = b l → k = l :=
        fun k hk l hl he => hinj k (by omega) l (by omega) he
      have hc' := chainCfg_valid (t := t) hinj' (by omega)
      have hs : (minCtx n t).state (pmin T) (chainCfg (t := t) b (m - 1)) m i =
          (minCtx n t).state (pmin T) c m i := by
        have := chain_state_next (t := t) (T := T) hinj' (show m - 1 + 1 ≤ T by omega)
          (fun k hk => hbi k (by omega))
        rw [Nat.sub_add_cancel hm0] at this
        rw [this, state_core, hd, hj]
        have : c.init i = 1 := by rcases val_cases (c.init i) with h | h; exact absurd h hi1; exact h
        rw [this]
      have hiN : i ∈ (chainCfg (t := t) b (m - 1)).pat.N := chain_N_of hinj' (fun k hk => hbi k (by omega))
      refine ⟨_, hc', hs, hiN, i, hiN, ?_, fun _ => ⟨_, hc', b (m - 1), hiN,
        chain_N_of hinj' (fun k hk he => by have := hinj' k (by omega) (m - 1) le_rfl he; omega),
        rfl, chain_deciding hinj' (by omega) (by omega)⟩⟩
      refine hZ.jd0 _ hc' m i (by simp only [dec, hs]; exact hd) (by rw [hs]; exact hj)
  · -- `i` does not decide `0`; it cannot decide `1` either, so `m < T`
    have hm : m < T := by
      refine lt_of_le_of_ne hmT fun hmT' => ?_
      subst hmT'
      exact hK (otest_at_T hT3 hc hd h0)
    obtain ⟨a, hai, hinj⟩ := exists_seq_avoid i
    have hinj' : ∀ k ≤ m, ∀ l ≤ m, a k = a l → k = l :=
      fun k hk l hl he => hinj k (by omega) l (by omega) he
    have hc' := chainCfg_valid (t := t) hinj' (by omega)
    have hjN : a m ∈ (chainCfg (t := t) a m).pat.N :=
      chain_N_of hinj' (fun k hk he => by have := hinj' k (by omega) m le_rfl he; omega)
    refine ⟨_, hc', ?_, chain_N_of hinj' (fun k hk => hai k (by omega)), a m, hjN,
      chain_deciding hinj' (by omega) (by omega), fun hm1 => ?_⟩
    · rw [chain_state_other hinj' (by omega) (fun k hk => hai k (by omega)),
        state_of_undecided hc hd h0 (by omega)]
    · obtain ⟨b, hbi, hinjb⟩ := exists_seq_avoid (a m)
      have hinjb' : ∀ k ≤ m - 1, ∀ l ≤ m - 1, b k = b l → k = l :=
        fun k hk l hl he => hinjb k (by omega) l (by omega) he
      have hc'' := chainCfg_valid (t := t) hinjb' (by omega)
      refine ⟨_, hc'', b (m - 1), chain_N_of hinjb' (fun k hk => hbi k (by omega)),
        chain_N_of hinjb' (fun k hk he => by have := hinjb' k (by omega) (m - 1) le_rfl he; omega),
        ?_, chain_deciding hinjb' (by omega) (by omega)⟩
      have := chain_state_next (t := t) (T := T) hinjb' (show m - 1 + 1 ≤ T by omega)
        (fun k hk => hbi k (by omega))
      rw [Nat.sub_add_cancel hm1] at this
      rw [this, chain_state_end hinj' (by omega) hm1]

end Impl

/-- Undecided agents of `γ_min` cannot detect their own faultiness: making an undecided agent
nonfaulty does not change the run up to the current time. -/
theorem nfConsistent (P : (minCtx n t).Protocol) : NFConsistent P := by
  intro c hc m i hd
  let c' : (minCtx n t).Config :=
    ⟨⟨insert i c.pat.N, fun k l r => c.pat.F k l r || decide (l = i)⟩, c.init, c.x0⟩
  have hSO : c.pat ∈ SO n t := hc.1
  have hc' : c'.Valid := by
    refine ⟨⟨?_, ?_⟩, hc.2⟩
    · exact (Finset.card_le_card (Finset.sdiff_subset_sdiff le_rfl (Finset.subset_insert _ _))).trans hSO.1
    · intro k l r hF
      simp only [c', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hF
      simp only [c', Finset.mem_insert, not_or]
      exact ⟨hF.2, hSO.2 k l r hF.1⟩
  refine ⟨c', hc', rfl, Finset.mem_insert_self _ _, ?_⟩
  have key : ∀ k ≤ m, (minCtx n t).state P c' k = (minCtx n t).state P c k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have e := ih (by omega)
      have hi : P i ((minCtx n t).state P c k i) = .noop :=
        act_noop_of_dec_succ (dec_none_of_le_any hd hk)
      funext r
      have hr : rcv P c' k r = rcv P c k r := by
        funext l
        simp only [rcv, e]
        by_cases hl : l = i
        · subst hl; simp only [hi]; split_ifs <;> rfl
        · simp [c', hl]
      simp only [state_succ, e, hr]
  rw [key m le_rfl]

end Min

end Podc.OptimalEBAOmission
