import Papers.PODC2023.OptimalEBAOmission.MinCtx

/-!
# The basic context `γ_basic,n,t` and the protocol `P^basic` (Theorem 6.6)

`E_basic(n)`: local states `⟨time, init, decided, jd, #1⟩`, messages `{0, 1, (init,1)}`. An agent
deciding `v` sends `v` to everybody; an undecided agent with `init = 1` and `jd = ⊥` that does not
act sends `(init,1)` to everybody; otherwise nothing. `#1` is the number of `(init,1)` messages
received in the last round, or `0` if the agent has decided (we read "`decided_i = ⊥`" in the
paper's update rule as the value after the round) or received a `0`/`1`.

`P^basic` decides `0` on `init = 0 ∨ jd = 0` and `1` on `#1 > n - time ∨ jd = 1`.
-/

namespace Podc.OptimalEBAOmission

open Context

/-- Messages of `E_basic`: `val v` (= the message `v`, sent when deciding `v`) and `init1`
(= `(init, 1)`). -/
inductive BMsg where
  | val (v : Val)
  | init1
  deriving DecidableEq

/-- The tag of a basic message. -/
def BMsg.tag : BMsg → Option Val
  | .val v => some v
  | .init1 => none

/-- Does `s` have the form `⟨m, 1, ⊥, ⊥, k⟩`? -/
def BForm (s : Core) : Prop := s.init = 1 ∧ s.decided = none ∧ s.jd = none

instance (s : Core) : Decidable (BForm s) := by unfold BForm; infer_instance

/-- Message selection of `E_basic`. -/
def bμ (s : Core × ℕ) : Act → Option BMsg
  | .decide v => some (.val v)
  | .noop => if BForm s.1 then some .init1 else none

/-- Update of `#1`: the number of `(init,1)` messages received, or `0` if the agent has decided
or received `0`/`1`. -/
def bδX {n : ℕ} (s : Core × ℕ) (a : Act) (rcv : Fin n → Option BMsg) : ℕ :=
  if newDec s.1.decided a ≠ none ∨ ∃ j v, rcv j = some (.val v) then 0
  else (Finset.univ.filter (fun j => rcv j = some .init1)).card

/-- The basic EBA context `γ_basic,n,t = (E_basic(n), SO(t))`. -/
abbrev basicCtx (n t : ℕ) : Context n where
  X := ℕ
  M := BMsg
  tag := BMsg.tag
  initX _ _ := {0}
  initX_nonempty _ _ := ⟨0, rfl⟩
  μ _ s a _ := bμ s a
  μ_decide _ _ v _ := ⟨.val v, rfl, rfl⟩
  μ_noop _ s _ m h := by
    simp only [bμ] at h
    split_ifs at h
    cases h; rfl
  δX _ s a rcv := bδX s a rcv
  FM := SO n t

/-- `#1` at a local state. -/
def cnt {n t : ℕ} (s : (basicCtx n t).L) : ℕ := s.2

/-- The protocol `P^basic`:
```
if decided_i ≠ ⊥ then noop
else if init_i = 0 ∨ jd_i = 0 then decide_i(0)
else if #1_i > n - time_i ∨ jd_i = 1 then decide_i(1)
else noop
``` -/
def pbasic {n t : ℕ} : (basicCtx n t).Protocol := fun _ s =>
  if s.1.decided ≠ none then .noop
  else if s.1.init = 0 ∨ s.1.jd = some 0 then .decide 0
  else if (cnt s : ℤ) > (n : ℤ) - s.1.time ∨ s.1.jd = some 1 then .decide 1 else .noop

namespace Basic

variable {n t : ℕ}


theorem oneShot : OneShot (pbasic (n := n) (t := t)) := fun _ s h => by
  simp only [pbasic, if_pos h]

theorem silent : SilentAfterDecide (basicCtx n t) := fun _ s _ h => by
  show (if BForm s.1 then some BMsg.init1 else none) = none
  rw [if_neg]; exact fun hf => h hf.2.1

theorem initIndep : InitIndep (basicCtx n t) := fun _ _ => Iff.rfl

theorem act_eq (c : (basicCtx n t).Config) (m : ℕ) (i : Fin n) :
    pbasic i ((basicCtx n t).state pbasic c m i) =
      if dec pbasic c m i ≠ none then .noop
      else if c.init i = 0 ∨ ((basicCtx n t).state pbasic c m i).1.jd = some 0 then .decide 0
      else if ((cnt ((basicCtx n t).state pbasic c m i) : ℕ) : ℤ) > (n : ℤ) - m ∨
          ((basicCtx n t).state pbasic c m i).1.jd = some 1 then .decide 1
      else .noop := by
  simp only [pbasic, time_state, init_state, dec]

theorem cnt_zero (c : (basicCtx n t).Config) (hc : c.Valid) (i : Fin n) : cnt ((basicCtx n t).state pbasic c 0 i) = 0 :=
  hc.2 i

/-- The messages received by `i` in round `k + 1`, as basic messages. -/
noncomputable def brcv (c : (basicCtx n t).Config) (k : ℕ) (i : Fin n) : Fin n → Option BMsg := fun j =>
  if c.pat.F k j i then bμ ((basicCtx n t).state pbasic c k j)
    (pbasic j ((basicCtx n t).state pbasic c k j)) else none

theorem rcv_eq (c : (basicCtx n t).Config) (k : ℕ) (i : Fin n) :
    rcv pbasic c k i = brcv c k i := rfl

/-- The update of `#1`. -/
theorem cnt_succ (c : (basicCtx n t).Config) (k : ℕ) (i : Fin n) :
    cnt ((basicCtx n t).state pbasic c (k + 1) i) =
      bδX ((basicCtx n t).state pbasic c k i) (pbasic i ((basicCtx n t).state pbasic c k i))
        (brcv c k i) := rfl

theorem bμ_eq_init1_iff {s : Core × ℕ} {a : Act} : bμ s a = some .init1 ↔ a = .noop ∧ BForm s.1 := by
  cases a with
  | decide v => simp [bμ]
  | noop => simp only [bμ, true_and]; split_ifs <;> simp_all

/-- The agents delivering `(init,1)` to `i` in round `k + 1`. -/
theorem rcv_eq_init1_iff {c : (basicCtx n t).Config} {k : ℕ} {i j : Fin n} :
    brcv c k i j = some .init1 ↔
      c.pat.F k j i = true ∧ pbasic j ((basicCtx n t).state pbasic c k j) = .noop ∧
        BForm ((basicCtx n t).state pbasic c k j).1 := by
  simp only [brcv]
  split_ifs with hF
  · rw [bμ_eq_init1_iff]; simp [hF]
  · simp [hF]

section Run

variable {c : (basicCtx n t).Config} (hc : c.Valid)
include hc

theorem deciding_iff' {m : ℕ} {i : Fin n} {v : Val} :
    Deciding pbasic c m i v ↔ dec pbasic c m i = none ∧ pbasic i ((basicCtx n t).state pbasic c m i) = .decide v :=
  deciding_iff oneShot.oneShotOn hc

/-- `#1` is at most the number of agents sending `(init,1)`. -/
theorem cnt_succ_le {k : ℕ} {i : Fin n} :
    cnt ((basicCtx n t).state pbasic c (k + 1) i) ≤
      (Finset.univ.filter (fun j => pbasic j ((basicCtx n t).state pbasic c k j) = .noop ∧
        BForm ((basicCtx n t).state pbasic c k j).1)).card := by
  rw [cnt_succ]; unfold bδX
  split_ifs
  · exact Nat.zero_le _
  · apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact (rcv_eq_init1_iff.1 hj).2

theorem deciding_one {d : ℕ} {i : Fin n} (h : Deciding pbasic c d i 1) :
    (((cnt ((basicCtx n t).state pbasic c d i) : ℕ) : ℤ) > (n : ℤ) - d ∨ ((basicCtx n t).state pbasic c d i).1.jd = some 1) ∧
      c.init i = 1 ∧ ((basicCtx n t).state pbasic c d i).1.jd ≠ some 0 := by
  obtain ⟨hd, ha⟩ := (deciding_iff' hc).1 h
  rw [act_eq, if_neg (by simpa using hd)] at ha
  split_ifs at ha with h1 h2
  · cases ha
  · push_neg at h1
    exact ⟨h2, by rcases val_cases (c.init i) with h | h; exact absurd h h1.1; exact h, h1.2⟩

theorem prev {m : ℕ} {j : Fin n} (h : Deciding pbasic c (m + 1) j 0) :
    ∃ l, Deciding pbasic c m l 0 := by
  obtain ⟨hd, ha⟩ := (deciding_iff' hc).1 h
  have hinit : c.init j ≠ 0 := by
    intro h0
    have hD : Deciding pbasic c 0 j 0 := (deciding_iff' hc).2 ⟨rfl, by
      rw [act_eq, if_neg (by simp [dec_zero]), if_pos (Or.inl h0)]⟩
    exact absurd (deciding_unique oneShot.oneShotOn hc h hD).1 (by omega)
  rw [act_eq, if_neg (by simpa using hd)] at ha
  split_ifs at ha with h1 h2
  · rcases h1 with h1 | h1
    · exact absurd h1 hinit
    · obtain ⟨l, -, hl⟩ := (jd_succ_eq_zero_iff _ c m j).1 h1
      exact ⟨l, deciding_of_act oneShot.oneShotOn hc hl⟩
  · cases ha

theorem start {j : Fin n} (h : Deciding pbasic c 0 j 0) : c.init j = 0 := by
  obtain ⟨-, ha⟩ := (deciding_iff' hc).1 h
  rw [act_eq, if_neg (by simp [dec_zero])] at ha
  split_ifs at ha with h1 h2
  · rcases h1 with h1 | h1
    · exact h1
    · rw [jd_zero] at h1; cases h1
  · cases ha

/-- If some agent decides `0` at a time `≥ k`, then at most `n - (k + 1)` agents send `(init,1)`
in round `k + 1`, so every `#1` at time `k + 1` is at most `n - (k + 1)`. -/
theorem cnt_le_of_zero {k m : ℕ} {l : Fin n} (hl : Deciding pbasic c m l 0) (hkm : k ≤ m)
    (i : Fin n) : cnt ((basicCtx n t).state pbasic c (k + 1) i) ≤ n - (k + 1) := by
  have hOS := (oneShot (n := n) (t := t)).oneShotOn
  obtain ⟨b, -, hb, -⟩ := exists_chain_of_prev hOS (fun m j h => prev hc h) hc hl
  obtain ⟨a, -, hdec, hinj⟩ := exists_chain_of_prev hOS (fun m j h => prev hc h) hc (hb k hkm)
  refine (cnt_succ_le hc).trans ?_
  have hsub : Finset.univ.filter (fun j => pbasic j ((basicCtx n t).state pbasic c k j) = .noop ∧
      BForm ((basicCtx n t).state pbasic c k j).1) ⊆ Finset.univ \ (Finset.range (k + 1)).image a := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range,
      not_exists, not_and]
    intro k' hk' he
    subst he
    have hD := hdec k' (by omega)
    by_cases hk'k : k' = k
    · subst hk'k
      rw [((deciding_iff' hc).1 hD).2] at hj; exact absurd hj.1 (by simp)
    · have := dec_stable hOS hc hD.2 k (by omega)
      exact absurd hj.2.2.1 (by simp [this])
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_image_of_injOn, Finset.card_range]
  intro x hx y hy he
  simp only [Finset.coe_range, Set.mem_Iio] at hx hy
  exact hinj x (by omega) y (by omega) he

/-- A `0`-decision at time `m` needs `m + 1` distinct agents. -/
theorem lt_of_deciding_zero {m : ℕ} {l : Fin n} (hl : Deciding pbasic c m l 0) : m + 1 ≤ n := by
  obtain ⟨a, -, -, hinj⟩ := exists_chain_of_prev (oneShot (n := n) (t := t)).oneShotOn
    (fun m j h => prev hc h) hc hl
  have hcard : ((Finset.range (m + 1)).image a).card = m + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro x hx y hy he
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    exact hinj x (by omega) y (by omega) he
  have := Finset.card_le_univ ((Finset.range (m + 1)).image a)
  rw [hcard, Fintype.card_fin] at this
  exact this

/-- `#1 > n - d` at time `d` rules out `0`-decisions at times `≥ d - 1`. -/
theorem no_zero_of_cnt {d : ℕ} {i : Fin n}
    (h : ((cnt ((basicCtx n t).state pbasic c d i) : ℕ) : ℤ) > (n : ℤ) - d) {m : ℕ} (hm : d ≤ m + 1) (l : Fin n) :
    ¬ Deciding pbasic c m l 0 := by
  intro hl
  cases d with
  | zero => rw [cnt_zero c hc] at h; omega
  | succ k =>
    have := cnt_le_of_zero hc hl (show k ≤ m by omega) i
    have := lt_of_deciding_zero hc hl
    omega

/-- `0`-decisions happen strictly before `1`-decisions. -/
theorem zeroBeforeOne : ∀ d, ∀ {d' : ℕ} {i j : Fin n}, Deciding pbasic c d i 1 →
    Deciding pbasic c d' j 0 → d' < d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro d' i j h1 h0
    obtain ⟨hc1 | hc1, -, -⟩ := deciding_one hc h1
    · by_contra hle
      exact no_zero_of_cnt hc hc1 (show d ≤ d' + 1 by omega) j h0
    · cases d with
      | zero => rw [jd_zero] at hc1; cases hc1
      | succ k =>
        obtain ⟨l, -, hl⟩ := exists_of_jd_succ_eq_one _ c k i hc1
        have := ih k (by omega) (deciding_of_act oneShot.oneShotOn hc hl) h0
        omega

end Run

/-- `P^basic` is `0`-biased. -/
theorem zeroBiased : ZeroBiased (pbasic (n := n) (t := t)) where
  oneShot := oneShot.oneShotOn
  init0 c hc m i hd h0 := (deciding_iff' hc).2 ⟨hd, by
    rw [act_eq, if_neg (by simpa using hd), if_pos (Or.inl h0)]⟩
  jd0 c hc m i hd hj := (deciding_iff' hc).2 ⟨hd, by
    rw [act_eq, if_neg (by simpa using hd), if_pos (Or.inr hj)]⟩
  zeroBeforeOne c hc d d' i j h1 h0 := zeroBeforeOne hc d h1 h0
  prev c hc m j h := prev hc h
  start c hc j h := start hc h

/-- Local states of `γ_basic`. -/
theorem state_ext (P : (basicCtx n t).Protocol) (c : (basicCtx n t).Config) (m : ℕ) (i : Fin n) :
    (basicCtx n t).state P c m i =
      (⟨m, c.init i, dec P c m i, ((basicCtx n t).state P c m i).1.jd⟩,
        ((basicCtx n t).state P c m i).2) := by
  ext <;> simp [dec]

/-! ### Chain runs -/

/-- The run with a chain `a 0, …, a L` (as for `γ_min`) plus a set `E` of faulty agents that
never deliver anything: `a 0` has preference `0`, all others `1`; `a k` (`k < L`) delivers only
its `0` to `a (k + 1)`. -/
def chainCfgB (a : ℕ → Fin n) (L : ℕ) (E : Finset (Fin n)) : (basicCtx n t).Config :=
  ⟨⟨Finset.univ \ ((Finset.range L).image a ∪ E),
    fun k l r => decide (l ∉ (Finset.range L).image a ∪ E) ||
      (decide (l ∈ (Finset.range L).image a) && decide (l = a k) && decide (r = a (k + 1)))⟩,
    fun l => if l = a 0 then 0 else 1, fun _ => 0⟩

variable {a : ℕ → Fin n} {L : ℕ} {E : Finset (Fin n)}

theorem chainCfgB_valid (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l) (hL : L + E.card ≤ t) :
    (chainCfgB (t := t) a L E).Valid := by
  refine ⟨⟨?_, ?_⟩, fun _ => rfl⟩
  · simp only [chainCfgB]
    rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
    refine (Finset.card_union_le _ _).trans ?_
    have := (Finset.card_image_le (s := Finset.range L) (f := a))
    simp only [Finset.card_range] at this
    omega
  · intro k l r hF
    simp only [chainCfgB, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not] at hF
    simp only [chainCfgB, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    exact hF.1

theorem chainCfgB_N {l : Fin n} :
    l ∈ (chainCfgB (t := t) a L E).pat.N ↔ l ∉ (Finset.range L).image a ∪ E := by
  simp [chainCfgB]

theorem card_le_of_inj (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l) : L + 1 ≤ n := by
  have hcard : ((Finset.range (L + 1)).image a).card = L + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro x hx y hy he
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    exact hinj x (by omega) y (by omega) he
  have := Finset.card_le_univ ((Finset.range (L + 1)).image a)
  rw [hcard, Fintype.card_fin] at this
  exact this

/-- The run of `P^basic` on a chain configuration, up to time `L + 1`. -/
theorem chainB_inv (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l)
    (hE : ∀ e ∈ E, ∀ k ≤ L, a k ≠ e) :
    ∀ k ≤ L + 1, ∀ l,
      dec pbasic (chainCfgB (t := t) a L E) k l =
        (if ∃ k' < k, a k' = l then some 0 else none) ∧
      ((basicCtx n t).state pbasic (chainCfgB (t := t) a L E) k l).1.jd =
        (if (1 ≤ k ∧ k ≤ L ∧ a k = l) ∨ k = L + 1 then some 0 else none) ∧
      cnt ((basicCtx n t).state pbasic (chainCfgB (t := t) a L E) k l) =
        (if k = 0 ∨ (∃ k' < k, a k' = l) ∨ (1 ≤ k ∧ k ≤ L ∧ a k = l) ∨ k = L + 1 then 0
          else n - L - E.card) := by
  have hnL := card_le_of_inj hinj
  set A := (Finset.range L).image a with hA
  have hmemA : ∀ k ≤ L, a k ∈ A ↔ k < L := by
    intro k hk
    constructor
    · intro h
      obtain ⟨k', hk', he⟩ := Finset.mem_image.1 h
      simp only [Finset.mem_range] at hk'
      have := hinj k' (by omega) k hk he
      omega
    · intro h; exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 h, rfl⟩
  have hdisj : Disjoint A E := by
    rw [Finset.disjoint_left]
    intro x hx hxE
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    exact hE _ hxE k (by simp at hk; omega) rfl
  have hcardA : A.card = L := by
    rw [hA, Finset.card_image_of_injOn, Finset.card_range]
    intro x hx y hy he
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    exact hinj x (by omega) y (by omega) he
  intro k
  induction k with
  | zero => intro _ l; simp [dec_zero, jd_zero, cnt, state_zero, chainCfgB]
  | succ k ih =>
    intro hk
    have IH := ih (by omega)
    -- actions at time `k`
    have hact : ∀ l, pbasic l ((basicCtx n t).state pbasic (chainCfgB (t := t) a L E) k l) =
        if l = a k then .decide 0 else .noop := by
      intro l
      obtain ⟨hdl, hjl, hcl⟩ := IH l
      rw [act_eq]
      by_cases hl : l = a k
      · subst hl
        have hund : ¬ ∃ k' < k, a k' = a k := fun ⟨k', hk', he⟩ => by
          have := hinj k' (by omega) k (by omega) he; omega
        rw [hdl, if_neg hund, if_pos rfl]
        simp only [ne_eq, not_true_eq_false, if_false]
        rw [if_pos]
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · left; subst h0; simp [chainCfgB]
        · right; rw [hjl, if_pos (Or.inl ⟨h0, by omega, rfl⟩)]
      · rw [if_neg hl]
        by_cases hd : ∃ k' < k, a k' = l
        · rw [hdl, if_pos hd]; simp
        · rw [hdl, if_neg hd]
          simp only [ne_eq, not_true_eq_false, if_false]
          have hinit : (chainCfgB (t := t) a L E).init l ≠ 0 := by
            simp only [chainCfgB]
            split_ifs with h
            · exfalso; rcases Nat.eq_zero_or_pos k with h0 | h0
              · subst h0; exact hl h
              · exact hd ⟨0, h0, h.symm⟩
            · decide
          have hjd : ((basicCtx n t).state pbasic (chainCfgB (t := t) a L E) k l).1.jd = none := by
            rw [hjl]
            split_ifs with h
            · exfalso; rcases h with h | h
              · exact hl h.2.2.symm
              · omega
            · rfl
          have hcnt : ((cnt ((basicCtx n t).state pbasic (chainCfgB (t := t) a L E) k l) : ℕ) : ℤ) ≤
              (n : ℤ) - k := by
            rw [hcl]; split_ifs <;> omega
          rw [if_neg (by rw [hjd]; tauto), if_neg (by rw [hjd]; push_neg; exact ⟨by omega, by simp⟩)]
    have hdecs : ∀ l, dec pbasic (chainCfgB (t := t) a L E) (k + 1) l =
        if ∃ k' < k + 1, a k' = l then some 0 else none := by
      intro l
      rw [dec_succ, hact, (IH l).1]
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
    -- delivery of `a k`'s message
    have hF : ∀ r, (chainCfgB (t := t) a L E).pat.F k (a k) r = (decide (k = L) || decide (r = a (k + 1))) := by
      intro r
      have hEk : a k ∉ E := fun h => hE _ h k (by omega) rfl
      have hmem := hmemA k (by omega)
      show (decide (a k ∉ A ∪ E) || (decide (a k ∈ A) && decide (a k = a k) &&
        decide (r = a (k + 1)))) = _
      by_cases hkL : k = L
      · have hA' : a k ∉ A := by rw [hmem]; omega
        have : a k ∉ A ∪ E := by simp [Finset.mem_union, hA', hEk]
        rw [decide_eq_true this]; simp [hkL]
      · have hA' : a k ∈ A := by rw [hmem]; omega
        simp [Finset.mem_union, hA', hkL]
    have hval : ∀ r, (∃ j v, brcv (chainCfgB (t := t) a L E) k r j = some (.val v)) ↔
        (k = L ∨ r = a (k + 1)) := by
      intro r
      constructor
      · rintro ⟨j, v, h⟩
        simp only [brcv] at h
        split_ifs at h with hFj
        rw [hact] at h
        split_ifs at h with hj
        · subst hj; rw [hF] at hFj; simpa using hFj
        · simp [bμ] at h
      · intro h
        refine ⟨a k, 0, ?_⟩
        simp only [brcv, hF, hact, if_pos rfl]
        rcases h with h | h <;> simp [h, bμ]
    refine fun l => ⟨hdecs l, ?_, ?_⟩
    · by_cases hcond : k = L ∨ l = a (k + 1)
      · have : ((basicCtx n t).state pbasic (chainCfgB (t := t) a L E) (k + 1) l).1.jd = some 0 := by
          refine (jd_succ_eq_zero_iff _ _ k l).2 ⟨a k, ?_, by rw [hact, if_pos rfl]⟩
          rw [hF]; rcases hcond with h | h <;> simp [h]
        rw [this, if_pos]
        rcases hcond with h | h
        · right; omega
        · by_cases hkL : k = L
          · right; omega
          · left; exact ⟨by omega, by omega, h.symm⟩
      · push_neg at hcond
        have : ((basicCtx n t).state pbasic (chainCfgB (t := t) a L E) (k + 1) l).1.jd = none := by
          refine (jd_succ_eq_none_iff _ _ k l).2 fun j hj => ?_
          rw [hact]
          split_ifs with h
          · subst h; rw [hF] at hj; simp [hcond.1, hcond.2] at hj
          · rfl
        rw [this, if_neg]
        rintro (h | h)
        · exact hcond.2 h.2.2.symm
        · omega
    · rw [cnt_succ]
      unfold bδX
      have hnd : newDec (dec pbasic (chainCfgB (t := t) a L E) k l)
          (pbasic l ((basicCtx n t).state pbasic (chainCfgB (t := t) a L E) k l)) =
          dec pbasic (chainCfgB (t := t) a L E) (k + 1) l := (dec_succ _ _ _ _).symm
      rw [hnd]
      by_cases hc1 : dec pbasic (chainCfgB (t := t) a L E) (k + 1) l ≠ none ∨
          ∃ j v, brcv (chainCfgB (t := t) a L E) k l j = some (.val v)
      · rw [if_pos hc1, if_pos]
        rcases hc1 with h | h
        · rw [hdecs l] at h; right; left; by_contra hne; exact h (by rw [if_neg hne])
        · rcases (hval l).1 h with h2 | h2
          · right; right; right; omega
          · by_cases hkL : k = L
            · right; right; right; omega
            · right; right; left; exact ⟨by omega, by omega, h2.symm⟩
      have h1 : ¬ ∃ k' < k + 1, a k' = l := fun h =>
        hc1 (Or.inl (by rw [hdecs l, if_pos h]; simp))
      have h2 : ¬ (k = L ∨ l = a (k + 1)) := fun h => hc1 (Or.inr ((hval l).2 h))
      push_neg at h2
      rw [if_neg hc1, if_neg]
      swap
      · rintro (h | h | h | h)
        · omega
        · exact h1 h
        · exact h2.2 h.2.2.symm
        · omega
      have hkL : k < L := by omega
      -- the `(init,1)` messages received by `l`
      have hset : Finset.univ.filter (fun j => brcv (chainCfgB (t := t) a L E) k l j = some .init1) =
          Finset.univ \ (A ∪ E) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
        rw [rcv_eq_init1_iff, hact]
        obtain ⟨hdj, hjj, -⟩ := IH j
        constructor
        · rintro ⟨hFj, hnoop, -⟩ hmem
          change (decide (j ∉ A ∪ E) || (decide (j ∈ A) && decide (j = a k) &&
            decide (l = a (k + 1)))) = true at hFj
          simp only [hmem, not_true_eq_false, decide_false, Bool.false_or, Bool.and_eq_true,
            decide_eq_true_eq] at hFj
          rw [if_pos hFj.1.2] at hnoop; cases hnoop
        · intro hj
          have hnA : ∀ k' < L, a k' ≠ j := fun k' hk' he =>
            hj (Finset.mem_union_left _ (he ▸ (hmemA k' (by omega)).2 hk'))
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · change (decide (j ∉ A ∪ E) || _) = true
            simp [hj]
          · rw [if_neg (Ne.symm (hnA k hkL))]
          · simp only [init_state, chainCfgB, if_neg (Ne.symm (hnA 0 (by omega)))]
          · show dec pbasic _ k j = none
            rw [hdj, if_neg]; rintro ⟨k', hk', he⟩; exact hnA k' (by omega) he
          · rw [hjj, if_neg]
            rintro (h | h)
            · exact hnA k hkL h.2.2
            · omega
      rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, Finset.card_union_of_disjoint hdisj, hcardA]
      omega

theorem chainB_state_other (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l)
    (hE : ∀ e ∈ E, ∀ k ≤ L, a k ≠ e) {l : Fin n} (hl : ∀ k ≤ L, a k ≠ l) :
    (basicCtx n t).state pbasic (chainCfgB (t := t) a L E) L l =
      (⟨L, 1, none, none⟩, if L = 0 then 0 else n - L - E.card) := by
  obtain ⟨hd, hj, hcn⟩ := chainB_inv (t := t) hinj hE L (by omega) l
  rw [state_ext, hd, hj, if_neg, if_neg]
  · have h1 : (chainCfgB (t := t) a L E).init l = 1 := by
      simp only [chainCfgB, if_neg (Ne.symm (hl 0 (Nat.zero_le _)))]
    rw [h1]
    congr 1
    change cnt _ = _
    rw [hcn]
    by_cases hL : L = 0
    · simp [hL]
    · rw [if_neg, if_neg hL]
      rintro (h | ⟨k', hk', he⟩ | h | h)
      · exact hL h
      · exact hl k' (by omega) he
      · exact hl L le_rfl h.2.2
      · omega
  · rintro (h | h)
    · exact hl L le_rfl h.2.2
    · omega
  · rintro ⟨k', hk', he⟩; exact hl k' (by omega) he

theorem chainB_state_end (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l)
    (hE : ∀ e ∈ E, ∀ k ≤ L, a k ≠ e) (hL1 : 1 ≤ L) :
    (basicCtx n t).state pbasic (chainCfgB (t := t) a L E) L (a L) = (⟨L, 1, none, some 0⟩, 0) := by
  obtain ⟨hd, hj, hcn⟩ := chainB_inv (t := t) hinj hE L (by omega) (a L)
  rw [state_ext, hd, hj, if_pos (Or.inl ⟨hL1, le_rfl, rfl⟩), if_neg]
  · have : a L ≠ a 0 := fun h => by have := hinj L le_rfl 0 (Nat.zero_le _) h; omega
    have h1 : (chainCfgB (t := t) a L E).init (a L) = 1 := by simp only [chainCfgB, if_neg this]
    rw [h1]
    congr 1
    change cnt _ = _
    rw [hcn, if_pos (Or.inr (Or.inr (Or.inl ⟨hL1, le_rfl, rfl⟩)))]
  · rintro ⟨k', hk', he⟩; have := hinj k' (by omega) L le_rfl he; omega

theorem chainB_state_next (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l)
    (hE : ∀ e ∈ E, ∀ k ≤ L, a k ≠ e) {l : Fin n} (hl : ∀ k ≤ L, a k ≠ l) :
    (basicCtx n t).state pbasic (chainCfgB (t := t) a L E) (L + 1) l =
      (⟨L + 1, 1, none, some 0⟩, 0) := by
  obtain ⟨hd, hj, hcn⟩ := chainB_inv (t := t) hinj hE (L + 1) le_rfl l
  rw [state_ext, hd, hj, if_pos (Or.inr rfl), if_neg]
  · have h1 : (chainCfgB (t := t) a L E).init l = 1 := by
      simp only [chainCfgB, if_neg (Ne.symm (hl 0 (Nat.zero_le _)))]
    rw [h1]
    congr 1
    change cnt _ = _
    rw [hcn, if_pos (Or.inr (Or.inr (Or.inr rfl)))]
  · rintro ⟨k', hk', he⟩; exact hl k' (by omega) he

theorem chainB_deciding (hinj : ∀ k ≤ L, ∀ l ≤ L, a k = a l → k = l)
    (hE : ∀ e ∈ E, ∀ k ≤ L, a k ≠ e) (hL : L + E.card ≤ t) :
    Deciding pbasic (chainCfgB (t := t) a L E) L (a L) 0 := by
  obtain ⟨hd, hj, -⟩ := chainB_inv (t := t) hinj hE L (by omega) (a L)
  have hund : dec pbasic (chainCfgB (t := t) a L E) L (a L) = none := by
    rw [hd, if_neg]; rintro ⟨k', hk', he⟩; have := hinj k' (by omega) L le_rfl he; omega
  refine (deciding_iff' (chainCfgB_valid hinj hL)).2 ⟨hund, ?_⟩
  rw [act_eq, if_neg (by simpa using hund), if_pos]
  rcases Nat.eq_zero_or_pos L with h0 | h0
  · left; subst h0; simp [chainCfgB]
  · right; rw [hj, if_pos (Or.inl ⟨h0, le_rfl, rfl⟩)]

theorem chainB_N_of {l : Fin n} (hl : ∀ k < L, a k ≠ l) (hlE : l ∉ E) :
    l ∈ (chainCfgB (t := t) a L E).pat.N := by
  rw [chainCfgB_N, Finset.mem_union, not_or]
  refine ⟨fun h => ?_, hlE⟩
  obtain ⟨k, hk, he⟩ := Finset.mem_image.1 h
  exact hl k (Finset.mem_range.1 hk) he

end Basic

/-! ### Reachable states and Theorem 6.6 -/

namespace Basic

variable {n t : ℕ}

/-- `#1 = 0` after receiving a `0` or `1`. -/
theorem cnt_eq_zero_of_jd {c : (basicCtx n t).Config} {k : ℕ} {i : Fin n}
    (h : ((basicCtx n t).state pbasic c (k + 1) i).1.jd ≠ none) :
    cnt ((basicCtx n t).state pbasic c (k + 1) i) = 0 := by
  rw [cnt_succ]; unfold bδX
  rw [if_pos]
  right
  rw [jd_succ, Ne, jdOf_eq_none_iff] at h
  push_neg at h
  obtain ⟨j, msg, hm, ht⟩ := h
  cases msg with
  | val v => exact ⟨j, v, hm⟩
  | init1 => exact absurd rfl ht

section Reach

variable {c : (basicCtx n t).Config} (hc : c.Valid)
include hc

/-- An undecided agent acts on `jd ≠ ⊥`. -/
theorem act_of_jd {m : ℕ} {i : Fin n} (hd : dec pbasic c m i = none)
    (hj : ((basicCtx n t).state pbasic c m i).1.jd ≠ none) :
    pbasic i ((basicCtx n t).state pbasic c m i) ≠ .noop := by
  rw [act_eq, if_neg (by simpa using hd)]
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hj
  rcases val_cases v with rfl | rfl
  · rw [if_pos (Or.inr hv)]; simp
  · split_ifs <;> simp_all

/-- **Reachable states.** An undecided agent with `jd = ⊥` at a time `m ≥ 1` has `#1 ≥ n - t`:
every nonfaulty agent sent it `(init, 1)`. -/
theorem cnt_ge {k : ℕ} {i : Fin n} (hd : dec pbasic c (k + 1) i = none)
    (hj : ((basicCtx n t).state pbasic c (k + 1) i).1.jd = none) :
    n - t ≤ cnt ((basicCtx n t).state pbasic c (k + 1) i) := by
  have hSO : c.pat ∈ SO n t := hc.1
  have hdk : dec pbasic c k i = none := dec_none_of_le_any hd (by omega)
  have hnoop := act_noop_of_dec_succ hd
  have hall := (jd_succ_eq_none_iff _ c k i).1 hj
  rw [cnt_succ]; unfold bδX
  rw [if_neg]
  swap
  · rintro (h | ⟨j, v, h⟩)
    · rw [hnoop] at h; exact h hdk
    · simp only [brcv] at h
      split_ifs at h with hF
      rw [hall j hF] at h
      simp [bμ] at h
  have hsub : c.pat.N ⊆ Finset.univ.filter (fun j => brcv c k i j = some .init1) := by
    intro j hjN
    have hF : c.pat.F k j i = true := by
      by_contra h; exact hSO.2 k j i (by simpa using h) hjN
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rcv_eq_init1_iff]
    have hjnoop := hall j hF
    -- `j` is undecided at time `k`
    have hdj : dec pbasic c k j = none := by
      by_contra hne
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hne
      obtain ⟨d, hdk', hD⟩ := exists_deciding oneShot.oneShotOn hc hv
      have hact := ((deciding_iff' hc).1 hD).2
      have hjd : ((basicCtx n t).state pbasic c (d + 1) i).1.jd ≠ none := by
        intro hn
        have := (jd_succ_eq_none_iff _ c d i).1 hn j (by
          by_contra h; exact hSO.2 d j i (by simpa using h) hjN)
        rw [hact] at this; cases this
      have hdi : dec pbasic c (d + 1) i = none := dec_none_of_le_any hdk (by omega)
      have := act_of_jd hc hdi hjd
      have hdi2 : dec pbasic c (d + 2) i = none := dec_none_of_le_any hd (by omega)
      exact this (act_noop_of_dec_succ hdi2)
    refine ⟨hF, hjnoop, ?_, hdj, ?_⟩
    · simp only [init_state]
      rcases val_cases (c.init j) with h | h
      · exfalso
        rw [act_eq, if_neg (by simpa using hdj), if_pos (Or.inl h)] at hjnoop; cases hjnoop
      · exact h
    · by_contra hne
      exact act_of_jd hc hdj hne hjnoop
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ \ c.pat.N).card = n - c.pat.N.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have h3 := hSO.1
  have h4 := Finset.card_le_univ c.pat.N
  rw [Fintype.card_fin] at h4
  omega

/-- Every agent has decided after `t + 1` rounds. -/
theorem le_of_undecided {m : ℕ} {i : Fin n} (hd : dec pbasic c m i = none) : m ≤ t + 1 := by
  by_contra hlt
  have h1 : dec pbasic c (t + 1) i = none := dec_none_of_le_any hd (by omega)
  have h2 : dec pbasic c (t + 2) i = none := dec_none_of_le_any hd (by omega)
  have hnoop := act_noop_of_dec_succ h2
  by_cases hj : ((basicCtx n t).state pbasic c (t + 1) i).1.jd = none
  · have hcnt := cnt_ge hc h1 hj
    rw [act_eq, if_neg (by simpa using h1)] at hnoop
    split_ifs at hnoop with ha hb
    push_neg at ha hb
    have := hb.1
    simp only [time_state, Nat.cast_add, Nat.cast_one] at this
    omega
  · exact act_of_jd hc h1 hj hnoop

end Reach

section Impl

variable (ht : t + 2 ≤ n)

/-- `P^basic`'s rule for deciding `1` is sound: nobody decides `0` at that time. -/
theorem otest {c : (basicCtx n t).Config} (hc : c.Valid) {m : ℕ} {i : Fin n}
    (h1 : ((cnt ((basicCtx n t).state pbasic c m i) : ℕ) : ℤ) > (n : ℤ) - m ∨
      ((basicCtx n t).state pbasic c m i).1.jd = some 1) :
    OTest pbasic i ((basicCtx n t).state pbasic c m i) := by
  intro c' hc' m' hs j hj
  have hm := time_eq_of_state_eq hs
  rw [hm] at hs hj
  rcases h1 with h1 | h1
  · rw [← hs] at h1
    exact no_zero_of_cnt hc' h1 (by omega) j hj
  · rw [← hs] at h1
    cases m with
    | zero => rw [jd_zero] at h1; cases h1
    | succ k =>
      obtain ⟨l, -, hl⟩ := exists_of_jd_succ_eq_one _ c' k i h1
      have := zeroBeforeOne hc' k (deciding_of_act oneShot.oneShotOn hc' hl) hj
      omega

/-- The local state of an undecided agent that does not act. -/
theorem state_of_noop {c : (basicCtx n t).Config} {m : ℕ} {i : Fin n}
    (hd : dec pbasic c m i = none)
    (h0 : ¬ (c.init i = 0 ∨ ((basicCtx n t).state pbasic c m i).1.jd = some 0))
    (h1 : ¬ (((cnt ((basicCtx n t).state pbasic c m i) : ℕ) : ℤ) > (n : ℤ) - m ∨
      ((basicCtx n t).state pbasic c m i).1.jd = some 1)) :
    (basicCtx n t).state pbasic c m i =
      (⟨m, 1, none, none⟩, cnt ((basicCtx n t).state pbasic c m i)) := by
  push_neg at h0 h1
  rw [state_ext, hd]
  have hi : c.init i = 1 := by rcases val_cases (c.init i) with h | h; exact absurd h h0.1; exact h
  have hj : ((basicCtx n t).state pbasic c m i).1.jd = none := by
    cases h : ((basicCtx n t).state pbasic c m i).1.jd with
    | none => rfl
    | some v =>
      rcases val_cases v with rfl | rfl
      · exact absurd h h0.2
      · exact absurd h h1.2
  rw [hi, hj]; rfl

include ht in
/-- A run with a nonfaulty agent `j ≠ i` deciding `0` at time `m` in which `i` (nonfaulty) has the
local state `⟨m, 1, ⊥, ⊥, κ⟩` of a reachable undecided agent that does not act; and, if `m ≥ 1`, a
second run in which `j` has the same state and some nonfaulty agent decides `0` at `m - 1`. -/
theorem exists_chain_run {c : (basicCtx n t).Config} (hc : c.Valid) {m : ℕ} {i : Fin n}
    (hd : dec pbasic c m i = none)
    (h0 : ¬ (c.init i = 0 ∨ ((basicCtx n t).state pbasic c m i).1.jd = some 0))
    (h1 : ¬ (((cnt ((basicCtx n t).state pbasic c m i) : ℕ) : ℤ) > (n : ℤ) - m ∨
      ((basicCtx n t).state pbasic c m i).1.jd = some 1)) :
    ∃ c' : (basicCtx n t).Config, c'.Valid ∧
      (basicCtx n t).state pbasic c' m i = (basicCtx n t).state pbasic c m i ∧ i ∈ c'.pat.N ∧
      ∃ j ∈ c'.pat.N, Deciding pbasic c' m j 0 ∧
        (1 ≤ m → ∃ c'' : (basicCtx n t).Config, c''.Valid ∧ ∃ j', j ∈ c''.pat.N ∧
          j' ∈ c''.pat.N ∧ (basicCtx n t).state pbasic c'' m j =
            (basicCtx n t).state pbasic c' m j ∧ Deciding pbasic c'' (m - 1) j' 0) := by
  have hs := state_of_noop hd h0 h1
  set κ := cnt ((basicCtx n t).state pbasic c m i) with hκ
  have hκle : κ + m ≤ n := by
    push_neg at h1; have := h1.1; omega
  obtain ⟨a, hai, hinj⟩ := exists_seq_avoid i
  -- the set `E` of silent faulty agents
  have hκ2 : m = 0 ∨ (2 ≤ κ ∧ m ≤ n - 2 ∧ n - t ≤ κ ∧ 0 < m) := by
    rcases Nat.eq_zero_or_pos m with h | h
    · left; exact h
    · right
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hj : ((basicCtx n t).state pbasic c (k + 1) i).1.jd = none := by
        have := congrArg (fun s : (basicCtx n t).L => s.1.jd) hs; simpa using this
      have := cnt_ge hc hd hj
      omega
  have hm2 : m ≤ n - 2 := by rcases hκ2 with h | h; omega; exact h.2.1
  have hinj' : ∀ k ≤ m, ∀ l ≤ m, a k = a l → k = l :=
    fun k hk l hl he => hinj k (by omega) l (by omega) he
  let C := Finset.univ \ insert i ((Finset.range (m + 1)).image a)
  have hCcard : C.card = n - (m + 2) := by
    have hcard : ((Finset.range (m + 1)).image a).card = m + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro x hx y hy he
      simp only [Finset.coe_range, Set.mem_Iio] at hx hy
      exact hinj' x (by omega) y (by omega) he
    have hi : i ∉ (Finset.range (m + 1)).image a := by
      simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
      exact fun k hk => hai k (by omega)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem hi, hcard]
  obtain ⟨E, hEC, hEcard⟩ : ∃ E ⊆ C, E.card = if m = 0 then 0 else n - m - κ := by
    apply Finset.exists_subset_card_eq
    rw [hCcard]
    rcases hκ2 with h | h
    · simp [h]
    · rw [if_neg (by omega)]; omega
  have hE : ∀ e ∈ E, ∀ k ≤ m, a k ≠ e := by
    intro e he k hk hke
    have := hEC he
    simp only [C, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image,
      Finset.mem_range, not_or, not_exists, not_and] at this
    exact this.2 k (by omega) hke
  have hiE : i ∉ E := by
    intro h; have := hEC h; simp [C] at this
  have hfaulty : m + E.card ≤ t := by
    rw [hEcard]; rcases hκ2 with h | h
    · simp [h]
    · rw [if_neg (by omega)]; omega
  have hc' := chainCfgB_valid (t := t) hinj' hfaulty
  have hjN : a m ∈ (chainCfgB (t := t) a m E).pat.N :=
    chainB_N_of (fun k hk he => by have := hinj' k (by omega) m le_rfl he; omega)
      (fun h => hE _ h m le_rfl rfl)
  refine ⟨_, hc', ?_, chainB_N_of (fun k hk => hai k (by omega)) hiE, a m, hjN,
    chainB_deciding hinj' hE hfaulty, fun hm1 => ?_⟩
  · rw [chainB_state_other hinj' hE (fun k hk => hai k (by omega)), hs, hEcard]
    congr 1
    by_cases h : m = 0
    · subst h; simp only [if_true]
      rw [hκ, show (0 : ℕ) = 0 + 0 from rfl]
      have := cnt_zero c hc i
      exact this.symm
    · rw [if_neg h, if_neg h]; omega
  · obtain ⟨b, hbi, hinjb⟩ := exists_seq_avoid (a m)
    have hinjb' : ∀ k ≤ m - 1, ∀ l ≤ m - 1, b k = b l → k = l :=
      fun k hk l hl he => hinjb k (by omega) l (by omega) he
    have hE0 : ∀ e ∈ (∅ : Finset (Fin n)), ∀ k ≤ m - 1, b k ≠ e := by simp
    have hf0 : m - 1 + (∅ : Finset (Fin n)).card ≤ t := by
      simp only [Finset.card_empty, add_zero]; omega
    refine ⟨_, chainCfgB_valid (t := t) hinjb' hf0, b (m - 1),
      chainB_N_of (fun k hk => hbi k (by omega)) (Finset.notMem_empty _),
      chainB_N_of (fun k hk he => by have := hinjb' k (by omega) (m - 1) le_rfl he; omega)
        (Finset.notMem_empty _), ?_, chainB_deciding hinjb' hE0 hf0⟩
    have := chainB_state_next (t := t) hinjb' hE0 (fun k hk => hbi k (by omega))
    rw [Nat.sub_add_cancel hm1] at this
    rw [this, chainB_state_end hinj' hE hm1]

include ht in
/-- **Theorem 6.6.** If `t ≤ n - 2`, then `P^basic` implements `P0` in `γ_basic,n,t`. -/
theorem thm_6_6 : Implements (pbasic (n := n) (t := t)) := by
  have hZ := zeroBiased (n := n) (t := t)
  intro c hc m i
  by_cases hd : dec pbasic c m i ≠ none
  · rw [oneShot i _ hd, P0, if_pos hd]
  push_neg at hd
  rw [P0_of_undecided _ _ _ hd, act_eq, if_neg (by simpa using hd)]
  by_cases h0 : c.init i = 0 ∨ ((basicCtx n t).state pbasic c m i).1.jd = some 0
  · rw [if_pos h0, if_pos]
    rcases h0 with h0 | h0
    · left; simpa using h0
    · right; exact knows_of_jd oneShot.oneShotOn h0
  have hZf : ¬ ZTest pbasic i ((basicCtx n t).state pbasic c m i) := by
    rintro (h | h)
    · exact h0 (Or.inl (by simpa using h))
    · refine hZ.not_knows_jDecided (t := t) rfl silent initIndep hc ?_ h
      rw [dec_succ, act_eq, if_neg (by simpa using hd), if_neg h0]
      split_ifs <;> simp [newDec, hd]
  rw [if_neg h0, if_neg hZf]
  by_cases h1 : ((cnt ((basicCtx n t).state pbasic c m i) : ℕ) : ℤ) > (n : ℤ) - m ∨
      ((basicCtx n t).state pbasic c m i).1.jd = some 1
  · rw [if_pos h1, if_pos (otest hc h1)]
  · rw [if_neg h1, if_neg]
    intro hK
    obtain ⟨c', hc', hs, -, j, -, hj, -⟩ := exists_chain_run ht hc hd h0 h1
    exact hK c' hc' m hs j hj

include ht in
/-- **Safety condition (2)** for `P^basic`. -/
theorem safe : SafeWrt (ReceivedChain (pbasic (n := n) (t := t))) pbasic := by
  have hP := thm_6_6 (n := n) (t := t) ht
  have hZ := zeroBiased (n := n) (t := t)
  refine ⟨hP.safe_one rfl silent initIndep, ?_⟩
  intro c hc m i hK hd
  by_cases h0 : c.init i = 0 ∨ ((basicCtx n t).state pbasic c m i).1.jd = some 0
  · -- `i` is deciding `0`
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      have hi0 : c.init i = 0 := by
        rcases h0 with h | h
        · exact h
        · rw [jd_zero] at h; cases h
      have hinj : ∀ k ≤ 0, ∀ l ≤ 0, (fun _ => i) k = (fun _ : ℕ => i) l → k = l :=
        fun k hk l hl _ => by omega
      have hE0 : ∀ e ∈ (∅ : Finset (Fin n)), ∀ k ≤ 0, (fun _ : ℕ => i) k ≠ e := by simp
      have hf0 : 0 + (∅ : Finset (Fin n)).card ≤ t := by simp
      have hiN : i ∈ (chainCfgB (t := t) (fun _ => i) 0 ∅).pat.N :=
        chainB_N_of (fun k hk => by omega) (Finset.notMem_empty _)
      refine ⟨chainCfgB (t := t) (fun _ => i) 0 ∅, chainCfgB_valid hinj hf0, ?_, hiN, i, hiN,
        chainB_deciding (a := fun _ => i) hinj hE0 hf0, fun h => by omega⟩
      rw [state_zero, state_zero]
      simp [chainCfgB, hi0, hc.2 i]
      exact (hc.2 i).symm
    · have hi1 : c.init i ≠ 0 := by
        intro h
        have := dec_stable oneShot.oneShotOn hc (hZ.init0 c hc 0 i rfl h).2 m (by omega)
        rw [hd] at this; cases this
      have hj : ((basicCtx n t).state pbasic c m i).1.jd = some 0 := by tauto
      have hmt := le_of_undecided hc hd
      obtain ⟨b, hbi, hinj⟩ := exists_seq_avoid i
      have hinj' : ∀ k ≤ m - 1, ∀ l ≤ m - 1, b k = b l → k = l :=
        fun k hk l hl he => hinj k (by omega) l (by omega) he
      have hE0 : ∀ e ∈ (∅ : Finset (Fin n)), ∀ k ≤ m - 1, b k ≠ e := by simp
      have hf0 : m - 1 + (∅ : Finset (Fin n)).card ≤ t := by simp; omega
      have hc' := chainCfgB_valid (t := t) hinj' hf0
      have hs : (basicCtx n t).state pbasic (chainCfgB (t := t) b (m - 1) ∅) m i =
          (basicCtx n t).state pbasic c m i := by
        have := chainB_state_next (t := t) hinj' hE0 (fun k hk => hbi k (by omega))
        rw [Nat.sub_add_cancel hm0] at this
        rw [this, state_ext, hd, hj]
        have h1 : c.init i = 1 := by
          rcases val_cases (c.init i) with h | h; exact absurd h hi1; exact h
        rw [h1]
        congr 1
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        exact (cnt_eq_zero_of_jd (by rw [hj]; simp)).symm
      have hiN : i ∈ (chainCfgB (t := t) b (m - 1) ∅).pat.N :=
        chainB_N_of (fun k hk => hbi k (by omega)) (Finset.notMem_empty _)
      refine ⟨_, hc', hs, hiN, i, hiN, ?_, fun _ => ⟨_, hc', b (m - 1), hiN,
        chainB_N_of (fun k hk he => by have := hinj' k (by omega) (m - 1) le_rfl he; omega)
          (Finset.notMem_empty _),
        rfl, chainB_deciding hinj' hE0 hf0⟩⟩
      exact hZ.jd0 _ hc' m i (by simp only [dec, hs]; exact hd) (by rw [hs]; exact hj)
  · by_cases h1 : ((cnt ((basicCtx n t).state pbasic c m i) : ℕ) : ℤ) > (n : ℤ) - m ∨
        ((basicCtx n t).state pbasic c m i).1.jd = some 1
    · exact absurd (otest hc h1) hK
    · exact exists_chain_run ht hc hd h0 h1

end Impl

/-! ### Undecided agents cannot detect their own faultiness -/

/-- An agent undecided at time `k + 1` did nothing at time `k` and sent `(init, 1)`. -/
theorem sends_of_undecided {c : (basicCtx n t).Config} (hc : c.Valid) {k : ℕ} {j : Fin n}
    (hd : dec pbasic c (k + 1) j = none) :
    pbasic j ((basicCtx n t).state pbasic c k j) = .noop ∧
      BForm ((basicCtx n t).state pbasic c k j).1 := by
  have hnoop := act_noop_of_dec_succ hd
  have hdk : dec pbasic c k j = none := dec_none_of_le_any hd (by omega)
  refine ⟨hnoop, ?_, hdk, ?_⟩
  · simp only [init_state]
    rcases val_cases (c.init j) with h | h
    · rw [act_eq, if_neg (by simpa using hdk), if_pos (Or.inl h)] at hnoop; cases hnoop
    · exact h
  · by_contra hne
    exact act_of_jd hc hdk hne hnoop

theorem bδX_comp_equiv (σ : Fin n ≃ Fin n) (s : Core × ℕ) (a : Act) (r : Fin n → Option BMsg) :
    bδX s a (r ∘ σ) = bδX s a r := by
  unfold bδX
  have h1 : (∃ j v, (r ∘ σ) j = some (BMsg.val v)) ↔ ∃ j v, r j = some (BMsg.val v) :=
    ⟨fun ⟨j, v, h⟩ => ⟨σ j, v, h⟩, fun ⟨j, v, h⟩ => ⟨σ.symm j, v, by simpa using h⟩⟩
  have h2 : (Finset.univ.filter (fun j => (r ∘ σ) j = some BMsg.init1)).card =
      (Finset.univ.filter (fun j => r j = some BMsg.init1)).card := by
    refine Finset.card_bij (fun j _ => σ j) (by simp) (fun _ _ _ _ h => σ.injective h) ?_
    intro j hj
    exact ⟨σ.symm j, by simpa using hj, by simp⟩
  simp only [h1, h2]

/-- **Undecided agents of `γ_basic` cannot detect their own faultiness** (`t < n`): a faulty agent
`i`, undecided at time `m`, has the same local state at time `m` in the run where the roles of `i`
and a nonfaulty agent `i'` are swapped (as in the paper's proof of Proposition 6.4). -/
theorem nfConsistent (htn : t < n) : NFConsistent (pbasic (n := n) (t := t)) := by
  classical
  intro c hc m i hd
  have hSO : c.pat ∈ SO n t := hc.1
  by_cases hi : i ∈ c.pat.N
  · exact ⟨c, hc, rfl, hi, rfl⟩
  obtain ⟨i', hi'⟩ : c.pat.N.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := hSO.1
    rw [h, Finset.sdiff_empty, Finset.card_univ, Fintype.card_fin] at this
    omega
  have hii' : i' ≠ i := fun h => hi (h ▸ hi')
  cases m with
  | zero =>
    let c' : (basicCtx n t).Config := ⟨⟨insert i c.pat.N, fun k l r => c.pat.F k l r || decide (l = i)⟩,
      c.init, c.x0⟩
    refine ⟨c', ⟨⟨?_, ?_⟩, hc.2⟩, rfl, Finset.mem_insert_self _ _, rfl⟩
    · exact (Finset.card_le_card (Finset.sdiff_subset_sdiff le_rfl (Finset.subset_insert _ _))).trans hSO.1
    · intro k l r hF
      simp only [c', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hF
      simp only [c', Finset.mem_insert, not_or]
      exact ⟨hF.2, hSO.2 k l r hF.1⟩
  | succ k0 =>
    -- `i` sends `(init,1)` in rounds `1, …, k0 + 1`
    have hS1 : ∀ k ≤ k0, pbasic i ((basicCtx n t).state pbasic c k i) = .noop ∧
        BForm ((basicCtx n t).state pbasic c k i).1 :=
      fun k hk => sends_of_undecided hc (dec_none_of_le_any hd (by omega))
    -- `i'` is undecided at time `k0`
    have hd' : dec pbasic c k0 i' = none := by
      by_contra hne
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hne
      obtain ⟨d, hdk, hD⟩ := exists_deciding oneShot.oneShotOn hc hv
      have hact := ((deciding_iff' hc).1 hD).2
      have hjd : ((basicCtx n t).state pbasic c (d + 1) i).1.jd ≠ none := by
        intro hn
        have := (jd_succ_eq_none_iff _ c d i).1 hn i' (by
          by_contra h; exact hSO.2 d i' i (by simpa using h) hi')
        rw [hact] at this; cases this
      exact hjd (hS1 (d + 1) (by omega)).2.2.2
    have hS2 : ∀ k < k0, pbasic i' ((basicCtx n t).state pbasic c k i') = .noop ∧
        BForm ((basicCtx n t).state pbasic c k i').1 :=
      fun k hk => sends_of_undecided hc (dec_none_of_le_any hd' (by omega))
    let sends' : Prop := pbasic i' ((basicCtx n t).state pbasic c k0 i') = .noop ∧
        BForm ((basicCtx n t).state pbasic c k0 i').1
    let F' : ℕ → Fin n → Fin n → Bool := fun k l r =>
      if l = i then true
      else if l = i' then (if k < k0 then c.pat.F k i r
        else if k = k0 then (if sends' then c.pat.F k i r else true) else true)
      else c.pat.F k l r
    let c' : (basicCtx n t).Config := ⟨⟨insert i (c.pat.N.erase i'), F'⟩, c.init, c.x0⟩
    have hc' : c'.Valid := by
      refine ⟨⟨?_, ?_⟩, hc.2⟩
      · have h1 : (insert i (c.pat.N.erase i')).card = c.pat.N.card := by
          rw [Finset.card_insert_of_notMem (by simp [hi]), Finset.card_erase_of_mem hi']
          have := Finset.card_pos.2 ⟨i', hi'⟩
          omega
        have e1 : (Finset.univ \ insert i (c.pat.N.erase i')).card = n - c.pat.N.card := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, h1]
        have e2 : (Finset.univ \ c.pat.N).card = n - c.pat.N.card := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        show (Finset.univ \ insert i (c.pat.N.erase i')).card ≤ t
        rw [e1, ← e2]; exact hSO.1
      · intro k l r hF
        show l ∉ insert i (c.pat.N.erase i')
        change (if l = i then true else if l = i' then (if k < k0 then c.pat.F k i r
          else if k = k0 then (if sends' then c.pat.F k i r else true) else true)
          else c.pat.F k l r) = false at hF
        simp only [Finset.mem_insert, Finset.mem_erase, not_or, not_and]
        by_cases hl : l = i
        · rw [if_pos hl] at hF; cases hF
        rw [if_neg hl] at hF
        by_cases hl' : l = i'
        · exact ⟨hl, fun h => absurd hl' h⟩
        rw [if_neg hl'] at hF
        exact ⟨hl, fun _ => hSO.2 k l r hF⟩
    refine ⟨c', hc', rfl, Finset.mem_insert_self _ _, ?_⟩
    -- the runs agree up to time `k0`
    have key : ∀ k ≤ k0, (basicCtx n t).state pbasic c' k = (basicCtx n t).state pbasic c k := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have e := ih (by omega)
        funext r
        have hr : brcv c' k r = brcv c k r ∘ Equiv.swap i i' := by
          funext j
          simp only [brcv, Function.comp_apply, e]
          by_cases hj : j = i
          · subst hj
            rw [Equiv.swap_apply_left]
            have h1 : c.pat.F k i' r = true := by
              by_contra h; exact hSO.2 k i' r (by simpa using h) hi'
            simp only [c', F', if_true, h1]
            rw [bμ_eq_init1_iff.2 (hS1 k (by omega)), bμ_eq_init1_iff.2 (hS2 k (by omega))]
          by_cases hj' : j = i'
          · subst hj'
            rw [Equiv.swap_apply_right]
            simp only [c', F', if_neg hj, if_true, if_pos (show k < k0 by omega)]
            rw [bμ_eq_init1_iff.2 (hS1 k (by omega)), bμ_eq_init1_iff.2 (hS2 k (by omega))]
          · rw [Equiv.swap_apply_of_ne_of_ne hj hj']
            simp only [c', F', if_neg hj, if_neg hj']
        rw [state_succ, state_succ, e, rcv_eq, rcv_eq, hr]
        simp only [δ]
        congr 1
        · congr 1; exact jdOf_comp_equiv _ _
        · exact bδX_comp_equiv _ _ _ _
    -- and `i` has the same state at time `k0 + 1`
    rw [state_succ, state_succ, key k0 le_rfl, rcv_eq, rcv_eq]
    by_cases hs : sends'
    · have hr : brcv c' k0 i = brcv c k0 i ∘ Equiv.swap i i' := by
        funext j
        simp only [brcv, Function.comp_apply, key k0 le_rfl]
        by_cases hj : j = i
        · subst hj
          rw [Equiv.swap_apply_left]
          have h1 : c.pat.F k0 i' j = true := by
            by_contra h; exact hSO.2 k0 i' j (by simpa using h) hi'
          simp only [c', F', if_true, h1]
          rw [bμ_eq_init1_iff.2 (hS1 k0 le_rfl), bμ_eq_init1_iff.2 hs]
        by_cases hj' : j = i'
        · subst hj'
          rw [Equiv.swap_apply_right]
          simp only [c', F', if_neg hj, if_true, lt_irrefl, if_false, if_pos hs]
          rw [bμ_eq_init1_iff.2 (hS1 k0 le_rfl), bμ_eq_init1_iff.2 hs]
        · rw [Equiv.swap_apply_of_ne_of_ne hj hj']
          simp only [c', F', if_neg hj, if_neg hj']
      rw [hr]
      simp only [δ]
      congr 1
      · congr 1; exact jdOf_comp_equiv _ _
      · exact bδX_comp_equiv _ _ _ _
    · -- `i'` decides in round `k0 + 1` and its message reaches everybody
      obtain ⟨v, hv⟩ : ∃ v, pbasic i' ((basicCtx n t).state pbasic c k0 i') = .decide v := by
        cases h : pbasic i' ((basicCtx n t).state pbasic c k0 i') with
        | decide v => exact ⟨v, rfl⟩
        | noop =>
          exfalso; apply hs
          refine ⟨h, ?_, hd', ?_⟩
          · simp only [init_state]
            rcases val_cases (c.init i') with h0 | h0
            · rw [act_eq, if_neg (by simpa using hd'), if_pos (Or.inl h0)] at h; cases h
            · exact h0
          · by_contra hne; exact act_of_jd hc hd' hne h
      have hF' : c.pat.F k0 i' i = true := by
        by_contra h; exact hSO.2 k0 i' i (by simpa using h) hi'
      have hri' : brcv c' k0 i i' = some (.val v) ∧ brcv c k0 i i' = some (.val v) := by
        have hF'' : F' k0 i' i = true := by
          simp only [F', if_neg hii', if_true, lt_irrefl, if_false, if_neg hs]
        constructor
        · show (if F' k0 i' i then bμ ((basicCtx n t).state pbasic c' k0 i')
            (pbasic i' ((basicCtx n t).state pbasic c' k0 i')) else none) = _
          rw [hF'', if_pos rfl, key k0 le_rfl, hv]; rfl
        · simp only [brcv, hF', if_true, hv]; rfl
      have hother : ∀ j, j ≠ i → brcv c' k0 i j = brcv c k0 i j := by
        intro j hj
        by_cases hj' : j = i'
        · subst hj'; rw [hri'.1, hri'.2]
        · simp only [brcv, key k0 le_rfl, c', F', if_neg hj, if_neg hj']
      have hii : ∀ msg, brcv c' k0 i i = some msg ∨ brcv c k0 i i = some msg →
          msg = .init1 := by
        intro msg hmsg
        have : bμ ((basicCtx n t).state pbasic c k0 i)
            (pbasic i ((basicCtx n t).state pbasic c k0 i)) = some .init1 :=
          bμ_eq_init1_iff.2 (hS1 k0 le_rfl)
        rcases hmsg with h | h <;> simp only [brcv, key k0 le_rfl] at h <;> split_ifs at h <;>
          rw [this] at h <;> exact (Option.some_injective _ h).symm
      have hjd : (basicCtx n t).jdOf (brcv c' k0 i) = (basicCtx n t).jdOf (brcv c k0 i) := by
        apply jdOf_congr
        intro w
        constructor
        · rintro ⟨j, msg, hm, ht⟩
          by_cases hj : j = i
          · subst hj; rw [hii msg (Or.inl hm)] at ht; cases ht
          · exact ⟨j, msg, (hother j hj) ▸ hm, ht⟩
        · rintro ⟨j, msg, hm, ht⟩
          by_cases hj : j = i
          · subst hj; rw [hii msg (Or.inr hm)] at ht; cases ht
          · exact ⟨j, msg, (hother j hj).symm ▸ hm, ht⟩
      have hX : bδX ((basicCtx n t).state pbasic c k0 i) (pbasic i ((basicCtx n t).state pbasic c k0 i))
          (brcv c' k0 i) = bδX ((basicCtx n t).state pbasic c k0 i)
            (pbasic i ((basicCtx n t).state pbasic c k0 i)) (brcv c k0 i) := by
        unfold bδX
        rw [if_pos (Or.inr ⟨i', v, hri'.1⟩), if_pos (Or.inr ⟨i', v, hri'.2⟩)]
      simp only [δ]
      rw [hjd]
      congr 1

end Basic

end Podc.OptimalEBAOmission
