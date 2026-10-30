import Papers.PODC2023.OptimalEBAOmission.Thm63

/-!
# Safety condition (1): moving to a run where all preferences are `1`

`allOnes`: in a sending-omission context where decided agents send nothing and the initial
extra state does not depend on the preference, for a "0-biased" protocol (implementations of `P0`,
`P_min`, `P_basic`) every run `c` has an all-`1` companion run `c'` with the same nonfaulty agents
in which every agent that has not decided `0` by time `k` has the same local state at time `k` as
in `c`. The companion run silences every faulty agent from the round in which it decides `0` on.

The paper's proof of Proposition 6.4 keeps the failure pattern unchanged ("the adversary is the
same as in `r`"); this works for `γ_min` but not for `γ_basic`, where an agent that decided `0` in `r`
sends `(init, 1)` in `r'` and changes the counts `#1` of other agents.
-/

namespace Podc.OptimalEBAOmission

open Classical

namespace Context

variable {n : ℕ} {γ : Context n}

/-- Decided agents send nothing (when they do not act). -/
def SilentAfterDecide (γ : Context n) : Prop :=
  ∀ i (s : γ.L) j, s.1.decided ≠ none → γ.μ i s .noop j = none

/-- The initial extra state does not depend on the initial preference. -/
def InitIndep (γ : Context n) : Prop := ∀ i x, x ∈ γ.initX i 0 ↔ x ∈ γ.initX i 1

/-- Properties shared by implementations of `P0`, `P_min` and `P_basic`. -/
structure ZeroBiased (P : γ.Protocol) : Prop where
  oneShot : OneShotOn P
  init0 : ∀ c : γ.Config, c.Valid → ∀ m i, dec P c m i = none → c.init i = 0 → Deciding P c m i 0
  jd0 : ∀ c : γ.Config, c.Valid → ∀ m i, dec P c m i = none →
    (γ.state P c m i).1.jd = some 0 → Deciding P c m i 0
  zeroBeforeOne : ∀ c : γ.Config, c.Valid → ∀ d d' i j,
    Deciding P c d i 1 → Deciding P c d' j 0 → d' < d
  prev : ∀ c : γ.Config, c.Valid → ∀ m j, Deciding P c (m + 1) j 0 → ∃ l, Deciding P c m l 0
  start : ∀ c : γ.Config, c.Valid → ∀ j, Deciding P c 0 j 0 → c.init j = 0

theorem Implements.zeroBiased {P : γ.Protocol} (hP : Implements P) : ZeroBiased P where
  oneShot := hP.oneShotOn
  init0 c hc _ _ hd h0 := hP.deciding_of_init hc hd h0
  jd0 c hc _ _ hd hj := hP.deciding_of_jd hc hd hj
  zeroBeforeOne c hc d d' i j h1 h0 := by
    by_contra hle
    obtain ⟨l, hl⟩ := hP.exists_deciding_le hc h0 (show d ≤ d' by omega)
    exact hP.not_deciding_zero_of_one hc h1 hl
  prev c hc _ _ h := hP.exists_prev hc h
  start c hc _ h := hP.init_of_deciding_zero hc h

/-- Chains from the `prev` property alone. -/
theorem exists_chain_of_prev {P : γ.Protocol} (hOS : OneShotOn P) {c : γ.Config}
    (hprev : ∀ m j, Deciding P c (m + 1) j 0 → ∃ l, Deciding P c m l 0) (hc : c.Valid)
    {m : ℕ} {j : Fin n} (h : Deciding P c m j 0) :
    ∃ a : ℕ → Fin n, a m = j ∧ (∀ k ≤ m, Deciding P c k (a k) 0) ∧
      ∀ k ≤ m, ∀ l ≤ m, a k = a l → k = l := by
  have key : ∀ m j, Deciding P c m j 0 → ∃ a : ℕ → Fin n, a m = j ∧
      ∀ k ≤ m, Deciding P c k (a k) 0 := by
    intro m
    induction m with
    | zero => exact fun j h => ⟨fun _ => j, rfl, fun k hk => by
        obtain rfl : k = 0 := by omega
        exact h⟩
    | succ m ih =>
      intro j h
      obtain ⟨l, hl⟩ := hprev m j h
      obtain ⟨a, -, ha⟩ := ih l hl
      refine ⟨fun k => if k = m + 1 then j else a k, by simp, fun k hk => ?_⟩
      by_cases hk' : k = m + 1
      · subst hk'; simpa using h
      · simpa [hk'] using ha k (by omega)
  obtain ⟨a, ham, ha⟩ := key m j h
  exact ⟨a, ham, ha, inj_of_deciding hOS hc ha⟩

section ZB

variable {P : γ.Protocol} (hZ : ZeroBiased P)
include hZ

/-- A 0-decision is preceded by 0-decisions at all earlier times. -/
theorem ZeroBiased.exists_le {c : γ.Config} (hc : c.Valid) {m d : ℕ} {j : Fin n}
    (h : Deciding P c m j 0) (hd : d ≤ m) : ∃ l, Deciding P c d l 0 := by
  induction m, hd using Nat.le_induction generalizing j with
  | base => exact ⟨j, h⟩
  | succ m _ ih =>
    obtain ⟨l, hl⟩ := hZ.prev c hc m j h
    exact ih hl

/-- An agent deciding `0` at time `m` ends a chain of distinct agents deciding `0` at times
`0, …, m`. -/
theorem ZeroBiased.exists_chain {c : γ.Config} (hc : c.Valid) {m : ℕ} {j : Fin n}
    (h : Deciding P c m j 0) :
    ∃ a : ℕ → Fin n, a m = j ∧ (∀ k ≤ m, Deciding P c k (a k) 0) ∧
      ∀ k ≤ m, ∀ l ≤ m, a k = a l → k = l :=
  exists_chain_of_prev hZ.oneShot (hZ.prev c hc) hc h

/-- In a run where all preferences are `1`, nobody decides `0`. -/
theorem ZeroBiased.not_deciding_zero {c : γ.Config} (hc : c.Valid) (h1 : ∀ j, c.init j = 1)
    {m : ℕ} {j : Fin n} : ¬ Deciding P c m j 0 := by
  intro h
  obtain ⟨l, hl⟩ := hZ.exists_le hc h (Nat.zero_le m)
  have := hZ.start c hc l hl
  rw [h1 l] at this; exact absurd this (by decide)

/-- In a run where all preferences are `1`, no agent ever just decided `0`. -/
theorem ZeroBiased.not_jDecided_zero {c : γ.Config} (hc : c.Valid) (h1 : ∀ j, c.init j = 1)
    {m : ℕ} {j : Fin n} : ¬ JDecided P c m j 0 := by
  intro h
  cases m with
  | zero => exact Context.not_jDecided_zero hZ.oneShot hc h
  | succ m => exact hZ.not_deciding_zero hc h1 ((jDecided_succ_iff hZ.oneShot hc).1 h)

/-- **The all-`1` companion run.** -/
theorem ZeroBiased.allOnes {t : ℕ} (hFM : γ.FM = SO n t) (hSil : SilentAfterDecide γ)
    (hInit : InitIndep γ) {c : γ.Config} (hc : c.Valid) :
    ∃ c' : γ.Config, c'.Valid ∧ (∀ j, c'.init j = 1) ∧ c'.pat.N = c.pat.N ∧
      ∀ k j, dec P c (k + 1) j ≠ some 0 → γ.state P c' k j = γ.state P c k j := by
  have hOS := hZ.oneShot
  have hSO : c.pat ∈ SO n t := hFM ▸ hc.1
  let F' : ℕ → Fin n → Fin n → Bool := fun k l j =>
    c.pat.F k l j && !(decide (l ∉ c.pat.N ∧ dec P c (k + 1) l = some 0))
  let c' : γ.Config := ⟨⟨c.pat.N, F'⟩, fun _ => 1, c.x0⟩
  have hc' : c'.Valid := by
    refine ⟨?_, fun j => ?_⟩
    · rw [hFM]
      refine ⟨hSO.1, fun k l j hF => ?_⟩
      intro hlN
      have hT : c.pat.F k l j = true := by
        by_contra h; exact hSO.2 k l j (by simpa using h) hlN
      change l ∈ c.pat.N at hlN
      change (c.pat.F k l j && !decide (l ∉ c.pat.N ∧ dec P c (k + 1) l = some 0)) = false at hF
      simp [hT, hlN] at hF
    · rcases val_cases (c.init j) with h | h
      · have := hc.2 j; rw [h] at this; exact (hInit j _).1 this
      · have := hc.2 j; rw [h] at this; exact this
  refine ⟨c', hc', fun _ => rfl, rfl, ?_⟩
  -- `j` decided `1` at some time `≤ k` while `l` decides `0` at time `k`: impossible
  have no_one_then_zero : ∀ k l j v, Deciding P c k l 0 → dec P c (k + 1) j = some v → v ≠ 0 →
      False := by
    intro k l j v hl hj hv
    obtain ⟨d, hd, hD⟩ := exists_deciding hOS hc hj
    have hv1 : v = 1 := by rcases val_cases v with h | h; exact absurd h hv; exact h
    subst hv1
    have := hZ.zeroBeforeOne c hc d k j l hD hl
    omega
  intro k
  induction k with
  | zero =>
    intro j hj
    have h1 : c.init j = 1 := by
      rcases val_cases (c.init j) with h | h
      · exact absurd (hZ.init0 c hc 0 j rfl h).2 hj
      · exact h
    simp only [state_zero, c', h1]
  | succ k ih =>
    intro j hj
    have hj' : dec P c (k + 1) j ≠ some 0 := fun h =>
      hj (dec_stable hOS hc h (k + 2) (by omega))
    have hst := ih j hj'
    have hr : rcv P c' (k + 1 - 1) j = rcv P c k j := by
      simp only [Nat.add_sub_cancel]
      funext l
      by_cases hl : dec P c (k + 1) l = some 0
      · -- `l` has decided `0`: in `c`, `j` receives nothing from `l`
        have hnone : rcv P c k j l = none := by
          by_contra hne
          obtain ⟨msg, hmsg⟩ := Option.ne_none_iff_exists'.1 hne
          simp only [rcv] at hmsg
          split_ifs at hmsg with hF
          by_cases hdl : dec P c k l = none
          · have hDl : Deciding P c k l 0 := ⟨hdl, hl⟩
            have hact := ((deciding_iff hOS hc).1 hDl).2
            rw [hact] at hmsg
            obtain ⟨m', hm', ht⟩ := γ.μ_decide l (γ.state P c k l) 0 j
            have hjd : (γ.state P c (k + 1) j).1.jd = some 0 :=
              (jd_succ_eq_zero_iff P c k j).2 ⟨l, hF, hact⟩
            cases hdj : dec P c (k + 1) j with
            | none => exact hj (hZ.jd0 c hc (k + 1) j hdj hjd).2
            | some v => exact no_one_then_zero k l j v hDl hdj (fun h => hj' (h ▸ hdj))
          · rw [hOS c hc k l hdl, hSil l _ j hdl] at hmsg; cases hmsg
        have hlN : l ∉ c.pat.N := by
          intro hlN
          obtain ⟨d, hd, hD⟩ := exists_deciding hOS hc hl
          have hjd : (γ.state P c (d + 1) j).1.jd = some 0 := by
            refine (jd_succ_eq_zero_iff P c d j).2 ⟨l, ?_, ((deciding_iff hOS hc).1 hD).2⟩
            by_contra hF; exact hSO.2 d l j (by simpa using hF) hlN
          cases hdj : dec P c (d + 1) j with
          | none =>
            have := dec_stable hOS hc (hZ.jd0 c hc (d + 1) j hdj hjd).2 (k + 2) (by omega)
            exact hj this
          | some v =>
            exact no_one_then_zero d l j v hD hdj (fun h => hj (dec_stable hOS hc (h ▸ hdj) _ (by omega)))
        rw [hnone]
        simp only [rcv, c', F', hlN, hl, not_false_eq_true, and_self, decide_true, Bool.not_true,
          Bool.and_false, Bool.false_eq_true, if_false]
      · have hsl := ih l hl
        simp only [rcv, c', F', hl, and_false, decide_false, Bool.not_false, Bool.and_true]
        rw [show γ.state P ⟨⟨c.pat.N, F'⟩, fun _ => 1, c.x0⟩ k l = γ.state P c k l from hsl]
    show γ.state P c' (k + 1) j = γ.state P c (k + 1) j
    rw [state_succ, state_succ, hst, ← hr]
    simp only [Nat.add_sub_cancel]

/-- **Safety condition (1)** for a `0`-biased protocol in such contexts: an agent that has not
decided `0` by time `m` has its local state at time `m` in a run with all preferences `1`. -/
theorem ZeroBiased.safe_one {t : ℕ} (hFM : γ.FM = SO n t) (hSil : SilentAfterDecide γ)
    (hInit : InitIndep γ) {c : γ.Config} (hc : c.Valid) {m : ℕ} {i : Fin n}
    (h : dec P c (m + 1) i ≠ some 0) :
    ∃ c' : γ.Config, c'.Valid ∧ (∀ j, c'.init j = 1) ∧ γ.state P c' m i = γ.state P c m i := by
  obtain ⟨c', hc', h1, -, hst⟩ := hZ.allOnes hFM hSil hInit hc
  exact ⟨c', hc', h1, hst m i h⟩

/-- An agent that is not deciding `0` does not know that some agent has just decided `0`. -/
theorem ZeroBiased.not_knows_jDecided {t : ℕ} (hFM : γ.FM = SO n t) (hSil : SilentAfterDecide γ)
    (hInit : InitIndep γ) {c : γ.Config} (hc : c.Valid) {m : ℕ} {i : Fin n}
    (h : dec P c (m + 1) i ≠ some 0) :
    ¬ Knows P i (γ.state P c m i) (fun c' m' => ∃ j, JDecided P c' m' j 0) := by
  intro hK
  obtain ⟨c', hc', h1, hst⟩ := hZ.safe_one hFM hSil hInit hc h
  obtain ⟨j, hj⟩ := hK c' hc' m hst
  exact hZ.not_jDecided_zero hc' h1 hj

end ZB

/-- **Safety condition (1)** for implementations of `P0` (repaired 0-chains). -/
theorem Implements.safe_one {t : ℕ} (hFM : γ.FM = SO n t) (hSil : SilentAfterDecide γ)
    (hInit : InitIndep γ) {P : γ.Protocol} (hP : Implements P) :
    ∀ c : γ.Config, c.Valid → ∀ m i, ¬ ReceivedChain P c m i →
      ∃ c' : γ.Config, c'.Valid ∧ (∀ j, c'.init j = 1) ∧ γ.state P c' m i = γ.state P c m i := by
  intro c hc m i h
  rw [hP.receivedChain_iff hc] at h
  exact hP.zeroBiased.safe_one hFM hSil hInit hc h

/-! ### Transfer between protocols with the same runs -/

section Transfer

variable {P Q : γ.Protocol}
  (hPQ : ∀ m, ∀ c : γ.Config, c.Valid → γ.state P c m = γ.state Q c m)
include hPQ

theorem deciding_congr {c : γ.Config} (hc : c.Valid) {m : ℕ} {j : Fin n} {v : Val} :
    Deciding P c m j v ↔ Deciding Q c m j v := by
  simp only [Deciding, dec, hPQ m c hc, hPQ (m + 1) c hc]

theorem SafeWrt.congr {recvP recvQ : γ.Config → ℕ → Fin n → Prop}
    (hR : ∀ c : γ.Config, c.Valid → ∀ m i, recvP c m i ↔ recvQ c m i) (h : SafeWrt recvP P) :
    SafeWrt recvQ Q := by
  constructor
  · intro c hc m i hr
    obtain ⟨c', hc', h1, hs⟩ := h.one c hc m i ((hR c hc m i).not.2 hr)
    exact ⟨c', hc', h1, by rwa [← hPQ m c' hc', ← hPQ m c hc]⟩
  · intro c hc m i hK hd
    have hK' : ¬ Knows P i (γ.state P c m i) (fun c' m' => ∀ j, ¬ Deciding P c' m' j 0) := by
      intro hK'
      apply hK
      intro c' hc' m' hs j
      rw [← deciding_congr hPQ hc']
      exact hK' c' hc' m' (by rwa [hPQ m' c' hc', hPQ m c hc]) j
    obtain ⟨c', hc', hs, hi, j, hj, hD, hmore⟩ := h.two c hc m i hK' (by
      simpa only [dec, hPQ m c hc] using hd)
    refine ⟨c', hc', by rwa [← hPQ m c' hc', ← hPQ m c hc], hi, j, hj,
      (deciding_congr hPQ hc').1 hD, fun h1 => ?_⟩
    obtain ⟨c'', hc'', j', hj1, hj2, hs', hD'⟩ := hmore h1
    exact ⟨c'', hc'', j', hj1, hj2, by rwa [← hPQ m c'' hc'', ← hPQ m c' hc'],
      (deciding_congr hPQ hc'').1 hD'⟩

theorem NFConsistent.congr (h : NFConsistent P) : NFConsistent Q := by
  intro c hc m i hd
  obtain ⟨c', hc', hinit, hi, hs⟩ := h c hc m i (by simpa only [dec, hPQ m c hc] using hd)
  exact ⟨c', hc', hinit, hi, by rwa [← hPQ m c' hc', ← hPQ m c hc]⟩

end Transfer

/-- Safety (repaired 0-chains) transfers between implementations of `P0`. -/
theorem Implements.safeWrt_congr {P Q : γ.Protocol} (hP : Implements P) (hQ : Implements Q)
    (h : SafeWrt (ReceivedChain P) P) : SafeWrt (ReceivedChain Q) Q :=
  h.congr (hP.state_eq hQ) fun c hc m i => by
    rw [hP.receivedChain_iff hc, hQ.receivedChain_iff hc]
    simp only [dec, hP.state_eq hQ (m + 1) c hc]

end Context

end Podc.OptimalEBAOmission
