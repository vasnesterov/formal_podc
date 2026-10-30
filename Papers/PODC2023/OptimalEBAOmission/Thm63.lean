import Papers.PODC2023.OptimalEBAOmission.Prop61

/-!
# Theorem 6.3: safety implies optimality

`thm_6_3`: if `P` implements `P0`, the safety conditions hold for `P` (with repaired 0-chains),
and undecided agents cannot detect their own faultiness (`NFConsistent P`), then no one-shot EBA
decision protocol strictly dominates `P`.

The proof follows the paper: take the first time `m*` at which `P` and a strictly dominating `P'`
act differently in corresponding runs; up to `m*` the runs coincide. The paper's proof only treats
the cases where `P'` decides at `m*`, and silently assumes the agent `i` considered is nonfaulty in
the runs supplied by safety condition (1); `NFConsistent` supplies such runs, and also handles the
case missing from the paper (`P` decides at `m*` and `P'` does not).
-/

namespace Podc.OptimalEBAOmission

open Classical

namespace Context

variable {n : ℕ} {γ : Context n}

/-- If two protocols act identically before time `m` (on all admissible runs), their runs coincide
up to time `m`. -/
theorem state_eq_of_act_eq {P P' : γ.Protocol} {m : ℕ}
    (h : ∀ k < m, ∀ c : γ.Config, c.Valid → ∀ i, P i (γ.state P c k i) = P' i (γ.state P' c k i)) :
    ∀ k ≤ m, ∀ c : γ.Config, c.Valid → γ.state P c k = γ.state P' c k := by
  intro k hk c hc
  induction k with
  | zero => rfl
  | succ k ih =>
    have e := ih (by omega)
    have ha : ∀ i, P' i (γ.state P' c k i) = P i (γ.state P c k i) := fun i => (h k (by omega) c hc i).symm
    funext i
    have hr : rcv P c k i = rcv P' c k i := by
      funext j; simp only [rcv, e, ha]
    simp only [state_succ, hr, e, ha]

/-- **Theorem 6.3** (repaired). Let `P` implement `P0` in `γ`, satisfy the safety conditions of
Definition 6.2 (with repaired 0-chains) and `NFConsistent`. Then no one-shot EBA decision protocol
strictly dominates `P`. -/
theorem thm_6_3_core {P : γ.Protocol} (hP : Implements P) (hS : SafeWrt (ReceivedChain P) P)
    (hNF : NFConsistent P) :
    ∀ P', IsEBA P' → OneShot P' → ¬ StrictlyDominates P' P := by
  intro P' hE hOS ⟨hDom, hND⟩
  have hOSP := hP.oneShotOn
  have hOS' := hOS.oneShotOn
  -- some action differs
  have hex : ∃ m, ∃ c : γ.Config, c.Valid ∧ ∃ i, P i (γ.state P c m i) ≠ P' i (γ.state P' c m i) := by
    by_contra hne
    push_neg at hne
    apply hND
    intro c hc i _ m v hv m' hm' w hw
    rw [← hne m' c hc i] at hw
    have hD := deciding_of_act hOSP hc hw
    have hdm : dec P c m i ≠ none := by
      rw [dec_stable hOSP hc hD.2 m (by omega)]; simp
    rw [hOSP c hc m i hdm] at hv; cases hv
  let ms := Nat.find hex
  obtain ⟨c, hc, i, hdiff⟩ := Nat.find_spec hex
  have hmin : ∀ k < ms, ∀ c : γ.Config, c.Valid → ∀ i,
      P i (γ.state P c k i) = P' i (γ.state P' c k i) := by
    intro k hk c hc i
    by_contra hne
    exact Nat.find_min hex hk ⟨c, hc, i, hne⟩
  have heq := state_eq_of_act_eq hmin
  have heqm : ∀ c : γ.Config, c.Valid → γ.state P c ms = γ.state P' c ms :=
    fun c hc => heq ms le_rfl c hc
  change P i (γ.state P c ms i) ≠ P' i (γ.state P' c ms i) at hdiff
  rw [← heqm c hc] at hdiff
  set s := γ.state P c ms i with hs_def
  -- `P'` acts at `s` wherever `i` has local state `s` at time `ms`
  have hP's : ∀ c' : γ.Config, c'.Valid → γ.state P c' ms i = s →
      P' i (γ.state P' c' ms i) = P' i s := by
    intro c' hc' h; rw [← heqm c' hc', h]
  -- `P'` decides at `ms` at a nonfaulty agent where `P` does
  have forced : ∀ c' : γ.Config, c'.Valid → ∀ j ∈ c'.pat.N, ∀ v,
      P j (γ.state P c' ms j) = .decide v → ∃ w, P' j (γ.state P' c' ms j) = .decide w := by
    intro c' hc' j hj v hv
    have hdP : dec P c' ms j = none := ((deciding_iff hOSP hc').1 (deciding_of_act hOSP hc' hv)).1
    obtain ⟨m', -, hm'⟩ := hE.termination c' hc' j hj (ms + 1)
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hm'
    obtain ⟨d, -, hD⟩ := exists_deciding hOS' hc' hw
    have hact := ((deciding_iff hOS' hc').1 hD).2
    rcases lt_trichotomy d ms with hlt | heq' | hgt
    · exfalso
      rw [← hmin d hlt c' hc' j] at hact
      have := dec_stable hOSP hc' (deciding_of_act hOSP hc' hact).2 ms (by omega)
      rw [hdP] at this; cases this
    · exact ⟨w, heq' ▸ hact⟩
    · exact absurd hv (hDom c' hc' j hj d w hact ms hgt v)
  -- `i` is undecided at `ms`
  have hd : dec P c ms i = none := by
    by_contra hne
    apply hdiff
    rw [hOSP c hc ms i hne, hOS i s hne]
  cases ha' : P' i s with
  | noop =>
    -- `P` decides at `s`, `P'` does not: take a run where `i` is nonfaulty
    obtain ⟨v, hv⟩ : ∃ v, P i s = .decide v := by
      cases h : P i s with
      | decide v => exact ⟨v, rfl⟩
      | noop => exact absurd (h.trans ha'.symm) hdiff
    obtain ⟨c1, hc1, -, hi1, hs1⟩ := hNF c hc ms i hd
    obtain ⟨w, hw⟩ := forced c1 hc1 i hi1 v (by rw [hs1]; exact hv)
    rw [hP's c1 hc1 hs1, ha'] at hw; cases hw
  | decide v =>
    rcases val_cases v with rfl | rfl
    · -- `P'` decides `0`, `P` does not
      have hPne : P i s ≠ .decide 0 := fun h => hdiff (h.trans ha'.symm)
      have hnot : ¬ ReceivedChain P c ms i := by
        rw [hP.receivedChain_iff hc, dec_succ, hd]
        cases h : P i (γ.state P c ms i) with
        | noop => simp [newDec]
        | decide u =>
          rcases val_cases u with rfl | rfl
          · exact absurd h hPne
          · simp [newDec]
      obtain ⟨c1, hc1, hall, hs1⟩ := hS.one c hc ms i hnot
      have hd1 : dec P c1 ms i = none := by simp only [dec, hs1]; exact hd
      obtain ⟨c2, hc2, hinit, hi2, hs2⟩ := hNF c1 hc1 ms i hd1
      have hact : P' i (γ.state P' c2 ms i) = .decide 0 := by
        rw [hP's c2 hc2 (hs2.trans hs1), ha']
      have hdec : dec P' c2 (ms + 1) i = some 0 := by rw [dec_succ, hact]; rfl
      obtain ⟨j, hj⟩ := hE.validity c2 hc2 i hi2 (ms + 1) 0 hdec
      rw [hinit, hall j] at hj
      exact absurd hj (by decide)
    · -- `P'` decides `1`, `P` does not
      have hPne : P i s ≠ .decide 1 := fun h => hdiff (h.trans ha'.symm)
      have hnK : ¬ Knows P i s (fun c' m' => ∀ j, ¬ Deciding P c' m' j 0) := by
        intro hK
        cases h : P i s with
        | noop => exact ((hP.act_noop_iff hc hd).1 h).2 hK
        | decide u =>
          rcases val_cases u with rfl | rfl
          · exact hK c hc ms rfl i (deciding_of_act hOSP hc h)
          · exact hPne h
      obtain ⟨c1, hc1, hs1, hi1, j, hj1, hDj, hmore⟩ := hS.two c hc ms i hnK hd
      have hact_i : P' i (γ.state P' c1 ms i) = .decide 1 := by rw [hP's c1 hc1 hs1, ha']
      obtain ⟨w, hw⟩ := forced c1 hc1 j hj1 0 ((deciding_iff hOSP hc1).1 hDj).2
      have hw1 : w = 1 := by
        have h1 : dec P' c1 (ms + 1) i = some 1 := by rw [dec_succ, hact_i]; rfl
        have h2 : dec P' c1 (ms + 1) j = some w := by rw [dec_succ, hw]; rfl
        exact (hE.agreement c1 hc1 i hi1 j hj1 (ms + 1) 1 w h1 h2).symm
      subst hw1
      by_cases hms : ms = 0
      · -- `j` has preference `0`: move it to a run where all preferences are `0`
        rw [hms] at hDj hw
        have hinit := hP.init_of_deciding_zero hc1 hDj
        let c3 : γ.Config := ⟨c1.pat, fun _ => 0,
          fun l => if l = j then c1.x0 j else (γ.initX_nonempty l 0).some⟩
        have hc3 : c3.Valid := by
          refine ⟨hc1.1, fun l => ?_⟩
          by_cases hl : l = j
          · subst hl; simp only [c3, if_true]; rw [← hinit]; exact hc1.2 l
          · simp only [c3, if_neg hl]; exact (γ.initX_nonempty l 0).some_mem
        have hs3 : γ.state P' c3 0 j = γ.state P' c1 0 j := by
          simp only [state_zero, c3, if_true, hinit]
        have hdec : dec P' c3 1 j = some 1 := by
          rw [dec_succ, hs3, hw]; rfl
        obtain ⟨l, hl⟩ := hE.validity c3 hc3 j hj1 1 1 hdec
        simp [c3] at hl
      · obtain ⟨c4, hc4, j', hj4, hj'4, hs4, hD'⟩ := hmore (by omega)
        have hstate : γ.state P' c4 ms j = γ.state P' c1 ms j := by
          rw [← heqm c4 hc4, ← heqm c1 hc1, hs4]
        have h1 : dec P' c4 (ms + 1) j = some 1 := by
          rw [dec_succ, hstate, hw]; rfl
        have hact' : P' j' (γ.state P' c4 (ms - 1) j') = .decide 0 := by
          rw [← hmin (ms - 1) (by omega) c4 hc4 j']
          exact ((deciding_iff hOSP hc4).1 hD').2
        have h2 : dec P' c4 (ms + 1) j' = some 0 :=
          dec_stable hOS' hc4 (show dec P' c4 (ms - 1 + 1) j' = some 0 by rw [dec_succ, hact']; rfl)
            _ (by omega)
        exact absurd (hE.agreement c4 hc4 j hj4 j' hj'4 _ 1 0 h1 h2) (by decide)

/-- **Theorem 6.3** (repaired, for an EBA context with sending-omission failures): an
implementation of `P0` satisfying the safety conditions (repaired 0-chains) and `NFConsistent` is
optimal among one-shot protocols. -/
theorem thm_6_3 {t : ℕ} (hFM : γ.FM ⊆ SO n t) {P : γ.Protocol} (hP : Implements P)
    (hS : SafeWrt (ReceivedChain P) P) (hNF : NFConsistent P) : OptimalOneShot P :=
  ⟨(prop_6_1 hFM hP).1, thm_6_3_core hP hS hNF⟩

/-- A paper 0-chain is a repaired 0-chain. -/
theorem IsZeroChainLit.isZeroChain {P : γ.Protocol} {c : γ.Config} {m : ℕ} {a : ℕ → Fin n}
    (h : IsZeroChainLit P c m a) : IsZeroChain P c m a :=
  ⟨h.1, h.2.1, h.2.2.1, fun k h1 h2 c' hc' m' hs => ⟨_, h.2.2.2 k h1 h2 c' hc' m' hs⟩⟩

/-- Safety with the paper's 0-chains implies safety with repaired 0-chains. -/
theorem SafeWrt.of_lit {P : γ.Protocol} (h : SafeWrt (ReceivedChainLit P) P) :
    SafeWrt (ReceivedChain P) P :=
  ⟨fun c hc m i hr => h.one c hc m i fun ⟨m', hm', a, ha, hai⟩ =>
      hr ⟨m', hm', a, ha.isZeroChain, hai⟩, h.two⟩

/-- **Theorem 6.3** with the paper's notion of safety (Definition 6.2), under the extra hypotheses
`NFConsistent` and one-shot competitors. -/
theorem thm_6_3_lit {t : ℕ} (hFM : γ.FM ⊆ SO n t) (hS : SafeLit γ) {P : γ.Protocol}
    (hP : Implements P) (hNF : NFConsistent P) : OptimalOneShot P :=
  thm_6_3 hFM hP (hS P hP).of_lit hNF

end Context

end Podc.OptimalEBAOmission
