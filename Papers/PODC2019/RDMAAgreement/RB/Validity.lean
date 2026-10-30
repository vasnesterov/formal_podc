import Papers.PODC2019.RDMAAgreement.RB.Validity3

/-!
# Algorithm 2 — Property (1) of Definition 1 (validity)

If a correct process `p` broadcasts `(k, m)`, every correct process eventually delivers `(k, m)`
from `p` (fair executions, `|F| ≤ f`, `n ≥ 2f + 1`).

Proof (as in Appendix A, by induction on `k` and contradiction): if no correct process ever
delivered key `k`, all correct threads `(·,p)` would stay on key `k`; then all correct processes
echo `(k,m)` (stage 1), write L1 proofs (stage 2), write L2 proofs (stage 3), and then deliver
(`deliver_of_slot`) — contradiction. Once one correct process delivers, all do (totality), and
by integrity they deliver `m`.
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

lemma persist {Q : ℕ → Prop} {t : ℕ} (h0 : Q t) (hs : ∀ t' ≥ t, Q t' → Q (t' + 1)) :
    ∀ t' ≥ t, Q t' := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base => exact h0
  | succ n hn ih => exact hs n hn ih

lemma TStep.phase_ne_wfs {s s' : St P M} {r q : P} (T : TStep F f s s' r q)
    (h : s.phase r q ≠ .wfs) (hk : s'.key r q = s.key r q) : s'.phase r q ≠ .wfs := by
  cases T with
  | copy _ _ _ _ hlast => exfalso; simp [St.key] at hk; omega
  | echo _ _ _ _ _ hph => rw [hph]; simp
  | l1Done _ _ _ _ _ hph => rw [hph]; simp
  | _ => simp_all

lemma TStep.phase_wfl2 {s s' : St P M} {r q : P} (T : TStep F f s s' r q) (IA : InvA F s)
    (hr : r ∉ F) (h : s.phase r q = .wfl2) (hk : s'.key r q = s.key r q) :
    s'.phase r q = .wfl2 := by
  cases T with
  | copy _ _ _ _ hlast => exfalso; simp [St.key] at hk; omega
  | echo _ _ hpc =>
    have := (IA.thr r hr q).ph .wfs (by simp [St.loc, hpc, PC.ph])
    simp [St.loc, h] at this
  | l1Done _ _ _ _ _ hph => exact hph
  | _ => simp_all

lemma Step.bret_mem {s s' : St P M} {p : P} {b : Base P M} (h : Step F f s (.bret p) s')
    (hb : s.bpend p = some b) : s'.mem ⟨.val, p, b.key, p⟩ = .cp ⟨p, b⟩ := by
  cases h with
  | bret _ hb2 => rw [hb] at hb2; cases hb2; simp [St.tick, St.write]
  | bretIdle _ hid => rw [hb] at hid; cases hid

/-- Phase facts persist while the key does not change. -/
lemma phase_persist [Inhabited P] (e : Exec (M := M) F f) {r p : P} (hr : r ∉ F) {t : ℕ}
    (hk : (e.s (t + 1)).key r p = (e.s t).key r p) :
    ((e.s t).phase r p ≠ .wfs → (e.s (t + 1)).phase r p ≠ .wfs) ∧
    ((e.s t).phase r p = .wfl2 → (e.s (t + 1)).phase r p = .wfl2) := by
  have hs := e.step t
  by_cases hl : e.ℓ t = .thr r p
  · rw [hl] at hs
    exact ⟨fun h => hs.tstep.phase_ne_wfs h hk,
      fun h => hs.tstep.phase_wfl2 (InvA.reach (e.reach t)) hr h hk⟩
  · have hl' : (e.s (t + 1)).loc r p = (e.s t).loc r p := by
      by_cases hT : ∃ p' q', e.ℓ t = .thr p' q'
      · obtain ⟨p', q', he⟩ := hT
        rw [he] at hs hl
        exact hs.frame_thr.1 r p (by rintro ⟨rfl, rfl⟩; exact hl rfl)
      · push_neg at hT; exact (hs.frame_other hT).1 r p
    simp only [St.loc, Loc.mk.injEq] at hl'
    rw [hl'.2.2.1]; exact ⟨id, id⟩

/-- **Property (1) of Definition 1 (validity).** In a fair execution with `|F| ≤ f` and
`n ≥ 2f + 1`, if a correct process `p` broadcasts `(k, m)` then every correct process eventually
delivers `(k, m)` from `p`. -/
theorem Exec.validity [Inhabited P] (hF : F.card ≤ f) (hn : 2 * f + 1 ≤ Fintype.card P)
    (e : Exec (M := M) F f) (hfair : e.Fair) {p : P} (hp : p ∉ F) :
    ∀ k m t0, (e.s t0).bc p k = some m → ∀ r ∉ F, ∃ t, (e.s t).dlv r p k = some m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro m t0 hb r hr
  have IG0 := InvG.reach (e.reach t0)
  have hk1 := (IG0.bcIff p hp k).1 (by rw [hb]; simp)
  have hbcT : ∀ t ≥ t0, (e.s t).bc p k = some m := fun t ht => (e.grows ht).2 p hp k m hb
  -- all correct threads `(·,p)` eventually reach key `k`
  have step1 : ∀ r ∉ F, ∃ t, k - 1 ≤ (e.s t).last r p := by
    intro r hr
    by_cases hk : k = 1
    · exact ⟨0, by omega⟩
    obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.1
      ((IG0.bcIff p hp (k - 1)).2 ⟨by omega, by omega⟩)
    obtain ⟨t, ht⟩ := IH (k - 1) (by omega) m' t0 hm' r hr
    exact ⟨t, (((InvF.reach hF (e.reach t)).dlvIff r hr p (k - 1)).1 (by rw [ht]; simp)).2⟩
  -- some correct process delivers key `k`
  have step2 : ∃ r0 ∉ F, ∃ t, k ≤ (e.s t).last r0 p := by
    by_contra H
    push_neg at H
    obtain ⟨T0, hT0⟩ := eventually_all (F := F)
      (Q := fun r t => k - 1 ≤ (e.s t).last r p)
      (fun r _ t t' h h' => le_trans h' (e.last_mono r p h)) step1
    have hkey : ∀ r ∉ F, ∀ t ≥ T0, (e.s t).key r p = k := by
      intro r hr t ht
      have h1 := hT0 r hr t ht; have h2 := H r hr t
      simp [St.key]; omega
    -- the broadcast write completes
    obtain ⟨T1, hT1⟩ : ∃ T1, ∀ t ≥ T1, (e.s t).mem ⟨.val, p, k, p⟩ ≠ .bot := by
      obtain ⟨tb, htb, hlb⟩ := hfair.2 p hp t0
      have IGb := InvG.reach (e.reach tb)
      have hbn := ((IGb.bcIff p hp k).1 (by rw [hbcT tb htb]; simp)).2
      have h0 : (e.s (tb + 1)).mem ⟨.val, p, k, p⟩ ≠ .bot := by
        rcases IGb.written p hp k hk1.1 hbn with ⟨b, hb', hbk⟩ | hm
        · have hs := e.step tb; rw [hlb] at hs
          rw [← hbk, hs.bret_mem hb']; simp
        · exact (e.step tb).mem_ne_bot hp hm
      exact ⟨tb + 1, persist h0 fun t' _ h => (e.step t').mem_ne_bot hp h⟩
    set T := max (max T0 T1) t0
    have hkeyT : ∀ r ∉ F, ∀ t ≥ T, (e.s (t + 1)).key r p = (e.s t).key r p := fun r hr t ht => by
      rw [hkey r hr t (by omega), hkey r hr (t + 1) (by omega)]
    -- stage 1
    obtain ⟨T2, hT2⟩ := eventually_all (F := F)
      (Q := fun r t => T ≤ t ∧ (e.s t).phase r p ≠ .wfs)
      (fun r hr t t' h h' => ⟨le_trans h'.1 h, persist h'.2 (fun t'' ht'' h'' =>
        (phase_persist e hr (hkeyT r hr t'' (le_trans h'.1 ht''))).1 h'') t' h⟩)
      (fun r hr => by
        obtain ⟨t, ht, h⟩ := stage1 e hfair hp hr (T := T) (fun t ht => hkey r hr t (by omega))
          (fun t ht => hT1 t (by omega))
        exact ⟨t, ht, h⟩)
    set T2' := max T2 T
    have hecho : ∀ j ∉ F, ∀ t ≥ T2', (e.s t).echoT j p k ≠ none := by
      intro j hj t ht
      obtain ⟨x, hx⟩ := (InvA.reach (e.reach t)).thr j hj p |>.echoed
        (by simpa [St.loc] using (hT2 j hj t (by omega)).2)
      simp only [St.loc] at hx
      have := hkey j hj t (by omega); simp only [St.key] at this
      rw [this] at hx; rw [hx]; simp
    -- stage 2
    obtain ⟨T3, hT3⟩ := eventually_all (F := F)
      (Q := fun r t => T2' ≤ t ∧ (e.s t).phase r p = .wfl2)
      (fun r hr t t' h h' => ⟨le_trans h'.1 h, persist h'.2 (fun t'' ht'' h'' =>
        (phase_persist e hr (hkeyT r hr t'' (by omega))).2 h'') t' h⟩)
      (fun r hr => by
        obtain ⟨t, ht, h⟩ := stage2 hF hn e hfair hp hr (T := T2') (m := m)
          (fun t ht => hkey r hr t (by omega)) (fun t ht => hbcT t (by omega))
          (fun t ht => (hT2 r hr t (by omega)).2) hecho
        exact ⟨t, ht, h⟩)
    set T3' := max T3 T2'
    have hall : ∀ j ∉ F, ∀ t ≥ T3', (e.s t).phase j p = .wfl2 ∧ (e.s t).key j p = k :=
      fun j hj t ht => ⟨(hT3 j hj t (by omega)).2, hkey j hj t (by omega)⟩
    -- stage 3, for some correct process
    obtain ⟨r1, hr1⟩ : ∃ r1, r1 ∉ F := by
      obtain ⟨r1, hr1⟩ := Finset.card_pos.1 (lt_of_lt_of_le (Nat.succ_pos f)
        (card_correct_le hF hn))
      exact ⟨r1, by simpa using hr1⟩
    obtain ⟨t4, ht4, hslot⟩ := stage3 hF hn e hfair hp hr1 (T := T3') (m := m)
      (fun t ht => hbcT t (by omega)) hall
    have hslotP : ∀ t ≥ t4, SlotOK f (e.s t) r1 k p := persist hslot fun t' _ h =>
      (e.step t').slotOK (InvE.reach hF (e.reach t')) (InvH.reach (e.reach t'))
        (InvE.reach hF (e.reach (t' + 1))) (InvH.reach (e.reach (t' + 1))) hr1 h
    obtain ⟨t5, -, ht5⟩ := deliver_of_slot e hfair hr1 hr1 hslotP (hkey r1 hr1 t4 (by omega))
    exact absurd ht5 (not_le.2 (H r1 hr1 t5))
  -- everybody delivers, and delivers `m`
  obtain ⟨r0, hr0, t1, ht1⟩ := step2
  obtain ⟨m0, hm0⟩ := Option.ne_none_iff_exists'.1
    (((InvF.reach hF (e.reach t1)).dlvIff r0 hr0 p k).2 ⟨hk1.1, ht1⟩)
  obtain ⟨t2, m', hm'⟩ := Exec.totality hF e hfair hr0 hr hm0
  have hb2 := Exec.integrity hF e hr hp hm'
  have e1 := (e.grows (le_max_right t0 t2)).2 p hp k m' hb2
  rw [hbcT (max t0 t2) (le_max_left _ _)] at e1
  cases e1
  exact ⟨t2, hm'⟩

end Podc.RDMAAgreement.RB
