import Papers.PODC2016.TwoBitRegisters.LivenessSteps

/-!
# Liveness (Lemmas 6–9 of the paper)

In every fair execution of the algorithm of Figure 1 with at most `t` crashes, `2t < n`, every
operation invoked by a correct process terminates (`live`).

* Lemma 6 (`lemma6`): for correct `i ≠ j`, `w_sync_i[j]` eventually reaches the current value
  of `w_sync_i[i]` (pairwise synchronization of the alternating-bit `WRITE` exchanges; Lemma 7 —
  no correct process blocks forever at line 11 — is the step `recv_progress`);
* Lemma 8 (`write_terminates`): a write of a correct writer terminates;
* Lemma 9 (`read_terminates`): a read of a correct reader terminates (the `READ()` request
  pipeline to every correct process eventually completes: `pipeline`).
-/

set_option linter.unusedSectionVars false

namespace Podc.TwoBit

open Cslib.SharedMemory Cslib.AsyncMP Cslib.AsyncMP.Protocol

variable {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V]
variable {w : P} {t : ℕ} {v₀ : V}

namespace Liveness

variable (e : (alg w t v₀).Exec)

lemma invW (b : ℕ) : InvW w (e.cfg b) := invW_of_reach (e.reach b)

lemma invP (b : ℕ) : InvP (e.cfg b) := invP_of_reach (e.reach b)

lemma W_mono (i j : P) : Monotone (fun b => W (e.cfg b) i j) :=
  monotone_nat_of_le_succ (fun b => W_step_mono (invW e b) (e.step b) i j)

lemma W_le {a b : ℕ} (hab : a ≤ b) (i j : P) : W (e.cfg a) i j ≤ W (e.cfg b) i j :=
  W_mono e i j hab

lemma sent_le {a b : ℕ} (hab : a ≤ b) (i j : P) : sent (e.cfg a) i j ≤ sent (e.cfg b) i j := by
  have h1 := W_le e hab i i
  have h2 := W_le e hab i j
  simp only [sent]; omega

/-- The writer's history is stable (Lemma 4). -/
lemma Hw_stable (ht : 2 * t < Fintype.card P) {a b : ℕ} (hab : a ≤ b) {k : ℕ}
    (hk : k ≤ W (e.cfg a) w w) : Hw w (e.cfg b) k = Hw w (e.cfg a) k := by
  obtain ⟨ga, hHa⟩ := invH_of_reach ht (e.reach a)
  obtain ⟨gb, hHb⟩ := invH_of_reach ht (e.reach b)
  obtain ⟨β, hβ⟩ := e.hist_prefix hab
  rw [hHb.hist_w k (hk.trans (W_le e hab w w)), hHa.hist_w k hk, hβ, opsOf_append,
    writeVal_append_of_le (by rw [← hHa.own_w]; exact hk)]

lemma step_at {b : ℕ} {s : Step P (register V v₀) (Msg V) (Act P)} (hs : e.stp b = s) :
    (alg w t v₀).step (e.cfg b) s = some (e.cfg (b + 1), e.lbl b) := by
  rw [← hs]; exact e.step b

/-- **Lemma 7** (one step): a `WRITE` message from `i` not yet processed by the correct process `j`
is eventually processed (the parity wait of line 11 eventually holds). -/
lemma recv_progress (hf : e.Fair) (ht : 2 * t < Fintype.card P) {i j : P} (hij : i ≠ j)
    (hi : e.Correct i) (hj : e.Correct j) (T : ℕ) (hlt : W (e.cfg T) j i < sent (e.cfg T) i j) :
    ∃ b ≥ T, W (e.cfg T) j i < W (e.cfg b) j i := by
  obtain ⟨z, hz⟩ : ∃ z, W (e.cfg T) j i = z := ⟨_, rfl⟩
  have hk : z + 1 ≤ W (e.cfg T) w w := by
    have := InvW.sent_le_own (e.cfg T) i j
    have := (invW e T).own_le i
    omega
  refine e.eventually_gt hf hj (.recv i j (.write (par (z + 1)) (Hw w (e.cfg T) (z + 1)))) rfl
    (fun b => W (e.cfg b) j i) (W_mono e j i) T ?_ ?_
  · intro b hb hzb
    simp only [hz] at hzb
    have hsb := sent_le e hb i j
    have hmem := (invW e b).exact i j (z + 1) hij (hi b) (by omega) (by omega)
    rw [Hw_stable e ht hb hk] at hmem
    exact enabled_recv_write (hj b) (Multiset.count_pos.1 hmem) (by rw [hzb])
  · intro b hb hst hzb
    have := W_recv_write (invW e b) (step_at e hst)
    omega

/-- **Lemma 6.** For correct processes `i ≠ j`, `w_sync_i[j]` eventually reaches the value that
`w_sync_i[i]` has at time `T`. -/
theorem lemma6 (hf : e.Fair) (ht : 2 * t < Fintype.card P) {i j : P} (hij : i ≠ j)
    (hi : e.Correct i) (hj : e.Correct j) (T : ℕ) :
    ∃ b ≥ T, W (e.cfg T) i i ≤ W (e.cfg b) i j := by
  refine Exec.eventually_ge (fun b => W (e.cfg b) i j) _ T ?_
  intro T' hT' hlt
  by_contra H
  push Not at H
  obtain ⟨y, hy⟩ : ∃ y, W (e.cfg T') i j = y := ⟨_, rfl⟩
  have hconst : ∀ b ≥ T', W (e.cfg b) i j = y := fun b hb =>
    le_antisymm (hy ▸ H b hb) (hy ▸ W_le e hb i j)
  have hown : ∀ b ≥ T', y < W (e.cfg b) i i := fun b hb => by
    have := W_le e (le_trans hT' hb) i i; omega
  -- `j` eventually processes the `(y+1)`-th message of `i`
  obtain ⟨t1, ht1, hy1⟩ := Exec.eventually_ge (fun b => W (e.cfg b) j i) (y + 1) T' (by
    intro T'' hT'' hlt'
    refine recv_progress e hf ht hij hi hj T'' ?_
    have h1 := hconst T'' hT''
    have h2 := hown T'' hT''
    simp only [sent]; omega)
  -- then `j` sends its `(y+1)`-th message to `i`, which `i` eventually processes
  obtain ⟨b, hb, hlt2⟩ := recv_progress e hf ht (Ne.symm hij) hj hi t1 (by
    have h1 := hconst t1 ht1
    have h2 := (invW e t1).ws_le j i
    simp only [sent]; omega)
  have := hconst b (le_trans ht1 hb)
  have := hconst t1 ht1
  omega

/-! ## Bookkeeping on histories -/

lemma resps_le {a b : ℕ} (hab : a ≤ b) (p : P) :
    (respsOf (e.hist a) p).length ≤ (respsOf (e.hist b) p).length := by
  obtain ⟨β, hβ⟩ := e.hist_prefix hab
  rw [hβ, respsOf_append, List.length_append]; omega

lemma ops_le {a b : ℕ} (hab : a ≤ b) (p : P) :
    (opsOf (e.hist a) p).length ≤ (opsOf (e.hist b) p).length := by
  obtain ⟨β, hβ⟩ := e.hist_prefix hab
  rw [hβ, opsOf_append, List.length_append]; omega

lemma resps_succ_of_ret {b : ℕ} {p : P} {r : V} (h : e.lbl b = some (.ret p r)) :
    (respsOf (e.hist (b + 1)) p).length = (respsOf (e.hist b) p).length + 1 := by
  rw [e.hist_succ, h]; simp

open Classical in
/-- At least `n - t` processes are correct. -/
lemma card_correct (hres : e.Resilient t) :
    Fintype.card P - t ≤ count (fun j => e.Correct j) := by
  have h1 := e.card_faulty_le hres
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset P))
    (fun j => e.Correct j)
  simp only [Finset.card_univ] at h2
  simp only [count]
  omega

/-- If no response of `p` occurs after `T` while `p` has a pending operation at `T`, then `p`
stays busy with the same operation. -/
lemma busy_of_no_resp (ht : 2 * t < Fintype.card P) {p : P} {T : ℕ}
    (hpend : (respsOf (e.hist T) p).length < (opsOf (e.hist T) p).length)
    (H : ∀ b, (respsOf (e.hist b) p).length ≤ (respsOf (e.hist T) p).length) (b : ℕ)
    (hb : T ≤ b) :
    ((e.cfg b).loc p).phase ≠ .idle ∧
      (opsOf (e.hist b) p).length = (opsOf (e.hist T) p).length := by
  obtain ⟨gT, hHT⟩ := invH_of_reach ht (e.reach T)
  obtain ⟨gb, hHb⟩ := invH_of_reach ht (e.reach b)
  have hcT := hHT.cnt p
  have hcb := hHb.cnt p
  have h1 := ops_le e hb p
  have h2 := resps_le e hb p
  have h3 := H b
  by_cases hid : ((e.cfg b).loc p).phase = .idle
  · rw [if_pos hid] at hcb
    split_ifs at hcT <;> omega
  · refine ⟨hid, ?_⟩
    rw [if_neg hid] at hcb
    split_ifs at hcT <;> omega

lemma noret_of_no_resp {p : P} {T : ℕ}
    (H : ∀ b, (respsOf (e.hist b) p).length ≤ (respsOf (e.hist T) p).length) (b : ℕ)
    (hb : T ≤ b) (r : V) : e.lbl b ≠ some (.ret p r) := by
  intro hl
  have := resps_succ_of_ret e hl
  have := resps_le e hb p
  have := H (b + 1)
  omega

/-! ## Lemma 8 -/

/-- **Lemma 8.** If the writer does not crash, each of its write operations terminates. -/
theorem write_terminates (hf : e.Fair) (hres : e.Resilient t) (ht : 2 * t < Fintype.card P)
    (hw : e.Correct w) (T : ℕ)
    (hpend : (respsOf (e.hist T) w).length < (opsOf (e.hist T) w).length) :
    ∃ b, (respsOf (e.hist T) w).length < (respsOf (e.hist b) w).length := by
  by_contra H
  push Not at H
  set wsn := (opsOf (e.hist T) w).length with hwsn
  -- the writer stays at line 3 with `wsn`
  have hph : ∀ b ≥ T, ((e.cfg b).loc w).phase = .w3 wsn ∧ W (e.cfg b) w w = wsn := by
    intro b hb
    obtain ⟨hbusy, hops⟩ := busy_of_no_resp e ht hpend H b hb
    obtain ⟨g, hH⟩ := invH_of_reach ht (e.reach b)
    have hown := hH.own_w
    revert hbusy
    cases hphase : ((e.cfg b).loc w).phase with
    | idle => intro h; exact absurd rfl h
    | w3 n =>
      intro _
      obtain ⟨-, hn⟩ := hH.ph_w3 w n hphase
      refine ⟨by rw [hn, hown, hops], by rw [hown, hops]⟩
    | r7 n => intro _; exact absurd rfl (hH.ph_r7 w n hphase)
    | r9 n => intro _; exact absurd rfl (hH.ph_r9 w n hphase).1
  -- every correct process eventually knows the value
  obtain ⟨B, hB⟩ := Exec.eventually_forall (Q := fun j b => e.Correct j → W (e.cfg b) w j = wsn)
    (by
      intro j
      by_cases hj : e.Correct j
      · by_cases hjw : j = w
        · subst hjw
          exact ⟨T, fun b hb _ => (hph b hb).2⟩
        · obtain ⟨b1, hb1, hle⟩ := lemma6 e hf ht (Ne.symm hjw) hw hj T
          refine ⟨b1, fun b hb _ => ?_⟩
          have h1 := W_le e hb w j
          have h2 := (invW e b).ws_le w j
          have h3 := (hph b (le_trans hb1 hb)).2
          have h4 := (hph T le_rfl).2
          omega
      · exact ⟨0, fun _ _ h => absurd h hj⟩)
  -- hence line 3 is eventually enabled forever
  have hen : ∀ b ≥ max B T, (alg w t v₀).Enabled (e.cfg b) (.internal w .wret) := by
    intro b hb
    refine enabled_internal (hw b) ?_
    have hq : Fintype.card P - t ≤ count (fun j => ((e.cfg b).loc w).ws j = wsn) := by
      classical
      refine (card_correct e hres).trans (count_mono ?_)
      intro j hj; exact hB j b (le_of_max_le_left hb) hj
    simp only [internal, (hph b (le_of_max_le_right hb)).1]
    rw [if_pos hq]; rfl
  obtain ⟨b, hb, hst⟩ := hf _ w rfl hw _ hen
  obtain ⟨r, hr⟩ := wret_label (step_at e hst)
  exact noret_of_no_resp e H b (le_of_max_le_right hb) r hr

/-! ## Lemma 9 -/

/-- The `READ()` request of a reader `p` waiting at line 7 is eventually acknowledged by every
correct process `j` (claim in the proof of Lemma 9): from some time on `r_sync_p[j] = rsn`. -/
lemma pipeline (hf : e.Fair) (ht : 2 * t < Fintype.card P) {p j : P} (hpj : p ≠ j)
    (hp : e.Correct p) (hj : e.Correct j) {T rsn : ℕ}
    (hr7 : ∀ b ≥ T, ((e.cfg b).loc p).phase = .r7 rsn) :
    ∃ b ≥ T, ∀ b' ≥ b, R (e.cfg b') p j = rsn := by
  have hsum : ∀ b ≥ T, cR (e.cfg b) p j + tk (e.cfg b) j p + cP (e.cfg b) j p +
      R (e.cfg b) p j = rsn := by
    intro b hb
    rw [(invP e b).pipe_eq p j hpj (hp b) (hj b)]
    exact ((invP e b).r7_rsn p rsn (hr7 b hb)).symm
  have hbusy : ∀ b ≥ T, ((e.cfg b).loc p).phase ≠ .idle := fun b hb => by rw [hr7 b hb]; simp
  have hst := fun b (hb : b ≥ T) =>
    pipe_step (invW e b) (invP e b) (e.step b) hpj (hbusy b hb) (hj b)
  have hcR_anti : ∀ a b, T ≤ a → a ≤ b → cR (e.cfg b) p j ≤ cR (e.cfg a) p j := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_refl _
    | succ b hab ih => exact (hst b (le_trans ha hab)).1.trans ih
  have hR_mono : ∀ a b, T ≤ a → a ≤ b → R (e.cfg a) p j ≤ R (e.cfg b) p j := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_refl _
    | succ b hab ih => exact ih.trans (hst b (le_trans ha hab)).2.1
  have hcPR_mono : ∀ a b, T ≤ a → a ≤ b →
      cP (e.cfg a) j p + R (e.cfg a) p j ≤ cP (e.cfg b) j p + R (e.cfg b) p j := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_refl _
    | succ b hab ih => exact ih.trans (hst b (le_trans ha hab)).2.2.1
  -- (A) all `READ()` messages from `p` to `j` are received
  obtain ⟨b3, hb3, h3⟩ := Exec.eventually_zero (fun b => cR (e.cfg b) p j) T (by
    intro T0 hT0 hpos
    refine e.eventually_lt hf hj (.recv p j .read) rfl (fun b => cR (e.cfg b) p j) T0
      (fun a b ha hab => hcR_anti a b (le_trans hT0 ha) hab) T0 ?_ ?_
    · intro b hb hc
      have h1 := hc b hb le_rfl
      try simp only at h1 hpos
      refine enabled_recv (hj b) (Multiset.count_pos.1 (by simp only [cR] at h1 hpos; omega)) ?_
      simp [receive]
    · intro b hb hs hfb
      have := pipe_recv_read (step_at e hs)
      try simp only at hfb hpos ⊢
      omega)
  have hcR0 : ∀ b ≥ b3, cR (e.cfg b) p j = 0 := fun b hb => by
    have := hcR_anti b3 b hb3 hb; omega
  -- (B) all pending handlers of `j` for `p` send `PROCEED()`
  obtain ⟨b2, hb2, h2⟩ := Exec.eventually_zero
    (fun b => rsn - (cP (e.cfg b) j p + R (e.cfg b) p j)) b3 (by
    intro T0 hT0 hpos
    try simp only at hpos
    have hsT0 := hsum T0 (le_trans hb3 hT0)
    have hc0 := hcR0 T0 hT0
    have htk : 0 < tk (e.cfg T0) j p := by omega
    obtain ⟨x, hx, hx1⟩ := Multiset.countP_pos.1 htk
    obtain ⟨q, sn⟩ := x
    try simp only at hx1
    subst hx1
    have hsn := (invP e T0).tasks_le j q sn hx
    obtain ⟨b1, hb1, hle⟩ := lemma6 e hf ht (Ne.symm hpj) hj hp T0
    refine e.eventually_lt hf hj (.internal j (.proceed q sn)) rfl
      (fun b => rsn - (cP (e.cfg b) j q + R (e.cfg b) q j)) T0
      (fun a b ha hab => by
        have := hcPR_mono a b (le_trans (le_trans hb3 hT0) ha) hab
        omega) b1 ?_ ?_
    · intro b hb hc
      have hmem : ∀ c, T0 ≤ c → c ≤ b → (q, sn) ∈ ((e.cfg c).loc j).tasks := by
        intro c hc0 hcb
        induction c, hc0 using Nat.le_induction with
        | base => exact hx
        | succ c hc0 ih =>
          rcases (hst c (le_trans (le_trans hb3 hT0) hc0)).2.2.2 sn (ih (by omega)) with h | h
          · exact h
          · exfalso
            have e1 := hc c hc0 (by omega)
            have e2 := hc (c + 1) (by omega) hcb
            try simp only at e1 e2
            omega
      have hm := hmem b (le_trans hb1 hb) le_rfl
      have hW := W_le e hb j q
      refine enabled_internal (hj b) ?_
      have hcond : (q, sn) ∈ ((e.cfg b).loc j).tasks ∧ sn ≤ ((e.cfg b).loc j).ws q :=
        ⟨hm, by simp only [W] at hW hle hsn; omega⟩
      rcases hjl : (e.cfg b).loc j with ⟨hist, ws, rs, ph, tasks⟩
      rw [hjl] at hcond
      cases ph <;> simp [internal, hcond]
    · intro b hb hs hfb
      have := pipe_proceed hpj (step_at e hs)
      try simp only at hfb ⊢
      omega)
  have hcPR : ∀ b ≥ b2, cP (e.cfg b) j p + R (e.cfg b) p j = rsn := fun b hb => by
    have h1 := hcPR_mono b2 b (le_trans hb3 hb2) hb
    have h4 := hsum b (le_trans (le_trans hb3 hb2) hb)
    try simp only at h2
    omega
  -- (C) all `PROCEED()` messages are received
  obtain ⟨b1, hb1, h1⟩ := Exec.eventually_zero (fun b => rsn - R (e.cfg b) p j) b2 (by
    intro T0 hT0 hpos
    refine e.eventually_lt hf hp (.recv j p .proceed) rfl (fun b => rsn - R (e.cfg b) p j) T0
      (fun a b ha hab => by
        have := hR_mono a b (le_trans (le_trans (le_trans hb3 hb2) hT0) ha) hab
        omega) T0 ?_ ?_
    · intro b hb hc
      have e1 := hc b hb le_rfl
      have e2 := hcPR b (le_trans hT0 hb)
      try simp only at e1 hpos
      refine enabled_recv (hp b) (Multiset.count_pos.1 (by simp only [cP] at e2; omega)) ?_
      simp [receive]
    · intro b hb hs hfb
      have := pipe_recv_proceed (step_at e hs)
      try simp only at hfb hpos ⊢
      omega)
  refine ⟨b1, le_trans hb3 (le_trans hb2 hb1), fun b' hb' => ?_⟩
  have := hR_mono b1 b' (le_trans hb3 (le_trans hb2 hb1)) hb'
  have := hsum b' (le_trans (le_trans hb3 (le_trans hb2 hb1)) hb')
  try simp only at h1
  omega

/-- **Lemma 9.** If a reader does not crash, each of its read operations terminates. -/
theorem read_terminates (hf : e.Fair) (hres : e.Resilient t) (ht : 2 * t < Fintype.card P)
    {p : P} (hpw : p ≠ w) (hp : e.Correct p) (T : ℕ)
    (hpend : (respsOf (e.hist T) p).length < (opsOf (e.hist T) p).length) :
    ∃ b, (respsOf (e.hist T) p).length < (respsOf (e.hist b) p).length := by
  by_contra H
  push Not at H
  have hbusy := busy_of_no_resp e ht hpend H
  have hnoret := noret_of_no_resp e H
  -- a reader waiting at line 9 eventually returns (contradiction)
  have hr9 : ∀ T1 ≥ T, ∀ sn, ((e.cfg T1).loc p).phase = .r9 sn → False := by
    intro T1 hT1 sn h9
    have hstay : ∀ b ≥ T1, ((e.cfg b).loc p).phase = .r9 sn := by
      intro b hb
      induction b, hb using Nat.le_induction with
      | base => exact h9
      | succ b hb ih =>
        rcases (phase_step (invW e b) (invP e b) (e.step b) (by rw [ih]; simp)
          (hnoret b (le_trans hT1 hb))).2 with h | ⟨rsn, h1, -⟩
        · rw [h, ih]
        · rw [ih] at h1; cases h1
    obtain ⟨g, hH⟩ := invH_of_reach ht (e.reach T1)
    have hsn := (hH.ph_r9 p sn h9).2
    obtain ⟨B, hB⟩ := Exec.eventually_forall
      (Q := fun j b => e.Correct j → sn ≤ W (e.cfg b) p j) (by
      intro j
      by_cases hj : e.Correct j
      · by_cases hjp : j = p
        · subst hjp; exact ⟨T1, fun b hb _ => hsn.trans (W_le e hb _ _)⟩
        · obtain ⟨b1, hb1, hle⟩ := lemma6 e hf ht (Ne.symm hjp) hp hj T1
          exact ⟨b1, fun b hb _ => le_trans hsn (le_trans hle (W_le e hb p j))⟩
      · exact ⟨0, fun _ _ h => absurd h hj⟩)
    have hen : ∀ b ≥ max B T1, (alg w t v₀).Enabled (e.cfg b) (.internal p .rret) := by
      intro b hb
      refine enabled_internal (hp b) ?_
      have hq : Fintype.card P - t ≤ count (fun j => sn ≤ ((e.cfg b).loc p).ws j) := by
        classical
        exact (card_correct e hres).trans
          (count_mono fun j hj => hB j b (le_of_max_le_left hb) hj)
      simp only [internal, hstay b (le_of_max_le_right hb)]
      rw [if_pos hq]; rfl
    obtain ⟨b, hb, hst⟩ := hf _ p rfl hp _ hen
    obtain ⟨r, hr⟩ := rret_label (step_at e hst)
    exact hnoret b (le_trans hT1 (le_of_max_le_right hb)) r hr
  obtain ⟨g, hH⟩ := invH_of_reach ht (e.reach T)
  have hbT := (hbusy T le_rfl).1
  cases hphT : ((e.cfg T).loc p).phase with
  | idle => exact hbT hphT
  | w3 n => exact hpw (hH.ph_w3 p n hphT).1
  | r9 sn => exact hr9 T le_rfl sn hphT
  | r7 rsn =>
    -- the reader stays at line 7
    have halt : ∀ b ≥ T, ((e.cfg b).loc p).phase = .r7 rsn ∨
        ∃ sn, ((e.cfg b).loc p).phase = .r9 sn := by
      intro b hb
      induction b, hb using Nat.le_induction with
      | base => exact Or.inl hphT
      | succ b hb ih =>
        rcases (phase_step (invW e b) (invP e b) (e.step b) (hbusy b hb).1
          (hnoret b hb)).2 with h | ⟨rsn', -, h⟩
        · rw [h]; exact ih
        · exact Or.inr ⟨_, h⟩
    have hr7 : ∀ b ≥ T, ((e.cfg b).loc p).phase = .r7 rsn := by
      intro b hb
      rcases halt b hb with h | ⟨sn, h⟩
      · exact h
      · exact (hr9 b hb sn h).elim
    -- every correct process eventually acknowledges the request
    obtain ⟨B, hB⟩ := Exec.eventually_forall
      (Q := fun j b => e.Correct j → R (e.cfg b) p j = rsn) (by
      intro j
      by_cases hj : e.Correct j
      · by_cases hjp : j = p
        · subst hjp
          exact ⟨T, fun b hb _ => ((invP e b).r7_rsn j rsn (hr7 b hb)).symm⟩
        · obtain ⟨b1, -, h1⟩ := pipeline e hf ht (Ne.symm hjp) hp hj hr7
          exact ⟨b1, fun b hb _ => h1 b hb⟩
      · exact ⟨0, fun _ _ h => absurd h hj⟩)
    have hen : ∀ b ≥ max B T, (alg w t v₀).Enabled (e.cfg b) (.internal p .r8) := by
      intro b hb
      refine enabled_internal (hp b) ?_
      have hq : Fintype.card P - t ≤ count (fun j => ((e.cfg b).loc p).rs j = rsn) := by
        classical
        exact (card_correct e hres).trans
          (count_mono fun j hj => hB j b (le_of_max_le_left hb) hj)
      simp only [internal, hr7 b (le_of_max_le_right hb)]
      rw [if_pos hq]; rfl
    obtain ⟨b, hb, hst⟩ := hf _ p rfl hp _ hen
    obtain ⟨sn, hsn⟩ := r8_phase (step_at e hst)
    rw [hr7 (b + 1) (by have := le_of_max_le_right hb; omega)] at hsn
    cases hsn

end Liveness

/-- **Theorem 1 (liveness part; Lemmas 8 and 9).** In every fair execution of the algorithm of
Figure 1 in which at most `t` processes crash, with `t < n/2`, every operation invoked by a correct
process terminates. -/
theorem live (ht : 2 * t < Fintype.card P) : (alg w t v₀).Live t := by
  intro e hf hres p hp T hpend
  by_cases hpw : p = w
  · subst hpw; exact Liveness.write_terminates e hf hres ht hp T hpend
  · exact Liveness.read_terminates e hf hres ht hpw hp T hpend

end Podc.TwoBit
