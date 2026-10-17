import Papers.PODC2020.DetectableSpace.Alg1Step

/-!
# Algorithm 1: preservation of the invariant by local steps of a `Write`
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg1

attribute [local simp] LC LCW LCR Ph Dec Kd vw valOf progOf at20b bitOf Loc.stage Loc.isDec
  Loc.prog Loc.kd Loc.is20b Loc.is12 Loc.info

variable {V : Type} [DecidableEq V] {n : ℕ} [NeZero n] {v₀ : V}
variable {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}

lemma pv_self (C : Cfg1 V v₀ n) (r : Fin n) : C.pv = Function.update C.pv r (C.pv r) :=
  (Function.update_eq_self r C.pv).symm

/-- Line 1. -/
theorem step_w1 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    (hr : C.ps r = .run a o b (.w1 v)) : StepOK C h (.step r) := by
  rw [StepOK, step1_sh hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r g.wc, g.wr⟩, L, ?_⟩
  rw [List.append_nil, pv_self C r]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, hm0, -, -, -, -, -, -, -, -, -, -⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, rfl, hcp, hres, hwr⟩, -⟩ := hlc
  apply hI.local r _ _ g.wc
  · rintro a' o' b' l' h1
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, -⟩ := h1
    exact ⟨_, _, hr⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hcp, hres, hwr]
    · simp
    · intro a' v'' b' l' h1 _ _ _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -⟩ := h1
      simpa using hm0 a v rfl
    · intro a' v'' b' l' _ h2
      simp [hwr, hcp] at h2
    · simp
    · intro _ k hk1 hk2; omega
    · simp [hwr]
    · intro _; exact ⟨le_rfl, by simp [hI.R]⟩
    · intro _ h1 h2
      simp only [vw, Loc.info] at h1 h2
      have := hI.f3 r (by rw [← hI.R]; exact h1) (by rw [← hI.R]; exact h2.symm)
      simp [hwr] at this
    · simp [hcp]
    · intro h1; simp [hcp] at h1
    · simp [hwr]
  · rintro a' o' b' l' x h1 h2
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    left; exact ⟨_, _, _, hr, by simpa using h2⟩
  · rintro a' v'' b' l' h1 _ h3 _
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, -, -, -⟩ := h1
    exact ⟨_, _, _, hr, h3⟩
  · exact hI.f3 r
  · intro t p hk
    obtain ⟨ka, -, -⟩ := hk
    exact ⟨ka, by simp [hcp], by simp [hcp]⟩
  · intro hk; simp [hwr] at hk

/-- Line 3. -/
theorem step_w3 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} (hr : C.ps r = .run a o b (.w3 v tr)) : StepOK C h (.step r) := by
  rw [StepOK, step1_pv hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, hm1, -, -, hf1, hf1w, hf2a, hf2b, -, hcl1, -⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, rfl, hcp, hres, hwr⟩, -⟩ := hlc
  apply hI.local r _ _ (g.s r)
  · rintro a' o' b' l' h1
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, -⟩ := h1
    exact ⟨_, _, hr⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hcp, hres, hwr]
    · simp
    · intro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -⟩ := h1
      exact hm1 _ _ _ _ rfl (by simp) h3 (by omega)
    · intro a' v'' b' l' _ h2
      simp [hcp, hwr] at h2
    · simp
    · intro _ k hk1 hk2 hk3
      simpa using hf1 (by simp) k hk1 hk2 hk3
    · exact hf1w
    · intro _
      simpa using hf2a (by simp)
    · intro _
      simpa using hf2b (by simp)
    · simp [hcp]
    · intro _ hb
      exact hcl1 (by simp) (by simpa using hb)
    · simp [hwr]
  · rintro a' o' b' l' x h1 h2
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    left; exact ⟨_, _, _, hr, by simpa using h2⟩
  · rintro a' v'' b' l' h1 _ h3 _
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, -, -, -⟩ := h1
    exact ⟨_, _, _, hr, h3⟩
  · exact hI.f3 r
  · intro t p hk
    obtain ⟨ka, -, -⟩ := hk
    refine ⟨ka, fun _ h2 => ka (by simpa using h2), by simp [hcp]⟩
  · apply hI.hkk_of
    · intro t p hk
      obtain ⟨ka, -, -⟩ := hk
      refine ⟨ka, fun _ h2 => ka (by simpa using h2), by simp [hcp]⟩
    · simp [hwr]

/-- Line 4. -/
theorem step_w4 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} (hr : C.ps r = .run a o b (.w4 v tr mt)) :
    StepOK C h (.step r) := by
  rw [StepOK, step1_pv hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, hm1, -, -, hf1, hf1w, hf2a, hf2b, -, hcl1, -⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, rfl, hcp, hres, hwr, hT⟩, -⟩ := hlc
  apply hI.local r _ _ (g.s r)
  · rintro a' o' b' l' h1
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, -⟩ := h1
    exact ⟨_, _, hr⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hcp, hres, hwr, hT]
    · simp
    · intro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -⟩ := h1
      exact hm1 _ _ _ _ rfl (by simp) h3 (by simp [hcp])
    · intro a' v'' b' l' _ h2
      simp [hcp, hwr] at h2
    · simp
    · intro _ k hk1 hk2 hk3
      simpa using hf1 (by simp) k hk1 hk2 hk3
    · exact hf1w
    · intro _
      simpa using hf2a (by simp)
    · intro _
      simpa using hf2b (by simp)
    · simp [hcp]
    · intro _ hb
      exact hcl1 (by simp) (by simpa using hb)
    · simp [hwr]
  · rintro a' o' b' l' x h1 h2
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    left; exact ⟨_, _, _, hr, by simpa using h2⟩
  · rintro a' v'' b' l' h1 _ h3 _
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, -, -, -⟩ := h1
    exact ⟨_, _, _, hr, by simpa using h3⟩
  · exact hI.f3 r
  · intro t p hk
    rw [hr] at hk
    obtain ⟨ka, kb, kc⟩ := hk
    exact ⟨ka, fun h1 h2 => kb (by simp) (by simpa using h2), by simp [hcp]⟩
  · apply hI.hkk_of
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simp) (by simpa using h2), by simp [hcp]⟩
    · simp [hwr]

/-- Line 5. -/
theorem step_w5 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} (hr : C.ps r = .run a o b (.w5 v tr mt)) :
    StepOK C h (.step r) := by
  rw [StepOK, step1_sh hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil, pv_self C r]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, hm1, -, -, hf1, hf1w, hf2a, hf2b, hd, hcl1, -⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, rfl, hcp, hres, hwr, hrd⟩, -, -, -, -, htt1, -⟩ := hlc
  have hT : (C.pv r).T = mt := by simpa [hcp] using htt1
  have hf2b' : tr.2.1 = r → tr.2.2 ≠ mt := by simpa using hf2b (by simp)
  have hf2a' : g.s r ≤ g.wc ∧ g.rv (g.s r) = tr := by simpa using hf2a (by simp)
  split_ifs with hR
  · -- the check of line 5 succeeds
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hcp, hres, hwr, hT, hrd]
      · simp
      · intro a' v'' b' l' h1 _ h3 _
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm1 _ _ _ _ rfl (by simp) h3 (by simp [hcp])
      · intro a' v'' b' l' _ h2
        simp [hcp, hwr] at h2
      · simp
      · intro _ k hk1 hk2 hk3
        simpa using hf1 (by simp) k hk1 hk2 hk3
      · exact hf1w
      · intro _
        simpa using hf2a (by simp)
      · intro _
        simpa using hf2b (by simp)
      · simp [hcp]
      · intro _ hb
        exact hcl1 (by simp) (by simpa using hb)
      · simp [hwr]
    · rintro a' o' b' l' x h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact ⟨_, _, _, hr, by simpa using h3⟩
    · exact hI.f3 r
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simp) (by simpa using h2), by simp [hcp]⟩
    · -- line 6 is reached: establish the conditions for claim 2
      intro _ _
      simp only [vw, Loc.info]
      by_cases hq : tr.2.1 = r
      · rw [hq]
        simp only [Function.update_self]
        refine ⟨fun h1 => ?_, fun _ h2 => ?_, by simp [hcp]⟩
        · exact absurd (h1.symm.trans hT) (hf2b' hq)
        · exact absurd h2.symm (hf2b' hq)
      · simp only [Function.update_of_ne hq]
        have := hI.kq_last r
        rwa [← hI.R, hR] at this
  · -- the check of line 5 fails: goto 8
    have hlt : g.s r < g.wc := by
      rcases Nat.lt_or_eq_of_le hf2a'.1 with h1 | h1
      · exact h1
      · exact absurd (by rw [hI.R, ← h1, hf2a'.2]) hR
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hcp, hres, hwr, hT, hrd]
      · simp
      · intro a' v'' b' l' h1 _ h3 _
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm1 _ _ _ _ rfl (by simp) h3 (by simp [hcp])
      · intro a' v'' b' l' h1 _
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact (hm1 _ _ _ _ rfl (by simp) hwr (by simp [hcp])).2 hlt
      · simp
      · intro _ k hk1 hk2 hk3
        simpa using hf1 (by simp) k hk1 hk2 hk3
      · exact hf1w
      · intro _
        simpa using hf2a (by simp)
      · intro _
        simpa using hf2b (by simp)
      · intro _; exact hlt
      · intro _ hb
        exact hcl1 (by simp) (by simpa using hb)
      · simp [hwr]
    · rintro a' o' b' l' x h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact ⟨_, _, _, hr, by simpa using h3⟩
    · exact hI.f3 r
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simp) (by simpa using h2),
        fun _ _ => ⟨hT, Nat.zero_le _⟩⟩
    · intro hk; simp [hwr] at hk

/-- Line 6. -/
theorem step_w6 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} (hr : C.ps r = .run a o b (.w6 v tr mt)) :
    StepOK C h (.step r) := by
  rw [StepOK, step1_pv hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, hm1, -, -, hf1, hf1w, hf2a, hf2b, hd, hcl1, -⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, rfl, hcp, hres, hwr, hrd⟩, -, -, -, -, htt1, -⟩ := hlc
  have hT : (C.pv r).T = mt := by simpa [hcp] using htt1
  apply hI.local r _ _ (g.s r)
  · rintro a' o' b' l' h1
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, -⟩ := h1
    exact ⟨_, _, hr⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hres, hwr, hT, hrd]
    · simp
    · intro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -⟩ := h1
      exact hm1 _ _ _ _ rfl (by simp) h3 (by simp [hcp])
    · intro a' v'' b' l' _ h2
      simp [hwr] at h2
    · simp
    · intro _ k hk1 hk2 hk3
      simpa using hf1 (by simp) k hk1 hk2 hk3
    · exact hf1w
    · intro _
      simpa using hf2a (by simp)
    · intro _
      simpa using hf2b (by simp)
    · simp
    · intro _ hb
      exact hcl1 (by simp) (by simpa using hb)
    · simp [hwr]
  · rintro a' o' b' l' x h1 h2
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    left; exact ⟨_, _, _, hr, by simpa using h2⟩
  · rintro a' v'' b' l' h1 _ h3 _
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, -, -, -⟩ := h1
    exact ⟨_, _, _, hr, by simp [hcp]⟩
  · exact hI.f3 r
  · intro t p hk
    rw [hr] at hk
    obtain ⟨ka, kb, kc⟩ := hk
    exact ⟨ka, fun h1 h2 => kb (by simp) (by simpa using h2), by simp⟩
  · apply hI.hkk_of
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simp) (by simpa using h2), by simp⟩
    · intro _; rw [hr]; simp

/-- Line 8 (= 22). -/
theorem step_w8 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} (hr : C.ps r = .run a o b (.w8 v tr mt)) :
    StepOK C h (.step r) := by
  rw [StepOK, step1_pv hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, -, hm2, -, hf1, hf1w, hf2a, hf2b, hd, hcl1, -⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, hres, hrd, -, -⟩, -, -, -, -, -, -⟩ := hlc
  apply hI.local r _ _ (g.s r)
  · rintro a' o' b' l' h1
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, -⟩ := h1
    exact ⟨_, _, hr⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hres, hrd]
    · simp
    · intro a' v'' b' l' _ _ _ h4
      simp at h4
    · intro a' v'' b' l' h1 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -⟩ := h1
      exact hm2 _ _ _ _ rfl (.inr (by simp))
    · simp
    · intro _ k hk1 hk2 hk3
      simpa using hf1 (by simp) k hk1 hk2 hk3
    · exact hf1w
    · intro _
      simpa using hf2a (by simp)
    · intro _
      simpa using hf2b (by simp)
    · intro _; exact hd (by simp)
    · intro _ hb
      exact hcl1 (by simp) (by simpa using hb)
    · intro _ h2; simp at h2
  · rintro a' o' b' l' x h1 h2
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    left; exact ⟨_, _, _, hr, by simpa using h2⟩
  · rintro a' v'' b' l' _ _ h3 _
    simp at h3
  · exact hI.f3 r
  · intro t p hk
    rw [hr] at hk
    obtain ⟨ka, kb, kc⟩ := hk
    exact ⟨ka, fun h1 h2 => kb (by simp) (by simpa using h2),
      fun h1 h2 => by simpa using kc (by simp) (by simpa using h2)⟩
  · intro hk; simp at hk

/-- Line 11 (= 25). -/
theorem step_w11 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} (hr : C.ps r = .run a o b (.w11 v tr mt)) :
    StepOK C h (.step r) := by
  rw [StepOK, step1_pv hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, -, hm2, -, hf1, hf1w, hf2a, hf2b, hd, hcl1, -⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, hcp, hres⟩, -, -, -, hrd, -, -⟩ := hlc
  have hrd' : (C.pv r).rd = some (mt, tr) := by simpa [hcp] using hrd
  apply hI.local r _ _ (g.s r)
  · rintro a' o' b' l' h1
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, -⟩ := h1
    exact ⟨_, _, hr⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hres, hrd', hcp]
    · simp
    · intro a' v'' b' l' _ _ _ h4
      simp [hcp] at h4
    · intro a' v'' b' l' h1 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -⟩ := h1
      exact hm2 _ _ _ _ rfl (.inr (by simp))
    · simp
    · intro _ k hk1 hk2 hk3
      simpa using hf1 (by simp [hcp]) k hk1 hk2 hk3
    · exact hf1w
    · intro _
      simpa using hf2a (by simp [hcp])
    · intro _
      simpa using hf2b (by simp [hcp])
    · intro _; exact hd (by simp)
    · intro _ hb
      exact hcl1 (by simp [hcp]) (by simpa using hb)
    · intro _ h2; simp [hcp] at h2
  · rintro a' o' b' l' x h1 h2
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    left; exact ⟨_, _, _, hr, by simpa using h2⟩
  · rintro a' v'' b' l' _ _ h3 _
    simp [hcp] at h3
  · intro h1 h2
    obtain ⟨-, he⟩ := hf1 (by simp [hcp]) g.wc (hd (by simp)) le_rfl h1
    simp only [he] at h2
    cases mt <;> simp at h2
  · intro t p hk
    rw [hr] at hk
    obtain ⟨ka, kb, kc⟩ := hk
    have hmt : mt = t := by
      by_contra hne
      have := (kc (by simp) (by cases t <;> cases mt <;> simp_all)).2
      simp at this
      exact absurd this (by omega)
    subst hmt
    refine ⟨fun h1 => by cases mt <;> simp at h1, fun h1 h2 => kb (by simp [hcp]) (by simp),
      fun _ h2 => by cases mt <;> simp at h2⟩
  · intro hk; simp [hcp] at hk

/-- Line 12 (= 26). -/
theorem step_w12 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} (hr : C.ps r = .run a o b (.w12 v tr mt)) :
    StepOK C h (.step r) := by
  rw [StepOK, step1_pv hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, -, hm2, -, hf1, hf1w, hf2a, hf2b, hd, hcl1, -⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, hcp, hres⟩, -, -, -, hrd, -, htt2⟩ := hlc
  have hrd' : (C.pv r).rd = some (mt, tr) := by simpa [hcp] using hrd
  have hT : (C.pv r).T = !mt := by simpa using htt2
  apply hI.local r _ _ (g.s r)
  · rintro a' o' b' l' h1
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, -⟩ := h1
    exact ⟨_, _, hr⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hrd', hcp, hT]
    · simp
    · intro a' v'' b' l' _ _ _ h4
      simp [hcp] at h4
    · intro a' v'' b' l' h1 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -⟩ := h1
      exact hm2 _ _ _ _ rfl (.inr (by simp))
    · simp
    · intro _ k hk1 hk2 hk3
      simpa [hrd'] using hf1 (by simp [hcp]) k hk1 hk2 hk3
    · exact hf1w
    · intro _
      simpa [hrd'] using hf2a (by simp [hcp])
    · intro _
      simpa [hrd'] using hf2b (by simp [hcp])
    · intro _; exact hd (by simp)
    · intro _ hb
      exact hcl1 (by simp [hcp]) (by simpa [hrd'] using hb)
    · intro _ h2; simp [hcp] at h2
  · rintro a' o' b' l' x h1 h2
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    right
    intro y hy hya
    rw [hI.entry hr y hy hya]
    simp at h2
    rw [h2]
  · rintro a' v'' b' l' _ _ h3 _
    simp [hcp] at h3
  · exact hI.f3 r
  · intro t p hk
    rw [hr] at hk
    obtain ⟨ka, kb, kc⟩ := hk
    exact ⟨ka, fun h1 h2 => kb (by simp [hcp]) (by simpa [hrd'] using h2),
      fun h1 h2 => by simpa [hrd'] using kc (by simp) (by simpa [hrd'] using h2)⟩
  · intro hk; simp [hcp] at hk

end Alg1

end Papers.PODC2020.DetectableSpace
