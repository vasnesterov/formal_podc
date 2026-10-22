import Papers.PODC2019.SmallBuffersAQT.Round

/-!
# Badness accounting for one HPTS round

Throughout, `A0 = actLv … lam 0` is the final activation of a round at level `lam` and
`F = fwdOf … A0` the resulting forwarding.
-/

namespace Podc.SmallBuffersAQT

open Finset

variable {m ℓ : ℕ} {c : Config} {sel : ℕ → Key → ℕ} {lam : ℕ}

local notation "A0" => actLv m ℓ c sel lam 0
local notation "F" => fwdOf m ℓ c sel (actLv m ℓ c sel lam 0)

lemma pb_pos {u : ℕ} {q : Key} (h : 1 ≤ pb m ℓ c u q) :
    ∃ w, u < w ∧ w < m ^ ℓ ∧ key m ℓ u w = q ∧ 1 ≤ c u w := by
  unfold pb at h
  obtain ⟨w, hw, hne⟩ := exists_ne_zero_of_sum_ne_zero (Nat.one_le_iff_ne_zero.mp h)
  simp only [mem_filter, mem_range] at hw
  exact ⟨w, hw.2.1, hw.1, hw.2.2, by omega⟩

lemma fpAct_dvd {v : ℕ} {q : Key} (h : fpAct m ℓ c lam v = some q) : m ^ lam ∣ q.2 := by
  obtain ⟨h1, -, -, u, -, hb⟩ := fpAct_eq_some h
  obtain ⟨w, -, -, hk, -⟩ := pb_pos (by omega : 1 ≤ pb m ℓ c u q)
  rw [← h1, ← hk]
  exact dvd_xd u w

lemma fpAct_pos_m {v : ℕ} {q : Key} (h : fpAct m ℓ c lam v = some q) : 0 < m := by
  obtain ⟨-, -, -, u, -, hb⟩ := fpAct_eq_some h
  obtain ⟨w, huw, hw, -, -⟩ := pb_pos (by omega : 1 ≤ pb m ℓ c u q)
  have := (two_le_of_lt huw hw).1; omega

/-- Activity at level `lam` is suffix-closed inside a block of `m^lam` nodes (the paper's
footnote 3: `FormPaths` intervals end at level-`lam` intermediate destinations). -/
lemma fpAct_suffix {p i : ℕ} {q : Key} (h : fpAct m ℓ c lam p = some q) (hpi : p ≤ i)
    (hb : p / m ^ lam = i / m ^ lam) : fpAct m ℓ c lam i ≠ none := by
  obtain ⟨h1, h2, h3, u, hu, hbad⟩ := fpAct_eq_some h
  have hix := lt_of_dvd_of_lt (fpAct_pos_m h) (fpAct_dvd h) h2 hb
  refine fpAct_ne_none_of (x := q.2) (u := u) h3 hix (by omega) ?_
  rw [← h1]; exact hbad

lemma actLv_at_level {v : ℕ} {q : Key} (h : A0 v = some q) (hq : q.1 < lam) :
    actLv m ℓ c sel lam q.1 v = some q := by
  rcases actLv_cases (Nat.zero_le lam) h with h' | ⟨-, h2, h3, w, hc, he⟩
  · exact absurd (fpAct_level h') hq.ne
  · rw [actLv_of_lt h2, preBadStep_eq_some]
    exact Or.inr ⟨h3, w, hc, he⟩

/-- If a node was active before level `j` was processed, it already had its final pseudo-buffer. -/
lemma actLv_eq_A0 {j v : ℕ} {q : Key} (h : actLv m ℓ c sel lam j v = some q) :
    A0 v = some q := actLv_mono (Nat.zero_le j) h

variable (hsel : ValidSel m ℓ c sel)
include hsel

lemma F_valid {v w : ℕ} (h : F v = some w) :
    1 ≤ c v w ∧ v < w ∧ w < m ^ ℓ ∧ A0 v = some (key m ℓ v w) :=
  fwdOf_valid hsel h

lemma outQ_F (u : ℕ) (q : Key) :
    outQ m ℓ F u q = if A0 u = some q ∧ 1 ≤ pb m ℓ c u q then 1 else 0 := by
  unfold outQ
  rcases hF : F u with _ | w
  · rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    rw [fwdOf_of_act h1 h2] at hF; cases hF
  · obtain ⟨-, -, -, hA⟩ := F_valid hsel hF
    obtain ⟨q', hq', hpb, -⟩ := fwdOf_eq_some hF
    rw [hA] at hq'; cases hq'
    by_cases hk : key m ℓ u w = q
    · subst hk; simp [hA, hpb]
    · dsimp only; rw [ite_eq_right hk, ite_eq_right]; rintro ⟨h1, -⟩; rw [hA] at h1; exact hk (Option.some.inj h1)

/-- The pseudo-buffer of an arriving packet: same as at the sender inside a segment, a strictly
lower level at the segment's end. -/
lemma arrival_key {u w : ℕ} (h : arrival F u = some w) :
    0 < u ∧ u < w ∧ w < m ^ ℓ ∧ A0 (u - 1) = some (key m ℓ (u - 1) w) ∧
      ((u < xd m ℓ (u - 1) w ∧ key m ℓ u w = key m ℓ (u - 1) w) ∨
        (u = xd m ℓ (u - 1) w ∧ lv m ℓ u w < lv m ℓ (u - 1) w)) := by
  obtain ⟨hu, hF, huw⟩ := arrival_spec h
  obtain ⟨-, h1, hw, hA⟩ := F_valid hsel hF
  refine ⟨hu, huw, hw, hA, ?_⟩
  have hx := lt_xd h1 hw
  rcases Nat.lt_or_ge u (xd m ℓ (u - 1) w) with hlt | hge
  · left
    refine ⟨hlt, ?_⟩
    have := key_succ (m := m) (ℓ := ℓ) h1 hw (by omega)
    rwa [Nat.sub_add_cancel hu] at this
  · right
    have heq : u = xd m ℓ (u - 1) w := by omega
    refine ⟨heq, ?_⟩
    have := lv_xd_lt h1 hw (by omega)
    rwa [← heq] at this

lemma inQ_level {u : ℕ} {q : Key} (h : 1 ≤ inQ m ℓ F u q) : q.1 ≤ lam := by
  unfold inQ at h
  rcases har : arrival F u with _ | w
  · simp [har] at h
  · simp only [har] at h
    split_ifs at h with hk
    · obtain ⟨hu, -, -, hA, hcase⟩ := arrival_key hsel har
      have hl := actLv_level_le (Nat.zero_le lam) hA
      rw [← hk]
      rcases hcase with ⟨-, he⟩ | ⟨-, hl'⟩
      · rw [he]; exact hl
      · exact (hl'.le.trans hl)
    · omega

omit hsel in
/-- If `ActivatePreBad` at level `j1` could activate `v` via the packet `w1` and the left
endpoint of the interval is `≤ v - 1`, it also activates `v - 1`. -/
lemma pred_activated {j1 v w1 : ℕ} (hj1 : j1 < lam)
    (hc : PreBadCond m ℓ c sel j1 (actLv m ℓ c sel lam (j1 + 1)) v w1)
    (ha : lvl m j1 v ≤ v - 1) :
    A0 (v - 1) = some (key m ℓ (lvl m j1 v) w1) := by
  obtain ⟨h0, hf, haw, hlv, hpb, hvx, hall⟩ := hc
  have hlvl : lvl m j1 (v - 1) = lvl m j1 v := lvl_eq_of_between rfl ha (Nat.sub_le v 1)
  have hnone : actLv m ℓ c sel lam (j1 + 1) (v - 1) = none :=
    hall _ (mem_Icc.2 ⟨ha, Nat.sub_le v 1⟩)
  have : actLv m ℓ c sel lam j1 (v - 1) = some (key m ℓ (lvl m j1 v) w1) := by
    rw [actLv_of_lt hj1, preBadStep_eq_some]
    refine Or.inr ⟨hnone, w1, ?_, by rw [hlvl]⟩
    rw [PreBadCond, hlvl]
    refine ⟨h0, hf, haw, hlv, hpb, by omega, fun u hu => hall u ?_⟩
    simp only [mem_Icc] at hu ⊢; omega
  exact actLv_eq_A0 this

/-- (L1) A packet that arrives in a nonempty lower-level pseudo-buffer which does not forward
can only arrive at a node active at level `lam`. -/
lemma fpAct_of_bad_arrival {u w : ℕ} (har : arrival F u = some w)
    (hlow : (key m ℓ u w).1 < lam) (hA : A0 u ≠ some (key m ℓ u w))
    (hpb : 1 ≤ pb m ℓ c u (key m ℓ u w)) : fpAct m ℓ c lam u ≠ none := by
  intro hfp
  obtain ⟨hu, huw, hw, hA1, hcase⟩ := arrival_key hsel har
  have hF : F (u - 1) = some w := (arrival_spec har).2.1
  -- any activation of `u` before some level is not a FormPaths activation
  have notfp : ∀ {j : ℕ} {q : Key}, j ≤ lam → actLv m ℓ c sel lam j u = some q →
      j ≤ q.1 ∧ q.1 < lam ∧ actLv m ℓ c sel lam (q.1 + 1) u = none ∧
        ∃ w1, PreBadCond m ℓ c sel q.1 (actLv m ℓ c sel lam (q.1 + 1)) u w1 ∧
          q = key m ℓ (lvl m q.1 u) w1 := by
    intro j q hj h
    rcases actLv_cases hj h with h' | h'
    · rw [hfp] at h'; cases h'
    · exact h'
  rcases hcase with ⟨hlt, hkey⟩ | ⟨heq, hlv⟩
  · -- inside a segment: `u - 1` is in a pre-bad run that continues to `u`
    set q0 := key m ℓ (u - 1) w with hq0
    rw [hkey] at hlow hA
    rcases actLv_cases (Nat.zero_le lam) hA1 with h' | ⟨-, hj0, hnone, w', hc, he⟩
    · exact absurd (fpAct_level h') hlow.ne
    set j0 := q0.1
    set a := lvl m j0 (u - 1)
    have hc' := hc
    obtain ⟨h0, hf, haw, hlva, hpba, hvx, hall⟩ := hc
    have hx0 : q0.2 = xd m ℓ a w' := by rw [he]; rfl
    have hua : lvl m j0 u = a := by
      have hlx : lvl m j0 (xd m ℓ a w') = a := by
        have := div_succ_eq_xd (m := m) (ℓ := ℓ) haw (fwdOf_valid hsel hf).2.2.1
        rw [hlva] at this
        rw [lvl_eq_of_div_eq this.symm, lvl_lvl]
      exact lvl_eq_of_between hlx (by have := lvl_le (m := m) j0 (u - 1); omega)
        (by rw [← hx0]; exact hlt.le)
    have hunone : actLv m ℓ c sel lam (j0 + 1) u = none := by
      by_contra hne
      obtain ⟨q1, hq1⟩ := Option.ne_none_iff_exists'.1 hne
      obtain ⟨hj1, hj1l, -, w1, hc1, he1⟩ := notfp hj0 hq1
      have hc1' := hc1
      obtain ⟨-, -, -, -, -, -, -⟩ := hc1
      rcases Nat.lt_or_ge (lvl m q1.1 u) u with hlt1 | hge1
      · have hp := pred_activated hj1l hc1' (by omega)
        rw [hA1] at hp
        have hl : q0.1 = (key m ℓ (lvl m q1.1 u) w1).1 := by rw [Option.some.inj hp]
        have hl2 : (key m ℓ (lvl m q1.1 u) w1).1 = q1.1 := hc1'.2.2.2.1
        have : j0 = q0.1 := rfl
        omega
      · have hself : lvl m q1.1 u = u := le_antisymm (lvl_le _ _) hge1
        have hdvd : m ^ (q1.1 + 1) ∣ u := by
          rw [← hself]; exact Dvd.intro_left _ rfl
        have : lvl m j0 u = u := lvl_eq_self_of_dvd ((pow_dvd_pow m (by omega)).trans hdvd)
        have := lvl_le (m := m) j0 (u - 1)
        omega
    have : actLv m ℓ c sel lam j0 u = some q0 := by
      rw [actLv_of_lt hj0, preBadStep_eq_some]
      refine Or.inr ⟨hunone, w', ?_, by rw [hua]; exact he⟩
      rw [PreBadCond, hua]
      refine ⟨h0, hf, haw, hlva, hpba, by rw [← hx0]; exact hlt, fun v hv => ?_⟩
      simp only [mem_Icc] at hv
      rcases Nat.lt_or_ge v u with hvu | hvu
      · exact hall v (mem_Icc.2 ⟨hv.1, by omega⟩)
      · rw [show v = u by omega]; exact hunone
    exact hA (actLv_eq_A0 this)
  · -- at the end of a segment: the packet is pre-bad at the left endpoint `u`
    set q0 := key m ℓ (u - 1) w with hq0
    set j := lv m ℓ u w
    have hj : j < lam := hlow
    have hjq0 : j < q0.1 := hlv
    have hq0l : q0.1 ≤ lam := actLv_level_le (Nat.zero_le lam) hA1
    have hdvd : m ^ (j + 1) ∣ u := by rw [heq]; exact dvd_xd_of_lt hjq0
    have hlu : lvl m j u = u := lvl_eq_self_of_dvd hdvd
    -- `u - 1` was active with `q0` before level `j` was processed
    have hA1' : actLv m ℓ c sel lam (j + 1) (u - 1) = some q0 := by
      rcases actLv_cases (Nat.zero_le lam) hA1 with h' | h'
      · exact actLv_of_fpAct (by omega) h'
      · exact actLv_mono (by omega) (actLv_at_level hA1 h'.2.1)
    have hFj : fwdOf m ℓ c sel (actLv m ℓ c sel lam (j + 1)) (u - 1) = some w := by
      rw [fwdOf_congr (act' := A0) (by rw [hA1', hA1])]; exact hF
    have hunone : actLv m ℓ c sel lam (j + 1) u = none := by
      by_contra hne
      obtain ⟨q1, hq1⟩ := Option.ne_none_iff_exists'.1 hne
      obtain ⟨hj1, hj1l, -, w1, hc1, he1⟩ := notfp (by omega) hq1
      rcases Nat.lt_or_ge (lvl m q1.1 u) u with hlt1 | hge1
      · have h2 := pred_activated hj1l hc1 (by omega)
        rw [hA1] at h2
        have hx : xd m ℓ (u - 1) w = xd m ℓ (lvl m q1.1 u) w1 := by
          have := congrArg Prod.snd (Option.some.inj h2)
          simpa [hq0, key] using this
        have := hc1.2.2.2.2.2.1
        omega
      · have hself : lvl m q1.1 u = u := le_antisymm (lvl_le _ _) hge1
        obtain ⟨-, hf1, -, hlv1, -⟩ := hc1
        rw [hself] at hf1 hlv1
        obtain ⟨q', hq', -, -⟩ := fwdOf_eq_some hf1
        have : fwdOf m ℓ c sel (actLv m ℓ c sel lam (q1.1 + 1)) (u - 1) = F (u - 1) :=
          fwdOf_congr (by rw [hq', actLv_eq_A0 hq'])
        rw [this, hF] at hf1
        cases hf1
        omega
    have : actLv m ℓ c sel lam j u = some (key m ℓ u w) := by
      rw [actLv_of_lt hj, preBadStep_eq_some]
      refine Or.inr ⟨hunone, w, ?_, by rw [hlu]⟩
      rw [PreBadCond, hlu]
      refine ⟨hu, hFj, huw, rfl, hpb, lt_xd huw hw, fun v hv => ?_⟩
      simp only [mem_Icc] at hv
      rw [show v = u by omega]; exact hunone
    exact hA (actLv_eq_A0 this)

end Podc.SmallBuffersAQT
