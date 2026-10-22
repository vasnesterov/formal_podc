import Papers.PODC2019.SmallBuffersAQT.RoundBad

/-!
# Claim 2 (repaired): the badness of a node does not increase in a round

See the module docstring of `Round.lean`.
-/

namespace Podc.SmallBuffersAQT

open Finset

variable {m ℓ : ℕ} {c : Config} {sel : ℕ → Key → ℕ} {lam : ℕ}

local notation "A0" => actLv m ℓ c sel lam 0
local notation "F" => fwdOf m ℓ c sel (actLv m ℓ c sel lam 0)
local notation "C'" => hptsStep m ℓ lam c sel

lemma inQ_le_one (f : ℕ → Option ℕ) (u : ℕ) (q : Key) : inQ m ℓ f u q ≤ 1 := by
  unfold inQ; split <;> [split_ifs <;> omega; omega]

lemma inQ_eq_one {f : ℕ → Option ℕ} {u : ℕ} {q : Key} (h : 1 ≤ inQ m ℓ f u q) :
    ∃ w, arrival f u = some w ∧ key m ℓ u w = q := by
  unfold inQ at h
  rcases har : arrival f u with _ | w
  · simp [har] at h
  · simp only [har] at h
    split_ifs at h with hk
    · exact ⟨w, rfl, hk⟩
    · omega

/-- The start of a `FormPaths` run is a bad pseudo-buffer. -/
lemma fpAct_run_start {u : ℕ} {q : Key} (h : fpAct m ℓ c lam u = some q)
    (hs : ¬ (0 < u ∧ fpAct m ℓ c lam (u - 1) = some q)) : 2 ≤ pb m ℓ c u q := by
  obtain ⟨hq1, hux, hxn, u', hu'u, hb⟩ := fpAct_eq_some h
  have hq : q = (lam, q.2) := by rw [← hq1]
  rcases Nat.lt_or_ge u' u with hlt | hge
  · exfalso
    have hne : fpAct m ℓ c lam (u - 1) ≠ none :=
      fpAct_ne_none_of (x := q.2) (u := u') hxn (by omega) (by omega) (by rw [← hq]; exact hb)
    obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.1 hne
    have hle := fpAct_max hq' hxn (by omega) (by omega : u' ≤ u - 1) (by rw [← hq]; exact hb)
    obtain ⟨hq'1, -, hq'n, u'', hu'', hb'⟩ := fpAct_eq_some hq'
    have hq'e : q' = (lam, q'.2) := by rw [← hq'1]
    rcases lt_or_eq_of_le hle with hlt' | heq'
    · have := fpAct_max h hq'n (by omega) (by omega : u'' ≤ u) (by rw [← hq'e]; exact hb')
      omega
    · apply hs
      refine ⟨by omega, ?_⟩
      rw [hq', hq'e, hq, heq']
  · rwa [show u = u' by omega]

/-- Indicator that `u - 1` is active at level `lam` with pseudo-buffer `q`. -/
def gfp (m ℓ : ℕ) (c : Config) (lam : ℕ) (q : Key) (u : ℕ) : ℤ :=
  if 0 < u ∧ fpAct m ℓ c lam (u - 1) = some q then 1 else 0

lemma gfp_succ (q : Key) (u : ℕ) :
    gfp m ℓ c lam q (u + 1) = if fpAct m ℓ c lam u = some q then 1 else 0 := by
  simp [gfp]

variable (hsel : ValidSel m ℓ c sel)
include hsel

lemma pb_step (u : ℕ) (q : Key) :
    pb m ℓ C' u q + (if A0 u = some q ∧ 1 ≤ pb m ℓ c u q then 1 else 0) =
      pb m ℓ c u q + inQ m ℓ F u q := by
  rw [← outQ_F hsel]
  exact pb_fwd (fun v w h => let ⟨a, b, d, _⟩ := F_valid hsel h; ⟨a, b, d⟩) u q

/-- Claim 2 (1): pseudo-buffers of levels above `lam` are untouched. -/
lemma pb_step_high {u : ℕ} {q : Key} (hq : lam < q.1) : pb m ℓ C' u q = pb m ℓ c u q := by
  have h := pb_step (lam := lam) hsel u q
  have h1 : ¬ (A0 u = some q ∧ 1 ≤ pb m ℓ c u q) := fun ⟨h1, _⟩ =>
    absurd (actLv_level_le (Nat.zero_le lam) h1) (by omega)
  have h2 : inQ m ℓ F u q = 0 := by
    by_contra hne
    have := inQ_level hsel (by omega : 1 ≤ inQ m ℓ F u q)
    omega
  rw [ite_eq_right h1, h2] at h
  omega

theorem Bad_high_eq {L : Finset ℕ} (hL : ∀ j ∈ L, lam < j) (i : ℕ) :
    Bad m ℓ C' L i = Bad m ℓ c L i := by
  unfold Bad
  refine sum_congr rfl fun q hq => sum_congr rfl fun u _ => ?_
  rw [pb_step_high hsel (hL _ (mem_filter.1 hq).2.1)]

lemma inQ_lam {u : ℕ} {q : Key} (hq : q.1 = lam) (h : 1 ≤ inQ m ℓ F u q) :
    0 < u ∧ fpAct m ℓ c lam (u - 1) = some q := by
  obtain ⟨w, har, hk⟩ := inQ_eq_one h
  obtain ⟨hu, -, -, hA, hcase⟩ := arrival_key hsel har
  rcases hcase with ⟨-, he⟩ | ⟨-, hl⟩
  · rw [he] at hk
    rw [hk] at hA
    exact ⟨hu, fpAct_of_actLv_level (Nat.zero_le lam) hA hq⟩
  · have := actLv_level_le (Nat.zero_le lam) hA
    have h' : (key m ℓ u w).1 = lam := by rw [hk, hq]
    simp only [key] at h' this
    omega

/-- Per-node, per-pseudo-buffer bound at level `lam` (Lemma 3.4). -/
lemma delta_lam {u : ℕ} {q : Key} (hq : q.1 = lam) :
    (((pb m ℓ C' u q - 1 : ℕ) : ℤ) - ((pb m ℓ c u q - 1 : ℕ) : ℤ)) ≤
      gfp m ℓ c lam q u - gfp m ℓ c lam q (u + 1) := by
  rw [gfp_succ]; unfold gfp
  have h := pb_step (lam := lam) hsel u q
  have hi := inQ_le_one (m := m) (ℓ := ℓ) F u q
  by_cases hfp : fpAct m ℓ c lam u = some q
  · have hA : A0 u = some q := actLv_of_fpAct (Nat.zero_le lam) hfp
    rw [ite_eq_left hfp]
    by_cases hg : 0 < u ∧ fpAct m ℓ c lam (u - 1) = some q
    · rw [ite_eq_left hg]
      have := delta_le h hi (by split_ifs <;> omega)
      refine this.trans ?_
      split_ifs with h1 h2 <;> simp_all
    · rw [ite_eq_right hg]
      have hin : inQ m ℓ F u q = 0 := by
        by_contra hne; exact hg (inQ_lam hsel hq (by omega))
      have h2 := fpAct_run_start hfp hg
      have := delta_le_neg h hin (by rw [ite_eq_left ⟨hA, by omega⟩]) h2
      simpa using this
  · rw [ite_eq_right hfp]
    have ho : ¬ (A0 u = some q ∧ 1 ≤ pb m ℓ c u q) := fun ⟨h1, _⟩ =>
      hfp (fpAct_of_actLv_level (Nat.zero_le lam) h1 hq)
    have := delta_le h hi (by split_ifs; omega)
    refine this.trans ?_
    split_ifs with h1 h2
    · simp
    · exact absurd (inQ_lam hsel hq (by omega)) h2
    · simp
    · simp

/-- Claim 2 (2) together with Lemma 3.4: the level-`lam` badness drops by one at every node that
is active at level `lam`. -/
theorem Bad_lam_le (hlam : lam < ℓ) (i : ℕ) :
    (Bad m ℓ C' {lam} i : ℤ) + (if fpAct m ℓ c lam i ≠ none then 1 else 0) ≤
      Bad m ℓ c {lam} i := by
  set s := (KS m ℓ).filter (fun q => q.1 ∈ ({lam} : Finset ℕ) ∧ i < q.2)
  have hsum : (Bad m ℓ C' {lam} i : ℤ) - Bad m ℓ c {lam} i ≤
      ∑ q ∈ s, -(if fpAct m ℓ c lam i = some q then 1 else 0 : ℤ) := by
    unfold Bad
    push_cast
    rw [← sum_sub_distrib]
    refine sum_le_sum fun q hq => ?_
    have hq1 : q.1 = lam := by simpa using (mem_filter.1 hq).2.1
    rw [← sum_sub_distrib]
    refine (sum_le_sum fun u _ => delta_lam hsel hq1).trans (le_of_eq ?_)
    rw [sum_range_sub', gfp_succ]
    simp [gfp]
  have hs : ∑ q ∈ s, -(if fpAct m ℓ c lam i = some q then 1 else 0 : ℤ) =
      -(if fpAct m ℓ c lam i ≠ none then 1 else 0) := by
    rw [sum_neg_distrib]
    congr 1
    rcases hfi : fpAct m ℓ c lam i with _ | q0
    · simp
    · obtain ⟨h1, h2, h3, -⟩ := fpAct_eq_some hfi
      simp only [Option.some.injEq]
      rw [sum_ite_eq]
      rw [ite_eq_left]
      · simp
      · simp only [s, KS, mem_filter, mem_product, mem_range, mem_singleton]
        exact ⟨⟨by omega, h3⟩, h1, h2⟩
  linarith

omit hsel in
/-- Claim 1 of the PPTS analysis: positive level-`lam` badness forces activity at level `lam`. -/
theorem fpAct_of_Bad_lam_pos {i : ℕ} (h : 0 < Bad m ℓ c {lam} i) : fpAct m ℓ c lam i ≠ none := by
  unfold Bad at h
  obtain ⟨q, hq, hpos⟩ := exists_ne_zero_of_sum_ne_zero h.ne'
  obtain ⟨u, hu, hpos'⟩ := exists_ne_zero_of_sum_ne_zero hpos
  simp only [KS, mem_filter, mem_product, mem_range, mem_singleton] at hq
  simp only [mem_range] at hu
  have hqe : q = (lam, q.2) := by rw [← hq.2.1]
  exact fpAct_ne_none_of (x := q.2) (u := u) hq.1.2 hq.2.2 (by omega) (by rw [← hqe]; omega)

/-- A bad arrival at `u` counted in the badness of `i`. -/
def BadArr (m ℓ : ℕ) (c : Config) (sel : ℕ → Key → ℕ) (lam i u : ℕ) : Prop :=
  ∃ w, arrival (fwdOf m ℓ c sel (actLv m ℓ c sel lam 0)) u = some w ∧ (key m ℓ u w).1 < lam ∧
    i < (key m ℓ u w).2 ∧ actLv m ℓ c sel lam 0 u ≠ some (key m ℓ u w) ∧
    1 ≤ pb m ℓ c u (key m ℓ u w)

lemma BadArr_block {i u : ℕ} (h : BadArr m ℓ c sel lam i u) (hui : u ≤ i) :
    u / m ^ lam = i / m ^ lam := by
  obtain ⟨w, har, hlow, hix, -, -⟩ := h
  obtain ⟨-, huw, hw, -, -⟩ := arrival_key hsel har
  exact div_pow_eq_of_le (div_eq_of_key huw hw hui hix) hlow

lemma fpAct_of_BadArr {i u : ℕ} (h : BadArr m ℓ c sel lam i u) (hui : u ≤ i) :
    fpAct m ℓ c lam i ≠ none := by
  have hb := BadArr_block hsel h hui
  obtain ⟨w, har, hlow, -, hA, hpb⟩ := h
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 (fpAct_of_bad_arrival hsel har hlow hA hpb)
  exact fpAct_suffix hq hui hb

lemma BadArr_unique {i u u' : ℕ} (h : BadArr m ℓ c sel lam i u) (h' : BadArr m ℓ c sel lam i u')
    (huu : u < u') (hu'i : u' ≤ i) : False := by
  have hb := BadArr_block hsel h (by omega)
  have hb' := BadArr_block hsel h' hu'i
  have hb1 : u / m ^ lam = (u' - 1) / m ^ lam := by
    apply le_antisymm (Nat.div_le_div_right (by omega))
    rw [hb, ← hb']; exact Nat.div_le_div_right (by omega)
  obtain ⟨w, har, hlow, -, hA, hpb⟩ := h
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 (fpAct_of_bad_arrival hsel har hlow hA hpb)
  obtain ⟨qq, hqq⟩ := Option.ne_none_iff_exists'.1 (fpAct_suffix hq (by omega : u ≤ u' - 1) hb1)
  obtain ⟨hqq1, hqq2, -, -⟩ := fpAct_eq_some hqq
  have hb2 : (u' - 1) / m ^ lam = u' / m ^ lam := by rw [← hb1, hb, hb']
  have hu'x : u' < qq.2 := lt_of_dvd_of_lt (fpAct_pos_m hqq) (fpAct_dvd hqq) hqq2 hb2
  have hAq : A0 (u' - 1) = some qq := actLv_of_fpAct (Nat.zero_le lam) hqq
  obtain ⟨w', har', hlow', -, -, -⟩ := h'
  obtain ⟨-, -, -, hA', hcase⟩ := arrival_key hsel har'
  rw [hAq] at hA'
  have hk := (Option.some.inj hA').symm
  rcases hcase with ⟨-, he⟩ | ⟨he, -⟩
  · rw [he, hk] at hlow'; omega
  · have : qq.2 = xd m ℓ (u' - 1) w' := by rw [← hk]; rfl
    omega

/-- Claim 2 (3), lower levels: their total badness grows by at most one, and only at nodes active
at level `lam` (which lose one unit of level-`lam` badness, `Bad_lam_le`). -/
theorem Bad_low_le (i : ℕ) :
    (Bad m ℓ C' (range lam) i : ℤ) ≤
      Bad m ℓ c (range lam) i + (if fpAct m ℓ c lam i ≠ none then 1 else 0) := by
  classical
  set s := (KS m ℓ).filter (fun q => q.1 ∈ range lam ∧ i < q.2)
  -- per pseudo-buffer bound
  have hper : ∀ u, ∀ q ∈ s, (((pb m ℓ C' u q - 1 : ℕ) : ℤ) - ((pb m ℓ c u q - 1 : ℕ) : ℤ)) ≤
      if key m ℓ u ((arrival F u).getD 0) = q then
        (if (arrival F u).isSome ∧ BadArr m ℓ c sel lam i u then 1 else 0) else 0 := by
    intro u q hq
    have hq' := mem_filter.1 hq
    simp only [mem_range] at hq'
    have h := pb_step (lam := lam) hsel u q
    have hd := delta_le h (inQ_le_one (m := m) (ℓ := ℓ) F u q) (by split_ifs <;> omega)
    refine hd.trans ?_
    by_cases hc : inQ m ℓ F u q = 1 ∧ (if A0 u = some q ∧ 1 ≤ pb m ℓ c u q then 1 else 0) = 0 ∧
        1 ≤ pb m ℓ c u q
    · rw [ite_eq_left hc]
      obtain ⟨w, har, hk⟩ := inQ_eq_one (m := m) (ℓ := ℓ) (by omega : 1 ≤ inQ m ℓ F u q)
      have ho : ¬ (A0 u = some q ∧ 1 ≤ pb m ℓ c u q) := fun h' => by rw [ite_eq_left h'] at hc; omega
      subst hk
      have hb : BadArr m ℓ c sel lam i u :=
        ⟨w, har, hq'.2.1, hq'.2.2, fun h' => ho ⟨h', hc.2.2⟩, hc.2.2⟩
      simp [har, hb]
    · rw [ite_eq_right hc]; split_ifs <;> simp
  have hsum : (Bad m ℓ C' (range lam) i : ℤ) - Bad m ℓ c (range lam) i ≤
      ∑ u ∈ range (i + 1), (if BadArr m ℓ c sel lam i u then 1 else 0 : ℤ) := by
    unfold Bad
    push_cast
    rw [← sum_sub_distrib]
    simp_rw [← sum_sub_distrib]
    rw [sum_comm]
    refine sum_le_sum fun u _ => ?_
    refine (sum_le_sum fun q hq => hper u q hq).trans ?_
    rw [sum_ite_eq]
    split_ifs with h1 h2 <;> simp_all
  have hcount : ∑ u ∈ range (i + 1), (if BadArr m ℓ c sel lam i u then 1 else 0 : ℤ) ≤
      if fpAct m ℓ c lam i ≠ none then 1 else 0 := by
    rw [sum_boole]
    have hcard : ((range (i + 1)).filter (BadArr m ℓ c sel lam i)).card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      simp only [mem_filter, mem_range] at ha hb
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact BadArr_unique hsel ha.2 hb.2 h (by omega)
      · exact BadArr_unique hsel hb.2 ha.2 h (by omega)
    split_ifs with hfp
    · exact_mod_cast hcard
    · have : (range (i + 1)).filter (BadArr m ℓ c sel lam i) = ∅ := by
        rw [filter_eq_empty_iff]
        intro u hu hb
        exact hfp (fpAct_of_BadArr hsel hb (by simpa [Nat.lt_succ_iff] using hu))
      simp [this]
  linarith

end Podc.SmallBuffersAQT
