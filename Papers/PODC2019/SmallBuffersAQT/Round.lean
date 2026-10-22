import Papers.PODC2019.SmallBuffersAQT.HPTS

/-!
# Analysis of one HPTS round (Claim 2 of Appendix C, repaired)

For a round at level `lam` and every node `i`:
* `Bad_high_eq`: the badness at levels `> lam` does not change;
* `Bad_lam_le`: the level-`lam` badness drops by one if `i` is active at level `lam`
  (`fpAct … i ≠ none`), and `i` is active whenever its level-`lam` badness is positive
  (`fpAct_of_Bad_lam_pos`); this is Lemma 3.4 / Claim 1 of the PPTS analysis;
* `Bad_low_le`: the badness at levels `< lam` grows by at most one, and only if `i` is active at
  level `lam` (the paper's Cases 1–3 in the proof of Claim 2(3)).
-/

namespace Podc.SmallBuffersAQT

open Finset

variable {m ℓ : ℕ}

section Structure

variable (m ℓ) in
/-- Packets leaving pseudo-buffer `q` of `u` (0 or 1). -/
def outQ (f : ℕ → Option ℕ) (u : ℕ) (q : Key) : ℕ :=
  match f u with
  | some w => if key m ℓ u w = q then 1 else 0
  | none => 0

variable (m ℓ) in
/-- Packets arriving in pseudo-buffer `q` of `u` (0 or 1). -/
def inQ (f : ℕ → Option ℕ) (u : ℕ) (q : Key) : ℕ :=
  match arrival f u with
  | some w => if key m ℓ u w = q then 1 else 0
  | none => 0

lemma arrival_spec {f : ℕ → Option ℕ} {u w : ℕ} (h : arrival f u = some w) :
    0 < u ∧ f (u - 1) = some w ∧ u < w := by
  cases u with
  | zero => simp [arrival] at h
  | succ u =>
    simp only [arrival] at h
    split at h
    · rename_i w' hw'
      split_ifs at h with h1
      cases h
      exact ⟨Nat.succ_pos _, by simpa using hw', h1⟩
    · cases h

lemma arrival_eq_some {f : ℕ → Option ℕ} {u w : ℕ} (hu : 0 < u) (hf : f (u - 1) = some w)
    (huw : u < w) : arrival f u = some w := by
  cases u with
  | zero => omega
  | succ u =>
    simp only [Nat.add_sub_cancel] at hf
    simp [arrival, hf, huw]

/-- Effect of a forwarding step on a pseudo-buffer: `pb' + out = pb + in`. -/
lemma pb_fwd {c : Config} {f : ℕ → Option ℕ}
    (hf : ∀ v w, f v = some w → 1 ≤ c v w ∧ v < w ∧ w < m ^ ℓ) (u : ℕ) (q : Key) :
    pb m ℓ (fwd c f) u q + outQ m ℓ f u q = pb m ℓ c u q + inQ m ℓ f u q := by
  set s := (range (m ^ ℓ)).filter (fun w => u < w ∧ key m ℓ u w = q)
  have hout : outQ m ℓ f u q = ∑ w ∈ s, (if f u = some w then 1 else 0) := by
    unfold outQ
    rcases hfu : f u with _ | w0
    · simp
    · obtain ⟨-, h1, h2⟩ := hf u w0 hfu
      simp only [Option.some.injEq, s]
      rw [Finset.sum_ite_eq]
      simp [h1, h2]
  have hin : inQ m ℓ f u q = ∑ w ∈ s, (if arrival f u = some w then 1 else 0) := by
    unfold inQ
    rcases har : arrival f u with _ | w0
    · simp
    · obtain ⟨-, h1, h2⟩ := arrival_spec har
      obtain ⟨-, -, h3⟩ := hf _ _ h1
      simp only [Option.some.injEq, s]
      rw [Finset.sum_ite_eq]
      simp [h2, h3]
  rw [hout, hin]
  unfold pb
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun w _ => ?_
  simp only [fwd]
  by_cases h : f u = some w
  · have := (hf u w h).1
    simp only [h, ite_true]; omega
  · simp only [h, ite_false]; omega

/-- Arithmetic of the change of `max(x - 1, 0)` when `x' + o = x + i`. -/
lemma delta_le {x x' i o : ℕ} (h : x' + o = x + i) (hi : i ≤ 1) (ho : o ≤ 1) :
    ((x' - 1 : ℕ) : ℤ) - ((x - 1 : ℕ) : ℤ) ≤ if i = 1 ∧ o = 0 ∧ 1 ≤ x then 1 else 0 := by
  split_ifs with hc <;> omega

lemma delta_le_neg {x x' i o : ℕ} (h : x' + o = x + i) (hi : i = 0) (ho : o = 1) (hx : 2 ≤ x) :
    ((x' - 1 : ℕ) : ℤ) - ((x - 1 : ℕ) : ℤ) ≤ -1 := by
  omega

end Structure

section Activation

variable {c : Config} {sel : ℕ → Key → ℕ} {lam : ℕ}

lemma actLv_self : actLv m ℓ c sel lam lam = fpAct m ℓ c lam := by
  simp [actLv, actIter]

lemma actLv_of_lt {j : ℕ} (hj : j < lam) :
    actLv m ℓ c sel lam j = preBadStep m ℓ c sel j (actLv m ℓ c sel lam (j + 1)) := by
  unfold actLv
  rw [show lam - j = (lam - (j + 1)) + 1 by omega, actIter]
  congr 1
  omega

lemma preBadStep_of_some {j : ℕ} {act : ℕ → Option Key} {v : ℕ} {q : Key}
    (h : act v = some q) : preBadStep m ℓ c sel j act v = some q := by
  simp [preBadStep, h]

/-- The conditions under which `ActivatePreBad` at level `j` activates node `v` (with `a` the
left endpoint of the level-`j` interval of `v` and `w` the destination of the packet arriving at
`a`). -/
def PreBadCond (m ℓ : ℕ) (c : Config) (sel : ℕ → Key → ℕ) (j : ℕ) (act : ℕ → Option Key)
    (v w : ℕ) : Prop :=
  0 < lvl m j v ∧ fwdOf m ℓ c sel act (lvl m j v - 1) = some w ∧ lvl m j v < w ∧
    lv m ℓ (lvl m j v) w = j ∧ 1 ≤ pb m ℓ c (lvl m j v) (key m ℓ (lvl m j v) w) ∧
    v < xd m ℓ (lvl m j v) w ∧ ∀ u ∈ Icc (lvl m j v) v, act u = none

lemma preBadStep_eq_some {j : ℕ} {act : ℕ → Option Key} {v : ℕ} {q : Key} :
    preBadStep m ℓ c sel j act v = some q ↔
      act v = some q ∨ (act v = none ∧ ∃ w, PreBadCond m ℓ c sel j act v w ∧
        q = key m ℓ (lvl m j v) w) := by
  unfold preBadStep PreBadCond
  rcases hv : act v with _ | q'
  · simp only [reduceCtorEq, false_or, true_and]
    split_ifs with h0
    · rcases hf : fwdOf m ℓ c sel act (lvl m j v - 1) with _ | w
      · simp
      · simp only
        split_ifs with hc
        · simp only [Option.some.injEq]
          constructor
          · rintro rfl; exact ⟨w, ⟨h0, rfl, hc⟩, rfl⟩
          · rintro ⟨w', ⟨-, hw', -⟩, rfl⟩; cases hw'; rfl
        · simp only [false_iff, not_exists, not_and]
          rintro w' ⟨-, hw', hc'⟩ -
          cases hw'; exact hc hc'
    · simp [h0]
  · simp

lemma actLv_succ_mono {k v : ℕ} {q : Key} (h : actLv m ℓ c sel lam (k + 1) v = some q) :
    actLv m ℓ c sel lam k v = some q := by
  by_cases hkl : k < lam
  · rw [actLv_of_lt hkl]; exact preBadStep_of_some h
  · have : lam - k = lam - (k + 1) := by omega
    unfold actLv at h ⊢; rwa [this]

lemma actLv_mono {j j' : ℕ} (hjj : j' ≤ j) {v : ℕ} {q : Key}
    (h : actLv m ℓ c sel lam j v = some q) : actLv m ℓ c sel lam j' v = some q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjj
  induction d generalizing j' with
  | zero => simpa using h
  | succ d ih =>
    exact actLv_succ_mono (ih (j' := j' + 1) (by omega) (by rwa [show j' + 1 + d = j' + (d + 1) by omega]))

lemma fpAct_eq_some {v : ℕ} {q : Key} (h : fpAct m ℓ c lam v = some q) :
    q.1 = lam ∧ v < q.2 ∧ q.2 < m ^ ℓ ∧ ∃ u ≤ v, 2 ≤ pb m ℓ c u q := by
  unfold fpAct at h
  split_ifs at h with hne
  cases h
  have hmem := max'_mem _ hne
  simp only [mem_filter, mem_range] at hmem
  obtain ⟨h1, h2, u, hu⟩ := hmem.1, hmem.2.1, hmem.2.2
  simp only [mem_filter, mem_range] at hu
  exact ⟨rfl, h2, h1, u, by omega, hu.2⟩

lemma fpAct_ne_none_of {v x u : ℕ} (hx : x < m ^ ℓ) (hvx : v < x) (huv : u ≤ v)
    (hb : 2 ≤ pb m ℓ c u (lam, x)) : fpAct m ℓ c lam v ≠ none := by
  have hne : ((range (m ^ ℓ)).filter (fun x => v < x ∧
      ((range (v + 1)).filter (fun u => 2 ≤ pb m ℓ c u (lam, x))).Nonempty)).Nonempty :=
    ⟨x, mem_filter.2 ⟨mem_range.2 hx, hvx, ⟨u, mem_filter.2 ⟨mem_range.2 (by omega), hb⟩⟩⟩⟩
  unfold fpAct
  simp [hne]

/-- `fpAct` picks the largest admissible intermediate destination. -/
lemma fpAct_max {v x u : ℕ} {q : Key} (h : fpAct m ℓ c lam v = some q) (hx : x < m ^ ℓ)
    (hvx : v < x) (huv : u ≤ v) (hb : 2 ≤ pb m ℓ c u (lam, x)) : x ≤ q.2 := by
  unfold fpAct at h
  split_ifs at h with hne
  cases h
  exact le_max' _ _ (mem_filter.2 ⟨mem_range.2 hx, hvx, ⟨u, mem_filter.2 ⟨mem_range.2 (by omega), hb⟩⟩⟩)

/-- Structure of the final activation: either a `FormPaths` activation, or an activation by
`ActivatePreBad` at some level `q.1 < lam`. -/
lemma actLv_cases {j : ℕ} (hj : j ≤ lam) {v : ℕ} {q : Key}
    (h : actLv m ℓ c sel lam j v = some q) :
    fpAct m ℓ c lam v = some q ∨
      (j ≤ q.1 ∧ q.1 < lam ∧ actLv m ℓ c sel lam (q.1 + 1) v = none ∧
        ∃ w, PreBadCond m ℓ c sel q.1 (actLv m ℓ c sel lam (q.1 + 1)) v w ∧
          q = key m ℓ (lvl m q.1 v) w) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
  induction d generalizing j q with
  | zero => left; rw [show j = lam by omega, actLv_self] at h; exact h
  | succ d ih' =>
    have hk : j < lam := by omega
    have ih := fun {q : Key} (h : actLv m ℓ c sel lam (j + 1) v = some q) =>
      ih' (j := j + 1) (q := q) (by omega) h (by omega)
    set k := j
    rw [actLv_of_lt hk, preBadStep_eq_some] at h
    rcases h with h | ⟨hnone, w, hcond, rfl⟩
    · rcases ih h with h' | ⟨h1, h2, h3⟩
      · exact Or.inl h'
      · exact Or.inr ⟨by omega, h2, h3⟩
    · have hlv : (key m ℓ (lvl m k v) w).1 = k := hcond.2.2.2.1
      right
      refine ⟨by rw [hlv], by rw [hlv]; exact hk, by rw [hlv]; exact hnone, w, by rw [hlv]; exact hcond,
        by rw [hlv]⟩

lemma fpAct_level {v : ℕ} {q : Key} (h : fpAct m ℓ c lam v = some q) : q.1 = lam :=
  (fpAct_eq_some h).1

/-- Final activation of a node active at level `lam` is its `FormPaths` activation. -/
lemma actLv_of_fpAct {j : ℕ} (hj : j ≤ lam) {v : ℕ} {q : Key} (h : fpAct m ℓ c lam v = some q) :
    actLv m ℓ c sel lam j v = some q :=
  actLv_mono hj (by rwa [actLv_self])

lemma actLv_level_le {j : ℕ} (hj : j ≤ lam) {v : ℕ} {q : Key}
    (h : actLv m ℓ c sel lam j v = some q) : q.1 ≤ lam := by
  rcases actLv_cases hj h with h' | h'
  · exact (fpAct_level h').le
  · exact h'.2.1.le

/-- An activated pseudo-buffer of level `lam` is a `FormPaths` activation. -/
lemma fpAct_of_actLv_level {j : ℕ} (hj : j ≤ lam) {v : ℕ} {q : Key}
    (h : actLv m ℓ c sel lam j v = some q) (hq : q.1 = lam) : fpAct m ℓ c lam v = some q := by
  rcases actLv_cases hj h with h' | h'
  · exact h'
  · omega

lemma fwdOf_congr {act act' : ℕ → Option Key} {u : ℕ} (h : act u = act' u) :
    fwdOf m ℓ c sel act u = fwdOf m ℓ c sel act' u := by
  simp [fwdOf, h]

lemma fwdOf_eq_some {act : ℕ → Option Key} {u w : ℕ} (h : fwdOf m ℓ c sel act u = some w) :
    ∃ q, act u = some q ∧ 1 ≤ pb m ℓ c u q ∧ sel u q = w := by
  unfold fwdOf at h
  rcases hu : act u with _ | q
  · simp [hu] at h
  · simp only [hu] at h
    split_ifs at h with h1
    cases h
    exact ⟨q, rfl, h1, rfl⟩

lemma fwdOf_valid (hsel : ValidSel m ℓ c sel) {act : ℕ → Option Key} {u w : ℕ}
    (h : fwdOf m ℓ c sel act u = some w) :
    1 ≤ c u w ∧ u < w ∧ w < m ^ ℓ ∧ act u = some (key m ℓ u w) := by
  obtain ⟨q, hq, hpb, rfl⟩ := fwdOf_eq_some h
  obtain ⟨h1, h2, h3, h4⟩ := hsel u q hpb
  exact ⟨h1, h2, h3, by rw [h4]; exact hq⟩

lemma fwdOf_of_act {act : ℕ → Option Key} {u : ℕ} {q : Key} (h : act u = some q)
    (hpb : 1 ≤ pb m ℓ c u q) : fwdOf m ℓ c sel act u = some (sel u q) := by
  simp [fwdOf, h, hpb]

end Activation

end Podc.SmallBuffersAQT
