import Papers.PODC2019.RMESubLogBoth.LiveToken
import Papers.PODC2019.RMESubLogBoth.InvSteps

/-!
# Liveness, part 3 (cont.): a rank for a waiting process

`tokMu c yp = 10 · #(ports whose node is an unreleased strict ancestor of `yp`) + stage of the
holder of the right to the CS`. It never increases in steps outside the recovery code, and every
step of the holder decreases it (or brings the process of `yp` into the CS).
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation Classical

/-- The port `q` owns a node holding the right to the CS. -/
def HO (c : Cfg k) (q : Fin k) : Prop := ∃ z, c.node q = some z ∧ c.InH z

/-- The port `q` owns an unreleased strict ancestor of `yp`. -/
def Anc (c : Cfg k) (yp : ℕ) (q : Fin k) : Prop :=
  ∃ z, c.node q = some z ∧ TransGen c.Bh yp z ∧ ¬ c.Rel z

/-- Stage of the holder. -/
def HW : PC k → ℕ
  | .l14 _ _ => 6
  | .l15 _ _ => 5
  | .l25 _ _ => 4
  | .l26 _ => 3
  | .cs _ => 2
  | .l28 _ => 1
  | _ => 0

/-- The rank. -/
noncomputable def tokMu (c : Cfg k) (yp : ℕ) : ℕ :=
  10 * (Finset.univ.filter (Anc c yp)).card + ∑ q, if HO c q then HW (c.pc q) else 0

section
variable {c c' : Cfg k} {own : ℕ → ℕ}

lemma HO.unique (hG : Glob c own) {q q' : Fin k} (h : HO c q) (h' : HO c q') : q = q' := by
  obtain ⟨z, hz, hHz⟩ := h
  obtain ⟨z', hz', hHz'⟩ := h'
  have := hG.hUniq z z' hHz hHz'; subst this
  exact hG.node_inj hz hz'

lemma hstage_eq (hG : Glob c own) {s : Fin k} (hs : HO c s) :
    (∑ q, if HO c q then HW (c.pc q) else 0) = HW (c.pc s) := by
  rw [Finset.sum_eq_single s]
  · simp [hs]
  · intro q _ hq; simp only [ite_eq_right_iff]; intro h; exact absurd (h.unique hG hs) hq
  · simp

lemma HW_le (r : PC k) : HW r ≤ 6 := by cases r <;> simp [HW]

lemma hstage_le (hG : Glob c own) : (∑ q, if HO c q then HW (c.pc q) else 0) ≤ 6 := by
  by_cases h : ∃ s, HO c s
  · obtain ⟨s, hs⟩ := h; rw [hstage_eq hG hs]; exact HW_le _
  · push_neg at h; simp [h]

lemma tokMu_eq {yp : ℕ} (hanc : ∀ q, Anc c' yp q ↔ Anc c yp q) (hHO : ∀ q, HO c' q ↔ HO c q)
    (hpc : ∀ q, HO c q → c'.pc q = c.pc q) : tokMu c' yp = tokMu c yp := by
  unfold tokMu
  congr 1
  · congr 2; ext q; simp [hanc q]
  · refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases h : HO c q
    · rw [if_pos ((hHO q).mpr h), if_pos h, hpc q h]
    · rw [if_neg (fun h' => h ((hHO q).mp h')), if_neg h]

/-- A holder of the right to the CS, outside the recovery code, is at lines 14–28. -/
lemma HO.pc (hG : Glob c own) (hL : ∀ q, LI c own q) (hNR : NoRec c) {s : Fin k}
    (h : HO c s) : HW (c.pc s) ≠ 0 := by
  obtain ⟨z, hz, ⟨-, hH⟩⟩ := h
  have hLs := hL s; unfold LI at hLs
  have hpl := hNR.plain s
  cases hpc : c.pc s <;> rw [hpc] at hLs hpl <;> simp only [PC.Plain] at hpl <;> simp [HW]
  · rw [hLs] at hz; cases hz
  · rw [hLs] at hz; cases hz
  · -- line 13: `Pred = NIL`, nobody behind
    rename_i y
    obtain ⟨h1, h2, -, -, h5, h6⟩ := hLs
    rw [h1] at hz; cases hz
    rcases hH with h | ⟨w, hw, -⟩ | ⟨h, -⟩
    · rw [h2] at h; cases h
    · obtain ⟨j, hj, hv⟩ := hw
      have := hG.node_inj hj h1; subst this
      rw [Cfg.vp_of_ovr_none (by simp [hpc, PC.ovr]) hj, h2] at hv; cases hv
    · rw [h2] at h; cases h
  · obtain ⟨y, hy, hr⟩ := hLs
    rw [hy] at hz; cases hz
    exact InH.not_rel hG hL ⟨⟨s, hy⟩, hH⟩ hr

/-- If the view (nodes, `Bh`, `Rel`, `InH`) does not change, neither do `Anc` and `HO`. -/
lemma view_eq {yp : ℕ} (hn : c'.node = c.node) (hBh : c'.Bh = c.Bh) (hRel : c'.Rel = c.Rel)
    (hH : c'.InH = c.InH) : (∀ q, Anc c' yp q ↔ Anc c yp q) ∧ (∀ q, HO c' q ↔ HO c q) := by
  refine ⟨fun q => ?_, fun q => ?_⟩
  · simp only [Anc, hn, hBh, hRel]
  · simp only [HO, hn, hH]

/-- The rank when the holder `s` moves without changing the view. -/
lemma tokMu_view_owner {yp : ℕ} {own' : ℕ → ℕ} (hG : Glob c own) (hG' : Glob c' own') {s : Fin k}
    (hn : c'.node = c.node) (hBh : c'.Bh = c.Bh) (hRel : c'.Rel = c.Rel) (hH : c'.InH = c.InH)
    (hs : HO c s) (hlt : HW (c'.pc s) < HW (c.pc s)) : tokMu c' yp < tokMu c yp := by
  obtain ⟨ha, hho⟩ := view_eq (yp := yp) hn hBh hRel hH
  unfold tokMu
  rw [hstage_eq hG hs, hstage_eq hG' ((hho s).mpr hs)]
  have : (Finset.univ.filter (Anc c' yp)) = Finset.univ.filter (Anc c yp) := by
    ext q; simp [ha q]
  rw [this]; omega

lemma tokMu_view_other {yp : ℕ} {s : Fin k}
    (hn : c'.node = c.node) (hBh : c'.Bh = c.Bh) (hRel : c'.Rel = c.Rel) (hH : c'.InH = c.InH)
    (hs : ¬ HO c s) (hpc : ∀ j, j ≠ s → c'.pc j = c.pc j) :
    tokMu c' yp = tokMu c yp ∧ ∀ q, HO c' q ↔ HO c q := by
  obtain ⟨ha, hho⟩ := view_eq (yp := yp) hn hBh hRel hH
  refine ⟨tokMu_eq ha hho (fun q hq => hpc q (fun h => hs (h ▸ hq))), hho⟩

end

end Podc.RMESubLogBoth
