import Papers.PODC2019.RMESubLogBoth.LiveRepair2

/-!
# Liveness, part 2 (continued): the rank decreases

`rank_step`: while the set of processes in the recovery/`RLock` region does not change, no step
increases the rank `μc`, a step of a driver decreases it, and drivers stay drivers.
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

/-- The setting of the liveness argument for `RLock`: the invariants hold and nobody runs the
recovery code before line 24. -/
def Good (c : Cfg k) : Prop := Inv c ∧ HolderOK c ∧ ∀ q, preW c q = 0

lemma Good.holder_pos {c : Cfg k} (hc : Good c) {h : Fin k} (hh : c.holder = some h) :
    (c.pc h).InR ∨ ∃ y v, c.pc h = .l24 y v := by
  rcases hc.2.1 h hh with hR | ⟨y, -, -, hpc⟩
  · exact .inl hR
  · have h0 := hc.2.2 h
    rcases hpc with hpc | hpc | hpc | ⟨v, hpc | hpc⟩
    · simp [preW, hpc] at h0; split_ifs at h0
    · simp [preW, hpc] at h0
    · simp [preW, hpc] at h0
    · simp [preW, hpc] at h0
    · exact .inr ⟨y, v, hpc⟩

lemma Drv_none {c : Cfg k} (hh : c.holder = none) {p : Fin k} :
    Drv c p ↔ ∃ y v, c.pc p = .l24 y v := by
  simp [Drv, hh]

lemma Drv_some {c : Cfg k} {h : Fin k} (hh : c.holder = some h) {p : Fin k} :
    Drv c p ↔ (∃ x tl V E i a, c.pc h = .l35 x tl V E i a ∧ c.nn a = false ∧
      c.node p = some a) ∨ (p = h ∧ ∀ x tl V E i a, c.pc h = .l35 x tl V E i a → c.nn a = true) := by
  simp only [Drv, hh]

/-- **Rank lemma.** -/
theorem rank_step {c c' : Cfg k} (hc : Good c) (hc' : Good c') {p : Fin k} (hs : Step c p c')
    (hrec : ∀ q, (c.pc q).Rec → (c'.pc q).Rec) :
    μc c' ≤ μc c ∧ (Drv c p → μc c' < μc c) ∧
      (∀ q, q ≠ p → Drv c q → μc c' = μc c → Drv c' q) := by
  have strict : μc c' < μc c → (μc c' ≤ μc c ∧ (Drv c p → μc c' < μc c) ∧
      (∀ q, q ≠ p → Drv c q → μc c' = μc c → Drv c' q)) :=
    fun h => ⟨h.le, fun _ => h, fun _ _ _ he => absurd he h.ne⟩
  have hpos : ∀ {h : Fin k}, c.holder = some h → _ := fun hh => hc.holder_pos hh
  obtain ⟨⟨own, hG, hL⟩, -, h0⟩ := hc
  obtain ⟨⟨own', hG', hL'⟩, -, -⟩ := hc'
  cases hhc : c.holder with
  | none =>
    by_cases hch : c'.holder = c.holder
    · rw [hhc] at hch
      have hμ : μc c' = μc c := by rw [μc_none hch, μc_none hhc]
      refine ⟨hμ.le, ?_, ?_⟩
      · intro hd
        obtain ⟨y, v, hpc⟩ := (Drv_none hhc).1 hd
        have := (step_l24_acq hs hpc (.inl hhc)).2
        rw [hch] at this; cases this
      · intro q hqp hd _
        rw [Drv_none hch, Step.pc_other hs hqp]
        exact (Drv_none hhc).1 hd
    · rcases step_holder hs hch with ⟨x, v, -, -, h1, h2⟩ | ⟨x, v, -, h1⟩
      · apply strict
        rw [μc_some h1, μc_none hhc, h2, blk_eq_zero (by simp [h2])]
        simp [rd]
      · exact absurd (h1.trans hhc.symm) hch
  | some h =>
    have hpos := hpos hhc
    by_cases hph : p = h
    · subst hph
      rcases hpos with hR | ⟨y, v, hpc⟩
      · by_cases hrx : ∃ x v, c.pc p = .rx x v
        · obtain ⟨x, v, hpc⟩ := hrx
          have := hrec p (PC.rec_of_InR hR)
          rw [(step_rx hs hpc).1] at this; simp [PC.Rec, PC.isRec] at this
        push Not at hrx
        by_cases hb : ∃ x tl V E i a, c.pc p = .l35 x tl V E i a ∧ c.nn a = false
        · obtain ⟨x, tl, V, E, i, a, hpc, hna⟩ := hb
          have hcc : c' = c := by
            rcases step_l35 hs hpc with ⟨h1, -⟩ | ⟨-, h1⟩
            · rw [hna] at h1; cases h1
            · exact h1
          subst hcc
          refine ⟨le_rfl, ?_, fun q _ hd _ => hd⟩
          intro hd
          rcases (Drv_some hhc).1 hd with ⟨x', tl', V', E', i', a', hpc', -, hn'⟩ | ⟨-, hnb⟩
          · rw [hpc] at hpc'; cases hpc'
            have hLp := hL p; unfold LI at hLp; rw [hpc] at hLp
            rw [hLp.1] at hn'; cases hn'; rw [hLp.2.2.1] at hna; cases hna
          · rw [hnb _ _ _ _ _ _ hpc] at hna; cases hna
        · have hnb : ∀ x tl V E i a, c.pc p = .l35 x tl V E i a → c.nn a = true := by
            intro x tl V E i a hpc
            by_contra hn
            exact hb ⟨x, tl, V, E, i, a, hpc, by simpa using hn⟩
          rcases step_InR hs hR with ⟨-, hhold⟩ | ⟨x, v, hpc, -⟩
          · apply strict
            have := rd_step (hL p) hs hR hrx hnb
            rw [μc_some (hhold.trans hhc), μc_some hhc, blk_eq_zero hnb]
            have := blk_le c' p; omega
          · exact absurd hpc (hrx x v)
      · apply strict
        obtain ⟨h1, h2⟩ := step_l24_acq hs hpc (.inr hhc)
        rw [μc_some h2, μc_some hhc, h1, hpc, blk_eq_zero (by simp [h1]),
          blk_eq_zero (by simp [hpc])]
        simp [rd]
    · -- a step of another process
      have hh' : c'.holder = some h := by
        by_contra hch
        have hch' : c'.holder ≠ c.holder := by rw [hhc]; exact hch
        rcases step_holder hs hch' with ⟨x, v, -, hl, -, -⟩ | ⟨x, v, hpc, -⟩
        · rw [hhc] at hl
          rcases hl with hl | hl
          · cases hl
          · exact hph (Option.some_injective _ hl).symm
        · have := hG.holder p (by simp [hpc, PC.InR])
          rw [hhc] at this
          exact hph (Option.some_injective _ this).symm
      have hpch : c'.pc h = c.pc h := Step.pc_other hs (Ne.symm hph)
      have hμ : μc c = 4 * rd (c.pc h) + blk c h := μc_some hhc
      have hμ' : μc c' = 4 * rd (c.pc h) + blk c' h := by rw [μc_some hh', hpch]
      by_cases hb : ∃ x tl V E i a, c.pc h = .l35 x tl V E i a ∧ c.nn a = false
      · obtain ⟨x, tl, V, E, i, a, hpc, hna⟩ := hb
        have hLh := hL h; unfold LI at hLh; rw [hpc] at hLh
        obtain ⟨-, -, -, -, EA, -, -, ha, -⟩ := hLh
        obtain ⟨o, ho, hf⟩ := owner_of_nn hG hL h0 ha hna
        have hblk : blk c h = f13 (c.pc o) := by
          rw [blk_of_l35 hpc, hna, ownW_eq hG ho]; rfl
        have hblk' : blk c' h = if c'.nn a then 0 else ownW c' a := blk_of_l35 (hpch.trans hpc)
        by_cases hpo : p = o
        · subst hpo
          apply strict
          rw [hμ, hμ', hblk, hblk']
          have hLp := hL p; unfold LI at hLp
          have hLp' := hL' p; unfold LI at hLp'
          cases hpcp : c.pc p with
          | l13 y =>
            rw [hpcp] at hLp; rw [hLp.1] at ho; cases ho
            have h1 := step_l13 hs hpcp
            rw [h1] at hLp'
            have hn' : c'.nn a = false := by
              by_contra hn
              rcases step_nn_change hs (a := a) (by rw [hna]; simpa using hn) with ⟨m, hm⟩ | ⟨v, hm⟩
                <;> rw [hpcp] at hm <;> cases hm
            rw [hn', ite_eq_right (by simp), ownW_eq hG' hLp'.1, h1]; simp [f13]
          | l14 y m =>
            rw [hpcp] at hLp; rw [hLp.1] at ho; cases ho
            have h1 := step_l14 hs hpcp
            rw [h1] at hLp'
            have hn' : c'.nn a = false := by
              by_contra hn
              rcases step_nn_change hs (a := a) (by rw [hna]; simpa using hn) with ⟨m, hm⟩ | ⟨v, hm⟩
                <;> rw [hpcp] at hm <;> cases hm
            rw [hn', ite_eq_right (by simp), ownW_eq hG' hLp'.1, h1]; simp [f13]
          | l15 y m =>
            rw [hpcp] at hLp; rw [hLp.1] at ho; cases ho
            have h1 := step_l15 hs hpcp
            rw [h1] at hLp'
            rw [ite_eq_left hLp'.2.2.2]; simp [f13]
          | _ => rw [hpcp] at hf; simp [f13] at hf
        · have hnn' : c'.nn a = false := by
            by_contra hn
            rcases step_nn_change hs (a := a) (by rw [hna]; simpa using hn) with ⟨m, hm⟩ | ⟨v, hm⟩
            · have hLp := hL p; unfold LI at hLp; rw [hm] at hLp
              exact hpo (hG.node_inj hLp.1 ho)
            · have hLp := hL p; unfold LI at hLp; rw [hm] at hLp
              exact hpo (hG.node_inj hLp.1 ho)
          have ho' : c'.node o = some a := (Step.node_other hs (Ne.symm hpo)).trans ho
          have hpco : c'.pc o = c.pc o := Step.pc_other hs (Ne.symm hpo)
          have heq : μc c' = μc c := by
            rw [hμ, hμ', hblk, hblk', hnn', ite_eq_right (by simp), ownW_eq hG' ho', hpco]
          refine ⟨heq.le, ?_, ?_⟩
          · intro hd
            rcases (Drv_some hhc).1 hd with ⟨x', tl', V', E', i', a', hpc', -, hn'⟩ | ⟨hph', -⟩
            · rw [hpc] at hpc'; cases hpc'
              exact absurd (hG.node_inj hn' ho) hpo
            · exact absurd hph' hph
          · intro q hqp hd _
            rcases (Drv_some hhc).1 hd with ⟨x', tl', V', E', i', a', hpc', -, hn'⟩ | ⟨-, hnb⟩
            · rw [hpc] at hpc'; cases hpc'
              exact (Drv_some hh').2 (.inl ⟨x, tl, V, E, i, a, hpch.trans hpc, hnn',
                (Step.node_other hs hqp).trans hn'⟩)
            · rw [hnb _ _ _ _ _ _ hpc] at hna; cases hna
      · have hnb : ∀ x tl V E i a, c.pc h = .l35 x tl V E i a → c.nn a = true := by
          intro x tl V E i a hpc
          by_contra hn
          exact hb ⟨x, tl, V, E, i, a, hpc, by simpa using hn⟩
        have hnb' : ∀ x tl V E i a, c'.pc h = .l35 x tl V E i a → c'.nn a = true := by
          intro x tl V E i a hpc
          exact step_nn_mono hs (hnb x tl V E i a (hpch ▸ hpc))
        have heq : μc c' = μc c := by rw [hμ, hμ', blk_eq_zero hnb, blk_eq_zero hnb']
        refine ⟨heq.le, ?_, ?_⟩
        · intro hd
          rcases (Drv_some hhc).1 hd with ⟨x', tl', V', E', i', a', hpc', hna', -⟩ | ⟨hph', -⟩
          · exact absurd ⟨x', tl', V', E', i', a', hpc', hna'⟩ hb
          · exact absurd hph' hph
        · intro q hqp hd _
          rcases (Drv_some hhc).1 hd with ⟨x', tl', V', E', i', a', hpc', hna', -⟩ | ⟨hqh, -⟩
          · exact absurd ⟨x', tl', V', E', i', a', hpc', hna'⟩ hb
          · exact (Drv_some hh').2 (.inr ⟨hqh, hnb'⟩)

end Podc.RMESubLogBoth
