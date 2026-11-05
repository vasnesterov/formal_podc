import Papers.PODC2014.DistributedUniversality.InvBStep2

/-! # Preservation of `InvB`: the birth records of `G`; reachable states satisfy `InvB` -/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

theorem pc_upd_post (h : stepFn M s a = some s') {mm : ℕ} (hpre : (s.loc a.proc).pc = .upd mm) :
    (s'.loc a.proc).pc = updPC (k := k) mm ∧ (s'.loc a.proc).r = (s.loc a.proc).r := by
  du_step_cases h <;> rw [hpc] at hpre <;> first
    | (simp at hpre; done)
    | (simp at hpre; subst hpre; simp)

theorem getElem?_append_single {α : Type*} {l : List α} {z : α} {x : ℕ} {β : α}
    (h : (l ++ [z])[x]? = some β) : (x < l.length ∧ l[x]? = some β) ∨ (x = l.length ∧ β = z) := by
  rw [List.getElem?_append] at h
  split_ifs at h with hx
  · exact Or.inl ⟨hx, h⟩
  · right
    have : x - l.length = 0 := by
      by_contra hne
      have : [z][x - l.length]? = none := List.getElem?_eq_none (by simp; omega)
      rw [this] at h; simp at h
    rw [this] at h
    simp at h
    exact ⟨by omega, h.symm⟩

section Fields
variable (I : InvA M s) (B : InvB M s) (hM : M.Good) (h : stepFn M s a = some s')
include I B hM h

theorem InvB.GS1_step : ∀ y (x β : ℕ) (e : Op n), (s'.born y)[x]? = some β →
    (s'.G y)[x]? = some e → ∃ j, s'.finR β y j = some (true, e) := by
  intro y x β e hb he
  have hfm := I.finR_mono h
  rcases GB_cases h y with ⟨h1, h2⟩ | ⟨mm, hpc, hy, htag, -, -, h1, h2⟩
  · rw [h1] at he; rw [h2] at hb
    obtain ⟨j, hj⟩ := B.GS1 y x β e hb he
    exact ⟨j, hfm _ _ _ _ hj⟩
  · rw [h1] at he; rw [h2] at hb
    rcases getElem?_append_single hb with ⟨hx, hb'⟩ | ⟨hx, rfl⟩
    · have hxG : x < (s.G y).length := by rw [← B.born_len]; exact hx
      rw [List.getElem?_append_left hxG] at he
      obtain ⟨j, hj⟩ := B.GS1 y x β e hb' he
      exact ⟨j, hfm _ _ _ _ hj⟩
    · rw [B.born_len] at hx
      subst hx
      rcases getElem?_append_single he with ⟨hx, -⟩ | ⟨-, rfl⟩
      · omega
      · refine ⟨a.proc, hfm _ _ _ _ ?_⟩
        rw [I.finR_loc a.proc (by simp [hpc]) y, htag]

/-- Getting the pre-state uniformity for a round below a birth round. -/
theorem InvB.unif_pre_born {y : Fin k} {x β ρ : ℕ} {V : Op n} (hb : (s'.born y)[x]? = some β)
    (hlt : ρ < β) (hU : Unif s' ρ y V) : Unif s ρ y V := by
  have I' := I.step h
  have hx : x < (s'.G y).length := by
    rw [← InvB.born_len_step I B hM h y]
    exact (List.getElem?_eq_some_iff.1 hb).1
  obtain ⟨j, hj⟩ := InvB.GS1_step I B hM h y x β _ hb (List.getElem?_eq_getElem hx)
  have hle : β ≤ (s'.loc j).r := by
    rcases I'.finR_fut _ _ _ _ hj with h1 | ⟨h1, -⟩ <;> omega
  exact I.unif_pre_of_lt (p := j) h hU (by omega)

theorem InvB.GS3_step : ∀ y (x β ρ : ℕ) V, (s'.born y)[x]? = some β → ρ + 1 < β →
    Unif s' ρ y V → V ∈ (s'.G y).take x := by
  intro y x β ρ V hb hlt hU
  have hUp := InvB.unif_pre_born I B hM h hb (by omega) hU
  rcases GB_cases h y with ⟨h1, h2⟩ | ⟨mm, hpc, hy, -, -, heq, h1, h2⟩
  · rw [h1]; rw [h2] at hb
    exact B.GS3 y x β ρ V hb hlt hUp
  · rw [h1]; rw [h2] at hb
    rcases getElem?_append_single hb with ⟨hx, hb'⟩ | ⟨hx, rfl⟩
    · have hxG : x ≤ (s.G y).length := by rw [← B.born_len]; omega
      rw [List.take_append_of_le_length hxG]
      exact B.GS3 y x β ρ V hb' hlt hUp
    · rw [B.born_len] at hx
      subst hx
      rw [List.take_append_of_le_length le_rfl, List.take_length, ← heq]
      exact B.know a.proc ρ y V hUp (Or.inl hlt)

theorem InvB.GS4_step : ∀ y (x β ρ : ℕ) V, (s'.born y)[x]? = some β → ρ + 1 = β →
    Unif s' ρ y V → V ∈ (s'.G y).take (x + 1) := by
  intro y x β ρ V hb hlt hU
  have hUp := InvB.unif_pre_born I B hM h hb (by omega) hU
  rcases GB_cases h y with ⟨h1, h2⟩ | ⟨mm, hpc, hy, -, -, heq, h1, h2⟩
  · rw [h1]; rw [h2] at hb
    exact B.GS4 y x β ρ V hb hlt hUp
  · have hG' := h1
    rw [h2] at hb
    rcases getElem?_append_single hb with ⟨hx, hb'⟩ | ⟨hx, rfl⟩
    · rw [h1]
      have hxG : x + 1 ≤ (s.G y).length := by rw [← B.born_len]; omega
      rw [List.take_append_of_le_length hxG]
      exact B.GS4 y x β ρ V hb' hlt hUp
    · rw [B.born_len] at hx
      subst hx
      obtain ⟨hpc', hr'⟩ := pc_upd_post h hpc
      have hmk : mm < k := by rw [← hy]; exact y.isLt
      have hpu : pastUpd (s'.loc a.proc).pc y := by
        rw [hpc', pastUpd_updPC hmk]; omega
      have hk := InvB.know_step I B hM h a.proc ρ y V hU (Or.inr ⟨by rw [hr']; omega, hpu⟩)
      have hsub := InvB.hist_G_step I B hM h a.proc y
      have : (s'.G y).take ((s.G y).length + 1) = s'.G y := by
        rw [h1]; simp
      rw [this]
      exact hsub.subset hk

end Fields

theorem InvB.step (I : InvA M s) (B : InvB M s) (hM : M.Good) (h : stepFn M s a = some s') :
    InvB M s' where
  G_nodup := B.G_nodup_step I hM h
  born_len := B.born_len_step I hM h
  hist_G := B.hist_G_step I hM h
  gst_hist := B.gst_hist_step I hM h
  gs_gst := B.gs_gst_step I hM h
  hist_eq := B.hist_eq_step I hM h
  know := InvB.know_step I B hM h
  opPre := InvB.opPre_step I B hM h
  opPost := InvB.opPost_step I B hM h
  PIa := InvB.PIa_step I B hM h
  CI := InvB.CI_step I B hM h
  GS1 := InvB.GS1_step I B hM h
  GS3 := InvB.GS3_step I B hM h
  GS4 := InvB.GS4_step I B hM h

/-- All reachable states satisfy both invariants. -/
theorem Reachable.inv (hM : M.Good) (hs : Reachable M s) : InvA M s ∧ InvB M s := by
  induction hs with
  | refl => exact ⟨invA_init M, invB_init M⟩
  | tail _ hst ih =>
    obtain ⟨a, ha⟩ := hst
    exact ⟨ih.1.step ha, ih.2.step ih.1 hM ha⟩

end Podc.DistributedUniversality
