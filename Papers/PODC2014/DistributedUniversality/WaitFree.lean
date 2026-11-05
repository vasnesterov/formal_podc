import Papers.PODC2014.DistributedUniversality.Progress2

/-!
# Theorem 3: wait-freedom of the constructions with helping (lines L1–L5)
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

/-- The current operation of a process is never in its own local history. -/
def MyOpNin (s : St n k) : Prop := ∀ i x, (i, (s.loc i).cnt x) ∉ (s.loc i).hist x

theorem MyOpNin.step (N : MyOpNin s) (hI : Inv M s) (h : stepFn M s a = some s') :
    MyOpNin s' := by
  intro i y
  obtain ⟨I, B, C, D⟩ := hI
  have fresh : ∀ c, (s.loc a.proc).cnt y < c ∨ (s.loc a.proc).pc = .init →
      ∀ p, (a.proc, c) ∉ (s.loc p).hist y := by
    intro c hc p
    apply C.not_mem_hist_of_fresh
    cases hh : s.invAt a.proc y c with
    | none => rfl
    | some t =>
      rcases hc with hc | hc
      · have := C.inv_cnt _ _ _ _ hh; omega
      · rw [C.inv_init _ _ _ hc] at hh; simp at hh
  by_cases hi : i = a.proc
  · subst hi
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc,
      tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc,
      tUpdAdopt_loc, tWrite_loc, Function.update_self]
    · exact fresh 0 (Or.inr hpc) _
    · exact N _ y
    · exact N _ y
    · exact N _ y
    · exact N _ y
    · exact N _ y
    · exact N _ y
    · exact N _ y
    · -- loc
      split_ifs with hd
      · intro hm
        rcases mem_merge hm with h1 | ⟨q, h1⟩
        · exact fresh _ (Or.inl (by omega)) _ h1
        · exact fresh _ (Or.inl (by omega)) q
            (((B.gs_gst _ q y).trans (B.gst_hist q y)).subset h1)
      · exact hd
    · exact N _ y
    · -- upd mine
      by_cases hy : y = ⟨m, hm⟩
      · subst hy
        simp only [Function.update_self, List.mem_append, List.mem_singleton, not_or]
        refine ⟨fresh _ (Or.inl (by omega)) _, ?_⟩
        rw [hmine]; simp
      · simp only [Function.update_of_ne hy]; exact N _ y
    · by_cases hy : y = ⟨m, hm⟩
      · subst hy
        simp only [Function.update_self, List.mem_append, List.mem_singleton, not_or]
        exact ⟨N _ _, fun e => hmine e.symm⟩
      · simp only [Function.update_of_ne hy]; exact N _ y
    · exact N _ y
    · exact N _ y
  · rw [loc_ne h hi]; exact N i y

theorem Reachable.myOpNin (hM : M.Good) (hs : Reachable M s) : MyOpNin s := by
  induction hs with
  | refl => intro i x; simp [init, initLoc]
  | tail hr hst ih =>
    obtain ⟨a, ha⟩ := hst
    exact ih.step (Reachable.invAll hM hr) ha

end Podc.DistributedUniversality
