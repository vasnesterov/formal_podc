import Papers.PODC2023.WaitFreeQueuePolylog.MemOps

/-!
# The memory updates of the algorithm are monotone (`Upd`)
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ} {M : Mem V}

lemma upd2_apply {X : Type} (f : ℕ → ℕ → X) (n j : ℕ) (x : X) (m i : ℕ) :
    upd2 f n j x m i = if m = n ∧ i = j then x else f m i := by
  simp only [upd2]
  by_cases hm : m = n
  · subst hm; by_cases hi : i = j
    · subst hi; simp
    · simp [hi]
  · simp [hm]

/-- A step that changes only the ghost variables of the stepping process. -/
lemma Upd.ghostOnly (p : Fin np) (M : Mem V) (G G' : Ghost np) (hbg : G'.bg = G.bg)
    (hhm : G'.hm = G.hm) (hhs : G'.hs = G.hs)
    (hpg : ∀ q, q ≠ p → G'.pg q = G.pg q ∧ G'.ph q = G.ph q ∧ G'.pg1 q = G.pg1 q) :
    Upd H np p M M G G' where
  blk_eq _ _ _ := rfl
  cnt_mono _ := le_rfl
  cnt_leaf _ _ := rfl
  head_mono _ := le_rfl
  head_inc n h := absurd h (lt_irrefl _)
  sup_mono _ _ _ h := h
  bg_eq _ _ _ := by rw [hbg]
  hm_eq _ _ _ := by rw [hhm]
  hm_new n j h1 h2 := absurd (h1.trans_le h2) (lt_irrefl _)
  hs_eq _ _ _ := by rw [hhs]
  pg_eq := hpg
  lin_ext := ⟨[], by simp⟩

lemma Upd.rfl' (p : Fin np) (M : Mem V) (G : Ghost np) : Upd H np p M M G G :=
  Upd.ghostOnly p M G G rfl rfl rfl (fun _ _ => ⟨rfl, rfl, rfl⟩)

/-- Setting a `super` field. -/
lemma Upd.setSup (hS : Shape H np M) (p : Fin np) (G : Ghost np) (n i x : ℕ)
    (hn : M.sup n i = none) : Upd H np p M (M.setSup n i x) G G where
  blk_eq _ _ _ := rfl
  cnt_mono _ := le_rfl
  cnt_leaf _ _ := rfl
  head_mono _ := le_rfl
  head_inc n h := absurd h (lt_irrefl _)
  sup_mono m j s h := by
    rw [setSup_sup, if_neg]; exact h
    rintro ⟨rfl, rfl⟩; rw [hn] at h; cases h
  bg_eq _ _ _ := rfl
  hm_eq _ _ _ := rfl
  hm_new n j h1 h2 := absurd (h1.trans_le h2) (lt_irrefl _)
  hs_eq _ _ _ := rfl
  pg_eq _ _ := ⟨rfl, rfl, rfl⟩
  lin_ext := ⟨[], by rw [List.append_nil]; exact rootLin_eq hS (fun _ _ _ => rfl) rfl⟩

/-- Advancing a `head` field (with the ghost update of `hs`). -/
lemma Upd.setHead (hS : Shape H np M) (p : Fin np) (G : Ghost np) {w hw : ℕ}
    (hn : (M.blk w hw).isSome) (hh : M.head w = hw) :
    Upd H np p M (M.setHead w (hw + 1)) G
      ⟨G.pg, G.ph, G.pg1, G.bg, G.hm, upd2 G.hs w (hw + 1) (ccnt M w)⟩ where
  blk_eq _ _ _ := rfl
  cnt_mono m := (hS.cnt_setHead hn hh m).ge
  cnt_leaf q _ := hS.cnt_setHead hn hh _
  head_mono m := by rw [setHead_head]; split_ifs with h <;> [subst h; skip] <;> omega
  head_inc m h := by
    rw [setHead_head] at h ⊢
    split_ifs at h ⊢ with hm
    · subst hm; refine ⟨by omega, by rw [hh]; exact hn, ?_⟩
      simp [upd2_apply]
    · omega
  sup_mono _ _ _ h := h
  bg_eq _ _ _ := rfl
  hm_eq _ _ _ := rfl
  hm_new n j h1 h2 := by rw [hS.cnt_setHead hn hh] at h2; omega
  hs_eq m j hj := by
    simp only [upd2_apply]; rw [if_neg (by rintro ⟨rfl, rfl⟩; omega)]
  pg_eq _ _ := ⟨rfl, rfl, rfl⟩
  lin_ext := ⟨[], by
    rw [List.append_nil]
    exact rootLin_eq hS (fun _ _ _ => rfl) (hS.cnt_setHead hn hh 1)⟩

/-- Installing a fresh block `n.blocks[h]` (with the ghost updates `hm := parent's head` and,
optionally, `bg`). -/
lemma Upd.setBlk (hS : Shape H np M) (p : Fin np) (G : Ghost np) {n h : ℕ} (B : Blk V)
    (hn : M.blk n h = none) (hh : h ≤ M.head n) (hleaf : ∀ q : Fin np, q ≠ p → leafOf H q ≠ n)
    (bg' : ℕ → ℕ → ℕ × ℕ) (hbg : ∀ m j, ¬ (m = n ∧ j = h) → bg' m j = G.bg m j) :
    Upd H np p M (M.setBlk n h B) G
      ⟨G.pg, G.ph, G.pg1, bg', upd2 G.hm n h (M.head (n / 2)), G.hs⟩ where
  blk_eq m j hj := hS.blk_setBlk_old hn B hj
  cnt_mono m := by
    rw [hS.cnt_setBlk hn hh]; split_ifs with hm
    · subst hm; omega
    · exact le_rfl
  cnt_leaf q hq := by rw [hS.cnt_setBlk hn hh, if_neg (hleaf q hq)]
  head_mono _ := le_rfl
  head_inc n h := absurd h (lt_irrefl _)
  sup_mono _ _ _ h := h
  bg_eq m j hj := hbg m j (by
    rintro ⟨rfl, rfl⟩; have := (hS.fresh hn hh).1; omega)
  hm_eq m j hj := by
    simp only [upd2_apply]
    rw [if_neg (by rintro ⟨rfl, rfl⟩; have := (hS.fresh hn hh).1; omega)]
  hm_new m j h1 h2 := by
    rw [hS.cnt_setBlk hn hh] at h2
    split_ifs at h2 with hm
    · subst hm; have := (hS.fresh hn hh).1
      simp only [upd2_apply, true_and]; rw [if_pos (by omega)]
    · omega
  hs_eq _ _ _ := rfl
  pg_eq _ _ := ⟨rfl, rfl, rfl⟩
  lin_ext := by
    have hag := fun (m j : ℕ) (hj : j ≤ cnt M m) => hS.blk_setBlk_old hn B hj
    by_cases h1 : n = 1
    · exact ⟨_, rootLin_succ hS hag (by rw [hS.cnt_setBlk hn hh, if_pos h1.symm, h1])⟩
    · refine ⟨[], ?_⟩
      rw [List.append_nil]
      exact rootLin_eq hS hag (by rw [hS.cnt_setBlk hn hh, if_neg (Ne.symm h1)])

end Podc.WaitFreeQueuePolylog
