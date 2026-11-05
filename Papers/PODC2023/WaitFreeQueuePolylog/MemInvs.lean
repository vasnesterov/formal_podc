import Papers.PODC2023.WaitFreeQueuePolylog.Upd

/-!
# The memory and ghost invariants under the four memory updates
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ} {M : Mem V}

lemma endOf_lt_head (hS : Shape H np M) {m j d : ℕ} (hd : d < 2) (hj : j ≤ cnt M m) :
    endOf M m j d < M.head (2 * m + d) := by
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
  · simpa [endOf, Blk.endd] using (hS.endlt m j hj).1
  · simpa [endOf, Blk.endd] using (hS.endlt m j hj).2

lemma two_mul_div_add {n : ℕ} : 2 * (n / 2) + n % 2 = n := by omega

/-! ### Line 61: setting a `super` field -/

lemma MInv.setSup (hS : Shape H np M) (hm : MInv H M) {w hw hp : ℕ} (hw2 : 2 ≤ w)
    (hwc : hw ≤ cnt M w) (hn : M.sup w hw = none) (hhp : hp ≤ M.head (w / 2)) :
    MInv H (M.setSup w hw hp) := by
  constructor
  · intro n i hi; rw [setSup_sup, if_neg (by rintro ⟨rfl, rfl⟩; rw [cnt_setSup] at hi; omega)]
    exact hm.supNone n i hi
  · intro n hn2 i h1 hi; rw [setSup_sup]; split_ifs
    · rfl
    · exact hm.supSet n hn2 i h1 hi
  · intro n i s hs; rw [setSup_sup] at hs; split_ifs at hs with h
    · obtain ⟨rfl, rfl⟩ := h; cases hs; exact hhp
    · exact hm.supBound n i s hs
  · intro n hn2 b s hb hs j hj hbj
    rw [cnt_setSup] at hj
    change b ≤ endOf M _ _ _ at hbj
    rw [setSup_sup] at hs; split_ifs at hs with h
    · obtain ⟨rfl, rfl⟩ := h
      have := endOf_lt_head hS (m := n / 2) (d := n % 2) (by omega) hj
      rw [two_mul_div_add] at this
      have := hm.supSet n hn2 b hb (by omega)
      rw [hn] at this; cases this
    · exact hm.l12up n hn2 b s hb hs j hj hbj

lemma GInv.setSup {G : Ghost np} (hg : GInv H M G) {w hw hp : ℕ} (hn : M.sup w hw = none)
    (hhm : G.hm w hw ≤ hp) : GInv H (M.setSup w hw hp) G := by
  obtain ⟨a, b, c, d, e, f⟩ := hg
  refine ⟨a, b, c, d, fun n hn2 bb h1 h2 => ⟨(e n hn2 bb h1 h2).1, fun s hs => ?_⟩, f⟩
  rw [setSup_sup] at hs; split_ifs at hs with h
  · obtain ⟨rfl, rfl⟩ := h; cases hs; exact hhm
  · exact (e n hn2 bb h1 h2).2 s hs

/-! ### Line 63: advancing a `head` field -/

lemma MInv.setHead (hS : Shape H np M) (hm : MInv H M) {w hw : ℕ} (hn : (M.blk w hw).isSome)
    (hh : M.head w = hw) (hsup : 2 ≤ w → (M.sup w hw).isSome) :
    MInv H (M.setHead w (hw + 1)) := by
  have hc := hS.cnt_setHead hn hh
  constructor
  · intro n i hi; rw [hc] at hi; exact hm.supNone n i hi
  · intro n hn2 i h1 hi; rw [setHead_head] at hi; simp only [setHead_sup]
    split_ifs at hi with h
    · subst h
      by_cases hi' : i = hw
      · subst hi'; exact hsup hn2
      · exact hm.supSet n hn2 i h1 (by omega)
    · exact hm.supSet n hn2 i h1 hi
  · intro n i s hs
    refine (hm.supBound n i s hs).trans ?_
    rw [setHead_head]; split_ifs with h
    · subst h; omega
    · exact le_rfl
  · intro n hn2 b s hb hs j hj hbj
    rw [hc] at hj
    exact hm.l12up n hn2 b s hb hs j hj hbj

lemma GInv.setHead (hS : Shape H np M) {G : Ghost np} (hg : GInv H M G) {w hw : ℕ}
    (hn : (M.blk w hw).isSome) (hh : M.head w = hw) :
    GInv H (M.setHead w (hw + 1)) ⟨G.pg, G.ph, G.pg1, G.bg, G.hm, upd2 G.hs w (hw + 1) (ccnt M w)⟩ := by
  have hc := hS.cnt_setHead hn hh
  have hcw : cnt M w = hw := by simp [cnt, hh, hn]
  have hhead : ∀ n, (M.setHead w (hw + 1)).head n = if n = w then hw + 1 else M.head n :=
    fun n => setHead_head M w (hw + 1) n
  obtain ⟨a, b, c, d, e, f⟩ := hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n h1 h2 j hj1 hj; rw [hc] at hj; exact a n h1 h2 j hj1 hj
  · intro n h1 h2 j hj1 hj; rw [hc] at hj
    simp only [upd2_apply]; rw [if_neg (by rintro ⟨rfl, rfl⟩; omega)]
    exact b n h1 h2 j hj1 hj
  · intro n h1 h2 j j' hj hjj' hj'
    simp only [upd2_apply]
    rw [hhead] at hj'
    by_cases hnw : n = w
    · subst hnw; simp only [true_and]; rw [if_pos rfl] at hj'
      by_cases h' : j' = hw + 1
      · rw [if_pos h']
        by_cases hjw : j = hw + 1
        · rw [if_pos hjw]; exact ⟨le_rfl, le_rfl⟩
        · rw [if_neg hjw]; exact d n h1 h2 j (by omega)
      · rw [if_neg h', if_neg (by omega)]; exact c n h1 h2 j j' hj hjj' (by omega)
    · simp only [hnw, false_and, if_false]; rw [if_neg hnw] at hj'; exact c n h1 h2 j j' hj hjj' hj'
  · intro n h1 h2 j hj
    simp only [upd2_apply]; rw [hc, hc]; rw [hhead] at hj
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨le_rfl, le_rfl⟩
    · split_ifs at hj with hnw
      · subst hnw; exact d n h1 h2 j (by
          by_contra hcon; exact h ⟨rfl, by omega⟩)
      · exact d n h1 h2 j hj
  · intro n hn2 bb h1 h2; rw [hc] at h2
    refine ⟨(e n hn2 bb h1 h2).1.trans ?_, (e n hn2 bb h1 h2).2⟩
    rw [hhead]; split_ifs with h
    · rw [h]; omega
    · exact le_rfl
  · intro n hn2 hn3 bb h1 h2 j hj1 hj; rw [hc] at h2 hj; exact f n hn2 hn3 bb h1 h2 j hj1 hj

/-! ### Lines 12 and 35: installing a block -/

lemma endOf_setBlk_old (hS : Shape H np M) {n h : ℕ} (hn : M.blk n h = none) (B : Blk V)
    {m j d : ℕ} (hj : j ≤ cnt M m) : endOf (M.setBlk n h B) m j d = endOf M m j d := by
  simp [endOf, hS.bk_setBlk_old hn B hj]

lemma MInv.setBlk (hS : Shape H np M) (hm : MInv H M) {v h : ℕ} {B : Blk V}
    (hn : M.blk v h = none) (hh : h ≤ M.head v)
    (hsup : ∀ d, d < 2 → ∀ b s, 1 ≤ b → M.sup (2 * v + d) b = some s → b ≤ B.endd d → s ≤ h) :
    MInv H (M.setBlk v h B) := by
  have hc := hS.cnt_setBlk hn hh B
  obtain ⟨hfr, hhd⟩ := hS.fresh hn hh
  constructor
  · intro n i hi; rw [hc] at hi; simp only [setBlk_sup]
    split_ifs at hi with h1
    · subst h1
      by_cases hih : i = h
      · subst hih; exact hm.supNone n i (by omega)
      · exact hm.supNone n i (by omega)
    · exact hm.supNone n i hi
  · intro n hn2 i h1 hi; exact hm.supSet n hn2 i h1 hi
  · intro n i s hs; exact hm.supBound n i s hs
  · intro n hn2 b s hb hs j hj hbj
    simp only [setBlk_sup] at hs
    rw [hc] at hj
    by_cases hnew : n / 2 = v ∧ j = h
    · obtain ⟨h1, rfl⟩ := hnew
      simp only [endOf, setBlk_bk, h1, and_self, if_true] at hbj
      have := hsup (n % 2) (by omega) b s hb (by rw [← h1, two_mul_div_add]; exact hs) hbj
      exact this
    · have hj' : j ≤ cnt M (n / 2) := by
        split_ifs at hj with h1
        · rw [h1]; by_contra hc'; exact hnew ⟨h1, by omega⟩
        · exact hj
      rw [endOf_setBlk_old hS hn B hj'] at hbj
      exact hm.l12up n hn2 b s hb hs j hj' hbj

lemma GInv.setBlk_internal (hS : Shape H np M) {G : Ghost np} (hg : GInv H M G) {v h : ℕ}
    {B : Blk V} {g : ℕ × ℕ} (hv1 : 1 ≤ v) (hv : v < 2 ^ H)
    (hn : M.blk v h = none) (hh : h ≤ M.head v) (hsn : M.sup v h = none)
    (hg1 : g.1 ≤ B.endl) (hg2 : g.2 ≤ B.endr) (hsg1 : (G.hs v h).1 ≤ g.1)
    (hsg2 : (G.hs v h).2 ≤ g.2)
    (hpend : ∀ d, d < 2 → ∀ b, gd g d < b → b ≤ cnt M (2 * v + d) → h ≤ G.hm (2 * v + d) b) :
    GInv H (M.setBlk v h B)
      ⟨G.pg, G.ph, G.pg1, upd2 G.bg v h g, upd2 G.hm v h (M.head (v / 2)), G.hs⟩ := by
  have hc := hS.cnt_setBlk hn hh B
  obtain ⟨hfr, hhd⟩ := hS.fresh hn hh
  have hold := fun {m j : ℕ} (hj : j ≤ cnt M m) => hS.bk_setBlk_old hn B hj
  have key : ∀ m i, i ≤ cnt (M.setBlk v h B) m → (m = v ∧ i = h) ∨ i ≤ cnt M m := by
    intro m i hi; rw [hc] at hi; split_ifs at hi with hm
    · subst hm; by_cases hih : i = h
      · exact Or.inl ⟨rfl, hih⟩
      · exact Or.inr (by omega)
    · exact Or.inr hi
  have hne : ∀ m i, i ≤ cnt M m → ¬ (m = v ∧ i = h) := by
    rintro m i hi ⟨rfl, rfl⟩; omega
  obtain ⟨a, b, c, d, e, f⟩ := hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n h1 h2 j hj1 hj
    simp only [upd2_apply]
    rcases key n j hj with ⟨rfl, rfl⟩ | hj'
    · rw [if_pos ⟨rfl, rfl⟩, setBlk_bk, if_pos ⟨rfl, rfl⟩]; exact ⟨hg1, hg2⟩
    · rw [if_neg (hne n j hj'), hold hj']; exact a n h1 h2 j hj1 hj'
  · intro n h1 h2 j hj1 hj
    simp only [upd2_apply]
    rcases key n j hj with ⟨rfl, rfl⟩ | hj'
    · rw [if_pos ⟨rfl, rfl⟩]; exact ⟨hsg1, hsg2⟩
    · rw [if_neg (hne n j hj')]; exact b n h1 h2 j hj1 hj'
  · intro n h1 h2 j j' hj hjj' hj'; exact c n h1 h2 j j' hj hjj' hj'
  · intro n h1 h2 j hj
    have hcm : ∀ m, cnt M m ≤ cnt (M.setBlk v h B) m := fun m => by
      rw [hc]; split_ifs with hm
      · subst hm; omega
      · exact le_rfl
    obtain ⟨x, y⟩ := d n h1 h2 j hj
    exact ⟨x.trans (hcm _), y.trans (hcm _)⟩
  · intro n hn2 bb h1 h2
    simp only [upd2_apply, setBlk_sup, setBlk_head]
    rcases key n bb h2 with ⟨rfl, rfl⟩ | hj'
    · rw [if_pos ⟨rfl, rfl⟩]
      exact ⟨le_rfl, fun s hs => by rw [hsn] at hs; cases hs⟩
    · rw [if_neg (hne n bb hj')]; exact e n hn2 bb h1 hj'
  · intro n hn2 hn3 bb h1 h2 j hj1 hj
    simp only [upd2_apply]
    rcases key n bb h2 with ⟨rfl, rfl⟩ | hb'
    · rw [if_pos (show n = n ∧ bb = bb from ⟨rfl, rfl⟩)]
      intro _
      have : j ≤ cnt M (n / 2) := by
        rcases key (n / 2) j hj with ⟨h', -⟩ | h'
        · omega
        · exact h'
      exact this.trans (cnt_le_head M _)
    · rw [if_neg (hne n bb hb')]
      rcases key (n / 2) j hj with ⟨h', rfl⟩ | hj'
      · rw [if_pos ⟨h', rfl⟩]
        intro hlt
        have hd : n % 2 < 2 := by omega
        have := hpend (n % 2) hd bb hlt (by rw [← h', two_mul_div_add]; exact hb')
        rwa [← h', two_mul_div_add] at this
      · rw [if_neg (hne (n / 2) j hj')]
        exact f n hn2 hn3 bb h1 hb' j hj1 hj'

lemma GInv.setBlk_leaf (hS : Shape H np M) {G : Ghost np} (hg : GInv H M G) {L h : ℕ}
    {B : Blk V} (hL : 2 ^ H ≤ L) (hn : M.blk L h = none) (hh : h ≤ M.head L)
    (hsn : M.sup L h = none) :
    GInv H (M.setBlk L h B)
      ⟨G.pg, G.ph, G.pg1, G.bg, upd2 G.hm L h (M.head (L / 2)), G.hs⟩ := by
  have hc := hS.cnt_setBlk hn hh B
  obtain ⟨hfr, hhd⟩ := hS.fresh hn hh
  have hold := fun {m j : ℕ} (hj : j ≤ cnt M m) => hS.bk_setBlk_old hn B hj
  have key : ∀ m i, i ≤ cnt (M.setBlk L h B) m → (m = L ∧ i = h) ∨ i ≤ cnt M m := by
    intro m i hi; rw [hc] at hi; split_ifs at hi with hm
    · subst hm; by_cases hih : i = h
      · exact Or.inl ⟨rfl, hih⟩
      · exact Or.inr (by omega)
    · exact Or.inr hi
  have hne : ∀ m i, i ≤ cnt M m → ¬ (m = L ∧ i = h) := by
    rintro m i hi ⟨rfl, rfl⟩; omega
  have hcm : ∀ m, cnt M m ≤ cnt (M.setBlk L h B) m := fun m => by
    rw [hc]; split_ifs with hm
    · subst hm; omega
    · exact le_rfl
  obtain ⟨a, b, c, d, e, f⟩ := hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n h1 h2 j hj1 hj
    rw [hc, if_neg (by omega)] at hj
    rw [hold hj]; exact a n h1 h2 j hj1 hj
  · intro n h1 h2 j hj1 hj
    rw [hc, if_neg (by omega)] at hj
    exact b n h1 h2 j hj1 hj
  · intro n h1 h2 j j' hj hjj' hj'; exact c n h1 h2 j j' hj hjj' hj'
  · intro n h1 h2 j hj
    obtain ⟨x, y⟩ := d n h1 h2 j hj
    exact ⟨x.trans (hcm _), y.trans (hcm _)⟩
  · intro n hn2 bb h1 h2
    simp only [upd2_apply, setBlk_sup, setBlk_head]
    rcases key n bb h2 with ⟨rfl, rfl⟩ | hj'
    · rw [if_pos ⟨rfl, rfl⟩]
      exact ⟨le_rfl, fun s hs => by rw [hsn] at hs; cases hs⟩
    · rw [if_neg (hne n bb hj')]; exact e n hn2 bb h1 hj'
  · intro n hn2 hn3 bb h1 h2 j hj1 hj
    simp only [upd2_apply]
    have hj' : j ≤ cnt M (n / 2) := by
      rw [hc, if_neg (by omega)] at hj; exact hj
    rcases key n bb h2 with ⟨rfl, rfl⟩ | hb'
    · rw [if_pos (show n = n ∧ bb = bb from ⟨rfl, rfl⟩)]
      intro _; exact hj'.trans (cnt_le_head M _)
    · rw [if_neg (hne n bb hb')]
      exact f n hn2 hn3 bb h1 hb' j hj1 hj'

end Podc.WaitFreeQueuePolylog
