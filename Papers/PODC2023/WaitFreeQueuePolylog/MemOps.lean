import Papers.PODC2023.WaitFreeQueuePolylog.InvFrame

/-!
# The four kinds of memory updates and the structural invariant

Installing a block (lines 12 and 35), setting a `super` field (line 61) and advancing a `head`
(line 63) preserve `Shape` under the conditions guaranteed by the invariant of the stepping
process.
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ} {M : Mem V}

@[simp] lemma setBlk_head (M : Mem V) (n h : ℕ) (B : Blk V) : (M.setBlk n h B).head = M.head := rfl
@[simp] lemma setBlk_sup (M : Mem V) (n h : ℕ) (B : Blk V) : (M.setBlk n h B).sup = M.sup := rfl
@[simp] lemma setSup_head (M : Mem V) (n i x : ℕ) : (M.setSup n i x).head = M.head := rfl
@[simp] lemma setSup_blk (M : Mem V) (n i x : ℕ) : (M.setSup n i x).blk = M.blk := rfl
@[simp] lemma setHead_blk (M : Mem V) (n h : ℕ) : (M.setHead n h).blk = M.blk := rfl
@[simp] lemma setHead_sup (M : Mem V) (n h : ℕ) : (M.setHead n h).sup = M.sup := rfl

lemma setBlk_blk (M : Mem V) (n h : ℕ) (B : Blk V) (m j : ℕ) :
    (M.setBlk n h B).blk m j = if m = n ∧ j = h then some B else M.blk m j := by
  simp only [Mem.setBlk, upd2]
  by_cases hm : m = n
  · subst hm; by_cases hj : j = h
    · subst hj; simp
    · simp [hj]
  · simp [hm]

lemma setBlk_bk (M : Mem V) (n h : ℕ) (B : Blk V) (m j : ℕ) :
    (M.setBlk n h B).bk m j = if m = n ∧ j = h then B else M.bk m j := by
  simp only [Mem.bk, setBlk_blk]; split_ifs <;> rfl

lemma setSup_sup (M : Mem V) (n i x : ℕ) (m j : ℕ) :
    (M.setSup n i x).sup m j = if m = n ∧ j = i then some x else M.sup m j := by
  simp only [Mem.setSup]
  by_cases hm : m = n
  · subst hm; by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  · simp [hm]

lemma setHead_head (M : Mem V) (n h m : ℕ) :
    (M.setHead n h).head m = if m = n then h else M.head m := by
  simp only [Mem.setHead]; by_cases hm : m = n
  · subst hm; simp
  · simp [hm]

@[simp] lemma setSup_bk (M : Mem V) (n i x : ℕ) : (M.setSup n i x).bk = M.bk := rfl
@[simp] lemma setHead_bk (M : Mem V) (n h : ℕ) : (M.setHead n h).bk = M.bk := rfl

lemma cnt_setSup (M : Mem V) (n i x m : ℕ) : cnt (M.setSup n i x) m = cnt M m := rfl

lemma cnt_setBlk_ne (M : Mem V) (n h : ℕ) (B : Blk V) {m : ℕ} (hm : m ≠ n) :
    cnt (M.setBlk n h B) m = cnt M m := by
  simp [cnt, setBlk_blk, hm]

namespace Shape

/-- Installing at `h ≤ head` an empty slot: it is the slot `head = cnt + 1`. -/
lemma fresh (hS : Shape H np M) {n h : ℕ} (hn : M.blk n h = none) (hh : h ≤ M.head n) :
    h = cnt M n + 1 ∧ M.head n = h := by
  have h1 : ¬ h ≤ cnt M n := fun hc => by simpa [hn] using (hS.inst n h).2 hc
  have := cnt_le_head M n
  have := head_le_cnt_succ M n
  omega

lemma cnt_setBlk_self (hS : Shape H np M) {n h : ℕ} (hn : M.blk n h = none) (hh : h ≤ M.head n)
    (B : Blk V) : cnt (M.setBlk n h B) n = h := by
  obtain ⟨-, h2⟩ := hS.fresh hn hh
  simp [cnt, setBlk_blk, h2]

lemma cnt_setBlk (hS : Shape H np M) {n h : ℕ} (hn : M.blk n h = none) (hh : h ≤ M.head n)
    (B : Blk V) (m : ℕ) : cnt (M.setBlk n h B) m = if m = n then cnt M n + 1 else cnt M m := by
  split_ifs with hm
  · subst hm; rw [hS.cnt_setBlk_self hn hh]; exact (hS.fresh hn hh).1
  · exact cnt_setBlk_ne M n h B hm

lemma cnt_setHead (hS : Shape H np M) {n h : ℕ} (hn : (M.blk n h).isSome) (hh : M.head n = h)
    (m : ℕ) : cnt (M.setHead n (h + 1)) m = cnt M m := by
  by_cases hm : m = n
  · subst hm
    have hc : cnt M m = h := by simp [cnt, hh, hn]
    have hn1 : M.blk m (h + 1) = none := hS.blk_none (by omega)
    rw [hc]; simp [cnt, setHead_head, hn1]
  · simp [cnt, setHead_head, hm]

lemma setSup (hS : Shape H np M) (n i x : ℕ) : Shape H np (M.setSup n i x) := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := hS
  exact ⟨a, b, c, d, e, f, g, h, i, j, k⟩

lemma setHead (hS : Shape H np M) {n h : ℕ} (hn : (M.blk n h).isSome) (hh : M.head n = h) :
    Shape H np (M.setHead n (h + 1)) := by
  have hc := hS.cnt_setHead hn hh
  have hmono : ∀ m, M.head m ≤ (M.setHead n (h + 1)).head m := by
    intro m; rw [setHead_head]; split_ifs with hm
    · subst hm; omega
    · rfl
  refine ⟨hS.blk0, fun m => (hS.head_pos m).trans (hmono m), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun m hm i => by simpa using hS.leafEnd m hm i⟩
  · intro m i; rw [hc]; exact hS.inst m i
  · intro m i hi; rw [hc] at hi; exact hS.mono m i hi
  · intro m i hi; rw [hc] at hi
    exact ⟨(hS.endlt m i hi).1.trans_le (hmono _), (hS.endlt m i hi).2.trans_le (hmono _)⟩
  · intro m hm i hi; rw [hc] at hi; exact hS.sumI m hm i hi
  · intro m hm i h1 hi; rw [hc] at hi; exact hS.sumL m hm i h1 hi
  · intro m i h1 hi; rw [hc] at hi; exact hS.nonempty m i h1 hi
  · intro i h1 hi; rw [hc] at hi; exact hS.size i h1 hi
  · intro m hm; rw [hc]; exact hS.unused m hm

/-- Installed blocks are not affected by installing a new block. -/
lemma bk_setBlk_old (hS : Shape H np M) {n h : ℕ} (hn : M.blk n h = none) (B : Blk V)
    {m j : ℕ} (hj : j ≤ cnt M m) : (M.setBlk n h B).bk m j = M.bk m j := by
  rw [setBlk_bk, if_neg]
  rintro ⟨rfl, rfl⟩
  have := (hS.inst m j).2 hj
  rw [hn] at this; simp at this

lemma blk_setBlk_old (hS : Shape H np M) {n h : ℕ} (hn : M.blk n h = none) (B : Blk V)
    {m j : ℕ} (hj : j ≤ cnt M m) : (M.setBlk n h B).blk m j = M.blk m j := by
  rw [setBlk_blk, if_neg]
  rintro ⟨rfl, rfl⟩
  have := (hS.inst m j).2 hj
  rw [hn] at this; simp at this

lemma lt_head_le_cnt {M : Mem V} {a n : ℕ} (h : a < M.head n) : a ≤ cnt M n := by
  have := head_le_cnt_succ M n; omega

/-- Installing a block in an internal node (line 35). -/
lemma setBlk_internal (hS : Shape H np M) {v h : ℕ} {B : Blk V} (hv1 : 1 ≤ v) (hv : v < 2 ^ H)
    (hn : M.blk v h = none) (hh : h ≤ M.head v)
    (e1 : (M.bk v (h - 1)).endl ≤ B.endl) (e2 : (M.bk v (h - 1)).endr ≤ B.endr)
    (e3 : B.endl < M.head (2 * v)) (e4 : B.endr < M.head (2 * v + 1))
    (s1 : B.sumenq = (M.bk (2 * v) B.endl).sumenq + (M.bk (2 * v + 1) B.endr).sumenq)
    (s2 : B.sumdeq = (M.bk (2 * v) B.endl).sumdeq + (M.bk (2 * v + 1) B.endr).sumdeq)
    (ne : (M.bk v (h - 1)).sumenq + (M.bk v (h - 1)).sumdeq < B.sumenq + B.sumdeq)
    (sz : v = 1 → B.size = (M.bk v (h - 1)).size + (B.sumenq - (M.bk v (h - 1)).sumenq) -
        (B.sumdeq - (M.bk v (h - 1)).sumdeq)) :
    Shape H np (M.setBlk v h B) := by
  obtain ⟨hfr, hhd⟩ := hS.fresh hn hh
  have hc := hS.cnt_setBlk hn hh B
  have hold := fun {m j : ℕ} (hj : j ≤ cnt M m) => hS.bk_setBlk_old hn B hj
  have hnew : (M.setBlk v h B).bk v h = B := by rw [setBlk_bk, if_pos ⟨rfl, rfl⟩]
  have hprev : (M.setBlk v h B).bk v (h - 1) = M.bk v (h - 1) := hold (by omega)
  have hl := hold (lt_head_le_cnt e3)
  have hr := hold (lt_head_le_cnt e4)
  -- cases: the new block or an old one
  have key : ∀ m i, i ≤ cnt (M.setBlk v h B) m → (m = v ∧ i = h) ∨ i ≤ cnt M m := by
    intro m i hi; rw [hc] at hi; split_ifs at hi with hm
    · subst hm; by_cases hih : i = h
      · exact Or.inl ⟨rfl, hih⟩
      · exact Or.inr (by omega)
    · exact Or.inr hi
  refine ⟨?_, hS.head_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m; rw [hS.blk_setBlk_old hn B (Nat.zero_le _)]; exact hS.blk0 m
  · intro m i; rw [hc, setBlk_blk]
    by_cases hm : m = v
    · subst hm; by_cases hi : i = h
      · subst hi; simp; omega
      · simp only [true_and, hi, if_false, ite_true]; rw [hS.inst]; omega
    · simp only [hm, false_and, if_false]; exact hS.inst m i
  · intro m i hi
    rcases key m (i + 1) (by omega) with ⟨rfl, rfl⟩ | hi'
    · simp only [Nat.add_sub_cancel] at e1 e2 hprev
      rw [hnew, hprev]; exact ⟨e1, e2⟩
    · rw [hold hi', hold (by omega)]; exact hS.mono m i (by omega)
  · intro m i hi; simp only [setBlk_head]
    rcases key m i hi with ⟨rfl, rfl⟩ | hi'
    · rw [hnew]; exact ⟨e3, e4⟩
    · rw [hold hi']; exact hS.endlt m i hi'
  · intro m hm i hi
    rcases key m i hi with ⟨rfl, rfl⟩ | hi'
    · rw [hnew, hl, hr]; exact ⟨s1, s2⟩
    · rw [hold hi', hold (hS.endl_le hi'), hold (hS.endr_le hi')]; exact hS.sumI m hm i hi'
  · intro m hm i h1 hi
    rcases key m i hi with ⟨rfl, rfl⟩ | hi'
    · omega
    · rw [hold hi', hold (by omega)]; exact hS.sumL m hm i h1 hi'
  · intro m i h1 hi
    rcases key m i hi with ⟨rfl, rfl⟩ | hi'
    · rw [hnew, hprev]; exact ne
    · rw [hold hi', hold (by omega)]; exact hS.nonempty m i h1 hi'
  · intro i h1 hi
    rcases key 1 i hi with ⟨hv', rfl⟩ | hi'
    · subst hv'; rw [hnew, hprev]; exact sz rfl
    · rw [hold hi', hold (by omega)]; exact hS.size i h1 hi'
  · intro m hm; rw [hc, if_neg (by omega)]; exact hS.unused m hm
  · intro m hm i; rw [setBlk_bk, if_neg (by omega)]; exact hS.leafEnd m hm i

/-- Installing a block in a leaf (line 12). -/
lemma setBlk_leaf (hS : Shape H np M) {L h : ℕ} (o : FifoOp V) (hL : 2 ^ H ≤ L)
    (hLn : L < 2 ^ H + np) (hL2 : 2 ≤ L) (hn : M.blk L h = none) (hh : h = M.head L) :
    Shape H np (M.setBlk L h (newLeafBlk o (M.bk L (h - 1)))) := by
  have hpow : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  set B := newLeafBlk o (M.bk L (h - 1)) with hB
  obtain ⟨hfr, hhd⟩ := hS.fresh hn hh.le
  have hc := hS.cnt_setBlk hn hh.le B
  have hold := fun {m j : ℕ} (hj : j ≤ cnt M m) => hS.bk_setBlk_old hn B hj
  have hnew : (M.setBlk L h B).bk L h = B := by rw [setBlk_bk, if_pos ⟨rfl, rfl⟩]
  have hprev : (M.setBlk L h B).bk L (h - 1) = M.bk L (h - 1) := hold (by omega)
  have hnb : B.endl = 0 ∧ B.endr = 0 := by cases o <;> simp [hB, newLeafBlk]
  have key : ∀ m i, i ≤ cnt (M.setBlk L h B) m → (m = L ∧ i = h) ∨ i ≤ cnt M m := by
    intro m i hi; rw [hc] at hi; split_ifs at hi with hm
    · subst hm; by_cases hih : i = h
      · exact Or.inl ⟨rfl, hih⟩
      · exact Or.inr (by omega)
    · exact Or.inr hi
  have hLE : ∀ m, 2 ^ H ≤ m → ∀ i, ((M.setBlk L h B).bk m i).endl = 0 ∧
      ((M.setBlk L h B).bk m i).endr = 0 := by
    intro m hm i; rw [setBlk_bk]; split_ifs
    · exact hnb
    · exact hS.leafEnd m hm i
  refine ⟨?_, hS.head_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hLE⟩
  · intro m; rw [hS.blk_setBlk_old hn B (Nat.zero_le _)]; exact hS.blk0 m
  · intro m i; rw [hc, setBlk_blk]
    by_cases hm : m = L
    · subst hm; by_cases hi : i = h
      · subst hi; simp; omega
      · simp only [true_and, hi, if_false, ite_true]; rw [hS.inst]; omega
    · simp only [hm, false_and, if_false]; exact hS.inst m i
  · intro m i hi
    rcases key m (i + 1) (by omega) with ⟨rfl, rfl⟩ | hi'
    · rw [(hLE m hL i).1, (hLE m hL (i + 1)).1, (hLE m hL i).2, (hLE m hL (i + 1)).2]
      exact ⟨le_rfl, le_rfl⟩
    · rw [hold hi', hold (by omega)]; exact hS.mono m i (by omega)
  · intro m i hi; simp only [setBlk_head]
    rcases key m i hi with ⟨rfl, rfl⟩ | hi'
    · rw [hnew, hnb.1, hnb.2]; exact ⟨hS.head_pos _, hS.head_pos _⟩
    · rw [hold hi']; exact hS.endlt m i hi'
  · intro m hm i hi
    rcases key m i hi with ⟨rfl, rfl⟩ | hi'
    · omega
    · rw [hold hi', hold (hS.endl_le hi'), hold (hS.endr_le hi')]; exact hS.sumI m hm i hi'
  · intro m hm i h1 hi
    rcases key m i hi with ⟨rfl, rfl⟩ | hi'
    · rw [hnew, hprev, hB]; cases o <;> simp [newLeafBlk, blkOp, isEnq]
    · rw [hold hi', hold (by omega)]; exact hS.sumL m hm i h1 hi'
  · intro m i h1 hi
    rcases key m i hi with ⟨rfl, rfl⟩ | hi'
    · rw [hnew, hprev, hB]; cases o <;> simp [newLeafBlk] <;> omega
    · rw [hold hi', hold (by omega)]; exact hS.nonempty m i h1 hi'
  · intro i h1 hi
    rcases key 1 i hi with ⟨hv', rfl⟩ | hi'
    · omega
    · rw [hold hi', hold (by omega)]; exact hS.size i h1 hi'
  · intro m hm; rw [hc, if_neg (by omega)]; exact hS.unused m hm

end Shape

end Podc.WaitFreeQueuePolylog
