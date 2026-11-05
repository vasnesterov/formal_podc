import Papers.PODC2023.WaitFreeQueuePolylog.Shape

/-!
# Correctness of one level of `IndexDequeue`, `GetEnqueue` and of `FindResponse`

Lemmas 13, 14 and 17 of the paper are proved by induction along the path between a leaf and
the root; the inductive step is a statement about one level, proved here for every memory
satisfying the structural invariants `Shape` and the accuracy of the `super` fields
(`SupOK`, Lemma 12).
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ} {M : Mem V}


/-- **Lemma 12** (accuracy of `super`), for the blocks below `head`: `super` is set and is the
index `s` of the superblock or `s - 1`, i.e. it is at most every parent index whose block
covers `b`, and at least every parent index whose block ends before `b`. -/
def SupOK (M : Mem V) : Prop :=
  ∀ n, 2 ≤ n → ∀ b, 1 ≤ b → b < M.head n → ∃ s, M.sup n b = some s ∧
    (∀ j, j ≤ cnt M (n / 2) → b ≤ endOf M (n / 2) j (n % 2) → s ≤ j) ∧
    (∀ j, j ≤ cnt M (n / 2) → endOf M (n / 2) j (n % 2) < b → j ≤ s)

/-! ### Helper lemmas: positions in the operation sequences of a node -/

section StepHelpers

variable {H np : ℕ} {M : Mem V}

/-- `findFirst` on a list `range'`: the least `j` satisfying `p`. -/
lemma wfq_find?_range' (p : ℕ → Bool) (lo n : ℕ) (h : ∃ j, lo ≤ j ∧ j < lo + n ∧ p j) :
    ∃ r, (List.range' lo n).find? p = some r ∧ lo ≤ r ∧ r < lo + n ∧ p r ∧
      ∀ j, lo ≤ j → j < r → p j = false := by
  induction n generalizing lo with
  | zero => obtain ⟨j, h1, h2, -⟩ := h; omega
  | succ n ih =>
    rw [List.range'_succ, List.find?_cons]
    by_cases hp : p lo
    · simp only [hp]
      exact ⟨lo, rfl, le_rfl, by omega, hp, fun j h1 h2 => by omega⟩
    · simp only [Bool.not_eq_true] at hp
      simp only [hp]
      obtain ⟨j, h1, h2, h3⟩ := h
      have hj : j ≠ lo := by rintro rfl; rw [hp] at h3; simp at h3
      obtain ⟨r, e, r1, r2, r3, r4⟩ := ih (lo + 1) ⟨j, by omega, by omega, h3⟩
      refine ⟨r, e, by omega, by omega, r3, fun k k1 k2 => ?_⟩
      rcases Nat.eq_or_lt_of_le k1 with rfl | hk
      · exact hp
      · exact r4 k hk k2

/-- Specification of `findFirst`. -/
lemma wfq_findFirst_spec (f : ℕ → ℕ) (x lo hi : ℕ) (h : ∃ j, lo ≤ j ∧ j ≤ hi ∧ x ≤ f j) :
    lo ≤ findFirst f x lo hi ∧ findFirst f x lo hi ≤ hi ∧ x ≤ f (findFirst f x lo hi) ∧
      ∀ j, lo ≤ j → j < findFirst f x lo hi → f j < x := by
  obtain ⟨j, h1, h2, h3⟩ := h
  obtain ⟨r, e, r1, r2, r3, r4⟩ := wfq_find?_range' (fun j => decide (x ≤ f j)) lo (hi + 1 - lo)
    ⟨j, h1, by omega, by simpa using h3⟩
  unfold findFirst
  rw [e, Option.getD_some]
  refine ⟨r1, by omega, by simpa using r3, fun k k1 k2 => ?_⟩
  have := r4 k k1 k2
  simp at this; omega

lemma wfq_pre_eq_append_rng (w : ℕ) {a c : ℕ} (h : a ≤ c) :
    pre H np M w c = pre H np M w a ++ (rng a c).flatMap (ops H np M w) := by
  unfold pre preK ops
  exact (flatMap_range'_split _ (Nat.zero_le a) h).symm

lemma wfq_ops_eq_rng (w : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    ops H np M w j = (rng (j - 1) j).flatMap (ops H np M w) := by
  have : rng (j - 1) j = [j] := by
    simp only [rng, show j - (j - 1) = 1 by omega, show j - 1 + 1 = j by omega]; rfl
  rw [this]; simp

lemma wfq_enqs_rng (hS : Shape H np M) {w a c : ℕ} (h : a ≤ c) (hc : c ≤ cnt M w) (k : ℕ) :
    (enqs ((rng a c).flatMap (ops H np M w)))[k]? =
      (enqs (pre H np M w c))[(M.bk w a).sumenq + k]? := by
  have ha := hS.sumenq_eq (n := w) (h.trans hc)
  rw [wfq_pre_eq_append_rng w h, enqs_append, List.getElem?_append_right (by omega), ha]
  congr 1; omega

lemma wfq_deqs_rng (hS : Shape H np M) {w a c : ℕ} (h : a ≤ c) (hc : c ≤ cnt M w) (k : ℕ) :
    (deqs ((rng a c).flatMap (ops H np M w)))[k]? =
      (deqs (pre H np M w c))[(M.bk w a).sumdeq + k]? := by
  have ha := hS.sumdeq_eq (n := w) (h.trans hc)
  rw [wfq_pre_eq_append_rng w h, deqs_append, List.getElem?_append_right (by omega), ha]
  congr 1; omega

lemma wfq_len_enqs_rng (hS : Shape H np M) {w a c : ℕ} (h : a ≤ c) (hc : c ≤ cnt M w) :
    (enqs ((rng a c).flatMap (ops H np M w))).length = (M.bk w c).sumenq - (M.bk w a).sumenq ∧
      (M.bk w a).sumenq ≤ (M.bk w c).sumenq := by
  have ha := hS.sumenq_eq (n := w) (h.trans hc)
  have hc' := hS.sumenq_eq (n := w) hc
  have e := congrArg (fun l => (enqs l).length) (wfq_pre_eq_append_rng (H := H) (np := np)
    (M := M) w h)
  simp only [enqs_append, List.length_append] at e
  omega

lemma wfq_len_deqs_rng (hS : Shape H np M) {w a c : ℕ} (h : a ≤ c) (hc : c ≤ cnt M w) :
    (deqs ((rng a c).flatMap (ops H np M w))).length = (M.bk w c).sumdeq - (M.bk w a).sumdeq ∧
      (M.bk w a).sumdeq ≤ (M.bk w c).sumdeq := by
  have ha := hS.sumdeq_eq (n := w) (h.trans hc)
  have hc' := hS.sumdeq_eq (n := w) hc
  have e := congrArg (fun l => (deqs l).length) (wfq_pre_eq_append_rng (H := H) (np := np)
    (M := M) w h)
  simp only [deqs_append, List.length_append] at e
  omega

lemma wfq_enqs_pre_mono (hS : Shape H np M) {w c c' : ℕ} (h : c ≤ c') (hc' : c' ≤ cnt M w)
    {k : ℕ} (hk : k < (M.bk w c).sumenq) :
    (enqs (pre H np M w c'))[k]? = (enqs (pre H np M w c))[k]? := by
  rw [wfq_pre_eq_append_rng w h, enqs_append, List.getElem?_append_left]
  rw [hS.sumenq_eq (h.trans hc')]; exact hk

lemma wfq_deqs_pre_mono (hS : Shape H np M) {w c c' : ℕ} (h : c ≤ c') (hc' : c' ≤ cnt M w)
    {k : ℕ} (hk : k < (M.bk w c).sumdeq) :
    (deqs (pre H np M w c'))[k]? = (deqs (pre H np M w c))[k]? := by
  rw [wfq_pre_eq_append_rng w h, deqs_append, List.getElem?_append_left]
  rw [hS.sumdeq_eq (h.trans hc')]; exact hk

/-- The descent into one child (lines 113–116 of `GetEnqueue`). -/
lemma wfq_child_step (hS : Shape H np M) {c a e i' b' : ℕ} (hae : a ≤ e) (he : e ≤ cnt M c)
    (hi1 : 1 ≤ i') (hi : i' + (M.bk c a).sumenq ≤ (M.bk c e).sumenq)
    (hb' : b' = findFirst (fun j => (M.bk c j).sumenq) (i' + (M.bk c a).sumenq) (a + 1) e) :
    1 ≤ b' ∧ b' ≤ cnt M c ∧ 1 ≤ i' - ((M.bk c (b' - 1)).sumenq - (M.bk c a).sumenq) ∧
    i' - ((M.bk c (b' - 1)).sumenq - (M.bk c a).sumenq) ≤ (enqs (ops H np M c b')).length ∧
    (enqs (ops H np M c b'))[i' - ((M.bk c (b' - 1)).sumenq - (M.bk c a).sumenq) - 1]? =
      (enqs ((rng a e).flatMap (ops H np M c)))[i' - 1]? := by
  have hlt : a < e := by
    by_contra hh
    have : a = e := by omega
    subst this; omega
  obtain ⟨f1, f2, f3, f4⟩ := wfq_findFirst_spec (fun j => (M.bk c j).sumenq)
    (i' + (M.bk c a).sumenq) (a + 1) e ⟨e, by omega, le_rfl, hi⟩
  rw [← hb'] at f1 f2 f3 f4
  have hprev : (M.bk c (b' - 1)).sumenq < i' + (M.bk c a).sumenq := by
    rcases Nat.eq_or_lt_of_le f1 with h | h
    · rw [← h, Nat.add_sub_cancel]; omega
    · exact f4 _ (by omega) (by omega)
  have hmono := (wfq_len_enqs_rng hS (w := c) (show a ≤ b' - 1 by omega) (by omega)).2
  have hlen := (wfq_len_enqs_rng hS (w := c) (show b' - 1 ≤ b' by omega) (by omega)).1
  rw [wfq_ops_eq_rng c (show 1 ≤ b' by omega)]
  refine ⟨by omega, by omega, by omega, by rw [hlen]; omega, ?_⟩
  rw [wfq_enqs_rng hS (by omega) (by omega), wfq_enqs_rng hS hae he,
    wfq_enqs_pre_mono hS (c := b') (c' := e) f2 he]
  · congr 1; omega
  · omega

/-- The dequeues of one block `w.blocks[b]` inside the range of subblocks `E+1..F` of a parent
block (line 76 of `IndexDequeue`). -/
lemma wfq_idx_child (hS : Shape H np M) {w E F b i : ℕ} (hEb : E < b) (hbF : b ≤ F)
    (hF : F ≤ cnt M w) (hi1 : 1 ≤ i) (hi : i ≤ (deqs (ops H np M w b)).length) :
    1 ≤ i + ((M.bk w (b - 1)).sumdeq - (M.bk w E).sumdeq) ∧
    i + ((M.bk w (b - 1)).sumdeq - (M.bk w E).sumdeq) ≤
      (deqs ((rng E F).flatMap (ops H np M w))).length ∧
    (deqs ((rng E F).flatMap (ops H np M w)))[i + ((M.bk w (b - 1)).sumdeq -
      (M.bk w E).sumdeq) - 1]? = (deqs (ops H np M w b))[i - 1]? := by
  have hb1 : 1 ≤ b := by omega
  have hbc : b ≤ cnt M w := hbF.trans hF
  obtain ⟨l1, m1⟩ := wfq_len_deqs_rng hS (w := w) (show E ≤ b - 1 by omega) (by omega)
  obtain ⟨l2, m2⟩ := wfq_len_deqs_rng hS (w := w) (show b - 1 ≤ b by omega) hbc
  obtain ⟨l3, m3⟩ := wfq_len_deqs_rng hS (w := w) hbF hF
  obtain ⟨l4, m4⟩ := wfq_len_deqs_rng hS (w := w) (show E ≤ F by omega) hF
  rw [wfq_ops_eq_rng w hb1] at hi ⊢
  rw [l2] at hi
  refine ⟨by omega, by rw [l4]; omega, ?_⟩
  rw [wfq_deqs_rng hS (by omega) hF, wfq_deqs_rng hS (show b - 1 ≤ b by omega) hbc,
    wfq_deqs_pre_mono hS hbF hF]
  · congr 1; omega
  · omega

/-- Lines 72–74 of `IndexDequeue` compute the index of the superblock (from Lemma 12). -/
lemma wfq_sup_spec (hS : Shape H np M) (hsup : SupOK M) {v b : ℕ} (hv2 : 2 ≤ v) (hb1 : 1 ≤ b)
    (hbc : b ≤ endOf M (v / 2) (cnt M (v / 2)) (v % 2)) :
    ∃ j, 1 ≤ j ∧ j ≤ cnt M (v / 2) ∧ endOf M (v / 2) (j - 1) (v % 2) < b ∧
      b ≤ endOf M (v / 2) j (v % 2) ∧
      (if (M.bk (v / 2) ((M.sup v b).getD 0)).endd (v % 2) < b then (M.sup v b).getD 0 + 1
        else (M.sup v b).getD 0) = j := by
  have hm1 : 1 ≤ v / 2 := by omega
  have hvd : v = 2 * (v / 2) + v % 2 := by omega
  have hhead : endOf M (v / 2) (cnt M (v / 2)) (v % 2) < M.head v := by
    have := hS.endlt (v / 2) (cnt M (v / 2)) le_rfl
    rcases Nat.mod_two_eq_zero_or_one v with h | h
    · simp only [endOf, Blk.endd, h, ite_true]
      exact this.1.trans_eq (by congr 1; omega)
    · simp only [endOf, Blk.endd, h, one_ne_zero, ite_false]
      exact this.2.trans_eq (by congr 1; omega)
  obtain ⟨s, hs, hs1, hs2⟩ := hsup v hv2 b hb1 (by omega)
  have h0 : endOf M (v / 2) 0 (v % 2) = 0 := by
    simp [endOf, hS.bk_zero, Blk.zero, Blk.endd]
  have hscnt := hs1 (cnt M (v / 2)) le_rfl hbc
  rw [hs, Option.getD_some]
  by_cases h : endOf M (v / 2) s (v % 2) < b
  · have hlt : s < cnt M (v / 2) := by
      by_contra hc
      have : s = cnt M (v / 2) := by omega
      rw [this] at h; omega
    refine ⟨s + 1, by omega, hlt, by simpa using h, ?_, ?_⟩
    · by_contra hc
      have := hs2 (s + 1) hlt (by omega); omega
    · simp only [endOf] at h; simp [h]
  · have hs0 : 1 ≤ s := by
      by_contra hc
      have : s = 0 := by omega
      rw [this, h0] at h; omega
    refine ⟨s, hs0, hscnt, ?_, by omega, ?_⟩
    · by_contra hc
      have := hs1 (s - 1) (by omega) (by omega); omega
    · simp only [endOf] at h; simp [h]

lemma wfq_numEnq_map (l : List ℕ) :
    numEnq (l.map (rootBatch H np M)) = (enqs (l.flatMap (ops H np M 1))).length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [numEnq, rootBatch, List.flatMap_cons] at ih ⊢; omega

lemma wfq_enqVals_map (l : List ℕ) :
    enqVals (l.map (rootBatch H np M)) = (enqs (l.flatMap (ops H np M 1))).map Prod.snd := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [enqVals, rootBatch, List.flatMap_cons] at ih ⊢; rw [ih]

/-- The `size` field of the root block `j` is the queue size after the first `j` batches. -/
lemma wfq_batchSize_root (hS : Shape H np M) {j : ℕ} (hj : j ≤ cnt M 1) :
    batchSize ((List.range' 1 j).map (rootBatch H np M)) = (M.bk 1 j).size := by
  induction j with
  | zero => simp [batchSize, hS.bk_zero, Blk.zero]
  | succ j ih =>
    rw [List.range'_1_concat, List.map_append, List.map_singleton, batchSize_append_singleton,
      ih (by omega)]
    have hsz := hS.size (j + 1) (by omega) hj
    simp only [Nat.add_sub_cancel] at hsz
    obtain ⟨l1, -⟩ := wfq_len_enqs_rng hS (w := 1) (show j ≤ j + 1 by omega) hj
    obtain ⟨l2, -⟩ := wfq_len_deqs_rng hS (w := 1) (show j ≤ j + 1 by omega) hj
    have e := wfq_ops_eq_rng (H := H) (np := np) (M := M) 1 (show 1 ≤ j + 1 by omega)
    simp only [Nat.add_sub_cancel] at e
    rw [← e] at l1 l2
    simp only [rootBatch, Nat.add_comm 1 j]
    rw [l1, l2, hsz]

end StepHelpers

/-- **Lemma 13 (one level).** If `v.blocks[b]` has been propagated to `v.parent` and has at
least `i` dequeues, one level of `IndexDequeue` (lines 71–79, with the repaired line 78) returns
the index `s` of the superblock and the rank `i'` of the same dequeue in it. -/
theorem idxStep_spec (hS : Shape H np M) (hsup : SupOK M) {v b i : ℕ} (hv2 : 2 ≤ v)
    (hv : v < 2 ^ (H + 1)) (hb1 : 1 ≤ b)
    (hbc : b ≤ endOf M (v / 2) (cnt M (v / 2)) (v % 2))
    (hi1 : 1 ≤ i) (hi : i ≤ (deqs (ops H np M v b)).length) :
    let r := idxStep Variant.fixed M v b i
    1 ≤ r.1 ∧ r.1 ≤ cnt M (v / 2) ∧ endOf M (v / 2) (r.1 - 1) (v % 2) < b ∧
    b ≤ endOf M (v / 2) r.1 (v % 2) ∧ 1 ≤ r.2 ∧ r.2 ≤ (deqs (ops H np M (v / 2) r.1)).length ∧
    (deqs (ops H np M (v / 2) r.1))[r.2 - 1]? = (deqs (ops H np M v b))[i - 1]? := by
  intro r
  obtain ⟨j, hj1, hjc, hjlo, hjhi, hj⟩ := wfq_sup_spec hS hsup hv2 hb1 hbc
  simp only [r, idxStep]
  rw [hj]
  refine ⟨hj1, hjc, hjlo, hjhi, ?_⟩
  rw [pow_succ] at hv
  obtain ⟨ml, mr⟩ := hS.mono_le (show j - 1 ≤ j by omega) hjc
  rcases Nat.even_or_odd' v with ⟨m, rfl | rfl⟩
  · simp only [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega] at hjlo hjhi hjc ml mr ⊢
    have hops := Shape.ops_internal (H := H) (np := np) (M := M) m (j - 1) (by omega) (by omega)
    rw [show j - 1 + 1 = j by omega] at hops
    simp only [endOf, Blk.endd, ite_true] at hjlo hjhi
    obtain ⟨c1, c2, c3⟩ := wfq_idx_child hS hjlo hjhi (hS.endl_le hjc) hi1 hi
    simp only [zero_ne_one, ite_false, Blk.endd, ite_true]
    rw [hops, deqs_append, List.length_append]
    refine ⟨c1, by omega, ?_⟩
    rw [List.getElem?_append_left (by omega), c3]
  · simp only [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]
      at hjlo hjhi hjc ml mr ⊢
    have hops := Shape.ops_internal (H := H) (np := np) (M := M) m (j - 1) (by omega) (by omega)
    rw [show j - 1 + 1 = j by omega] at hops
    simp only [endOf, Blk.endd, one_ne_zero, ite_false] at hjlo hjhi
    obtain ⟨c1, c2, c3⟩ := wfq_idx_child hS hjlo hjhi (hS.endr_le hjc) hi1 hi
    obtain ⟨lL, sL⟩ := wfq_len_deqs_rng hS (w := 2 * m) ml (hS.endl_le hjc)
    simp only [Variant.fixed, ite_true, Blk.endd, one_ne_zero, ite_false]
    rw [hops, deqs_append, List.length_append]
    refine ⟨by omega, by omega, ?_⟩
    rw [List.getElem?_append_right (by omega), lL]
    convert c3 using 2
    omega

/-- **Lemma 14 (one level).** One level of `GetEnqueue` at an internal node (lines 101–116)
returns the child, the subblock and the rank of the same enqueue. -/
theorem getEnqStep_spec (hS : Shape H np M) {v b i : ℕ} (hv1 : 1 ≤ v) (hv : v < 2 ^ H)
    (hb1 : 1 ≤ b) (hb : b ≤ cnt M v) (hi1 : 1 ≤ i) (hi : i ≤ (enqs (ops H np M v b)).length) :
    let r := getEnqStep M v b i
    (r.1 = 2 * v ∨ r.1 = 2 * v + 1) ∧ 1 ≤ r.2.1 ∧ r.2.1 ≤ cnt M r.1 ∧ 1 ≤ r.2.2 ∧
    r.2.2 ≤ (enqs (ops H np M r.1 r.2.1)).length ∧
    (enqs (ops H np M r.1 r.2.1))[r.2.2 - 1]? = (enqs (ops H np M v b))[i - 1]? := by
  intro r
  obtain ⟨ml, mr⟩ := hS.mono_le (show b - 1 ≤ b by omega) hb
  have hEl := hS.endl_le hb
  have hEr := hS.endr_le hb
  have hops := Shape.ops_internal (H := H) (np := np) (M := M) v (b - 1) hv1 hv
  rw [show b - 1 + 1 = b by omega] at hops
  obtain ⟨lL, sL⟩ := wfq_len_enqs_rng hS ml hEl
  obtain ⟨lR, sR⟩ := wfq_len_enqs_rng hS mr hEr
  have hlen := congrArg (fun l => (enqs l).length) hops
  simp only [enqs_append, List.length_append] at hlen
  rw [hops, enqs_append]
  simp only [r, getEnqStep]
  by_cases hd : i ≤ (M.bk (2 * v) (M.bk v b).endl).sumenq - (M.bk (2 * v) (M.bk v (b - 1)).endl).sumenq
  · simp only [hd, ite_true, Blk.endd, Nat.add_zero, true_or, true_and]
    obtain ⟨c1, c2, c3, c4, c5⟩ := wfq_child_step (H := H) (np := np) hS (c := 2 * v) ml hEl hi1
      (by omega) rfl
    refine ⟨c1, c2, c3, c4, ?_⟩
    rw [c5, List.getElem?_append_left (by omega)]
  · simp only [hd, ite_false, Blk.endd, one_ne_zero, or_true, true_and]
    obtain ⟨c1, c2, c3, c4, c5⟩ := wfq_child_step (H := H) (np := np) hS (c := 2 * v + 1)
      (i' := i - ((M.bk (2 * v) (M.bk v b).endl).sumenq -
        (M.bk (2 * v) (M.bk v (b - 1)).endl).sumenq)) mr hEr (by omega) (by omega) rfl
    refine ⟨c1, c2, c3, c4, ?_⟩
    rw [c5, List.getElem?_append_right (by omega), lL]
    congr 1; omega

/-- **Lemma 17 (arithmetic of `FindResponse`).** For the `i`-th dequeue of the root block
`b`, `FindResponse` decides correctly whether it is a null dequeue in the linearization `L`,
and otherwise finds the block `bₑ` and rank `iₑ` of the enqueue whose value it returns in `L`. -/
theorem findResp_spec (hS : Shape H np M) (hH : 1 ≤ H)
    (hnd : ((rootLin H np M).map Prod.fst).Nodup) {b i : ℕ}
    (hb1 : 1 ≤ b) (hb : b ≤ cnt M 1) (hi1 : 1 ≤ i) (hi : i ≤ (deqs (ops H np M 1 b)).length) :
    match findResp M b i with
    | none => (queueObj V).respIn [] (rootLin H np M) ((deqs (ops H np M 1 b))[i - 1]'(by omega))
        = some none
    | some (be, ie) => 1 ≤ be ∧ be ≤ cnt M 1 ∧ 1 ≤ ie ∧ ie ≤ (enqs (ops H np M 1 be)).length ∧
        (queueObj V).respIn [] (rootLin H np M) ((deqs (ops H np M 1 b))[i - 1]'(by omega)) =
          ((enqs (ops H np M 1 be))[ie - 1]?).map (fun e => some e.2) := by
  have hbs : (rootBatches H np M).length = cnt M 1 := by simp [rootBatches]
  have hget : (rootBatches H np M)[b - 1]'(by omega) = rootBatch H np M b := by
    simp only [rootBatches, List.getElem_map, List.getElem_range']; congr 1; omega
  have hD : (deqs (ops H np M 1 b)).length = ((rootBatches H np M)[b - 1]'(by omega)).2.length := by
    rw [hget]; rfl
  have key := respIn_batchLin_deq (rootBatches H np M) hnd (b - 1) (by omega) (i - 1)
    (by rw [← hD]; omega)
  have hkey : ((rootBatches H np M)[b - 1]'(by omega)).2[i - 1]'(by rw [← hD]; omega) =
      (deqs (ops H np M 1 b))[i - 1]'(by omega) := by
    simp only [hget, rootBatch]
  rw [hkey] at key
  have htake : (rootBatches H np M).take (b - 1) = (List.range' 1 (b - 1)).map (rootBatch H np M) := by
    simp only [rootBatches, ← List.map_take]; congr 1; exact List.take_range'_of_length_ge (by omega)
  have hsize := wfq_batchSize_root hS (show b - 1 ≤ cnt M 1 by omega)
  have hnum := wfq_numEnq_map (H := H) (np := np) (M := M) (List.range' 1 (b - 1))
  have hse := hS.sumenq_eq (n := 1) (show b - 1 ≤ cnt M 1 by omega)
  have hle := (runOps_batchLin (V := V) ((rootBatches H np M).take (b - 1))).1
  rw [← htake] at hsize hnum
  change (enqs ((List.range' 1 (b - 1)).flatMap (ops H np M 1))).length = _ at hse
  rw [← hnum] at hse
  have hvals : enqVals (rootBatches H np M) = (enqs (pre H np M 1 (cnt M 1))).map Prod.snd :=
    wfq_enqVals_map _
  obtain ⟨lE, sE⟩ := wfq_len_enqs_rng hS (w := 1) (show b - 1 ≤ b by omega) hb
  rw [← wfq_ops_eq_rng 1 hb1] at lE
  have hE : ((rootBatches H np M)[b - 1]'(by omega)).1.length =
      (M.bk 1 b).sumenq - (M.bk 1 (b - 1)).sumenq := by
    rw [hget]; exact lE
  rw [hE, hsize, hse, hvals] at key
  rw [hsize, hse] at hle
  change (queueObj V).respIn [] (rootLin H np M) _ = _ at key
  unfold findResp
  by_cases hc : (M.bk 1 (b - 1)).size + ((M.bk 1 b).sumenq - (M.bk 1 (b - 1)).sumenq) < i
  · simp only [hc, ite_true]
    rw [key]; split_ifs
    · rfl
    · omega
  · simp only [hc, ite_false]
    set e := i + (M.bk 1 (b - 1)).sumenq - (M.bk 1 (b - 1)).size with he
    obtain ⟨f1, f2, f3, f4⟩ := wfq_findFirst_spec (fun j => (M.bk 1 j).sumenq) e 0 b
      ⟨b, by omega, le_rfl, by omega⟩
    set be := findFirst (fun j => (M.bk 1 j).sumenq) e 0 b with hbe
    have h00 : (M.bk 1 0).sumenq = 0 := by simp [hS.bk_zero, Blk.zero]
    have hbe1 : 1 ≤ be := by
      by_contra h
      have : be = 0 := by omega
      rw [this, h00] at f3; omega
    have hprev : (M.bk 1 (be - 1)).sumenq < e := f4 _ (by omega) (by omega)
    obtain ⟨l1, m1⟩ := wfq_len_enqs_rng hS (w := 1) (show be - 1 ≤ be by omega) (by omega)
    obtain ⟨l2, m2⟩ := wfq_len_enqs_rng hS (w := 1) (show be ≤ cnt M 1 by omega) le_rfl
    have hx := wfq_enqs_pre_mono hS (w := 1) (c := be) (c' := cnt M 1) (by omega) le_rfl
      (k := e - 1) (by omega)
    have hL := hS.sumenq_eq (n := 1) (le_refl (cnt M 1))
    rw [wfq_ops_eq_rng 1 hbe1]
    refine ⟨hbe1, by omega, by omega, by rw [l1]; omega, ?_⟩
    rw [wfq_enqs_rng hS (show be - 1 ≤ be by omega) (by omega),
      show (M.bk 1 (be - 1)).sumenq + (e - (M.bk 1 (be - 1)).sumenq - 1) = e - 1 by omega, ← hx,
      key]
    split_ifs
    · omega
    · rw [show i - 1 + (M.bk 1 (b - 1)).sumenq - (M.bk 1 (b - 1)).size = e - 1 by omega,
        List.getElem?_map, List.getElem?_eq_getElem (by omega)]
      rfl

end Podc.WaitFreeQueuePolylog
