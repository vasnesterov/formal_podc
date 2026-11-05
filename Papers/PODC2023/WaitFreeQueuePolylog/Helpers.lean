import Papers.PODC2023.WaitFreeQueuePolylog.MemInvs

/-!
# Auxiliary facts for the step proofs
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ} {M : Mem V}

/-- The blocks of a process's own leaf. -/
lemma ops_own_leaf (hS : Shape H np M) (p : Fin np) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ cnt M (leafOf H p)) :
    ops H np M (leafOf H p) j = [((p, j - 1), blkOp (M.bk (leafOf H p) j))] := by
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 (hS.blk_isSome hj)
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hB' : M.blk (2 ^ H + ↑p) (j' + 1) = some B := hB
  rw [Shape.ops_leaf _ _ (by simp [leafOf]), hB]
  simp only [leafOps, leafOf, Nat.le_add_right, Nat.add_sub_cancel_left, p.isLt, and_self,
    dite_true, Nat.add_sub_cancel, Mem.bk, hB', Option.getD_some]

lemma mem_pre_own_leaf (hS : Shape H np M) (p : Fin np) {j : ℕ} (hj : j < cnt M (leafOf H p)) :
    (p, j) ∈ (pre H np M (leafOf H p) (cnt M (leafOf H p))).map Prod.fst := by
  rw [List.mem_map]
  refine ⟨((p, j), blkOp (M.bk (leafOf H p) (j + 1))), (mem_pre_iff M _ _ _).2
    ⟨j + 1, by omega, by omega, ?_⟩, rfl⟩
  rw [ops_own_leaf hS p (by omega) (by omega)]; simp

/-- Lemma 12 for the memory invariants. -/
theorem supOK_of (hS : Shape H np M) (hm : MInv H M) {G : Ghost np} (hg : GInv H M G)
    (hnp : np ≤ 2 ^ H) : SupOK M := by
  intro n hn2 b hb1 hbh
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 (hm.supSet n hn2 b hb1 hbh)
  have hbc : b ≤ cnt M n := Shape.lt_head_le_cnt hbh
  refine ⟨s, hs, fun j hj hbj => hm.l12up n hn2 b s hb1 hs j hj hbj, fun j hj hlt => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · omega
  have hnT : n < 2 ^ (H + 1) := by
    by_contra hc
    have := hS.unused n (Or.inr (by rw [pow_succ] at hc; omega)); omega
  have hbg := hg.bg_le (n / 2) (by omega) (by rw [pow_succ] at hnT; omega) j hj1 hj
  have : gd (G.bg (n / 2) j) (n % 2) < b := by
    rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h0 | h0
    · simp only [gd, h0, if_true]; simp only [endOf, Blk.endd, h0, if_true] at hlt; omega
    · simp only [gd, h0, one_ne_zero, if_false]
      simp only [endOf, Blk.endd, h0, one_ne_zero, if_false] at hlt; omega
  exact (hg.hm_lb n hn2 hnT b hb1 hbc j hj1 hj this).trans ((hg.hm_le n hn2 b hb1 hbc).2 s hs)

lemma ht_eq_of_mem_ops {n i : ℕ} {y : OpId (Fin np) × FifoOp V} (hy : y ∈ ops H np M n i) :
    (2 ^ H + y.1.1) / 2 ^ ht H n = n := mem_opsK M _ n i hy

lemma ht_eq_of_mem_pre {n i : ℕ} {y : OpId (Fin np) × FifoOp V} (hy : y ∈ pre H np M n i) :
    (2 ^ H + y.1.1) / 2 ^ ht H n = n := mem_preK M _ n i hy

/-- Descending into the child that contains an operation. -/
lemma mem_child_of_mem (hS : Shape H np M) {m j d : ℕ} (hm1 : 1 ≤ m) (hmH : m < 2 ^ H)
    (hj : j ≤ cnt M m) (hd : d < 2) {y : OpId (Fin np) × FifoOp V} (hy : y ∈ pre H np M m j)
    (hsub : (2 ^ H + y.1.1) / 2 ^ ht H (2 * m + d) = 2 * m + d) :
    y ∈ pre H np M (2 * m + d) (endOf M m j d) := by
  have h0 := ht_child' hm1 hmH
  have h1 := ht_child hm1 hmH (d := 1) (by norm_num)
  rcases List.mem_append.1 ((hS.pre_perm hm1 hmH hj).mem_iff.1 hy) with h | h
  · have := ht_eq_of_mem_pre h
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · simpa [endOf, Blk.endd] using h
    · rw [show ht H (2 * m + 1) = ht H (2 * m) by omega] at hsub; omega
  · have := ht_eq_of_mem_pre h
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · simp only [Nat.add_zero] at hsub
      rw [show ht H (2 * m) = ht H (2 * m + 1) by omega] at hsub; omega
    · simpa [endOf, Blk.endd] using h

/-- An operation of the root is in the blocks `1..end_d(parent's last block)` of each node on
its path. -/
lemma mem_anc (hS : Shape H np M) (hnp : np ≤ 2 ^ H) {y : OpId (Fin np) × FifoOp V}
    (hy : y ∈ pre H np M 1 (cnt M 1)) :
    ∀ n, 2 ≤ n → n < 2 ^ (H + 1) → (2 ^ H + y.1.1) / 2 ^ ht H n = n →
      y ∈ pre H np M n (endOf M (n / 2) (cnt M (n / 2)) (n % 2)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn2 hnT hsub
    have hm1 : 1 ≤ n / 2 := by omega
    have hmH : n / 2 < 2 ^ H := by rw [pow_succ] at hnT; omega
    have hc := ht_child hm1 hmH (d := n % 2) (by omega)
    rw [two_mul_div_add] at hc
    have hsubm : (2 ^ H + y.1.1) / 2 ^ ht H (n / 2) = n / 2 := by
      rw [← hc, pow_succ, ← Nat.div_div_eq_div_mul, hsub]
    have hym : y ∈ pre H np M (n / 2) (cnt M (n / 2)) := by
      by_cases h1 : n / 2 = 1
      · rw [h1]; exact hy
      · have := ih (n / 2) (by omega) (by omega) (by omega) hsubm
        refine mem_pre_mono ?_ this
        have h2 := endOf_lt_head hS (m := n / 2 / 2) (d := n / 2 % 2) (by omega)
          (le_refl (cnt M (n / 2 / 2)))
        rw [two_mul_div_add] at h2
        exact Shape.lt_head_le_cnt h2
    have := mem_child_of_mem hS hm1 hmH le_rfl (d := n % 2) (by omega) hym
      (by rw [two_mul_div_add]; exact hsub)
    rwa [two_mul_div_add] at this

/-- The block of `v` containing an operation of `L` lies within the subblocks of the parent's
last block (it has been propagated to the parent). -/
lemma idx_bound (hS : Shape H np M) (hnp : np ≤ 2 ^ H) {x : OpId (Fin np)}
    (hx : x ∈ (pre H np M 1 (cnt M 1)).map Prod.fst) {v b : ℕ} (hv2 : 2 ≤ v)
    (hvT : v < 2 ^ (H + 1)) (hb : b ≤ cnt M v) (hxb : x ∈ (ops H np M v b).map Prod.fst) :
    b ≤ endOf M (v / 2) (cnt M (v / 2)) (v % 2) := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨z, hz, hzy⟩ := List.mem_map.1 hxb
  have hsub := ht_eq_of_mem_ops hz
  rw [hzy] at hsub
  have hanc := mem_anc hS hnp hy v hv2 hvT hsub
  set e := endOf M (v / 2) (cnt M (v / 2)) (v % 2) with he
  have hec : e ≤ cnt M v := by
    have h2 := endOf_lt_head hS (m := v / 2) (d := v % 2) (by omega) le_rfl
    rw [two_mul_div_add] at h2
    exact Shape.lt_head_le_cnt h2
  by_contra hlt
  have hnd := nodup_keys_preK (H := H) (np := np) M (cnt M) (fun m => by simp [hS.bk_zero, Blk.zero])
    (fun m j hj => hS.mono m j hj) (fun m j hj => ⟨hS.endl_le hj, hS.endr_le hj⟩) (ht H v) v b hb
  have hsplit : pre H np M v b = pre H np M v e ++ (rng e b).flatMap (ops H np M v) :=
    pre_prefix M v (by omega)
  change ((pre H np M v b).map Prod.fst).Nodup at hnd
  rw [hsplit, List.map_append, List.nodup_append] at hnd
  refine hnd.2.2 y.1 (List.mem_map.2 ⟨y, hanc, rfl⟩) z.1
    (List.mem_map.2 ⟨z, List.mem_flatMap.2 ⟨b, mem_rng.2 ⟨by omega, le_rfl⟩, hz⟩, rfl⟩) hzy.symm

lemma sumenq_mono (hS : Shape H np M) {w a c : ℕ} (h : a ≤ c) (hc : c ≤ cnt M w) :
    (M.bk w a).sumenq ≤ (M.bk w c).sumenq :=
  (wfq_len_enqs_rng (H := H) (np := np) hS h hc).2

lemma sumdeq_mono (hS : Shape H np M) {w a c : ℕ} (h : a ≤ c) (hc : c ≤ cnt M w) :
    (M.bk w a).sumdeq ≤ (M.bk w c).sumdeq :=
  (wfq_len_deqs_rng (H := H) (np := np) hS h hc).2

lemma sum_strict (hS : Shape H np M) {w a c : ℕ} (h : a < c) (hc : c ≤ cnt M w) :
    (M.bk w a).sumenq + (M.bk w a).sumdeq < (M.bk w c).sumenq + (M.bk w c).sumdeq := by
  induction c, h using Nat.le_induction with
  | base => have := hS.nonempty w (a + 1) (by omega) hc; simpa using this
  | succ c hac ih =>
    have := hS.nonempty w (c + 1) (by omega) hc
    simp only [Nat.add_sub_cancel] at this
    exact (ih (by omega)).trans this

lemma eq_of_sums (hS : Shape H np M) {w a c : ℕ} (h : a ≤ c) (hc : c ≤ cnt M w)
    (h1 : (M.bk w c).sumenq ≤ (M.bk w a).sumenq) (h2 : (M.bk w c).sumdeq ≤ (M.bk w a).sumdeq) :
    a = c := by
  by_contra hne
  have := sum_strict hS (show a < c by omega) hc
  omega

/-- `CreateBlock` returns `null` only if the children have no new blocks (Lemma 9, second
case). -/
lemma create_none (hS : Shape H np M) {v h el : ℕ} (hv1 : 1 ≤ v) (hv : v < 2 ^ H)
    (hh : h - 1 ≤ cnt M v) (hel : (M.bk v (h - 1)).endl ≤ el) (helc : el < M.head (2 * v))
    (hz : createBlock M v h el = none) :
    el ≤ (M.bk v (h - 1)).endl ∧ M.head (2 * v + 1) - 1 ≤ (M.bk v (h - 1)).endr := by
  unfold createBlock at hz
  simp only at hz
  split_ifs at hz with hzero
  obtain ⟨s1, s2⟩ := hS.sumI v hv (h - 1) hh
  have hl := hS.endl_le hh
  have hr := hS.endr_le hh
  have hel' := Shape.lt_head_le_cnt helc
  have her : (M.bk v (h - 1)).endr ≤ M.head (2 * v + 1) - 1 := by
    have := (hS.endlt v (h - 1) hh).2; omega
  have her' : M.head (2 * v + 1) - 1 ≤ cnt M (2 * v + 1) := by
    have := head_le_cnt_succ M (2 * v + 1); omega
  have m1 := sumenq_mono hS hel hel'
  have m2 := sumdeq_mono hS hel hel'
  have m3 := sumenq_mono hS her her'
  have m4 := sumdeq_mono hS her her'
  constructor
  · have := eq_of_sums hS hel hel' (by omega) (by omega); omega
  · have := eq_of_sums hS her her' (by omega) (by omega); omega

lemma create_some (hS : Shape H np M) {v h el : ℕ} {B : Blk V} (hv : v < 2 ^ H)
    (hh : h - 1 ≤ cnt M v) (hel : (M.bk v (h - 1)).endl ≤ el) (helc : el < M.head (2 * v))
    (hz : createBlock M v h el = some B) :
    B.endl = el ∧ B.endr = M.head (2 * v + 1) - 1 ∧
    B.sumenq = (M.bk (2 * v) B.endl).sumenq + (M.bk (2 * v + 1) B.endr).sumenq ∧
    B.sumdeq = (M.bk (2 * v) B.endl).sumdeq + (M.bk (2 * v + 1) B.endr).sumdeq ∧
    (M.bk v (h - 1)).sumenq + (M.bk v (h - 1)).sumdeq < B.sumenq + B.sumdeq ∧
    (v = 1 → B.size = (M.bk v (h - 1)).size + (B.sumenq - (M.bk v (h - 1)).sumenq) -
        (B.sumdeq - (M.bk v (h - 1)).sumdeq)) := by
  unfold createBlock at hz
  simp only at hz
  split at hz
  · cases hz
  rename_i hzero
  cases hz
  obtain ⟨s1, s2⟩ := hS.sumI v hv (h - 1) hh
  have hl := hS.endl_le hh
  have hel' := Shape.lt_head_le_cnt helc
  have her : (M.bk v (h - 1)).endr ≤ M.head (2 * v + 1) - 1 := by
    have := (hS.endlt v (h - 1) hh).2; omega
  have her' : M.head (2 * v + 1) - 1 ≤ cnt M (2 * v + 1) := by
    have := head_le_cnt_succ M (2 * v + 1); omega
  have m1 := sumenq_mono hS hel hel'
  have m2 := sumdeq_mono hS hel hel'
  have m3 := sumenq_mono hS her her'
  have m4 := sumdeq_mono hS her her'
  refine ⟨rfl, rfl, rfl, rfl, by simp only; omega, ?_⟩
  intro h1; simp [h1]

/-- `super` fields of child blocks below the child's `head` are set, and are at most `h` while
`v.blocks[h]` is empty. -/
lemma supUp_of_lt_head (hS : Shape H np M) (hm : MInv H M) {c e v h : ℕ} (hc2 : 2 ≤ c)
    (hcv : c / 2 = v) (he : e < M.head c) : SupUp M c e v h := by
  intro b hb1 hbe
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 (hm.supSet c hc2 b hb1 (by omega))
  refine ⟨s, hs, fun hn => ?_⟩
  have h1 := hm.supBound c b s hs
  rw [hcv] at h1
  have : M.head v ≤ h := by
    by_contra hlt
    have := (hS.inst v h).2 (Shape.lt_head_le_cnt (show h < M.head v by omega))
    rw [hn] at this; simp at this
  omega

end Podc.WaitFreeQueuePolylog
