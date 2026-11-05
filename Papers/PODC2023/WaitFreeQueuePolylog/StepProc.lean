import Papers.PODC2023.WaitFreeQueuePolylog.Helpers

/-!
# One step of a process preserves the invariant
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ}

/-- The effect of a step of `p` in local state `l` on memory `M` (repaired algorithm). -/
def stepLoc (H : ℕ) {np : ℕ} (p : Fin np) (l : Loc V) (M : Mem V) : Mem V × Loc V :=
  match act H Variant.fixed p.val l with
  | .access _ o k => ((memδ M o).1, k (memδ M o).2)
  | .ret _ l' => (M, l')

/-- What a step must preserve. -/
structure StepRes (H np : ℕ) (p : Fin np) (os : List (FifoOp V)) (rs : List (Option V))
    (pend : Option (FifoOp V)) (M : Mem V) (G : Ghost np) (M' : Mem V) (G' : Ghost np)
    (l' : Loc V) : Prop where
  shape : Shape H np M'
  minv : MInv H M'
  ginv : GInv H M' G'
  upd : Upd H np p M M' G G'
  pinv : PInv H os rs M' G' p pend l'

lemma leaf_ge (H : ℕ) {np : ℕ} (p : Fin np) : 2 ^ H ≤ leafOf H p := by simp [leafOf]
lemma leaf_lt (H : ℕ) {np : ℕ} (p : Fin np) : leafOf H p < 2 ^ H + np := by
  simp [leafOf, p.isLt]
lemma leaf_two {H : ℕ} {np : ℕ} (p : Fin np) (hH : 1 ≤ H) : 2 ≤ leafOf H p := by
  have : 2 ^ 1 ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) hH
  simp [leafOf] at *; omega
lemma leaf_lt_pow {H : ℕ} {np : ℕ} (p : Fin np) (hnp : np ≤ 2 ^ H) : leafOf H p < 2 ^ (H + 1) := by
  have := leaf_lt H p; rw [pow_succ]; omega

section

variable {p : Fin np} {os : List (FifoOp V)} {rs : List (Option V)} {pend : Option (FifoOp V)}
  {M : Mem V} {G : Ghost np} {cur : FifoOp V} {lh : ℕ}

lemma step_app0 (hS : Shape H np M) (hm : MInv H M) (hg : GInv H M G)
    (hP : PInv H os rs M G p pend ⟨.app0, cur, lh⟩) :
    StepRes H np p os rs pend M G M G ⟨.app1 (M.head (leafOf H p)), cur, lh⟩ :=
  ⟨hS, hm, hg, Upd.rfl' p M G, hP.1, hP.2, rfl⟩

/-- The leaf operations of `p` (first component of `PInv`). -/
def LeafOK (H : ℕ) {np : ℕ} (os : List (FifoOp V)) (M : Mem V) (p : Fin np) : Prop :=
  ∀ j, 1 ≤ j → j ≤ cnt M (leafOf H p) → os[j - 1]? = some (blkOp (M.bk (leafOf H p) j))

lemma LeafOK.upd (hS : Shape H np M) {M' : Mem V} {G' : Ghost np}
    (hU : Upd H np p M M' G G') (hcl : cnt M' (leafOf H p) = cnt M (leafOf H p))
    (h : LeafOK H os M p) : LeafOK H os M' p := by
  intro j h1 h2; rw [hcl] at h2; rw [hU.bk_eq h2]; exact h j h1 h2

lemma blkOp_cur (h : LeafOK H os M p) {l : Loc V} (hB : Base H os rs M p pend l)
    (hcur : ∀ o, pend = some o → os[rs.length]? = some o) :
    blkOp (M.bk (leafOf H p) (cnt M (leafOf H p))) = l.cur := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  have := h (cnt M (leafOf H p)) (by omega) le_rfl
  rw [show cnt M (leafOf H p) - 1 = rs.length by omega, hcur _ h1] at this
  exact (Option.some.inj this).symm

/-- After a refresh at `v` that put the current operation into `v`: go on with the parent, or
(at the root) finish `Propagate`. -/
lemma after_level (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) (hS : Shape H np M) {v pc0 : _}
    (hv1 : 1 ≤ v) (hv : v < 2 ^ H) (hlf : LeafOK H os M p)
    (hB : BaseH H os rs M p pend ⟨pc0, cur, lh⟩)
    (hx : xOf rs p ∈ (pre H np M v (cnt M v)).map Prod.fst)
    (hcur : ∀ o, pend = some o → os[rs.length]? = some o) :
    PInv H os rs M G p pend
      ⟨if v = 1 then afterProp (2 ^ H + p.val) ⟨pc0, cur, lh⟩ else .r25 (v / 2) 1, cur, lh⟩ := by
  refine ⟨hlf, ?_⟩
  by_cases hv1' : v = 1
  · subst hv1'
    rw [if_pos rfl]
    have hL2 := leaf_two p hH
    have hop := blkOp_cur hlf hB.1 hcur
    cases cur with
    | enq val =>
      refine ⟨hB, ?_⟩
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hx
      obtain ⟨hprov1, hprov2⟩ := mem_pre_prov hS (le_refl _) hy
      rw [hyx] at hprov1 hprov2
      simp only [xOf] at hprov1 hprov2
      have hcl : cnt M (leafOf H p) = rs.length + 1 := by
        have := hB.1.2.2.1; have := hB.1.2.1; omega
      have hy2 : y.2 = FifoOp.enq val := by
        rw [hprov2]; change blkOp (M.bk (leafOf H p) (rs.length + 1)) = _
        rw [← hcl, hop]
      obtain ⟨b, hb1, hb2, hyb⟩ := (mem_pre_iff M 1 _ y).1 hy
      have hmem : (y.1, val) ∈ (rootBatch H np M b).1 := by
        simp only [rootBatch, enqs, List.mem_filterMap]
        exact ⟨y, hyb, by rw [hy2]⟩
      rw [← hyx]
      exact respIn_batchLin_enq _ (nodup_rootLin hS)
        (List.mem_map.2 ⟨b, List.mem_range'.2 ⟨b - 1, by omega, by omega⟩, rfl⟩) hmem
    | deq =>
      have hLne : (2 ^ H + p.val) ≠ 1 := by simp [leafOf] at hL2; omega
      have e : afterProp (2 ^ H + p.val) (⟨pc0, .deq, lh⟩ : Loc V) = .idx (2 ^ H + p.val) lh 1 := by
        simp [afterProp, hLne]
      rw [e]
      obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hB
      have hcl1 : 1 ≤ cnt M (leafOf H p) := by omega
      have hops := ops_own_leaf hS p hcl1 le_rfl
      rw [hop] at hops
      have hlh : lh = cnt M (leafOf H p) := h4
      have hLT := leaf_lt_pow p hnp
      simp only [leafOf] at hlh hcl1 hops hL2 hLT
      refine ⟨⟨⟨h1, h2, h3, h4⟩, h5⟩, rfl, hx, hL2, hLT, by omega, by omega, le_rfl, ?_, ?_⟩
      · rw [hlh, hops]; simp [deqs]
      · rw [hlh, hops]; simp [deqs, xOf]
        have : cnt M (leafOf H p) = os.length := h3
        simp only [leafOf] at this; omega
  · simp only [hv1', if_false]
    refine ⟨⟨by omega, by omega, Or.inl rfl, v % 2, by omega, ?_, by omega⟩, hB⟩
    simp only [InChild, two_mul_div_add]; exact hx

lemma InChild.mono {v d g g' : ℕ} (h : InChild H rs M p v d g) (hg : g ≤ g') :
    InChild H rs M p v d g' := by
  obtain ⟨y, hy, hyx⟩ := List.mem_map.1 h
  exact List.mem_map.2 ⟨y, mem_pre_mono hg hy, hyx⟩

lemma RefCtx.gd_le {v k h d : ℕ} (hR : RefCtx H rs M G p v k h) (hd : d < 2) :
    gd (G.pg p) d ≤ cnt M (2 * v + d) := by
  obtain ⟨-, -, -, -, -, -, r7, r8, -⟩ := hR
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
  · simpa [gd] using r7
  · simpa [gd] using r8

/-- After a terminated `Refresh(v)` (lines 17–22). -/
lemma after_refresh (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) (hS : Shape H np M) {v k h : ℕ}
    {res : Bool} {pc0 : Pc V} (hlf : LeafOK H os M p) (hR : RefCtx H rs M G p v k h)
    (hB : BaseH H os rs M p pend ⟨pc0, cur, lh⟩) (hO : OwnPost H rs M p v k res)
    (hhd : k = 1 ∧ res = false → h < M.head v)
    (hcur : ∀ o, pend = some o → os[rs.length]? = some o) :
    PInv H os rs M G p pend ⟨refDone (2 ^ H + p.val) ⟨pc0, cur, lh⟩ v k res, cur, lh⟩ := by
  have hR' := hR
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, ⟨dc, hdc, hin, hk2⟩, r12⟩ := hR
  unfold refDone
  by_cases hk : k = 1 ∧ res = false
  · rw [if_pos hk]
    refine ⟨hlf, ⟨r1, r2, Or.inr rfl, dc, hdc, hin.mono (hR'.gd_le hdc), fun _ => ⟨hin, ?_, ?_, ?_,
      r7, r8⟩⟩, hB⟩
    · rw [r6]; exact hhd hk
    · rw [r6]; exact (r11 (hhd hk)).1
    · rw [r6]; exact (r11 (hhd hk)).2
  · rw [if_neg hk]
    have : res = true ∨ k = 2 := by
      rcases r3 with rfl | rfl
      · left; cases res <;> simp_all
      · right; rfl
    exact after_level hH hnp hS r1 r2 hlf hB (hO this) hcur

lemma step_app1 (hS : Shape H np M) (hm : MInv H M) (hg : GInv H M G) {h : ℕ}
    (hP : PInv H os rs M G p pend ⟨.app1 h, cur, lh⟩) :
    StepRes H np p os rs pend M G M G (stepLoc H p ⟨.app1 h, cur, lh⟩ M).2 := by
  obtain ⟨hlf, ⟨h1, h2, h3, h4⟩, h5⟩ := hP
  have hb : M.blk (2 ^ H + p.val) (h - 1) = some (M.bk (2 ^ H + p.val) (h - 1)) := by
    have : h - 1 ≤ cnt M (leafOf H p) := by omega
    obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 (hS.blk_isSome this)
    simp only [leafOf] at hB; simp [Mem.bk, hB]
  refine ⟨hS, hm, hg, Upd.rfl' p M G, ?_⟩
  simp only [stepLoc, act, memδ, hb]
  refine ⟨hlf, ⟨h1, h2, h3, h4⟩, h5, ?_⟩
  cases cur <;> rfl

lemma blkOp_newLeafBlk (o : FifoOp V) (B : Blk V) : blkOp (newLeafBlk o B) = o := by
  cases o <;> rfl

lemma step_app2 (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) (hS : Shape H np M) (hm : MInv H M)
    (hg : GInv H M G) {h : ℕ} {B : Blk V}
    (hP : PInv H os rs M G p pend ⟨.app2 h B, cur, lh⟩)
    (hcur : ∀ o, pend = some o → os[rs.length]? = some o) :
    StepRes H np p os rs pend M G (M.setBlk (leafOf H p) h B)
      ⟨G.pg, G.ph, G.pg1, G.bg, upd2 G.hm (leafOf H p) h (M.head (leafOf H p / 2)), G.hs⟩
      ⟨.adv0 .app (leafOf H p) h, cur, h⟩ := by
  obtain ⟨hlf, ⟨h1, h2, h3, h4⟩, h5, h6⟩ := hP
  have hL2 := leaf_two p hH
  have hLge := leaf_ge H p
  have hLlt := leaf_lt H p
  have hhL : h = cnt M (leafOf H p) + 1 := by omega
  have hn : M.blk (leafOf H p) h = none := hS.blk_none (by omega)
  have hsn : M.sup (leafOf H p) h = none := hm.supNone (leafOf H p) h (by omega)
  have h6' : B = newLeafBlk cur (M.bk (leafOf H p) (h - 1)) := h6
  subst h6'
  have hShape := hS.setBlk_leaf cur hLge hLlt hL2 hn h5
  have hcL : cnt (M.setBlk (leafOf H p) h (newLeafBlk cur (M.bk (leafOf H p) (h - 1)))) (leafOf H p) = h :=
    hS.cnt_setBlk_self hn h5.le _
  refine ⟨hShape, hm.setBlk hS hn h5.le ?_, hg.setBlk_leaf hS hLge hn h5.le hsn,
    Upd.setBlk hS p G _ hn h5.le ?_ G.bg (fun _ _ _ => rfl), ?_, ?_⟩
  · intro d hd b s hb hs hbd
    have : (newLeafBlk cur (M.bk (leafOf H p) (h - 1))).endd d = 0 := by
      cases cur <;> simp [newLeafBlk, Blk.endd]
    omega
  · intro q hq heq; apply hq; simp only [leafOf] at heq; exact Fin.ext (by omega)
  · intro j hj1 hj
    rw [hcL] at hj
    rw [setBlk_bk]
    by_cases hjh : j = h
    · subst hjh; rw [if_pos ⟨rfl, rfl⟩, blkOp_newLeafBlk, show j - 1 = rs.length by omega]
      exact hcur _ h1
    · rw [if_neg (by omega)]; exact hlf j hj1 (by omega)
  · refine ⟨⟨by omega, leaf_lt_pow p hnp, by omega, by omega⟩, hL2, rfl, ⟨h1, h2, by omega, ?_⟩, rfl⟩
    exact hcL.symm

lemma step_adv0 (hS : Shape H np M) (hm : MInv H M) (hg : GInv H M G) {c : Ctx} {w hw : ℕ}
    (hP : PInv H os rs M G p pend ⟨.adv0 c w hw, cur, lh⟩) :
    StepRes H np p os rs pend M G M G ⟨.adv1 c w hw (M.head (w / 2)), cur, lh⟩ := by
  obtain ⟨hlf, ha, hw2, hc⟩ := hP
  exact ⟨hS, hm, hg, Upd.rfl' p M G, hlf, ha, hw2,
    (hg.hm_le w hw2 hw ha.2.2.1 ha.2.2.2).1, le_rfl, hc⟩

lemma Keeps.refl' (p : Fin np) (M M' : Mem V) (G G' : Ghost np) (h1 : G'.pg p = G.pg p)
    (h2 : G'.ph p = G.ph p) (h3 : G'.pg1 p = G.pg1 p)
    (h4 : cnt M' (leafOf H p) = cnt M (leafOf H p)) : Keeps H M M' G G' p := ⟨h1, h2, h3, h4⟩

lemma step_adv1 (hS : Shape H np M) (hm : MInv H M) (hg : GInv H M G) {c : Ctx} {w hw hp : ℕ}
    (hP : PInv H os rs M G p pend ⟨.adv1 c w hw hp, cur, lh⟩) :
    StepRes H np p os rs pend M G (stepLoc H p ⟨.adv1 c w hw hp, cur, lh⟩ M).1 G
      (stepLoc H p ⟨.adv1 c w hw hp, cur, lh⟩ M).2 := by
  obtain ⟨hlf, ha, hw2, hhm, hhp, hc⟩ := hP
  simp only [stepLoc, act, memδ]
  by_cases hn : (M.sup w hw).isNone
  · rw [if_pos hn]
    have hn' : M.sup w hw = none := by simpa using hn
    have hU := Upd.setSup (H := H) hS p G w hw hp hn'
    have hk : Keeps H M (M.setSup w hw hp) G G p := ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨hS.setSup w hw hp, hm.setSup hS hw2 ha.2.2.2 hn' hhp, hg.setSup hn' hhm, hU,
      hlf, ha, fun _ => by rw [setSup_sup, if_pos ⟨rfl, rfl⟩]; rfl, hc.frame hS hU hk⟩
  · rw [if_neg hn]
    refine ⟨hS, hm, hg, Upd.rfl' p M G, hlf, ha, fun _ => ?_, hc⟩
    cases h : M.sup w hw <;> simp_all

lemma post_adv (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) (hS : Shape H np M) {M' : Mem V} {G' : Ghost np}
    (hS' : Shape H np M') (hU : Upd H np p M M' G G') (hk : Keeps H M M' G G' p)
    {pc0 : Pc V} {c : Ctx} {w hw : ℕ} (hlf : LeafOK H os M p)
    (hc : CtxInv H os rs M G p pend ⟨pc0, cur, lh⟩ c w hw) (hgt : hw < M'.head w)
    (hcur : ∀ o, pend = some o → os[rs.length]? = some o) :
    PInv H os rs M' G' p pend ⟨afterAdv (2 ^ H + p.val) ⟨pc0, cur, lh⟩ c, cur, lh⟩ := by
  have hlf' := hlf.upd hS hU hk.2.2.2
  obtain ⟨hpg, hph, hpg1, hcl⟩ := id hk
  cases c with
  | app =>
    obtain ⟨rfl, hB, rfl⟩ := hc
    have hB' := hB.frame hU hk
    obtain ⟨h1, h2, h3, h4⟩ := hB'
    have hL2 := leaf_two p hH
    have hLT := leaf_lt_pow p hnp
    refine ⟨hlf', ⟨by simp [leafOf] at hL2 ⊢; omega, ?_, Or.inl rfl, (2 ^ H + p.val) % 2,
      by omega, ?_, by omega⟩, ⟨h1, h2, h3, h4⟩, ?_⟩
    · rw [pow_succ] at hLT; simp [leafOf] at hLT ⊢; omega
    · simp only [InChild]
      rw [two_mul_div_add]
      exact mem_pre_own_leaf hS' p (by change rs.length < cnt M' (leafOf H p); omega)
    · have := head_le_cnt_succ M' (leafOf H p)
      have hlh : hw = cnt M (leafOf H p) := hB.2.2.2
      change hw < M'.head (leafOf H p) at hgt
      omega
  | ref v k h d =>
    obtain ⟨hR, hB, hd, rfl, hgd, hd1⟩ := hc
    have hR' := hR.frame hS hU hk
    have hB' := hB.frame hS hU hk
    simp only [afterAdv]
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · refine ⟨hlf', hR', hB', by omega, fun _ => ?_⟩
      rw [hpg]; simp only [gd, ite_true] at hgd; simpa using hgd.trans_lt hgt
    · refine ⟨hlf', hR', hB', ?_, ?_⟩
      · rw [hpg]; exact (hd1 rfl).trans_le (hU.head_mono _)
      · rw [hpg]; simp only [gd] at hgd; simpa using hgd.trans_lt hgt
  | own v k h res =>
    obtain ⟨hR, hB, rfl, rfl, hO⟩ := hc
    exact after_refresh hH hnp hS' hlf' (hR.frame hS hU hk) (hB.frame hS hU hk)
      (hO.frame hS hU) (fun _ => hgt) hcur

lemma step_adv2 (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) (hS : Shape H np M) (hm : MInv H M)
    (hg : GInv H M G) {c : Ctx} {w hw : ℕ}
    (hP : PInv H os rs M G p pend ⟨.adv2 c w hw, cur, lh⟩)
    (hcur : ∀ o, pend = some o → os[rs.length]? = some o) :
    StepRes H np p os rs pend M G (stepLoc H p ⟨.adv2 c w hw, cur, lh⟩ M).1
      (gstepLoc H M G p ⟨.adv2 c w hw, cur, lh⟩) (stepLoc H p ⟨.adv2 c w hw, cur, lh⟩ M).2 := by
  obtain ⟨hlf, ha, hsup, hc⟩ := hP
  have hn : (M.blk w hw).isSome := hS.blk_isSome ha.2.2.2
  simp only [stepLoc, act, memδ, gstepLoc]
  by_cases hh : M.head w = hw
  · rw [if_pos hh, if_pos hh]
    have hS' := hS.setHead hn hh
    have hU := Upd.setHead hS p G hn hh
    refine ⟨hS', hm.setHead hS hn hh hsup, hg.setHead hS hn hh, hU, ?_⟩
    exact post_adv hH hnp hS hS' hU ⟨rfl, rfl, rfl, hS.cnt_setHead hn hh _⟩ hlf hc
      (by rw [setHead_head, if_pos rfl]; omega) hcur
  · rw [if_neg hh, if_neg hh]
    refine ⟨hS, hm, hg, Upd.rfl' p M G, ?_⟩
    have := cnt_le_head M w
    exact post_adv hH hnp hS hS (Upd.rfl' p M G) ⟨rfl, rfl, rfl, rfl⟩ hlf hc
      (by have := ha.2.2.2; omega) hcur

lemma GInv.congr {G' : Ghost np} (hg : GInv H M G) (h1 : G'.bg = G.bg) (h2 : G'.hm = G.hm)
    (h3 : G'.hs = G.hs) : GInv H M G' := by
  obtain ⟨a, b, c, d, e, f⟩ := hg
  exact ⟨by rw [h1]; exact a, by rw [h1, h3]; exact b, by rw [h3]; exact c, by rw [h3]; exact d,
    by rw [h2]; exact e, by rw [h1, h2]; exact f⟩

lemma gd_ccnt (M : Mem V) (v d : ℕ) (hd : d < 2) : gd (ccnt M v) d = cnt M (2 * v + d) := by
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> simp [gd, ccnt]

lemma step_r25 (hS : Shape H np M) (hm : MInv H M) (hg : GInv H M G) {v k : ℕ}
    (hP : PInv H os rs M G p pend ⟨.r25 v k, cur, lh⟩) :
    StepRes H np p os rs pend M G M
      ⟨Function.update G.pg p (ccnt M v), Function.update G.ph p (M.head v),
        Function.update G.pg1 p (G.pg p), G.bg, G.hm, G.hs⟩
      ⟨.r27 v k (M.head v) 0, cur, lh⟩ := by
  obtain ⟨hlf, ⟨r1, r2, r3, dc, hdc, hin, hk2⟩, hB⟩ := hP
  refine ⟨hS, hm, hg.congr rfl rfl rfl, Upd.ghostOnly p M G _ rfl rfl rfl (fun q hq => by
    simp [Function.update_of_ne hq]), hlf, ?_, hB, by omega, by omega⟩
  have hhl := hg.hs_le_cnt v r1 r2 (M.head v) le_rfl
  refine ⟨r1, r2, r3, hS.head_pos v, le_rfl, by simp, by simp [ccnt], by simp [ccnt],
    by simpa [ccnt] using hhl.1, by simpa [ccnt] using hhl.2, fun h => absurd h (lt_irrefl _),
    ⟨dc, hdc, ?_, fun hk => ?_⟩, ?_⟩
  · simp only [Function.update_self]; rw [gd_ccnt M v dc hdc]; exact hin
  · obtain ⟨a, b, c, d, e, f⟩ := hk2 hk
    have hmono := hg.hs_mono v r1 r2 (G.ph p + 1) (M.head v) (by omega) (by omega) le_rfl
    simp only [Function.update_self]
    exact ⟨a, c.trans hmono.1, d.trans hmono.2⟩
  · intro d hd b hb hbc
    simp only [Function.update_self] at hb
    rw [gd_ccnt M v d hd] at hb; omega

lemma step_r27 (hS : Shape H np M) (hm : MInv H M) (hg : GInv H M G) {v k h d : ℕ}
    (hP : PInv H os rs M G p pend ⟨.r27 v k h d, cur, lh⟩) :
    StepRes H np p os rs pend M G M G ⟨.r28 v k h d (M.head (2 * v + d)), cur, lh⟩ := by
  obtain ⟨hlf, hR, hB, hd, hd1⟩ := hP
  exact ⟨hS, hm, hg, Upd.rfl' p M G, hlf, hR, hB, hd, hd1,
    (hR.gd_le hd).trans (cnt_le_head M _), hS.head_pos _, le_rfl⟩

lemma step_r28 (hS : Shape H np M) (hm : MInv H M) (hg : GInv H M G) {v k h d ch : ℕ}
    (hP : PInv H os rs M G p pend ⟨.r28 v k h d ch, cur, lh⟩) :
    StepRes H np p os rs pend M G M G (stepLoc H p ⟨.r28 v k h d ch, cur, lh⟩ M).2 := by
  obtain ⟨hlf, hR, hB, hd, hd1, hgd, hch1, hch⟩ := hP
  refine ⟨hS, hm, hg, Upd.rfl' p M G, ?_⟩
  have hR' := hR
  obtain ⟨r1, r2, -⟩ := hR'
  simp only [stepLoc, act, memδ]
  by_cases hb : (M.blk (2 * v + d) ch).isSome
  · rw [hb]
    simp only [enterAdv, show 2 * v + d ≠ 1 by omega, if_false]
    exact ⟨hlf, ⟨by omega, by rw [pow_succ]; omega, hch1, (hS.inst _ _).1 hb⟩, by omega,
      hR, hB, hd, rfl, hgd, hd1⟩
  · have hlt : gd (G.pg p) d < M.head (2 * v + d) := by
      have := (hS.inst (2 * v + d) ch).not.1 hb
      have := hR.gd_le hd
      omega
    simp only [Bool.not_eq_true] at hb
    rw [hb]
    simp only [afterAdv]
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · simp only [ite_true]
      exact ⟨hlf, hR, hB, by omega, fun _ => by simpa [gd] using hlt⟩
    · simp only [one_ne_zero, ite_false]
      exact ⟨hlf, hR, hB, hd1 rfl, by simpa [gd] using hlt⟩

lemma step_c43 (hS : Shape H np M) (hm : MInv H M) (hg : GInv H M G) {v k h : ℕ}
    (hP : PInv H os rs M G p pend ⟨.c43 v k h, cur, lh⟩) :
    StepRes H np p os rs pend M G M G ⟨.c44 v k h (M.head (2 * v) - 1), cur, lh⟩ := by
  obtain ⟨hlf, hR, hB, hl, hr⟩ := hP
  have hR' := hR
  obtain ⟨r1, r2, r3, r4, r5, -⟩ := hR'
  have hh1 : h - 1 ≤ cnt M v := by have := head_le_cnt_succ M v; omega
  have := hS.head_pos (2 * v)
  refine ⟨hS, hm, hg, Upd.rfl' p M G, hlf, hR, hB, by omega,
    by have := (hS.endlt v (h - 1) hh1).1; omega, by omega, hr,
    supUp_of_lt_head hS hm (by omega) (by omega) (by omega)⟩

lemma gd_le_endOf {g : ℕ × ℕ} {B : Blk V} {d : ℕ} (hd : d < 2) (h1 : g.1 ≤ B.endl)
    (h2 : g.2 ≤ B.endr) : gd g d ≤ B.endd d := by
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> simp [gd, Blk.endd, *]

lemma step_c44 (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) (hS : Shape H np M) (hm : MInv H M)
    (hg : GInv H M G) {v k h el : ℕ} (hP : PInv H os rs M G p pend ⟨.c44 v k h el, cur, lh⟩)
    (hcur : ∀ o, pend = some o → os[rs.length]? = some o) :
    StepRes H np p os rs pend M G M G (stepLoc H p ⟨.c44 v k h el, cur, lh⟩ M).2 := by
  obtain ⟨hlf, hR, hB, c1, c2, c3, c4, c5⟩ := hP
  have hR' := hR
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, ⟨dc, hdc, hin, hk2⟩, r12⟩ := hR'
  have hh1 : h - 1 ≤ cnt M v := by have := head_le_cnt_succ M v; omega
  refine ⟨hS, hm, hg, Upd.rfl' p M G, ?_⟩
  simp only [stepLoc, act, memδ]
  cases hz : createBlock M v h el with
  | some B =>
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := create_some hS r2 hh1 c2 c3 hz
    have := hS.head_pos (2 * v + 1)
    have hend := (hS.endlt v (h - 1) hh1).2
    refine ⟨hlf, hR, hB, by omega, by omega, by omega, by omega, by omega, by omega, e3, e4, e5, e6,
      by rw [e1]; exact c5, by rw [e2]; exact supUp_of_lt_head hS hm (by omega) (by omega) (by omega)⟩
  | none =>
    obtain ⟨n1, n2⟩ := create_none hS r1 r2 hh1 c2 c3 hz
    refine after_refresh hH hnp hS hlf hR hB ?_ (fun h' => by simp at h') hcur
    intro _
    have hle : gd (G.pg p) dc ≤ endOf M v (h - 1) dc := by
      rcases (show dc = 0 ∨ dc = 1 by omega) with rfl | rfl
      · simp only [gd, endOf, Blk.endd, ite_true]; omega
      · simp only [gd, endOf, Blk.endd, one_ne_zero, ite_false]; omega
    have := mem_pre_of_child hS r1 r2 hh1 hdc hle (List.mem_map.1 hin).choose_spec.1
    obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hin
    exact List.mem_map.2 ⟨y, mem_pre_mono hh1 (mem_pre_of_child hS r1 r2 hh1 hdc hle hy), hyx⟩

lemma step_r35 (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) (hS : Shape H np M) (hm : MInv H M)
    (hg : GInv H M G) {v k h : ℕ} {B : Blk V} (hP : PInv H os rs M G p pend ⟨.r35 v k h B, cur, lh⟩) :
    StepRes H np p os rs pend M G (stepLoc H p ⟨.r35 v k h B, cur, lh⟩ M).1
      (gstepLoc H M G p ⟨.r35 v k h B, cur, lh⟩) (stepLoc H p ⟨.r35 v k h B, cur, lh⟩ M).2 := by
  obtain ⟨hlf, hR, hB, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := hP
  have hR' := hR
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, ⟨dc, hdc, hin, hk2⟩, r12⟩ := hR'
  have hh1 : h - 1 ≤ cnt M v := by have := head_le_cnt_succ M v; omega
  simp only [stepLoc, act, memδ, gstepLoc]
  by_cases hn : (M.blk v h).isNone
  · rw [if_pos hn, if_pos hn]
    have hn' : M.blk v h = none := by simpa using hn
    have hsn : M.sup v h = none := hm.supNone v h (by have := (hS.fresh hn' r5).1; omega)
    have hS' := hS.setBlk_internal r1 r2 hn' r5 c3 c4 c5 c6 c7 c8 c9 c10
    have hU := Upd.setBlk hS p G B hn' r5 (fun q _ heq => by
        have := leaf_ge H q; omega) (upd2 G.bg v h (G.pg p))
      (fun m j hmj => by rw [upd2_apply, if_neg hmj])
    have hk : Keeps H M (M.setBlk v h B) G
        ⟨G.pg, G.ph, G.pg1, upd2 G.bg v h (G.pg p), upd2 G.hm v h (M.head (v / 2)), G.hs⟩ p :=
      ⟨rfl, rfl, rfl, by rw [hS.cnt_setBlk hn' r5, if_neg (by have := leaf_ge H p; omega)]⟩
    have hcv : cnt (M.setBlk v h B) v = h := hS.cnt_setBlk_self hn' r5 B
    refine ⟨hS', hm.setBlk hS hn' r5 ?_, hg.setBlk_internal hS r1 r2 hn' r5 hsn c1 c2 r9 r10 r12,
      hU, ?_⟩
    · intro d hd b s hb hs hbd
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
      · obtain ⟨s', hs', hle⟩ := c11 b hb (by simpa [Blk.endd] using hbd)
        rw [Nat.add_zero] at hs; rw [hs] at hs'; cases hs'; exact hle hn'
      · obtain ⟨s', hs', hle⟩ := c12 b hb (by simpa [Blk.endd] using hbd)
        rw [hs] at hs'; cases hs'; exact hle hn'
    · have hctx : CtxInv H os rs (M.setBlk v h B)
          ⟨G.pg, G.ph, G.pg1, upd2 G.bg v h (G.pg p), upd2 G.hm v h (M.head (v / 2)), G.hs⟩
          p pend ⟨.r35 v k h B, cur, lh⟩ (.own v k h true) v h := by
        refine ⟨hR.frame hS hU hk, hB.frame hS hU hk, rfl, rfl, fun _ => ?_⟩
        rw [hcv]
        have hle : gd (G.pg p) dc ≤ endOf (M.setBlk v h B) v h dc := by
          rw [endOf, setBlk_bk, if_pos ⟨rfl, rfl⟩]; exact gd_le_endOf hdc c1 c2
        obtain ⟨y, hy, hyx⟩ := List.mem_map.1 (hin.frame hS hU (hR.gd_le hdc))
        exact List.mem_map.2 ⟨y, mem_pre_of_child hS' r1 r2 hcv.ge hdc hle hy, hyx⟩
      have hlf' := LeafOK.upd (p := p) (os := os) hS hU hk.2.2.2 hlf
      have hadv : AdvOK H (M.setBlk v h B) v h := ⟨r1, by rw [pow_succ]; omega, r4, hcv.ge⟩
      simp only [enterAdv]
      split_ifs with hv1
      · exact ⟨hlf', hadv, fun h2 => by omega, hctx⟩
      · exact ⟨hlf', hadv, by omega, hctx⟩
  · rw [if_neg hn, if_neg hn]
    have hsome : (M.blk v h).isSome := Option.ne_none_iff_isSome.1 (by simpa using hn)
    have hhc : h ≤ cnt M v := (hS.inst v h).1 hsome
    refine ⟨hS, hm, hg, Upd.rfl' p M G, ?_⟩
    have hctx : CtxInv H os rs M G p pend ⟨.r35 v k h B, cur, lh⟩ (.own v k h false) v h := by
      refine ⟨hR, hB, rfl, rfl, fun hor => ?_⟩
      have hk : k = 2 := by simpa using hor
      obtain ⟨a, b, c⟩ := hk2 hk
      have hbg := hg.bg_le v r1 r2 h r4 hhc
      have hsb := hg.hs_le_bg v r1 r2 h r4 hhc
      have hle : gd (G.pg1 p) dc ≤ endOf M v h dc := by
        rcases (show dc = 0 ∨ dc = 1 by omega) with rfl | rfl
        · simp only [gd, endOf, Blk.endd, ite_true]; omega
        · simp only [gd, endOf, Blk.endd, one_ne_zero, ite_false]; omega
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 a
      exact List.mem_map.2 ⟨y, mem_pre_mono hhc (mem_pre_of_child hS r1 r2 hhc hdc hle hy), hyx⟩
    have hadv : AdvOK H M v h := ⟨r1, by rw [pow_succ]; omega, r4, hhc⟩
    simp only [enterAdv]
    split_ifs with hv1
    · exact ⟨hlf, hadv, fun h2 => by omega, hctx⟩
    · exact ⟨hlf, hadv, by omega, hctx⟩

lemma mem_keys_of_mem_deqs {K : Type} {l : List (K × FifoOp V)} {k : K} (h : k ∈ deqs l) :
    k ∈ l.map Prod.fst := by
  simp only [deqs, List.mem_filterMap] at h
  obtain ⟨y, hy, hy'⟩ := h
  obtain ⟨x, o⟩ := y
  cases o <;> simp at hy'
  subst hy'; exact List.mem_map.2 ⟨_, hy, rfl⟩

lemma step_idx (hnp : np ≤ 2 ^ H) (hS : Shape H np M) (hm : MInv H M) (hg : GInv H M G)
    {v b i : ℕ} (hP : PInv H os rs M G p pend ⟨.idx v b i, cur, lh⟩) :
    StepRes H np p os rs pend M G M G (stepLoc H p ⟨.idx v b i, cur, lh⟩ M).2 := by
  obtain ⟨hlf, hB, hcur, hroot, hv2, hvT, hb1, hb, hi1, hi, hx⟩ := hP
  refine ⟨hS, hm, hg, Upd.rfl' p M G, ?_⟩
  have hxk : xOf rs p ∈ (ops H np M v b).map Prod.fst :=
    mem_keys_of_mem_deqs (List.mem_of_getElem? hx)
  have hbc := idx_bound hS hnp hroot hv2 hvT hb hxk
  obtain ⟨s1, s2, -, -, s5, s6, s7⟩ :=
    idxStep_spec hS (supOK_of hS hm hg hnp) hv2 hvT hb1 hbc hi1 hi
  simp only [stepLoc, act, memδ]
  rw [hx] at s7
  split_ifs with hv
  · rw [hv] at s2 s6 s7
    exact ⟨hlf, hB, hcur, hroot, s1, s2, s5, s6, s7⟩
  · exact ⟨hlf, hB, hcur, hroot, by omega, by omega, s1, s2, s5, s6, s7⟩

lemma step_fr (hH : 1 ≤ H) (hS : Shape H np M) (hm : MInv H M) (hg : GInv H M G)
    {b i : ℕ} (hP : PInv H os rs M G p pend ⟨.fr b i, cur, lh⟩) :
    StepRes H np p os rs pend M G M G (stepLoc H p ⟨.fr b i, cur, lh⟩ M).2 := by
  obtain ⟨hlf, hB, hcur, hroot, hb1, hb, hi1, hi, hx⟩ := hP
  refine ⟨hS, hm, hg, Upd.rfl' p M G, ?_⟩
  have spec := findResp_spec hS hH (nodup_rootLin hS) hb1 hb hi1 hi
  have hxe : (deqs (ops H np M 1 b))[i - 1]'(by omega) = xOf rs p := by
    rw [List.getElem?_eq_getElem (by omega)] at hx; exact Option.some.inj hx
  simp only [stepLoc, act, memδ]
  revert spec
  cases hf : findResp M b i with
  | none =>
    intro spec; simp only at spec
    rw [hxe] at spec
    exact ⟨hlf, hB, spec⟩
  | some r =>
    obtain ⟨be, ie⟩ := r
    intro spec; simp only at spec
    obtain ⟨t1, t2, t3, t4, t5⟩ := spec
    rw [hxe, List.getElem?_eq_getElem (by omega)] at t5
    exact ⟨hlf, hB, hcur, le_rfl, Nat.one_lt_two_pow (by omega), t1, t2, t3, t4, _,
      List.getElem?_eq_getElem (by omega), t5⟩

lemma step_ge (hS : Shape H np M) (hm : MInv H M) (hg : GInv H M G)
    {v b i : ℕ} (hP : PInv H os rs M G p pend ⟨.ge v b i, cur, lh⟩) :
    StepRes H np p os rs pend M G M G (stepLoc H p ⟨.ge v b i, cur, lh⟩ M).2 := by
  obtain ⟨hlf, hB, hcur, hv1, hvT, hb1, hb, hi1, hi, e, he, hresp⟩ := hP
  refine ⟨hS, hm, hg, Upd.rfl' p M G, ?_⟩
  simp only [stepLoc, act, memδ, isLeaf]
  by_cases hleaf : 2 ^ H ≤ v
  · simp only [hleaf, decide_true, ite_true]
    refine ⟨hlf, hB, ?_⟩
    rw [hresp]
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    obtain ⟨B, hBb⟩ := Option.isSome_iff_exists.1 (hS.blk_isSome hb)
    have hused : v - 2 ^ H < np := by
      by_contra hc; have := hS.unused v (Or.inr (by omega)); omega
    rw [Shape.ops_leaf _ _ hleaf, hBb] at he hi
    simp only [leafOps, hleaf, hused, and_self, dite_true] at he hi
    simp only [hBb, Option.getD_some]
    unfold blkOp at he hi
    cases hel : B.elem with
    | none => simp [hel, enqs] at hi; omega
    | some val =>
      simp only [hel, enqs] at he hi
      simp at hi
      have : i = 1 := by omega
      subst this
      simp at he; rw [← he]
  · simp only [hleaf, decide_false, ite_false]
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := getEnqStep_spec hS hv1 (by omega) hb1 hb hi1 hi
    refine ⟨hlf, hB, hcur, by omega, by rcases g1 with h | h <;> rw [h, pow_succ] <;> omega,
      g2, g3, g4, g5, e, by rw [g6]; exact he, hresp⟩

/-- **One step of a process preserves the invariant** (repaired algorithm). -/
theorem stepRes (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) (hS : Shape H np M) (hm : MInv H M)
    (hg : GInv H M G) {l : Loc V} (hP : PInv H os rs M G p pend l)
    (hcur : ∀ o, pend = some o → os[rs.length]? = some o)
    (hact : ∃ i o k, act H Variant.fixed p.val l = .access i o k) :
    StepRes H np p os rs pend M G (stepLoc H p l M).1 (gstepLoc H M G p l)
      (stepLoc H p l M).2 := by
  obtain ⟨pc, cur, lh⟩ := l
  cases pc with
  | idle => obtain ⟨_, _, _, h⟩ := hact; cases h
  | done r => obtain ⟨_, _, _, h⟩ := hact; cases h
  | app0 => exact step_app0 hS hm hg hP
  | app1 h => exact step_app1 hS hm hg hP
  | app2 h B =>
    have hL : 2 ^ H + p.val ≠ 1 := by have := leaf_two p hH; simp [leafOf] at this; omega
    have e : stepLoc H p ⟨.app2 h B, cur, lh⟩ M =
        (M.setBlk (leafOf H p) h B, ⟨.adv0 .app (leafOf H p) h, cur, h⟩) := by
      simp [stepLoc, act, memδ, Variant.fixed, enterAdv, hL, leafOf]
    rw [e]
    exact step_app2 hH hnp hS hm hg hP hcur
  | app3 h => exact absurd hP.2 id
  | adv0 c w hw => exact step_adv0 hS hm hg hP
  | adv1 c w hw hp => exact step_adv1 hS hm hg hP
  | adv2 c w hw => exact step_adv2 hH hnp hS hm hg hP hcur
  | r25 v k => exact step_r25 hS hm hg hP
  | r27 v k h d => exact step_r27 hS hm hg hP
  | r28 v k h d ch => exact step_r28 hS hm hg hP
  | c43 v k h => exact step_c43 hS hm hg hP
  | c44 v k h el => exact step_c44 hH hnp hS hm hg hP hcur
  | r35 v k h B => exact step_r35 hH hnp hS hm hg hP
  | idx v b i => exact step_idx hnp hS hm hg hP
  | fr b i => exact step_fr hH hS hm hg hP
  | ge v b i =>
    have e1 : (stepLoc H p ⟨.ge v b i, cur, lh⟩ M).1 = M := by
      simp only [stepLoc, act]; split_ifs <;> rfl
    rw [e1]; exact step_ge hS hm hg hP

end

end Podc.WaitFreeQueuePolylog
