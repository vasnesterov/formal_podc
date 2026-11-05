import Papers.PODC2023.WaitFreeQueuePolylog.Inv

/-!
# Steps of other processes preserve a process's invariant

Every step changes the memory and the ghost state in a monotone way (`Upd`): installed blocks
and `super` fields never change, `head` fields only grow (by one, after the block at the old
`head` is installed), the ghost values of installed blocks and of past `head` values never
change, and the linearization only grows. `PInv.frame` shows that the per-process invariant of
any process other than the stepping one survives such an update.
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ}

/-- A monotone update of memory and ghost state by a step of process `p`. -/
structure Upd (H np : ℕ) (p : Fin np) (M M' : Mem V) (G G' : Ghost np) : Prop where
  blk_eq : ∀ n j, j ≤ cnt M n → M'.blk n j = M.blk n j
  cnt_mono : ∀ n, cnt M n ≤ cnt M' n
  cnt_leaf : ∀ q : Fin np, q ≠ p → cnt M' (leafOf H q) = cnt M (leafOf H q)
  head_mono : ∀ n, M.head n ≤ M'.head n
  head_inc : ∀ n, M.head n < M'.head n →
    M'.head n = M.head n + 1 ∧ (M.blk n (M.head n)).isSome ∧ G'.hs n (M'.head n) = ccnt M n
  sup_mono : ∀ n j s, M.sup n j = some s → M'.sup n j = some s
  bg_eq : ∀ n j, j ≤ cnt M n → G'.bg n j = G.bg n j
  hm_eq : ∀ n j, j ≤ cnt M n → G'.hm n j = G.hm n j
  hm_new : ∀ n j, cnt M n < j → j ≤ cnt M' n → G'.hm n j = M.head (n / 2)
  hs_eq : ∀ n j, j ≤ M.head n → G'.hs n j = G.hs n j
  pg_eq : ∀ q, q ≠ p → G'.pg q = G.pg q ∧ G'.ph q = G.ph q ∧ G'.pg1 q = G.pg1 q
  lin_ext : ∃ E, rootLin H np M' = rootLin H np M ++ E

namespace Upd

variable {p : Fin np} {M M' : Mem V} {G G' : Ghost np}

lemma bk_eq (hU : Upd H np p M M' G G') {n j : ℕ} (h : j ≤ cnt M n) : M'.bk n j = M.bk n j := by
  simp [Mem.bk, hU.blk_eq n j h]

lemma head_eq_of_full (hS : Shape H np M) (hU : Upd H np p M M' G G') {n : ℕ}
    (h : M.head n = cnt M n + 1) : M'.head n = M.head n := by
  by_contra hne
  have hlt : M.head n < M'.head n := lt_of_le_of_ne (hU.head_mono n) (Ne.symm hne)
  have := (hU.head_inc n hlt).2.1
  rw [hS.inst] at this; omega

lemma pre_eq (hS : Shape H np M) (hU : Upd H np p M M' G G') {n j : ℕ} (h : j ≤ cnt M n) :
    pre H np M' n j = pre H np M n j := pre_congr hS hU.blk_eq h

lemma ops_eq (hS : Shape H np M) (hU : Upd H np p M M' G G') {n j : ℕ} (h : j ≤ cnt M n) :
    ops H np M' n j = ops H np M n j := ops_congr hS hU.blk_eq n j h

lemma mem_pre (hS : Shape H np M) (hU : Upd H np p M M' G G') {n j : ℕ} (h : j ≤ cnt M n)
    {x : OpId (Fin np)} (hx : x ∈ (pre H np M n j).map Prod.fst) :
    x ∈ (pre H np M' n j).map Prod.fst := by rwa [hU.pre_eq hS h]

lemma mem_pre_cnt (hS : Shape H np M) (hU : Upd H np p M M' G G') {n : ℕ}
    {x : OpId (Fin np)} (hx : x ∈ (pre H np M n (cnt M n)).map Prod.fst) :
    x ∈ (pre H np M' n (cnt M' n)).map Prod.fst := by
  rw [← hU.pre_eq hS le_rfl] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact List.mem_map.2 ⟨y, mem_pre_mono (hU.cnt_mono n) hy, rfl⟩

lemma respIn_eq (hU : Upd H np p M M' G G') {x : OpId (Fin np)} {r : Option V}
    (h : (queueObj V).respIn [] (rootLin H np M) x = some r) :
    (queueObj V).respIn [] (rootLin H np M') x = some r := by
  obtain ⟨E, hE⟩ := hU.lin_ext
  rw [hE, ObjSpec.respIn_append_of_mem (ObjSpec.mem_of_respIn_eq_some h)]; exact h

lemma ccnt_le (hU : Upd H np p M M' G G') (v : ℕ) :
    (ccnt M v).1 ≤ (ccnt M' v).1 ∧ (ccnt M v).2 ≤ (ccnt M' v).2 :=
  ⟨hU.cnt_mono _, hU.cnt_mono _⟩

end Upd

/-- The ghost variables and the leaf of `q` are unchanged. -/
def Keeps (H : ℕ) {np : ℕ} (M M' : Mem V) (G G' : Ghost np) (q : Fin np) : Prop :=
  G'.pg q = G.pg q ∧ G'.ph q = G.ph q ∧ G'.pg1 q = G.pg1 q ∧
    cnt M' (leafOf H q) = cnt M (leafOf H q)

lemma Upd.keeps {p q : Fin np} {M M' : Mem V} {G G' : Ghost np} (hU : Upd H np p M M' G G')
    (hq : q ≠ p) : Keeps H M M' G G' q :=
  ⟨(hU.pg_eq q hq).1, (hU.pg_eq q hq).2.1, (hU.pg_eq q hq).2.2, hU.cnt_leaf q hq⟩

section Frame

variable {p q : Fin np} {M M' : Mem V} {G G' : Ghost np} {os : List (FifoOp V)}
  {rs : List (Option V)} {pend : Option (FifoOp V)} {l : Loc V}

lemma PreW.frame (hS : Shape H np M) (hU : Upd H np p M M' G G') (hq : Keeps H M M' G G' q)
    (h : PreW H os rs M q pend l) : PreW H os rs M' q pend l := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, by rw [hq.2.2.2]; exact h3, ?_⟩
  rw [hq.2.2.2, hU.head_eq_of_full hS h4, h4]

lemma Base.frame (hU : Upd H np p M M' G G') (hq : Keeps H M M' G G' q)
    (h : Base H os rs M q pend l) : Base H os rs M' q pend l := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, by rw [hq.2.2.2]; exact h3, by rw [hq.2.2.2]; exact h4⟩

lemma BaseH.frame (hS : Shape H np M) (hU : Upd H np p M M' G G') (hq : Keeps H M M' G G' q)
    (h : BaseH H os rs M q pend l) : BaseH H os rs M' q pend l := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1.frame hU hq, ?_⟩
  rw [hq.2.2.2, hU.head_eq_of_full hS h2, h2]

lemma SupUp.frame (hS : Shape H np M) (hU : Upd H np p M M' G G') {c e v h : ℕ}
    (hh : SupUp M c e v h) : SupUp M' c e v h := by
  intro b h1 h2
  obtain ⟨s, hs, hle⟩ := hh b h1 h2
  refine ⟨s, hU.sup_mono _ _ _ hs, fun hn => hle ?_⟩
  by_cases hc : h ≤ cnt M v
  · rw [hU.blk_eq v h hc] at hn; exact hn
  · exact hS.blk_none (by omega)

lemma InChild.frame (hS : Shape H np M) (hU : Upd H np p M M' G G') {v d g : ℕ}
    (hg : g ≤ cnt M (2 * v + d)) (h : InChild H rs M q v d g) : InChild H rs M' q v d g :=
  hU.mem_pre hS hg h

lemma RefCtx.frame (hS : Shape H np M) (hU : Upd H np p M M' G G') (hq : Keeps H M M' G G' q) {v k h : ℕ}
    (hh : RefCtx H rs M G q v k h) : RefCtx H rs M' G' q v k h := by
  obtain ⟨hpg, hph, hpg1, -⟩ := id hq
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ⟨dc, hdc, hin, hk2⟩, h12⟩ := hh
  have hsh : G'.hs v h = G.hs v h := hU.hs_eq v h h5
  refine ⟨h1, h2, h3, h4, h5.trans (hU.head_mono v), by rw [hph]; exact h6,
    by rw [hpg]; exact h7.trans (hU.cnt_mono _), by rw [hpg]; exact h8.trans (hU.cnt_mono _),
    by rw [hsh, hpg]; exact h9, by rw [hsh, hpg]; exact h10, ?_, ?_, ?_⟩
  · intro hlt
    rw [hpg]
    by_cases hl : h < M.head v
    · rw [hU.hs_eq v (h + 1) hl]; exact h11 hl
    · have he : M.head v = h := by omega
      have hinc := hU.head_inc v (by omega)
      have : M'.head v = h + 1 := by omega
      rw [← this, hinc.2.2]; exact ⟨h7, h8⟩
  · have hgle : ∀ d, d < 2 → gd (G.pg q) d ≤ cnt M (2 * v + d) := by
      intro d hd
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
      · simpa [gd] using h7
      · simpa [gd] using h8
    refine ⟨dc, hdc, by rw [hpg]; exact hin.frame hS hU (hgle dc hdc), fun hk => ?_⟩
    obtain ⟨a, b, c⟩ := hk2 hk
    have hle : gd (G.pg1 q) dc ≤ gd (G.pg q) dc := by
      rcases (show dc = 0 ∨ dc = 1 by omega) with rfl | rfl
      · simp only [gd, ite_true]; exact b.trans h9
      · simp only [gd, one_ne_zero, ite_false]; exact c.trans h10
    exact ⟨by rw [hpg1]; exact a.frame hS hU (hle.trans (hgle dc hdc)),
      by rw [hpg1, hsh]; exact b, by rw [hpg1, hsh]; exact c⟩
  · intro d hd b hb hbc
    rw [hpg] at hb
    by_cases hold : b ≤ cnt M (2 * v + d)
    · rw [hU.hm_eq _ _ hold]; exact h12 d hd b hb hold
    · rw [hU.hm_new _ _ (by omega) hbc]
      rw [show (2 * v + d) / 2 = v by omega]; exact h5

lemma OwnPost.frame (hS : Shape H np M) (hU : Upd H np p M M' G G') {v k : ℕ} {res : Bool}
    (h : OwnPost H rs M q v k res) : OwnPost H rs M' q v k res :=
  fun hr => hU.mem_pre_cnt hS (h hr)

lemma PropAt.frame (hS : Shape H np M) (hU : Upd H np p M M' G G') (hq : Keeps H M M' G G' q) {v k : ℕ}
    (hh : PropAt H rs M G q v k) : PropAt H rs M' G' q v k := by
  obtain ⟨hpg, hph, hpg1, -⟩ := id hq
  obtain ⟨h1, h2, h3, dc, hdc, hin, hk2⟩ := hh
  refine ⟨h1, h2, h3, dc, hdc, hU.mem_pre_cnt hS hin, fun hk => ?_⟩
  obtain ⟨a, b, c, d, e, f⟩ := hk2 hk
  have hsh := hU.hs_eq v (G.ph q + 1) b
  refine ⟨?_, by rw [hph]; exact b.trans_le (hU.head_mono v), by rw [hpg, hph, hsh]; exact c,
    by rw [hpg, hph, hsh]; exact d, by rw [hpg]; exact e.trans (hU.cnt_mono _),
    by rw [hpg]; exact f.trans (hU.cnt_mono _)⟩
  rw [hpg]
  refine a.frame hS hU ?_
  rcases (show dc = 0 ∨ dc = 1 by omega) with rfl | rfl
  · simpa [gd] using e
  · simpa [gd] using f

lemma InRoot.frame (hS : Shape H np M) (hU : Upd H np p M M' G G')
    (h : InRoot H rs M q) : InRoot H rs M' q := hU.mem_pre_cnt hS h

lemma AdvOK.frame (hU : Upd H np p M M' G G') {w hw : ℕ} (h : AdvOK H M w hw) :
    AdvOK H M' w hw := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans (hU.cnt_mono w)⟩

lemma head_le_of_lt_head (hU : Upd H np p M M' G G') {a n : ℕ} (h : a < M.head n) :
    a < M'.head n := h.trans_le (hU.head_mono n)

lemma CtxInv.frame (hS : Shape H np M) (hU : Upd H np p M M' G G') (hq : Keeps H M M' G G' q) {c : Ctx}
    {w hw : ℕ} (h : CtxInv H os rs M G q pend l c w hw) : CtxInv H os rs M' G' q pend l c w hw := by
  obtain ⟨hpg, -, -, -⟩ := id hq
  cases c with
  | app => exact ⟨h.1, h.2.1.frame hU hq, h.2.2⟩
  | ref v k h' d =>
    obtain ⟨a, b, c, e, f, g⟩ := h
    exact ⟨a.frame hS hU hq, b.frame hS hU hq, c, e, by rw [hpg]; exact f,
      fun hd => by rw [hpg]; exact head_le_of_lt_head hU (g hd)⟩
  | own v k h' res =>
    obtain ⟨a, b, c, e, f⟩ := h
    exact ⟨a.frame hS hU hq, b.frame hS hU hq, c, e, f.frame hS hU⟩

lemma RefCtx.h_le_cnt {v k h : ℕ} (hh : RefCtx H rs M G q v k h) : h - 1 ≤ cnt M v := by
  have := hh.2.2.2.2.1
  have := head_le_cnt_succ M v
  omega

/-- **Frame.** The invariant of a process survives the steps of other processes. -/
theorem PInv.frame (hS : Shape H np M) (hU : Upd H np p M M' G G') (hq : Keeps H M M' G G' q)
    (h : PInv H os rs M G q pend l) : PInv H os rs M' G' q pend l := by
  obtain ⟨hpg, hph, hpg1, -⟩ := id hq
  obtain ⟨hleaf, hpc⟩ := h
  refine ⟨?_, ?_⟩
  · intro j h1 h2
    rw [hq.2.2.2] at h2
    rw [hU.bk_eq h2]; exact hleaf j h1 h2
  obtain ⟨pc, cur, lh⟩ := l
  have hcl := hq.2.2.2
  cases pc with
  | idle =>
    obtain ⟨a, b, c, d⟩ := hpc
    exact ⟨a, b, by rw [hcl]; exact c, by rw [hcl, hU.head_eq_of_full hS d, d]⟩
  | app0 => exact PreW.frame hS hU hq hpc
  | app1 h =>
    obtain ⟨a, b⟩ := hpc
    exact ⟨a.frame hS hU hq, by rw [hU.head_eq_of_full hS a.2.2.2]; exact b⟩
  | app2 h B =>
    obtain ⟨a, b, c⟩ := hpc
    have hh := hU.head_eq_of_full hS a.2.2.2
    refine ⟨a.frame hS hU hq, by rw [hh]; exact b, ?_⟩
    rw [hU.bk_eq (by have := a.2.2.2; omega)]; exact c
  | app3 h => exact hpc
  | adv0 c w hw =>
    obtain ⟨a, b, e⟩ := hpc
    exact ⟨a.frame hU, b, e.frame hS hU hq⟩
  | adv1 c w hw hp =>
    obtain ⟨a, b, e, f, g⟩ := hpc
    exact ⟨a.frame hU, b, by rw [hU.hm_eq _ _ a.2.2.2]; exact e,
      f.trans (hU.head_mono _), g.frame hS hU hq⟩
  | adv2 c w hw =>
    obtain ⟨a, b, e⟩ := hpc
    refine ⟨a.frame hU, fun hw2 => ?_, e.frame hS hU hq⟩
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 (b hw2)
    rw [hU.sup_mono _ _ _ hs]; rfl
  | r25 v k =>
    obtain ⟨a, b⟩ := hpc
    exact ⟨a.frame hS hU hq, b.frame hS hU hq⟩
  | r27 v k h d =>
    obtain ⟨a, b, c, e⟩ := hpc
    exact ⟨a.frame hS hU hq, b.frame hS hU hq, c,
      fun hd => by rw [hpg]; exact head_le_of_lt_head hU (e hd)⟩
  | r28 v k h d ch =>
    obtain ⟨a, b, c, e, f, g, i⟩ := hpc
    exact ⟨a.frame hS hU hq, b.frame hS hU hq, c,
      fun hd => by rw [hpg]; exact head_le_of_lt_head hU (e hd), by rw [hpg]; exact f, g,
      i.trans (hU.head_mono _)⟩
  | c43 v k h =>
    obtain ⟨a, b, c, e⟩ := hpc
    exact ⟨a.frame hS hU hq, b.frame hS hU hq, by rw [hpg]; exact head_le_of_lt_head hU c,
      by rw [hpg]; exact head_le_of_lt_head hU e⟩
  | c44 v k h el =>
    obtain ⟨a, b, c, e, f, g, i⟩ := hpc
    exact ⟨a.frame hS hU hq, b.frame hS hU hq, by rw [hpg]; exact c,
      by rw [hU.bk_eq a.h_le_cnt]; exact e, head_le_of_lt_head hU f,
      by rw [hpg]; exact head_le_of_lt_head hU g, i.frame hS hU⟩
  | r35 v k h B =>
    obtain ⟨a, b, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := hpc
    have e1 : B.endl ≤ cnt M (2 * v) := Nat.le_of_lt_succ (c5.trans_le (head_le_cnt_succ M _))
    have e2 : B.endr ≤ cnt M (2 * v + 1) :=
      Nat.le_of_lt_succ (c6.trans_le (head_le_cnt_succ M _))
    have e3 := hU.bk_eq a.h_le_cnt
    exact ⟨a.frame hS hU hq, b.frame hS hU hq, by rw [hpg]; exact c1, by rw [hpg]; exact c2,
      by rw [e3]; exact c3, by rw [e3]; exact c4, head_le_of_lt_head hU c5,
      head_le_of_lt_head hU c6, by rw [hU.bk_eq e1, hU.bk_eq e2]; exact c7,
      by rw [hU.bk_eq e1, hU.bk_eq e2]; exact c8, by rw [e3]; exact c9,
      by rw [e3]; exact c10, c11.frame hS hU, c12.frame hS hU⟩
  | idx v b i =>
    obtain ⟨a, b', c, d, e, f, g, h1, h2, h3⟩ := hpc
    refine ⟨a.frame hS hU hq, b', c.frame hS hU, d, e, f, g.trans (hU.cnt_mono _), h1, ?_, ?_⟩
    · rw [hU.ops_eq hS g]; exact h2
    · rw [hU.ops_eq hS g]; exact h3
  | fr b i =>
    obtain ⟨a, b', c, f, g, h1, h2, h3⟩ := hpc
    refine ⟨a.frame hS hU hq, b', c.frame hS hU, f, g.trans (hU.cnt_mono _), h1, ?_, ?_⟩
    · rw [hU.ops_eq hS g]; exact h2
    · rw [hU.ops_eq hS g]; exact h3
  | ge v b i =>
    obtain ⟨a, b', d, e, f, g, h1, h2, x, h3, h4⟩ := hpc
    refine ⟨a.frame hS hU hq, b', d, e, f, g.trans (hU.cnt_mono _), h1, ?_, x, ?_,
      hU.respIn_eq h4⟩
    · rw [hU.ops_eq hS g]; exact h2
    · rw [hU.ops_eq hS g]; exact h3
  | done r =>
    obtain ⟨a, b⟩ := hpc
    exact ⟨a.frame hS hU hq, hU.respIn_eq b⟩

end Frame

end Podc.WaitFreeQueuePolylog
