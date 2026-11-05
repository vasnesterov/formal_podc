import Papers.PODC2013.ConstantBarriersMutex.RunBasic

/-!
# Performed doorway writes, and who changes tree nodes

`perf s p` is the number of doorway writes (statements 17, 18, 20) of `p`'s current passage that
have been *performed* (left the store buffer). Writes are performed in program order (TSO), so
the write of statement 20 to the node at level `l` (index `dIdx l = 2 + (h − l)` of `doorList`)
is performed iff `dIdx l < perf`.
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-- The program counter is in the doorway (statements 18–22). -/
def PC.Door : PC h → Prop
  | .e18 | .e19 _ | .e22 => True
  | _ => False

instance (c : PC h) : Decidable c.Door := by unfold PC.Door; split <;> infer_instance

/-- Number of performed doorway writes of the current passage (`h + 3` after the barrier). -/
def perf (s : Cfg h) (p : Proc h) : ℕ :=
  if (s.pc p).Door then (s.pc p).issued - (s.buf p).length else h + 3

/-- Index in `doorList` of the write to the node at level `l`. -/
def dIdx (h l : ℕ) : ℕ := 2 + (h - l)

lemma Door_iff {c : PC h} : c.Door ↔ c = .e18 ∨ (∃ l, c = .e19 l) ∨ c = .e22 := by
  cases c <;> simp [PC.Door]

lemma issued_le {s : Cfg h} (hI : Inv s) {p : Proc h} (hd : (s.pc p).Door) :
    (s.pc p).issued ≤ h + 3 := by
  have hL := hI.loc p; unfold LI at hL
  revert hd hL; cases s.pc p <;> simp [PC.Door, PC.issued] <;> omega

/-- In the doorway, the store buffer consists of the issued but not performed doorway writes. -/
lemma buf_door {s : Cfg h} (hI : Inv s) {p : Proc h} (hd : (s.pc p).Door) :
    s.buf p = ((doorList p).take (s.pc p).issued).drop (perf s p) ∧
      perf s p ≤ (s.pc p).issued ∧
      (s.mem.apply p = true ↔ 2 ≤ perf s p) := by
  obtain ⟨i, hi, hb, ha, -⟩ := LI_door (hI.loc p) (Door_iff.1 hd)
  have hk := issued_le hI hd
  have hlen : (s.buf p).length = (s.pc p).issued - i := by
    rw [hb, List.length_drop, List.length_take, doorList_length]; omega
  have hperf : perf s p = i := by unfold perf; rw [if_pos hd, hlen]; omega
  rw [hperf]; exact ⟨hb, hi, ha⟩

/-- A buffered doorway write has index at least `perf`. -/
lemma mem_buf_door {s : Cfg h} (hI : Inv s) {p : Proc h} (hd : (s.pc p).Door) {j : ℕ}
    {w : W h} (hj : (doorList p)[j]? = some w) (hw : w ∈ s.buf p)
    (hinj : ∀ j', (doorList p)[j']? = some w → j' = j) : perf s p ≤ j := by
  obtain ⟨hb, -, -⟩ := buf_door hI hd
  rw [hb] at hw
  obtain ⟨n, hn, hn'⟩ := List.getElem_of_mem hw
  have hn2 : (doorList p)[perf s p + n]? = some w := by
    rw [← hn']; simp only [List.getElem_drop, List.getElem_take]
    rw [List.getElem?_eq_getElem]
  have := hinj _ hn2; omega

/-! ### Levels of the tree -/

lemma anc_lt (p : Proc h) {l : ℕ} (hl : l ≤ h) : anc p l < 2 ^ (l + 1) := by
  unfold anc leaf
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  have hp := p.isLt
  calc 2 ^ h + p.val < 2 ^ h + 2 ^ h := by omega
    _ = 2 ^ (l + 1) * 2 ^ (h - l) := by
      rw [← pow_add, show l + 1 + (h - l) = h + 1 by omega, pow_succ]; ring

lemma le_anc (p : Proc h) {l : ℕ} (hl : l ≤ h) : 2 ^ l ≤ anc p l := by
  unfold anc leaf
  rw [Nat.le_div_iff_mul_le (by positivity), ← pow_add, show l + (h - l) = h by omega]
  omega

/-- The node at level `l` determines the level. -/
lemma anc_level {p q : Proc h} {l l' : ℕ} (hl : l ≤ h) (hl' : l' ≤ h) (he : anc p l = anc q l') :
    l = l' := by
  have h1 := anc_lt p hl; have h2 := le_anc p hl
  have h3 := anc_lt q hl'; have h4 := le_anc q hl'
  rw [he] at h1 h2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : 2 ^ (l + 1) ≤ 2 ^ l' := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have : 2 ^ (l' + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

lemma anc_zero (p : Proc h) : anc p 0 = 1 := by
  have h1 := anc_lt p (Nat.zero_le h); have h2 := le_anc p (Nat.zero_le h); simp at h1 h2; omega

/-- The node at level `k ≥ 1` is a child of the node at level `k − 1`. -/
lemma anc_child (p : Proc h) {k : ℕ} (hk : 1 ≤ k) (hkh : k ≤ h) :
    anc p k = 2 * anc p (k - 1) ∨ anc p k = 2 * anc p (k - 1) + 1 := by
  unfold anc
  have : h - (k - 1) = (h - k) + 1 := by omega
  rw [this, pow_succ, ← Nat.div_div_eq_div_mul]
  omega

lemma anc_child_target (p : Proc h) {k : ℕ} (hk : 1 ≤ k) (hkh : k ≤ h) :
    ∃ j, 1 ≤ j ∧ j ≤ 2 ∧ anc p k = target (anc p (k - 1)) j := by
  rcases anc_child p hk hkh with h1 | h1
  · exact ⟨1, le_rfl, by norm_num, by simp [target, h1]⟩
  · exact ⟨2, by norm_num, le_rfl, by simp [target, h1]⟩

/-- Distinct doorway node writes have distinct indices. -/
lemma doorList_node_inj (p : Proc h) {l j : ℕ} (hl : l ≤ h)
    (hj : (doorList p)[j]? = some (.node (anc p l) p)) : j = dIdx h l := by
  rcases j with _ | _ | j
  · simp [doorList_get0] at hj
  · simp [doorList_get1] at hj
  · simp only [doorList, List.getElem?_cons_succ] at hj
    have hjl : j < h + 1 := by
      by_contra hc; rw [List.getElem?_eq_none (by simp; omega)] at hj; simp at hj
    rw [List.getElem?_map, List.getElem?_reverse (by simpa using hjl)] at hj
    simp only [List.length_range] at hj
    rw [List.getElem?_range (by omega)] at hj
    simp only [Option.map_some, Option.some.injEq, W.node.injEq, and_true] at hj
    have := anc_level (p := p) (q := p) (by omega) hl hj
    unfold dIdx; omega

/-! ### Memory changes -/

/-- A step changes memory only by a flush (barrier) or, at a CAS, the `lock` field. -/
lemma stepProc_mem_cases {s : Cfg h} (hI : Inv s) (q : Proc h) :
    ((s.stepProc q).mem.node = s.mem.node ∧ (s.stepProc q).mem.apply = s.mem.apply) ∨
      (s.buf q ≠ [] ∧ s.stepProc q = s.flush q) := by
  by_cases hc : s.pc q = .e23 ∨ s.pc q = .e26
  · left
    have hL := hI.loc q; unfold LI at hL
    have hb : s.buf q = [] := by rcases hc with hc | hc <;> rw [hc] at hL <;> exact hL.1
    rcases hc with hc | hc <;> simp only [Cfg.stepProc, hc, Cfg.cas, hb, Mem.view_nil] <;>
      split <;> simp
  · by_cases hbar : s.pc q = .e22 ∨ ∃ o, s.pc q = .x50 o
    · by_cases hb : s.buf q = []
      · left
        rcases hbar with hbar | ⟨o, hbar⟩ <;> simp [Cfg.stepProc, hbar, Cfg.barrier, hb]
      · right; refine ⟨hb, ?_⟩
        rcases hbar with hbar | ⟨o, hbar⟩ <;> simp [Cfg.stepProc, hbar, Cfg.barrier, hb]
    · left; push_neg at hc hbar
      rw [Run.stepProc_mem _ _ hbar.1 hc.1 hc.2 hbar.2]; exact ⟨rfl, rfl⟩

/-- Who changes a tree node: a process `q` performing its write `node i ← q`. -/
lemma Run.node_change (r : Run h) {t i : ℕ}
    (hne : (r.s (t + 1)).mem.node i ≠ (r.s t).mem.node i) :
    ∃ q b, (r.s t).buf q = .node i q :: b ∧ (r.s (t + 1)).mem.node i = some q ∧
      (r.ev t = .flush q ∨ r.ev t = .step q) ∧ (r.s (t + 1)).buf q = b := by
  have hI := r.inv t
  have hflush : ∀ q, ((r.s t).flush q).mem.node i ≠ (r.s t).mem.node i →
      ∃ b, (r.s t).buf q = .node i q :: b ∧ ((r.s t).flush q).mem.node i = some q ∧
        ((r.s t).flush q).buf q = b := by
    intro q hq
    rcases hb : (r.s t).buf q with _ | ⟨w, b⟩
    · rw [flush_of_nil _ _ hb] at hq; exact absurd rfl hq
    · rw [flush_of_cons _ _ hb] at hq ⊢
      simp only [write_node] at hq ⊢
      have hw : ∃ v, w = .node i v := by
        cases w with
        | node i' v =>
          by_cases h1 : i' = i
          · subst h1; exact ⟨v, rfl⟩
          · simp [h1] at hq
        | _ => simp at hq
      obtain ⟨v, rfl⟩ := hw
      have hv : v = q := by
        by_cases hg : Holds (r.s t) q
        · rcases hI.holder_buf hg (.node i v) (by simp [hb]) with h1 | h1 | ⟨nx, h1⟩
          · rcases h1 with h1 | h1 | h1 | ⟨r', b', h1⟩ <;> simp_all [W.isExits, W.isPromQ]
          · simp [W.isLock] at h1
          · cases h1
        · rcases hI.nonholder_buf hg (.node i v) (by simp [hb]) with h1 | h1 | ⟨i', h1⟩ | ⟨nx, h1⟩ <;>
            simp_all
      subst hv
      exact ⟨b, rfl, by simp, by simp⟩
  rw [r.next_eq] at hne ⊢
  rcases he : r.ev t with q | q <;> simp only [he, Cfg.next] at hne ⊢
  · rcases stepProc_mem_cases hI q with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact absurd (by rw [h1]) hne
    · rw [h1] at hne ⊢
      obtain ⟨b, h2, h3, h4⟩ := hflush q hne
      exact ⟨q, b, h2, h3, Or.inr rfl, h4⟩
  · obtain ⟨b, h2, h3, h4⟩ := hflush q hne
    exact ⟨q, b, h2, h3, Or.inl rfl, h4⟩

/-! ### Dynamics of `perf` -/

lemma perf_congr {s s' : Cfg h} {p : Proc h} (hp : s'.pc p = s.pc p) (hb : s'.buf p = s.buf p) :
    perf s' p = perf s p := by unfold perf; rw [hp, hb]

/-- Performing the oldest doorway write increments `perf`. -/
lemma perf_flush {s : Cfg h} (hI : Inv s) {p : Proc h} (hd : (s.pc p).Door) {w : W h}
    {b : List (W h)} (hb : s.buf p = w :: b) :
    perf (s.flush p) p = perf s p + 1 ∧ (doorList p)[perf s p]? = some w ∧
      (s.flush p).mem = s.mem.write w := by
  obtain ⟨hb', hle, -⟩ := buf_door hI hd
  rw [hb] at hb'
  obtain ⟨hlt, hget, -⟩ := drop_take_cons hb'.symm
  have hlen : (s.buf p).length = (s.pc p).issued - perf s p := by
    rw [hb, hb', List.length_drop, List.length_take, doorList_length]
    have := issued_le hI hd; omega
  refine ⟨?_, hget, flush_mem hb⟩
  have hF : perf (s.flush p) p = (s.pc p).issued - b.length := by
    unfold perf; rw [flush_pc, if_pos hd, flush_buf_self hb]
  rw [hb] at hlen; simp at hlen
  omega

lemma stepProc_pc_wait {s : Cfg h} {q : Proc h} (hw : (s.pc q).Waiting ∨ s.pc q = .e23) :
    ¬ ((s.stepProc q).pc q).Door := by
  have key : ∀ c, (c = .e24 ∨ c = .e27) → ∀ c' : PC h, ¬ ((s.cas q c).pc q).Door := by
    intro c hc _; unfold Cfg.cas; simp only; split <;> simp <;> rcases hc with rfl | rfl <;>
      simp [PC.Door]
  rcases hw with hw | hw
  · revert hw; cases hpc : s.pc q <;> simp only [PC.Waiting, IsEmpty.forall_iff, forall_const]
    all_goals simp only [Cfg.stepProc, hpc]
    all_goals first
      | exact key _ (Or.inr rfl) .cs
      | (simp [PC.Door]; done)
      | (split_ifs <;> simp [PC.Door, hpc])
      | skip
  · simp only [Cfg.stepProc, hw]; exact key _ (Or.inl rfl) .cs

/-- One step of `perf` while `p` stays in its entry section: unchanged, or the next doorway
write is performed. -/
lemma Run.perf_succ (r : Run h) {t : ℕ} {p : Proc h} (hE : ((r.s t).pc p).Entry)
    (hE' : ((r.s (t + 1)).pc p).Entry) :
    perf (r.s (t + 1)) p = perf (r.s t) p ∨
      (perf (r.s (t + 1)) p = perf (r.s t) p + 1 ∧
        ∃ w, (doorList p)[perf (r.s t) p]? = some w ∧ (r.s (t + 1)).mem = (r.s t).mem.write w) := by
  have hI := r.inv t
  have hL := hI.loc p
  -- the flush case
  have hfl : ∀ s' : Cfg h, s' = (r.s t).flush p → (r.s (t + 1)) = s' →
      perf (r.s (t + 1)) p = perf (r.s t) p ∨
      (perf (r.s (t + 1)) p = perf (r.s t) p + 1 ∧
        ∃ w, (doorList p)[perf (r.s t) p]? = some w ∧ (r.s (t + 1)).mem = (r.s t).mem.write w) := by
    rintro s' rfl hs
    rw [hs]
    rcases hb : (r.s t).buf p with _ | ⟨w, b⟩
    · left; rw [flush_of_nil _ _ hb]
    · by_cases hd : ((r.s t).pc p).Door
      · obtain ⟨h1, h2, h3⟩ := perf_flush hI hd hb
        exact Or.inr ⟨h1, w, h2, h3⟩
      · left; unfold perf; rw [flush_pc, if_neg hd, if_neg hd]
  rcases he : r.ev t with q | q
  · by_cases hq : q = p
    · subst hq
      have hs : r.s (t + 1) = (r.s t).stepProc q := by rw [r.next_eq, he]; rfl
      rw [hs] at hE' ⊢
      unfold LI at hL
      cases hpc : (r.s t).pc q with
      | e18 =>
        rw [hpc] at hL
        left
        have : (r.s t).stepProc q = (r.s t).loc q [.apply q true] (.e19 h) := by
          simp [Cfg.stepProc, hpc, issue_eq_loc]
        rw [this]; unfold perf
        simp only [loc_pc_self, loc_buf_self, hpc, PC.Door, if_true, PC.issued, List.length_append,
          List.length_singleton]
        obtain ⟨i, hi, hb, -⟩ := hL
        have : ((r.s t).buf q).length ≤ 1 := by rw [hb]; simp
        omega
      | e19 l =>
        rw [hpc] at hL
        left
        by_cases hl0 : l = 0
        · subst hl0
          have : (r.s t).stepProc q = (r.s t).loc q [.node (anc q 0) q] .e22 := by
            simp [Cfg.stepProc, hpc, issue_eq_loc]
          rw [this]; unfold perf
          simp only [loc_pc_self, loc_buf_self, hpc, PC.Door, if_true, PC.issued,
            List.length_append, List.length_singleton]
          obtain ⟨-, i, hi, hb, -⟩ := hL
          have : ((r.s t).buf q).length ≤ 2 + h := by
            rw [hb]; simp
          omega
        · have : (r.s t).stepProc q = (r.s t).loc q [.node (anc q l) q] (.e19 (l - 1)) := by
            simp [Cfg.stepProc, hpc, issue_eq_loc, hl0]
          rw [this]; unfold perf
          simp only [loc_pc_self, loc_buf_self, hpc, PC.Door, if_true, PC.issued,
            List.length_append, List.length_singleton]
          obtain ⟨hlh, i, hi, hb, -⟩ := hL
          have : ((r.s t).buf q).length ≤ 2 + (h - l) := by
            rw [hb]; simp
          omega
      | e22 =>
        by_cases hb : (r.s t).buf q = []
        · left
          have : (r.s t).stepProc q = (r.s t).loc q [] .e23 := by
            simp only [Cfg.stepProc, hpc]; exact barrier_goto hb
          rw [this]; unfold perf
          simp [loc_pc_self, hpc, PC.Door, PC.issued, hb]
        · have : (r.s t).stepProc q = (r.s t).flush q := by
            simp only [Cfg.stepProc, hpc]; exact barrier_flush hb
          rw [← hs] at this ⊢
          exact hfl _ rfl this
      | e23 | e24 | e25a _ | e25b _ | e26 | e27 =>
        left
        unfold perf
        rw [if_neg (stepProc_pc_wait (by simp [hpc, PC.Waiting])), if_neg (by simp [hpc, PC.Door])]
      | _ => rw [hpc] at hE; simp [PC.Entry] at hE
    · left
      apply perf_congr
      · exact r.pc_succ_of_ne (by rw [he]; intro h'; cases h'; exact hq rfl)
      · exact r.buf_succ_of_ne (by rw [he]; intro h'; cases h'; exact hq rfl) (by rw [he]; simp)
  · by_cases hq : q = p
    · subst hq
      exact hfl _ rfl (by rw [r.next_eq, he]; rfl)
    · left
      apply perf_congr
      · exact r.pc_succ_of_ne (by rw [he]; simp)
      · exact r.buf_succ_of_ne (by rw [he]; simp) (by rw [he]; intro h'; cases h'; exact hq rfl)

/-! ### Consequences over intervals in the entry section -/

namespace Run

variable (r : Run h) {p : Proc h}

lemma perf_mono {t₁ t₂ : ℕ} (h12 : t₁ ≤ t₂)
    (hE : ∀ t, t₁ ≤ t → t ≤ t₂ → ((r.s t).pc p).Entry) : perf (r.s t₁) p ≤ perf (r.s t₂) p := by
  induction t₂, h12 using Nat.le_induction with
  | base => exact le_rfl
  | succ t ht ih =>
    have := ih (fun t' h1 h2 => hE t' h1 (by omega))
    rcases r.perf_succ (hE t ht (by omega)) (hE (t + 1) (by omega) le_rfl) with h1 | ⟨h1, -⟩ <;>
      omega

/-- After its write to the node at level `l` is performed (and while the passage lasts), `p`
cannot write `p` to that node again: a value other than `p` stays other than `p`. -/
lemma node_ne_persist {t₁ t₂ l : ℕ} (hl : l ≤ h) (h12 : t₁ ≤ t₂)
    (hE : ∀ t, t₁ ≤ t → t ≤ t₂ → ((r.s t).pc p).Entry) (hd : dIdx h l < perf (r.s t₁) p)
    (hne : (r.s t₁).mem.node (anc p l) ≠ some p) : (r.s t₂).mem.node (anc p l) ≠ some p := by
  induction t₂, h12 using Nat.le_induction with
  | base => exact hne
  | succ t ht ih =>
    have ih' := ih (fun t' h1 h2 => hE t' h1 (by omega))
    intro heq
    have hch : (r.s (t + 1)).mem.node (anc p l) ≠ (r.s t).mem.node (anc p l) := by
      rw [heq]; exact fun h' => ih' h'.symm
    obtain ⟨q, b, hb, hv, -, -⟩ := r.node_change hch
    rw [heq] at hv; cases hv
    -- `p` has its level-`l` write pending at `t`
    have hI := r.inv t
    have hpe : perf (r.s t₁) p ≤ perf (r.s t) p :=
      r.perf_mono ht (fun t' h1 h2 => hE t' h1 (by omega))
    by_cases hdoor : ((r.s t).pc p).Door
    · have := mem_buf_door hI hdoor (doorList_getNode p hl) (by rw [hb]; simp)
        (fun j' hj' => doorList_node_inj p hl hj')
      unfold dIdx at hd; omega
    · have hL := hI.loc p
      have hEt := hE t ht (by omega)
      unfold LI at hL
      revert hdoor hL hEt
      cases (r.s t).pc p <;> simp [PC.Door, PC.Entry, hb]

/-- `perf` crosses every value between its values at the ends of an interval in the entry
section; at the crossing, the corresponding doorway write is performed. -/
lemma perf_cross {t₁ t₂ d : ℕ} (h12 : t₁ ≤ t₂)
    (hE : ∀ t, t₁ ≤ t → t ≤ t₂ → ((r.s t).pc p).Entry) (h1 : perf (r.s t₁) p ≤ d)
    (h2 : d < perf (r.s t₂) p) :
    ∃ t, t₁ ≤ t ∧ t < t₂ ∧ perf (r.s t) p = d ∧
      ∃ w, (doorList p)[d]? = some w ∧ (r.s (t + 1)).mem = (r.s t).mem.write w := by
  induction t₂, h12 using Nat.le_induction with
  | base => omega
  | succ t ht ih =>
    rcases r.perf_succ (hE t ht (by omega)) (hE (t + 1) (by omega) le_rfl) with h3 | ⟨h3, w, hw, hm⟩
    · obtain ⟨t', ht1, ht2, ht3⟩ := ih (fun t' a b => hE t' a (by omega)) (by omega)
      exact ⟨t', ht1, by omega, ht3⟩
    · by_cases hd : d < perf (r.s t) p
      · obtain ⟨t', ht1, ht2, ht3⟩ := ih (fun t' a b => hE t' a (by omega)) hd
        exact ⟨t', ht1, by omega, ht3⟩
      · have : perf (r.s t) p = d := by omega
        exact ⟨t, ht, by omega, this, w, this ▸ hw, hm⟩

/-- At the crossing of the index of the level-`l` write, the node holds `p`. -/
lemma node_of_cross {t l : ℕ} (hl : l ≤ h) {w : W h}
    (hw : (doorList p)[dIdx h l]? = some w) (hm : (r.s (t + 1)).mem = (r.s t).mem.write w) :
    (r.s (t + 1)).mem.node (anc p l) = some p := by
  unfold dIdx at hw; rw [doorList_getNode p hl] at hw; cases hw
  rw [hm]; simp [Mem.write]

end Run

end Podc.ConstantBarriersMutex
