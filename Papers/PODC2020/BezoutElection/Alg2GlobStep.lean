import Papers.PODC2020.BezoutElection.Alg2Glob

/-!
# Algorithm 2: the global invariant is preserved by the micro-steps

Micro-steps: a read of the collect, the end of the collect (lines N(1)–N(4)), processing one
register in the for loop, the end of the for loop, a write, an invocation and a response.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P] {m : ℕ}
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id}

lemma AState.upd_self (A : AState Id P) (q : P) : A.upd q (A.loc q) = A := by
  unfold AState.upd; simp

/-- The program counters of the local states do not matter. -/
theorem ginv_congr {mem : Fin m → Reg Id} {loc loc' : P → St Id m} {vpc : P → VPC Id}
    {g : Ghost P} (G : GInv π pp ids mem loc vpc g)
    (h : ∀ q, ∃ c, loc' q = { loc q with pc := c }) : GInv π pp ids mem loc' vpc g := by
  choose c hc using h
  have habs : ∀ x, absAt π mem loc' vpc x = absAt π mem loc vpc x := by
    intro x; unfold absAt; congr 1; funext q; rw [hc q]; rfl
  exact ⟨fun x => (habs x) ▸ G.abs x, fun q => by rw [hc q]; exact G.me q,
    fun q => by rw [hc q]; exact G.g1 q, fun q => by rw [hc q]; exact G.g2 q, G.g3,
    fun ⟨q, hq⟩ => G.g4 ⟨q, by rw [hc q] at hq; exact hq⟩, G.g5, G.g6a, G.g6b, G.g6c,
    fun q k => by rw [hc q]; exact G.g7 q k, G.ret⟩

/-! ### Frame lemmas for pending writes -/

/-- `c` is not a pending write. -/
def VPC.NoPend (c : VPC Id) : Prop := ∀ k w, c ≠ .pc (.write k w)

lemma pendAt_update_noPend {vpc : P → VPC Id} {q : P} {c : VPC Id} (hc : c.NoPend)
    {q' : P} {x : Fin m} {w : Reg Id} :
    PendAt π (Function.update vpc q c) q' x w ↔ q' ≠ q ∧ PendAt π vpc q' x w := by
  constructor
  · rintro ⟨k, h1, h2⟩
    by_cases hq : q' = q
    · subst hq; simp at h1; exact absurd h1 (hc _ _)
    · rw [Function.update_of_ne hq] at h1; exact ⟨hq, k, h1, h2⟩
  · rintro ⟨hq, k, h1, h2⟩
    exact ⟨k, by rw [Function.update_of_ne hq]; exact h1, h2⟩

lemma not_isN11At_of_noPend {mem : Fin m → Reg Id} {vpc : P → VPC Id} {q : P}
    (h : (vpc q).NoPend) : ¬IsN11At π mem vpc q := by
  rintro ⟨x, w, ⟨k, h1, -⟩, -⟩; exact h _ _ h1

lemma n11Count_update_noPend {mem : Fin m → Reg Id} {vpc : P → VPC Id} {q : P} {c : VPC Id}
    (hold : (vpc q).NoPend) (hc : c.NoPend) :
    n11Count π mem (Function.update vpc q c) = n11Count π mem vpc := by
  classical
  have := n11Count_change (π := π) mem mem vpc (Function.update vpc q c) q (by
    intro j hj
    simp only [IsN11At, pendAt_update_noPend hc]
    exact ⟨fun ⟨x, w, h1, h2⟩ => ⟨x, w, ⟨hj, h1⟩, h2⟩, fun ⟨x, w, ⟨_, h1⟩, h2⟩ => ⟨x, w, h1, h2⟩⟩)
  rw [if_neg (not_isN11At_of_noPend hold), if_neg (not_isN11At_of_noPend (by simpa using hc))]
    at this
  omega

/-- Changing the virtual program counter and the local state of `q` without touching pending
writes, returns, the memory or the ghost: everything except the per-register invariants and
the local facts is preserved. -/
theorem ginv_frame {mem : Fin m → Reg Id} {loc : P → St Id m} {vpc : P → VPC Id} {g : Ghost P}
    (G : GInv π pp ids mem loc vpc g) {q : P} {s : St Id m} {c : VPC Id}
    (hold : (vpc q).NoPend) (hc : c.NoPend) (hret : ∀ L, c ≠ .pc (.ret L))
    (habs : ∀ x, AInv pp.n pp.U ids (absAt π mem (Function.update loc q s)
      (Function.update vpc q c) x))
    (hme : s.me = (loc q).me) (hfin : s.finishing = (loc q).finishing)
    (htw : s.toWin = (loc q).toWin) (hcand : s.cand = (loc q).cand) :
    GInv π pp ids mem (Function.update loc q s) (Function.update vpc q c) g := by
  have hloc : ∀ j, (Function.update loc q s j).me = (loc j).me ∧
      (Function.update loc q s j).finishing = (loc j).finishing ∧
      (Function.update loc q s j).toWin = (loc j).toWin ∧
      (Function.update loc q s j).cand = (loc j).cand := by
    intro j; by_cases hj : j = q
    · subst hj; simp [hme, hfin, htw, hcand]
    · simp [Function.update_of_ne hj]
  refine ⟨habs, fun j => (hloc j).1.trans (G.me j), fun j h => ?_, fun j h => ?_, G.g3,
    fun ⟨j, hj⟩ => G.g4 ⟨j, (hloc j).2.1 ▸ hj⟩, ?_, G.g6a, ?_, ?_, fun j k h => ?_, ?_⟩
  · rw [(hloc j).2.2.1]; exact G.g1 j ((hloc j).2.1 ▸ h)
  · rw [(hloc j).2.2.1]; exact G.g2 j ((hloc j).2.1 ▸ h)
  · rw [n11Count_update_noPend hold hc]; exact G.g5
  · intro j hj
    rcases G.g6b j hj with h | ⟨x, w, h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨x, w, pendAt_update_noPend hc |>.2 ⟨?_, h1⟩, h2⟩
      rintro rfl; obtain ⟨k, h1, -⟩ := h1; exact hold _ _ h1
  · intro j x w h; exact G.g6c j x w (pendAt_update_noPend hc |>.1 h).2
  · rw [(hloc j).2.2.2] at h ⊢; rw [(hloc j).2.2.1]; exact G.g7 j k h
  · intro j L h
    by_cases hj : j = q
    · subst hj; simp at h; exact absurd h (hret L)
    · rw [Function.update_of_ne hj] at h; exact G.ret j L h

/-! ### Reads of the collect -/

/-- The local state after reading `v` into the local copy of register `k`. -/
def St.setReg (s : St Id m) (k : Fin m) (v : Reg Id) : St Id m :=
  { s with regs := Function.update s.regs k v }

theorem ginv_read {mem : Fin m → Reg Id} {loc : P → St Id m} {vpc : P → VPC Id} {g : Ghost P}
    (G : GInv π pp ids mem loc vpc g) {q : P} {j : ℕ} (hj : j < m)
    (hq : vpc q = .pc (.collect j)) :
    GInv π pp ids mem
      (Function.update loc q ((loc q).setReg ⟨j, hj⟩ (mem (π q ⟨j, hj⟩))))
      (Function.update vpc q (.pc (.collect (j + 1)))) g := by
  set k : Fin m := ⟨j, hj⟩ with hk
  set s' : St Id m := (loc q).setReg k (mem (π q k)) with hs'
  refine ginv_frame G (by rw [hq]; intro _ _ h; cases h) (by intro _ _ h; cases h)
    (by intro _ h; cases h) ?_ rfl rfl rfl rfl
  intro x
  rw [absAt_update]
  by_cases hx : x = π q k
  · subst hx
    have h1 : (absAt π mem loc vpc (π q k)).loc q = locX (loc q) k .fresh := by
      rw [absAt_loc, hq]; simp [vstatus, hk]
    have := ainv_read (G.abs (π q k)) (p := q) (by rw [h1]; rfl)
    have e : (absAt π mem loc vpc (π q k)).upd q (locX s' ((π q).symm (π q k))
        (vstatus (.pc (.collect (j + 1))) s' ((π q).symm (π q k)))) =
        (absAt π mem loc vpc (π q k)).setSt q (.copy (mem (π q k))) := by
      unfold AState.setSt; congr 1; rw [h1]; simp [locX, vstatus, hs', St.setReg, hk]
    rw [e]; exact this
  · have hk' : (π q).symm x ≠ k := by
      intro h; apply hx; rw [← h]; simp
    have hv : ((π q).symm x).val ≠ j := fun h => hk' (Fin.ext h)
    convert G.abs x using 1
    conv_rhs => rw [← AState.upd_self (absAt π mem loc vpc x) q]
    congr 1
    rw [absAt_loc, hq]
    simp only [vstatus, hs', locX, St.setReg, Function.update_of_ne hk']
    congr 1
    by_cases h : j ≤ ((π q).symm x).val
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]

/-! ### The status of a process -/

lemma vstatus_pend_iff {c : VPC Id} {s : St Id m} {k : Fin m} {w : Reg Id} :
    vstatus c s k = .pend w ↔ c = .pc (.write k.val w) := by
  constructor
  · intro h
    cases c with
    | pc c =>
      cases c with
      | idle => simp [vstatus] at h
      | collect j => simp only [vstatus] at h; split_ifs at h
      | write j w' =>
        simp only [vstatus] at h; split_ifs at h with h1 h2
        cases h; rw [h2]
      | ret L => simp [vstatus] at h
      | fin => simp [vstatus] at h
    | loop j => simp only [vstatus] at h; split_ifs at h
  · rintro rfl; simp [vstatus]

lemma pendAt_iff {loc : P → St Id m} {vpc : P → VPC Id} {q : P} {x : Fin m} {w : Reg Id} :
    PendAt π vpc q x w ↔ vstatus (vpc q) (loc q) ((π q).symm x) = .pend w := by
  rw [vstatus_pend_iff]
  constructor
  · rintro ⟨k, h1, rfl⟩; simpa using h1
  · intro h; exact ⟨(π q).symm x, h, by simp⟩

/-- The end of the collect, when all competitions are solved: `q` will return. -/
theorem ginv_after_ret {mem : Fin m → Reg Id} {loc : P → St Id m} {vpc : P → VPC Id}
    {g : Ghost P} (G : GInv π pp ids mem loc vpc g) {q : P} (hq : vpc q = .pc (.collect m))
    (hsum : ∑ k, ((loc q).regs k).level = pp.U * m) :
    GInv π pp ids mem
      (Function.update loc q { loc q with pc := .ret (univ.sup fun k => ((loc q).regs k).leaders) })
      (Function.update vpc q (.pc (.ret (univ.sup fun k => ((loc q).regs k).leaders)))) g := by
  set L := univ.sup fun k => ((loc q).regs k).leaders with hL
  have habs : ∀ x, absAt π mem (Function.update loc q { loc q with pc := .ret L })
      (Function.update vpc q (.pc (.ret L))) x = absAt π mem loc vpc x := by
    intro x
    rw [absAt_update]
    conv_rhs => rw [← AState.upd_self (absAt π mem loc vpc x) q]
    congr 1
    rw [absAt_loc, hq]
    simp only [locX, vstatus]
    rw [if_neg (by omega)]
  -- what `q` read
  have hcopy : ∀ k, (absAt π mem loc vpc (π q k)).loc q = locX (loc q) k (.copy ((loc q).regs k)) := by
    intro k; rw [absAt_loc, hq]; simp only [vstatus, Equiv.symm_apply_apply]; rw [if_neg (by omega)]
  have hle : ∀ k, ((loc q).regs k).level ≤ (mem (π q k)).level ∧ (mem (π q k)).level ≤ pp.U := by
    intro k
    have A := G.abs (π q k)
    exact ⟨(A.1.copyLv q _ (by rw [hcopy k]; rfl)).2, A.1.lvU⟩
  have hU : ∀ k, ((loc q).regs k).level = pp.U := by
    have h1 : ∀ k ∈ univ, ((loc q).regs k).level ≤ pp.U := fun k _ => (hle k).1.trans (hle k).2
    have h2 : ∑ k, ((loc q).regs k).level = ∑ _k : Fin m, pp.U := by simp [hsum, mul_comm]
    intro k; exact (sum_eq_sum_iff_of_le h1).1 h2 k (mem_univ k)
  have hmemU : ∀ x, (mem x).level = pp.U := by
    intro x
    have := hle ((π q).symm x); rw [hU, Equiv.apply_symm_apply] at this; omega
  have hlead : ∀ k, ((loc q).regs k).leaders = (mem (π q k)).leaders := by
    intro k
    exact (G.abs (π q k)).1.copyLead q _ (by rw [hcopy k]; rfl) (by simp [hU, hmemU])
  refine ⟨fun x => (habs x) ▸ G.abs x, fun j => ?_, fun j => ?_, fun j => ?_, G.g3,
    fun ⟨j, hj⟩ => G.g4 ⟨j, ?_⟩, ?_, G.g6a, ?_, ?_, fun j => ?_, ?_⟩
  · by_cases hj : j = q
    · subst hj; simpa using G.me j
    · rw [Function.update_of_ne hj]; exact G.me j
  · by_cases hj : j = q
    · subst hj; simpa using G.g1 j
    · rw [Function.update_of_ne hj]; exact G.g1 j
  · by_cases hj : j = q
    · subst hj; simpa using G.g2 j
    · rw [Function.update_of_ne hj]; exact G.g2 j
  · by_cases hjq : j = q
    · subst hjq; simpa using hj
    · rwa [Function.update_of_ne hjq] at hj
  · rw [n11Count_update_noPend (by rw [hq]; intro _ _ h; cases h) (by intro _ _ h; cases h)]
    exact G.g5
  · intro j hj
    rcases G.g6b j hj with h | ⟨x, w, h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨x, w, (pendAt_update_noPend (by intro _ _ h; cases h)).2 ⟨?_, h1⟩, h2⟩
      rintro rfl; obtain ⟨k, h1, -⟩ := h1; rw [hq] at h1; cases h1
  · intro j x w h
    exact G.g6c j x w (pendAt_update_noPend (by intro _ _ h; cases h) |>.1 h).2
  · by_cases hj : j = q
    · subst hj; simpa using G.g7 j
    · rw [Function.update_of_ne hj]; exact G.g7 j
  · intro j L' h
    by_cases hj : j = q
    · rw [hj] at h
      simp only [Function.update_self, VPC.pc.injEq, PC.ret.injEq] at h
      subst h
      refine ⟨hmemU, ?_⟩
      apply le_antisymm
      · exact Finset.sup_le fun k _ => by
          rw [hlead k]; exact Finset.le_sup (f := fun x => (mem x).leaders) (mem_univ _)
      · exact Finset.sup_le fun x _ => by
          have h1 : (mem x).leaders = ((loc q).regs ((π q).symm x)).leaders := by
            rw [hlead, Equiv.apply_symm_apply]
          rw [h1]
          exact Finset.le_sup (f := fun k => ((loc q).regs k).leaders) (mem_univ ((π q).symm x))
    · rw [Function.update_of_ne hj] at h; exact G.ret j L' h

lemma absAt_update_same {mem : Fin m → Reg Id} {loc : P → St Id m} {vpc : P → VPC Id} (q : P)
    (s : St Id m) (c : VPC Id)
    (hs : ∀ k, locX s k (vstatus c s k) = locX (loc q) k (vstatus (vpc q) (loc q) k)) (x : Fin m) :
    absAt π mem (Function.update loc q s) (Function.update vpc q c) x = absAt π mem loc vpc x := by
  rw [absAt_update, hs, ← absAt_loc, AState.upd_self]

/-- The end of the collect, when not all competitions are solved: lines N(4) and the start of
the for loop. -/
theorem ginv_after_loop (hn : Fintype.card P = pp.n) {mem : Fin m → Reg Id}
    {loc : P → St Id m} {vpc : P → VPC Id} {g : Ghost P} (G : GInv π pp ids mem loc vpc g)
    {q : P} (hq : vpc q = .pc (.collect m)) :
    GInv π pp ids mem (Function.update loc q
      (if pp.W * pp.n ≤ ∑ k, ((loc q).regs k).level ∧ (loc q).finishing = false then
        { loc q with finishing := true, toWin := 1 } else loc q))
      (Function.update vpc q (.loop 0)) g := by
  have hst : ∀ (s : St Id m), s.regs = (loc q).regs → ∀ k : Fin m,
      vstatus (.loop 0) s k = vstatus (vpc q) (loc q) k := by
    intro s hs k; rw [hq]; simp only [vstatus, hs]; rw [if_pos (Nat.zero_le _), if_neg (by omega)]
  split_ifs with h
  · obtain ⟨hW, hf⟩ := h
    set s' : St Id m := { loc q with finishing := true, toWin := 1 } with hs'
    have habs : ∀ x, absAt π mem (Function.update loc q s') (Function.update vpc q (.loop 0)) x =
        absAt π mem loc vpc x :=
      absAt_update_same q s' _ (fun k => by rw [hst s' rfl k]; rfl)
    have hother : ∀ j, j ≠ q → Function.update loc q s' j = loc j :=
      fun j hj => Function.update_of_ne hj _ _
    refine ⟨fun x => (habs x) ▸ G.abs x, fun j => ?_, fun j hj => ?_, fun j hj => ?_, G.g3,
      fun _ => ?_, ?_, G.g6a, ?_, ?_, fun j k hj => ?_, ?_⟩
    · by_cases hjq : j = q
      · rw [hjq]; simpa [hs'] using G.me q
      · rw [hother j hjq]; exact G.me j
    · by_cases hjq : j = q
      · rw [hjq] at hj; simp [hs'] at hj
      · rw [hother j hjq] at hj ⊢; exact G.g1 j hj
    · by_cases hjq : j = q
      · rw [hjq]; simp [hs', (G.g1 q hf).2]
      · rw [hother j hjq] at hj ⊢; exact G.g2 j hj
    · by_cases hex : ∃ j, (loc j).finishing = true
      · exact G.g4 hex
      · push Not at hex
        have hwt : ∀ j, g.wt j = 0 := fun j => (G.g1 j (by simpa using hex j)).2
        have h5 := G.g5
        simp only [hwt, add_zero] at h5
        have hsol : ∑ k, ((loc q).regs k).level ≤ ∑ x, (mem x).level := by
          rw [← Equiv.sum_comp (π q) (fun x => (mem x).level)]
          refine Finset.sum_le_sum fun k _ => ?_
          have hc : (absAt π mem loc vpc (π q k)).loc q = locX (loc q) k (.copy ((loc q).regs k)) := by
            rw [absAt_loc, hq]; simp only [vstatus, Equiv.symm_apply_apply]; rw [if_neg (by omega)]
          exact ((G.abs (π q k)).1.copyLv q _ (by rw [hc]; rfl)).2
        have hle : ∑ j, g.wf j ≤ pp.W * pp.n := by
          calc ∑ j, g.wf j ≤ ∑ _j : P, pp.W := Finset.sum_le_sum fun j _ => G.g3 j
            _ = pp.W * pp.n := by simp [hn, mul_comm]
        omega
    · rw [n11Count_update_noPend (by rw [hq]; intro _ _ h; cases h) (by intro _ _ h; cases h)]
      exact G.g5
    · intro j hj
      rcases G.g6b j hj with h | ⟨x, w, h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨x, w, (pendAt_update_noPend (by intro _ _ h; cases h)).2 ⟨?_, h1⟩, h2⟩
        rintro rfl; obtain ⟨k, h1, -⟩ := h1; rw [hq] at h1; cases h1
    · intro j x w h
      exact G.g6c j x w (pendAt_update_noPend (by intro _ _ h; cases h) |>.1 h).2
    · by_cases hjq : j = q
      · rw [hjq] at hj ⊢; simp only [Function.update_self, hs'] at hj ⊢
        exact ⟨le_refl _, (G.g7 q k hj).2⟩
      · rw [hother j hjq] at hj ⊢; exact G.g7 j k hj
    · intro j L h
      by_cases hjq : j = q
      · rw [hjq] at h; simp at h
      · rw [Function.update_of_ne hjq] at h; exact G.ret j L h
  · exact ginv_frame G (by rw [hq]; intro _ _ h; cases h) (by intro _ _ h; cases h)
      (by intro _ h; cases h) (fun x => (absAt_update_same q (loc q) _
        (fun k => by rw [hst (loc q) rfl k]) x) ▸ G.abs x) rfl rfl rfl rfl

/-- The end of the for loop: a new collect starts. -/
theorem ginv_loopEnd {mem : Fin m → Reg Id} {loc : P → St Id m} {vpc : P → VPC Id}
    {g : Ghost P} (G : GInv π pp ids mem loc vpc g) {q : P} {j : ℕ} (hj : m ≤ j)
    (hq : vpc q = .loop j) :
    GInv π pp ids mem (Function.update loc q { loc q with pc := .collect 0 })
      (Function.update vpc q (.pc (.collect 0))) g := by
  have habs : ∀ x, absAt π mem (Function.update loc q { loc q with pc := .collect 0 })
      (Function.update vpc q (.pc (.collect 0))) x = absAt π mem loc vpc x :=
    absAt_update_same q _ _ (fun k => by
      rw [hq]; simp only [vstatus, locX]; rw [if_pos (Nat.zero_le _), if_neg (by omega)])
  exact ginv_frame G (by rw [hq]; intro _ _ h; cases h) (by intro _ _ h; cases h)
    (by intro _ h; cases h) (fun x => (habs x) ▸ G.abs x) rfl rfl rfl rfl

/-- An invocation. -/
theorem ginv_inv {mem : Fin m → Reg Id} {loc : P → St Id m} {vpc : P → VPC Id}
    {g : Ghost P} (G : GInv π pp ids mem loc vpc g) {q : P} (hq : vpc q = .pc .idle) :
    GInv π pp ids mem (Function.update loc q { loc q with pc := .collect 0 })
      (Function.update vpc q (.pc (.collect 0))) g := by
  have habs : ∀ x, absAt π mem (Function.update loc q { loc q with pc := .collect 0 })
      (Function.update vpc q (.pc (.collect 0))) x = absAt π mem loc vpc x :=
    absAt_update_same q _ _ (fun k => by
      rw [hq]; simp only [vstatus, locX]; rw [if_pos (Nat.zero_le _)])
  exact ginv_frame G (by rw [hq]; intro _ _ h; cases h) (by intro _ _ h; cases h)
    (by intro _ h; cases h) (fun x => (habs x) ▸ G.abs x) rfl rfl rfl rfl

/-- A response. -/
theorem ginv_retStep {mem : Fin m → Reg Id} {loc : P → St Id m} {vpc : P → VPC Id}
    {g : Ghost P} (G : GInv π pp ids mem loc vpc g) {q : P} {L : Finset Id}
    (hq : vpc q = .pc (.ret L)) :
    GInv π pp ids mem (Function.update loc q { loc q with pc := .fin })
      (Function.update vpc q (.pc .fin)) g := by
  have habs : ∀ x, absAt π mem (Function.update loc q { loc q with pc := .fin })
      (Function.update vpc q (.pc .fin)) x = absAt π mem loc vpc x :=
    absAt_update_same q _ _ (fun k => by rw [hq]; rfl)
  exact ginv_frame G (by rw [hq]; intro _ _ h; cases h) (by intro _ _ h; cases h)
    (by intro _ h; cases h) (fun x => (habs x) ▸ G.abs x) rfl rfl rfl rfl

end BezoutElection.Alg2
