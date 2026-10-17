import Papers.PODC2020.BezoutElection.Alg2GlobWrite

/-!
# Algorithm 2: the global invariant is preserved by the for loop
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P] {m : ℕ}
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id}

/-- The virtual program counter after processing register `j`. -/
def nextVPC (j : ℕ) : Option (Reg Id) → VPC Id
  | some w => .pc (.write j w)
  | none => .loop (j + 1)

lemma nextVPC_ne_ret (j : ℕ) (o : Option (Reg Id)) (L : Finset Id) :
    nextVPC j o ≠ .pc (.ret L) := by
  cases o <;> simp [nextVPC]

section ProcX

variable {n U : ℕ} {me : Id} {l : ALoc Id} {r : Reg Id} {ok fin : Bool}

lemma procX_st (a : AStatus Id) :
    procX n U me { l with st := a } r ok fin =
      ({ (procX n U me l r ok fin).1 with st := a }, (procX n U me l r ok fin).2) := by
  unfold procX
  split_ifs <;> rfl

lemma procX_ca (h : (procX n U me l r ok fin).1.ca = true) : l.ca = true ∨ ok = true := by
  rcases procX_cases n U me l r ok fin with
    ⟨-, -, e⟩ | e | ⟨-, -, -, -, e⟩ | ⟨-, -, -, -, -, -, e⟩ | ⟨-, -, -, -, -, e⟩ |
    ⟨-, -, -, -, -, e⟩ | ⟨-, -, -, -, -, -, -, e⟩ <;> rw [e] at h <;> simp at h
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inl h
  · unfold procX at e
    split_ifs at e with h1 h2 h3 h4 <;> simp_all

lemma procX_win_ca {w : Reg Id} (hw : (procX n U me l r ok fin).2 = some w)
    (hl : w.level = r.level + 1) : (procX n U me l r ok fin).1.ca = false := by
  rcases procX_cases n U me l r ok fin with
    ⟨-, -, e⟩ | e | ⟨-, -, -, -, e⟩ | ⟨-, -, -, -, -, -, e⟩ | ⟨-, -, -, -, -, e⟩ |
    ⟨-, -, -, -, -, e⟩ | ⟨-, -, -, -, -, -, -, e⟩ <;> rw [e] at hw ⊢ <;>
    simp only [reduceCtorEq, Option.some.injEq] at hw
  all_goals first | rfl | (subst hw; simp at hl)

end ProcX

lemma vstatus_next_self {s : St Id m} {j : ℕ} (hj : j < m) (o : Option (Reg Id)) :
    vstatus (nextVPC j o) s ⟨j, hj⟩ = stOf o := by
  cases o <;> simp [nextVPC, vstatus, stOf]

lemma vstatus_next_ne {s s' : St Id m} {j : ℕ} (o : Option (Reg Id)) (k' : Fin m)
    (hk : k'.val ≠ j) (hr : s'.regs = s.regs) :
    vstatus (nextVPC j o) s' k' = vstatus (.loop j) s k' := by
  cases o with
  | none =>
    simp only [nextVPC, vstatus, hr]
    by_cases h : j < k'.val
    · rw [if_pos (by omega), if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]
  | some w =>
    simp only [nextVPC, vstatus, hr]
    by_cases h : j < k'.val
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (Ne.symm hk), if_neg (by omega)]

lemma pendAt_next {vpc : P → VPC Id} {q : P} {j : ℕ} (hj : j < m) (o : Option (Reg Id))
    (hq : vpc q = .loop j) {j' : P} {x : Fin m} {w : Reg Id} :
    PendAt π (Function.update vpc q (nextVPC j o)) j' x w ↔
      (j' ≠ q ∧ PendAt π vpc j' x w) ∨ (j' = q ∧ o = some w ∧ x = π q ⟨j, hj⟩) := by
  by_cases hjq : j' = q
  · subst hjq
    simp only [ne_eq, not_true_eq_false, false_and, true_and, false_or]
    constructor
    · rintro ⟨k, h1, h2⟩
      simp only [Function.update_self] at h1
      cases o with
      | none => simp [nextVPC] at h1
      | some w' =>
        simp only [nextVPC, VPC.pc.injEq, PC.write.injEq] at h1
        obtain ⟨h1, rfl⟩ := h1
        refine ⟨rfl, ?_⟩
        rw [← h2]; congr 1; exact Fin.ext h1.symm
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨j, hj⟩, by simp [nextVPC], rfl⟩
  · constructor
    · rintro ⟨k, h1, h2⟩
      rw [Function.update_of_ne hjq] at h1
      exact Or.inl ⟨hjq, k, h1, h2⟩
    · rintro (⟨-, k, h1, h2⟩ | ⟨h, -⟩)
      · exact ⟨k, by rw [Function.update_of_ne hjq]; exact h1, h2⟩
      · exact absurd h hjq

/-- If `f ≤ W` pointwise and `Σ f = W n` with `n = |P|`, then `f = W`. -/
lemma all_eq_of_sum {W n : ℕ} (hn : Fintype.card P = n) (f : P → ℕ) (hle : ∀ i, f i ≤ W)
    (hs : ∑ i, f i = W * n) (i : P) : f i = W := by
  have h2 : ∑ i, f i = ∑ _i : P, W := by simp [hs, hn, mul_comm]
  exact (sum_eq_sum_iff_of_le (fun i _ => hle i)).1 h2 i (mem_univ i)

/-- Processing register `j` in the for loop. -/
theorem ginv_proc (hid : Function.Injective ids) (hn : Fintype.card P = pp.n)
    {mem : Fin m → Reg Id} {loc : P → St Id m} {vpc : P → VPC Id} {g : Ghost P}
    (G : GInv π pp ids mem loc vpc g) {q : P} {j : ℕ} (hj : j < m) (hq : vpc q = .loop j) :
    ∃ g', GInv π pp ids mem (Function.update loc q (procReg pp (loc q) ⟨j, hj⟩).1)
      (Function.update vpc q (nextVPC j (procReg pp (loc q) ⟨j, hj⟩).2)) g' := by
  obtain ⟨k, hk⟩ : ∃ k : Fin m, k = ⟨j, hj⟩ := ⟨_, rfl⟩
  rw [← hk]
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 = π q k := ⟨_, rfl⟩
  set s := loc q with hs
  set s' := (procReg pp s k).1 with hs'
  set o := (procReg pp s k).2 with ho
  set v := s.regs k with hv
  have hme : s.me = ids q := G.me q
  have hfields := procReg_fields pp s k
  rw [← hs'] at hfields
  obtain ⟨hme', hpc', hregs', hfin'⟩ := hfields
  have hoX : o = (oX pp s k).2 := procReg_snd pp s k
  -- the abstract step at `x0`
  have hst : (absAt π mem loc vpc x0).loc q = locX s k (.copy v) := by
    rw [absAt_loc, hq, hx0, Equiv.symm_apply_apply]; simp only [vstatus]
    rw [if_pos (by rw [hk])]
  have A0 := G.abs x0
  have hstc : ((absAt π mem loc vpc x0).loc q).st = .copy v := by rw [hst]; rfl
  have hprocX : procX pp.n pp.U (ids q) ((absAt π mem loc vpc x0).loc q) v (okOf s k) s.finishing =
      ({ (oX pp s k).1 with st := .copy v }, (oX pp s k).2) := by
    rw [hst, oX, hme.symm, show locX s k (.copy v) = { locX s k .fresh with st := .copy v } from rfl,
      procX_st]
  have habs0 : absAt π mem (Function.update loc q s') (Function.update vpc q (nextVPC j o)) x0 =
      (absAt π mem loc vpc x0).upd q (procL pp.n pp.U (ids q) ((absAt π mem loc vpc x0).loc q) v
        (okOf s k) s.finishing) := by
    rw [absAt_update, hx0, Equiv.symm_apply_apply, ← hx0]
    congr 1
    rw [procL, hprocX, hk, vstatus_next_self hj, ← hk, hs', procReg_locX, ← hoX]
  have habs1 : ∀ x, x ≠ x0 →
      absAt π mem (Function.update loc q s') (Function.update vpc q (nextVPC j o)) x =
        absAt π mem loc vpc x := by
    intro x hx
    have hk' : (π q).symm x ≠ k := by intro h; apply hx; rw [hx0, ← h]; simp
    have hv' : ((π q).symm x).val ≠ j := fun h => hk' (by rw [hk]; exact Fin.ext h)
    rw [absAt_update]
    conv_rhs => rw [← AState.upd_self (absAt π mem loc vpc x) q]
    congr 1
    rw [absAt_loc, hq, vstatus_next_ne o _ hv' hregs', hs', procReg_locX_ne pp s k _ hk']
  have hAinv : ∀ x, AInv pp.n pp.U ids
      (absAt π mem (Function.update loc q s') (Function.update vpc q (nextVPC j o)) x) := by
    intro x
    by_cases hx : x = x0
    · rw [hx, habs0]; exact ainv_proc hid hn _ _ A0 hstc
    · rw [habs1 x hx]; exact G.abs x
  have hwf : ∀ w, o = some w → v.level = (mem x0).level ∧ (w.level = v.level ∨
      (w.level = v.level + 1 ∧ s.cand k = true ∧
        w.leaders = if s.finishing then insert (ids q) v.leaders else v.leaders)) := by
    intro w hw
    have := write_facts hid hn A0 hstc (ok := okOf s k) (fin := s.finishing)
      (w := w) (by rw [hprocX, ← hoX]; exact hw)
    rw [hst] at this
    exact ⟨this.1, this.2.2⟩
  have hvlead : v.level = (mem x0).level → v.leaders = (mem x0).leaders :=
    fun h => A0.1.copyLead q v hstc h
  have hloc : ∀ j', j' ≠ q → Function.update loc q s' j' = loc j' :=
    fun j' h => Function.update_of_ne h _ _
  have hcand_ne : ∀ k', k' ≠ k → s'.cand k' = s.cand k' :=
    fun k' h => congrArg ALoc.ca (procReg_locX_ne pp s k k' h .fresh)
  have hcand_k : s'.cand k = (oX pp s k).1.ca := congrArg ALoc.ca (procReg_locX pp s k .fresh)
  -- the N(11)-status of the other processes is unchanged
  have hN11 : ∀ j', j' ≠ q →
      (IsN11At π mem vpc j' ↔ IsN11At π mem (Function.update vpc q (nextVPC j o)) j') := by
    intro j' hj'
    simp only [IsN11At, pendAt_next hj o hq, hj', ne_eq, not_false_eq_true, true_and, false_and,
      or_false]
  have hoN : ¬IsN11At π mem vpc q := not_isN11At_of_noPend (by rw [hq]; intro _ _ h; cases h)
  have hcnt := n11Count_change (π := π) mem mem vpc (Function.update vpc q (nextVPC j o)) q hN11
  rw [if_neg hoN] at hcnt
  have hx0' : π q ⟨j, hj⟩ = x0 := by rw [hx0, hk]
  have hnewN : IsN11At π mem (Function.update vpc q (nextVPC j o)) q ↔
      ∃ w, o = some w ∧ w.level = (mem x0).level + 1 := by
    simp only [IsN11At, pendAt_next hj o hq, ne_eq, not_true_eq_false, false_and, true_and,
      false_or, hx0']
    constructor
    · rintro ⟨x, w, ⟨h1, rfl⟩, h2⟩; exact ⟨w, h1, h2⟩
    · rintro ⟨w, h1, h2⟩; exact ⟨x0, w, ⟨h1, rfl⟩, h2⟩
  have hret : ∀ j' L, Function.update vpc q (nextVPC j o) j' = .pc (.ret L) →
      (∀ x, (mem x).level = pp.U) ∧ L = univ.sup (fun x => (mem x).leaders) := by
    intro j' L h
    by_cases hjq : j' = q
    · rw [hjq] at h; simp only [Function.update_self] at h
      exact absurd h (nextVPC_ne_ret j o L)
    · rw [Function.update_of_ne hjq] at h; exact G.ret j' L h
  by_cases hwin : ∃ w, o = some w ∧ w.level = v.level + 1
  · -- `q` wins the competition at `x0`
    obtain ⟨w, hw, hwl⟩ := hwin
    obtain ⟨hvl, hcase⟩ := hwf w hw
    obtain ⟨-, hca, hlead⟩ : w.level = v.level + 1 ∧ s.cand k = true ∧
        w.leaders = if s.finishing then insert (ids q) v.leaders else v.leaders := by
      rcases hcase with h | h
      · omega
      · exact h
    obtain ⟨hTW, hcand0⟩ := G.g7 q k hca
    have hTW' : 1 ≤ s.toWin := hTW
    have htw' : s'.toWin = s.toWin - 1 :=
      procReg_toWin_win pp s k w (show (oX pp s k).2 = some w by rw [← hoX]; exact hw) hwl
    have hcak : s'.cand k = false := by
      rw [hcand_k]; exact procX_win_ca (show (oX pp s k).2 = some w by rw [← hoX]; exact hw) hwl
    have hNq : IsN11At π mem (Function.update vpc q (nextVPC j o)) q :=
      hnewN.2 ⟨w, hw, by rw [hwl, hvl]⟩
    have hcnt' : n11Count π mem (Function.update vpc q (nextVPC j o)) = n11Count π mem vpc + 1 := by
      rw [if_pos hNq] at hcnt; omega
    have hpend : PendAt π (Function.update vpc q (nextVPC j o)) q x0 w :=
      (pendAt_next hj o hq).2 (Or.inr ⟨rfl, hw, hx0'.symm⟩)
    have hg7 : ∀ k'', s'.cand k'' = false := by
      intro k''
      by_cases h : k'' = k
      · rw [h]; exact hcak
      · rw [hcand_ne k'' h]; exact hcand0 k'' h
    by_cases hf : s.finishing = true
    · have h2 : s.toWin + g.wt q = 1 := G.g2 q hf
      have hwt0 : g.wt q = 0 := by omega
      refine ⟨⟨g.wf, Function.update g.wt q (g.wt q + 1)⟩, hAinv, fun j' => ?_, fun j' h => ?_,
        fun j' h => ?_, G.g3, fun ⟨j', h⟩ => G.g4 ⟨j', ?_⟩, ?_, fun x a ha => ?_, fun j' h => ?_,
        fun j' x w' h1 h2 a ha => ?_, fun j' k' h => ?_, hret⟩
      · by_cases hjq : j' = q
        · rw [hjq]; simp only [Function.update_self]; rw [hme', hme]
        · rw [hloc j' hjq]; exact G.me j'
      · by_cases hjq : j' = q
        · rw [hjq] at h; simp only [Function.update_self] at h; rw [hfin'] at h
          rw [hf] at h; cases h
        · rw [hloc j' hjq] at h ⊢; simp only [Function.update_of_ne hjq]; exact G.g1 j' h
      · by_cases hjq : j' = q
        · rw [hjq]; simp only [Function.update_self]; rw [htw']; omega
        · rw [hloc j' hjq] at h ⊢; simp only [Function.update_of_ne hjq]; exact G.g2 j' h
      · by_cases hjq : j' = q
        · rw [hjq] at h; simp only [Function.update_self] at h; rw [hfin'] at h; rw [hjq]
          exact h
        · rwa [hloc j' hjq] at h
      · have h5 := G.g5
        have hs := Fintype.sum_update_add (fun i => g.wf i + g.wt i) q (g.wf q + g.wt q + 1)
        have : ∑ i, (g.wf i + Function.update g.wt q (g.wt q + 1) i) =
            ∑ i, Function.update (fun i => g.wf i + g.wt i) q (g.wf q + g.wt q + 1) i := by
          apply Finset.sum_congr rfl; intro i _
          by_cases hi : i = q
          · subst hi; simp; omega
          · simp [Function.update_of_ne hi]
        simp only at hs ⊢
        rw [this, hcnt']; omega
      · obtain ⟨j', h1, h2⟩ := G.g6a x a ha
        refine ⟨j', h1, ?_⟩
        have hjq : j' ≠ q := by rintro rfl; omega
        simp only [Function.update_of_ne hjq]; exact h2
      · by_cases hjq : j' = q
        · subst hjq
          refine Or.inr ⟨x0, w, hpend, by omega, ?_⟩
          rw [hlead, if_pos hf]; exact Finset.mem_insert_self _ _
        · simp only [Function.update_of_ne hjq] at h
          rcases G.g6b j' h with h' | ⟨x, w', h1, h2, h3⟩
          · exact Or.inl h'
          · exact Or.inr ⟨x, w', (pendAt_next hj o hq).2 (Or.inl ⟨hjq, h1⟩), h2, h3⟩
      · rcases (pendAt_next hj o hq).1 h1 with ⟨hjq, h1⟩ | ⟨hjq, hw', hx⟩
        · rcases G.g6c j' x w' h1 h2 a ha with h | ⟨h3, h4⟩
          · exact Or.inl h
          · exact Or.inr ⟨h3, by simp only [Function.update_of_ne hjq]; exact h4⟩
        · obtain rfl : w = w' := Option.some.inj (hw.symm.trans hw')
          rw [hx, hx0', hjq]
          rw [hlead, if_pos hf] at ha
          rcases Finset.mem_insert.1 ha with h | h
          · exact Or.inr ⟨h, by simp [hwt0]⟩
          · exact Or.inl (by rw [← hvlead hvl]; exact h)
      · by_cases hjq : j' = q
        · rw [hjq] at h; simp only [Function.update_self] at h; rw [hg7] at h; cases h
        · rw [hloc j' hjq] at h ⊢; exact G.g7 j' k' h
    · have hf' : s.finishing = false := by simpa using hf
      have h1 : s.toWin + g.wf q = pp.W ∧ g.wt q = 0 := G.g1 q hf'
      refine ⟨⟨Function.update g.wf q (g.wf q + 1), g.wt⟩, hAinv, fun j' => ?_, fun j' h => ?_,
        fun j' h => ?_, fun j' => ?_, fun ⟨j', h⟩ => ?_, ?_, G.g6a, fun j' h => ?_,
        fun j' x w' h1 h2 a ha => ?_, fun j' k' h => ?_, hret⟩
      · by_cases hjq : j' = q
        · rw [hjq]; simp only [Function.update_self]; rw [hme', hme]
        · rw [hloc j' hjq]; exact G.me j'
      · by_cases hjq : j' = q
        · rw [hjq]; simp only [Function.update_self]; rw [htw']; constructor <;> omega
        · rw [hloc j' hjq] at h ⊢; simp only [Function.update_of_ne hjq]; exact G.g1 j' h
      · by_cases hjq : j' = q
        · rw [hjq] at h; simp only [Function.update_self] at h; rw [hfin', hf'] at h; cases h
        · rw [hloc j' hjq] at h ⊢; exact G.g2 j' h
      · by_cases hjq : j' = q
        · rw [hjq]; simp only [Function.update_self]; have := G.g3 q; omega
        · simp only [Function.update_of_ne hjq]; exact G.g3 j'
      · exfalso
        have h' : (loc j').finishing = true := by
          by_cases hjq : j' = q
          · rw [hjq] at h; simp only [Function.update_self] at h; rw [hfin', hf'] at h; cases h
          · rwa [hloc j' hjq] at h
        have := all_eq_of_sum hn g.wf G.g3 (G.g4 ⟨j', h'⟩) q
        omega
      · have h5 := G.g5
        have hs := Fintype.sum_update_add (fun i => g.wf i + g.wt i) q (g.wf q + g.wt q + 1)
        have : ∑ i, (Function.update g.wf q (g.wf q + 1) i + g.wt i) =
            ∑ i, Function.update (fun i => g.wf i + g.wt i) q (g.wf q + g.wt q + 1) i := by
          apply Finset.sum_congr rfl; intro i _
          by_cases hi : i = q
          · subst hi; simp; omega
          · simp [Function.update_of_ne hi]
        simp only at hs ⊢
        rw [this, hcnt']; omega
      · by_cases hjq : j' = q
        · rw [hjq] at h; have := h1.2; simp only at h; omega
        · rcases G.g6b j' h with h' | ⟨x, w', h1, h2, h3⟩
          · exact Or.inl h'
          · exact Or.inr ⟨x, w', (pendAt_next hj o hq).2 (Or.inl ⟨hjq, h1⟩), h2, h3⟩
      · rcases (pendAt_next hj o hq).1 h1 with ⟨hjq, h1⟩ | ⟨hjq, hw', hx⟩
        · exact G.g6c j' x w' h1 h2 a ha
        · obtain rfl : w = w' := Option.some.inj (hw.symm.trans hw')
          rw [hx, hx0']
          rw [hlead, if_neg hf] at ha
          exact Or.inl (by rw [← hvlead hvl]; exact ha)
      · by_cases hjq : j' = q
        · rw [hjq] at h; simp only [Function.update_self] at h; rw [hg7] at h; cases h
        · rw [hloc j' hjq] at h ⊢; exact G.g7 j' k' h
  · -- no win: the ghost is unchanged
    have htw' : s'.toWin = s.toWin := procReg_toWin_nowin pp s k (fun w hw hl =>
      hwin ⟨w, by rw [hoX]; exact hw, hl⟩)
    have hcnt' : n11Count π mem (Function.update vpc q (nextVPC j o)) = n11Count π mem vpc := by
      rw [if_neg] at hcnt
      · omega
      · rw [hnewN]; rintro ⟨w, hw, hl⟩
        obtain ⟨hvl, -⟩ := hwf w hw
        exact hwin ⟨w, hw, by omega⟩
    refine ⟨g, hAinv, fun j' => ?_, fun j' h => ?_, fun j' h => ?_, G.g3, fun ⟨j', h⟩ => G.g4 ⟨j', ?_⟩,
      by rw [hcnt']; exact G.g5, G.g6a, fun j' h => ?_, fun j' x w' h1 h2 a ha => ?_,
      fun j' k' h => ?_, hret⟩
    · by_cases hjq : j' = q
      · rw [hjq]; simp only [Function.update_self]; rw [hme', hme]
      · rw [hloc j' hjq]; exact G.me j'
    · by_cases hjq : j' = q
      · subst hjq; simp only [Function.update_self] at h ⊢; rw [htw']; rw [hfin'] at h
        exact G.g1 j' h
      · rw [hloc j' hjq] at h ⊢; exact G.g1 j' h
    · by_cases hjq : j' = q
      · subst hjq; simp only [Function.update_self] at h ⊢; rw [htw']; rw [hfin'] at h
        exact G.g2 j' h
      · rw [hloc j' hjq] at h ⊢; exact G.g2 j' h
    · by_cases hjq : j' = q
      · rw [hjq] at h; simp only [Function.update_self] at h; rw [hfin'] at h; rw [hjq]
        exact h
      · rwa [hloc j' hjq] at h
    · rcases G.g6b j' h with h' | ⟨x, w', h1, h2, h3⟩
      · exact Or.inl h'
      · have hjq : j' ≠ q := by
          rintro rfl; obtain ⟨k', h1, -⟩ := h1; rw [hq] at h1; cases h1
        exact Or.inr ⟨x, w', (pendAt_next hj o hq).2 (Or.inl ⟨hjq, h1⟩), h2, h3⟩
    · rcases (pendAt_next hj o hq).1 h1 with ⟨hjq, h1⟩ | ⟨hjq, hw', hx⟩
      · exact G.g6c j' x w' h1 h2 a ha
      · exfalso
        obtain ⟨hvl, -⟩ := hwf w' hw'
        rw [hx, hx0'] at h2
        exact hwin ⟨w', hw', by omega⟩
    · by_cases hjq : j' = q
      · rw [hjq] at h ⊢; simp only [Function.update_self] at h ⊢; rw [htw']
        by_cases hk' : k' = k
        · rw [hk'] at h ⊢
          rw [hcand_k] at h
          rcases procX_ca h with h'' | h''
          · obtain ⟨h3, h4⟩ := G.g7 q k h''
            exact ⟨h3, fun k'' hk'' => by rw [hcand_ne k'' hk'']; exact h4 k'' hk''⟩
          · simp only [okOf, decide_eq_true_eq] at h''
            refine ⟨h''.2, fun k'' hk'' => ?_⟩
            rw [hcand_ne k'' hk'']; exact h''.1 k'' hk''
        · rw [hcand_ne k' hk'] at h
          obtain ⟨h3, h4⟩ := G.g7 q k' h
          refine ⟨h3, fun k'' hk'' => ?_⟩
          by_cases hkk : k'' = k
          · rw [hkk, hcand_k]
            cases hc : (oX pp s k).1.ca
            · rfl
            · exfalso
              rcases procX_ca hc with h'' | h''
              · have h5 : s.cand k = false := h4 k (hkk ▸ hk'')
                simp only [locX] at h''; rw [h5] at h''; cases h''
              · simp only [okOf, decide_eq_true_eq] at h''
                rw [h''.1 k' hk'] at h; cases h
          · rw [hcand_ne k'' hkk]; exact h4 k'' hk''
      · rw [hloc j' hjq] at h ⊢; exact G.g7 j' k' h

end BezoutElection.Alg2

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P] {m : ℕ}
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id}

/-- The whole for loop from register `j` on (until the next write or the next collect). -/
theorem ginv_loopFrom (hid : Function.Injective ids) (hn : Fintype.card P = pp.n)
    {mem : Fin m → Reg Id} {loc : P → St Id m} {vpc : P → VPC Id} {g : Ghost P}
    (G : GInv π pp ids mem loc vpc g) {q : P} {j : ℕ} (hq : vpc q = .loop j) :
    ∃ g', GInv π pp ids mem (Function.update loc q (loopFrom pp (loc q) j))
      (Function.update vpc q (.pc (loopFrom pp (loc q) j).pc)) g' := by
  rw [loopFrom]
  by_cases h : j < m
  · rw [dif_pos h]
    obtain ⟨g1, G1⟩ := ginv_proc hid hn G h hq
    rcases e : procReg pp (loc q) ⟨j, h⟩ with ⟨s', _ | w⟩
    · simp only
      rw [e] at G1
      obtain ⟨g2, G2⟩ := ginv_loopFrom hid hn G1 (q := q) (j := j + 1) (by simp [nextVPC])
      refine ⟨g2, ?_⟩
      simpa [Function.update_idem] using G2
    · simp only
      rw [e] at G1
      refine ⟨g1, ginv_congr G1 (fun j' => ?_)⟩
      by_cases hj' : j' = q
      · subst hj'; exact ⟨.write j w, by simp⟩
      · exact ⟨(loc j').pc, by simp [Function.update_of_ne hj']⟩
  · rw [dif_neg h]
    exact ⟨g, ginv_loopEnd G (by omega) hq⟩
termination_by m - j

end BezoutElection.Alg2
