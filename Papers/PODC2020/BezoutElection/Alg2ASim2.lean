import Papers.PODC2020.BezoutElection.Alg2ASim

/-!
# Algorithm 2: every concrete step acts on a register by one abstract transition
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P] [Fintype P]
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id} {R : Type} [Inhabited R]
  {out : Id → Finset Id → R}

lemma absAt_mk (mem mem' : Fin m → Reg Id) (loc : P → St Id m) (q : P) (s' : St Id m)
    (x : Fin m) :
    absAt π mem' (Function.update loc q s') (vpcOf (Function.update loc q s')) x =
      ⟨mem' x, Function.update (absAt π mem loc (vpcOf loc) x).loc q
        (locX s' ((π q).symm x) (vstatus (.pc s'.pc) s' ((π q).symm x)))⟩ := by
  rw [absAt_step]; rfl

lemma absAt_none (mem : Fin m → Reg Id) (loc : P → St Id m) (q : P) (s' : St Id m)
    (x : Fin m) (h : locX s' ((π q).symm x) (vstatus (.pc s'.pc) s' ((π q).symm x)) =
      locX (loc q) ((π q).symm x) (vstatus (.pc (loc q).pc) (loc q) ((π q).symm x))) :
    absAt π mem (Function.update loc q s') (vpcOf (Function.update loc q s')) x =
      absAt π mem loc (vpcOf loc) x := by
  rw [absAt_mk mem mem, h]
  exact AState.upd_self (absAt π mem loc (vpcOf loc) x) q

/-- The abstract transition of one concrete step at the register `x`. -/
def SimOK (pp : Params) (ids : P → Id) (π : P → Equiv.Perm (Fin m)) (A A' : AState Id P)
    (q : P) (s s' : St Id m) (x : Fin m) (rd : Prop) : Prop :=
  ∃ tr, ATrRel pp.n pp.U ids A q tr A' ∧ (rd → tr = .read ∨ ∃ ok fin, tr = .readProc ok fin) ∧
    (∀ ok fin, (tr = .proc ok fin ∨ tr = .readProc ok fin) → ∃ s_mid : St Id m,
      ok = okOf s_mid ((π q).symm x) ∧ fin = s_mid.finishing ∧ MidOK s s' s_mid)

lemma simOK_none {A : AState Id P} {q : P} {s s' : St Id m} {x : Fin m} {rd : Prop} (hrd : ¬rd) :
    SimOK pp ids π A A q s s' x rd :=
  ⟨.none, rfl, fun h => absurd h hrd, fun ok fin h => by rcases h with h | h <;> cases h⟩


section Cases

variable (mem : Fin m → Reg Id) (loc : P → St Id m) (q : P)

/-- A read of the collect, not the last one. -/
lemma sim_collect_mid {j : ℕ} (hj : j < m) (hpc : (loc q).pc = .collect j) (x : Fin m) :
    SimOK pp ids π (absAt π mem loc (vpcOf loc) x)
      (absAt π mem (Function.update loc q
        { (loc q).setReg ⟨j, hj⟩ (mem (π q ⟨j, hj⟩)) with pc := .collect (j + 1) })
        (vpcOf (Function.update loc q
          { (loc q).setReg ⟨j, hj⟩ (mem (π q ⟨j, hj⟩)) with pc := .collect (j + 1) })) x)
      q (loc q) { (loc q).setReg ⟨j, hj⟩ (mem (π q ⟨j, hj⟩)) with pc := .collect (j + 1) } x
      (π q ⟨j, hj⟩ = x) := by
  by_cases hx : π q ⟨j, hj⟩ = x
  · subst hx
    refine ⟨.read, ⟨?_, ?_⟩, fun _ => Or.inl rfl, fun ok fin h => by rcases h with h | h <;> cases h⟩
    · rw [absAt_loc, Equiv.symm_apply_apply]; simp [vpcOf, hpc, locX, vstatus]
    · rw [absAt_mk mem mem]
      simp only [AState.setSt, AState.upd, absAt_reg, Equiv.symm_apply_apply]
      congr 2
      rw [absAt_loc, Equiv.symm_apply_apply]
      simp [vpcOf, hpc, locX, vstatus, St.setReg]
  · rw [absAt_none mem loc q _ x]
    · exact simOK_none hx
    · have hk : (π q).symm x ≠ ⟨j, hj⟩ := fun h => hx (by rw [← h]; simp)
      have hk' : ((π q).symm x).val ≠ j := fun h => hk (Fin.ext h)
      simp only [hpc, locX, vstatus, St.setReg, Function.update_of_ne hk]
      split_ifs <;> first | rfl | omega

/-- The last read of the collect, followed by the return. -/
lemma sim_collect_ret {j : ℕ} (hj : j < m) (hpc : (loc q).pc = .collect j) (hj1 : j + 1 = m)
    (L : Finset Id) (x : Fin m) :
    SimOK pp ids π (absAt π mem loc (vpcOf loc) x)
      (absAt π mem (Function.update loc q
        { (loc q).setReg ⟨j, hj⟩ (mem (π q ⟨j, hj⟩)) with pc := .ret L })
        (vpcOf (Function.update loc q
          { (loc q).setReg ⟨j, hj⟩ (mem (π q ⟨j, hj⟩)) with pc := .ret L })) x)
      q (loc q) { (loc q).setReg ⟨j, hj⟩ (mem (π q ⟨j, hj⟩)) with pc := .ret L } x
      (π q ⟨j, hj⟩ = x) := by
  by_cases hx : π q ⟨j, hj⟩ = x
  · subst hx
    refine ⟨.read, ⟨?_, ?_⟩, fun _ => Or.inl rfl, fun ok fin h => by rcases h with h | h <;> cases h⟩
    · rw [absAt_loc, Equiv.symm_apply_apply]; simp [vpcOf, hpc, locX, vstatus]
    · rw [absAt_mk mem mem]
      simp only [AState.setSt, AState.upd, absAt_reg, Equiv.symm_apply_apply]
      congr 2
      rw [absAt_loc, Equiv.symm_apply_apply]
      simp [vpcOf, hpc, locX, vstatus, St.setReg]
  · rw [absAt_none mem loc q _ x]
    · exact simOK_none hx
    · have hk : (π q).symm x ≠ ⟨j, hj⟩ := fun h => hx (by rw [← h]; simp)
      have hk' : ((π q).symm x).val ≠ j := fun h => hk (Fin.ext h)
      have hk'' := ((π q).symm x).isLt
      simp only [hpc, locX, vstatus, St.setReg, Function.update_of_ne hk]
      split_ifs <;> first | rfl | omega

/-- The intermediate state of the for loop after the collect. -/
lemma midOK_of {s s0 s_f s_mid : St Id m} (hcand : s0.cand = s.cand)
    (hfin : (s0.toWin = s.toWin ∧ s0.finishing = s.finishing) ∨
      (s.finishing = false ∧ s0.finishing = true))
    (hff : s_f.finishing = s0.finishing)
    (hc : ∀ k', s_mid.cand k' = s0.cand k' ∨ s_mid.cand k' = s_f.cand k')
    (htw : s_mid.toWin = s0.toWin) (hf : s_mid.finishing = s0.finishing) :
    MidOK s s_f s_mid := by
  refine ⟨fun k' => by rw [← hcand]; exact hc k', ?_⟩
  rcases hfin with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨htw.trans h1, hf.trans h2⟩
  · exact Or.inr ⟨h1, hf.trans h2, hff.trans h2⟩

/-- The last read of the collect, followed by the for loop. -/
lemma sim_collect_loop {j : ℕ} (hj : j < m) (hpc : (loc q).pc = .collect j) (hj1 : j + 1 = m)
    (s0 : St Id m) (hs : ∀ k st, locX s0 k st = locX (loc q) k st)
    (hregs : s0.regs = Function.update (loc q).regs ⟨j, hj⟩ (mem (π q ⟨j, hj⟩)))
    (hme : s0.me = ids q) (hcand : s0.cand = (loc q).cand)
    (hfin : (s0.toWin = (loc q).toWin ∧ s0.finishing = (loc q).finishing) ∨
      ((loc q).finishing = false ∧ s0.finishing = true)) (x : Fin m) :
    SimOK pp ids π (absAt π mem loc (vpcOf loc) x)
      (absAt π mem (Function.update loc q (loopFrom pp s0 0))
        (vpcOf (Function.update loc q (loopFrom pp s0 0))) x)
      q (loc q) (loopFrom pp s0 0) x (π q ⟨j, hj⟩ = x) := by
  obtain ⟨r1, r2, r3, -, r5, -⟩ := loopFrom_res pp s0 0
  set s_f := loopFrom pp s0 0 with hs_f
  have hlt := loop_tr (ids := ids) q s0 s_f ((π q).symm x) (r5 _ (Nat.zero_le _)) r1 hme
  have hA : (absAt π mem loc (vpcOf loc) x).loc q =
      locX (loc q) ((π q).symm x) (vstatus (.pc (.collect j)) (loc q) ((π q).symm x)) := by
    rw [absAt_loc]; simp [vpcOf, hpc]
  by_cases hx : π q ⟨j, hj⟩ = x
  · subst hx
    simp only [Equiv.symm_apply_apply] at hlt hA
    have hreg : s0.regs ⟨j, hj⟩ = mem (π q ⟨j, hj⟩) := by rw [hregs]; simp
    have hA' : (absAt π mem loc (vpcOf loc) (π q ⟨j, hj⟩)).loc q = locX (loc q) ⟨j, hj⟩ .fresh := by
      rw [hA]; simp [vstatus]
    rcases hlt with h | ⟨s_mid, h, hc, htw, hf⟩
    · refine ⟨.read, ⟨by rw [hA']; rfl, ?_⟩, fun _ => Or.inl rfl,
        fun ok fin h => by rcases h with h | h <;> cases h⟩
      rw [absAt_mk mem mem]
      simp only [AState.setSt, AState.upd, absAt_reg, Equiv.symm_apply_apply]
      rw [h, hs, hreg, hA']; rfl
    · refine ⟨.readProc (okOf s_mid ⟨j, hj⟩) s_mid.finishing, ⟨by rw [hA']; rfl, ?_⟩,
        fun _ => Or.inr ⟨_, _, rfl⟩, fun ok fin h => ?_⟩
      · rw [absAt_mk mem mem]
        simp only [AState.upd, absAt_reg, Equiv.symm_apply_apply]
        rw [h, hs, hreg, hA', procL_locX, procL_locX]
      · rcases h with h | h
        · cases h
        · simp only [ATr.readProc.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨s_mid, by simp, rfl, midOK_of hcand hfin r3 hc htw hf⟩
  · have hk : (π q).symm x ≠ ⟨j, hj⟩ := fun h => hx (by rw [← h]; simp)
    have hk' : ((π q).symm x).val < j := by
      have : ((π q).symm x).val ≠ j := fun h => hk (Fin.ext h)
      have := ((π q).symm x).isLt
      omega
    have hreg : s0.regs ((π q).symm x) = (loc q).regs ((π q).symm x) := by
      rw [hregs, Function.update_of_ne hk]
    have hA' : (absAt π mem loc (vpcOf loc) x).loc q =
        locX (loc q) ((π q).symm x) (.copy ((loc q).regs ((π q).symm x))) := by
      rw [hA]; simp only [vstatus]; rw [if_neg (by omega)]
    rcases hlt with h | ⟨s_mid, h, hc, htw, hf⟩
    · rw [absAt_none mem loc q _ x]
      · exact simOK_none hx
      · rw [h, hs, hreg, ← hA', absAt_loc]; simp [vpcOf]
    · refine ⟨.proc (okOf s_mid ((π q).symm x)) s_mid.finishing,
        ⟨(loc q).regs ((π q).symm x), by rw [hA']; rfl, ?_⟩, fun h => absurd h hx, fun ok fin h => ?_⟩
      · rw [absAt_mk mem mem]
        simp only [AState.upd, absAt_reg]
        rw [h, hs, hreg, hA']
      · rcases h with h | h
        · simp only [ATr.proc.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨s_mid, rfl, rfl, midOK_of hcand hfin r3 hc htw hf⟩
        · cases h

lemma absAt_mem_congr {mem' : Fin m → Reg Id} {loc' : P → St Id m} {vpc : P → VPC Id} {x : Fin m}
    (h : mem' x = mem x) : absAt π mem' loc' vpc x = absAt π mem loc' vpc x := by
  simp [absAt, h]

/-- A write, followed by the rest of the for loop. -/
lemma sim_write {j : ℕ} (hj : j < m) {w : Reg Id} (hpc : (loc q).pc = .write j w)
    (hme : (loc q).me = ids q) (x : Fin m) :
    SimOK pp ids π (absAt π mem loc (vpcOf loc) x)
      (absAt π (Function.update mem (π q ⟨j, hj⟩) w)
        (Function.update loc q (loopFrom pp (loc q) (j + 1)))
        (vpcOf (Function.update loc q (loopFrom pp (loc q) (j + 1)))) x)
      q (loc q) (loopFrom pp (loc q) (j + 1)) x False := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := loopFrom_res pp (loc q) (j + 1)
  set s_f := loopFrom pp (loc q) (j + 1) with hs_f
  have hA : (absAt π mem loc (vpcOf loc) x).loc q =
      locX (loc q) ((π q).symm x) (vstatus (.pc (.write j w)) (loc q) ((π q).symm x)) := by
    rw [absAt_loc]; simp [vpcOf, hpc]
  have hfresh : ∀ k : Fin m, k.val ≤ j → vstatus (.pc s_f.pc) s_f k = .fresh := by
    intro k hk
    rcases r6 with h | ⟨j', w', h1, -, h3⟩
    · rw [h]; simp [vstatus]
    · rw [h3]; simp only [vstatus]
      rw [if_neg (by omega), if_neg (by omega)]
  by_cases hx : π q ⟨j, hj⟩ = x
  · subst hx
    simp only [Equiv.symm_apply_apply] at hA
    refine ⟨.write, ⟨w, by rw [hA]; simp [locX, vstatus], ?_⟩, fun h => h.elim,
      fun ok fin h => by rcases h with h | h <;> cases h⟩
    rw [absAt_mk mem]
    simp only [AState.wr, AState.setSt, AState.upd, Function.update_self, Equiv.symm_apply_apply]
    rw [hfresh _ le_rfl, r4 _ (by simp), hA]
    rfl
  · rw [absAt_mem_congr (mem := mem) (Function.update_of_ne (Ne.symm hx) _ _)]
    have hk : (π q).symm x ≠ ⟨j, hj⟩ := fun h => hx (by rw [← h]; simp)
    have hk' : ((π q).symm x).val ≠ j := fun h => hk (Fin.ext h)
    by_cases hlt : ((π q).symm x).val < j
    · rw [absAt_none mem loc q _ x]
      · exact simOK_none id
      · rw [hfresh _ (by omega), r4 _ (by omega), hpc]
        simp only [vstatus]; rw [if_neg (by omega), if_neg (Ne.symm hk')]
    · have hA' : (absAt π mem loc (vpcOf loc) x).loc q =
          locX (loc q) ((π q).symm x) (.copy ((loc q).regs ((π q).symm x))) := by
        rw [hA]; simp only [vstatus]; rw [if_pos (by omega)]
      rcases loop_tr (ids := ids) q (loc q) s_f ((π q).symm x) (r5 _ (by omega)) r1 hme with
        h | ⟨s_mid, h, hc, htw, hf⟩
      · rw [absAt_none mem loc q _ x]
        · exact simOK_none id
        · rw [h, ← hA', absAt_loc]; simp [vpcOf]
      · refine ⟨.proc (okOf s_mid ((π q).symm x)) s_mid.finishing,
          ⟨(loc q).regs ((π q).symm x), by rw [hA']; rfl, ?_⟩, fun h => h.elim, fun ok fin h => ?_⟩
        · rw [absAt_mk mem mem]
          simp only [AState.upd, absAt_reg]
          rw [h, hA']
        · rcases h with h | h
          · simp only [ATr.proc.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨s_mid, rfl, rfl, hc, Or.inl ⟨htw, hf⟩⟩
          · cases h

end Cases

lemma simOK_mono {A A' : AState Id P} {q : P} {s s' : St Id m} {x : Fin m} {rd rd' : Prop}
    (h : SimOK pp ids π A A' q s s' x rd) (hrd : rd' → rd) : SimOK pp ids π A A' q s s' x rd' := by
  obtain ⟨tr, h1, h2, h3⟩ := h
  exact ⟨tr, h1, fun h => h2 (hrd h), h3⟩

/-- **Simulation**: every step of Algorithm 2 acts on every register by one abstract
transition; a read of the collect at the register is a read of the abstraction. -/
theorem sim_step {α : List (Label P (elecObj R))} {C C' : Cfg2 Id m R P}
    {ℓ : Label P (elecObj R)} (hI : RInv π pp ids out α C)
    (h : ((alg2 Id m pp out).impl ids π).step C ℓ = some C') (x : Fin m) :
    SimOK pp ids π (absAt π (C.mem ()) C.loc (vpcOf C.loc) x)
      (absAt π (C'.mem ()) C'.loc (vpcOf C'.loc) x) ℓ.proc (C.loc ℓ.proc) (C'.loc ℓ.proc) x
      (∃ q, ∃ k : Fin m, ℓ = .tau q ∧ (C.loc q).pc = .collect k.val ∧ π q k = x) := by
  obtain ⟨⟨g, G⟩, hpcok, hidle, -, -⟩ := hI
  cases ℓ with
  | inv q o =>
    obtain ⟨hp, rfl⟩ := SymAlg.impl_step_inv_cases h
    dsimp only [Label.proc]
    rw [absAt_none (C.mem ()) C.loc q _ x]
    · exact simOK_none (by rintro ⟨_, _, h, -⟩; cases h)
    · rcases hpc : (C.loc q).pc with _ | j | ⟨j, w⟩ | L | _ <;>
        simp [alg2, hpc, locX, vstatus]
  | ret q r =>
    obtain ⟨hp, s, hact, rfl⟩ := SymAlg.impl_step_ret_cases h
    dsimp only [Label.proc]
    rw [absAt_none (C.mem ()) C.loc q _ x]
    · exact simOK_none (by rintro ⟨_, _, h, -⟩; cases h)
    · rcases hpc : (C.loc q).pc with _ | j | ⟨j, w⟩ | L | _
      · exact absurd (hidle q hpc) hp
      · rw [act_collect _ hpc ((hpcok q).1 j hpc)] at hact; cases hact
      · rw [act_write _ hpc ((hpcok q).2 j w hpc)] at hact; cases hact
      · rw [act_ret _ hpc] at hact
        simp only [SymAction.ret.injEq] at hact
        obtain ⟨-, rfl⟩ := hact
        simp [vstatus, locX]
      · rw [act_fin _ hpc] at hact
        simp only [SymAction.ret.injEq] at hact
        obtain ⟨-, rfl⟩ := hact
        rw [hpc]
  | tau q =>
    obtain ⟨hp, ⟨x0, f, k, hact, rfl⟩ | ⟨k, hact, -⟩⟩ := SymAlg.impl_step_tau_cases h
    swap
    · exfalso
      simp only [alg2] at hact
      split at hact <;> (try split at hact) <;> simp at hact
    dsimp only [Label.proc]
    rcases hpc : (C.loc q).pc with _ | j | ⟨j, w⟩ | L | _
    · rw [act_idle _ hpc] at hact; cases hact
    · have hj := (hpcok q).1 j hpc
      rw [act_collect _ hpc hj] at hact
      simp only [SymAction.rmw.injEq] at hact
      obtain ⟨rfl, rfl, rfl⟩ := hact
      simp only [Function.update_eq_self, Function.update_self]
      have hrd : (∃ q', ∃ k : Fin m, Label.tau (A := elecObj R) q = Label.tau q' ∧
          (C.loc q').pc = .collect k.val ∧ π q' k = x) → π q ⟨j, hj⟩ = x := by
        rintro ⟨q', k, h1, h2, h3⟩
        cases h1
        rw [hpc] at h2; cases h2; exact h3
      by_cases hj1 : j + 1 < m
      · simp only [if_pos hj1]
        exact simOK_mono (sim_collect_mid (C.mem ()) C.loc q hj hpc x) hrd
      · simp only [if_neg hj1]
        have hj1' : j + 1 = m := by omega
        unfold afterCollect
        dsimp only
        by_cases hsum : ∑ y, (((C.loc q).setReg ⟨j, hj⟩ (C.mem () (π q ⟨j, hj⟩))).regs y).level =
            pp.U * m
        · rw [if_pos hsum]
          exact simOK_mono (sim_collect_ret (C.mem ()) C.loc q hj hpc hj1' _ x) hrd
        · rw [if_neg hsum]
          refine simOK_mono (sim_collect_loop (C.mem ()) C.loc q hj hpc hj1' _ ?_ ?_ ?_ ?_ ?_ x) hrd
          · intro k st; split_ifs <;> rfl
          · split_ifs <;> rfl
          · split_ifs <;> exact G.me q
          · split_ifs <;> rfl
          · split_ifs with hc
            · exact Or.inr ⟨hc.2, rfl⟩
            · exact Or.inl ⟨rfl, rfl⟩
    · have hj := (hpcok q).2 j w hpc
      rw [act_write _ hpc hj] at hact
      simp only [SymAction.rmw.injEq] at hact
      obtain ⟨rfl, rfl, rfl⟩ := hact
      simp only [Function.update_self]
      refine simOK_mono (sim_write (C.mem ()) C.loc q hj hpc (G.me q) x) ?_
      rintro ⟨q', k, h1, h2, -⟩
      cases h1
      rw [hpc] at h2; cases h2
    · rw [act_ret _ hpc] at hact; cases hact
    · rw [act_fin _ hpc] at hact; cases hact

end BezoutElection.Alg2
