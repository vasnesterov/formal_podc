import Papers.PODC2019.CryptoConsensusNumber.Fig3LStep2

/-!
# Figure 3: the linearization invariant is preserved (updates, line 11)

A successful transfer is linearized at the first `AS.update` that contains it (possibly by a
helping process); a process leaving the loop returns the result recorded in its `hist`.
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig3

open Cslib.SharedMemory

set_option allowUnsafeReducibility true in
attribute [local reducible] atSpec snapObj kConsObj

variable {n : ℕ} {Acct : Type} [DecidableEq Acct] {μ : Acct → Finset (Fin n)} {q₀ : Acct → ℕ}
  {k : ℕ} {α : Hst μ q₀} {C : Cfg μ q₀ k} {K : Set (Tx n Acct)} {gid : Tx n Acct → ℕ}
  {L : LinL n Acct} {q : Fin n}

/-- The configuration after an update step. -/
abbrev updCfg (C : Cfg μ q₀ k) (q : Fin n) (tx : Tx n Acct) (c : Finset (Tx n Acct))
    (d : Option (Tx n Acct × Bool)) : Cfg μ q₀ k :=
  { C with
    mem := Function.update C.mem (.inl ()) (Function.update (AS C.mem) q (C.loc q).hist)
    loc := Function.update C.loc q (updLoc (C.loc q) tx c d) }

lemma bal_push {Q : Acct → ℕ} {T : Finset (Tx n Acct)} {t : Tx n Acct} (ht : t ∉ T)
    (hx : t.x ≤ Q t.a) (hb : ∀ c, Q c + outSum c T = q₀ c + inSum c T) (c : Acct) :
    moveFunds Q t.a t.b t.x c + outSum c (insert t T) = q₀ c + inSum c (insert t T) := by
  rw [moveFunds_apply, inSum_insert ht, outSum_insert ht]
  have h := hb c
  have e1 : (if c = t.a then t.x else 0) = (if t.a = c then t.x else 0) := by simp [eq_comm]
  have e2 : (if c = t.b then t.x else 0) = (if t.b = c then t.x else 0) := by simp [eq_comm]
  rw [e1, e2]
  split_ifs with h1 h2 h2 <;> (try subst h1) <;> omega

/-- The response of a process leaving the loop is the decided result of its transfer. -/
lemma ret_after_loop {C' : Cfg μ q₀ k} (hM' : MInv μ C' K) {L' : LinL n Acct}
    (hS : ∀ t ∈ K, t ∈ U C'.mem → lrs (μ := μ) (q₀ := q₀) L' (t.p, gid t) = some (.inl true))
    (hF : ∀ t ∈ K, ∀ r, Dec C'.mem t.a r = some (t, false) →
      lrs (μ := μ) (q₀ := q₀) L' (t.p, gid t) = some (.inl false))
    {tx : Tx n Acct} (htx : tx ∈ K) (hcom : tx ∈ (C'.loc tx.p).com tx.a)
    (hhist : (C'.loc tx.p).hist = AS C'.mem tx.p) :
    lrs (μ := μ) (q₀ := q₀) L' (tx.p, gid tx) =
      some (.inl (decide ((tx, true) ∈ (C'.loc tx.p).hist))) := by
  obtain ⟨r, hr, b, hb⟩ := ((hM'.proc tx.p).com tx.a tx).1 hcom
  obtain ⟨d, hd, hdm⟩ := (hM'.proc tx.p).asAll tx.a r hr
  rw [hb] at hd; cases hd
  cases b with
  | true =>
    rw [hS tx htx (mem_U.2 ⟨tx.p, hdm⟩), hhist]
    simp [hdm]
  | false =>
    rw [hF tx htx r hb]
    have : (tx, true) ∉ (C'.loc tx.p).hist := by
      rw [hhist]; intro hm
      obtain ⟨r', hr'⟩ := hM'.dec_of_AS hm
      have := hM'.dec_res hb hr'
      cases this
    simp [this]

lemma LInv.step_upd (hL : LInv μ q₀ α C K gid L) (hM : MInv μ C K) {tx : Tx n Acct}
    {c : Finset (Tx n Acct)} {d : Option (Tx n Acct × Bool)}
    (hM' : MInv μ (updCfg C q tx c d) K) (hpc : (C.loc q).pc = .upd tx c d) :
    ∃ L', LInv μ q₀ (α ++ [.tau q]) (updCfg C q tx c d) K gid L' := by
  have hp := hM.proc q
  obtain ⟨htxp, htxK, htxr⟩ := hp.txP tx (by simp [hpc, PC.tx?])
  obtain ⟨hd, hds⟩ := hp.upd tx c d hpc
  obtain ⟨⟨t, b⟩, rfl⟩ := Option.isSome_iff_exists.1 hds
  set a := tx.a with ha
  set ρ := (C.loc q).rnd a with hρ
  obtain ⟨htK, hta⟩ := hM.decK a ρ t b hd.symm
  have hhist : (C.loc q).hist = AS C.mem q ∪ {(t, b)} := by rw [hp.hist, hpc]; simp [PC.updDec]
  set C' := updCfg C q tx c (some (t, b)) with hC'
  have hAS' : AS C'.mem = Function.update (AS C.mem) q (AS C.mem q ∪ {(t, b)}) := by
    simp only [hC', updCfg, AS_update_AS, hhist]
  have hU' : U C'.mem = if b = true then insert t (U C.mem) else U C.mem := by
    simp only [U, hAS']; exact succ_update_union _ _ _
  have hDec' : ∀ a' r, Dec C'.mem a' r = Dec C.mem a' r := fun a' r => Dec_update_AS _ _ _
  have hloc' : ∀ q', q' ≠ q → C'.loc q' = C.loc q' := by
    intro q' hq'; simp only [hC', updCfg, Function.update_of_ne hq']
  have hα : ∀ x, opOf (α ++ [.tau q]) x = opOf α x := opOf_append_noinv (by simp)
  have hPrec : ∀ q' tx' c' t' res', (C.loc q').pc = .prop tx' c' (t', res') →
      Invoked α (t'.p, gid t') :=
    fun q' tx' c' t' res' h => invoked_of_opOf (hL.opK t' (hM.prop_K h))
  -- the new program counter of `q`
  have hq'pc : (C'.loc q).pc = loopCheck tx (c \ ((C.loc q).com a ∪ {t}))
      (C.loc q).hist := by
    simp [hC', updCfg, updLoc, ha]
  have hq'cases : (C'.loc q).pc.tx? = some tx ∨ ∃ r, (C'.loc q).pc = .ret r := by
    rw [hq'pc]; unfold loopCheck; split_ifs
    · left; rfl
    · right; exact ⟨_, rfl⟩
  have hq'tx : ∀ tx', (C'.loc q).pc.tx? = some tx' → tx' = tx := by
    intro tx' h; rw [hq'pc] at h; unfold loopCheck at h; split_ifs at h
    · simp [PC.tx?] at h; exact h.symm
    · simp [PC.tx?] at h
  have hq'rs : ∀ a', (C'.loc q).pc ≠ .rscan a' := by
    intro a' h; rw [hq'pc] at h; unfold loopCheck at h; split_ifs at h
  have hq'prop : ∀ tx' c' pr, (C'.loc q).pc ≠ .prop tx' c' pr := by
    intro tx' c' pr h; rw [hq'pc] at h; unfold loopCheck at h; split_ifs at h
  have hq'ret : ∀ r, (C'.loc q).pc = .ret r → r = .inl (decide ((tx, true) ∈ (C'.loc q).hist)) ∧
      tx ∈ (C'.loc q).com tx.a := by
    intro r h
    have h1 := h; rw [hq'pc] at h1; unfold loopCheck at h1
    split_ifs at h1
    simp only [PC.ret.injEq] at h1
    have hq'h : (C'.loc q).hist = (C.loc q).hist := by simp [hC', updCfg, updLoc]
    refine ⟨by rw [hq'h]; exact h1.symm, ?_⟩
    rcases (hM'.proc q).kCur tx htxK htxp with h2 | h2
    · rw [h] at h2; simp [PC.tx?] at h2
    · exact h2
  have hq'hist : (C'.loc q).hist = AS C'.mem q := by
    have := (hM'.proc q).hist
    rcases hq'cases with h | ⟨r, h⟩
    · rw [this]; rw [hq'pc] at h ⊢; unfold loopCheck at h ⊢; split_ifs at h ⊢ <;> simp [PC.updDec]
    · rw [this, h]; simp [PC.updDec]
  -- facts shared by both cases
  have hgidLe : ∀ t' ∈ K, gid t' < (respsOf α t'.p).length ∨ (gid t' = (respsOf α t'.p).length ∧
      ((C'.loc t'.p).pc.tx? = some t' ∨ ∃ r, (C'.loc t'.p).pc = .ret r)) := by
    intro t' ht'
    rcases hL.gidLe t' ht' with h | ⟨h1, h2⟩
    · exact Or.inl h
    · right; refine ⟨h1, ?_⟩
      by_cases htp : t'.p = q
      · rw [htp] at h2 ⊢
        rw [hpc] at h2
        rcases h2 with h2 | ⟨r, h2⟩
        · simp [PC.tx?] at h2; subst h2; exact hq'cases
        · cases h2
      · rw [hloc' _ htp]; exact h2
  have hgidCur : ∀ q' tx', (C'.loc q').pc.tx? = some tx' →
      gid tx' = (respsOf (α ++ [.tau q]) q').length := by
    intro q' tx' h
    simp only [respsOf_append_tau]
    by_cases hq' : q' = q
    · subst hq'; rw [hq'tx tx' h]; exact hL.gidCur _ tx (by simp [hpc, PC.tx?])
    · rw [hloc' _ hq'] at h; exact hL.gidCur _ _ h
  have hmemL0 : ∀ y ∈ L, ∀ (T : Finset (Tx n Acct)), U C.mem ⊆ T →
      (∃ a, opOf (α ++ [.tau q]) y.1 = some (ATOp.read a)) ∨
      (∃ p' a b x, opOf (α ++ [.tau q]) y.1 = some (ATOp.transfer p' a b x) ∧ y.1.1 ∉ μ a) ∨
      (∃ t ∈ K, y.1 = (t.p, gid t) ∧ (t ∈ T ∨ ∃ r, Dec C'.mem t.a r = some (t, false))) := by
    intro y hy T hT
    rw [hα]
    rcases hL.memL y hy with h | h | ⟨t', ht', h1, h2 | ⟨r, hr⟩⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨t', ht', h1, Or.inl (hT h2)⟩)
    · exact Or.inr (Or.inr ⟨t', ht', h1, Or.inr ⟨r, by rw [hDec']; exact hr⟩⟩)
  by_cases hns : b = true ∧ t ∉ U C.mem
  · -- a new successful transfer: linearize it now
    obtain ⟨rfl, hnotU⟩ := hns
    have hU'' : U C'.mem = insert t (U C.mem) := by rw [hU']; rfl
    have hx : t.x ≤ lst (μ := μ) (q₀ := q₀) L t.a := by
      rw [hta]; exact hL.decP a ρ t hd.symm hnotU
    have htμ : t.p ∈ μ t.a := hM.kOwn t htK
    have hnoF : ∀ r, Dec C.mem t.a r ≠ some (t, false) := by
      intro r hr; rw [hta] at hr; have := hM.dec_res hd.symm hr; cases this
    have hnotL := hL.not_mem hM htK hnotU hnoF
    obtain ⟨htpc, htgid⟩ := hL.pending hM htK (hM.not_com_of_notU (by rw [hta]; exact hd.symm) hnotU)
    set xt : OpId (Fin n) := (t.p, gid t) with hxt
    set ot : ATOp (Fin n) Acct := ATOp.transfer t.p t.a t.b t.x with hot
    have hlst : lst (μ := μ) (q₀ := q₀) (L ++ [(xt, ot)]) =
        moveFunds (lst (μ := μ) (q₀ := q₀) L) t.a t.b t.x := lst_transfer_true L xt htμ hx
    have hnc : ¬ Completed (α ++ [.tau q]) xt := not_completed_of_eq (by simp [hxt, htgid])
    have hpushed (y : OpId (Fin n)) (hy : y ∈ L.map Prod.fst) :
        lrs (μ := μ) (q₀ := q₀) (L ++ [(xt, ot)]) y = lrs (μ := μ) (q₀ := q₀) L y :=
      ObjSpec.respIn_append_of_mem hy _
    have hS : ∀ t' ∈ K, t' ∈ U C'.mem →
        lrs (μ := μ) (q₀ := q₀) (L ++ [(xt, ot)]) (t'.p, gid t') = some (.inl true) := by
      intro t' ht' hu
      rw [hU'', Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · exact lrs_transfer_true L xt htμ hx hnotL
      · have := hL.respS t' ht' hu; rw [hpushed _ (ObjSpec.mem_of_respIn_eq_some this)]; exact this
    have hF : ∀ t' ∈ K, ∀ r, Dec C'.mem t'.a r = some (t', false) →
        lrs (μ := μ) (q₀ := q₀) (L ++ [(xt, ot)]) (t'.p, gid t') = some (.inl false) := by
      intro t' ht' r hr
      rw [hDec'] at hr
      have := hL.respF t' ht' r hr; rw [hpushed _ (ObjSpec.mem_of_respIn_eq_some this)]; exact this
    -- the only decided successful transfer not in `AS` is the latest one
    have hlatest : ∀ r t', Dec C.mem a r = some (t', true) → t' ∉ U C.mem → t' = t := by
      intro r t' h hu
      rcases lt_trichotomy r ρ with hr | rfl | hr
      · exfalso
        obtain ⟨q'', d'', hd'', hm⟩ := hM.dec_lt (by rw [← hd]; simp) hr
        rw [h] at hd''; cases hd''
        exact hu (mem_U.2 ⟨q'', hm⟩)
      · rw [h] at hd; simp only [Option.some.injEq, Prod.mk.injEq] at hd; exact hd.1.symm
      · exfalso
        obtain ⟨q'', d'', hd'', hm⟩ := hM.dec_lt (by rw [h]; simp) hr
        rw [← hd] at hd''; cases hd''
        exact hnotU (mem_U.2 ⟨q'', hm⟩)
    refine ⟨L ++ [(xt, ot)], ?_⟩
    exact {
      opK := fun t' ht' => by rw [hα]; exact hL.opK t' ht'
      inj := hL.inj
      gidLe := fun t' ht' => by simp only [respsOf_append_tau]; exact hgidLe t' ht'
      gidCur := hgidCur
      lin := (hL.lin.append_tau q).push (by rw [hα]; exact hL.opK t htK) hnotL hnc
      bal := by
        rw [hU'', hlst]
        exact bal_push hnotU hx hL.bal
      memL := fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · exact hmemL0 y hy _ (by rw [hU'']; exact Finset.subset_insert _ _)
        · simp only [List.mem_singleton] at hy; subst hy
          exact Or.inr (Or.inr ⟨t, htK, rfl, Or.inl (by rw [hU'']; exact Finset.mem_insert_self _ _)⟩)
      respS := hS
      respF := hF
      retR := fun q' r h => by
        simp only [respsOf_append_tau]
        by_cases hq' : q' = q
        · subst hq'
          obtain ⟨rfl, hcom⟩ := hq'ret r h
          rw [← hL.gidCur q' tx (by simp [hpc, PC.tx?])]
          have := ret_after_loop hM' hS hF htxK (by rw [htxp]; exact hcom)
            (by rw [htxp]; exact hq'hist)
          rw [htxp] at this; exact this
        · rw [hloc' _ hq'] at h
          have := hL.retR q' r h; rw [hpushed _ (ObjSpec.mem_of_respIn_eq_some this)]; exact this
      rscan := fun q' a' h => by
        simp only [respsOf_append_tau]
        by_cases hq' : q' = q
        · subst hq'; exact absurd h (hq'rs a')
        · rw [hloc' _ hq'] at h
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_singleton, not_or]
          refine ⟨hL.rscan q' a' h, fun he => ?_⟩
          rw [hxt, Prod.mk.injEq] at he
          rw [← he.1, h] at htpc; simp [PC.tx?] at htpc
      decP := fun a' r t' h hu => by
        rw [hDec'] at h
        rw [hU'', Finset.mem_insert, not_or] at hu
        rw [hlst]
        by_cases haa : a' = t.a
        · exfalso; rw [haa, hta] at h; exact hu.1 (hlatest r t' h hu.2)
        · exact (hL.decP a' r t' h hu.2).trans (le_moveFunds_of_ne _ _ haa)
      propI := fun q' tx' c' t' res' h hd' => by
        by_cases hq' : q' = q
        · subst hq'; exact absurd h (hq'prop _ _ _)
        · rw [hloc' _ hq'] at h hd'
          rw [hDec'] at hd'
          obtain ⟨h1, h2⟩ := hL.propI q' tx' c' t' res' h hd'
          refine ⟨fun hr => ?_, fun hr => ?_⟩
          · rw [hlst]
            by_cases haa : t'.a = t.a
            · exfalso
              have ht'a : t'.a = tx'.a :=
                ((hM.proc q').loop tx' c' (by simp [h, PC.loopC])).2 t'
                  ((hM.proc q').prop _ _ _ h).1 |>.2.1
              rw [haa, hta] at ht'a
              rcases lt_or_ge ρ ((C.loc q').rnd a) with hlt | hge
              · obtain ⟨d'', hd'', hm⟩ := (hM.proc q').asAll a ρ hlt
                rw [← hd] at hd''; cases hd''
                exact hnotU (mem_U.2 ⟨q', hm⟩)
              · rw [← ht'a] at hd'
                exact hM.dec_lt_ne (by rw [← hd]; simp) hge hd'
            · exact (h1 hr).trans (le_moveFunds_of_ne _ _ haa)
          · obtain ⟨S₁, S₂, h3, h4, h5⟩ := h2 hr
            refine ⟨S₁, S₂ ++ [(xt, ot)], by rw [h3]; simp, h4, ?_⟩
            intro y hy
            rcases List.mem_append.1 hy with hy | hy
            · exact not_precedes_append (hPrec q' tx' c' t' res' h) h5 y hy
            · simp only [List.mem_singleton] at hy; subst hy
              intro hp'; exact hnc hp'.completed }
  · -- nothing new is linearized
    have hU'' : U C'.mem = U C.mem := by
      rw [hU']; split_ifs with hb
      · exact Finset.insert_eq_of_mem (by by_contra h; exact hns ⟨hb, h⟩)
      · rfl
    have hS : ∀ t' ∈ K, t' ∈ U C'.mem →
        lrs (μ := μ) (q₀ := q₀) L (t'.p, gid t') = some (.inl true) := by
      intro t' ht' hu; rw [hU''] at hu; exact hL.respS t' ht' hu
    have hF : ∀ t' ∈ K, ∀ r, Dec C'.mem t'.a r = some (t', false) →
        lrs (μ := μ) (q₀ := q₀) L (t'.p, gid t') = some (.inl false) := by
      intro t' ht' r hr; rw [hDec'] at hr; exact hL.respF t' ht' r hr
    refine ⟨L, ?_⟩
    exact {
      opK := fun t' ht' => by rw [hα]; exact hL.opK t' ht'
      inj := hL.inj
      gidLe := fun t' ht' => by simp only [respsOf_append_tau]; exact hgidLe t' ht'
      gidCur := hgidCur
      lin := hL.lin.append_tau q
      bal := by rw [hU'']; exact hL.bal
      memL := fun y hy => by
        have := hmemL0 y hy (U C'.mem) (by rw [hU''])
        exact this
      respS := hS
      respF := hF
      retR := fun q' r h => by
        simp only [respsOf_append_tau]
        by_cases hq' : q' = q
        · subst hq'
          obtain ⟨rfl, hcom⟩ := hq'ret r h
          rw [← hL.gidCur q' tx (by simp [hpc, PC.tx?])]
          have := ret_after_loop hM' hS hF htxK (by rw [htxp]; exact hcom)
            (by rw [htxp]; exact hq'hist)
          rw [htxp] at this; exact this
        · rw [hloc' _ hq'] at h; exact hL.retR q' r h
      rscan := fun q' a' h => by
        simp only [respsOf_append_tau]
        by_cases hq' : q' = q
        · subst hq'; exact absurd h (hq'rs a')
        · rw [hloc' _ hq'] at h; exact hL.rscan q' a' h
      decP := fun a' r t' h hu => by
        rw [hDec'] at h; rw [hU''] at hu; exact hL.decP a' r t' h hu
      propI := fun q' tx' c' t' res' h hd' => by
        by_cases hq' : q' = q
        · subst hq'; exact absurd h (hq'prop _ _ _)
        · rw [hloc' _ hq'] at h hd'
          rw [hDec'] at hd'
          obtain ⟨h1, h2⟩ := hL.propI q' tx' c' t' res' h hd'
          refine ⟨h1, fun hr => ?_⟩
          obtain ⟨S₁, S₂, h3, h4, h5⟩ := h2 hr
          exact ⟨S₁, S₂, h3, h4, not_precedes_append (hPrec q' tx' c' t' res' h) h5⟩ }

end CryptoCons.Fig3
