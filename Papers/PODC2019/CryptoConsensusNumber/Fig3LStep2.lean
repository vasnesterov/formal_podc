import Papers.PODC2019.CryptoConsensusNumber.Fig3LStep

/-!
# Figure 3: the linearization invariant is preserved (proposals, line 9)

When a process is the first to invoke `kC_a[r]`, its proposal is decided. A failed transfer is
then linearized retroactively at the snapshot (line 8) the proposer took before proposing.
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig3

open Cslib.SharedMemory

set_option allowUnsafeReducibility true in
attribute [local reducible] atSpec snapObj kConsObj

variable {n : ℕ} {Acct : Type} [DecidableEq Acct] {μ : Acct → Finset (Fin n)} {q₀ : Acct → ℕ}
  {k : ℕ} {α : Hst μ q₀} {C : Cfg μ q₀ k} {K : Set (Tx n Acct)} {gid : Tx n Acct → ℕ}
  {L : LinL n Acct} {q : Fin n}

/-- The configuration after a proposal step. -/
abbrev propCfg (C : Cfg μ q₀ k) (q : Fin n) (tx : Tx n Acct) (c : Finset (Tx n Acct))
    (pr : Tx n Acct × Bool) : Cfg μ q₀ k :=
  { C with
    mem := Function.update C.mem (.inr (.inr (tx.a, (C.loc q).rnd tx.a)))
      (((some ((Dec C.mem tx.a ((C.loc q).rnd tx.a)).getD pr),
        (KC C.mem tx.a ((C.loc q).rnd tx.a)).2 + 1)) : Option (Tx n Acct × Bool) × ℕ)
    loc := Function.update C.loc q
      { C.loc q with
        pc := .upd tx c (some ((Dec C.mem tx.a ((C.loc q).rnd tx.a)).getD pr))
        hist := (C.loc q).hist ∪ {(Dec C.mem tx.a ((C.loc q).rnd tx.a)).getD pr} } }

lemma LInv.step_prop (hL : LInv μ q₀ α C K gid L) (hM : MInv μ C K)
    {tx : Tx n Acct} {c : Finset (Tx n Acct)} {pr : Tx n Acct × Bool}
    (hpc : (C.loc q).pc = .prop tx c pr) :
    ∃ L', LInv μ q₀ (α ++ [.tau q]) (propCfg C q tx c pr) K gid L' := by
  have hp := hM.proc q
  obtain ⟨hin, hcK⟩ := hp.loop tx c (by simp [hpc, PC.loopC])
  have hprc := (hp.prop tx c pr hpc).1
  obtain ⟨t, res⟩ := pr
  simp only at hprc
  obtain ⟨htK, hta, -⟩ := hcK t hprc
  set a := tx.a with ha
  set ρ := (C.loc q).rnd a with hρ
  set dn := (Dec C.mem a ρ).getD (t, res) with hdn
  set C' := propCfg C q tx c (t, res) with hC'
  have hDec' : ∀ a' r, Dec C'.mem a' r = if (a', r) = (a, ρ) then some dn else Dec C.mem a' r := by
    intro a' r; simp only [hC', propCfg, Dec, KC_update_KC]; split_ifs <;> rfl
  have hU' : U C'.mem = U C.mem := U_update_KC _ _
  have hloc' : ∀ q', C'.loc q' = if q' = q then
      { C.loc q with pc := .upd tx c (some dn), hist := (C.loc q).hist ∪ {dn} } else C.loc q' := by
    intro q'; simp only [hC', propCfg, Function.update_apply]; rfl
  have hExt : ∀ a' r d, Dec C.mem a' r = some d → Dec C'.mem a' r = some d := by
    intro a' r d h; rw [hDec']; split_ifs with he
    · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; simp [hdn, h]
    · exact h
  have hNone : ∀ a' r, Dec C'.mem a' r = none → Dec C.mem a' r = none := by
    intro a' r h; cases hd : Dec C.mem a' r with
    | none => rfl
    | some d => rw [hExt a' r d hd] at h; cases h
  have hα : ∀ x, opOf (α ++ [.tau q]) x = opOf α x := opOf_append_noinv (by simp)
  -- facts about the other processes' proposals
  have hPrec : ∀ q' tx' c' t' res', (C.loc q').pc = .prop tx' c' (t', res') →
      Invoked α (t'.p, gid t') :=
    fun q' tx' c' t' res' h => invoked_of_opOf (hL.opK t' (hM.prop_K h))
  by_cases hund : Dec C.mem a ρ = none ∧ res = false
  · -- the proposal `(t, false)` is decided: insert `t` at the snapshot point
    obtain ⟨hund, hres⟩ := hund
    subst hres
    have hdn' : dn = (t, false) := by simp [hdn, hund]
    obtain ⟨-, h2⟩ := hL.propI q tx c t false hpc hund
    obtain ⟨S₁, S₂, hS, hlt, hS₂⟩ := h2 rfl
    have hundec : ∀ r b, Dec C.mem t.a r ≠ some (t, b) :=
      fun r b => hM.undec_of_loop (by simp [hpc, PC.loopC]) hprc hund r b
    have hnotU : t ∉ U C.mem := fun h => by
      obtain ⟨r, hr⟩ := hM.dec_of_U h; exact hundec r true hr
    have hnotL := hL.not_mem hM htK hnotU (fun r => hundec r false)
    obtain ⟨htpc, htgid⟩ := hL.pending hM htK (hM.not_com_of_undec hundec)
    set xt : OpId (Fin n) := (t.p, gid t) with hxt
    set ot : ATOp (Fin n) Acct := ATOp.transfer t.p t.a t.b t.x with hot
    have hneu : (AT μ q₀).δ (lst (μ := μ) (q₀ := q₀) S₁) ot = (lst (μ := μ) (q₀ := q₀) S₁, .inl false) :=
      atSpec_transfer_neg (fun h => absurd h.2 (by omega))
    have hneu1 : (AT μ q₀).δ (linState (A := AT μ q₀) S₁) ot = (linState (A := AT μ q₀) S₁, .inl false) := hneu
    have hlst : ∀ B, lst (μ := μ) (q₀ := q₀) (S₁ ++ (xt, ot) :: B) = lst (μ := μ) (q₀ := q₀) (S₁ ++ B) :=
      fun B => linState_insert (A := AT μ q₀) S₁ B xt ot (by rw [hneu1])
    have hlrs : ∀ x, x ≠ xt → lrs (μ := μ) (q₀ := q₀) (S₁ ++ (xt, ot) :: S₂) x =
        lrs (μ := μ) (q₀ := q₀) L x := by
      intro x hx; rw [hS]
      exact linResp_insert (A := AT μ q₀) S₁ S₂ xt ot (by rw [hneu1]) x (Ne.symm hx)
    have hnc : ¬ Completed (α ++ [.tau q]) xt := not_completed_of_eq (by simp [hxt, htgid])
    have hxt_ne : ∀ q', (∀ t', (C.loc q').pc.tx? ≠ some t') → (q', (respsOf α q').length) ≠ xt := by
      intro q' hq' he
      simp only [hxt, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact hq' t htpc
    refine ⟨S₁ ++ (xt, ot) :: S₂, ?_⟩
    have hDecF : ∀ t' r, Dec C'.mem t'.a r = some (t', false) → t' = t ∨ Dec C.mem t'.a r = some (t', false) := by
      intro t' r h; rw [hDec'] at h; split_ifs at h with he
      · left; rw [hdn'] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
      · exact Or.inr h
    exact {
      opK := fun t' ht' => by rw [hα]; exact hL.opK t' ht'
      inj := hL.inj
      gidLe := fun t' ht' => by
        simp only [respsOf_append_tau, hloc']
        rcases hL.gidLe t' ht' with h | ⟨h1, h2⟩
        · exact Or.inl h
        · right; refine ⟨h1, ?_⟩
          split_ifs with htp
          · rw [htp, hpc] at h2; simpa [PC.tx?] using h2
          · exact h2
      gidCur := fun q' tx' h => by
        simp only [respsOf_append_tau]
        rw [hloc'] at h; split_ifs at h with hq'
        · subst hq'; exact hL.gidCur q' tx' (by simpa [hpc, PC.tx?] using h)
        · exact hL.gidCur q' tx' h
      lin := by
        have h0 := hL.lin.append_tau q
        rw [hS] at h0 hnotL
        exact isLin_insert h0 (by rw [hα]; exact hL.opK t htK) hnotL hnc
          (congrArg Prod.fst hneu1)
          (not_precedes_append (invoked_of_opOf (hL.opK t htK)) hS₂)
      bal := by rw [hlst, ← hS, hU']; exact hL.bal
      memL := fun y hy => by
        rw [hU']
        rcases List.mem_append.1 hy with hy | hy
        · have hyL : y ∈ L := by rw [hS]; exact List.mem_append_left _ hy
          rw [hL.opOf_mem _ hyL]
          rcases hL.memL y hyL with h | h | ⟨t', ht', h1, h2 | ⟨r, hr⟩⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨t', ht', h1, Or.inl h2⟩)
          · exact Or.inr (Or.inr ⟨t', ht', h1, Or.inr ⟨r, hExt _ _ _ hr⟩⟩)
        · rcases List.mem_cons.1 hy with rfl | hy
          · refine Or.inr (Or.inr ⟨t, htK, rfl, Or.inr ⟨ρ, ?_⟩⟩)
            rw [hDec', hta, ite_eq_left rfl, hdn']
          · have hyL : y ∈ L := by rw [hS]; exact List.mem_append_right _ hy
            rw [hL.opOf_mem _ hyL]
            rcases hL.memL y hyL with h | h | ⟨t', ht', h1, h2 | ⟨r, hr⟩⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨t', ht', h1, Or.inl h2⟩)
            · exact Or.inr (Or.inr ⟨t', ht', h1, Or.inr ⟨r, hExt _ _ _ hr⟩⟩)
      respS := fun t' ht' hu => by
        rw [hU'] at hu
        have hne : t' ≠ t := fun h => hnotU (h ▸ hu)
        rw [hlrs _ (fun h => hne (hL.inj t' ht' t htK (congrArg Prod.fst h)
          (congrArg Prod.snd h)))]
        exact hL.respS t' ht' hu
      respF := fun t' ht' r hr => by
        rcases hDecF t' r hr with rfl | hr
        · rw [show lrs (μ := μ) (q₀ := q₀) (S₁ ++ (xt, ot) :: S₂) (t'.p, gid t') =
            linResp (AT μ q₀) (S₁ ++ (xt, ot) :: S₂) xt from rfl]
          rw [linResp_insert_self _ _ _ _ (fun h => hnotL (by rw [hS]; simp [h])), hneu1]
        · have hne : t' ≠ t := fun h => hundec r false (h ▸ hr)
          rw [hlrs _ (fun h => hne (hL.inj t' ht' t htK (congrArg Prod.fst h)
            (congrArg Prod.snd h)))]
          exact hL.respF t' ht' r hr
      retR := fun q' r h => by
        simp only [respsOf_append_tau]
        by_cases hq' : q' = q
        · subst hq'; rw [hloc', ite_eq_left rfl] at h; simp at h
        · rw [hloc', ite_eq_right hq'] at h
          rw [hlrs _ (hxt_ne q' (fun t' => by rw [h]; simp [PC.tx?]))]
          exact hL.retR q' r h
      rscan := fun q' a' h => by
        simp only [respsOf_append_tau]
        by_cases hq' : q' = q
        · subst hq'; rw [hloc', ite_eq_left rfl] at h; simp at h
        · rw [hloc', ite_eq_right hq'] at h
          have h1 := hL.rscan q' a' h
          have h2 := hxt_ne q' (fun t' => by rw [h]; simp [PC.tx?])
          rw [hS] at h1
          simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at h1 ⊢
          tauto
      decP := fun a' r t' h hu => by
        rw [hU'] at hu
        rw [show S₁ ++ (xt, ot) :: S₂ = S₁ ++ (xt, ot) :: S₂ from rfl, hlst, ← hS]
        rw [hDec'] at h; split_ifs at h with he
        · rw [hdn'] at h; simp at h
        · exact hL.decP a' r t' h hu
      propI := fun q' tx' c' t' res' h hd => by
        by_cases hq' : q' = q
        · subst hq'; rw [hloc', ite_eq_left rfl] at h; simp at h
        · rw [hloc', ite_eq_right hq'] at h hd
          have hd0 := hNone _ _ hd
          obtain ⟨h1, h2⟩ := hL.propI q' tx' c' t' res' h hd0
          refine ⟨fun hr => by rw [hlst, ← hS]; exact h1 hr, fun hr => ?_⟩
          obtain ⟨T₁, T₂, hT, hTlt, hT₂⟩ := h2 hr
          rw [hS] at hT
          obtain ⟨T₁', T₂', hT', hmem2, hT₁'⟩ := split_insert' hT.symm (xt, ot)
          refine ⟨T₁', T₂', hT', ?_, ?_⟩
          · rcases hT₁' with rfl | ⟨B, rfl, rfl⟩
            · exact hTlt
            · rw [hlst]; exact hTlt
          · intro y hy hpr
            rcases hmem2 y hy with hy | rfl
            · exact not_precedes_append (hPrec q' tx' c' t' res' h) hT₂ y hy hpr
            · exact hnc hpr.completed }
  · -- the decision is not a new failure: `L` is unchanged
    have hDecT : ∀ a' r t' b, Dec C'.mem a' r = some (t', b) → Dec C.mem a' r = some (t', b) ∨
        ((a', r) = (a, ρ) ∧ Dec C.mem a ρ = none ∧ (t', b) = (t, res) ∧ res = true) := by
      intro a' r t' b h
      rw [hDec'] at h; split_ifs at h with he
      · simp only [Prod.mk.injEq] at he; obtain ⟨h1, h2⟩ := he
        subst h1 h2
        cases hd : Dec C.mem a ρ with
        | some d0 =>
          left
          have : dn = d0 := by simp [hdn, hd]
          rw [this] at h; exact h
        | none =>
          right
          have hres : res = true := by
            by_contra hr; simp only [Bool.not_eq_true] at hr; exact hund ⟨hd, hr⟩
          have : dn = (t, res) := by simp [hdn, hd]
          rw [this] at h
          exact ⟨rfl, rfl, (Option.some.inj h).symm, hres⟩
      · exact Or.inl h
    refine ⟨L, ?_⟩
    exact {
      opK := fun t' ht' => by rw [hα]; exact hL.opK t' ht'
      inj := hL.inj
      gidLe := fun t' ht' => by
        simp only [respsOf_append_tau, hloc']
        rcases hL.gidLe t' ht' with h | ⟨h1, h2⟩
        · exact Or.inl h
        · right; refine ⟨h1, ?_⟩
          split_ifs with htp
          · rw [htp, hpc] at h2; simpa [PC.tx?] using h2
          · exact h2
      gidCur := fun q' tx' h => by
        simp only [respsOf_append_tau]
        rw [hloc'] at h; split_ifs at h with hq'
        · subst hq'; exact hL.gidCur q' tx' (by simpa [hpc, PC.tx?] using h)
        · exact hL.gidCur q' tx' h
      lin := hL.lin.append_tau q
      bal := by rw [hU']; exact hL.bal
      memL := fun y hy => by
        rw [hU', hα]
        rcases hL.memL y hy with h | h | ⟨t', ht', h1, h2 | ⟨r, hr⟩⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨t', ht', h1, Or.inl h2⟩)
        · exact Or.inr (Or.inr ⟨t', ht', h1, Or.inr ⟨r, hExt _ _ _ hr⟩⟩)
      respS := fun t' ht' hu => by rw [hU'] at hu; exact hL.respS t' ht' hu
      respF := fun t' ht' r hr => by
        rcases hDecT _ _ _ _ hr with hr | ⟨-, -, h, hres⟩
        · exact hL.respF t' ht' r hr
        · simp only [Prod.mk.injEq] at h; rw [← h.2] at hres; cases hres
      retR := fun q' r h => by
        simp only [respsOf_append_tau]
        by_cases hq' : q' = q
        · subst hq'; rw [hloc', ite_eq_left rfl] at h; simp at h
        · rw [hloc', ite_eq_right hq'] at h; exact hL.retR q' r h
      rscan := fun q' a' h => by
        simp only [respsOf_append_tau]
        by_cases hq' : q' = q
        · subst hq'; rw [hloc', ite_eq_left rfl] at h; simp at h
        · rw [hloc', ite_eq_right hq'] at h; exact hL.rscan q' a' h
      decP := fun a' r t' h hu => by
        rw [hU'] at hu
        rcases hDecT _ _ _ _ h with h | ⟨he, hnone, h, hres⟩
        · exact hL.decP a' r t' h hu
        · simp only [Prod.mk.injEq] at he h
          have := (hL.propI q tx c t res hpc hnone).1 hres
          rw [he.1, h.1, ← hta]; exact this
      propI := fun q' tx' c' t' res' h hd => by
        by_cases hq' : q' = q
        · subst hq'; rw [hloc', ite_eq_left rfl] at h; simp at h
        · rw [hloc', ite_eq_right hq'] at h hd
          have hd0 := hNone _ _ hd
          obtain ⟨h1, h2⟩ := hL.propI q' tx' c' t' res' h hd0
          refine ⟨h1, fun hr => ?_⟩
          obtain ⟨T₁, T₂, hT, hTlt, hT₂⟩ := h2 hr
          exact ⟨T₁, T₂, hT, hTlt, not_precedes_append (hPrec q' tx' c' t' res' h) hT₂⟩ }

end CryptoCons.Fig3
