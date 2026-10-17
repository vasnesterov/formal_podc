import Papers.PODC2019.CryptoConsensusNumber.Fig3LInv

/-!
# Figure 3: the linearization invariant is preserved (invocations, responses, simple steps)
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig3

open Cslib.SharedMemory

set_option allowUnsafeReducibility true in
attribute [local reducible] atSpec snapObj kConsObj

variable {n : ℕ} {Acct : Type} [DecidableEq Acct] {μ : Acct → Finset (Fin n)} {q₀ : Acct → ℕ}
  {k : ℕ} {α : Hst μ q₀} {C : Cfg μ q₀ k} {K : Set (Tx n Acct)} {gid : Tx n Acct → ℕ}
  {L : LinL n Acct} {q : Fin n}

/-- Real-time precedence towards an already invoked operation is not created by new labels. -/
lemma not_precedes_append {β : Hst μ q₀} {S : LinL n Acct} {x : OpId (Fin n)}
    (hx : Invoked α x) (h : ∀ y ∈ S, ¬ Precedes α y.1 x) :
    ∀ y ∈ S, ¬ Precedes (α ++ β) y.1 x :=
  fun y hy hp => h y hy (hp.of_append_of_invoked hx)

/-- A proposal's tuple is a created tuple. -/
lemma MInv.prop_K (hM : MInv μ C K) {q : Fin n} {tx t : Tx n Acct} {c : Finset (Tx n Acct)}
    {res : Bool} (h : (C.loc q).pc = .prop tx c (t, res)) : t ∈ K := by
  have h1 := ((hM.proc q).prop tx c (t, res) h).1
  exact ((hM.proc q).loop tx c (by simp [h, PC.loopC])).2 t h1 |>.1

/-- Steps that change neither `L` nor the decisions nor `AS` (lines 4, 5, 8). -/
lemma LInv.tau_same (hL : LInv μ q₀ α C K gid L) (hM : MInv μ C K) (q : Fin n) (l' : Loc n Acct)
    (m' : Mem n Acct k) (hU : U m' = U C.mem) (hDec : ∀ a r, Dec m' a r = Dec C.mem a r)
    (htx : l'.pc.tx? = (C.loc q).pc.tx?)
    (hnret : ∀ r, (C.loc q).pc ≠ .ret r) (hnret' : ∀ r, l'.pc ≠ .ret r)
    (hrs : ∀ a, l'.pc ≠ .rscan a)
    (hprop : ∀ tx c t res, l'.pc = .prop tx c (t, res) → Dec C.mem tx.a (l'.rnd tx.a) = none →
      (res = true → t.x ≤ lst (μ := μ) (q₀ := q₀) L t.a) ∧
      (res = false → ∃ S₁ S₂, L = S₁ ++ S₂ ∧ lst (μ := μ) (q₀ := q₀) S₁ t.a < t.x ∧
        ∀ y ∈ S₂, ¬ Precedes (α ++ [.tau q]) y.1 (t.p, gid t))) :
    LInv μ q₀ (α ++ [.tau q]) ({ C with loc := Function.update C.loc q l', mem := m' } :
      Cfg μ q₀ k) K gid L where
  opK t ht := by rw [opOf_append_noinv (by simp)]; exact hL.opK t ht
  inj := hL.inj
  gidLe t ht := by
    simp only [respsOf_append_tau]
    rcases hL.gidLe t ht with h | ⟨h1, h2⟩
    · exact Or.inl h
    · right; refine ⟨h1, ?_⟩
      by_cases htp : t.p = q
      · rw [htp] at h2 ⊢; simp only [Function.update_self]
        rcases h2 with h2 | ⟨r, hr⟩
        · exact Or.inl (htx ▸ h2)
        · exact absurd hr (hnret r)
      · simpa [Function.update_of_ne htp] using h2
  gidCur q' tx h := by
    simp only [respsOf_append_tau]
    by_cases hq : q' = q
    · subst hq; simp only [Function.update_self] at h; exact hL.gidCur _ _ (htx ▸ h)
    · simp only [Function.update_of_ne hq] at h; exact hL.gidCur _ _ h
  lin := hL.lin.append_tau q
  bal := by rw [hU]; exact hL.bal
  memL y hy := by
    rw [opOf_append_noinv (by simp), hU]; simp only [hDec]; exact hL.memL y hy
  respS t ht hu := hL.respS t ht (by rwa [hU] at hu)
  respF t ht r hr := hL.respF t ht r (by rwa [hDec] at hr)
  retR q' r h := by
    simp only [respsOf_append_tau]
    by_cases hq : q' = q
    · subst hq; simp only [Function.update_self] at h; exact absurd h (hnret' r)
    · simp only [Function.update_of_ne hq] at h; exact hL.retR q' r h
  rscan q' a h := by
    simp only [respsOf_append_tau]
    by_cases hq : q' = q
    · subst hq; simp only [Function.update_self] at h; exact absurd h (hrs a)
    · simp only [Function.update_of_ne hq] at h; exact hL.rscan q' a h
  decP a r t h hu := hL.decP a r t (by rwa [hDec] at h) (by rwa [hU] at hu)
  propI q' tx c t res h hd := by
    by_cases hq : q' = q
    · subst hq
      simp only [Function.update_self] at h hd
      rw [hDec] at hd
      exact hprop tx c t res h hd
    · simp only [Function.update_of_ne hq] at h hd
      rw [hDec] at hd
      obtain ⟨h1, h2⟩ := hL.propI q' tx c t res h hd
      refine ⟨h1, fun hr => ?_⟩
      obtain ⟨S₁, S₂, h3, h4, h5⟩ := h2 hr
      exact ⟨S₁, S₂, h3, h4, not_precedes_append
        (Invoked.of_opOf_eq_some (hL.opK t (hM.prop_K h))) h5⟩

/-! ## Invocations -/

lemma LInv.lt_of_idle (hL : LInv μ q₀ α C K gid L) (hM : MInv μ C K) (h0 : C.pend q = none)
    {t : Tx n Acct} (ht : t ∈ K) (htp : t.p = q) : gid t < (respsOf α q).length := by
  have hidle : (C.loc q).pc = .idle := (hM.proc q).idle.1 h0
  rcases hL.gidLe t ht with h | ⟨-, h⟩
  · rw [htp] at h; exact h
  · rw [htp, hidle] at h; simp [PC.tx?] at h

lemma LInv.opOf_mem (hL : LInv μ q₀ α C K gid L) (β : Hst μ q₀) {y : OpId (Fin n) × ATOp (Fin n) Acct}
    (hy : y ∈ L) : opOf (α ++ β) y.1 = opOf α y.1 :=
  opOf_append_of_invoked (hL.lin.mem_invoked (List.mem_map_of_mem hy))

lemma LInv.step_inv_read (hL : LInv μ q₀ α C K gid L) (hM : MInv μ C K)
    (hrun : (impl μ q₀ k).run α = some C) (h0 : C.pend q = none) (a : Acct) :
    LInv μ q₀ (α ++ [.inv q (ATOp.read a)]) ({ C with
      pend := Function.update C.pend q (some (ATOp.read a))
      loc := Function.update C.loc q { C.loc q with pc := .rscan a } } : Cfg μ q₀ k) K gid L where
  opK t ht := opOf_append_of_some _ (hL.opK t ht)
  inj := hL.inj
  gidLe t ht := by
    simp only [respsOf_append_inv]
    by_cases htp : t.p = q
    · exact Or.inl (htp ▸ hL.lt_of_idle hM h0 ht htp)
    · simpa [Function.update_of_ne htp] using hL.gidLe t ht
  gidCur q' tx h := by
    simp only [respsOf_append_inv]
    by_cases hq : q' = q
    · subst hq; simp [PC.tx?] at h
    · simp only [Function.update_of_ne hq] at h; exact hL.gidCur _ _ h
  lin := hL.lin.append_inv q _
  bal := hL.bal
  memL y hy := by rw [hL.opOf_mem _ hy]; exact hL.memL y hy
  respS := hL.respS
  respF := hL.respF
  retR q' r h := by
    simp only [respsOf_append_inv]
    by_cases hq : q' = q
    · subst hq; simp at h
    · simp only [Function.update_of_ne hq] at h; exact hL.retR q' r h
  rscan q' a' h := by
    simp only [respsOf_append_inv]
    by_cases hq : q' = q
    · subst hq
      intro hm
      exact not_invoked_cur_of_idle (idle_counts_of_run hrun h0) (hL.lin.mem_invoked hm)
    · simp only [Function.update_of_ne hq] at h; exact hL.rscan q' a' h
  decP := hL.decP
  propI q' tx c t res h hd := by
    by_cases hq : q' = q
    · subst hq; simp at h
    · simp only [Function.update_of_ne hq] at h hd
      obtain ⟨h1, h2⟩ := hL.propI q' tx c t res h hd
      refine ⟨h1, fun hr => ?_⟩
      obtain ⟨S₁, S₂, h3, h4, h5⟩ := h2 hr
      exact ⟨S₁, S₂, h3, h4, not_precedes_append
        (Invoked.of_opOf_eq_some (hL.opK t (hM.prop_K h))) h5⟩

lemma LInv.step_inv_nonowner (hL : LInv μ q₀ α C K gid L) (hM : MInv μ C K)
    (hrun : (impl μ q₀ k).run α = some C) (h0 : C.pend q = none) (a b : Acct) (x : ℕ)
    (hq : q ∉ μ a) :
    LInv μ q₀ (α ++ [.inv q (ATOp.transfer q a b x)]) ({ C with
      pend := Function.update C.pend q (some (ATOp.transfer q a b x))
      loc := Function.update C.loc q { C.loc q with pc := .ret (.inl false) } } : Cfg μ q₀ k) K gid
      (L ++ [((q, (respsOf α q).length), ATOp.transfer q a b x)]) := by
  have hcnt := idle_counts_of_run hrun h0
  have hnotinv := not_invoked_cur_of_idle hcnt
  have hnotL : (q, (respsOf α q).length) ∉ L.map Prod.fst :=
    fun hm => hnotinv (hL.lin.mem_invoked hm)
  have hop : opOf (α ++ [.inv q (ATOp.transfer q a b x)]) (q, (respsOf α q).length) =
      some (ATOp.transfer q a b x) := by
    simp [opOf, opsOf_append, ← hcnt]
  have hδ : (AT μ q₀).δ (lst (μ := μ) (q₀ := q₀) L) (ATOp.transfer q a b x) =
      (lst (μ := μ) (q₀ := q₀) L, .inl false) :=
    atSpec_transfer_neg (by simp [hq])
  have hlst : lst (μ := μ) (q₀ := q₀) (L ++ [((q, (respsOf α q).length), ATOp.transfer q a b x)]) =
      lst (μ := μ) (q₀ := q₀) L := by
    show linState (A := AT μ q₀) _ = _; rw [linState_concat, hδ]
  have hpushed (y : OpId (Fin n)) (hy : y ∈ L.map Prod.fst) :
      lrs (μ := μ) (q₀ := q₀) (L ++ [((q, (respsOf α q).length), ATOp.transfer q a b x)]) y =
        lrs (μ := μ) (q₀ := q₀) L y := ObjSpec.respIn_append_of_mem hy _
  exact {
    opK := fun t ht => opOf_append_of_some _ (hL.opK t ht)
    inj := hL.inj
    gidLe := fun t ht => by
      simp only [respsOf_append_inv]
      by_cases htp : t.p = q
      · exact Or.inl (htp ▸ hL.lt_of_idle hM h0 ht htp)
      · simpa [Function.update_of_ne htp] using hL.gidLe t ht
    gidCur := fun q' tx h => by
      simp only [respsOf_append_inv]
      by_cases hq' : q' = q
      · subst hq'; simp [PC.tx?] at h
      · simp only [Function.update_of_ne hq'] at h; exact hL.gidCur _ _ h
    lin := (hL.lin.append_inv q _).push hop (by simpa using hnotL)
      (not_completed_of_eq (by simp))
    bal := by rw [hlst]; exact hL.bal
    memL := fun y hy => by
      rcases List.mem_append.1 hy with hy | hy
      · rw [hL.opOf_mem _ hy]; exact hL.memL y hy
      · simp only [List.mem_singleton] at hy; subst hy
        exact Or.inr (Or.inl ⟨q, a, b, x, hop, hq⟩)
    respS := fun t ht hu => by
      have := hL.respS t ht hu; rw [hpushed _ (ObjSpec.mem_of_respIn_eq_some this)]; exact this
    respF := fun t ht r hr => by
      have := hL.respF t ht r hr; rw [hpushed _ (ObjSpec.mem_of_respIn_eq_some this)]; exact this
    retR := fun q' r h => by
      simp only [respsOf_append_inv]
      by_cases hq' : q' = q
      · subst hq'; simp only [Function.update_self, PC.ret.injEq] at h; subst h
        show lrs (μ := μ) (q₀ := q₀) _ _ = _
        rw [lrs_concat_self _ _ _ hnotL, hδ]
      · simp only [Function.update_of_ne hq'] at h
        have := hL.retR q' r h; rw [hpushed _ (ObjSpec.mem_of_respIn_eq_some this)]; exact this
    rscan := fun q' a' h => by
      simp only [respsOf_append_inv]
      by_cases hq' : q' = q
      · subst hq'; simp at h
      · simp only [Function.update_of_ne hq'] at h
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton, Prod.mk.injEq, not_or]
        exact ⟨hL.rscan q' a' h, fun h' => hq' h'.1⟩
    decP := fun a' r t h hu => by rw [hlst]; exact hL.decP a' r t h hu
    propI := fun q' tx c t res h hd => by
      by_cases hq' : q' = q
      · subst hq'; simp at h
      · simp only [Function.update_of_ne hq'] at h hd
        obtain ⟨h1, h2⟩ := hL.propI q' tx c t res h hd
        refine ⟨fun hr => by rw [hlst]; exact h1 hr, fun hr => ?_⟩
        obtain ⟨S₁, S₂, h3, h4, h5⟩ := h2 hr
        refine ⟨S₁, S₂ ++ [((q, (respsOf α q).length), ATOp.transfer q a b x)], by rw [h3]; simp,
          h4, ?_⟩
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact not_precedes_append (Invoked.of_opOf_eq_some (hL.opK t (hM.prop_K h))) h5 y hy
        · simp only [List.mem_singleton] at hy; subst hy
          intro hp
          exact not_completed_of_eq (α := α ++ [.inv q (ATOp.transfer q a b x)])
            (by simp) hp.completed }

lemma LInv.step_inv_owner (hL : LInv μ q₀ α C K gid L) (hM : MInv μ C K)
    (hrun : (impl μ q₀ k).run α = some C) (h0 : C.pend q = none) (a b : Acct) (x : ℕ) :
    LInv μ q₀ (α ++ [.inv q (ATOp.transfer q a b x)]) ({ C with
      pend := Function.update C.pend q (some (ATOp.transfer q a b x))
      loc := Function.update C.loc q { C.loc q with pc := .write (newTx (C.loc q) q a b x) } } :
        Cfg μ q₀ k)
      (insert (newTx (C.loc q) q a b x) K)
      (Function.update gid (newTx (C.loc q) q a b x) (respsOf α q).length) L := by
  set tx := newTx (C.loc q) q a b x with htx
  have hnew : tx ∉ K := hM.newTx_not_mem h0 a b x
  have hcnt := idle_counts_of_run hrun h0
  have hgid : ∀ t ∈ K, Function.update gid tx (respsOf α q).length t = gid t := by
    intro t ht; rw [Function.update_of_ne (by rintro rfl; exact hnew ht)]
  have hop : opOf (α ++ [.inv q (ATOp.transfer q a b x)]) (q, (respsOf α q).length) =
      some (ATOp.transfer q a b x) := by
    simp [opOf, opsOf_append, ← hcnt]
  have hdecK : ∀ t r b', Dec C.mem t.a r = some (t, b') → t ∈ K :=
    fun t r b' h => (hM.decK _ _ _ _ h).1
  have hUK : ∀ t, t ∈ U C.mem → t ∈ K := fun t h => by
    obtain ⟨r, hr⟩ := hM.dec_of_U h; exact hdecK t r _ hr
  exact {
    opK := fun t ht => by
      rcases Set.mem_insert_iff.1 ht with rfl | ht
      · rw [Function.update_self]; exact hop
      · rw [hgid t ht]; exact opOf_append_of_some _ (hL.opK t ht)
    inj := fun t ht t' ht' h1 h2 => by
      rcases Set.mem_insert_iff.1 ht with rfl | ht <;>
        rcases Set.mem_insert_iff.1 ht' with rfl | ht'
      · rfl
      · exfalso; rw [Function.update_self, hgid t' ht'] at h2
        have := hL.lt_of_idle hM h0 ht' h1.symm; omega
      · exfalso; rw [Function.update_self, hgid t ht] at h2
        have := hL.lt_of_idle hM h0 ht h1; omega
      · rw [hgid t ht, hgid t' ht'] at h2; exact hL.inj t ht t' ht' h1 h2
    gidLe := fun t ht => by
      simp only [respsOf_append_inv]
      rcases Set.mem_insert_iff.1 ht with rfl | ht
      · right; refine ⟨by rw [Function.update_self]; rfl, Or.inl ?_⟩
        show (Function.update C.loc q _ q).pc.tx? = _
        simp [PC.tx?]
      · rw [hgid t ht]
        by_cases htp : t.p = q
        · exact Or.inl (htp ▸ hL.lt_of_idle hM h0 ht htp)
        · simpa [Function.update_of_ne htp] using hL.gidLe t ht
    gidCur := fun q' tx' h => by
      simp only [respsOf_append_inv]
      by_cases hq' : q' = q
      · subst hq'; simp only [Function.update_self, PC.tx?, Option.some.injEq] at h
        subst h; rw [Function.update_self]
      · simp only [Function.update_of_ne hq'] at h
        rw [hgid tx' ((hM.proc q').txP tx' h).2.1]; exact hL.gidCur _ _ h
    lin := hL.lin.append_inv q _
    bal := hL.bal
    memL := fun y hy => by
      rw [hL.opOf_mem _ hy]
      rcases hL.memL y hy with h | h | ⟨t, ht, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨t, Set.mem_insert_of_mem _ ht, by rw [hgid t ht]; exact h1, h2⟩)
    respS := fun t ht hu => by
      have htK := hUK t hu
      rw [hgid t htK]; exact hL.respS t htK hu
    respF := fun t ht r hr => by
      have htK := hdecK t r _ hr
      rw [hgid t htK]; exact hL.respF t htK r hr
    retR := fun q' r h => by
      simp only [respsOf_append_inv]
      by_cases hq' : q' = q
      · subst hq'; simp at h
      · simp only [Function.update_of_ne hq'] at h; exact hL.retR q' r h
    rscan := fun q' a' h => by
      simp only [respsOf_append_inv]
      by_cases hq' : q' = q
      · subst hq'; simp at h
      · simp only [Function.update_of_ne hq'] at h; exact hL.rscan q' a' h
    decP := hL.decP
    propI := fun q' tx' c t res h hd => by
      by_cases hq' : q' = q
      · subst hq'; simp at h
      · simp only [Function.update_of_ne hq'] at h hd
        have htK := hM.prop_K h
        obtain ⟨h1, h2⟩ := hL.propI q' tx' c t res h hd
        refine ⟨h1, fun hr => ?_⟩
        obtain ⟨S₁, S₂, h3, h4, h5⟩ := h2 hr
        refine ⟨S₁, S₂, h3, h4, ?_⟩
        rw [hgid t htK]
        exact not_precedes_append (Invoked.of_opOf_eq_some (hL.opK t htK)) h5 }

/-! ## Responses -/

lemma LInv.step_ret (hL : LInv μ q₀ α C K gid L) (hM : MInv μ C K) {r : Bool ⊕ ℕ}
    (hpc : (C.loc q).pc = .ret r) :
    LInv μ q₀ (α ++ [.ret q r]) ({ C with
      pend := Function.update C.pend q none
      loc := Function.update C.loc q { C.loc q with pc := .idle } } : Cfg μ q₀ k) K gid L := by
  have hres : ∀ q', respsOf (α ++ [.ret q r]) q' =
      if q' = q then respsOf α q ++ [r] else respsOf α q' := by
    intro q'; by_cases h : q' = q
    · subst h; simp [respsOf_append]
    · simp [respsOf_append, h, Ne.symm h]
  have hnoinv : ∀ x, opOf (α ++ [.ret q r]) x = opOf α x := opOf_append_noinv (by simp)
  obtain ⟨L₁, L₂, o, hsplit, hr⟩ := ObjSpec.exists_split_of_respIn_eq_some (hL.retR q r hpc)
  exact {
    opK := fun t ht => by rw [hnoinv]; exact hL.opK t ht
    inj := hL.inj
    gidLe := fun t ht => by
      by_cases htp : t.p = q
      · left; rw [hres, ite_eq_left htp, List.length_append, List.length_singleton]
        rcases hL.gidLe t ht with h | ⟨h, -⟩ <;> rw [htp] at h <;> omega
      · rw [hres, ite_eq_right htp]; simpa [Function.update_of_ne htp] using hL.gidLe t ht
    gidCur := fun q' tx h => by
      by_cases hq' : q' = q
      · subst hq'; simp [PC.tx?] at h
      · simp only [Function.update_of_ne hq'] at h; rw [hres, ite_eq_right hq']; exact hL.gidCur _ _ h
    lin := hL.lin.append_ret L₁ L₂ o hsplit hr
    bal := hL.bal
    memL := fun y hy => by rw [hnoinv]; exact hL.memL y hy
    respS := hL.respS
    respF := hL.respF
    retR := fun q' r' h => by
      by_cases hq' : q' = q
      · subst hq'; simp at h
      · simp only [Function.update_of_ne hq'] at h; rw [hres, ite_eq_right hq']; exact hL.retR q' r' h
    rscan := fun q' a' h => by
      by_cases hq' : q' = q
      · subst hq'; simp at h
      · simp only [Function.update_of_ne hq'] at h; rw [hres, ite_eq_right hq']; exact hL.rscan q' a' h
    decP := hL.decP
    propI := fun q' tx' c t res h hd => by
      by_cases hq' : q' = q
      · subst hq'; simp at h
      · simp only [Function.update_of_ne hq'] at h hd
        obtain ⟨h1, h2⟩ := hL.propI q' tx' c t res h hd
        refine ⟨h1, fun hr => ?_⟩
        obtain ⟨S₁, S₂, h3, h4, h5⟩ := h2 hr
        exact ⟨S₁, S₂, h3, h4, not_precedes_append
          (Invoked.of_opOf_eq_some (hL.opK t (hM.prop_K h))) h5⟩ }

/-! ## Reads -/

lemma balance_eq_lst (hL : LInv μ q₀ α C K gid L) (a : Acct) :
    balance q₀ a (AS C.mem) = lst (μ := μ) (q₀ := q₀) L a := by
  have := hL.bal a
  simp only [balance]
  change q₀ a + inSum a (U C.mem) - outSum a (U C.mem) = _
  omega

lemma LInv.step_rscan (hL : LInv μ q₀ α C K gid L) (hM : MInv μ C K)
    (hrun : (impl μ q₀ k).run α = some C) {a : Acct} (hpc : (C.loc q).pc = .rscan a) :
    LInv μ q₀ (α ++ [.tau q]) ({ C with
      loc := Function.update C.loc q
        { C.loc q with pc := .ret (.inr (balance q₀ a (AS C.mem))) } } : Cfg μ q₀ k) K gid
      (L ++ [((q, (respsOf α q).length), ATOp.read a)]) := by
  have hpend := (hM.proc q).pendR a hpc
  have hop0 := cur_op_of_run hrun hpend
  have hop : opOf (α ++ [.tau q]) (q, (respsOf α q).length) = some (ATOp.read a) :=
    opOf_append_of_some _ hop0
  have hnotL := hL.rscan q a hpc
  have hδ : (AT μ q₀).δ (lst (μ := μ) (q₀ := q₀) L) (ATOp.read a) =
      (lst (μ := μ) (q₀ := q₀) L, .inr (lst (μ := μ) (q₀ := q₀) L a)) := rfl
  have hlst : lst (μ := μ) (q₀ := q₀) (L ++ [((q, (respsOf α q).length), ATOp.read a)]) =
      lst (μ := μ) (q₀ := q₀) L := by
    show linState (A := AT μ q₀) _ = _; rw [linState_concat, hδ]
  have hpushed (y : OpId (Fin n)) (hy : y ∈ L.map Prod.fst) :
      lrs (μ := μ) (q₀ := q₀) (L ++ [((q, (respsOf α q).length), ATOp.read a)]) y =
        lrs (μ := μ) (q₀ := q₀) L y := ObjSpec.respIn_append_of_mem hy _
  exact {
    opK := fun t ht => opOf_append_of_some _ (hL.opK t ht)
    inj := hL.inj
    gidLe := fun t ht => by
      simp only [respsOf_append_tau]
      by_cases htp : t.p = q
      · left
        rcases hL.gidLe t ht with h | ⟨-, h⟩
        · exact h
        · rw [htp, hpc] at h; simp [PC.tx?] at h
      · simpa [Function.update_of_ne htp] using hL.gidLe t ht
    gidCur := fun q' tx h => by
      simp only [respsOf_append_tau]
      by_cases hq' : q' = q
      · subst hq'; simp [PC.tx?] at h
      · simp only [Function.update_of_ne hq'] at h; exact hL.gidCur _ _ h
    lin := (hL.lin.append_tau q).push hop hnotL (not_completed_of_eq (by simp))
    bal := by rw [hlst]; exact hL.bal
    memL := fun y hy => by
      rcases List.mem_append.1 hy with hy | hy
      · rw [hL.opOf_mem _ hy]; exact hL.memL y hy
      · simp only [List.mem_singleton] at hy; subst hy
        exact Or.inl ⟨a, hop⟩
    respS := fun t ht hu => by
      have := hL.respS t ht hu; rw [hpushed _ (ObjSpec.mem_of_respIn_eq_some this)]; exact this
    respF := fun t ht r hr => by
      have := hL.respF t ht r hr; rw [hpushed _ (ObjSpec.mem_of_respIn_eq_some this)]; exact this
    retR := fun q' r h => by
      simp only [respsOf_append_tau]
      by_cases hq' : q' = q
      · subst hq'; simp only [Function.update_self, PC.ret.injEq] at h; subst h
        show lrs (μ := μ) (q₀ := q₀) _ _ = _
        rw [lrs_concat_self _ _ _ hnotL, hδ, balance_eq_lst hL]
      · simp only [Function.update_of_ne hq'] at h
        have := hL.retR q' r h; rw [hpushed _ (ObjSpec.mem_of_respIn_eq_some this)]; exact this
    rscan := fun q' a' h => by
      simp only [respsOf_append_tau]
      by_cases hq' : q' = q
      · subst hq'; simp at h
      · simp only [Function.update_of_ne hq'] at h
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton, Prod.mk.injEq, not_or]
        exact ⟨hL.rscan q' a' h, fun h' => hq' h'.1⟩
    decP := fun a' r t h hu => by rw [hlst]; exact hL.decP a' r t h hu
    propI := fun q' tx c t res h hd => by
      by_cases hq' : q' = q
      · subst hq'; simp at h
      · simp only [Function.update_of_ne hq'] at h hd
        obtain ⟨h1, h2⟩ := hL.propI q' tx c t res h hd
        refine ⟨fun hr => by rw [hlst]; exact h1 hr, fun hr => ?_⟩
        obtain ⟨S₁, S₂, h3, h4, h5⟩ := h2 hr
        refine ⟨S₁, S₂ ++ [((q, (respsOf α q).length), ATOp.read a)], by rw [h3]; simp,
          h4, ?_⟩
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact not_precedes_append (Invoked.of_opOf_eq_some (hL.opK t (hM.prop_K h))) h5 y hy
        · simp only [List.mem_singleton] at hy; subst hy
          intro hp
          exact not_completed_of_eq (α := α ++ [.tau q]) (by simp) hp.completed }

end CryptoCons.Fig3
