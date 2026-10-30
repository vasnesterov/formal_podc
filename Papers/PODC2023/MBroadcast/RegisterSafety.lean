import Papers.PODC2023.MBroadcast.Register

/-!
# Theorem 2, safety: Algorithm 3 is linearizable

Every history of Algorithm 3 whose MBroadcast trace satisfies the safety properties of
MBroadcast is linearizable for an MWMR register (`alg3_linearizable`).

The proof is the paper's (full version, App. A.2): the timestamp `ts(o)` of an operation is
`⟨tᵢ, i⟩` for a write and `clockᵢ` at line 6 for a read; if `o₁` returns before `o₂` starts then
`ts(o₁) ≤ ts(o₂)`, strictly if `o₂` is a write. The real-time fact comes from Property 1 between
the last message of `o₁` and the `synch` message of `o₂`: mutual ordering forces the process of
`o₂` to mdeliver the last message of `o₁` before its own `synch`, hence before line 2/5.
We conclude with the timestamp criterion `Cslib.SharedMemory.TSLin`.

The invariant `Inv` carries ghost data: the list `W` of writes that have chosen their timestamp
(line 2) and the timestamp map `tok`.
-/

set_option linter.unusedSectionVars false

namespace Podc.MBroadcast.Alg3

open Cslib.SharedMemory

variable {P V : Type} [LinearOrder P] [DecidableEq V] {v₀ : V}

/-! ## Basic lemmas -/

@[simp] lemma upd_loc_self (C : Cfg P V) (p : P) (l : Loc P V) (es) :
    (C.upd p l es).loc p = l := by simp [Cfg.upd]

@[simp] lemma upd_loc_ne (C : Cfg P V) {p q : P} (l : Loc P V) (es) (h : q ≠ p) :
    (C.upd p l es).loc q = C.loc q := by simp [Cfg.upd, h]

@[simp] lemma upd_log (C : Cfg P V) (p : P) (l : Loc P V) (es) :
    (C.upd p l es).log = C.log ++ es := rfl

lemma bot_lt_ts (d : ℕ) (p : P) : (⊥ : TS P) < ts d p := WithBot.bot_lt_coe _

lemma ts_inj {d d' : ℕ} {p p' : P} (h : ts d p = ts d' p') : d = d' ∧ p = p' := by
  have := WithBot.coe_injective h
  have := toLex.injective this
  simp only [Prod.mk.injEq] at this
  exact this

/-- The phase is a final wait (line 3 or line 6). -/
def Phase.isFin : Phase P V → Bool
  | .wFin _ _ => true
  | .rFin _ _ => true
  | _ => false

/-- Operation `x` has completed, or is at its final wait (it has chosen its timestamp). -/
def Past (C : Cfg P V) (x : OpId P) : Prop :=
  x.2 < (C.loc x.1).k ∨ (x.2 = (C.loc x.1).k ∧ (C.loc x.1).phase.isFin = true)

/-- `(v, c)` is the initial pair or the pair of a write of `W`. -/
def ValOK (v₀ : V) (h : List (Label P (register V v₀))) (W : List (OpId P))
    (tok : OpId P → TS P) (v : V) (c : TS P) : Prop :=
  (c = ⊥ ∧ v = v₀) ∨ ∃ w ∈ W, tok w = c ∧ opOf h w = some (.write v)

lemma ValOK.mono {h h' : List (Label P (register V v₀))} {W W' : List (OpId P)}
    {tok tok' : OpId P → TS P} {v : V} {c : TS P} (hv : ValOK v₀ h W tok v c)
    (hh : ∀ x o, opOf h x = some o → opOf h' x = some o) (hW : ∀ w ∈ W, w ∈ W')
    (ht : ∀ w ∈ W, tok' w = tok w) : ValOK v₀ h' W' tok' v c := by
  rcases hv with hv | ⟨w, hw, h1, h2⟩
  · exact Or.inl hv
  · exact Or.inr ⟨w, hW w hw, (ht w hw).trans h1, hh _ _ h2⟩

/-- The invariant of Algorithm 3. -/
structure Inv (h : List (Label P (register V v₀))) (C : Cfg P V) (W : List (OpId P))
    (tok : OpId P → TS P) : Prop where
  wf : WellFormed h
  resps : ∀ p, (respsOf h p).length = (C.loc p).k
  ops : ∀ p, (opsOf h p).length = (C.loc p).k + if (C.loc p).phase = .idle then 0 else 1
  op_w : ∀ p v, ((C.loc p).phase = .wSync v ∨ ∃ c, (C.loc p).phase = .wFin v c) →
    opOf h (p, (C.loc p).k) = some (.write v)
  op_r : ∀ p, ((C.loc p).phase = .rSync ∨ ∃ v c, (C.loc p).phase = .rFin v c) →
    opOf h (p, (C.loc p).k) = some .read
  fin_w : ∀ p v c, (C.loc p).phase = .wFin v c →
    (p, (C.loc p).k) ∈ W ∧ tok (p, (C.loc p).k) = c
  fin_r : ∀ p v c, (C.loc p).phase = .rFin v c →
    tok (p, (C.loc p).k) = c ∧ ValOK v₀ h W tok v c
  val_ok : ∀ p, ValOK v₀ h W tok (C.loc p).val (C.loc p).clock
  msg_ok : ∀ q k v c, Ev.bc q (Msg.write k v c) ∈ C.log →
    ValOK v₀ h W tok v c ∧ Past C (q, k) ∧ tok (q, k) = c
  synch_ok : ∀ q k, Ev.bc q (Msg.synch k : Msg P V) ∈ C.log →
    k < (C.loc q).k ∨ (k = (C.loc q).k ∧ (C.loc q).phase ≠ .idle)
  W_mem : ∀ x ∈ W, (∃ v, opOf h x = some (.write v)) ∧ Past C x ∧ ∃ d, tok x = ts d x.1
  W_nodup : W.Nodup
  W_complete : ∀ x v, opOf h x = some (.write v) → Completed h x → x ∈ W
  write_resp : ∀ x v r, opOf h x = some (.write v) → respOf h x = some r → r = v
  read_resp : ∀ x r, opOf h x = some .read → respOf h x = some r → ValOK v₀ h W tok r (tok x)
  fin_dl : ∀ x, Completed h x → ∃ v, Ev.dl x.1 x.1 (Msg.write x.2 v (tok x)) ∈ C.log
  clock_ge : ∀ p q k v c, Ev.dl p q (Msg.write k v c) ∈ C.log → c ≤ (C.loc p).clock
  prec_sync : ∀ a b, Precedes h a b → Invoked h b →
    ∃ i v, C.log[i]? = some (Ev.dl a.1 a.1 (Msg.write a.2 v (tok a))) ∧
      Ev.bc b.1 (Msg.synch b.2) ∉ C.log.take i
  prec_past : ∀ a b, Precedes h a b → Past C b →
    (∀ v, opOf h b = some (.write v) → tok a < tok b) ∧ (opOf h b = some .read → tok a ≤ tok b)

section Lemmas

variable {h : List (Label P (register V v₀))} {C : Cfg P V} {W : List (OpId P)}
  {tok : OpId P → TS P}

lemma Inv.invoked_of_past (I : Inv h C W tok) {x : OpId P} (hx : Past C x) : Invoked h x := by
  have h1 := I.ops x.1
  unfold Invoked
  rcases hx with hx | ⟨hx, hf⟩
  · rw [h1]; omega
  · have : (C.loc x.1).phase ≠ .idle := by
      intro h0; rw [h0] at hf; simp [Phase.isFin] at hf
    rw [h1, if_neg this]; omega

lemma Inv.past_of_completed (I : Inv h C W tok) {x : OpId P} (hx : Completed h x) : Past C x := by
  left; have := I.resps x.1; unfold Completed at hx; omega

lemma Inv.not_completed_cur (I : Inv h C W tok) (p : P) : ¬ Completed h (p, (C.loc p).k) := by
  unfold Completed; rw [I.resps p]; simp

lemma Inv.not_past_cur (I : Inv h C W tok) {p : P} (hp : (C.loc p).phase.isFin = false) :
    ¬ Past C (p, (C.loc p).k) := by
  rintro (h1 | ⟨-, h2⟩)
  · simp at h1
  · rw [hp] at h2; cases h2

/-- The real-time argument (Property 1): if `a` precedes the current operation `b` of `p`, and
`p` has mdelivered its own `synch` of `b`, then `tok a ≤ clock_p`. -/
lemma Inv.tok_le_clock (I : Inv h C W tok) (hs : Validity C.log ∧ MutualOrdering C.log) {a : OpId P} {p : P}
    (hab : Precedes h a (p, (C.loc p).k)) (hinv : Invoked h (p, (C.loc p).k))
    (hdl : Ev.dl p p (Msg.synch (C.loc p).k) ∈ C.log) : tok a ≤ (C.loc p).clock := by
  obtain ⟨i, v, hi, hni⟩ := I.prec_sync a _ hab hinv
  have hDB : DelivBefore C.log a.1 (Msg.write a.2 v (tok a)) p (Msg.synch (C.loc p).k) := by
    refine ⟨i, hi, fun hmem => hni ?_⟩
    obtain ⟨j, hj, hj'⟩ := exists_lt_of_mem_take hmem
    obtain ⟨l, hl, hl'⟩ := exists_lt_of_mem_take (hs.1 j _ _ _ hj')
    exact mem_take_of_getElem? hl' (by omega)
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hdl
  by_contra hc
  refine hs.2 _ _ _ _ (by simp) ⟨hDB, j, hj, fun hmem => hc ?_⟩
  exact I.clock_ge _ _ _ _ _ (List.mem_of_mem_take hmem)

end Lemmas

/-! ## The initial configuration -/

lemma inv_init : Inv ([] : List (Label P (register V v₀))) (initCfg v₀) [] (fun _ => ⊥) where
  wf := by intro β ℓ γ h; simp at h
  resps _ := rfl
  ops _ := rfl
  op_w p v h := by simp [initCfg] at h
  op_r p h := by simp [initCfg] at h
  fin_w p v c h := by simp [initCfg] at h
  fin_r p v c h := by simp [initCfg] at h
  val_ok _ := Or.inl ⟨rfl, rfl⟩
  msg_ok _ _ _ _ h := by simp [initCfg] at h
  synch_ok _ _ h := by simp [initCfg] at h
  W_mem _ h := by simp at h
  W_nodup := List.nodup_nil
  W_complete _ _ h := by simp [opOf] at h
  write_resp _ _ _ h := by simp [opOf] at h
  read_resp _ _ h := by simp [opOf] at h
  fin_dl _ h := by simp [Completed] at h
  clock_ge _ _ _ _ _ h := by simp [initCfg] at h
  prec_sync _ _ _ h := by simp [Invoked] at h
  prec_past _ _ h := by obtain ⟨β, γ, e, hc, -⟩ := h; simp at e; simp [e.1, Completed] at hc

/-! ## From the invariant to linearizability -/

theorem Inv.tsLin {h : List (Label P (register V v₀))} {C : Cfg P V} {W : List (OpId P)}
    {tok : OpId P → TS P} (I : Inv h C W tok) : TSLin h W tok where
  wellFormed := I.wf
  W_nodup := I.W_nodup
  W_write x hx := (I.W_mem x hx).1
  W_complete := I.W_complete
  write_resp := I.write_resp
  W_inj a ha b hb hab := by
    obtain ⟨⟨va, hva⟩, hpa, da, hta⟩ := I.W_mem a ha
    obtain ⟨⟨vb, hvb⟩, hpb, db, htb⟩ := I.W_mem b hb
    obtain ⟨-, hp⟩ := ts_inj (hta.symm.trans (hab.trans htb))
    obtain ⟨p, i⟩ := a; obtain ⟨q, j⟩ := b
    simp only at hp; subst hp
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hprec := I.wf.precedes_of_lt hij (I.invoked_of_past hpb)
      have := (I.prec_past _ _ hprec hpb).1 vb hvb
      rw [hab] at this; exact absurd this (lt_irrefl _)
    · rfl
    · have hprec := I.wf.precedes_of_lt hij (I.invoked_of_past hpa)
      have := (I.prec_past _ _ hprec hpa).1 va hva
      rw [hab] at this; exact absurd this (lt_irrefl _)
  W_pos x hx := by
    obtain ⟨-, -, d, ht⟩ := I.W_mem x hx; rw [ht]; exact bot_lt_ts _ _
  read_val x r hx hr := I.read_resp x r hx hr
  prec_W a b hab hb := by
    obtain ⟨⟨v, hv⟩, hp, -⟩ := I.W_mem b hb
    exact (I.prec_past a b hab hp).1 v hv
  prec_R a b hab hb hc := (I.prec_past a b hab (I.past_of_completed hc)).2 hb

/-! ## Preservation: invocations -/

section Steps

variable {h : List (Label P (register V v₀))} {C : Cfg P V} {W : List (OpId P)}
  {tok : OpId P → TS P}

/-- Invocation steps (`invW`, `invR`): `p` invokes `o`, enters phase `ph` and mbroadcasts its
`synch`. -/
lemma Inv.invoke (I : Inv h C W tok) {p : P} (o : RWOp V) (ph : Phase P V)
    (hidle : (C.loc p).phase = .idle) (hne : ph ≠ .idle) (hfin : ph.isFin = false)
    (hw : ∀ v, (ph = .wSync v ∨ ∃ c, ph = .wFin v c) → o = .write v)
    (hr : (ph = .rSync ∨ ∃ v c, ph = .rFin v c) → o = .read) :
    Inv (h ++ [.inv p o]) (C.upd p { C.loc p with phase := ph } [.bc p (.synch (C.loc p).k)])
      W tok := by
  set C' := C.upd p { C.loc p with phase := ph } [.bc p (.synch (C.loc p).k)] with hC'
  have hops : (opsOf h p).length = (C.loc p).k := by rw [I.ops p, hidle]; simp
  have hopOf : ∀ x o', opOf h x = some o' → opOf (h ++ [.inv p o]) x = some o' :=
    fun x o' hx => opOf_append_of_eq_some hx _
  have hcomp : ∀ x, Completed (h ++ [.inv p o]) x ↔ Completed h x :=
    completed_append_of_not_ret (by intro q r h; cases h)
  have hresp : ∀ x, respOf (h ++ [.inv p o]) x = respOf h x :=
    respOf_append_of_not_ret (by intro q r h; cases h)
  have hk : ∀ q, (C'.loc q).k = (C.loc q).k := by
    intro q; by_cases hq : q = p
    · subst hq; simp [hC']
    · simp [hC', hq]
  have hvc : ∀ q, (C'.loc q).val = (C.loc q).val ∧ (C'.loc q).clock = (C.loc q).clock := by
    intro q; by_cases hq : q = p
    · subst hq; simp [hC']
    · simp [hC', hq]
  have hPast : ∀ x, Past C' x ↔ Past C x := by
    rintro ⟨q, i⟩
    by_cases hq : q = p
    · subst hq; simp only [Past, hC', upd_loc_self, hidle, hfin]; simp [Phase.isFin]
    · simp [Past, hC', hq]
  have hlog : C'.log = C.log ++ [.bc p (.synch (C.loc p).k)] := rfl
  have hVal : ∀ v c, ValOK v₀ h W tok v c → ValOK v₀ (h ++ [.inv p o]) W tok v c :=
    fun v c hv => hv.mono hopOf (fun _ h => h) (fun _ _ => rfl)
  refine ⟨I.wf.append_inv (by rw [hops, I.resps]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    I.W_nodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; rw [respsOf_append_inv, hk]; exact I.resps q
  · intro q; by_cases hq : q = p
    · subst hq; simp [hC', hne, hops]
    · have := I.ops q; simp [hC', hq, Ne.symm hq] at this ⊢; exact this
  · intro q v hq'; by_cases hq : q = p
    · subst hq; simp only [hC', upd_loc_self] at hq' ⊢
      rw [opOf_concat_inv, if_pos (by rw [hops]), hw v hq']
    · simp only [hC', upd_loc_ne _ _ _ hq] at hq' ⊢; exact hopOf _ _ (I.op_w q v hq')
  · intro q hq'; by_cases hq : q = p
    · subst hq; simp only [hC', upd_loc_self] at hq' ⊢
      rw [opOf_concat_inv, if_pos (by rw [hops]), hr hq']
    · simp only [hC', upd_loc_ne _ _ _ hq] at hq' ⊢; exact hopOf _ _ (I.op_r q hq')
  · intro q v c hq'; by_cases hq : q = p
    · subst hq; simp only [hC', upd_loc_self] at hq'; rw [hq'] at hfin; simp [Phase.isFin] at hfin
    · simp only [hC', upd_loc_ne _ _ _ hq] at hq' ⊢; exact I.fin_w q v c hq'
  · intro q v c hq'; by_cases hq : q = p
    · subst hq; simp only [hC', upd_loc_self] at hq'; rw [hq'] at hfin; simp [Phase.isFin] at hfin
    · simp only [hC', upd_loc_ne _ _ _ hq] at hq' ⊢
      exact ⟨(I.fin_r q v c hq').1, hVal _ _ (I.fin_r q v c hq').2⟩
  · intro q; rw [(hvc q).1, (hvc q).2]; exact hVal _ _ (I.val_ok q)
  · intro q k v c hm
    rw [hlog, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨h1, h2, h3⟩ := I.msg_ok q k v c hm
      exact ⟨hVal _ _ h1, (hPast _).2 h2, h3⟩
    · simp at hm
  · intro q k hm
    rw [hlog, List.mem_append] at hm
    by_cases hq : q = p
    · subst hq
      simp only [hC', upd_loc_self]
      rcases hm with hm | hm
      · rcases I.synch_ok q k hm with h1 | ⟨-, h1⟩
        · exact Or.inl h1
        · exact absurd hidle h1
      · simp at hm; exact Or.inr ⟨hm, hne⟩
    · simp only [hC', upd_loc_ne _ _ _ hq]
      rcases hm with hm | hm
      · exact I.synch_ok q k hm
      · simp at hm; exact absurd hm.1 hq
  · intro x hx
    obtain ⟨⟨v, hv⟩, h2, h3⟩ := I.W_mem x hx
    exact ⟨⟨v, hopOf _ _ hv⟩, (hPast x).2 h2, h3⟩
  · intro x v hv hc
    rw [hcomp] at hc
    have hinv := I.wf.invoked_of_completed hc
    rw [opOf_append_of_invoked hinv] at hv
    exact I.W_complete x v hv hc
  · intro x v r hv hr'
    rw [hresp] at hr'
    have hinv := I.wf.invoked_of_completed (Completed.of_respOf_eq_some hr')
    rw [opOf_append_of_invoked hinv] at hv
    exact I.write_resp x v r hv hr'
  · intro x r hv hr'
    rw [hresp] at hr'
    have hinv := I.wf.invoked_of_completed (Completed.of_respOf_eq_some hr')
    rw [opOf_append_of_invoked hinv] at hv
    exact hVal _ _ (I.read_resp x r hv hr')
  · intro x hx
    obtain ⟨v, hv⟩ := I.fin_dl x ((hcomp x).1 hx)
    exact ⟨v, by rw [hlog]; exact List.mem_append_left _ hv⟩
  · intro p' q k v c hm
    rw [hlog, List.mem_append] at hm
    rcases hm with hm | hm
    · rw [(hvc p').2]; exact I.clock_ge p' q k v c hm
    · simp at hm
  · intro a b hab hb
    by_cases hbi : Invoked h b
    · obtain ⟨i, v, hi, hni⟩ := I.prec_sync a b (hab.of_append_of_invoked hbi) hbi
      have hil : i < C.log.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
      refine ⟨i, v, ?_, ?_⟩
      · rw [hlog, List.getElem?_append_left hil]; exact hi
      · rwa [hlog, List.take_append_of_le_length hil.le]
    · -- `b` is the new operation of `p`
      have hb' : b = (p, (opsOf h p).length) := by
        obtain ⟨q, i⟩ := b
        simp only [Invoked, opsOf_append, List.length_append] at hb hbi
        by_cases hq : q = p
        · subst hq; simp at hb; ext <;> simp; omega
        · simp [Ne.symm hq] at hb; omega
      subst hb'
      have ha : Completed h a := precedes_append_inv_iff.1 hab
      obtain ⟨v, hv⟩ := I.fin_dl a ha
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hv
      have hil : i < C.log.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
      refine ⟨i, v, by rw [hlog, List.getElem?_append_left hil]; exact hi, ?_⟩
      rw [hlog, List.take_append_of_le_length hil.le, hops]
      intro hm
      rcases I.synch_ok p _ (List.mem_of_mem_take hm) with h1 | ⟨-, h1⟩
      · exact lt_irrefl _ h1
      · exact h1 hidle
  · intro a b hab hb
    rw [hPast] at hb
    have hbi := I.invoked_of_past hb
    rw [opOf_append_of_invoked hbi]
    exact I.prec_past a b (hab.of_append_of_invoked hbi) hb

@[simp] lemma handle_k (m : Msg P V) (l : Loc P V) : (handle m l).k = l.k := by
  cases m <;> simp only [handle] <;> split_ifs <;> rfl

@[simp] lemma handle_phase (m : Msg P V) (l : Loc P V) : (handle m l).phase = l.phase := by
  cases m <;> simp only [handle] <;> split_ifs <;> rfl

lemma handle_clock_ge (m : Msg P V) (l : Loc P V) : l.clock ≤ (handle m l).clock := by
  cases m with
  | synch k => exact le_rfl
  | write k v c =>
    simp only [handle]; split_ifs with h
    · exact h.le
    · exact le_rfl

lemma handle_val (m : Msg P V) (l : Loc P V) :
    ((handle m l).val = l.val ∧ (handle m l).clock = l.clock) ∨
      ∃ k v c, m = .write k v c ∧ (handle m l).val = v ∧ (handle m l).clock = c := by
  cases m with
  | synch k => left; exact ⟨rfl, rfl⟩
  | write k v c =>
    simp only [handle]; split_ifs
    · right; exact ⟨k, v, c, rfl, rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩

lemma handle_clock_ge_msg (k : ℕ) (v : V) (c : TS P) (l : Loc P V) :
    c ≤ (handle (.write k v c) l).clock := by
  simp only [handle]; split_ifs with h
  · exact le_rfl
  · exact not_lt.1 h

/-- Delivery steps (`dlv`): `p` mdelivers `m` from `q` and runs line 8. -/
lemma Inv.deliver (I : Inv h C W tok) {p q : P} {m : Msg P V}
    (hv : Validity (C.log ++ [.dl p q m])) :
    Inv h (C.upd p (handle m (C.loc p)) [.dl p q m]) W tok := by
  set C' := C.upd p (handle m (C.loc p)) [.dl p q m] with hC'
  have hk : ∀ r, (C'.loc r).k = (C.loc r).k ∧ (C'.loc r).phase = (C.loc r).phase := by
    intro r; by_cases hr : r = p
    · subst hr; simp [hC']
    · simp [hC', hr]
  have hPast : ∀ x, Past C' x ↔ Past C x := by
    rintro ⟨r, i⟩; simp only [Past, (hk r).1, (hk r).2]
  have hlog : C'.log = C.log ++ [.dl p q m] := rfl
  have hbc : ∀ e, e ∈ C'.log → (∀ a b c, e ≠ .dl a b c) → e ∈ C.log := by
    intro e he hne; rw [hlog, List.mem_append] at he
    rcases he with he | he
    · exact he
    · simp at he; exact absurd he (hne _ _ _)
  refine ⟨I.wf, fun r => (hk r).1 ▸ I.resps r, fun r => by rw [(hk r).1, (hk r).2]; exact I.ops r,
    fun r v hr => by rw [(hk r).1]; rw [(hk r).2] at hr; exact I.op_w r v hr,
    fun r hr => by rw [(hk r).1]; rw [(hk r).2] at hr; exact I.op_r r hr,
    fun r v c hr => by rw [(hk r).1]; rw [(hk r).2] at hr; exact I.fin_w r v c hr,
    fun r v c hr => by rw [(hk r).1]; rw [(hk r).2] at hr; exact I.fin_r r v c hr,
    ?_, ?_, ?_, ?_, I.W_nodup, I.W_complete, I.write_resp, I.read_resp, ?_, ?_, ?_, ?_⟩
  · intro r; by_cases hr : r = p
    · subst hr; simp only [hC', upd_loc_self]
      rcases handle_val m (C.loc r) with ⟨h1, h2⟩ | ⟨k, v, c, rfl, h1, h2⟩
      · rw [h1, h2]; exact I.val_ok r
      · rw [h1, h2]
        have := hv C.log.length r q (.write k v c) (by simp)
        rw [List.take_left' rfl] at this
        exact (I.msg_ok q k v c this).1
    · simp only [hC', upd_loc_ne _ _ _ hr]; exact I.val_ok r
  · intro r k v c hm
    obtain ⟨h1, h2, h3⟩ := I.msg_ok r k v c (hbc _ hm (by intro a b c h; cases h))
    exact ⟨h1, (hPast _).2 h2, h3⟩
  · intro r k hm
    rw [(hk r).1, (hk r).2]; exact I.synch_ok r k (hbc _ hm (by intro a b c h; cases h))
  · intro x hx; obtain ⟨h1, h2, h3⟩ := I.W_mem x hx; exact ⟨h1, (hPast x).2 h2, h3⟩
  · intro x hx; obtain ⟨v, hv⟩ := I.fin_dl x hx; exact ⟨v, List.mem_append_left _ hv⟩
  · intro r q' k v c hm
    rw [hlog, List.mem_append] at hm
    by_cases hr : r = p
    · subst hr; simp only [hC', upd_loc_self]
      rcases hm with hm | hm
      · exact (I.clock_ge r q' k v c hm).trans (handle_clock_ge _ _)
      · simp at hm; obtain ⟨-, -, rfl⟩ := hm; exact handle_clock_ge_msg _ _ _ _
    · simp only [hC', upd_loc_ne _ _ _ hr]
      rcases hm with hm | hm
      · exact I.clock_ge r q' k v c hm
      · simp at hm; exact absurd hm.1 hr
  · intro a b hab hb
    obtain ⟨i, v, hi, hni⟩ := I.prec_sync a b hab hb
    have hil : i < C.log.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
    exact ⟨i, v, by rw [hlog, List.getElem?_append_left hil]; exact hi,
      by rwa [hlog, List.take_append_of_le_length hil.le]⟩
  · intro a b hab hb; exact I.prec_past a b hab ((hPast b).1 hb)

/-- Lines 2–3 (`line2`): the writer chooses `⟨d, p⟩ > clock` and mbroadcasts its write. -/
lemma Inv.line2 (I : Inv h C W tok) (hsafe : Validity C.log ∧ MutualOrdering C.log) {p : P} {v : V} {d : ℕ}
    (hph : (C.loc p).phase = .wSync v) (hs : .dl p p (.synch (C.loc p).k) ∈ C.log)
    (hd : (C.loc p).clock < ts d p) :
    Inv h (C.upd p { C.loc p with phase := .wFin v (ts d p) }
        [.bc p (.write (C.loc p).k v (ts d p))])
      (W ++ [(p, (C.loc p).k)]) (Function.update tok (p, (C.loc p).k) (ts d p)) := by
  have hfin0 : (C.loc p).phase.isFin = false := by rw [hph]; rfl
  have hnotP : ¬ Past C (p, (C.loc p).k) := I.not_past_cur hfin0
  have hnotW : (p, (C.loc p).k) ∉ W := fun hw => hnotP (I.W_mem _ hw).2.1
  have ht : ∀ x, x ≠ (p, (C.loc p).k) →
      Function.update tok (p, (C.loc p).k) (ts d p) x = tok x :=
    fun x hx => Function.update_of_ne hx _ _
  have htk : Function.update tok (p, (C.loc p).k) (ts d p) (p, (C.loc p).k) = ts d p :=
    Function.update_self _ _ _
  have htW : ∀ w ∈ W, Function.update tok (p, (C.loc p).k) (ts d p) w = tok w :=
    fun w hw => ht w (fun he => hnotW (he ▸ hw))
  have hop : opOf h (p, (C.loc p).k) = some (.write v) := I.op_w p v (Or.inl hph)
  have hPast : ∀ x, Past (C.upd p { C.loc p with phase := .wFin v (ts d p) }
      [.bc p (.write (C.loc p).k v (ts d p))]) x ↔ Past C x ∨ x = (p, (C.loc p).k) := by
    rintro ⟨q, i⟩
    rcases eq_or_ne q p with rfl | hq
    · have e2 : Past C (q, i) ↔ i < (C.loc q).k := by
        simp only [Past, hfin0]; simp
      rw [e2]; simp only [Past, upd_loc_self, Prod.mk.injEq, true_and]; simp [Phase.isFin]
    · simp [Past, upd_loc_ne _ _ _ hq, hq]
  have hVal : ∀ v' c, ValOK v₀ h W tok v' c →
      ValOK v₀ h (W ++ [(p, (C.loc p).k)]) (Function.update tok (p, (C.loc p).k) (ts d p)) v' c :=
    fun v' c hv => hv.mono (fun _ _ h => h) (fun w hw => List.mem_append_left _ hw) htW
  have hne_cur : ∀ q, q ≠ p → (q, (C.loc q).k) ≠ (p, (C.loc p).k) :=
    fun q hq he => hq (Prod.mk.inj he).1
  have hcomp_ne : ∀ x, Completed h x → x ≠ (p, (C.loc p).k) := fun x hx he =>
    I.not_completed_cur p (he ▸ hx)
  refine ⟨I.wf, fun q => ?_, fun q => ?_, fun q v' hq' => ?_, fun q hq' => ?_, fun q v' c hq' => ?_,
    fun q v' c hq' => ?_, fun q => ?_, ?_, ?_, ?_, ?_, ?_, I.write_resp, ?_, ?_, ?_, ?_, ?_⟩
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self]; exact I.resps q
    · rw [upd_loc_ne _ _ _ hq]; exact I.resps q
  · rcases eq_or_ne q p with rfl | hq
    · have := I.ops q; rw [hph] at this; simp only [upd_loc_self]; simpa using this
    · rw [upd_loc_ne _ _ _ hq]; exact I.ops q
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self] at hq' ⊢
      rcases hq' with hq' | ⟨c, hq'⟩ <;> cases hq'
      exact hop
    · rw [upd_loc_ne _ _ _ hq] at hq' ⊢; exact I.op_w q v' hq'
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self] at hq'
      rcases hq' with hq' | ⟨_, _, hq'⟩ <;> cases hq'
    · rw [upd_loc_ne _ _ _ hq] at hq' ⊢; exact I.op_r q hq'
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self] at hq' ⊢
      cases hq'
      exact ⟨List.mem_append_right _ (by simp), htk⟩
    · rw [upd_loc_ne _ _ _ hq] at hq' ⊢
      obtain ⟨h1, h2⟩ := I.fin_w q v' c hq'
      exact ⟨List.mem_append_left _ h1, by rw [ht _ (hne_cur q hq), h2]⟩
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self] at hq'; cases hq'
    · rw [upd_loc_ne _ _ _ hq] at hq' ⊢
      obtain ⟨h1, h2⟩ := I.fin_r q v' c hq'
      exact ⟨by rw [ht _ (hne_cur q hq), h1], hVal _ _ h2⟩
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self]; exact hVal _ _ (I.val_ok q)
    · rw [upd_loc_ne _ _ _ hq]; exact hVal _ _ (I.val_ok q)
  · intro q k' v' c hm
    rw [upd_log, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨h1, h2, h3⟩ := I.msg_ok q k' v' c hm
      have hne : (q, k') ≠ (p, (C.loc p).k) := fun he => hnotP (he ▸ h2)
      exact ⟨hVal _ _ h1, (hPast _).2 (Or.inl h2), by rw [ht _ hne, h3]⟩
    · simp only [List.mem_singleton, Ev.bc.injEq, Msg.write.injEq] at hm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      exact ⟨Or.inr ⟨(q, (C.loc q).k), List.mem_append_right _ (by simp), htk, hop⟩,
        (hPast _).2 (Or.inr rfl), htk⟩
  · intro q k' hm
    rw [upd_log, List.mem_append] at hm
    rcases hm with hm | hm
    · rcases eq_or_ne q p with rfl | hq
      · simp only [upd_loc_self]
        rcases I.synch_ok q k' hm with h1 | ⟨h1, -⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, by simp⟩
      · rw [upd_loc_ne _ _ _ hq]; exact I.synch_ok q k' hm
    · simp at hm
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨h1, h2, d', h3⟩ := I.W_mem x hx
      exact ⟨h1, (hPast x).2 (Or.inl h2), d', by rw [htW x hx, h3]⟩
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨⟨v, hop⟩, (hPast _).2 (Or.inr rfl), d, htk⟩
  · rw [List.nodup_append]
    exact ⟨I.W_nodup, List.nodup_singleton _, by
      intro a ha b hb hab; simp only [List.mem_singleton] at hb; subst hb hab; exact hnotW ha⟩
  · intro x v' hv hc; exact List.mem_append_left _ (I.W_complete x v' hv hc)
  · intro x r hv hr
    rw [ht x (hcomp_ne x (Completed.of_respOf_eq_some hr))]
    exact hVal _ _ (I.read_resp x r hv hr)
  · intro x hx
    rw [ht x (hcomp_ne x hx)]
    obtain ⟨v', hv⟩ := I.fin_dl x hx
    exact ⟨v', List.mem_append_left _ hv⟩
  · intro q q' k' v' c hm
    rw [upd_log, List.mem_append] at hm
    rcases hm with hm | hm
    · rcases eq_or_ne q p with rfl | hq
      · simp only [upd_loc_self]; exact I.clock_ge q q' k' v' c hm
      · rw [upd_loc_ne _ _ _ hq]; exact I.clock_ge q q' k' v' c hm
    · simp at hm
  · intro a b hab hb
    rw [ht a (hcomp_ne a hab.completed)]
    obtain ⟨i, v', hi, hni⟩ := I.prec_sync a b hab hb
    have hil : i < C.log.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
    exact ⟨i, v', by rw [upd_log, List.getElem?_append_left hil]; exact hi,
      by rwa [upd_log, List.take_append_of_le_length hil.le]⟩
  · intro a b hab hb
    rw [ht a (hcomp_ne a hab.completed)]
    rcases (hPast b).1 hb with hb | rfl
    · have hne : b ≠ (p, (C.loc p).k) := fun he => hnotP (he ▸ hb)
      rw [ht b hne]; exact I.prec_past a b hab hb
    · rw [htk]
      refine ⟨fun _ _ => ?_, fun hr => by rw [hop] at hr; cases hr⟩
      exact (I.tok_le_clock hsafe hab (Invoked.of_opOf_eq_some hop) hs).trans_lt hd

/-- Lines 5–6 (`line5`): the reader reads `val`, `clock` and mbroadcasts them. -/
lemma Inv.line5 (I : Inv h C W tok) (hsafe : Validity C.log ∧ MutualOrdering C.log) {p : P}
    (hph : (C.loc p).phase = .rSync) (hs : .dl p p (.synch (C.loc p).k) ∈ C.log) :
    Inv h (C.upd p { C.loc p with phase := .rFin (C.loc p).val (C.loc p).clock }
        [.bc p (.write (C.loc p).k (C.loc p).val (C.loc p).clock)])
      W (Function.update tok (p, (C.loc p).k) (C.loc p).clock) := by
  have hfin0 : (C.loc p).phase.isFin = false := by rw [hph]; rfl
  have hnotP : ¬ Past C (p, (C.loc p).k) := I.not_past_cur hfin0
  have hnotW : (p, (C.loc p).k) ∉ W := fun hw => hnotP (I.W_mem _ hw).2.1
  have ht : ∀ x, x ≠ (p, (C.loc p).k) →
      Function.update tok (p, (C.loc p).k) (C.loc p).clock x = tok x :=
    fun x hx => Function.update_of_ne hx _ _
  have htk : Function.update tok (p, (C.loc p).k) (C.loc p).clock (p, (C.loc p).k) =
      (C.loc p).clock := Function.update_self _ _ _
  have htW : ∀ w ∈ W, Function.update tok (p, (C.loc p).k) (C.loc p).clock w = tok w :=
    fun w hw => ht w (fun he => hnotW (he ▸ hw))
  have hop : opOf h (p, (C.loc p).k) = some .read := I.op_r p (Or.inl hph)
  have hPast : ∀ x, Past (C.upd p { C.loc p with phase := .rFin (C.loc p).val (C.loc p).clock }
      [.bc p (.write (C.loc p).k (C.loc p).val (C.loc p).clock)]) x ↔
        Past C x ∨ x = (p, (C.loc p).k) := by
    rintro ⟨q, i⟩
    rcases eq_or_ne q p with rfl | hq
    · have e2 : Past C (q, i) ↔ i < (C.loc q).k := by
        simp only [Past, hfin0]; simp
      rw [e2]; simp only [Past, upd_loc_self, Prod.mk.injEq, true_and]; simp [Phase.isFin]
    · simp [Past, upd_loc_ne _ _ _ hq, hq]
  have hVal : ∀ v' c, ValOK v₀ h W tok v' c →
      ValOK v₀ h W (Function.update tok (p, (C.loc p).k) (C.loc p).clock) v' c :=
    fun v' c hv => hv.mono (fun _ _ h => h) (fun w hw => hw) htW
  have hne_cur : ∀ q, q ≠ p → (q, (C.loc q).k) ≠ (p, (C.loc p).k) :=
    fun q hq he => hq (Prod.mk.inj he).1
  have hcomp_ne : ∀ x, Completed h x → x ≠ (p, (C.loc p).k) := fun x hx he =>
    I.not_completed_cur p (he ▸ hx)
  refine ⟨I.wf, fun q => ?_, fun q => ?_, fun q v' hq' => ?_, fun q hq' => ?_, fun q v' c hq' => ?_,
    fun q v' c hq' => ?_, fun q => ?_, ?_, ?_, ?_, I.W_nodup, I.W_complete, I.write_resp, ?_, ?_,
    ?_, ?_, ?_⟩
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self]; exact I.resps q
    · rw [upd_loc_ne _ _ _ hq]; exact I.resps q
  · rcases eq_or_ne q p with rfl | hq
    · have := I.ops q; rw [hph] at this; simp only [upd_loc_self]; simpa using this
    · rw [upd_loc_ne _ _ _ hq]; exact I.ops q
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self] at hq'
      rcases hq' with hq' | ⟨c, hq'⟩ <;> cases hq'
    · rw [upd_loc_ne _ _ _ hq] at hq' ⊢; exact I.op_w q v' hq'
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self]; exact hop
    · rw [upd_loc_ne _ _ _ hq] at hq' ⊢; exact I.op_r q hq'
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self] at hq'; cases hq'
    · rw [upd_loc_ne _ _ _ hq] at hq' ⊢
      obtain ⟨h1, h2⟩ := I.fin_w q v' c hq'
      exact ⟨h1, by rw [ht _ (hne_cur q hq), h2]⟩
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self] at hq' ⊢
      cases hq'
      exact ⟨htk, hVal _ _ (I.val_ok q)⟩
    · rw [upd_loc_ne _ _ _ hq] at hq' ⊢
      obtain ⟨h1, h2⟩ := I.fin_r q v' c hq'
      exact ⟨by rw [ht _ (hne_cur q hq), h1], hVal _ _ h2⟩
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self]; exact hVal _ _ (I.val_ok q)
    · rw [upd_loc_ne _ _ _ hq]; exact hVal _ _ (I.val_ok q)
  · intro q k' v' c hm
    rw [upd_log, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨h1, h2, h3⟩ := I.msg_ok q k' v' c hm
      have hne : (q, k') ≠ (p, (C.loc p).k) := fun he => hnotP (he ▸ h2)
      exact ⟨hVal _ _ h1, (hPast _).2 (Or.inl h2), by rw [ht _ hne, h3]⟩
    · simp only [List.mem_singleton, Ev.bc.injEq, Msg.write.injEq] at hm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      exact ⟨hVal _ _ (I.val_ok q), (hPast _).2 (Or.inr rfl), htk⟩
  · intro q k' hm
    rw [upd_log, List.mem_append] at hm
    rcases hm with hm | hm
    · rcases eq_or_ne q p with rfl | hq
      · simp only [upd_loc_self]
        rcases I.synch_ok q k' hm with h1 | ⟨h1, -⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, by simp⟩
      · rw [upd_loc_ne _ _ _ hq]; exact I.synch_ok q k' hm
    · simp at hm
  · intro x hx
    obtain ⟨h1, h2, d', h3⟩ := I.W_mem x hx
    exact ⟨h1, (hPast x).2 (Or.inl h2), d', by rw [htW x hx, h3]⟩
  · intro x r hv hr
    rw [ht x (hcomp_ne x (Completed.of_respOf_eq_some hr))]
    exact hVal _ _ (I.read_resp x r hv hr)
  · intro x hx
    rw [ht x (hcomp_ne x hx)]
    obtain ⟨v', hv⟩ := I.fin_dl x hx
    exact ⟨v', List.mem_append_left _ hv⟩
  · intro q q' k' v' c hm
    rw [upd_log, List.mem_append] at hm
    rcases hm with hm | hm
    · rcases eq_or_ne q p with rfl | hq
      · simp only [upd_loc_self]; exact I.clock_ge q q' k' v' c hm
      · rw [upd_loc_ne _ _ _ hq]; exact I.clock_ge q q' k' v' c hm
    · simp at hm
  · intro a b hab hb
    rw [ht a (hcomp_ne a hab.completed)]
    obtain ⟨i, v', hi, hni⟩ := I.prec_sync a b hab hb
    have hil : i < C.log.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
    exact ⟨i, v', by rw [upd_log, List.getElem?_append_left hil]; exact hi,
      by rwa [upd_log, List.take_append_of_le_length hil.le]⟩
  · intro a b hab hb
    rw [ht a (hcomp_ne a hab.completed)]
    rcases (hPast b).1 hb with hb | rfl
    · have hne : b ≠ (p, (C.loc p).k) := fun he => hnotP (he ▸ hb)
      rw [ht b hne]; exact I.prec_past a b hab hb
    · rw [htk]
      refine ⟨fun _ hw => (by rw [hop] at hw; cases hw), fun _ => ?_⟩
      exact I.tok_le_clock hsafe hab (Invoked.of_opOf_eq_some hop) hs

/-- Return steps (`retW`, `retR`): the final wait of `p` is over, it returns `v`. -/
lemma Inv.ret (I : Inv h C W tok) {p : P} {v : V} {c : TS P}
    (hph : (C.loc p).phase = .wFin v c ∨ (C.loc p).phase = .rFin v c)
    (hs : .dl p p (.write (C.loc p).k v c) ∈ C.log) :
    Inv (h ++ [.ret p v]) (C.upd p { C.loc p with phase := .idle, k := (C.loc p).k + 1 } [])
      W tok := by
  have hne : (C.loc p).phase ≠ .idle := by rcases hph with h1 | h1 <;> rw [h1] <;> simp
  have hops : (opsOf h p).length = (C.loc p).k + 1 := by rw [I.ops p, if_neg hne]
  have hopOf : ∀ x, opOf (h ++ [.ret p v]) x = opOf h x := fun x => opOf_append_ret _ _ _ _
  have hVal : ∀ v' c', ValOK v₀ h W tok v' c' → ValOK v₀ (h ++ [.ret p v]) W tok v' c' :=
    fun v' c' hv => hv.mono (fun x o h => by rw [hopOf]; exact h) (fun _ h => h) (fun _ _ => rfl)
  have hPast : ∀ x, Past (C.upd p { C.loc p with phase := .idle, k := (C.loc p).k + 1 } []) x ↔
      Past C x := by
    rintro ⟨q, i⟩
    rcases eq_or_ne q p with rfl | hq
    · have hf : (C.loc q).phase.isFin = true := by rcases hph with h1 | h1 <;> rw [h1] <;> rfl
      simp only [Past, upd_loc_self, hf]; simp [Phase.isFin]; omega
    · simp [Past, upd_loc_ne _ _ _ hq]
  have hcur_w : ∀ v', opOf h (p, (C.loc p).k) = some (.write v') → (C.loc p).phase = .wFin v c := by
    intro v' hv'
    rcases hph with h1 | h1
    · exact h1
    · rw [I.op_r p (Or.inr ⟨v, c, h1⟩)] at hv'; cases hv'
  have hcur_r : opOf h (p, (C.loc p).k) = some .read → (C.loc p).phase = .rFin v c := by
    intro hv'
    rcases hph with h1 | h1
    · rw [I.op_w p v (Or.inr ⟨c, h1⟩)] at hv'; cases hv'
    · exact h1
  have hresp : (respsOf h p).length = (C.loc p).k := I.resps p
  refine ⟨I.wf.append_ret (by rw [hops, hresp]), fun q => ?_, fun q => ?_, fun q v' hq' => ?_,
    fun q hq' => ?_, fun q v' c' hq' => ?_, fun q v' c' hq' => ?_, fun q => ?_, ?_, ?_, ?_,
    I.W_nodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases eq_or_ne q p with rfl | hq
    · simp [hresp]
    · rw [upd_loc_ne _ _ _ hq, respsOf_append_ret_of_ne _ _ hq]; exact I.resps q
  · rw [opsOf_append_ret]
    rcases eq_or_ne q p with rfl | hq
    · simp [hops]
    · rw [upd_loc_ne _ _ _ hq]; exact I.ops q
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self] at hq'; rcases hq' with hq' | ⟨_, hq'⟩ <;> cases hq'
    · rw [upd_loc_ne _ _ _ hq] at hq' ⊢; rw [hopOf]; exact I.op_w q v' hq'
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self] at hq'; rcases hq' with hq' | ⟨_, _, hq'⟩ <;> cases hq'
    · rw [upd_loc_ne _ _ _ hq] at hq' ⊢; rw [hopOf]; exact I.op_r q hq'
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self] at hq'; cases hq'
    · rw [upd_loc_ne _ _ _ hq] at hq' ⊢; exact I.fin_w q v' c' hq'
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self] at hq'; cases hq'
    · rw [upd_loc_ne _ _ _ hq] at hq' ⊢
      exact ⟨(I.fin_r q v' c' hq').1, hVal _ _ (I.fin_r q v' c' hq').2⟩
  · rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self]; exact hVal _ _ (I.val_ok q)
    · rw [upd_loc_ne _ _ _ hq]; exact hVal _ _ (I.val_ok q)
  · intro q k' v' c' hm
    obtain ⟨h1, h2, h3⟩ := I.msg_ok q k' v' c' (by simpa using hm)
    exact ⟨hVal _ _ h1, (hPast _).2 h2, h3⟩
  · intro q k' hm
    have hm' : Ev.bc q (Msg.synch k') ∈ C.log := by simpa using hm
    rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self]
      rcases I.synch_ok q k' hm' with h1 | ⟨h1, -⟩ <;> left <;> omega
    · rw [upd_loc_ne _ _ _ hq]; exact I.synch_ok q k' hm'
  · intro x hx
    obtain ⟨⟨v', hv'⟩, h2, h3⟩ := I.W_mem x hx
    exact ⟨⟨v', by rw [hopOf]; exact hv'⟩, (hPast x).2 h2, h3⟩
  · intro x v' hv hc
    rw [hopOf] at hv
    rcases (completed_append_ret x).1 hc with hc | hx
    · exact I.W_complete x v' hv hc
    · rw [hresp] at hx; subst hx
      exact (I.fin_w p v c (hcur_w v' hv)).1
  · intro x v' r hv hr
    rw [hopOf] at hv
    rw [respOf_append_ret] at hr
    split_ifs at hr with hx
    · rw [hresp] at hx; subst hx
      cases hr
      have := I.op_w p v (Or.inr ⟨c, hcur_w v' hv⟩)
      rw [hv] at this; cases this; rfl
    · exact I.write_resp x v' r hv hr
  · intro x r hv hr
    rw [hopOf] at hv
    rw [respOf_append_ret] at hr
    split_ifs at hr with hx
    · rw [hresp] at hx; subst hx
      cases hr
      obtain ⟨h1, h2⟩ := I.fin_r p v c (hcur_r hv)
      rw [h1]; exact hVal _ _ h2
    · exact hVal _ _ (I.read_resp x r hv hr)
  · intro x hx
    rcases (completed_append_ret x).1 hx with hx | hx
    · obtain ⟨v', hv⟩ := I.fin_dl x hx; exact ⟨v', by simpa using hv⟩
    · rw [hresp] at hx; subst hx
      refine ⟨v, ?_⟩
      have htc : tok (p, (C.loc p).k) = c := by
        rcases hph with h1 | h1
        · exact (I.fin_w p v c h1).2
        · exact (I.fin_r p v c h1).1
      simpa [htc] using hs
  · intro q q' k' v' c' hm
    have hm' : Ev.dl q q' (Msg.write k' v' c') ∈ C.log := by simpa using hm
    rcases eq_or_ne q p with rfl | hq
    · simp only [upd_loc_self]; exact I.clock_ge q q' k' v' c' hm'
    · rw [upd_loc_ne _ _ _ hq]; exact I.clock_ge q q' k' v' c' hm'
  · intro a b hab hb
    have hb' : Invoked h b := by simpa [Invoked, opsOf_append_ret] using hb
    obtain ⟨i, v', hi, hni⟩ := I.prec_sync a b (hab.of_append_of_invoked hb') hb'
    exact ⟨i, v', by simpa using hi, by simpa using hni⟩
  · intro a b hab hb
    rw [hPast] at hb
    have hbi := I.invoked_of_past hb
    rw [hopOf]
    exact I.prec_past a b (hab.of_append_of_invoked hbi) hb

lemma Inv.crash (I : Inv h C W tok) (p : P) :
    Inv h ⟨C.loc, C.log, insert p C.crashed⟩ W tok :=
  ⟨I.wf, I.resps, I.ops, I.op_w, I.op_r, I.fin_w, I.fin_r, I.val_ok, I.msg_ok, I.synch_ok,
    I.W_mem, I.W_nodup, I.W_complete, I.write_resp, I.read_resp, I.fin_dl, I.clock_ge,
    I.prec_sync, I.prec_past⟩

end Steps

/-! ## Theorem 2 (safety) -/

/-- Every reachable configuration whose MBroadcast trace satisfies the safety properties of
MBroadcast satisfies the invariant. -/
theorem Reach.exists_inv {C : Cfg P V} {h : List (Label P (register V v₀))}
    (hr : Reach v₀ C h) (hs : Validity C.log ∧ MutualOrdering C.log) :
    ∃ W tok, Inv h C W tok := by
  induction hr with
  | init => exact ⟨[], _, inv_init⟩
  | @step C C' h ℓ _ hst ih =>
    obtain ⟨es, hes⟩ := hst.log_eq
    have hs0 : Validity C.log ∧ MutualOrdering C.log := by
      rw [hes] at hs; exact ⟨hs.1.of_append, hs.2.of_append⟩
    obtain ⟨W, tok, I⟩ := ih hs0
    cases hst with
    | invW p v hp hi =>
      exact ⟨W, tok, I.invoke (.write v) (.wSync v) hi (by simp) rfl
        (fun v' h => by rcases h with h | ⟨_, h⟩ <;> cases h; rfl)
        (fun h => by rcases h with h | ⟨_, _, h⟩ <;> cases h)⟩
    | invR p hp hi =>
      exact ⟨W, tok, I.invoke .read .rSync hi (by simp) rfl
        (fun v' h => by rcases h with h | ⟨_, h⟩ <;> cases h)
        (fun h => rfl)⟩
    | dlv p q m hp => exact ⟨W, tok, by simpa using I.deliver hs.1⟩
    | line2 p v d hp hph hsy hd => exact ⟨_, _, by simpa using I.line2 hs0 hph hsy hd⟩
    | line5 p hp hph hsy => exact ⟨_, _, by simpa using I.line5 hs0 hph hsy⟩
    | retW p v c hp hph hd => exact ⟨W, tok, I.ret (Or.inl hph) hd⟩
    | retR p v c hp hph hd => exact ⟨W, tok, I.ret (Or.inr hph) hd⟩
    | crash p => exact ⟨W, tok, by simpa using I.crash p⟩

/-- **Theorem 2 (safety).** Algorithm 3 implements an atomic (linearizable) multi-writer
multi-reader register on top of MBroadcast: every history of an execution whose MBroadcast trace
satisfies validity, no-duplication and mutual ordering is linearizable. This holds for any
number of crashes (no assumption `t < n/2`). -/
theorem alg3_linearizable {C : Cfg P V} {h : List (Label P (register V v₀))}
    (hr : Reach v₀ C h) (hs : Safe C.log) : ∃ L, IsLinearization h L := by
  obtain ⟨W, tok, I⟩ := hr.exists_inv ⟨hs.validity, hs.mutualOrd⟩
  exact I.tsLin.exists_isLinearization

/-- Theorem 2 (safety) needs only validity and mutual ordering of the MBroadcast layer
(no-duplication is not used). -/
theorem alg3_linearizable_of_validity_mutualOrdering {C : Cfg P V}
    {h : List (Label P (register V v₀))} (hr : Reach v₀ C h) (hv : Validity C.log)
    (hmo : MutualOrdering C.log) : ∃ L, IsLinearization h L := by
  obtain ⟨W, tok, I⟩ := hr.exists_inv ⟨hv, hmo⟩
  exact I.tsLin.exists_isLinearization


end Podc.MBroadcast.Alg3
