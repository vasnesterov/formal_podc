import Papers.PODC2016.OhRAMAtomicMemory.SafetyMsg
import Podc.Computability.Distributed.SharedMemory.TimestampLin

/-!
# The history invariant

`Inv Vr next v₀ h C Wl tok` relates a reachable configuration `C` with its history `h` and the
ghost data of the timestamp criterion `Cslib.SharedMemory.TSLin`:

* `Wl`: the writes that have chosen their tag (SWMR: at the invocation; MWMR: at the end of the
  discover phase, line 86), `tok x`: the tag of such a write;
* for a completed read, `tok x` is the tag it returned (the minimum tag of `rAck`, lines 12–13, or
  the common tag of a majority of relays, line 137).

Its main components are the paper's arguments:

* `val_*` (every tag/value pair in the system is the initial pair or the pair of a write of `Wl`);
* `stable` (after a completed operation `a`, a majority of servers has a tag `≥ tok a`: the
  `writeAck`s of a write, the `readAck`s of a slow read, the relays of a fast read);
* `disc_rt`, `read_rt` (real time: for every `a` that precedes the pending operation `b`, the
  messages of `b` sent by the servers of a majority `Q` carry tags `≥ tok a`, and every server
  whose relay counter for `b` has met `Q` has a tag `≥ tok a`; this is the core of Lemmas 2–4,
  7–11, 14–15, 18–21).
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]

/-- Histories of the protocol. -/
abbrev Hist (W R S V : Type) (v₀ : V) := List (Label (Node W R S) (register V v₀))

/-- `(v, t)` is the initial pair or the pair of a write of `Wl`. -/
def ValOK {v₀ : V} (h : Hist W R S V v₀) (Wl : List (OpId (Node W R S)))
    (tok : OpId (Node W R S) → T) (v : V) (t : T) : Prop :=
  (t = ⊥ ∧ v = v₀) ∨ ∃ x ∈ Wl, tok x = t ∧ opOf h x = some (.write v)

/-- A majority of servers has a tag `≥ t`. -/
def Stable (C : Cfg W R S T V) (t : T) : Prop :=
  ∃ Q : Finset S, maj S ≤ Q.card ∧ ∀ s ∈ Q, t ≤ (C.sl s).tag

/-- The history invariant. -/
structure Inv (next : W → T → T) (v₀ : V) (h : Hist W R S V v₀) (C : Cfg W R S T V)
    (Wl : List (OpId (Node W R S))) (tok : OpId (Node W R S) → T) : Prop where
  wf : WellFormed h
  /-- Servers invoke nothing, writers only write, readers only read. -/
  sv_ops : ∀ s, opsOf h (.sv s) = []
  w_ops : ∀ w o, o ∈ opsOf h (.wr w) → ∃ v, o = .write v
  r_ops : ∀ r o, o ∈ opsOf h (.rd r) → o = .read
  /-- A writer has a pending operation iff it is not idle. -/
  w_cnt : ∀ w, (opsOf h (.wr w)).length =
    (respsOf h (.wr w)).length + if (C.wl w).phase = .idle then 0 else 1
  /-- A reader has a pending operation iff `pending`. -/
  r_cnt : ∀ r, (opsOf h (.rd r)).length =
    (respsOf h (.rd r)).length + if (C.rl r).pending then 1 else 0
  w_cur_disc : ∀ w v, (C.wl w).phase = .disc v → opOf h (curOp h (.wr w)) = some (.write v)
  /-- In its update phase, the pending write of `w` has chosen its tag: the tag of `w`. -/
  w_cur_upd : ∀ w, (C.wl w).phase = .upd →
    opOf h (curOp h (.wr w)) = some (.write (C.wl w).val) ∧ curOp h (.wr w) ∈ Wl ∧
      tok (curOp h (.wr w)) = (C.wl w).tag
  write_resp : ∀ x v r, opOf h x = some (.write v) → respOf h x = some r → r = v
  W_nodup : Wl.Nodup
  /-- The writes of `Wl` have been invoked, have tags created by `next`, and are not in their
  discover phase. -/
  W_mem : ∀ x ∈ Wl, ∃ w, x.1 = .wr w ∧ Invoked h x ∧ (∃ t, tok x = next w t) ∧
    (x = curOp h (.wr w) → (C.wl w).phase.isDisc = false)
  W_complete : ∀ x v, opOf h x = some (.write v) → Completed h x → x ∈ Wl
  /-- The tag of a writer is at least the tags of all its writes. -/
  tok_le : ∀ w x, x ∈ Wl → x.1 = .wr w → tok x ≤ (C.wl w).tag
  /-- Every tag/value pair of a server, a writer or a message is the initial pair or the pair
  of a write of `Wl`. -/
  val_s : ∀ s, ValOK h Wl tok (C.sl s).val (C.sl s).tag
  val_w : ∀ w, ValOK h Wl tok (C.wl w).val (C.wl w).tag
  val_msg : ∀ x ∈ C.sent, ∀ t v, x.2.2.tv = some (t, v) → ValOK h Wl tok v t
  /-- A completed read returned the value of its tag. -/
  read_resp : ∀ x r, opOf h x = some .read → respOf h x = some r → ValOK h Wl tok r (tok x)
  /-- Lemmas 8, 11, 20, 21 (and the increment of the single writer in Theorems 5, 16): a write
  gets a tag larger than the tag of every preceding operation. -/
  prec_W : ∀ a b, Precedes h a b → b ∈ Wl → tok a < tok b
  /-- Lemmas 2, 4, 7, 10, 14, 15, 18, 19: a read returns a tag at least the tag of every
  preceding operation. -/
  prec_R : ∀ a b, Precedes h a b → opOf h b = some .read → Completed h b → tok a ≤ tok b
  /-- After an operation completes, a majority of servers has a tag at least its tag (the sets
  `WSet`, `RSet` of the proofs of Lemmas 2–3, 7–9, 11). -/
  stable : ∀ a, Completed h a → Stable C (tok a)
  /-- Real time for a pending discover phase (Lemmas 8, 11): the `discoverAck`s sent by a
  majority `Q` carry tags at least the tag of every preceding operation. -/
  disc_rt : ∀ w v a, (C.wl w).phase = .disc v → Precedes h a (curOp h (.wr w)) →
    ∃ Q : Finset S, maj S ≤ Q.card ∧ (∀ s ∈ Q, tok a ≤ (C.sl s).tag) ∧
      ∀ s ∈ Q, ∀ t v', (Node.sv s, Node.wr w, Msg.discoverAck t v' (C.wl w).op) ∈ C.sent →
        tok a ≤ t
  /-- Real time for a pending read (Lemmas 2, 3, 7, 9, 14, 18): for every preceding operation `a`
  there is a majority `Q` of servers with tags `≥ tok a` whose relays for the read carry tags
  `≥ tok a`; every server whose relay counter for the read has met `Q` has a tag `≥ tok a`; hence
  every `readAck` of the read carries a tag `≥ tok a` (Lemmas 3, 9). -/
  read_rt : ∀ r a, (C.rl r).pending = true → Precedes h a (curOp h (.rd r)) →
    ∃ Q : Finset S, maj S ≤ Q.card ∧ (∀ s ∈ Q, tok a ≤ (C.sl s).tag) ∧
      (∀ s ∈ Q, ∀ d t v, (Node.sv s, d, Msg.readRelay t v r (C.rl r).op) ∈ C.sent →
        tok a ≤ t) ∧
      (∀ sx, (C.sl sx).ops r = (C.rl r).op → (∃ s ∈ Q, s ∈ (C.sl sx).got r) →
        tok a ≤ (C.sl sx).tag) ∧
      (∀ sx t v, (Node.sv sx, Node.rd r, Msg.readAck t v (C.rl r).op) ∈ C.sent → tok a ≤ t)

/-! ## Lists of acknowledgments -/

lemma le_maxTag {a : List (S × T × V)} {e : S × T × V} (he : e ∈ a) : e.2.1 ≤ maxTag a := by
  unfold maxTag
  induction a with
  | nil => simp at he
  | cons x a ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 he with rfl | he
    · exact le_max_left _ _
    · exact (ih he).trans (le_max_right _ _)

lemma minVal_spec (v₀ : V) {a : List (S × T × V)} (ha : a ≠ []) :
    ∃ e ∈ a, minVal v₀ a = e.2.2 ∧ ∀ e' ∈ a, e.2.1 ≤ e'.2.1 := by
  unfold minVal
  cases hm : a.argmin (·.2.1) with
  | none => exact absurd (List.argmin_eq_none.1 hm) ha
  | some e =>
    exact ⟨e, List.argmin_mem hm, rfl, fun e' he' =>
      List.le_of_mem_argmin (f := fun x : S × T × V => x.2.1) he' hm⟩

lemma fastVal_spec {a : List (S × T × V)} {v : V} (h : fastVal a = some v) :
    ∃ p ∈ a, v = p.2.2 ∧ maj S ≤ (a.filter (fun q => decide (q.2.1 = p.2.1))).length := by
  unfold fastVal at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨p, List.mem_of_find?_eq_some hp, rfl, by simpa using List.find?_some hp⟩

/-! ## Basic consequences of the invariant -/

section Basic

variable {next : W → T → T} {v₀ : V} {h : Hist W R S V v₀} {C : Cfg W R S T V}
  {Wl : List (OpId (Node W R S))} {tok : OpId (Node W R S) → T}

lemma ValOK.mono {h' : Hist W R S V v₀} {Wl' : List (OpId (Node W R S))}
    {tok' : OpId (Node W R S) → T} {v : V} {t : T} (hv : ValOK h Wl tok v t)
    (hh : ∀ x o, opOf h x = some o → opOf h' x = some o) (hW : ∀ w ∈ Wl, w ∈ Wl')
    (ht : ∀ w ∈ Wl, tok' w = tok w) : ValOK h' Wl' tok' v t := by
  rcases hv with hv | ⟨w, hw, h1, h2⟩
  · exact Or.inl hv
  · exact Or.inr ⟨w, hW w hw, (ht w hw).trans h1, hh _ _ h2⟩

lemma Stable.mono {C' : Cfg W R S T V} {t : T} (hs : Stable C t)
    (h : ∀ s, (C.sl s).tag ≤ (C'.sl s).tag) : Stable C' t := by
  obtain ⟨Q, hQ, hQt⟩ := hs
  exact ⟨Q, hQ, fun s hs => (hQt s hs).trans (h s)⟩

lemma Inv.invoked_of_completed (I : Inv next v₀ h C Wl tok) {x : OpId (Node W R S)}
    (hx : Completed h x) : Invoked h x := I.wf.invoked_of_completed hx

lemma opOf_of_invoked {x : OpId (Node W R S)} (hx : Invoked h x) : ∃ o, opOf h x = some o := by
  simp only [opOf, Invoked] at *
  exact ⟨_, List.getElem?_eq_getElem hx⟩

/-- Invoked operations are writes of writers and reads of readers. -/
lemma Inv.kind (I : Inv next v₀ h C Wl tok) {x : OpId (Node W R S)} (hx : Invoked h x) :
    (∃ w v, x.1 = .wr w ∧ opOf h x = some (.write v)) ∨
      (∃ r, x.1 = .rd r ∧ opOf h x = some .read) := by
  obtain ⟨o, ho⟩ := opOf_of_invoked hx
  have hmem : o ∈ opsOf h x.1 := List.mem_of_getElem? ho
  obtain ⟨p, k⟩ := x
  cases p with
  | wr w =>
    obtain ⟨v, rfl⟩ := I.w_ops w o hmem
    exact Or.inl ⟨w, v, rfl, ho⟩
  | rd r =>
    rw [I.r_ops r o hmem] at ho
    exact Or.inr ⟨r, rfl, ho⟩
  | sv s =>
    rw [I.sv_ops s] at hmem; simp at hmem

/-- Distinct writes of `Wl` have distinct tags (writers: `hinj`; one writer: real time). -/
lemma Inv.W_inj (I : Inv next v₀ h C Wl tok) (hinj : ∀ w w' t t', next w t = next w' t' → w = w')
    {a b : OpId (Node W R S)} (ha : a ∈ Wl) (hb : b ∈ Wl) (hab : tok a = tok b) : a = b := by
  obtain ⟨w, hwa, hia, ⟨t, hta⟩, -⟩ := I.W_mem a ha
  obtain ⟨w', hwb, hib, ⟨t', htb⟩, -⟩ := I.W_mem b hb
  have hw : w = w' := hinj w w' t t' (hta.symm.trans (hab.trans htb))
  subst hw
  obtain ⟨p, i⟩ := a; obtain ⟨q, j⟩ := b
  simp only at hwa hwb; subst hwa; subst hwb
  rcases lt_trichotomy i j with hij | rfl | hij
  · have := I.prec_W _ _ (I.wf.precedes_of_lt hij hib) hb
    rw [hab] at this; exact absurd this (lt_irrefl _)
  · rfl
  · have := I.prec_W _ _ (I.wf.precedes_of_lt hij hia) ha
    rw [hab] at this; exact absurd this (lt_irrefl _)

lemma Inv.W_pos (I : Inv next v₀ h C Wl tok) (hlt : ∀ w t, t < next w t) {x : OpId (Node W R S)}
    (hx : x ∈ Wl) : ⊥ < tok x := by
  obtain ⟨w, -, -, ⟨t, ht⟩, -⟩ := I.W_mem x hx
  rw [ht]; exact lt_of_le_of_lt bot_le (hlt w t)

/-- A tag determines the value (`ValOK` is functional). -/
lemma Inv.val_unique (I : Inv next v₀ h C Wl tok) (hlt : ∀ w t, t < next w t)
    (hinj : ∀ w w' t t', next w t = next w' t' → w = w') {v v' : V} {t : T}
    (h1 : ValOK h Wl tok v t) (h2 : ValOK h Wl tok v' t) : v = v' := by
  rcases h1 with ⟨h1, rfl⟩ | ⟨x, hx, hxt, hxo⟩ <;> rcases h2 with ⟨h2, rfl⟩ | ⟨y, hy, hyt, hyo⟩
  · rfl
  · have := I.W_pos hlt hy; rw [hyt, h1] at this; exact absurd this (lt_irrefl _)
  · have := I.W_pos hlt hx; rw [hxt, h2] at this; exact absurd this (lt_irrefl _)
  · have := I.W_inj hinj hx hy (hxt.trans hyt.symm)
    subst this
    rw [hxo] at hyo; cases hyo; rfl

/-- The current operation of a writer that is not idle has been invoked. -/
lemma Inv.w_cur_invoked (I : Inv next v₀ h C Wl tok) {w : W} (hw : (C.wl w).phase ≠ .idle) :
    Invoked h (curOp h (.wr w)) := by
  have := I.w_cnt w; rw [ite_eq_right hw] at this
  simp only [Invoked]; omega

lemma Inv.r_cur_invoked (I : Inv next v₀ h C Wl tok) {r : R} (hr : (C.rl r).pending = true) :
    Invoked h (curOp h (.rd r)) := by
  have := I.r_cnt r; rw [ite_eq_left hr] at this
  simp only [Invoked]; omega

end Basic

/-! ## The initial configuration and frame lemmas -/

section Steps

variable {next : W → T → T} {v₀ : V} {h : Hist W R S V v₀} {C : Cfg W R S T V}
  {Wl : List (OpId (Node W R S))} {tok : OpId (Node W R S) → T}

lemma inv_init (Vr : Variant) :
    Inv next v₀ ([] : Hist W R S V v₀) ((proto Vr next v₀).initCfg : Cfg W R S T V) []
      (fun _ => ⊥) where
  wf := by intro β ℓ γ h; simp at h
  sv_ops _ := rfl
  w_ops _ _ h := by simp at h
  r_ops _ _ h := by simp at h
  w_cnt _ := by simp [Protocol.initCfg, Cfg.wl, proto, initLoc]
  r_cnt _ := by simp [Protocol.initCfg, Cfg.rl, proto, initLoc]
  w_cur_disc _ _ h := by simp [Protocol.initCfg, Cfg.wl, proto, initLoc] at h
  w_cur_upd _ h := by simp [Protocol.initCfg, Cfg.wl, proto, initLoc] at h
  write_resp _ _ _ h := by simp [opOf] at h
  W_nodup := List.nodup_nil
  W_mem _ h := by simp at h
  W_complete _ _ h := by simp [opOf] at h
  tok_le _ _ h := by simp at h
  val_s _ := Or.inl ⟨rfl, rfl⟩
  val_w _ := Or.inl ⟨rfl, rfl⟩
  val_msg _ h := by simp [Protocol.initCfg] at h
  read_resp _ _ h := by simp [opOf] at h
  prec_W _ _ h := by obtain ⟨β, γ, e, hc, -⟩ := h; simp at e; simp [e.1, Completed] at hc
  prec_R _ _ h := by obtain ⟨β, γ, e, hc, -⟩ := h; simp at e; simp [e.1, Completed] at hc
  stable _ h := by simp [Completed] at h
  disc_rt _ _ _ h := by simp [Protocol.initCfg, Cfg.wl, proto, initLoc] at h
  read_rt _ _ h := by simp [Protocol.initCfg, Cfg.rl, proto, initLoc] at h

/-- The invariant only depends on the phase, tag, value and counter of the writers, the pending
flag and counter of the readers, the servers and the sent messages. -/
lemma Inv.congr (I : Inv next v₀ h C Wl tok) {C' : Cfg W R S T V}
    (hph : ∀ w, (C'.wl w).phase = (C.wl w).phase) (htag : ∀ w, (C'.wl w).tag = (C.wl w).tag)
    (hval : ∀ w, (C'.wl w).val = (C.wl w).val) (hop : ∀ w, (C'.wl w).op = (C.wl w).op)
    (hpend : ∀ r, (C'.rl r).pending = (C.rl r).pending) (hrop : ∀ r, (C'.rl r).op = (C.rl r).op)
    (hs : ∀ s, C'.sl s = C.sl s) (hsent : C'.sent = C.sent) : Inv next v₀ h C' Wl tok where
  wf := I.wf
  sv_ops := I.sv_ops
  w_ops := I.w_ops
  r_ops := I.r_ops
  w_cnt w := by rw [hph]; exact I.w_cnt w
  r_cnt r := by rw [hpend]; exact I.r_cnt r
  w_cur_disc w v hw := I.w_cur_disc w v (by rw [← hph]; exact hw)
  w_cur_upd w hw := by rw [hval, htag]; exact I.w_cur_upd w (by rw [← hph]; exact hw)
  write_resp := I.write_resp
  W_nodup := I.W_nodup
  W_mem x hx := by
    obtain ⟨w, h1, h2, h3, h4⟩ := I.W_mem x hx
    exact ⟨w, h1, h2, h3, by rw [hph]; exact h4⟩
  W_complete := I.W_complete
  tok_le w x hx hxw := by rw [htag]; exact I.tok_le w x hx hxw
  val_s s := by rw [hs]; exact I.val_s s
  val_w w := by rw [hval, htag]; exact I.val_w w
  val_msg := by rw [hsent]; exact I.val_msg
  read_resp := I.read_resp
  prec_W := I.prec_W
  prec_R := I.prec_R
  stable a ha := (I.stable a ha).mono (fun s => by rw [hs])
  disc_rt w v a hw hab := by
    simp only [hs, hsent, hop]
    exact I.disc_rt w v a (by rw [← hph]; exact hw) hab
  read_rt r a hr hab := by
    simp only [hs, hsent, hrop]
    exact I.read_rt r a (by rw [← hpend]; exact hr) hab

/-- Silent steps. -/
lemma Inv.of_silent (I : Inv next v₀ h C Wl tok) {C' : Cfg W R S T V} (hloc : C'.loc = C.loc)
    (hsent : C'.sent = C.sent) : Inv next v₀ h C' Wl tok :=
  I.congr (fun w => by simp [Cfg.wl, hloc]) (fun w => by simp [Cfg.wl, hloc])
    (fun w => by simp [Cfg.wl, hloc]) (fun w => by simp [Cfg.wl, hloc])
    (fun r => by simp [Cfg.rl, hloc]) (fun r => by simp [Cfg.rl, hloc])
    (fun s => by simp [Cfg.sl, hloc]) hsent

/-! ## Server steps -/

lemma Inv.sRecv {Vr : Variant} (I : Inv next v₀ h C Wl tok) (IC : CInv Vr C) {s0 : S}
    {q : Node W R S} {m : Msg R T V} (hx : (q, Node.sv s0, m) ∈ C.net) :
    Inv next v₀ h (C.setS s0 (OhRAM.sRecv Vr q m (C.sl s0)).1 (OhRAM.sRecv Vr q m (C.sl s0)).2
      (C.net.erase (q, Node.sv s0, m))) Wl tok := by
  have IC' := IC.sRecv hx
  have hxs := IC.net_sent _ hx
  set l' := (OhRAM.sRecv Vr q m (C.sl s0)).1 with hl'
  set out := (OhRAM.sRecv Vr q m (C.sl s0)).2 with hout
  set C' := C.setS s0 l' out (C.net.erase (q, Node.sv s0, m)) with hC'
  have hsent : C'.sent = C.sent + outMsgs (.sv s0) out := rfl
  have hr : ∀ r, C'.rl r = C.rl r := by simp [hC']
  have hw : ∀ w, C'.wl w = C.wl w := by simp [hC']
  have hother : ∀ s', s' ≠ s0 → C'.sl s' = C.sl s' := by intro s' h; simp [hC', h]
  have hself : C'.sl s0 = l' := by simp [hC']
  have hmono : (C.sl s0).tag ≤ l'.tag := sRecv_tag_mono q m (C.sl s0)
  have htag : ∀ s', (C.sl s').tag ≤ (C'.sl s').tag := by
    intro s'; by_cases h : s' = s0
    · subst h; rw [hself]; exact hmono
    · rw [hother s' h]
  -- new messages are sent by `s0` and carry its new tag and value
  have hnew : ∀ a b c, (a, b, c) ∈ C'.sent → (a, b, c) ∈ C.sent ∨
      (a = .sv s0 ∧ ∀ t v, c.tv = some (t, v) → t = l'.tag ∧ v = l'.val) := by
    intro a b c hm
    rw [hsent, Multiset.mem_add, mem_outMsgs_iff] at hm
    rcases hm with hm | ⟨h1, h2⟩
    · exact Or.inl hm
    · refine Or.inr ⟨h1, fun t v htv => ?_⟩
      have := sRecv_out_tv (Vr := Vr) q m (C.sl s0) _ h2
      simp only [htv, Option.some.injEq, Prod.mk.injEq] at this
      exact this
  have hvals : ∀ s, ValOK h Wl tok (C'.sl s).val (C'.sl s).tag := by
    intro s
    by_cases hs : s = s0
    · subst hs; rw [hself]
      rcases sRecv_tv (Vr := Vr) q m (C.sl s) with ⟨h1, h2⟩ | h1
      · rw [hl', h1, h2]; exact I.val_s s
      · exact I.val_msg _ hxs _ _ h1
    · rw [hother s hs]; exact I.val_s s
  -- relay counters after the step
  have hgot : ∀ r a (Q : Finset S), (∀ s ∈ Q, ∀ d t v, (Node.sv s, d, Msg.readRelay t v r (C.rl r).op)
      ∈ C.sent → tok a ≤ t) →
      (∀ sx, (C.sl sx).ops r = (C.rl r).op → (∃ s ∈ Q, s ∈ (C.sl sx).got r) →
        tok a ≤ (C.sl sx).tag) →
      ∀ sx, (C'.sl sx).ops r = (C.rl r).op → (∃ s ∈ Q, s ∈ (C'.sl sx).got r) →
        tok a ≤ (C'.sl sx).tag := by
    intro r a Q hii hiii sx hops hQ
    by_cases hsx : sx = s0
    · subst hsx
      rw [hself] at hops hQ ⊢
      rcases sRecv_counters Vr q m (C.sl sx) with ⟨sj, t0, v0, r0, k0, rfl, rfl⟩ | ⟨h1, -, h3⟩
      · have hl'' : l' = (sRelay Vr sj t0 v0 r0 k0 (C.sl sx)).1 := rfl
        rw [hl''] at hops hQ ⊢
        by_cases hr0 : r = r0
        · subst hr0
          rw [sRelay_ops, ite_eq_left rfl] at hops
          rw [sRelay_got, ite_eq_left rfl] at hQ
          obtain ⟨s, hsQ, hsg⟩ := hQ
          have hge : t0 ≤ (sRelay Vr sj t0 v0 r k0 (C.sl sx)).1.tag := by
            rw [sRelay_tag]; split_ifs with h' <;> [exact le_rfl; exact not_lt.1 h']
          have hmono' : (C.sl sx).tag ≤ (sRelay Vr sj t0 v0 r k0 (C.sl sx)).1.tag :=
            sRecv_tag_mono (Vr := Vr) (Node.sv sj) (Msg.readRelay t0 v0 r k0) (C.sl sx)
          have hk0 := IC.rel_le _ _ _ _ _ _ hxs
          have hops0 := IC.ops_le sx r
          split_ifs at hsg with h1 h2
          · rw [Finset.mem_singleton] at hsg; subst hsg
            have : k0 = (C.rl r).op := by omega
            subst this
            exact (hii s hsQ _ _ _ hxs).trans hge
          · rcases Finset.mem_insert.1 hsg with rfl | hsg
            · have : k0 = (C.rl r).op := by omega
              subst this
              exact (hii s hsQ _ _ _ hxs).trans hge
            · exact (hiii sx (by omega) ⟨s, hsQ, hsg⟩).trans hmono'
          · exact (hiii sx (by omega) ⟨s, hsQ, hsg⟩).trans hmono'
        · rw [sRelay_ops, ite_eq_right hr0] at hops
          rw [sRelay_got, ite_eq_right hr0] at hQ
          exact (hiii sx hops hQ).trans
            (sRecv_tag_mono (Vr := Vr) (Node.sv sj) (Msg.readRelay t0 v0 r0 k0) (C.sl sx))
      · rw [hl', h1] at hops; rw [hl', h3] at hQ
        exact (hiii sx hops hQ).trans hmono
    · rw [hother sx hsx] at hops hQ ⊢
      exact hiii sx hops hQ
  refine {
    wf := I.wf, sv_ops := I.sv_ops, w_ops := I.w_ops, r_ops := I.r_ops,
    w_cnt := ?w_cnt, r_cnt := ?r_cnt, w_cur_disc := ?w_cur_disc, w_cur_upd := ?w_cur_upd,
    write_resp := I.write_resp, W_nodup := I.W_nodup, W_mem := ?W_mem,
    W_complete := I.W_complete, tok_le := ?tok_le, val_s := hvals, val_w := ?val_w,
    val_msg := ?val_msg, read_resp := I.read_resp, prec_W := I.prec_W, prec_R := I.prec_R,
    stable := fun a ha => (I.stable a ha).mono htag, disc_rt := ?disc_rt, read_rt := ?read_rt }
  case w_cnt => intro w; rw [hw]; exact I.w_cnt w
  case r_cnt => intro r; rw [hr]; exact I.r_cnt r
  case w_cur_disc => intro w; rw [hw]; exact I.w_cur_disc w
  case w_cur_upd => intro w; rw [hw]; exact I.w_cur_upd w
  case W_mem =>
    intro x hx'
    obtain ⟨w, h1, h2, h3, h4⟩ := I.W_mem x hx'
    exact ⟨w, h1, h2, h3, by rw [hw]; exact h4⟩
  case tok_le => intro w; rw [hw]; exact I.tok_le w
  case val_w => intro w; rw [hw]; exact I.val_w w
  case val_msg =>
    rintro ⟨a, b, c⟩ hm t v htv
    rcases hnew a b c hm with hm | ⟨rfl, h2⟩
    · exact I.val_msg _ hm t v htv
    · obtain ⟨rfl, rfl⟩ := h2 t v htv
      have := hvals s0; rwa [hself] at this
  case disc_rt =>
    intro w v a hph hab
    rw [hw] at hph ⊢
    obtain ⟨Q, hQ, hQt, hQm⟩ := I.disc_rt w v a hph hab
    refine ⟨Q, hQ, fun s hs => (hQt s hs).trans (htag s), fun s hs t v' hm => ?_⟩
    rcases hnew _ _ _ hm with hm | ⟨h1, h2⟩
    · exact hQm s hs t v' hm
    · cases h1
      obtain ⟨rfl, -⟩ := h2 t v' rfl
      exact (hQt s0 hs).trans hmono
  case read_rt =>
    intro r a hpend hab
    rw [hr] at hpend ⊢
    obtain ⟨Q, hQ, hQt, hii, hiii, hiv⟩ := I.read_rt r a hpend hab
    have hiii' := hgot r a Q hii hiii
    refine ⟨Q, hQ, fun s hs => (hQt s hs).trans (htag s), fun s hs d t v hm => ?_, hiii', ?_⟩
    · rcases hnew _ _ _ hm with hm | ⟨h1, h2⟩
      · exact hii s hs d t v hm
      · cases h1
        obtain ⟨rfl, -⟩ := h2 t v rfl
        exact (hQt s0 hs).trans hmono
    · intro sx t v hm
      rcases hnew _ _ _ hm with hm | ⟨h1, h2⟩
      · exact hiv sx t v hm
      · cases h1
        obtain ⟨rfl, -⟩ := h2 t v rfl
        -- the `readAck` was sent when the relay counter reached a majority
        rw [hsent, Multiset.mem_add, mem_outMsgs_iff] at hm
        rcases hm with hm | ⟨-, hm⟩
        · exact hiv _ _ _ hm
        rcases sRecv_cases (Vr := Vr) q m (C.sl s0) with ⟨r0, k0, -, -, h⟩ |
          ⟨sj, t0, v0, r0, k0, rfl, rfl, h⟩ |
          ⟨w0, t0, v0, op0, -, -, h⟩ | ⟨w0, op0, -, -, h⟩ | h <;> rw [hout, h] at hm
        · simp only [Multiset.mem_add, mem_bcast_iff] at hm
          rcases hm with ⟨-, hm⟩ | hm
          · cases hm
          · split_ifs at hm
            · rw [Multiset.mem_singleton] at hm; cases hm
            · simp at hm
        · rw [sRelay_out] at hm
          split_ifs at hm with hsend
          · rw [Multiset.mem_singleton] at hm
            simp only [Prod.mk.injEq, Node.rd.injEq, Msg.readAck.injEq] at hm
            obtain ⟨rfl, -, -, rfl⟩ := hm
            have hops : (C'.sl s0).ops r = (C.rl r).op := by
              rw [hself, hl', h, sRelay_ops, ite_eq_left rfl]
              exact max_eq_right (IC.ops_le s0 r)
            have hcard : maj S ≤ ((C'.sl s0).got r).card := by
              rw [← IC'.relays_card, hself, hl', h, hsend.2]
            obtain ⟨s, hs⟩ := maj_inter hQ hcard
            rw [Finset.mem_inter] at hs
            have := hiii' s0 hops ⟨s, hs.1, hs.2⟩
            rwa [hself] at this
          · simp at hm
        · rw [sWrite_snd, Multiset.mem_singleton] at hm; cases hm
        · rw [Multiset.mem_singleton] at hm; cases hm
        · simp at hm

/-! ## Invocations -/

omit [Fintype S] [LinearOrder T] [OrderBot T] [DecidableEq V] in
lemma not_ret_inv (p : Node W R S) (o : RWOp V) :
    ∀ q r, (Label.inv p o : Label (Node W R S) (register V v₀)) ≠ .ret q r := by
  intro q r h; cases h

lemma Inv.rInvoke {Vr : Variant} (I : Inv next v₀ h C Wl tok) (IC : CInv Vr C) {r : R}
    {l : RLoc S T V} {out : Multiset (Node W R S × Msg R T V)}
    (hinv : rInvoke (C.rl r) = some (l, out)) :
    Inv next v₀ (h ++ [.inv (.rd r) .read]) (C.setR r l out C.net) Wl tok := by
  obtain ⟨hpend, rfl, rfl⟩ := rInvoke_eq hinv
  set h' := h ++ [(Label.inv (.rd r) .read : Label (Node W R S) (register V v₀))] with hh'
  set C' := C.setR r ⟨(C.rl r).op + 1, true, [], []⟩ (bcast (.readRequest ((C.rl r).op + 1)))
    C.net with hC'
  have hcnt := I.r_cnt r
  rw [hpend] at hcnt; simp only [Bool.false_eq_true, ite_false, add_zero] at hcnt
  have hopOf : ∀ x o, opOf h x = some o → opOf h' x = some o :=
    fun x o hx => opOf_append_of_eq_some hx _
  have hresp : ∀ x, respOf h' x = respOf h x := respOf_append_of_not_ret (not_ret_inv _ _)
  have hcomp : ∀ x, Completed h' x ↔ Completed h x := completed_append_of_not_ret (not_ret_inv _ _)
  have hcur : ∀ p, curOp h' p = curOp h p := fun p => curOp_append_inv h _ p _
  have hopOf' : ∀ x o, opOf h' x = some o → opOf h x = some o ∨ (x = (.rd r, (opsOf h (.rd r)).length) ∧ o = .read) := by
    intro x o hx
    rcases opOf_concat_cases hx with hx | ⟨h1, h2⟩
    · exact Or.inl hx
    · obtain ⟨p, k⟩ := x
      simp only [Label.inv.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact Or.inr ⟨Prod.ext rfl h2, rfl⟩
  have hnc : ¬ Completed h (Node.rd r, (opsOf h (.rd r)).length) := by
    simp only [Completed]; omega
  have hpre : ∀ a b, Invoked h b → Precedes h' a b → Precedes h a b :=
    fun a b hb hab => hab.of_append_of_invoked hb
  have hw : ∀ w, C'.wl w = C.wl w := by simp [hC']
  have hs : ∀ s, C'.sl s = C.sl s := by simp [hC']
  have hother : ∀ r', r' ≠ r → C'.rl r' = C.rl r' := by intro r' h; simp [hC', h]
  have hsv : ∀ s d m, (Node.sv s, d, m) ∈ C'.sent → (Node.sv s, d, m) ∈ C.sent := by
    intro s d m hm; simpa [hC'] using hm
  have hV : ∀ v t, ValOK h Wl tok v t → ValOK h' Wl tok v t :=
    fun v t hv => hv.mono hopOf (fun _ h => h) (fun _ _ => rfl)
  refine {
    wf := ?wf, sv_ops := ?sv_ops, w_ops := ?w_ops, r_ops := ?r_ops, w_cnt := ?w_cnt,
    r_cnt := ?r_cnt, w_cur_disc := ?w_cur_disc, w_cur_upd := ?w_cur_upd,
    write_resp := ?write_resp, W_nodup := I.W_nodup, W_mem := ?W_mem,
    W_complete := ?W_complete, tok_le := ?tok_le, val_s := ?val_s, val_w := ?val_w,
    val_msg := ?val_msg, read_resp := ?read_resp, prec_W := ?prec_W, prec_R := ?prec_R,
    stable := ?stable, disc_rt := ?disc_rt, read_rt := ?read_rt }
  case wf => exact I.wf.append_inv hcnt
  case sv_ops =>
    intro s; rw [opsOf_concat_of_ne (fun o h => by cases h)]; exact I.sv_ops s
  case w_ops =>
    intro w o ho; rw [opsOf_concat_of_ne (fun o h => by cases h)] at ho; exact I.w_ops w o ho
  case r_ops =>
    intro r' o ho
    rw [opsOf_concat, List.mem_append] at ho
    rcases ho with ho | ho
    · exact I.r_ops r' o ho
    · simp only [Label.invOf_inv] at ho; split_ifs at ho <;> simp_all
  case w_cnt =>
    intro w; rw [hw, opsOf_concat_of_ne (fun o h => by cases h), respsOf_append_inv]
    exact I.w_cnt w
  case r_cnt =>
    intro r'
    by_cases hr : r' = r
    · subst hr; simp [hh', hC', hcnt]
    · rw [hother r' hr, opsOf_concat_of_ne (fun o h => by cases h; exact hr rfl),
        respsOf_append_inv]
      exact I.r_cnt r'
  case w_cur_disc =>
    intro w v hph; rw [hw] at hph; rw [hcur]; exact hopOf _ _ (I.w_cur_disc w v hph)
  case w_cur_upd =>
    intro w hph; rw [hw] at hph ⊢; rw [hcur]
    obtain ⟨h1, h2, h3⟩ := I.w_cur_upd w hph
    exact ⟨hopOf _ _ h1, h2, h3⟩
  case write_resp =>
    intro x v r' hx hr'
    rw [hresp] at hr'
    rcases hopOf' x _ hx with hx | ⟨-, h2⟩
    · exact I.write_resp x v r' hx hr'
    · cases h2
  case W_mem =>
    intro x hx
    obtain ⟨w, h1, h2, h3, h4⟩ := I.W_mem x hx
    exact ⟨w, h1, h2.mono, h3, by rw [hcur, hw]; exact h4⟩
  case W_complete =>
    intro x v hx hc
    rw [hcomp] at hc
    rcases hopOf' x _ hx with hx | ⟨-, h2⟩
    · exact I.W_complete x v hx hc
    · cases h2
  case tok_le => intro w; rw [hw]; exact I.tok_le w
  case val_s => intro s; rw [hs]; exact hV _ _ (I.val_s s)
  case val_w => intro w; rw [hw]; exact hV _ _ (I.val_w w)
  case val_msg =>
    rintro ⟨a, b, c⟩ hm t v htv
    simp only [hC', setR_sent, Multiset.mem_add, mem_outMsgs_iff, mem_bcast_iff] at hm
    rcases hm with hm | ⟨-, -, rfl⟩
    · exact hV _ _ (I.val_msg _ hm t v htv)
    · simp at htv
  case read_resp =>
    intro x r' hx hr'
    rw [hresp] at hr'
    rcases hopOf' x _ hx with hx | ⟨rfl, -⟩
    · exact hV _ _ (I.read_resp x r' hx hr')
    · exact absurd (Completed.of_respOf_eq_some hr') hnc
  case prec_W =>
    intro a b hab hb
    exact I.prec_W a b (hpre a b (I.W_mem b hb).choose_spec.2.1 hab) hb
  case prec_R =>
    intro a b hab hb hc
    rw [hcomp] at hc
    have hbi := I.invoked_of_completed hc
    rcases hopOf' b _ hb with hb | ⟨rfl, -⟩
    · exact I.prec_R a b (hpre a b hbi hab) hb hc
    · exact absurd hc hnc
  case stable => intro a ha; rw [hcomp] at ha; exact (I.stable a ha).mono (fun s => by rw [hs])
  case disc_rt =>
    intro w v a hph hab
    rw [hw] at hph ⊢
    rw [hcur] at hab
    obtain ⟨Q, hQ, hQt, hQm⟩ := I.disc_rt w v a hph
      (hpre a _ (I.w_cur_invoked (by rw [hph]; simp)) hab)
    exact ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs',
      fun s hs' t v' hm => hQm s hs' t v' (hsv _ _ _ hm)⟩
  case read_rt =>
    intro r' a hp hab
    rw [hcur] at hab
    by_cases hr : r' = r
    · subst hr
      have hb : curOp h (Node.rd r') = (Node.rd r', (opsOf h (.rd r')).length) := by
        simp only [curOp]; rw [hcnt]
      rw [hb] at hab
      have ha := precedes_append_inv_iff.1 hab
      obtain ⟨Q, hQ, hQt⟩ := I.stable a ha
      have hop : (C'.rl r').op = (C.rl r').op + 1 := by simp [hC']
      refine ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs', ?_, ?_, ?_⟩
      · intro s _ d t v hm
        have := IC.rel_le _ _ _ _ _ _ (hsv _ _ _ hm); omega
      · intro sx hops _
        rw [hs] at hops
        have := IC.ops_le sx r'; omega
      · intro sx t v hm
        have := IC.rack_le _ _ _ _ _ (hsv _ _ _ hm); omega
    · rw [hother r' hr] at hp ⊢
      obtain ⟨Q, hQ, hQt, hii, hiii, hiv⟩ := I.read_rt r' a hp
        (hpre a _ (I.r_cur_invoked hp) hab)
      refine ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs',
        fun s hs' d t v hm => hii s hs' d t v (hsv _ _ _ hm), fun sx => by rw [hs]; exact hiii sx,
        fun sx t v hm => hiv sx t v (hsv _ _ _ hm)⟩

/-- Facts on the history after an invocation of a write by `w`. -/
lemma Inv.winv_hist (I : Inv next v₀ h C Wl tok) {w : W} {val : V}
    (hidle : (C.wl w).phase = .idle) :
    let h' := h ++ [(Label.inv (.wr w) (.write val) : Label (Node W R S) (register V v₀))]
    let b : OpId (Node W R S) := (.wr w, (opsOf h (.wr w)).length)
    WellFormed h' ∧ (∀ x o, opOf h x = some o → opOf h' x = some o) ∧
    (∀ x, respOf h' x = respOf h x) ∧ (∀ x, Completed h' x ↔ Completed h x) ∧
    (∀ p, curOp h' p = curOp h p) ∧
    (∀ x o, opOf h' x = some o → opOf h x = some o ∨ (x = b ∧ o = .write val)) ∧
    opOf h' b = some (.write val) ∧ ¬ Invoked h b ∧ curOp h (.wr w) = b ∧ Invoked h' b ∧
    (∀ a c, Invoked h c → Precedes h' a c → Precedes h a c) ∧
    (∀ a, Precedes h' a b ↔ Completed h a) ∧
    (∀ p, p ≠ .wr w → opsOf h' p = opsOf h p) ∧
    opsOf h' (.wr w) = opsOf h (.wr w) ++ [.write val] ∧
    (∀ p, respsOf h' p = respsOf h p) := by
  intro h' b
  have hcnt := I.w_cnt w
  rw [hidle] at hcnt; simp only [ite_true, add_zero] at hcnt
  refine ⟨I.wf.append_inv hcnt, fun x o hx => opOf_append_of_eq_some hx _,
    respOf_append_of_not_ret (not_ret_inv _ _), completed_append_of_not_ret (not_ret_inv _ _),
    fun p => curOp_append_inv h _ p _, ?_, ?_, ?_, ?_, ?_, fun a c hc hac => hac.of_append_of_invoked hc,
    fun a => precedes_append_inv_iff, ?_, ?_, fun p => respsOf_append_inv h _ p _⟩
  · intro x o hx
    rcases opOf_concat_cases hx with hx | ⟨h1, h2⟩
    · exact Or.inl hx
    · obtain ⟨p, k⟩ := x
      simp only [Label.inv.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact Or.inr ⟨Prod.ext rfl h2, rfl⟩
  · rw [opOf_concat_inv, ite_eq_left rfl]
  · simp [Invoked, b]
  · simp [curOp, b, hcnt]
  · simp [Invoked, b, h']
  · intro p hp; rw [opsOf_concat_of_ne]; intro o h; cases h; exact hp rfl
  · simp [h']

/-- **MWMR invocation** (lines 80–83). -/
lemma Inv.wInvoke_mw {Vr : Variant} (hmw : Vr.mw = true) (I : Inv next v₀ h C Wl tok)
    (IC : CInv Vr C) {w : W} {val : V} {l : WLoc S T V}
    {out : Multiset (Node W R S × Msg R T V)}
    (hinv : wInvoke Vr next w val (C.wl w) = some (l, out)) :
    Inv next v₀ (h ++ [.inv (.wr w) (.write val)]) (C.setW w l out C.net) Wl tok := by
  obtain ⟨hidle, hcase⟩ := wInvoke_cases hinv
  obtain ⟨-, rfl, rfl⟩ : Vr.mw = true ∧
      l = { C.wl w with op := (C.wl w).op + 1, ack := [], phase := .disc val } ∧
      out = bcast (.discover ((C.wl w).op + 1)) := by
    rcases hcase with h1 | ⟨h1, -⟩
    · exact h1
    · rw [hmw] at h1; cases h1
  obtain ⟨hwf, hopOf, hresp, hcomp, hcur, hopOf', hb, hbn, hcb, hbi, hpre, hpreb, hops, hopsw,
    hresps⟩ := I.winv_hist (val := val) hidle
  set h' := h ++ [(Label.inv (.wr w) (.write val) : Label (Node W R S) (register V v₀))]
  set b : OpId (Node W R S) := (.wr w, (opsOf h (.wr w)).length) with hbdef
  set C' := C.setW w { C.wl w with op := (C.wl w).op + 1, ack := [], phase := .disc val }
    (bcast (.discover ((C.wl w).op + 1))) C.net with hC'
  have hr : ∀ r, C'.rl r = C.rl r := by simp [hC']
  have hs : ∀ s, C'.sl s = C.sl s := by simp [hC']
  have hother : ∀ w', w' ≠ w → C'.wl w' = C.wl w' := by intro w' h; simp [hC', h]
  have hself : C'.wl w = { C.wl w with op := (C.wl w).op + 1, ack := [], phase := .disc val } := by
    simp [hC']
  have hsv : ∀ s d m, (Node.sv s, d, m) ∈ C'.sent → (Node.sv s, d, m) ∈ C.sent := by
    intro s d m hm; simpa [hC'] using hm
  have hV : ∀ v t, ValOK h Wl tok v t → ValOK h' Wl tok v t :=
    fun v t hv => hv.mono hopOf (fun _ h => h) (fun _ _ => rfl)
  have hbW : b ∉ Wl := fun hbW => hbn (I.W_mem b hbW).choose_spec.2.1
  refine {
    wf := hwf, sv_ops := ?sv_ops, w_ops := ?w_ops, r_ops := ?r_ops, w_cnt := ?w_cnt,
    r_cnt := ?r_cnt, w_cur_disc := ?w_cur_disc, w_cur_upd := ?w_cur_upd,
    write_resp := ?write_resp, W_nodup := I.W_nodup, W_mem := ?W_mem,
    W_complete := ?W_complete, tok_le := ?tok_le, val_s := ?val_s, val_w := ?val_w,
    val_msg := ?val_msg, read_resp := ?read_resp, prec_W := ?prec_W, prec_R := ?prec_R,
    stable := ?stable, disc_rt := ?disc_rt, read_rt := ?read_rt }
  case sv_ops => intro s; rw [hops _ (by simp)]; exact I.sv_ops s
  case w_ops =>
    intro w' o ho
    by_cases hw : w' = w
    · subst hw; rw [hopsw, List.mem_append] at ho
      rcases ho with ho | ho
      · exact I.w_ops w' o ho
      · simp at ho; exact ⟨val, ho⟩
    · rw [hops _ (by simp [hw])] at ho; exact I.w_ops w' o ho
  case r_ops => intro r o ho; rw [hops _ (by simp)] at ho; exact I.r_ops r o ho
  case w_cnt =>
    intro w'
    by_cases hw : w' = w
    · subst hw; rw [hself, hopsw, hresps]; have := I.w_cnt w'; rw [hidle] at this; simp [this]
    · rw [hother w' hw, hops _ (by simp [hw]), hresps]; exact I.w_cnt w'
  case r_cnt => intro r; rw [hr, hops _ (by simp), hresps]; exact I.r_cnt r
  case w_cur_disc =>
    intro w' v hph
    rw [hcur]
    by_cases hw : w' = w
    · subst hw; rw [hself] at hph; cases hph; rw [hcb]; exact hb
    · rw [hother w' hw] at hph; exact hopOf _ _ (I.w_cur_disc w' v hph)
  case w_cur_upd =>
    intro w' hph
    rw [hcur]
    by_cases hw : w' = w
    · subst hw; rw [hself] at hph; cases hph
    · rw [hother w' hw] at hph ⊢
      obtain ⟨h1, h2, h3⟩ := I.w_cur_upd w' hph
      exact ⟨hopOf _ _ h1, h2, h3⟩
  case write_resp =>
    intro x v r' hx hr'
    rw [hresp] at hr'
    rcases hopOf' x _ hx with hx | ⟨rfl, -⟩
    · exact I.write_resp x v r' hx hr'
    · exact absurd (I.invoked_of_completed (Completed.of_respOf_eq_some hr')) hbn
  case W_mem =>
    intro x hx
    obtain ⟨w', h1, h2, h3, h4⟩ := I.W_mem x hx
    refine ⟨w', h1, h2.mono, h3, fun hxc => ?_⟩
    rw [hcur] at hxc
    by_cases hw : w' = w
    · subst hw; rw [hcb] at hxc; subst hxc; exact absurd hx hbW
    · rw [hother w' hw]; exact h4 hxc
  case W_complete =>
    intro x v hx hc
    rw [hcomp] at hc
    rcases hopOf' x _ hx with hx | ⟨rfl, -⟩
    · exact I.W_complete x v hx hc
    · exact absurd (I.invoked_of_completed hc) hbn
  case tok_le =>
    intro w' x hx hxw
    by_cases hw : w' = w
    · subst hw; rw [hself]; exact I.tok_le w' x hx hxw
    · rw [hother w' hw]; exact I.tok_le w' x hx hxw
  case val_s => intro s; rw [hs]; exact hV _ _ (I.val_s s)
  case val_w =>
    intro w'
    by_cases hw : w' = w
    · subst hw; rw [hself]; exact hV _ _ (I.val_w w')
    · rw [hother w' hw]; exact hV _ _ (I.val_w w')
  case val_msg =>
    rintro ⟨a, b', c⟩ hm t v htv
    simp only [hC', setW_sent, Multiset.mem_add, mem_outMsgs_iff, mem_bcast_iff] at hm
    rcases hm with hm | ⟨-, -, rfl⟩
    · exact hV _ _ (I.val_msg _ hm t v htv)
    · simp at htv
  case read_resp =>
    intro x r' hx hr'
    rw [hresp] at hr'
    rcases hopOf' x _ hx with hx | ⟨-, h2⟩
    · exact hV _ _ (I.read_resp x r' hx hr')
    · cases h2
  case prec_W =>
    intro a c hac hc
    exact I.prec_W a c (hpre a c (I.W_mem c hc).choose_spec.2.1 hac) hc
  case prec_R =>
    intro a c hac hc hcc
    rw [hcomp] at hcc
    have hci := I.invoked_of_completed hcc
    rcases hopOf' c _ hc with hc | ⟨-, h2⟩
    · exact I.prec_R a c (hpre a c hci hac) hc hcc
    · cases h2
  case stable => intro a ha; rw [hcomp] at ha; exact (I.stable a ha).mono (fun s => by rw [hs])
  case disc_rt =>
    intro w' v a hph hab
    rw [hcur] at hab
    by_cases hw : w' = w
    · subst hw
      rw [hcb, hpreb] at hab
      obtain ⟨Q, hQ, hQt⟩ := I.stable a hab
      refine ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs', fun s _ t v' hm => ?_⟩
      rw [hself] at hm
      have := (IC.dack_le hmw _ _ _ _ _ (hsv _ _ _ hm)).1
      simp only at this; omega
    · rw [hother w' hw] at hph ⊢
      obtain ⟨Q, hQ, hQt, hQm⟩ := I.disc_rt w' v a hph
        (hpre a _ (I.w_cur_invoked (by rw [hph]; simp)) hab)
      exact ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs',
        fun s hs' t v' hm => hQm s hs' t v' (hsv _ _ _ hm)⟩
  case read_rt =>
    intro r a hp hab
    rw [hcur] at hab
    rw [hr] at hp ⊢
    obtain ⟨Q, hQ, hQt, hii, hiii, hiv⟩ := I.read_rt r a hp (hpre a _ (I.r_cur_invoked hp) hab)
    exact ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs',
      fun s hs' d t v hm => hii s hs' d t v (hsv _ _ _ hm), fun sx => by rw [hs]; exact hiii sx,
      fun sx t v hm => hiv sx t v (hsv _ _ _ hm)⟩

/-- With a single writer, every completed operation has a tag `≤` the writer's tag. -/
lemma Inv.tok_le_sw (I : Inv next v₀ h C Wl tok) (hsw : ∀ w w' : W, w = w') (w : W)
    {a : OpId (Node W R S)} (ha : Completed h a) : tok a ≤ (C.wl w).tag := by
  have hW : ∀ x ∈ Wl, tok x ≤ (C.wl w).tag := by
    intro x hx
    obtain ⟨w', hw', -⟩ := I.W_mem x hx
    rw [hsw w w'] at *
    exact I.tok_le w' x hx hw'
  rcases I.kind (I.invoked_of_completed ha) with ⟨w', v, -, hv⟩ | ⟨r, -, hr⟩
  · exact hW a (I.W_complete a v hv ha)
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (completed_iff_respOf.1 ha)
    rcases I.read_resp a x hr hx with ⟨h1, -⟩ | ⟨y, hy, h1, -⟩
    · rw [h1]; exact bot_le
    · rw [← h1]; exact hW y hy

/-- **SWMR invocation** (lines 23–26): the write takes the tag `ts + 1` at once. -/
lemma Inv.wInvoke_sw {Vr : Variant} (hmw : Vr.mw = false) (hlt : ∀ w t, t < next w t)
    (hsw : ∀ w w' : W, w = w') (I : Inv next v₀ h C Wl tok)
    {w : W} {val : V} {l : WLoc S T V} {out : Multiset (Node W R S × Msg R T V)}
    (hinv : wInvoke Vr next w val (C.wl w) = some (l, out)) :
    Inv next v₀ (h ++ [.inv (.wr w) (.write val)]) (C.setW w l out C.net)
      (Wl ++ [(.wr w, (opsOf h (.wr w)).length)])
      (Function.update tok (.wr w, (opsOf h (.wr w)).length) (next w (C.wl w).tag)) := by
  obtain ⟨hidle, hcase⟩ := wInvoke_cases hinv
  obtain ⟨-, rfl, rfl⟩ : Vr.mw = false ∧
      l = { C.wl w with tag := next w (C.wl w).tag, val := val, ack := [], phase := .upd } ∧
      out = bcast (.writeRequest (next w (C.wl w).tag) val 0) := by
    rcases hcase with ⟨h1, -⟩ | h1
    · rw [hmw] at h1; cases h1
    · exact h1
  obtain ⟨hwf, hopOf, hresp, hcomp, hcur, hopOf', hb, hbn, hcb, hbi, hpre, hpreb, hops, hopsw,
    hresps⟩ := I.winv_hist (val := val) hidle
  set h' := h ++ [(Label.inv (.wr w) (.write val) : Label (Node W R S) (register V v₀))]
  set b : OpId (Node W R S) := (.wr w, (opsOf h (.wr w)).length) with hbdef
  set nt := next w (C.wl w).tag with hnt
  set tok' := Function.update tok b nt with htok'
  set C' := C.setW w { C.wl w with tag := nt, val := val, ack := [], phase := .upd }
    (bcast (.writeRequest nt val 0)) C.net with hC'
  have hr : ∀ r, C'.rl r = C.rl r := by simp [hC']
  have hs : ∀ s, C'.sl s = C.sl s := by simp [hC']
  have hother : ∀ w', w' ≠ w → C'.wl w' = C.wl w' := by intro w' h; simp [hC', h]
  have hself : C'.wl w = { C.wl w with tag := nt, val := val, ack := [], phase := .upd } := by
    simp [hC']
  have hsv : ∀ s d m, (Node.sv s, d, m) ∈ C'.sent → (Node.sv s, d, m) ∈ C.sent := by
    intro s d m hm; simpa [hC'] using hm
  have hbW : b ∉ Wl := fun hbW => hbn (I.W_mem b hbW).choose_spec.2.1
  have htok : ∀ x, Invoked h x → tok' x = tok x := by
    intro x hx; rw [htok', Function.update_of_ne]; rintro rfl; exact hbn hx
  have htokW : ∀ x ∈ Wl, tok' x = tok x := fun x hx => htok x (I.W_mem x hx).choose_spec.2.1
  have htokC : ∀ x, Completed h x → tok' x = tok x :=
    fun x hx => htok x (I.invoked_of_completed hx)
  have hV : ∀ v t, ValOK h Wl tok v t → ValOK h' (Wl ++ [b]) tok' v t :=
    fun v t hv => hv.mono hopOf (fun x h => List.mem_append_left _ h) htokW
  have hVb : ValOK h' (Wl ++ [b]) tok' val nt :=
    Or.inr ⟨b, by simp, by simp [htok'], hb⟩
  refine {
    wf := hwf, sv_ops := ?sv_ops, w_ops := ?w_ops, r_ops := ?r_ops, w_cnt := ?w_cnt,
    r_cnt := ?r_cnt, w_cur_disc := ?w_cur_disc, w_cur_upd := ?w_cur_upd,
    write_resp := ?write_resp, W_nodup := ?W_nodup, W_mem := ?W_mem,
    W_complete := ?W_complete, tok_le := ?tok_le, val_s := ?val_s, val_w := ?val_w,
    val_msg := ?val_msg, read_resp := ?read_resp, prec_W := ?prec_W, prec_R := ?prec_R,
    stable := ?stable, disc_rt := ?disc_rt, read_rt := ?read_rt }
  case sv_ops => intro s; rw [hops _ (by simp)]; exact I.sv_ops s
  case w_ops =>
    intro w' o ho
    by_cases hw : w' = w
    · subst hw; rw [hopsw, List.mem_append] at ho
      rcases ho with ho | ho
      · exact I.w_ops w' o ho
      · simp at ho; exact ⟨val, ho⟩
    · rw [hops _ (by simp [hw])] at ho; exact I.w_ops w' o ho
  case r_ops => intro r o ho; rw [hops _ (by simp)] at ho; exact I.r_ops r o ho
  case w_cnt =>
    intro w'
    by_cases hw : w' = w
    · subst hw; rw [hself, hopsw, hresps]; have := I.w_cnt w'; rw [hidle] at this; simp [this]
    · rw [hother w' hw, hops _ (by simp [hw]), hresps]; exact I.w_cnt w'
  case r_cnt => intro r; rw [hr, hops _ (by simp), hresps]; exact I.r_cnt r
  case w_cur_disc =>
    intro w' v hph
    rw [hcur]
    by_cases hw : w' = w
    · subst hw; rw [hself] at hph; cases hph
    · rw [hother w' hw] at hph; exact hopOf _ _ (I.w_cur_disc w' v hph)
  case w_cur_upd =>
    intro w' hph
    rw [hcur]
    by_cases hw : w' = w
    · subst hw; rw [hself, hcb]
      exact ⟨hb, by simp, by simp [htok']⟩
    · rw [hother w' hw] at hph ⊢
      obtain ⟨h1, h2, h3⟩ := I.w_cur_upd w' hph
      exact ⟨hopOf _ _ h1, List.mem_append_left _ h2, by rw [htokW _ h2]; exact h3⟩
  case write_resp =>
    intro x v r' hx hr'
    rw [hresp] at hr'
    rcases hopOf' x _ hx with hx | ⟨rfl, -⟩
    · exact I.write_resp x v r' hx hr'
    · exact absurd (I.invoked_of_completed (Completed.of_respOf_eq_some hr')) hbn
  case W_nodup => rw [← List.concat_eq_append]; exact I.W_nodup.concat hbW
  case W_mem =>
    intro x hx
    rcases List.mem_append.1 hx with hx1 | hx1
    · obtain ⟨w', h1, h2, h3, h4⟩ := I.W_mem x hx1
      refine ⟨w', h1, h2.mono, by rw [htokW x hx1]; exact h3, fun hxc => ?_⟩
      rw [hcur] at hxc
      by_cases hw : w' = w
      · subst hw; rw [hcb] at hxc; rw [hxc] at hx1; exact absurd hx1 hbW
      · rw [hother w' hw]; exact h4 hxc
    · rw [List.mem_singleton] at hx1; rw [hx1]
      exact ⟨w, rfl, hbi, ⟨(C.wl w).tag, by simp [htok', hnt]⟩, fun _ => by rw [hself]; rfl⟩
  case W_complete =>
    intro x v hx hc
    rw [hcomp] at hc
    rcases hopOf' x _ hx with hx | ⟨rfl, -⟩
    · exact List.mem_append_left _ (I.W_complete x v hx hc)
    · exact absurd (I.invoked_of_completed hc) hbn
  case tok_le =>
    intro w' x hx hxw
    rcases List.mem_append.1 hx with hx1 | hx1
    · rw [htokW x hx1]
      by_cases hw : w' = w
      · subst hw; rw [hself]; exact (I.tok_le w' x hx1 hxw).trans (hlt w' _).le
      · rw [hother w' hw]; exact I.tok_le w' x hx1 hxw
    · rw [List.mem_singleton] at hx1; rw [hx1] at hxw ⊢
      have hw : w = w' := by simpa [hbdef] using hxw
      subst hw
      rw [hself]; simp [htok']
  case val_s => intro s; rw [hs]; exact hV _ _ (I.val_s s)
  case val_w =>
    intro w'
    by_cases hw : w' = w
    · subst hw; rw [hself]; exact hVb
    · rw [hother w' hw]; exact hV _ _ (I.val_w w')
  case val_msg =>
    rintro ⟨a, b', c⟩ hm t v htv
    simp only [hC', setW_sent, Multiset.mem_add, mem_outMsgs_iff, mem_bcast_iff] at hm
    rcases hm with hm | ⟨-, -, rfl⟩
    · exact hV _ _ (I.val_msg _ hm t v htv)
    · simp only [Msg.tv_writeRequest, Option.some.injEq, Prod.mk.injEq] at htv
      obtain ⟨rfl, rfl⟩ := htv; exact hVb
  case read_resp =>
    intro x r' hx hr'
    rw [hresp] at hr'
    rcases hopOf' x _ hx with hx | ⟨-, h2⟩
    · rw [htokC x (Completed.of_respOf_eq_some hr')]
      exact hV _ _ (I.read_resp x r' hx hr')
    · cases h2
  case prec_W =>
    intro a c hac hc
    have ha : Completed h a := by
      have := hac.completed; rwa [hcomp] at this
    rw [htokC a ha]
    rcases List.mem_append.1 hc with hc | hc
    · rw [htokW c hc]
      exact I.prec_W a c (hpre a c (I.W_mem c hc).choose_spec.2.1 hac) hc
    · rw [List.mem_singleton] at hc; subst hc
      rw [show tok' b = nt by simp [htok']]
      exact (I.tok_le_sw hsw w ha).trans_lt (hlt w _)
  case prec_R =>
    intro a c hac hc hcc
    rw [hcomp] at hcc
    have hci := I.invoked_of_completed hcc
    rcases hopOf' c _ hc with hc | ⟨-, h2⟩
    · have hac' := hpre a c hci hac
      rw [htokC a hac'.completed, htokC c hcc]
      exact I.prec_R a c hac' hc hcc
    · cases h2
  case stable =>
    intro a ha; rw [hcomp] at ha; rw [htokC a ha]
    exact (I.stable a ha).mono (fun s => by rw [hs])
  case disc_rt =>
    intro w' v a hph hab
    rw [hcur] at hab
    by_cases hw : w' = w
    · subst hw; rw [hself] at hph; cases hph
    · rw [hother w' hw] at hph ⊢
      have hab' := hpre a _ (I.w_cur_invoked (by rw [hph]; simp)) hab
      rw [htokC a hab'.completed]
      obtain ⟨Q, hQ, hQt, hQm⟩ := I.disc_rt w' v a hph hab'
      exact ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs',
        fun s hs' t v' hm => hQm s hs' t v' (hsv _ _ _ hm)⟩
  case read_rt =>
    intro r a hp hab
    rw [hcur] at hab
    rw [hr] at hp ⊢
    have hab' := hpre a _ (I.r_cur_invoked hp) hab
    rw [htokC a hab'.completed]
    obtain ⟨Q, hQ, hQt, hii, hiii, hiv⟩ := I.read_rt r a hp hab'
    exact ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs',
      fun s hs' d t v hm => hii s hs' d t v (hsv _ _ _ hm), fun sx => by rw [hs]; exact hiii sx,
      fun sx t v hm => hiv sx t v (hsv _ _ _ hm)⟩

end Steps

end Podc.OhRAM
