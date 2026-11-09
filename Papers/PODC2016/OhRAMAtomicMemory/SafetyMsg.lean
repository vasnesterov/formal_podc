import Papers.PODC2016.OhRAMAtomicMemory.SafetySteps

/-!
# The message invariant

`CInv Vr C` collects the facts about local states and messages that do not involve the history:

* every message sent by a server carries a tag `≤` the current tag of the server (with
  `sRecv_tag_mono`: Lemmas 1, 6, 13, 17 of the paper);
* the operation counters carried by messages are bounded by the counter of the client;
* the acknowledgment lists of the clients consist of messages that were sent;
* counting (the network is not FIFO and messages may be received in any order, but every message
  is received at most once): `relays[r] = |got r|` (a server counts each relay at most once), at
  most one `readAck` per server and read operation is recorded by the reader, and at most one
  acknowledgment per server and phase is recorded by an MWMR writer.
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]

/-- The writer is in its discover phase. -/
def WPhase.isDisc : WPhase V → Bool
  | .disc _ => true
  | _ => false

@[simp] lemma WPhase.isDisc_disc (v : V) : (WPhase.disc v).isDisc = true := rfl
@[simp] lemma WPhase.isDisc_upd : (WPhase.upd : WPhase V).isDisc = false := rfl
@[simp] lemma WPhase.isDisc_idle : (WPhase.idle : WPhase V).isDisc = false := rfl

/-- Tokens of the relay counting for the senders `si`, receiver `sx`, read `(r, k)`: the
`readRequest` to `si` and the `readRelay` from `si` to `sx`. -/
def rtok (si sx : S) (r : R) (k : ℕ) : Node W R S × Node W R S × Msg R T V → Bool
  | (.rd r', .sv s, .readRequest k') => decide (r' = r ∧ s = si ∧ k' = k)
  | (.sv s, .sv s', .readRelay _ _ r' k') => decide (s = si ∧ s' = sx ∧ r' = r ∧ k' = k)
  | _ => false

/-- `readAck`s from `sx` to `r` for `read_op = k`. -/
def atok (sx : S) (r : R) (k : ℕ) : Node W R S × Node W R S × Msg R T V → Bool
  | (.sv s, .rd r', .readAck _ _ k') => decide (s = sx ∧ r' = r ∧ k' = k)
  | _ => false

/-- Messages between writer `w` and server `s` with `write_op = k`. -/
def wtok (w : W) (s : S) (k : ℕ) : Node W R S × Node W R S × Msg R T V → Bool
  | (.wr w', .sv s', .discover k') => decide (w' = w ∧ s' = s ∧ k' = k)
  | (.wr w', .sv s', .writeRequest _ _ k') => decide (w' = w ∧ s' = s ∧ k' = k)
  | (.sv s', .wr w', .discoverAck _ _ k') => decide (w' = w ∧ s' = s ∧ k' = k)
  | (.sv s', .wr w', .writeAck _ _ k') => decide (w' = w ∧ s' = s ∧ k' = k)
  | _ => false

/-- The entry `e` of the acknowledgment list of writer `w` comes from a message that was sent
(and accepted: SWMR, the tag is the writer's; MWMR, the operation counter is the writer's). -/
def WAckSent (Vr : Variant) (C : Cfg W R S T V) (w : W) (e : S × T × V) : Prop :=
  if Vr.mw then
    (Node.sv e.1, Node.wr w, Msg.writeAck e.2.1 e.2.2 (C.wl w).op) ∈ C.sent ∨
      (Node.sv e.1, Node.wr w, Msg.discoverAck e.2.1 e.2.2 (C.wl w).op) ∈ C.sent
  else (∃ k, (Node.sv e.1, Node.wr w, Msg.writeAck e.2.1 e.2.2 k) ∈ C.sent) ∧ e.2.1 = (C.wl w).tag

/-- The message invariant. -/
structure CInv (Vr : Variant) (C : Cfg W R S T V) : Prop where
  net_sent : ∀ x ∈ C.net, x ∈ C.sent
  tag_le : ∀ s d m t v, (Node.sv s, d, m) ∈ C.sent → Msg.tv m = some (t, v) → t ≤ (C.sl s).tag
  req_le : ∀ r s k, (Node.rd r, Node.sv s, Msg.readRequest k) ∈ C.sent → k ≤ (C.rl r).op
  rel_le : ∀ s d t v r k, (Node.sv s, d, Msg.readRelay t v r k) ∈ C.sent → k ≤ (C.rl r).op
  rel_dst : ∀ s r' t v r k, (Node.sv s, Node.rd r', Msg.readRelay t v r k) ∈ C.sent → r' = r
  rack_le : ∀ s r t v k, (Node.sv s, Node.rd r, Msg.readAck t v k) ∈ C.sent → k ≤ (C.rl r).op
  ops_le : ∀ s r, (C.sl s).ops r ≤ (C.rl r).op
  rack_sent : ∀ r e, e ∈ (C.rl r).ack →
    (Node.sv e.1, Node.rd r, Msg.readAck e.2.1 e.2.2 (C.rl r).op) ∈ C.sent
  rrel_sent : ∀ r e, e ∈ (C.rl r).relay →
    ∃ r', (Node.sv e.1, Node.rd r, Msg.readRelay e.2.1 e.2.2 r' (C.rl r).op) ∈ C.sent
  rrel_nodup : ∀ r, (C.rl r).relay.Nodup
  relays_card : ∀ s r, (C.sl s).relays r = ((C.sl s).got r).card
  relay_tok : ∀ si sx r k, C.net.countP (fun x => rtok si sx r k x) +
    (if (C.sl sx).ops r = k ∧ si ∈ (C.sl sx).got r then 1 else 0) ≤ 1
  rack_tok : ∀ sx r, C.net.countP (fun x => atok sx r (C.rl r).op x) +
    (C.rl r).ack.countP (fun e => decide (e.1 = sx)) ≤
      if (C.sl sx).ops r = (C.rl r).op ∧ maj S ≤ (C.sl sx).relays r then 1 else 0
  wack_sent : ∀ w e, e ∈ (C.wl w).ack → WAckSent Vr C w e
  wack_nodup : ∀ w, (C.wl w).ack.Nodup
  disc_le : Vr.mw = true → ∀ w s k, (Node.wr w, Node.sv s, Msg.discover k) ∈ C.sent →
    k ≤ (C.wl w).op ∧ (k = (C.wl w).op → (C.wl w).phase.isDisc = true)
  dack_le : Vr.mw = true → ∀ w s t v k, (Node.sv s, Node.wr w, Msg.discoverAck t v k) ∈ C.sent →
    k ≤ (C.wl w).op ∧ (k = (C.wl w).op → (C.wl w).phase.isDisc = true)
  wreq_le : Vr.mw = true → ∀ w s t v k, (Node.wr w, Node.sv s, Msg.writeRequest t v k) ∈ C.sent →
    1 ≤ k ∧ k ≤ (C.wl w).op ∧
      (k = (C.wl w).op → (C.wl w).phase.isDisc = false ∧ t = (C.wl w).tag)
  wack_le : Vr.mw = true → ∀ w s t v k, (Node.sv s, Node.wr w, Msg.writeAck t v k) ∈ C.sent →
    k ≤ (C.wl w).op ∧ (k = (C.wl w).op → (C.wl w).phase.isDisc = false ∧ (C.wl w).tag ≤ t)
  wops : Vr.mw = true → ∀ s w, 0 < (C.sl s).wops w →
    ∃ t v, (Node.wr w, Node.sv s, Msg.writeRequest t v ((C.sl s).wops w)) ∈ C.sent ∧
      t ≤ (C.sl s).tag
  wtok_le : Vr.mw = true → ∀ w s, C.net.countP (fun x => wtok w s (C.wl w).op x) +
    (C.wl w).ack.countP (fun e => decide (e.1 = s)) ≤ 1
  disc_mw : ∀ w v, (C.wl w).phase = .disc v → Vr.mw = true

/-! ## Basic lemmas -/

omit [LinearOrder T] [OrderBot T] in
@[simp] lemma mem_outMsgs_iff {p a b : Node W R S} {c : Msg R T V}
    {out : Multiset (Node W R S × Msg R T V)} :
    (a, b, c) ∈ outMsgs p out ↔ a = p ∧ (b, c) ∈ out := by
  simp only [outMsgs, Multiset.mem_map, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨b', c', h, rfl, rfl, rfl⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨b, c, h, rfl, rfl, rfl⟩

omit [LinearOrder T] [OrderBot T] in
@[simp] lemma mem_bcast_iff {d : Node W R S} {c m : Msg R T V} :
    (d, c) ∈ (bcast m : Multiset (Node W R S × Msg R T V)) ↔ (∃ s, d = .sv s) ∧ c = m := by
  simp only [bcast, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨s, rfl, rfl⟩; exact ⟨⟨s, rfl⟩, rfl⟩
  · rintro ⟨⟨s, rfl⟩, rfl⟩; exact ⟨s, rfl, rfl⟩

lemma maj_pos : 0 < maj S := Nat.succ_pos _

/-- Two majorities of servers intersect. -/
lemma maj_inter {A B : Finset S} (hA : maj S ≤ A.card) (hB : maj S ≤ B.card) :
    (A ∩ B).Nonempty := by
  apply Finset.inter_nonempty_of_card_lt_card_add_card (Finset.subset_univ _)
    (Finset.subset_univ _)
  simp only [Finset.card_univ, maj] at *
  omega

/-- Servers of a list of acknowledgments with at most one entry per server. -/
lemma card_servers {L : List (S × T × V)} (h : ∀ s, L.countP (fun e => decide (e.1 = s)) ≤ 1) :
    (L.map Prod.fst).toFinset.card = L.length := by
  rw [List.toFinset_card_of_nodup, List.length_map]
  rw [List.nodup_iff_count_le_one]
  intro s
  rw [List.count, List.countP_map]; refine le_trans (le_of_eq ?_) (h s); congr 1

omit [Fintype S] [LinearOrder T] [OrderBot T] [DecidableEq V] in
lemma rtok_iff {si sx : S} {r : R} {k : ℕ} {x : Node W R S × Node W R S × Msg R T V} :
    rtok si sx r k x = true ↔ x = (.rd r, .sv si, .readRequest k) ∨
      ∃ t v, x = (.sv si, .sv sx, .readRelay t v r k) := by
  obtain ⟨a, b, c⟩ := x
  cases a <;> cases b <;> cases c <;> simp [rtok]

omit [Fintype S] [LinearOrder T] [OrderBot T] [DecidableEq V] in
lemma atok_iff {sx : S} {r : R} {k : ℕ} {x : Node W R S × Node W R S × Msg R T V} :
    atok sx r k x = true ↔ ∃ t v, x = (.sv sx, .rd r, .readAck t v k) := by
  obtain ⟨a, b, c⟩ := x
  cases a <;> cases b <;> cases c <;> simp [atok]

omit [Fintype S] [LinearOrder T] [OrderBot T] [DecidableEq V] in
lemma wtok_iff {w : W} {s : S} {k : ℕ} {x : Node W R S × Node W R S × Msg R T V} :
    wtok w s k x = true ↔ x = (.wr w, .sv s, .discover k) ∨
      (∃ t v, x = (.wr w, .sv s, .writeRequest t v k)) ∨
      (∃ t v, x = (.sv s, .wr w, .discoverAck t v k)) ∨
      ∃ t v, x = (.sv s, .wr w, .writeAck t v k) := by
  obtain ⟨a, b, c⟩ := x
  cases a <;> cases b <;> cases c <;> simp [wtok] <;> tauto

/-- No new token among the sent messages. -/
lemma countP_eq_zero_of {P : Node W R S × Node W R S × Msg R T V → Bool}
    {M : Multiset (Node W R S × Node W R S × Msg R T V)} (h : ∀ x ∈ M, P x = false) :
    M.countP (fun x => P x) = 0 :=
  Multiset.countP_eq_zero.2 fun x hx => by simp [h x hx]

lemma WAckSent.mono' {Vr : Variant} {C C' : Cfg W R S T V} {w : W} {e : S × T × V}
    (h : WAckSent Vr C w e) (hs : C.sent ≤ C'.sent) (hop : (C'.wl w).op = (C.wl w).op)
    (htag : (C'.wl w).tag = (C.wl w).tag) :
    WAckSent Vr C' w e := by
  unfold WAckSent at *
  rw [hop, htag]
  split_ifs at h ⊢
  · exact h.imp (Multiset.mem_of_le hs) (Multiset.mem_of_le hs)
  · exact ⟨h.1.imp fun k hk => Multiset.mem_of_le hs hk, h.2⟩

lemma WAckSent.mono {Vr : Variant} {C C' : Cfg W R S T V} {w : W} {e : S × T × V}
    (h : WAckSent Vr C w e) (hs : C.sent ≤ C'.sent) (hw : C'.wl w = C.wl w) :
    WAckSent Vr C' w e := by
  unfold WAckSent at *
  rw [hw]
  split_ifs at h ⊢
  · exact h.imp (Multiset.mem_of_le hs) (Multiset.mem_of_le hs)
  · exact ⟨h.1.imp fun k hk => Multiset.mem_of_le hs hk, h.2⟩

lemma countP_outMsgs_zero {P : Node W R S × Node W R S × Msg R T V → Bool} {p : Node W R S}
    {out : Multiset (Node W R S × Msg R T V)} (h : ∀ b c, P (p, b, c) = false) :
    (outMsgs p out).countP (fun x => P x) = 0 :=
  Multiset.countP_eq_zero.2 fun x hx => by
    obtain ⟨a, b, c⟩ := x
    rw [mem_outMsgs_iff] at hx
    rw [hx.1, h b c]; simp

section Tok
omit [Fintype S] [LinearOrder T] [OrderBot T] [DecidableEq V]
variable {si sx s : S} {r : R} {k : ℕ} {w : W} (b : Node W R S) (c : Msg R T V)
@[simp] lemma rtok_wr (w : W) : rtok si sx r k ((.wr w : Node W R S), b, c) = false := by
  cases b <;> cases c <;> rfl
@[simp] lemma rtok_sv_rd (s : S) (r' : R) :
    rtok si sx r k ((.sv s : Node W R S), (.rd r' : Node W R S), c) = false := by cases c <;> rfl
@[simp] lemma rtok_sv_wr (s : S) (w : W) :
    rtok si sx r k ((.sv s : Node W R S), (.wr w : Node W R S), c) = false := by cases c <;> rfl
@[simp] lemma atok_wr (w : W) : atok sx r k ((.wr w : Node W R S), b, c) = false := by
  cases b <;> cases c <;> rfl
@[simp] lemma atok_rd (r' : R) : atok sx r k ((.rd r' : Node W R S), b, c) = false := by
  cases b <;> cases c <;> rfl
@[simp] lemma atok_sv_sv (s s' : S) :
    atok sx r k ((.sv s : Node W R S), (.sv s' : Node W R S), c) = false := by cases c <;> rfl
@[simp] lemma atok_sv_wr (s : S) (w : W) :
    atok sx r k ((.sv s : Node W R S), (.wr w : Node W R S), c) = false := by cases c <;> rfl
@[simp] lemma wtok_rd (r' : R) : wtok w s k ((.rd r' : Node W R S), b, c) = false := by
  cases b <;> cases c <;> rfl
@[simp] lemma wtok_sv_sv (s₁ s₂ : S) :
    wtok w s k ((.sv s₁ : Node W R S), (.sv s₂ : Node W R S), c) = false := by cases c <;> rfl
@[simp] lemma wtok_sv_rd (s₁ : S) (r' : R) :
    wtok w s k ((.sv s₁ : Node W R S), (.rd r' : Node W R S), c) = false := by cases c <;> rfl
lemma wtok_wr_ne {w' : W} (h : w' ≠ w) : wtok w s k ((.wr w' : Node W R S), b, c) = false := by
  cases b <;> cases c <;> simp [wtok, h]
end Tok

@[simp] lemma countP_singleton' {α : Type} (p : α → Prop) [DecidablePred p] (a : α) :
    ({a} : Multiset α).countP p = if p a then 1 else 0 := by
  rw [← Multiset.cons_zero, Multiset.countP_cons]; simp

lemma countP_insert_le {α : Type} [DecidableEq α] (p : α → Bool) (l : List α) (a : α) :
    (l.insert a).countP p ≤ l.countP p + if p a then 1 else 0 := by
  by_cases h : a ∈ l
  · rw [List.insert_of_mem h]; omega
  · rw [List.insert_of_not_mem h, List.countP_cons]

lemma countP_insert_of_not {α : Type} [DecidableEq α] {p : α → Bool} (l : List α) {a : α}
    (ha : p a = false) : (l.insert a).countP p = l.countP p := by
  by_cases h : a ∈ l
  · rw [List.insert_of_mem h]
  · rw [List.insert_of_not_mem h, List.countP_cons]; simp [ha]

/-! ## Initial configuration and silent steps -/

variable {Vr : Variant} {next : W → T → T} {v₀ : V}

lemma cinv_init : CInv Vr ((proto Vr next v₀).initCfg : Cfg W R S T V) where
  net_sent _ h := by simp [Protocol.initCfg] at h
  tag_le _ _ _ _ _ h := by simp [Protocol.initCfg] at h
  req_le _ _ _ h := by simp [Protocol.initCfg] at h
  rel_le _ _ _ _ _ _ h := by simp [Protocol.initCfg] at h
  rel_dst _ _ _ _ _ _ h := by simp [Protocol.initCfg] at h
  rack_le _ _ _ _ _ h := by simp [Protocol.initCfg] at h
  ops_le _ _ := by simp [Protocol.initCfg, Cfg.sl, proto, initLoc]
  rack_sent _ _ h := by simp [Protocol.initCfg, Cfg.rl, proto, initLoc] at h
  rrel_sent _ _ h := by simp [Protocol.initCfg, Cfg.rl, proto, initLoc] at h
  rrel_nodup _ := by simp [Protocol.initCfg, Cfg.rl, proto, initLoc]
  relays_card _ _ := by simp [Protocol.initCfg, Cfg.sl, proto, initLoc]
  relay_tok _ _ _ _ := by simp [Protocol.initCfg, Cfg.sl, proto, initLoc]
  rack_tok _ _ := by simp [Protocol.initCfg, Cfg.rl, proto, initLoc]
  wack_sent _ _ h := by simp [Protocol.initCfg, Cfg.wl, proto, initLoc] at h
  wack_nodup _ := by simp [Protocol.initCfg, Cfg.wl, proto, initLoc]
  disc_le _ _ _ _ h := by simp [Protocol.initCfg] at h
  dack_le _ _ _ _ _ _ h := by simp [Protocol.initCfg] at h
  wreq_le _ _ _ _ _ _ h := by simp [Protocol.initCfg] at h
  wack_le _ _ _ _ _ _ h := by simp [Protocol.initCfg] at h
  wops _ _ _ h := by simp [Protocol.initCfg, Cfg.sl, proto, initLoc] at h
  wtok_le _ _ _ := by simp [Protocol.initCfg, Cfg.wl, proto, initLoc]
  disc_mw _ _ h := by simp [Protocol.initCfg, Cfg.wl, proto, initLoc] at h

/-- Silent steps (drop, crash, skip, receptions without effect) preserve `CInv`. -/
lemma CInv.of_silent {C C' : Cfg W R S T V} (I : CInv Vr C) (hloc : C'.loc = C.loc)
    (hsent : C'.sent = C.sent) (hnet : C'.net ≤ C.net) : CInv Vr C' := by
  obtain ⟨loc', net', sent', cr'⟩ := C'
  simp only at hloc hsent hnet; subst hloc hsent
  exact ⟨fun x hx => I.net_sent x (Multiset.mem_of_le hnet hx), I.tag_le, I.req_le, I.rel_le,
    I.rel_dst, I.rack_le, I.ops_le, I.rack_sent, I.rrel_sent, I.rrel_nodup, I.relays_card,
    fun si sx r k => le_trans (Nat.add_le_add_right (Multiset.countP_le_of_le _ hnet) _)
      (I.relay_tok si sx r k),
    fun sx r => le_trans (Nat.add_le_add_right (Multiset.countP_le_of_le _ hnet) _)
      (I.rack_tok sx r),
    I.wack_sent, I.wack_nodup, I.disc_le, I.dack_le, I.wreq_le, I.wack_le, I.wops,
    fun hmw w s => le_trans (Nat.add_le_add_right (Multiset.countP_le_of_le _ hnet) _)
      (I.wtok_le hmw w s), I.disc_mw⟩

/-! ## Reader invocations -/

lemma CInv.rInvoke {C : Cfg W R S T V} (I : CInv Vr C) {r : R} {l : RLoc S T V}
    {out : Multiset (Node W R S × Msg R T V)} (h : rInvoke (C.rl r) = some (l, out)) :
    CInv Vr (C.setR r l out C.net) := by
  obtain ⟨-, rfl, rfl⟩ := rInvoke_eq h
  set k := (C.rl r).op + 1 with hk
  have hop : ∀ r', (C.rl r').op ≤ (if r' = r then (⟨k, true, [], []⟩ : RLoc S T V)
      else C.rl r').op := by
    intro r'; split_ifs with h
    · subst h; simp [hk]
    · exact le_rfl
  refine {
    net_sent := ?net_sent, tag_le := ?tag_le, req_le := ?req_le, rel_le := ?rel_le, rel_dst := ?rel_dst,
    rack_le := ?rack_le, ops_le := ?ops_le, rack_sent := ?rack_sent, rrel_sent := ?rrel_sent, rrel_nodup := ?rrel_nodup,
    relays_card := ?relays_card, relay_tok := ?relay_tok, rack_tok := ?rack_tok, wack_sent := ?wack_sent, wack_nodup := ?wack_nodup,
    disc_le := ?disc_le, dack_le := ?dack_le, wreq_le := ?wreq_le, wack_le := ?wack_le, wops := ?wops, wtok_le := ?wtok_le, disc_mw := ?disc_mw }
  case net_sent =>
    intro x hx
    simp only [setR_net, setR_sent, Multiset.mem_add] at hx ⊢
    exact hx.imp_left (I.net_sent x)
  case tag_le =>
    intro s d m t v hm
    simp only [setR_sent, Multiset.mem_add, mem_outMsgs_iff, reduceCtorEq, false_and,
      or_false] at hm
    simpa using I.tag_le s d m t v hm
  case req_le =>
    intro r' s k' hm
    simp only [setR_sent, Multiset.mem_add, mem_outMsgs_iff, mem_bcast_iff, Node.rd.injEq,
      Msg.readRequest.injEq] at hm
    simp only [setR_rl]
    rcases hm with hm | ⟨rfl, -, rfl⟩
    · exact (I.req_le r' s k' hm).trans (hop r')
    · simp
  case rel_le =>
    intro s d t v r' k' hm
    simp only [setR_sent, Multiset.mem_add, mem_outMsgs_iff, reduceCtorEq, false_and,
      or_false] at hm
    simp only [setR_rl]
    exact (I.rel_le s d t v r' k' hm).trans (hop r')
  case rel_dst =>
    intro s r' t v r'' k' hm
    simp only [setR_sent, Multiset.mem_add, mem_outMsgs_iff, reduceCtorEq, false_and,
      or_false] at hm
    exact I.rel_dst s r' t v r'' k' hm
  case rack_le =>
    intro s r' t v k' hm
    simp only [setR_sent, Multiset.mem_add, mem_outMsgs_iff, reduceCtorEq, false_and,
      or_false] at hm
    simp only [setR_rl]
    exact (I.rack_le s r' t v k' hm).trans (hop r')
  case ops_le =>
    intro s r'
    simp only [setR_sl, setR_rl]
    exact (I.ops_le s r').trans (hop r')
  case rack_sent =>
    intro r' e he
    simp only [setR_rl] at he ⊢
    split_ifs at he ⊢ with hr
    · simp at he
    · simp only [setR_sent, Multiset.mem_add]; exact Or.inl (I.rack_sent r' e he)
  case rrel_sent =>
    intro r' e he
    simp only [setR_rl] at he ⊢
    split_ifs at he ⊢ with hr
    · simp at he
    · simp only [setR_sent, Multiset.mem_add]
      obtain ⟨r'', h⟩ := I.rrel_sent r' e he
      exact ⟨r'', Or.inl h⟩
  case rrel_nodup =>
    intro r'
    simp only [setR_rl]
    split_ifs
    · exact List.nodup_nil
    · exact I.rrel_nodup r'
  case relays_card => simpa using I.relays_card
  case relay_tok =>
    intro si sx r' k'
    simp only [setR_net, setR_sl, Multiset.countP_add]
    rw [countP_outMsgs_bcast]
    by_cases hrk : r' = r ∧ k' = k
    · obtain ⟨rfl, rfl⟩ := hrk
      have h0 : C.net.countP (fun x => rtok si sx r' k x) = 0 := by
        refine countP_eq_zero_of fun x hx => ?_
        by_contra hc
        rcases rtok_iff.1 (Bool.not_eq_false _ ▸ hc) with rfl | ⟨t, v, rfl⟩
        · have := I.req_le _ _ _ (I.net_sent _ hx); omega
        · have := I.rel_le _ _ _ _ _ _ (I.net_sent _ hx); omega
      have h1 : ¬ ((C.sl sx).ops r' = k ∧ si ∈ (C.sl sx).got r') := by
        rintro ⟨h1, -⟩; have := I.ops_le sx r'; omega
      rw [h0, ite_eq_right h1, Finset.card_eq_one.2 ⟨si, by ext s; simp [rtok, eq_comm]⟩]
    · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun s _ => by
        simp only [rtok, decide_eq_true_eq]
        rintro ⟨rfl, -, rfl⟩; exact hrk ⟨rfl, rfl⟩), add_zero]
      exact I.relay_tok si sx r' k'
  case rack_tok =>
    intro sx r'
    simp only [setR_net, setR_sl, setR_rl, Multiset.countP_add]
    have hz : (outMsgs (Node.rd r : Node W R S) (bcast (Msg.readRequest k : Msg R T V))).countP
        (fun x => atok sx r' (if r' = r then (⟨k, true, [], []⟩ : RLoc S T V) else C.rl r').op x)
        = 0 := by
      refine countP_eq_zero_of fun x hx => ?_
      obtain ⟨a, b, c⟩ := x
      simp only [mem_outMsgs_iff, mem_bcast_iff] at hx
      obtain ⟨rfl, ⟨s, rfl⟩, rfl⟩ := hx
      rfl
    rw [hz, add_zero]
    by_cases hr : r' = r
    · subst hr
      have h0 : C.net.countP (fun x => atok sx r' k x) = 0 := by
        refine countP_eq_zero_of fun x hx => ?_
        by_contra hc
        obtain ⟨t, v, rfl⟩ := atok_iff.1 (Bool.not_eq_false _ ▸ hc)
        have := I.rack_le _ _ _ _ _ (I.net_sent _ hx); omega
      simp [h0]
    · simp only [hr, ite_false]
      exact I.rack_tok sx r'
  case wack_sent =>
    intro w e he
    simp only [setR_wl] at he
    exact (I.wack_sent w e he).mono (Multiset.le_add_right _ _) (by simp)
  case wack_nodup => simpa using I.wack_nodup
  case disc_le =>
    intro hmw w s k' hm
    simp only [setR_sent, Multiset.mem_add, mem_outMsgs_iff, reduceCtorEq, false_and,
      or_false] at hm
    simpa using I.disc_le hmw w s k' hm
  case dack_le =>
    intro hmw w s t v k' hm
    simp only [setR_sent, Multiset.mem_add, mem_outMsgs_iff, reduceCtorEq, false_and,
      or_false] at hm
    simpa using I.dack_le hmw w s t v k' hm
  case wreq_le =>
    intro hmw w s t v k' hm
    simp only [setR_sent, Multiset.mem_add, mem_outMsgs_iff, reduceCtorEq, false_and,
      or_false] at hm
    simpa using I.wreq_le hmw w s t v k' hm
  case wack_le =>
    intro hmw w s t v k' hm
    simp only [setR_sent, Multiset.mem_add, mem_outMsgs_iff, reduceCtorEq, false_and,
      or_false] at hm
    simpa using I.wack_le hmw w s t v k' hm
  case wops =>
    intro hmw s w hw
    simp only [setR_sl] at hw ⊢
    obtain ⟨t, v, h1, h2⟩ := I.wops hmw s w hw
    exact ⟨t, v, by simp [h1], h2⟩
  case wtok_le =>
    intro hmw w s
    simp only [setR_net, setR_wl, Multiset.countP_add]
    have hz : (outMsgs (Node.rd r : Node W R S) (bcast (Msg.readRequest k : Msg R T V))).countP
        (fun x => wtok w s (C.wl w).op x) = 0 := by
      refine countP_eq_zero_of fun x hx => ?_
      obtain ⟨a, b, c⟩ := x
      simp only [mem_outMsgs_iff, mem_bcast_iff] at hx
      obtain ⟨rfl, ⟨s, rfl⟩, rfl⟩ := hx
      rfl
    rw [hz, add_zero]
    exact I.wtok_le hmw w s
  case disc_mw => intro w v h; simp only [setR_wl] at h; exact I.disc_mw w v h

/-! ## Receptions by readers -/

lemma CInv.rRecv {C : Cfg W R S T V} (I : CInv Vr C) {r : R} {s : S} {m : Msg R T V}
    (hx : (Node.sv s, Node.rd r, m) ∈ C.net) :
    CInv Vr (C.setR r (rWait Vr v₀ (rRecord Vr s m (C.rl r))).1 0
      (C.net.erase (Node.sv s, Node.rd r, m))) := by
  set l1 := rRecord Vr s m (C.rl r) with hl1
  set C' := C.setR r (rWait Vr v₀ l1).1 0 (C.net.erase (Node.sv s, Node.rd r, m)) with hC'
  have hsent : C'.sent = C.sent := by simp [hC']
  have hnet : C'.net ≤ C.net := by simpa [hC'] using Multiset.erase_le _ _
  have hw : ∀ w, C'.wl w = C.wl w := by simp [hC']
  have hs : ∀ s, C'.sl s = C.sl s := by simp [hC']
  have hop : ∀ r', (C'.rl r').op = (C.rl r').op := by
    intro r'; simp only [hC', setR_rl]; split_ifs with h
    · subst h; simp [hl1]
    · rfl
  have hother : ∀ r', r' ≠ r → C'.rl r' = C.rl r' := by
    intro r' h; simp [hC', h]
  have hself : C'.rl r = (rWait Vr v₀ l1).1 := by simp [hC']
  have hxs : (Node.sv s, Node.rd r, m) ∈ C.sent := I.net_sent _ hx
  refine {
    net_sent := ?net_sent, tag_le := ?tag_le, req_le := ?req_le, rel_le := ?rel_le,
    rel_dst := ?rel_dst, rack_le := ?rack_le, ops_le := ?ops_le, rack_sent := ?rack_sent,
    rrel_sent := ?rrel_sent, rrel_nodup := ?rrel_nodup, relays_card := ?relays_card,
    relay_tok := ?relay_tok, rack_tok := ?rack_tok, wack_sent := ?wack_sent,
    wack_nodup := ?wack_nodup, disc_le := ?disc_le, dack_le := ?dack_le, wreq_le := ?wreq_le,
    wack_le := ?wack_le, wops := ?wops, wtok_le := ?wtok_le, disc_mw := ?disc_mw }
  case net_sent => intro x h; rw [hsent]; exact I.net_sent x (Multiset.mem_of_le hnet h)
  case tag_le => rw [hsent]; simpa [hs] using I.tag_le
  case req_le => rw [hsent]; simpa [hop] using I.req_le
  case rel_le => rw [hsent]; simpa [hop] using I.rel_le
  case rel_dst => rw [hsent]; exact I.rel_dst
  case rack_le => rw [hsent]; simpa [hop] using I.rack_le
  case ops_le => simpa [hop, hs] using I.ops_le
  case rack_sent =>
    intro r' e he
    rw [hsent, hop]
    by_cases hr : r' = r
    · subst hr
      rw [hself, rWait_ack] at he
      rcases rRecord_cases Vr s m (C.rl r') with h | ⟨t, v, rfl, h⟩ | ⟨t, v, r'', -, -, h⟩ <;>
        rw [hl1, h] at he
      · exact I.rack_sent r' e he
      · rcases List.mem_insert_iff.1 he with rfl | he
        · exact hxs
        · exact I.rack_sent r' e he
      · exact I.rack_sent r' e he
    · rw [hother r' hr] at he; exact I.rack_sent r' e he
  case rrel_sent =>
    intro r' e he
    rw [hsent, hop]
    by_cases hr : r' = r
    · subst hr
      rw [hself, rWait_relay] at he
      rcases rRecord_cases Vr s m (C.rl r') with h | ⟨t, v, -, h⟩ | ⟨t, v, r'', -, rfl, h⟩ <;>
        rw [hl1, h] at he
      · exact I.rrel_sent r' e he
      · exact I.rrel_sent r' e he
      · rcases List.mem_insert_iff.1 he with rfl | he
        · exact ⟨r'', hxs⟩
        · exact I.rrel_sent r' e he
    · rw [hother r' hr] at he; exact I.rrel_sent r' e he
  case rrel_nodup =>
    intro r'
    by_cases hr : r' = r
    · subst hr
      rw [hself, rWait_relay]
      rcases rRecord_cases Vr s m (C.rl r') with h | ⟨t, v, -, h⟩ | ⟨t, v, r'', -, -, h⟩ <;>
        rw [hl1, h]
      · exact I.rrel_nodup r'
      · exact I.rrel_nodup r'
      · exact (I.rrel_nodup r').insert
    · rw [hother r' hr]; exact I.rrel_nodup r'
  case relays_card => simpa [hs] using I.relays_card
  case relay_tok =>
    intro si sx r' k
    rw [hs]
    exact le_trans (Nat.add_le_add_right (Multiset.countP_le_of_le _ hnet) _)
      (I.relay_tok si sx r' k)
  case rack_tok =>
    intro sx r'
    rw [hs, hop]
    by_cases hr : r' = r
    · subst hr
      rw [hself, rWait_ack]
      have hcnt := countP_erase_add (fun x => atok sx r' (C.rl r').op x = true) (o := 0) hx
      simp only [add_zero, Multiset.countP_zero] at hcnt
      have hnet' : C'.net = C.net.erase (Node.sv s, Node.rd r', m) := by simp [hC']
      rw [hnet']
      have := I.rack_tok sx r'
      rcases rRecord_cases Vr s m (C.rl r') with h | ⟨t, v, hm, h⟩ | ⟨t, v, r'', -, -, h⟩ <;>
        rw [hl1, h]
      · omega
      · subst hm
        dsimp only
        by_cases hsx : s = sx
        · subst hsx
          have h2 := countP_insert_le (fun e => decide (e.1 = s)) (C.rl r').ack (s, t, v)
          have hP : atok (W := W) s r' (C.rl r').op (Node.sv s, Node.rd r', Msg.readAck t v (C.rl r').op)
              = true := by simp [atok]
          simp only [hP, ite_true, decide_true] at hcnt h2
          omega
        · have hP : atok (W := W) sx r' (C.rl r').op (Node.sv s, Node.rd r', Msg.readAck t v (C.rl r').op)
              = false := by simp [atok, hsx]
          simp only [hP, Bool.false_eq_true, ite_false, add_zero] at hcnt
          rw [countP_insert_of_not _ (by simp [hsx])]
          omega
      · dsimp only; omega
    · rw [hother r' hr]
      exact le_trans (Nat.add_le_add_right (Multiset.countP_le_of_le _ hnet) _)
        (I.rack_tok sx r')
  case wack_sent =>
    intro w e he
    rw [hw] at he
    exact (I.wack_sent w e he).mono (by rw [hsent]) (hw w)
  case wack_nodup => simpa [hw] using I.wack_nodup
  case disc_le => rw [hsent]; simpa [hw] using I.disc_le
  case dack_le => rw [hsent]; simpa [hw] using I.dack_le
  case wreq_le => rw [hsent]; simpa [hw] using I.wreq_le
  case wack_le => rw [hsent]; simpa [hw] using I.wack_le
  case wops => rw [hsent]; simpa [hs] using I.wops
  case wtok_le =>
    intro hmw w s'
    rw [hw]
    exact le_trans (Nat.add_le_add_right (Multiset.countP_le_of_le _ hnet) _)
      (I.wtok_le hmw w s')
  case disc_mw => intro w v h; rw [hw] at h; exact I.disc_mw w v h

/-! ## Writer invocations -/

lemma CInv.wInvoke {C : Cfg W R S T V} (I : CInv Vr C) {w : W} {val : V} {l : WLoc S T V}
    {out : Multiset (Node W R S × Msg R T V)} (h : wInvoke Vr next w val (C.wl w) = some (l, out)) :
    CInv Vr (C.setW w l out C.net) := by
  obtain ⟨hidle, hcase⟩ := wInvoke_cases h
  set C' := C.setW w l out C.net with hC'
  have hsent : C'.sent = C.sent + outMsgs (.wr w) out := rfl
  have hnet : C'.net = C.net + outMsgs (.wr w) out := rfl
  have hr : ∀ r, C'.rl r = C.rl r := by simp [hC']
  have hs : ∀ s, C'.sl s = C.sl s := by simp [hC']
  have hother : ∀ w', w' ≠ w → C'.wl w' = C.wl w' := by intro w' h; simp [hC', h]
  have hself : C'.wl w = l := by simp [hC']
  have hsv : ∀ s d m, (Node.sv s, d, m) ∈ C'.sent → (Node.sv s, d, m) ∈ C.sent := by
    intro s d m hm; simpa [hsent] using hm
  have hrd : ∀ r d m, (Node.rd r, d, m) ∈ C'.sent → (Node.rd r, d, m) ∈ C.sent := by
    intro r d m hm; simpa [hsent] using hm
  -- the messages of the writer
  have hout : ∀ d m, (d, m) ∈ out → (Vr.mw = true ∧ m = .discover l.op ∧ l.phase.isDisc = true)
      ∨ (Vr.mw = false ∧ ∃ t v, m = .writeRequest t v 0) := by
    intro d m hm
    rcases hcase with ⟨hmw, rfl, rfl⟩ | ⟨hmw, rfl, rfl⟩
    · rw [mem_bcast_iff] at hm; exact Or.inl ⟨hmw, hm.2, rfl⟩
    · rw [mem_bcast_iff] at hm; exact Or.inr ⟨hmw, _, _, hm.2⟩
  have hopmw : Vr.mw = true → l.op = (C.wl w).op + 1 ∧ l.ack = [] := by
    intro hmw
    rcases hcase with ⟨-, rfl, rfl⟩ | ⟨h', -⟩
    · exact ⟨rfl, rfl⟩
    · simp [hmw] at h'
  refine {
    net_sent := ?net_sent, tag_le := ?tag_le, req_le := ?req_le, rel_le := ?rel_le,
    rel_dst := ?rel_dst, rack_le := ?rack_le, ops_le := ?ops_le, rack_sent := ?rack_sent,
    rrel_sent := ?rrel_sent, rrel_nodup := ?rrel_nodup, relays_card := ?relays_card,
    relay_tok := ?relay_tok, rack_tok := ?rack_tok, wack_sent := ?wack_sent,
    wack_nodup := ?wack_nodup, disc_le := ?disc_le, dack_le := ?dack_le, wreq_le := ?wreq_le,
    wack_le := ?wack_le, wops := ?wops, wtok_le := ?wtok_le, disc_mw := ?disc_mw }
  case net_sent =>
    intro x hx; rw [hnet, Multiset.mem_add] at hx; rw [hsent, Multiset.mem_add]
    exact hx.imp_left (I.net_sent x)
  case tag_le =>
    intro s d m t v hm; rw [hs]; exact I.tag_le s d m t v (hsv _ _ _ hm)
  case req_le => intro r s k hm; rw [hr]; exact I.req_le r s k (hrd _ _ _ hm)
  case rel_le => intro s d t v r k hm; rw [hr]; exact I.rel_le s d t v r k (hsv _ _ _ hm)
  case rel_dst => intro s r' t v r k hm; exact I.rel_dst s r' t v r k (hsv _ _ _ hm)
  case rack_le => intro s r t v k hm; rw [hr]; exact I.rack_le s r t v k (hsv _ _ _ hm)
  case ops_le => intro s r; rw [hr, hs]; exact I.ops_le s r
  case rack_sent =>
    intro r e he; rw [hr] at he ⊢; rw [hsent]; exact Multiset.mem_add.2 (Or.inl (I.rack_sent r e he))
  case rrel_sent =>
    intro r e he; rw [hr] at he ⊢; rw [hsent]
    obtain ⟨r', h⟩ := I.rrel_sent r e he; exact ⟨r', Multiset.mem_add.2 (Or.inl h)⟩
  case rrel_nodup => intro r; rw [hr]; exact I.rrel_nodup r
  case relays_card => intro s r; rw [hs]; exact I.relays_card s r
  case relay_tok =>
    intro si sx r k; rw [hs, hnet, Multiset.countP_add, countP_outMsgs_zero (by simp), add_zero]
    exact I.relay_tok si sx r k
  case rack_tok =>
    intro sx r; rw [hs, hr, hnet, Multiset.countP_add, countP_outMsgs_zero (by simp), add_zero]
    exact I.rack_tok sx r
  case wack_sent =>
    intro w' e he
    by_cases hw : w' = w
    · subst hw; rw [hself] at he
      rcases hcase with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp at he
    · rw [hother w' hw] at he
      exact (I.wack_sent w' e he).mono (Multiset.le_add_right _ _) (hother w' hw)
  case wack_nodup =>
    intro w'
    by_cases hw : w' = w
    · subst hw; rw [hself]; rcases hcase with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp
    · rw [hother w' hw]; exact I.wack_nodup w'
  case disc_le =>
    intro hmw w' s k hm
    rw [hsent, Multiset.mem_add, mem_outMsgs_iff] at hm
    by_cases hw : w' = w
    · subst hw; rw [hself]
      obtain ⟨hop, -⟩ := hopmw hmw
      rcases hm with hm | ⟨-, hm⟩
      · have := I.disc_le hmw w' s k hm; omega
      · rcases hout _ _ hm with ⟨-, h1, h2⟩ | ⟨h1, -⟩
        · cases h1; exact ⟨le_rfl, fun _ => h2⟩
        · simp [hmw] at h1
    · rw [hother w' hw]
      rcases hm with hm | ⟨h1, -⟩
      · exact I.disc_le hmw w' s k hm
      · cases h1; exact absurd rfl hw
  case dack_le =>
    intro hmw w' s t v k hm
    have hm' := hsv _ _ _ hm
    have := I.dack_le hmw w' s t v k hm'
    by_cases hw : w' = w
    · subst hw; rw [hself]; obtain ⟨hop, -⟩ := hopmw hmw; omega
    · rw [hother w' hw]; exact this
  case wreq_le =>
    intro hmw w' s t v k hm
    rw [hsent, Multiset.mem_add, mem_outMsgs_iff] at hm
    rcases hm with hm | ⟨h1, hm⟩
    · have := I.wreq_le hmw w' s t v k hm
      by_cases hw : w' = w
      · subst hw; rw [hself]; obtain ⟨hop, -⟩ := hopmw hmw; omega
      · rw [hother w' hw]; exact this
    · cases h1
      rcases hout _ _ hm with ⟨-, h1, -⟩ | ⟨h1, -⟩
      · cases h1
      · simp [hmw] at h1
  case wack_le =>
    intro hmw w' s t v k hm
    have := I.wack_le hmw w' s t v k (hsv _ _ _ hm)
    by_cases hw : w' = w
    · subst hw; rw [hself]; obtain ⟨hop, -⟩ := hopmw hmw; omega
    · rw [hother w' hw]; exact this
  case wops =>
    intro hmw s w' hw'
    rw [hs] at hw' ⊢
    obtain ⟨t, v, h1, h2⟩ := I.wops hmw s w' hw'
    exact ⟨t, v, by rw [hsent]; exact Multiset.mem_add.2 (Or.inl h1), h2⟩
  case wtok_le =>
    intro hmw w' s
    rw [hnet, Multiset.countP_add]
    by_cases hw : w' = w
    · subst hw
      rw [hself]
      obtain ⟨hop, hack⟩ := hopmw hmw
      rw [hack, hop]
      rcases hcase with ⟨-, -, rfl⟩ | ⟨h', -⟩
      · have h0 : C.net.countP (fun x => wtok w' s ((C.wl w').op + 1) x) = 0 := by
          refine countP_eq_zero_of fun x hx => ?_
          by_contra hc
          have hxs := I.net_sent x hx
          rcases wtok_iff.1 (Bool.not_eq_false _ ▸ hc) with rfl | ⟨t, v, rfl⟩ | ⟨t, v, rfl⟩ |
            ⟨t, v, rfl⟩
          · have := I.disc_le hmw _ _ _ hxs; omega
          · have := I.wreq_le hmw _ _ _ _ _ hxs; omega
          · have := I.dack_le hmw _ _ _ _ _ hxs; omega
          · have := I.wack_le hmw _ _ _ _ _ hxs; omega
        rw [h0, countP_outMsgs_bcast, Finset.card_eq_one.2 ⟨s, by ext s'; simp [wtok, eq_comm]⟩]
        simp
      · simp [hmw] at h'
    · rw [hother w' hw, countP_outMsgs_zero (fun b c => wtok_wr_ne b c (Ne.symm hw)), add_zero]
      exact I.wtok_le hmw w' s
  case disc_mw =>
    intro w' v hph
    by_cases hw : w' = w
    · subst hw; rw [hself] at hph
      rcases hcase with ⟨hmw, rfl, -⟩ | ⟨-, rfl, -⟩
      · exact hmw
      · cases hph
    · rw [hother w' hw] at hph; exact I.disc_mw w' v hph

/-! ## Receptions by writers -/

/-- The acknowledgment list after recording a received message. -/
lemma CInv.wRecord_ack {C : Cfg W R S T V} (I : CInv Vr C) {w : W} {s : S} {m : Msg R T V}
    (hx : (Node.sv s, Node.wr w, m) ∈ C.net) :
    (∀ e ∈ (wRecord Vr s m (C.wl w)).ack, WAckSent Vr C w e) ∧
    (wRecord Vr s m (C.wl w)).ack.Nodup ∧
    (Vr.mw = true → ∀ s', (C.net.erase (Node.sv s, Node.wr w, m)).countP
        (fun x => wtok w s' (C.wl w).op x) +
      (wRecord Vr s m (C.wl w)).ack.countP (fun e => decide (e.1 = s')) ≤ 1) := by
  have hxs := I.net_sent _ hx
  rcases wRecord_cases Vr s m (C.wl w) with h | ⟨t, v, hacc, h⟩ <;> rw [h]
  · refine ⟨I.wack_sent w, I.wack_nodup w, fun hmw s' => ?_⟩
    exact le_trans (Nat.add_le_add_right (Multiset.countP_le_of_le _ (Multiset.erase_le _ _)) _)
      (I.wtok_le hmw w s')
  · refine ⟨fun e he => ?_, (I.wack_nodup w).insert, fun hmw s' => ?_⟩
    · rcases List.mem_insert_iff.1 he with rfl | he
      · unfold WAckSent
        rcases hacc with ⟨k, rfl, hk⟩ | ⟨k, rfl, hmw, rfl⟩
        · split_ifs at hk ⊢ with hmw
          · subst hk; exact Or.inl hxs
          · exact ⟨⟨k, hxs⟩, hk⟩
        · rw [ite_eq_left hmw]; exact Or.inr hxs
      · exact I.wack_sent w e he
    · have hcnt := countP_erase_add (fun x => wtok w s' (C.wl w).op x = true) (o := 0) hx
      simp only [add_zero, Multiset.countP_zero] at hcnt
      have := I.wtok_le hmw w s'
      have hxt : wtok w s (C.wl w).op (Node.sv s, Node.wr w, m) = true := by
        rcases hacc with ⟨k, rfl, hk⟩ | ⟨k, rfl, -, rfl⟩
        · rw [ite_eq_left hmw] at hk; subst hk; simp [wtok]
        · simp [wtok]
      by_cases hss : s = s'
      · subst hss
        have h2 := countP_insert_le (fun e => decide (e.1 = s)) (C.wl w).ack (s, t, v)
        simp only [hxt, ite_true, decide_true] at hcnt h2
        dsimp only
        omega
      · have hP : wtok w s' (C.wl w).op (Node.sv s, Node.wr w, m) = false := by
          rcases hacc with ⟨k, rfl, hk⟩ | ⟨k, rfl, -, rfl⟩ <;> simp [wtok, hss]
        simp only [hP, Bool.false_eq_true, ite_false, add_zero] at hcnt
        dsimp only
        rw [countP_insert_of_not _ (by simp [hss])]
        omega

lemma CInv.wRecv {C : Cfg W R S T V} (I : CInv Vr C) {w : W} {s : S} {m : Msg R T V}
    (hx : (Node.sv s, Node.wr w, m) ∈ C.net) :
    CInv Vr (C.setW w (wWait (R := R) next w (wRecord Vr s m (C.wl w))).1
      (wWait (R := R) next w (wRecord Vr s m (C.wl w))).2.1
      (C.net.erase (Node.sv s, Node.wr w, m))) := by
  obtain ⟨hA, hN, hT⟩ := I.wRecord_ack hx
  set l1 := wRecord Vr s m (C.wl w) with hl1
  set l' := (wWait (R := R) next w l1).1 with hl'
  set out := (wWait (R := R) next w l1).2.1 with hout
  set C' := C.setW w l' out (C.net.erase (Node.sv s, Node.wr w, m)) with hC'
  have hsent : C'.sent = C.sent + outMsgs (.wr w) out := rfl
  have hnet : C'.net = C.net.erase (Node.sv s, Node.wr w, m) + outMsgs (.wr w) out := rfl
  have hr : ∀ r, C'.rl r = C.rl r := by simp [hC']
  have hs : ∀ s, C'.sl s = C.sl s := by simp [hC']
  have hother : ∀ w', w' ≠ w → C'.wl w' = C.wl w' := by intro w' h; simp [hC', h]
  have hself : C'.wl w = l' := by simp [hC']
  have hsv : ∀ s d m, (Node.sv s, d, m) ∈ C'.sent → (Node.sv s, d, m) ∈ C.sent := by
    intro s d m hm; simpa [hsent] using hm
  have hrd : ∀ r d m, (Node.rd r, d, m) ∈ C'.sent → (Node.rd r, d, m) ∈ C.sent := by
    intro r d m hm; simpa [hsent] using hm
  have herase : ∀ P : Node W R S × Node W R S × Msg R T V → Bool,
      (C.net.erase (Node.sv s, Node.wr w, m)).countP (fun x => P x) ≤ C.net.countP (fun x => P x) :=
    fun P => Multiset.countP_le_of_le _ (Multiset.erase_le _ _)
  -- the three outcomes of the wait
  have hcases : (l' = l1 ∧ out = 0) ∨
      (∃ val, l1.phase = .disc val ∧ l'.op = l1.op + 1 ∧ l'.ack = [] ∧ l'.phase = .upd ∧
        out = bcast (.writeRequest l'.tag l'.val l'.op)) ∨
      (l1.phase = .upd ∧ l' = { l1 with phase := .idle } ∧ out = 0) := by
    rcases wWait_cases (R := R) (next := next) w l1 with h | ⟨val, -, hph, h⟩ | ⟨-, hph, h⟩
    · rw [hl', hout, h]; exact Or.inl ⟨rfl, rfl⟩
    · rw [hl', hout, h]; exact Or.inr (Or.inl ⟨val, hph, rfl, rfl, rfl, rfl⟩)
    · rw [hl', hout, h]; exact Or.inr (Or.inr ⟨hph, rfl, rfl⟩)
  refine {
    net_sent := ?net_sent, tag_le := ?tag_le, req_le := ?req_le, rel_le := ?rel_le,
    rel_dst := ?rel_dst, rack_le := ?rack_le, ops_le := ?ops_le, rack_sent := ?rack_sent,
    rrel_sent := ?rrel_sent, rrel_nodup := ?rrel_nodup, relays_card := ?relays_card,
    relay_tok := ?relay_tok, rack_tok := ?rack_tok, wack_sent := ?wack_sent,
    wack_nodup := ?wack_nodup, disc_le := ?disc_le, dack_le := ?dack_le, wreq_le := ?wreq_le,
    wack_le := ?wack_le, wops := ?wops, wtok_le := ?wtok_le, disc_mw := ?disc_mw }
  case net_sent =>
    intro x hx'; rw [hnet, Multiset.mem_add] at hx'; rw [hsent, Multiset.mem_add]
    exact hx'.imp_left fun h => I.net_sent x (Multiset.mem_of_mem_erase h)
  case tag_le =>
    intro s d m t v hm; rw [hs]; exact I.tag_le s d m t v (hsv _ _ _ hm)
  case req_le => intro r s k hm; rw [hr]; exact I.req_le r s k (hrd _ _ _ hm)
  case rel_le => intro s d t v r k hm; rw [hr]; exact I.rel_le s d t v r k (hsv _ _ _ hm)
  case rel_dst => intro s r' t v r k hm; exact I.rel_dst s r' t v r k (hsv _ _ _ hm)
  case rack_le => intro s r t v k hm; rw [hr]; exact I.rack_le s r t v k (hsv _ _ _ hm)
  case ops_le => intro s r; rw [hr, hs]; exact I.ops_le s r
  case rack_sent =>
    intro r e he; rw [hr] at he ⊢; rw [hsent]; exact Multiset.mem_add.2 (Or.inl (I.rack_sent r e he))
  case rrel_sent =>
    intro r e he; rw [hr] at he ⊢; rw [hsent]
    obtain ⟨r', h⟩ := I.rrel_sent r e he; exact ⟨r', Multiset.mem_add.2 (Or.inl h)⟩
  case rrel_nodup => intro r; rw [hr]; exact I.rrel_nodup r
  case relays_card => intro s r; rw [hs]; exact I.relays_card s r
  case relay_tok =>
    intro si sx r k; rw [hs, hnet, Multiset.countP_add, countP_outMsgs_zero (by simp), add_zero]
    exact le_trans (Nat.add_le_add_right (herase _) _) (I.relay_tok si sx r k)
  case rack_tok =>
    intro sx r; rw [hs, hr, hnet, Multiset.countP_add, countP_outMsgs_zero (by simp), add_zero]
    exact le_trans (Nat.add_le_add_right (herase _) _) (I.rack_tok sx r)
  case wack_sent =>
    intro w' e he
    by_cases hw : w' = w
    · subst hw; rw [hself] at he
      rcases hcases with ⟨hl, -⟩ | ⟨val, -, -, hack, -, -⟩ | ⟨-, hl, -⟩
      · rw [hl] at he
        refine (hA e he).mono' (Multiset.le_add_right _ _) ?_ ?_ <;>
          simp [hself, hl, hl1]
      · rw [hack] at he; simp at he
      · rw [hl] at he
        refine (hA e he).mono' (Multiset.le_add_right _ _) ?_ ?_ <;>
          simp [hself, hl, hl1]
    · rw [hother w' hw] at he
      exact (I.wack_sent w' e he).mono (Multiset.le_add_right _ _) (hother w' hw)
  case wack_nodup =>
    intro w'
    by_cases hw : w' = w
    · subst hw; rw [hself]
      rcases hcases with ⟨hl, -⟩ | ⟨val, -, -, hack, -, -⟩ | ⟨-, hl, -⟩
      · rw [hl]; exact hN
      · rw [hack]; exact List.nodup_nil
      · rw [hl]; exact hN
    · rw [hother w' hw]; exact I.wack_nodup w'
  case disc_le =>
    intro hmw w' s' k hm
    by_cases hw : w' = w
    · subst hw
      have hm' : (Node.wr w', Node.sv s', Msg.discover k) ∈ C.sent := by
        rw [hsent, Multiset.mem_add, mem_outMsgs_iff] at hm
        rcases hm with hm | ⟨-, hm⟩
        · exact hm
        · rcases hcases with ⟨-, ho⟩ | ⟨val, -, -, -, -, ho⟩ | ⟨-, -, ho⟩ <;> rw [ho] at hm
          · simp at hm
          · rw [mem_bcast_iff] at hm; cases hm.2
          · simp at hm
      have := I.disc_le hmw w' s' k hm'
      rw [hself]
      rcases hcases with ⟨hl, -⟩ | ⟨val, -, hop, -, -, -⟩ | ⟨hph, hl, -⟩
      · rw [hl]; simpa [hl1] using this
      · rw [hop]; simp only [hl1, wRecord_op] at hop ⊢; omega
      · rw [hl]; simp only [hl1, wRecord_op, wRecord_phase] at hph ⊢
        refine ⟨this.1, fun hk => ?_⟩
        have := this.2 hk; rw [hph] at this; cases this
    · rw [hother w' hw]
      exact I.disc_le hmw w' s' k (by
        rw [hsent, Multiset.mem_add, mem_outMsgs_iff] at hm
        rcases hm with hm | ⟨h1, -⟩
        · exact hm
        · cases h1; exact absurd rfl hw)
  case dack_le =>
    intro hmw w' s' t v k hm
    have := I.dack_le hmw w' s' t v k (hsv _ _ _ hm)
    by_cases hw : w' = w
    · subst hw
      rw [hself]
      rcases hcases with ⟨hl, -⟩ | ⟨val, -, hop, -, -, -⟩ | ⟨hph, hl, -⟩
      · rw [hl]; simpa [hl1] using this
      · rw [hop]; simp only [hl1, wRecord_op] at hop ⊢; omega
      · rw [hl]; simp only [hl1, wRecord_op, wRecord_phase] at hph ⊢
        refine ⟨this.1, fun hk => ?_⟩
        have := this.2 hk; rw [hph] at this; cases this
    · rw [hother w' hw]; exact this
  case wreq_le =>
    intro hmw w' s' t v k hm
    rw [hsent, Multiset.mem_add, mem_outMsgs_iff] at hm
    by_cases hw : w' = w
    · subst hw
      rw [hself]
      rcases hm with hm | ⟨-, hm⟩
      · have := I.wreq_le hmw w' s' t v k hm
        rcases hcases with ⟨hl, -⟩ | ⟨val, -, hop, -, -, -⟩ | ⟨hph, hl, -⟩
        · rw [hl]; simp only [hl1, wRecord_op, wRecord_tag, wRecord_phase]; exact this
        · rw [hop]; simp only [hl1, wRecord_op] at hop ⊢; omega
        · rw [hl]; simp only [hl1, wRecord_op, wRecord_tag,
            WPhase.isDisc_idle, true_and]
          exact ⟨this.1, this.2.1, fun hk => (this.2.2 hk).2⟩
      · rcases hcases with ⟨-, ho⟩ | ⟨val, -, hop, -, hph, ho⟩ | ⟨-, -, ho⟩ <;> rw [ho] at hm
        · simp at hm
        · rw [mem_bcast_iff] at hm
          obtain ⟨-, h⟩ := hm
          cases h
          refine ⟨by omega, le_rfl, fun _ => ⟨by rw [hph]; rfl, rfl⟩⟩
        · simp at hm
    · rw [hother w' hw]
      rcases hm with hm | ⟨h1, -⟩
      · exact I.wreq_le hmw w' s' t v k hm
      · cases h1; exact absurd rfl hw
  case wack_le =>
    intro hmw w' s' t v k hm
    have := I.wack_le hmw w' s' t v k (hsv _ _ _ hm)
    by_cases hw : w' = w
    · subst hw
      rw [hself]
      rcases hcases with ⟨hl, -⟩ | ⟨val, -, hop, -, -, -⟩ | ⟨hph, hl, -⟩
      · rw [hl]; simp only [hl1, wRecord_op, wRecord_tag, wRecord_phase]; exact this
      · rw [hop]; simp only [hl1, wRecord_op] at hop ⊢; omega
      · rw [hl]; simp only [hl1, wRecord_op, wRecord_tag,
            WPhase.isDisc_idle, true_and]
        exact ⟨this.1, fun hk => (this.2 hk).2⟩
    · rw [hother w' hw]; exact this
  case wops =>
    intro hmw s' w' hw'
    rw [hs] at hw' ⊢
    obtain ⟨t, v, h1, h2⟩ := I.wops hmw s' w' hw'
    exact ⟨t, v, by rw [hsent]; exact Multiset.mem_add.2 (Or.inl h1), h2⟩
  case wtok_le =>
    intro hmw w' s'
    rw [hnet, Multiset.countP_add]
    by_cases hw : w' = w
    · subst hw
      rw [hself]
      rcases hcases with ⟨hl, ho⟩ | ⟨val, -, hop, hack, -, ho⟩ | ⟨hph, hl, ho⟩ <;> rw [ho]
      · rw [hl]; simp only [outMsgs_zero', Multiset.countP_zero, add_zero]
        simpa [hl1] using hT hmw s'
      · rw [hack, hop]
        have h0 : (C.net.erase (Node.sv s, Node.wr w', m)).countP
            (fun x => wtok w' s' (l1.op + 1) x) = 0 := by
          refine countP_eq_zero_of fun x hx' => ?_
          by_contra hc
          have hxs := I.net_sent x (Multiset.mem_of_mem_erase hx')
          simp only [hl1, wRecord_op] at hc
          rcases wtok_iff.1 (Bool.not_eq_false _ ▸ hc) with rfl | ⟨t, v, rfl⟩ | ⟨t, v, rfl⟩ |
            ⟨t, v, rfl⟩
          · have := I.disc_le hmw _ _ _ hxs; omega
          · have := I.wreq_le hmw _ _ _ _ _ hxs; omega
          · have := I.dack_le hmw _ _ _ _ _ hxs; omega
          · have := I.wack_le hmw _ _ _ _ _ hxs; omega
        rw [h0, countP_outMsgs_bcast, Finset.card_eq_one.2 ⟨s', by
          ext s''; simp [wtok, eq_comm]⟩]
        simp
      · rw [hl]; simp only [outMsgs_zero', Multiset.countP_zero, add_zero]
        simpa [hl1] using hT hmw s'
    · rw [hother w' hw, countP_outMsgs_zero (fun b c => wtok_wr_ne b c (Ne.symm hw)), add_zero]
      exact le_trans (Nat.add_le_add_right (herase _) _) (I.wtok_le hmw w' s')
  case disc_mw =>
    intro w' v hph
    by_cases hw : w' = w
    · subst hw; rw [hself] at hph
      rcases hcases with ⟨hl, -⟩ | ⟨val, -, -, -, hph', -⟩ | ⟨-, hl, -⟩
      · rw [hl, hl1, wRecord_phase] at hph; exact I.disc_mw w' v hph
      · rw [hph'] at hph; cases hph
      · rw [hl] at hph; cases hph
    · rw [hother w' hw] at hph; exact I.disc_mw w' v hph

/-! ## Receptions by servers -/

/-- The state of the server is unchanged except for the tag, the value and `write_ops` (all
receptions except `readRelay`). -/
lemma sRecv_counters (Vr : Variant) (q : Node W R S) (m : Msg R T V) (l : SLoc W R S T V) :
    (∃ sj t v r k, q = .sv sj ∧ m = .readRelay t v r k) ∨
    ((sRecv Vr q m l).1.ops = l.ops ∧ (sRecv Vr q m l).1.relays = l.relays ∧
      (sRecv Vr q m l).1.got = l.got) := by
  rcases sRecv_cases (Vr := Vr) q m l with ⟨r, k, -, -, h⟩ | ⟨sj, t, v, r, k, hq, hm, -⟩ |
    ⟨w, t, v, op, -, -, h⟩ | ⟨w, op, -, -, h⟩ | h
  · rw [h]; exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl ⟨sj, t, v, r, k, hq, hm⟩
  · rw [h, sWrite_fst]; right; split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  · rw [h]; exact Or.inr ⟨rfl, rfl, rfl⟩
  · rw [h]; exact Or.inr ⟨rfl, rfl, rfl⟩

lemma sRecv_wops (Vr : Variant) (q : Node W R S) (m : Msg R T V) (l : SLoc W R S T V) :
    (∃ w t v op, q = .wr w ∧ m = .writeRequest t v op) ∨ (sRecv Vr q m l).1.wops = l.wops := by
  rcases sRecv_cases (Vr := Vr) q m l with ⟨r, k, -, -, h⟩ | ⟨sj, t, v, r, k, -, -, h⟩ |
    ⟨w, t, v, op, hq, hm, -⟩ | ⟨w, op, -, -, h⟩ | h
  · rw [h]; exact Or.inr rfl
  · rw [h, sRelay_wops]; exact Or.inr rfl
  · exact Or.inl ⟨w, t, v, op, hq, hm⟩
  · rw [h]; exact Or.inr rfl
  · rw [h]; exact Or.inr rfl

/-- The relay-token indicator after a `readRelay` from `sj`. -/
lemma sRelay_ind (Vr : Variant) (sj si : S) (t : T) (v : V) (r : R) (k0 k : ℕ)
    (l : SLoc W R S T V) :
    (if (sRelay Vr sj t v r k0 l).1.ops r = k ∧ si ∈ (sRelay Vr sj t v r k0 l).1.got r then 1
      else 0) ≤
    (if l.ops r = k ∧ si ∈ l.got r then 1 else 0) + (if sj = si ∧ k0 = k then 1 else 0) := by
  rw [sRelay_ops, sRelay_got, ite_eq_left rfl, ite_eq_left rfl]
  rcases lt_trichotomy (l.ops r) k0 with h1 | h1 | h1
  · rw [ite_eq_left h1, max_eq_right h1.le]
    split_ifs <;> simp_all
  · rw [ite_eq_right (show ¬ l.ops r < k0 by omega), ite_eq_left h1, max_eq_left h1.ge]
    split_ifs <;> simp_all
  · rw [ite_eq_right (show ¬ l.ops r < k0 by omega), ite_eq_right (show ¬ l.ops r = k0 by omega),
      max_eq_left h1.le]
    omega

/-- The `readAck` indicator after a `readRelay` (for the current read `k` of `r`). -/
lemma sRelay_rack (Vr : Variant) (sj : S) (t : T) (v : V) (r : R) (k0 k : ℕ)
    (l : SLoc W R S T V) (hk0 : k0 ≤ k) (hops : l.ops r ≤ k) :
    (if l.ops r = k ∧ maj S ≤ l.relays r then 1 else 0) +
      (if ((Vr.fixAck = false ∨ (sRelay Vr sj t v r k0 l).1.ops r = k0) ∧
        (sRelay Vr sj t v r k0 l).1.relays r = maj S) ∧ k0 = k then 1 else 0) ≤
    (if (sRelay Vr sj t v r k0 l).1.ops r = k ∧ maj S ≤ (sRelay Vr sj t v r k0 l).1.relays r
      then 1 else 0) := by
  rw [sRelay_ops, sRelay_relays, ite_eq_left rfl, ite_eq_left rfl]
  rcases lt_trichotomy (l.ops r) k0 with h1 | h1 | h1
  · rw [ite_eq_left h1, max_eq_right h1.le]
    split_ifs <;> omega
  · rw [ite_eq_right (show ¬ l.ops r < k0 by omega), ite_eq_left h1, max_eq_left h1.ge]
    split_ifs <;> omega
  · rw [ite_eq_right (show ¬ l.ops r < k0 by omega), ite_eq_right (show ¬ l.ops r = k0 by omega),
      max_eq_left h1.le]
    split_ifs <;> omega

lemma CInv.sRecv {C : Cfg W R S T V} (I : CInv Vr C) {s : S} {q : Node W R S} {m : Msg R T V}
    (hx : (q, Node.sv s, m) ∈ C.net) :
    CInv Vr (C.setS s (sRecv Vr q m (C.sl s)).1 (sRecv Vr q m (C.sl s)).2
      (C.net.erase (q, Node.sv s, m))) := by
  have hxs := I.net_sent _ hx
  set l' := (OhRAM.sRecv Vr q m (C.sl s)).1 with hl'
  set out := (OhRAM.sRecv Vr q m (C.sl s)).2 with hout
  set C' := C.setS s l' out (C.net.erase (q, Node.sv s, m)) with hC'
  have hsent : C'.sent = C.sent + outMsgs (.sv s) out := rfl
  have hnet : C'.net = C.net.erase (q, Node.sv s, m) + outMsgs (.sv s) out := rfl
  have hr : ∀ r, C'.rl r = C.rl r := by simp [hC']
  have hw : ∀ w, C'.wl w = C.wl w := by simp [hC']
  have hother : ∀ s', s' ≠ s → C'.sl s' = C.sl s' := by intro s' h; simp [hC', h]
  have hself : C'.sl s = l' := by simp [hC']
  have hmono : (C.sl s).tag ≤ l'.tag := sRecv_tag_mono q m (C.sl s)
  have htag : ∀ s', (C.sl s').tag ≤ (C'.sl s').tag := by
    intro s'; by_cases h : s' = s
    · subst h; rw [hself]; exact hmono
    · rw [hother s' h]
  have hcnt : ∀ P : Node W R S × Node W R S × Msg R T V → Bool,
      C'.net.countP (fun x => P x) + (if P (q, Node.sv s, m) then 1 else 0) =
        C.net.countP (fun x => P x) + (outMsgs (Node.sv s) out).countP (fun x => P x) := by
    intro P; rw [hnet]; exact countP_erase_add (fun x => P x = true) hx
  -- new messages are sent by `s`, are not requests, and carry the new tag and value of `s`
  have hnew : ∀ a b c, (a, b, c) ∈ outMsgs (Node.sv s) out → a = .sv s ∧ (b, c) ∈ out :=
    fun a b c h => mem_outMsgs_iff.1 h
  refine {
    net_sent := ?net_sent, tag_le := ?tag_le, req_le := ?req_le, rel_le := ?rel_le,
    rel_dst := ?rel_dst, rack_le := ?rack_le, ops_le := ?ops_le, rack_sent := ?rack_sent,
    rrel_sent := ?rrel_sent, rrel_nodup := ?rrel_nodup, relays_card := ?relays_card,
    relay_tok := ?relay_tok, rack_tok := ?rack_tok, wack_sent := ?wack_sent,
    wack_nodup := ?wack_nodup, disc_le := ?disc_le, dack_le := ?dack_le, wreq_le := ?wreq_le,
    wack_le := ?wack_le, wops := ?wops, wtok_le := ?wtok_le, disc_mw := ?disc_mw }
  case net_sent =>
    intro x hx'; rw [hnet, Multiset.mem_add] at hx'; rw [hsent, Multiset.mem_add]
    exact hx'.imp_left fun h => I.net_sent x (Multiset.mem_of_mem_erase h)
  case tag_le =>
    intro s' d m' t v hm htv
    rw [hsent, Multiset.mem_add] at hm
    rcases hm with hm | hm
    · exact (I.tag_le s' d m' t v hm htv).trans (htag s')
    · obtain ⟨h1, h2⟩ := hnew _ _ _ hm
      cases h1
      have := sRecv_out_tv (Vr := Vr) q m (C.sl s) _ h2
      rw [htv] at this
      simp only [Option.some.injEq, Prod.mk.injEq] at this
      rw [hself, this.1]
  case req_le =>
    intro r s' k hm
    rw [hsent, Multiset.mem_add] at hm
    rw [hr]
    rcases hm with hm | hm
    · exact I.req_le r s' k hm
    · exact absurd (hnew _ _ _ hm).1 (by simp)
  case rel_le =>
    intro s' d t v r k hm
    rw [hsent, Multiset.mem_add] at hm
    rw [hr]
    rcases hm with hm | hm
    · exact I.rel_le s' d t v r k hm
    · obtain ⟨-, h2⟩ := hnew _ _ _ hm
      rcases sRecv_cases (Vr := Vr) q m (C.sl s) with ⟨r0, k0, rfl, rfl, h⟩ | ⟨sj, t0, v0, r0, k0, -, -, h⟩ |
        ⟨w0, t0, v0, op0, -, -, h⟩ | ⟨w0, op0, -, -, h⟩ | h <;> rw [hout, h] at h2
      · have := I.req_le _ _ _ hxs
        simp only [Multiset.mem_add, mem_bcast_iff] at h2
        rcases h2 with ⟨-, h2⟩ | h2
        · cases h2; exact this
        · split_ifs at h2
          · rw [Multiset.mem_singleton] at h2; cases h2; exact this
          · simp at h2
      · rw [sRelay_out] at h2; split_ifs at h2
        · rw [Multiset.mem_singleton] at h2; cases h2
        · simp at h2
      · rw [sWrite_snd, Multiset.mem_singleton] at h2; cases h2
      · rw [Multiset.mem_singleton] at h2; cases h2
      · simp at h2
  case rel_dst =>
    intro s' r' t v r k hm
    rw [hsent, Multiset.mem_add] at hm
    rcases hm with hm | hm
    · exact I.rel_dst s' r' t v r k hm
    · obtain ⟨-, h2⟩ := hnew _ _ _ hm
      rcases sRecv_cases (Vr := Vr) q m (C.sl s) with ⟨r0, k0, rfl, rfl, h⟩ | ⟨sj, t0, v0, r0, k0, -, -, h⟩ |
        ⟨w0, t0, v0, op0, -, -, h⟩ | ⟨w0, op0, -, -, h⟩ | h <;> rw [hout, h] at h2
      · simp only [Multiset.mem_add, mem_bcast_iff] at h2
        rcases h2 with ⟨⟨s'', h3⟩, -⟩ | h2
        · cases h3
        · split_ifs at h2
          · rw [Multiset.mem_singleton] at h2; cases h2; rfl
          · simp at h2
      · rw [sRelay_out] at h2; split_ifs at h2
        · rw [Multiset.mem_singleton] at h2; cases h2
        · simp at h2
      · rw [sWrite_snd, Multiset.mem_singleton] at h2; cases h2
      · rw [Multiset.mem_singleton] at h2; cases h2
      · simp at h2
  case rack_le =>
    intro s' r t v k hm
    rw [hsent, Multiset.mem_add] at hm
    rw [hr]
    rcases hm with hm | hm
    · exact I.rack_le s' r t v k hm
    · obtain ⟨-, h2⟩ := hnew _ _ _ hm
      rcases sRecv_cases (Vr := Vr) q m (C.sl s) with ⟨r0, k0, rfl, rfl, h⟩ |
        ⟨sj, t0, v0, r0, k0, rfl, rfl, h⟩ |
        ⟨w0, t0, v0, op0, -, -, h⟩ | ⟨w0, op0, -, -, h⟩ | h <;> rw [hout, h] at h2
      · simp only [Multiset.mem_add, mem_bcast_iff] at h2
        rcases h2 with ⟨-, h2⟩ | h2
        · cases h2
        · split_ifs at h2
          · rw [Multiset.mem_singleton] at h2; cases h2
          · simp at h2
      · rw [sRelay_out] at h2; split_ifs at h2
        · rw [Multiset.mem_singleton] at h2; cases h2
          exact I.rel_le _ _ _ _ _ _ hxs
        · simp at h2
      · rw [sWrite_snd, Multiset.mem_singleton] at h2; cases h2
      · rw [Multiset.mem_singleton] at h2; cases h2
      · simp at h2
  case ops_le =>
    intro s' r
    rw [hr]
    by_cases hs : s' = s
    · rw [hs, hself]
      rcases sRecv_counters Vr q m (C.sl s) with ⟨sj, t0, v0, r0, k0, rfl, rfl⟩ | ⟨h1, -, -⟩
      · rw [hl', show OhRAM.sRecv Vr (Node.sv sj) (Msg.readRelay t0 v0 r0 k0) (C.sl s) =
          sRelay Vr sj t0 v0 r0 k0 (C.sl s) from rfl, sRelay_ops]
        split_ifs with hr0
        · subst hr0
          exact max_le (I.ops_le _ _) (I.rel_le _ _ _ _ _ _ hxs)
        · exact I.ops_le _ _
      · rw [h1]; exact I.ops_le _ _
    · rw [hother s' hs]; exact I.ops_le s' r
  case rack_sent =>
    intro r e he; rw [hr] at he ⊢; rw [hsent]; exact Multiset.mem_add.2 (Or.inl (I.rack_sent r e he))
  case rrel_sent =>
    intro r e he; rw [hr] at he ⊢; rw [hsent]
    obtain ⟨r', h⟩ := I.rrel_sent r e he; exact ⟨r', Multiset.mem_add.2 (Or.inl h)⟩
  case rrel_nodup => intro r; rw [hr]; exact I.rrel_nodup r
  case relays_card =>
    intro s' r
    by_cases hs : s' = s
    · rw [hs, hself]
      rcases sRecv_counters Vr q m (C.sl s) with ⟨sj, t0, v0, r0, k0, rfl, rfl⟩ | ⟨-, h2, h3⟩
      · rw [hl', show OhRAM.sRecv Vr (Node.sv sj) (Msg.readRelay t0 v0 r0 k0) (C.sl s) =
          sRelay Vr sj t0 v0 r0 k0 (C.sl s) from rfl, sRelay_relays, sRelay_got]
        split_ifs with hr0 h1 h2
        · rfl
        · subst hr0
          have htok := I.relay_tok sj s r k0
          have hpos : 0 < C.net.countP (fun x => rtok sj s r k0 x) :=
            Multiset.countP_pos_of_mem hx (by simp [rtok])
          have hnot : sj ∉ (C.sl s).got r := by
            intro hin; rw [ite_eq_left ⟨h2, hin⟩] at htok; omega
          rw [Finset.card_insert_of_notMem hnot, I.relays_card]
        · exact I.relays_card _ _
        · exact I.relays_card _ _
      · rw [h2, h3]; exact I.relays_card _ _
    · rw [hother s' hs]; exact I.relays_card s' r
  case relay_tok =>
    intro si sx r k
    have h1 := hcnt (rtok si sx r k)
    have h0 := I.relay_tok si sx r k
    -- `count(out) + new indicator ≤ old indicator + [x is a token]`
    suffices hkey : (outMsgs (Node.sv s) out).countP (fun x => rtok si sx r k x) +
        (if (C'.sl sx).ops r = k ∧ si ∈ (C'.sl sx).got r then 1 else 0) ≤
        (if (C.sl sx).ops r = k ∧ si ∈ (C.sl sx).got r then 1 else 0) +
        (if rtok si sx r k (q, Node.sv s, m) then 1 else 0) by omega
    rcases sRecv_cases (Vr := Vr) q m (C.sl s) with ⟨r0, k0, rfl, rfl, h⟩ |
      ⟨sj, t0, v0, r0, k0, rfl, rfl, h⟩ |
      ⟨w0, t0, v0, op0, rfl, rfl, h⟩ | ⟨w0, op0, rfl, rfl, h⟩ | h
    · -- readRequest: one relay to each server, the state is unchanged
      have hsx : C'.sl sx = C.sl sx := by
        by_cases hs : sx = s
        · subst hs; rw [hself, hl', h]
        · exact hother sx hs
      rw [hsx, hout, h, outMsgs_add, Multiset.countP_add, countP_outMsgs_bcast]
      have hz : (outMsgs (Node.sv s : Node W R S) (if Vr.fast = true then
          {(Node.rd r0, Msg.readRelay (C.sl s).tag (C.sl s).val r0 k0)} else 0)).countP
          (fun x => rtok si sx r k x) = 0 := by
        split_ifs <;> simp
      rw [hz, add_zero]
      by_cases hc : si = s ∧ r0 = r ∧ k0 = k
      · obtain ⟨rfl, rfl, rfl⟩ := hc
        rw [Finset.card_eq_one.2 ⟨sx, by ext s''; simp [rtok, eq_comm]⟩]
        simp only [rtok, and_self, decide_true, ite_true]; omega
      · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun s'' _ => by
          simp only [rtok, decide_eq_true_eq, not_and]
          rintro rfl - hr hk; exact hc ⟨rfl, hr, hk⟩)]
        omega
    · -- readRelay from `sj`
      have hz : (outMsgs (Node.sv s) out).countP (fun x => rtok si sx r k x) = 0 := by
        rw [hout, h, sRelay_out]; split_ifs <;> simp [countP_singleton']
      rw [hz, zero_add]
      by_cases hsx : sx = s
      · subst hsx
        rw [hself, hl', h, sRelay_ops, sRelay_got]
        by_cases hr0 : r = r0
        · subst hr0
          have hP : rtok (W := W) si sx r k (Node.sv sj, Node.sv sx, Msg.readRelay t0 v0 r k0) =
              decide (sj = si ∧ k0 = k) := by simp [rtok]
          rw [← sRelay_ops, ← sRelay_got, hP]
          have := sRelay_ind Vr sj si t0 v0 r k0 k (C.sl sx)
          simp only [decide_eq_true_eq]
          omega
        · simp only [hr0, ite_false]; omega
      · rw [hother sx hsx]; omega
    · -- writeRequest
      have hz : (outMsgs (Node.sv s) out).countP (fun x => rtok si sx r k x) = 0 := by
        rw [hout, h, sWrite_snd]; simp [countP_singleton']
      have hsx : (C'.sl sx).ops = (C.sl sx).ops ∧ (C'.sl sx).got = (C.sl sx).got := by
        by_cases hs : sx = s
        · subst hs; rw [hself, hl', h, sWrite_fst]; split_ifs <;> exact ⟨rfl, rfl⟩
        · rw [hother sx hs]; exact ⟨rfl, rfl⟩
      rw [hz, hsx.1, hsx.2]; omega
    · have hz : (outMsgs (Node.sv s) out).countP (fun x => rtok si sx r k x) = 0 := by
        rw [hout, h]; simp
      have hsx : C'.sl sx = C.sl sx := by
        by_cases hs : sx = s
        · subst hs; rw [hself, hl', h]
        · exact hother sx hs
      rw [hz, hsx]; omega
    · have hz : (outMsgs (Node.sv s) out).countP (fun x => rtok si sx r k x) = 0 := by
        rw [hout, h]; simp
      have hsx : C'.sl sx = C.sl sx := by
        by_cases hs : sx = s
        · subst hs; rw [hself, hl', h]
        · exact hother sx hs
      rw [hz, hsx]; omega
  case rack_tok =>
    intro sx r
    rw [hr]
    have h1 := hcnt (atok sx r (C.rl r).op)
    have h0 := I.rack_tok sx r
    have hxa : atok (W := W) sx r (C.rl r).op (q, Node.sv s, m) = false := by cases q <;> simp
    rw [hxa] at h1
    simp only [Bool.false_eq_true, ite_false, add_zero] at h1
    suffices hkey : (outMsgs (Node.sv s) out).countP (fun x => atok sx r (C.rl r).op x) +
        (if (C.sl sx).ops r = (C.rl r).op ∧ maj S ≤ (C.sl sx).relays r then 1 else 0) ≤
        (if (C'.sl sx).ops r = (C.rl r).op ∧ maj S ≤ (C'.sl sx).relays r then 1 else 0) by
      omega
    rcases sRecv_cases (Vr := Vr) q m (C.sl s) with ⟨r0, k0, rfl, rfl, h⟩ |
      ⟨sj, t0, v0, r0, k0, rfl, rfl, h⟩ |
      ⟨w0, t0, v0, op0, rfl, rfl, h⟩ | ⟨w0, op0, rfl, rfl, h⟩ | h
    · have hsx : C'.sl sx = C.sl sx := by
        by_cases hs : sx = s
        · subst hs; rw [hself, hl', h]
        · exact hother sx hs
      have hz : (outMsgs (Node.sv s) out).countP (fun x => atok sx r (C.rl r).op x) = 0 := by
        rw [hout, h]; simp only [outMsgs_add, Multiset.countP_add]
        rw [countP_outMsgs_bcast]
        split_ifs <;> simp [atok]
      rw [hz, hsx]; omega
    · by_cases hsx : sx = s
      · subst hsx
        rw [hself, hl', h]
        by_cases hr0 : r = r0
        · subst hr0
          have hk0 := I.rel_le _ _ _ _ _ _ hxs
          have := sRelay_rack Vr sj t0 v0 r k0 (C.rl r).op (C.sl sx) hk0 (I.ops_le sx r)
          have hc : (outMsgs (Node.sv sx) out).countP (fun x => atok sx r (C.rl r).op x) =
              if ((Vr.fixAck = false ∨ (sRelay Vr sj t0 v0 r k0 (C.sl sx)).1.ops r = k0) ∧
                (sRelay Vr sj t0 v0 r k0 (C.sl sx)).1.relays r = maj S) ∧ k0 = (C.rl r).op
              then 1 else 0 := by
            rw [hout, h, sRelay_out]
            by_cases h2 : (Vr.fixAck = false ∨ (sRelay Vr sj t0 v0 r k0 (C.sl sx)).1.ops r = k0) ∧
                (sRelay Vr sj t0 v0 r k0 (C.sl sx)).1.relays r = maj S
            · rw [ite_eq_left h2]
              simp only [outMsgs_single, countP_singleton', h2, true_and]
              by_cases hk : k0 = (C.rl r).op <;> simp [atok, hk]
            · rw [ite_eq_right h2]; simp [h2]
          rw [hc]; omega
        · have hc : (outMsgs (Node.sv sx) out).countP (fun x => atok sx r (C.rl r).op x) = 0 := by
            rw [hout, h, sRelay_out]
            split_ifs <;> simp [atok, Ne.symm hr0]
          rw [hc, sRelay_ops, sRelay_relays, ite_eq_right hr0, ite_eq_right hr0]; omega
      · have hc : (outMsgs (Node.sv s) out).countP (fun x => atok sx r (C.rl r).op x) = 0 := by
          rw [hout, h, sRelay_out]
          split_ifs <;> simp [atok, Ne.symm hsx]
        rw [hc, hother sx hsx]; omega
    · have hz : (outMsgs (Node.sv s) out).countP (fun x => atok sx r (C.rl r).op x) = 0 := by
        rw [hout, h, sWrite_snd]; simp
      have hsx : (C'.sl sx).ops = (C.sl sx).ops ∧ (C'.sl sx).relays = (C.sl sx).relays := by
        by_cases hs : sx = s
        · subst hs; rw [hself, hl', h, sWrite_fst]; split_ifs <;> exact ⟨rfl, rfl⟩
        · rw [hother sx hs]; exact ⟨rfl, rfl⟩
      rw [hz, hsx.1, hsx.2]; omega
    · have hz : (outMsgs (Node.sv s) out).countP (fun x => atok sx r (C.rl r).op x) = 0 := by
        rw [hout, h]; simp
      have hsx : C'.sl sx = C.sl sx := by
        by_cases hs : sx = s
        · subst hs; rw [hself, hl', h]
        · exact hother sx hs
      rw [hz, hsx]; omega
    · have hz : (outMsgs (Node.sv s) out).countP (fun x => atok sx r (C.rl r).op x) = 0 := by
        rw [hout, h]; simp
      have hsx : C'.sl sx = C.sl sx := by
        by_cases hs : sx = s
        · subst hs; rw [hself, hl', h]
        · exact hother sx hs
      rw [hz, hsx]; omega
  case wack_sent =>
    intro w e he
    rw [hw] at he
    exact (I.wack_sent w e he).mono (Multiset.le_add_right _ _) (hw w)
  case wack_nodup => intro w; rw [hw]; exact I.wack_nodup w
  case disc_le =>
    intro hmw w s' k hm
    rw [hsent, Multiset.mem_add] at hm
    rw [hw]
    rcases hm with hm | hm
    · exact I.disc_le hmw w s' k hm
    · exact absurd (hnew _ _ _ hm).1 (by simp)
  case dack_le =>
    intro hmw w s' t v k hm
    rw [hsent, Multiset.mem_add] at hm
    rw [hw]
    rcases hm with hm | hm
    · exact I.dack_le hmw w s' t v k hm
    · obtain ⟨h1, h2⟩ := hnew _ _ _ hm
      cases h1
      rcases sRecv_cases (Vr := Vr) q m (C.sl s) with ⟨r0, k0, -, -, h⟩ |
        ⟨sj, t0, v0, r0, k0, -, -, h⟩ |
        ⟨w0, t0, v0, op0, -, -, h⟩ | ⟨w0, op0, rfl, rfl, h⟩ | h <;> rw [hout, h] at h2
      · simp only [Multiset.mem_add, mem_bcast_iff] at h2
        rcases h2 with ⟨⟨_, h3⟩, -⟩ | h2
        · cases h3
        · split_ifs at h2
          · rw [Multiset.mem_singleton] at h2; cases h2
          · simp at h2
      · rw [sRelay_out] at h2; split_ifs at h2
        · rw [Multiset.mem_singleton] at h2; cases h2
        · simp at h2
      · rw [sWrite_snd, Multiset.mem_singleton] at h2; cases h2
      · rw [Multiset.mem_singleton] at h2; cases h2
        exact I.disc_le hmw _ _ _ hxs
      · simp at h2
  case wreq_le =>
    intro hmw w s' t v k hm
    rw [hsent, Multiset.mem_add] at hm
    rw [hw]
    rcases hm with hm | hm
    · exact I.wreq_le hmw w s' t v k hm
    · exact absurd (hnew _ _ _ hm).1 (by simp)
  case wack_le =>
    intro hmw w s' t v k hm
    rw [hsent, Multiset.mem_add] at hm
    rw [hw]
    rcases hm with hm | hm
    · exact I.wack_le hmw w s' t v k hm
    · obtain ⟨h1, h2⟩ := hnew _ _ _ hm
      cases h1
      rcases sRecv_cases (Vr := Vr) q m (C.sl s) with ⟨r0, k0, -, -, h⟩ |
        ⟨sj, t0, v0, r0, k0, -, -, h⟩ |
        ⟨w0, t0, v0, op0, rfl, rfl, h⟩ | ⟨w0, op0, -, -, h⟩ | h <;> rw [hout, h] at h2
      · simp only [Multiset.mem_add, mem_bcast_iff] at h2
        rcases h2 with ⟨⟨_, h3⟩, -⟩ | h2
        · cases h3
        · split_ifs at h2
          · rw [Multiset.mem_singleton] at h2; cases h2
          · simp at h2
      · rw [sRelay_out] at h2; split_ifs at h2
        · rw [Multiset.mem_singleton] at h2; cases h2
        · simp at h2
      · rw [sWrite_snd, Multiset.mem_singleton] at h2
        simp only [Prod.mk.injEq, Node.wr.injEq, Msg.writeAck.injEq] at h2
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h2
        obtain ⟨hk1, hk2, hk3⟩ := I.wreq_le hmw _ _ _ _ _ hxs
        refine ⟨hk2, fun hk => ⟨(hk3 hk).1, ?_⟩⟩
        rw [(hk3 hk).2] at h ⊢
        rw [sWrite_fst, ite_eq_left hmw]
        split_ifs with hc
        · exact le_rfl
        · by_contra hlt
          push Not at hlt
          have hwops : k ≤ (C.sl s).wops w := by
            by_contra h'; exact hc ⟨hlt, by omega⟩
          obtain ⟨t', v', h5, h6⟩ := I.wops hmw s w (by omega)
          obtain ⟨-, h7, h8⟩ := I.wreq_le hmw _ _ _ _ _ h5
          have h9 : (C.sl s).wops w = (C.wl w).op := by omega
          rw [(h8 h9).2] at h6
          exact absurd h6 (not_le.2 hlt)
      · rw [Multiset.mem_singleton] at h2; cases h2
      · simp at h2
  case wops =>
    intro hmw s' w hw'
    by_cases hs : s' = s
    · rw [hs, hself] at hw' ⊢
      rcases sRecv_wops Vr q m (C.sl s) with ⟨w0, t0, v0, op0, rfl, rfl, -⟩ | h
      · rw [hl', show OhRAM.sRecv Vr (Node.wr w0) (Msg.writeRequest t0 v0 op0) (C.sl s) =
          sWrite Vr w0 t0 v0 op0 (C.sl s) from rfl, sWrite_fst, ite_eq_left hmw] at hw' ⊢
        split_ifs at hw' ⊢ with hc
        · by_cases hww : w = w0
          · subst hww
            simp only [Function.update_self] at hw' ⊢
            exact ⟨t0, v0, by rw [hsent]; exact Multiset.mem_add.2 (Or.inl hxs), le_rfl⟩
          · simp only [Function.update_of_ne hww] at hw' ⊢
            obtain ⟨t, v, h1, h2⟩ := I.wops hmw s w hw'
            exact ⟨t, v, by rw [hsent]; exact Multiset.mem_add.2 (Or.inl h1), h2.trans hc.1.le⟩
        · obtain ⟨t, v, h1, h2⟩ := I.wops hmw s w hw'
          exact ⟨t, v, by rw [hsent]; exact Multiset.mem_add.2 (Or.inl h1), h2⟩
      · rw [← hl'] at h
        rw [h] at hw' ⊢
        obtain ⟨t, v, h1, h2⟩ := I.wops hmw s w hw'
        exact ⟨t, v, by rw [hsent]; exact Multiset.mem_add.2 (Or.inl h1), h2.trans hmono⟩
    · rw [hother s' hs] at hw' ⊢
      obtain ⟨t, v, h1, h2⟩ := I.wops hmw s' w hw'
      exact ⟨t, v, by rw [hsent]; exact Multiset.mem_add.2 (Or.inl h1), h2⟩
  case wtok_le =>
    intro hmw w s'
    rw [hw]
    have h1 := hcnt (wtok w s' (C.wl w).op)
    have h0 := I.wtok_le hmw w s'
    suffices hkey : (outMsgs (Node.sv s) out).countP (fun x => wtok w s' (C.wl w).op x) ≤
        if wtok w s' (C.wl w).op (q, Node.sv s, m) then 1 else 0 by omega
    rcases sRecv_cases (Vr := Vr) q m (C.sl s) with ⟨r0, k0, rfl, rfl, h⟩ |
      ⟨sj, t0, v0, r0, k0, rfl, rfl, h⟩ |
      ⟨w0, t0, v0, op0, rfl, rfl, h⟩ | ⟨w0, op0, rfl, rfl, h⟩ | h
    · rw [hout, h]; simp only [outMsgs_add, Multiset.countP_add, countP_outMsgs_bcast]
      split_ifs <;> simp
    · rw [hout, h, sRelay_out]; split_ifs <;> simp
    · rw [hout, h, sWrite_snd]; simp [wtok]
    · rw [hout, h]; simp [wtok]
    · rw [hout, h]; simp
  case disc_mw => intro w v h; rw [hw] at h; exact I.disc_mw w v h

end Podc.OhRAM

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V] {Vr : Variant} {next : W → T → T} {v₀ : V}

/-- Every step preserves `CInv`. -/
lemma CInv.step {C C' : Cfg W R S T V} {st : Step (Node W R S) (register V v₀) (Msg R T V) Empty}
    {ℓ : Option (Label (Node W R S) (register V v₀))} (I : CInv Vr C)
    (h : (proto Vr next v₀).step C st = some (C', ℓ)) : CInv Vr C' := by
  rcases step_cases h with ⟨h1, h2, -, h4⟩ | ⟨w, v, l, out, hw, rfl, -⟩ |
    ⟨r, l, out, hr, rfl, -⟩ | ⟨w, s, m, hx, rfl, -⟩ | ⟨r, s, m, hx, rfl, -⟩ | ⟨s, q, m, hx, rfl, -⟩
  · exact I.of_silent h1 h2 h4
  · exact I.wInvoke hw
  · exact I.rInvoke hr
  · exact I.wRecv hx
  · exact I.rRecv hx
  · exact I.sRecv hx

/-- `CInv` holds in every reachable configuration. -/
lemma cinv_of_reach {C : Cfg W R S T V} {h : List (Label (Node W R S) (register V v₀))}
    (hr : (proto Vr next v₀).Reach C h) : CInv Vr C := by
  induction hr with
  | init => exact cinv_init
  | step _ hs ih => exact ih.step hs

end Podc.OhRAM
