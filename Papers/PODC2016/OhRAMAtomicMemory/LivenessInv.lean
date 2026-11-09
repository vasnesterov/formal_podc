import Papers.PODC2016.OhRAMAtomicMemory.LivenessSteps

/-!
# Invariants for the liveness proof

* `HInv`: a client has one more invocation than responses iff it is busy (a write in phase
  `disc`/`upd`, or a pending read).
* `RInv`: the read counters (`read_op` of the reader ≥ every `read_op` of a message, server
  `operations[r]` ≤ `read_op`), the ghost `got` (`|got[r]| ≤ relays[r]`), and "a server whose
  `relays[r]` reached `|S|/2 + 1` has sent `readAck` for `operations[r]`".
* `TInv` (single writer): all tags in the system are at most the writer's tag.
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM.Liveness

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]
variable {Vr : Variant} {next : W → T → T} {v₀ : V}
variable {C C' : Cfg W R S T V} {ℓ : Option (Label (Node W R S) (register V v₀))}
  {s : Step (Node W R S) (register V v₀) (Msg R T V) Empty}

/-! ## Busy clients and the history -/

/-- The process has a pending operation. -/
def Busy : Node W R S → Loc W R S T V → Prop
  | .wr _, L => L.w.phase ≠ .idle
  | .rd _, L => L.r.pending = true
  | .sv _, _ => False

lemma invoke_busy {p : Node W R S} {o : RWOp V} {L l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)}
    (h : (proto Vr next v₀).invoke p o L = some (l, out)) : ¬ Busy p L ∧ Busy p l := by
  cases p with
  | wr w =>
    obtain ⟨val, rfl, hw, -, -⟩ := invoke_wr h
    obtain ⟨hid, hc⟩ := wInvoke_spec hw
    simp only [Busy, hid, ne_eq, not_true_eq_false, not_false_eq_true, true_and]
    rcases hc with ⟨-, hl, -⟩ | ⟨-, hl, -⟩ <;> rw [hl] <;> simp
  | rd r =>
    obtain ⟨rfl, hr, -, -⟩ := invoke_rd h
    obtain ⟨hp, hl, -⟩ := rInvoke_spec hr
    simp [Busy, hp, hl]
  | sv _ => simp [invoke_sv] at h

lemma receive_busy {p src : Node W R S} {m : Msg R T V} {L l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)} {r : Option V}
    (h : (proto Vr next v₀).receive p src m L = some (l, out, r)) :
    (r.isSome → Busy p L ∧ ¬ Busy p l) ∧ (r = none → (Busy p l ↔ Busy p L)) := by
  cases p with
  | wr w =>
    obtain ⟨-, -, h | ⟨rfl, rfl, rfl⟩⟩ := receive_wr h
    · obtain ⟨s, rfl, hx⟩ := h
      obtain ⟨ack', hrec, -, -⟩ := wRecord_spec (Vr := Vr) s m L.w
      rw [hrec] at hx
      rcases wWait_spec (R := R) (next := next) w { L.w with ack := ack' } with
        ⟨-, hw⟩ | ⟨-, val, hph, hw⟩ | ⟨-, hph, hw⟩ <;> rw [hw] at hx <;>
        simp only [Prod.mk.injEq] at hx <;> obtain ⟨h1, -, rfl⟩ := hx
      · simp [Busy, h1]
      · simp only at hph
        simp [Busy, h1, hph]
      · simp only at hph
        simp [Busy, h1, hph]
    · simp
  | rd rr =>
    obtain ⟨-, -, -, h | ⟨rfl, rfl⟩⟩ := receive_rd h
    · obtain ⟨s, rfl, hx⟩ := h
      obtain ⟨ack', relay', hrec, -, -⟩ := rRecord_spec (Vr := Vr) s m L.r
      rw [hrec] at hx
      rcases rWait_spec (Vr := Vr) (v₀ := v₀) { L.r with ack := ack', relay := relay' } with
        ⟨-, hw⟩ | ⟨hp, h1, h2⟩
      · rw [hw] at hx
        simp only [Prod.mk.injEq] at hx
        obtain ⟨h1, rfl⟩ := hx
        simp only [Busy]
        rw [h1]
        simp
      · simp only [Prod.ext_iff] at hx
        obtain ⟨hx1, hx2⟩ := hx
        rw [h1] at hx1
        rw [← hx2] at h2
        simp only at hp
        simp only [Busy]
        rw [hx1]
        refine ⟨fun _ => ⟨hp, by simp⟩, fun hr => ?_⟩
        subst hr
        simp at h2
    · simp
  | sv _ =>
    obtain ⟨-, -, rfl, -⟩ := receive_sv h
    simp [Busy]

/-- A client has one more invocation than responses iff it is busy. -/
def HInv (C : Cfg W R S T V) (h : List (Label (Node W R S) (register V v₀))) : Prop :=
  ∀ p, ((opsOf h p).length = (respsOf h p).length + 1 ∧ Busy p (C.loc p)) ∨
    ((opsOf h p).length = (respsOf h p).length ∧ ¬ Busy p (C.loc p))

lemma hInv_of_reach {h : List (Label (Node W R S) (register V v₀))}
    (hr : (proto Vr next v₀).Reach C h) : HInv C h := by
  induction hr with
  | init =>
    intro p
    right
    cases p <;> simp [opsOf, respsOf, Busy, Protocol.initCfg, proto, initLoc]
  | step hr hs ih =>
    rename_i C h s C' ℓ
    rcases step_cases hs with ⟨hloc, -, -, rfl, -⟩ | ⟨p, o, l, out, rfl, -, rfl, hinv, rfl⟩ |
      ⟨src, dst, m, l, out, r, rfl, -, -, hrec, rfl, rfl⟩
    · intro q
      simpa [hloc] using ih q
    · intro q
      obtain ⟨hb1, hb2⟩ := invoke_busy hinv
      by_cases hq : q = p
      · subst hq
        rcases ih q with ⟨-, hb⟩ | ⟨he, -⟩
        · exact absurd hb hb1
        · left
          simp [opsOf, respsOf, Config.apply, List.filterMap_cons, hb2] at he ⊢
          simpa [opsOf, respsOf] using he
      · have := ih q
        simpa [opsOf, respsOf, Config.apply, List.filterMap_cons, Function.update_of_ne hq,
          Ne.symm hq] using this
    · intro q
      obtain ⟨hb1, hb2⟩ := receive_busy hrec
      by_cases hq : q = dst
      · subst hq
        cases r with
        | none =>
          have := ih q
          simpa [opsOf, respsOf, Config.apply, List.filterMap_cons, hb2 rfl] using this
        | some v =>
          obtain ⟨hb, hnb⟩ := hb1 rfl
          rcases ih q with ⟨he, -⟩ | ⟨-, hb'⟩
          · right
            simp [opsOf, respsOf, Config.apply, List.filterMap_cons, hnb] at he ⊢
            simpa [opsOf, respsOf] using he
          · exact absurd hb hb'
      · have := ih q
        cases r <;>
          simpa [opsOf, respsOf, Config.apply, List.filterMap_cons, Function.update_of_ne hq,
          Ne.symm hq] using this

/-! ## Read counters -/

/-- `read_op` of reader `r`. -/
def rop (C : Cfg W R S T V) (r : R) : ℕ := (C.loc (.rd r)).r.op

/-- The read counter carried by a message is at most the reader's `read_op` `f r`. -/
def MsgOK (f : R → ℕ) : Node W R S × Node W R S × Msg R T V → Prop
  | (src, dst, m) =>
    match m with
    | .readRequest k => ∀ r, src = .rd r → k ≤ f r
    | .readRelay _ _ r k => k ≤ f r
    | .readAck _ _ k => ∀ r, dst = .rd r → k ≤ f r
    | _ => True

lemma MsgOK.mono {f g : R → ℕ} (hfg : ∀ r, f r ≤ g r) {x : Node W R S × Node W R S × Msg R T V}
    (h : MsgOK f x) : MsgOK g x := by
  obtain ⟨src, dst, m⟩ := x
  cases m <;> simp only [MsgOK] at h ⊢
  · exact fun r hr => (h r hr).trans (hfg r)
  · exact h.trans (hfg _)
  · exact fun r hr => (h r hr).trans (hfg r)

/-- The invariant of read counters, relay counters and acknowledgments. -/
structure RInv (C : Cfg W R S T V) : Prop where
  msg : ∀ x ∈ C.sent, MsgOK (rop C) x
  net : ∀ x ∈ C.net, x ∈ C.sent
  ops : ∀ s r, (C.loc (.sv s)).s.ops r ≤ rop C r
  got : ∀ s r, ((C.loc (.sv s)).s.got r).card ≤ (C.loc (.sv s)).s.relays r
  quorum : ∀ s r, maj S ≤ (C.loc (.sv s)).s.relays r →
    ∃ t v, (Node.sv s, Node.rd r, Msg.readAck t v ((C.loc (.sv s)).s.ops r)) ∈ C.sent

variable (S) in
lemma one_le_maj : 1 ≤ maj S := by simp [maj]


lemma RInv.of_client (hI : RInv C) {p : Node W R S} {l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)} {net : Multiset (Node W R S × Node W R S × Msg R T V)}
    (hnet : net ≤ C.net) (hp : ∀ s, p ≠ .sv s) (hrop : ∀ r, rop C r ≤ rop (C.apply p l out net) r)
    (hnew : ∀ x ∈ outMsgs p out, MsgOK (rop (C.apply p l out net)) x) :
    RInv (C.apply p l out net) := by
  have hsv : ∀ s, (C.apply p l out net).loc (.sv s) = C.loc (.sv s) := fun s => by
    simp [Config.apply, Function.update_of_ne (hp s).symm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Config.apply, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · exact (hI.msg x hx).mono hrop
    · exact hnew x hx
  · intro x hx
    simp only [Config.apply, Multiset.mem_add] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (hI.net x (Multiset.mem_of_le hnet hx))
    · exact Or.inr hx
  · intro s r; rw [hsv]; exact (hI.ops s r).trans (hrop r)
  · intro s r; rw [hsv]; exact hI.got s r
  · intro s r; rw [hsv]
    intro h
    obtain ⟨t, v, h⟩ := hI.quorum s r h
    exact ⟨t, v, Multiset.mem_add.2 (Or.inl h)⟩

lemma rop_apply_sv {s0 : S} {l : Loc W R S T V} {out : Multiset (Node W R S × Msg R T V)}
    {net : Multiset (Node W R S × Node W R S × Msg R T V)} :
    rop (C.apply (.sv s0) l out net) = rop C := by
  funext r
  simp [rop, Config.apply]

lemma RInv.of_server (hI : RInv C) {s0 : S} {l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)} {net : Multiset (Node W R S × Node W R S × Msg R T V)}
    (hnet : net ≤ C.net) (hnew : ∀ x ∈ outMsgs (.sv s0) out, MsgOK (rop C) x)
    (hops : ∀ r, l.s.ops r ≤ rop C r) (hgot : ∀ r, (l.s.got r).card ≤ l.s.relays r)
    (hq : ∀ r, maj S ≤ l.s.relays r →
      ∃ t v, (Node.sv s0, Node.rd r, Msg.readAck t v (l.s.ops r)) ∈ C.sent + outMsgs (.sv s0) out) :
    RInv (C.apply (.sv s0) l out net) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [rop_apply_sv]
    intro x hx
    simp only [Config.apply, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · exact hI.msg x hx
    · exact hnew x hx
  · intro x hx
    simp only [Config.apply, Multiset.mem_add] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (hI.net x (Multiset.mem_of_le hnet hx))
    · exact Or.inr hx
  · intro s r
    rw [rop_apply_sv]
    by_cases hs : s = s0
    · subst hs; simpa [Config.apply] using hops r
    · simpa [Config.apply, hs] using hI.ops s r
  · intro s r
    by_cases hs : s = s0
    · subst hs; simpa [Config.apply] using hgot r
    · simpa [Config.apply, hs] using hI.got s r
  · intro s r
    by_cases hs : s = s0
    · subst hs; simpa [Config.apply] using hq r
    · simp only [Config.apply, ne_eq, Node.sv.injEq, hs, not_false_eq_true,
        Function.update_of_ne, Multiset.mem_add]
      intro h
      obtain ⟨t, v, h⟩ := hI.quorum s r h
      exact ⟨t, v, Or.inl h⟩

lemma rInv_init : RInv ((proto (R := R) (S := S) Vr next v₀).initCfg) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Protocol.initCfg, proto, initLoc, rop, maj]

lemma receive_rd_op {rr : R} {src : Node W R S} {m : Msg R T V} {L l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)} {r : Option V}
    (h : (proto Vr next v₀).receive (.rd rr) src m L = some (l, out, r)) : l.r.op = L.r.op := by
  obtain ⟨-, -, -, h | ⟨rfl, -⟩⟩ := receive_rd h
  · obtain ⟨s, rfl, hx⟩ := h
    obtain ⟨ack', relay', hrec, -, -⟩ := rRecord_spec (Vr := Vr) s m L.r
    rw [hrec] at hx
    rcases rWait_spec (Vr := Vr) (v₀ := v₀) { L.r with ack := ack', relay := relay' } with
      ⟨-, hw⟩ | ⟨-, h1, -⟩
    · rw [hw] at hx
      simp only [Prod.mk.injEq] at hx
      rw [hx.1]
    · simp only [Prod.ext_iff] at hx
      rw [hx.1, h1]
  · rfl

/-- Writers only send `discover` and `writeRequest` messages. -/
lemma wr_out {w : W} {src : Node W R S} {m : Msg R T V} {L l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)} {r : Option V}
    (h : (proto Vr next v₀).receive (.wr w) src m L = some (l, out, r)) {x}
    (hx : x ∈ out) : ∃ s t v op, x = (Node.sv s, Msg.writeRequest t v op) := by
  obtain ⟨-, -, h | ⟨-, rfl, -⟩⟩ := receive_wr h
  · obtain ⟨s, rfl, hx'⟩ := h
    obtain ⟨ack', hrec, -, -⟩ := wRecord_spec (Vr := Vr) s m L.w
    rw [hrec] at hx'
    rcases wWait_spec (R := R) (next := next) w { L.w with ack := ack' } with
      ⟨-, hw⟩ | ⟨-, val, -, hw⟩ | ⟨-, -, hw⟩ <;> rw [hw] at hx' <;>
      simp only [Prod.mk.injEq] at hx' <;> obtain ⟨-, rfl, -⟩ := hx'
    · simp at hx
    · obtain ⟨s', rfl⟩ := mem_bcast.1 hx
      exact ⟨s', _, _, _, rfl⟩
    · simp at hx
  · simp at hx

lemma rInv_step (hI : RInv C) (h : (proto Vr next v₀).step C s = some (C', ℓ)) : RInv C' := by
  rcases step_cases h with ⟨hloc, hsent, hnet, -, -⟩ | ⟨p, o, l, out, rfl, -, -, hinv, rfl⟩ |
      ⟨src, dst, m, l, out, r, rfl, -, hmem, hrec, rfl, -⟩
  · have hrop : rop C' = rop C := by funext r; simp [rop, hloc]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hsent, hrop]; exact hI.msg
    · intro x hx; rw [hsent]; exact hI.net x (Multiset.mem_of_le hnet hx)
    · rw [hrop, hloc]; exact hI.ops
    · rw [hloc]; exact hI.got
    · rw [hloc, hsent]; exact hI.quorum
  · cases p with
    | sv _ => simp [invoke_sv] at hinv
    | wr w =>
      obtain ⟨val, rfl, hw, -, -⟩ := invoke_wr hinv
      obtain ⟨-, hc⟩ := wInvoke_spec hw
      refine hI.of_client le_rfl (fun _ => by simp) (fun r => by simp [rop, Config.apply]) ?_
      rintro ⟨a, b, c⟩ hx
      simp only [mem_outMsgs] at hx
      obtain ⟨rfl, hx⟩ := hx
      rcases hc with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> obtain ⟨s', hs'⟩ := mem_bcast.1 hx <;>
        simp only [Prod.mk.injEq] at hs' <;>
        obtain ⟨rfl, rfl⟩ := hs' <;> simp [MsgOK]
    | rd r0 =>
      obtain ⟨-, hr, -, -⟩ := invoke_rd hinv
      obtain ⟨-, hl, rfl⟩ := rInvoke_spec hr
      have hrop : ∀ r, rop C r ≤ rop (C.apply (.rd r0) l (bcast (.readRequest
          ((C.loc (.rd r0)).r.op + 1))) C.net) r := by
        intro r
        by_cases hr : r = r0
        · subst hr; simp [rop, Config.apply, hl]
        · simp [rop, Config.apply, hr]
      refine hI.of_client le_rfl (fun _ => by simp) hrop ?_
      intro x hx
      obtain ⟨hx1, hx⟩ := mem_outMsgs.1 hx
      obtain ⟨s', hs'⟩ := mem_bcast.1 hx
      obtain ⟨a, b, c⟩ := x
      simp only [Prod.mk.injEq] at hs' hx1
      obtain ⟨rfl, rfl⟩ := hs'
      subst hx1
      simp [MsgOK, rop, Config.apply, hl]
  · cases dst with
    | wr w =>
      refine hI.of_client (Multiset.erase_le _ _) (fun _ => by simp)
        (fun r => by simp [rop, Config.apply]) ?_
      rintro ⟨a, b, c⟩ hx
      simp only [mem_outMsgs] at hx
      obtain ⟨rfl, hx⟩ := hx
      obtain ⟨s', t, v, op, hx'⟩ := wr_out hrec hx
      simp only [Prod.mk.injEq] at hx'
      obtain ⟨rfl, rfl⟩ := hx'
      simp [MsgOK]
    | rd r0 =>
      have hop := receive_rd_op hrec
      obtain ⟨-, -, rfl, -⟩ := receive_rd hrec
      refine hI.of_client (Multiset.erase_le _ _) (fun _ => by simp) ?_ (by simp [outMsgs])
      intro r
      by_cases hr : r = r0
      · subst hr; simp [rop, Config.apply, hop]
      · simp [rop, Config.apply, hr]
    | sv s0 =>
      obtain ⟨-, -, -, hx⟩ := receive_sv hrec
      have hmsg := hI.msg _ (hI.net _ hmem)
      rcases sRecv_spec (Vr := Vr) src m (C.loc (.sv s0)).s with
        ⟨r, k, rfl, rfl, he⟩ | ⟨sj, t, v, r, k, rfl, rfl, he⟩ | ⟨w, t, v, op, rfl, rfl, he⟩ |
        ⟨w, op, rfl, rfl, he⟩ | he <;> rw [he] at hx <;> simp only [Prod.ext_iff] at hx <;>
        obtain ⟨hls, rfl⟩ := hx
      · -- readRequest
        simp only [MsgOK] at hmsg
        have hk := hmsg r rfl
        refine hI.of_server (Multiset.erase_le _ _) ?_ (by rw [hls]; exact hI.ops s0)
          (by rw [hls]; exact hI.got s0) ?_
        · rintro ⟨a, b, c⟩ hx
          simp only [mem_outMsgs] at hx
          obtain ⟨rfl, hx⟩ := hx
          simp only [Multiset.mem_add] at hx
          rcases hx with hx | hx
          · obtain ⟨s', hs'⟩ := mem_bcast.1 hx
            simp only [Prod.mk.injEq] at hs'
            obtain ⟨rfl, rfl⟩ := hs'
            simpa [MsgOK] using hk
          · split_ifs at hx
            · simp only [Multiset.mem_singleton, Prod.mk.injEq] at hx
              obtain ⟨rfl, rfl⟩ := hx
              simpa [MsgOK] using hk
            · simp at hx
        · rw [hls]
          intro r' h
          obtain ⟨t, v, h⟩ := hI.quorum s0 r' h
          exact ⟨t, v, Multiset.mem_add.2 (Or.inl h)⟩
      · -- readRelay
        simp only [MsgOK] at hmsg
        set L := (C.loc (.sv s0)).s with hL
        have hmaj := one_le_maj S
        refine hI.of_server (Multiset.erase_le _ _) ?_ ?_ ?_ ?_
        · rintro ⟨a, b, c⟩ hx
          simp only [mem_outMsgs] at hx
          obtain ⟨rfl, hx⟩ := hx
          obtain ⟨t', v', hx'⟩ := sRelay_out_mem hx
          simp only [Prod.mk.injEq] at hx'
          obtain ⟨rfl, rfl⟩ := hx'
          simpa [MsgOK] using hmsg
        · intro r'
          rw [hls, sRelay_ops]
          split_ifs with hr
          · subst hr; exact max_le (hI.ops s0 r') hmsg
          · exact hI.ops s0 r'
        · intro r'
          rw [hls]
          by_cases hr : r' = r
          · subst hr
            rcases lt_trichotomy (L.ops r') k with hk | hk | hk
            · rw [(sRelay_lt hk).1, (sRelay_lt hk).2]; simp
            · rw [(sRelay_eq hk).1, (sRelay_eq hk).2]
              exact (Finset.card_insert_le _ _).trans
                (by have : (L.got r').card ≤ L.relays r' := hI.got s0 r'; omega)
            · rw [(sRelay_gt hk).1, (sRelay_gt hk).2]; exact hI.got s0 r'
          · rw [(sRelay_ne hr).1, (sRelay_ne hr).2]; exact hI.got s0 r'
        · intro r'
          rw [hls]
          by_cases hr : r' = r
          · subst hr
            have hops : (sRelay Vr sj t v r' k L).1.ops r' = max (L.ops r') k := by
              rw [sRelay_ops]; simp
            rcases lt_trichotomy (L.ops r') k with hk | hk | hk
            · rw [(sRelay_lt hk).1]
              intro h1
              have hm : (sRelay Vr sj t v r' k L).1.relays r' = maj S := by
                rw [(sRelay_lt hk).1]; omega
              have ho : (sRelay Vr sj t v r' k L).1.ops r' = k := by
                rw [hops]; exact max_eq_right hk.le
              obtain ⟨t', v', h'⟩ := sRelay_out_maj ho hm
              rw [ho]
              exact ⟨t', v', Multiset.mem_add.2 (Or.inr (mem_outMsgs.2 ⟨rfl, h'⟩))⟩
            · rw [(sRelay_eq hk).1]
              intro h1
              have ho : (sRelay Vr sj t v r' k L).1.ops r' = k := by rw [hops, hk]; simp
              rw [ho]
              by_cases hlt : maj S ≤ L.relays r'
              · obtain ⟨t', v', h'⟩ := hI.quorum s0 r' hlt
                rw [← hL, hk] at h'
                exact ⟨t', v', Multiset.mem_add.2 (Or.inl h')⟩
              · have hm : (sRelay Vr sj t v r' k L).1.relays r' = maj S := by
                  rw [(sRelay_eq hk).1]; omega
                obtain ⟨t', v', h'⟩ := sRelay_out_maj ho hm
                exact ⟨t', v', Multiset.mem_add.2 (Or.inr (mem_outMsgs.2 ⟨rfl, h'⟩))⟩
            · rw [(sRelay_gt hk).1]
              have ho : (sRelay Vr sj t v r' k L).1.ops r' = L.ops r' := by
                rw [hops]; exact max_eq_left hk.le
              rw [ho]
              intro h1
              obtain ⟨t', v', h'⟩ := hI.quorum s0 r' h1
              exact ⟨t', v', Multiset.mem_add.2 (Or.inl h')⟩
          · have ho : (sRelay Vr sj t v r k L).1.ops r' = L.ops r' := by
              rw [sRelay_ops]; simp [hr]
            rw [(sRelay_ne hr).1, ho]
            intro h1
            obtain ⟨t', v', h'⟩ := hI.quorum s0 r' h1
            exact ⟨t', v', Multiset.mem_add.2 (Or.inl h')⟩
      · -- writeRequest
        obtain ⟨h1, h2, h3, h4, -⟩ := sWrite_spec (Vr := Vr) (w := w) (t := t) (v := v) (op := op)
          (L := (C.loc (.sv s0)).s)
        refine hI.of_server (Multiset.erase_le _ _) ?_ (by rw [hls, h1]; exact hI.ops s0)
          (by rw [hls, h2, h3]; exact hI.got s0) ?_
        · rintro ⟨a, b, c⟩ hx
          simp only [mem_outMsgs] at hx
          obtain ⟨rfl, hx⟩ := hx
          rw [h4] at hx
          simp only [Multiset.mem_singleton, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          simp [MsgOK]
        · rw [hls, h1, h2]
          intro r' h
          obtain ⟨t, v, h⟩ := hI.quorum s0 r' h
          exact ⟨t, v, Multiset.mem_add.2 (Or.inl h)⟩
      · -- discover
        refine hI.of_server (Multiset.erase_le _ _) ?_ (by rw [hls]; exact hI.ops s0)
          (by rw [hls]; exact hI.got s0) ?_
        · rintro ⟨a, b, c⟩ hx
          simp only [mem_outMsgs] at hx
          obtain ⟨rfl, hx⟩ := hx
          simp only [Multiset.mem_singleton, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          simp [MsgOK]
        · rw [hls]
          intro r' h
          obtain ⟨t, v, h⟩ := hI.quorum s0 r' h
          exact ⟨t, v, Multiset.mem_add.2 (Or.inl h)⟩
      · refine hI.of_server (Multiset.erase_le _ _) (by simp [outMsgs])
          (by rw [hls]; exact hI.ops s0) (by rw [hls]; exact hI.got s0) ?_
        rw [hls]
        intro r' h
        obtain ⟨t, v, h⟩ := hI.quorum s0 r' h
        exact ⟨t, v, Multiset.mem_add.2 (Or.inl h)⟩

lemma rInv_of_reach {h : List (Label (Node W R S) (register V v₀))}
    (hr : (proto Vr next v₀).Reach C h) : RInv C := by
  induction hr with
  | init => exact rInv_init
  | step _ hs ih => exact rInv_step ih hs

/-! ## Single-writer tags -/

/-- The tag carried by a `writeRequest` or `readRelay` is at most `τ`. -/
def TagOK (τ : T) : Node W R S × Node W R S × Msg R T V → Prop
  | (_, _, m) =>
    match m with
    | .writeRequest t _ _ => t ≤ τ
    | .readRelay t _ _ _ => t ≤ τ
    | _ => True

lemma TagOK.mono {τ τ' : T} (h : τ ≤ τ') {x : Node W R S × Node W R S × Msg R T V}
    (hx : TagOK τ x) : TagOK τ' x := by
  obtain ⟨a, b, m⟩ := x
  cases m <;> simp only [TagOK] at hx ⊢ <;> first | trivial | exact hx.trans h

/-- Single writer: every tag in the system is at most the writer's tag. -/
structure TInv (C : Cfg W R S T V) : Prop where
  phase : ∀ w val, (C.loc (.wr w)).w.phase ≠ .disc val
  srv : ∀ w s, (C.loc (.sv s)).s.tag ≤ (C.loc (.wr w)).w.tag
  msg : ∀ w, ∀ x ∈ C.sent, TagOK (C.loc (.wr w)).w.tag x
  net : ∀ x ∈ C.net, x ∈ C.sent

section SW

variable (hmw : Vr.mw = false) (hsw : ∀ w w' : W, w = w') (hlt : ∀ w t, t ≤ next w t)
include hmw hsw hlt

lemma TInv.of_server (hI : TInv C) {s0 : S} {l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)} {net : Multiset (Node W R S × Node W R S × Msg R T V)}
    (hnet : net ≤ C.net) (hnew : ∀ w, ∀ x ∈ outMsgs (.sv s0) out, TagOK (C.loc (.wr w)).w.tag x)
    (htag : ∀ w, l.s.tag ≤ (C.loc (.wr w)).w.tag) :
    TInv (C.apply (.sv s0) l out net) := by
  have hw : ∀ w, (C.apply (.sv s0) l out net).loc (.wr w) = C.loc (.wr w) := fun w => by
    simp [Config.apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w val; rw [hw]; exact hI.phase w val
  · intro w s; rw [hw]
    by_cases hs : s = s0
    · subst hs; simpa [Config.apply] using htag w
    · simpa [Config.apply, hs] using hI.srv w s
  · intro w x hx; rw [hw]
    simp only [Config.apply, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · exact hI.msg w x hx
    · exact hnew w x hx
  · intro x hx
    simp only [Config.apply, Multiset.mem_add] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (hI.net x (Multiset.mem_of_le hnet hx))
    · exact Or.inr hx

lemma tInv_step (hI : TInv C) (h : (proto Vr next v₀).step C s = some (C', ℓ)) : TInv C' := by
  rcases step_cases h with ⟨hloc, hsent, hnet, -, -⟩ | ⟨p, o, l, out, rfl, -, -, hinv, rfl⟩ |
      ⟨src, dst, m, l, out, r, rfl, -, hmem, hrec, rfl, -⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hloc]; exact hI.phase
    · rw [hloc]; exact hI.srv
    · rw [hloc, hsent]; exact hI.msg
    · intro x hx; rw [hsent]; exact hI.net x (Multiset.mem_of_le hnet hx)
  · cases p with
    | sv _ => simp [invoke_sv] at hinv
    | wr w =>
      obtain ⟨val, rfl, hw, -, -⟩ := invoke_wr hinv
      obtain ⟨-, hc⟩ := wInvoke_spec hw
      rcases hc with ⟨h1, -⟩ | ⟨-, hl, rfl⟩
      · rw [hmw] at h1; cases h1
      have hw' : ∀ w', (C.apply (.wr w) l
          (bcast (.writeRequest (next w (C.loc (.wr w)).w.tag) val 0)) C.net).loc (.wr w') = l :=
        fun w' => by
        obtain rfl := hsw w w'; simp [Config.apply]
      have htag : (C.loc (.wr w)).w.tag ≤ l.w.tag := by rw [hl]; exact hlt _ _
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro w' val'; rw [hw', hl]; simp
      · intro w' s'
        rw [hw']
        simpa [Config.apply] using (hI.srv w s').trans htag
      · intro w' x hx
        rw [hw']
        simp only [Config.apply, Multiset.mem_add] at hx
        rcases hx with hx | hx
        · exact (hI.msg w x hx).mono htag
        · obtain ⟨a, b, c⟩ := x
          simp only [mem_outMsgs] at hx
          obtain ⟨-, hx⟩ := hx
          obtain ⟨s', hs'⟩ := mem_bcast.1 hx
          simp only [Prod.mk.injEq] at hs'
          obtain ⟨rfl, rfl⟩ := hs'
          simp [TagOK, hl]
      · intro x hx
        simp only [Config.apply, Multiset.mem_add] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (hI.net x hx)
        · exact Or.inr hx
    | rd r0 =>
      obtain ⟨-, hr, -, -⟩ := invoke_rd hinv
      obtain ⟨-, -, rfl⟩ := rInvoke_spec hr
      have hw : ∀ w, (C.apply (.rd r0) l (bcast (.readRequest ((C.loc (.rd r0)).r.op + 1)))
          C.net).loc (.wr w) = C.loc (.wr w) := fun w => by simp [Config.apply]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro w' val'; rw [hw]; exact hI.phase w' val'
      · intro w' s'; rw [hw]; simpa [Config.apply] using hI.srv w' s'
      · intro w' x hx
        rw [hw]
        simp only [Config.apply, Multiset.mem_add] at hx
        rcases hx with hx | hx
        · exact hI.msg w' x hx
        · obtain ⟨a, b, c⟩ := x
          simp only [mem_outMsgs] at hx
          obtain ⟨-, hx⟩ := hx
          obtain ⟨s', hs'⟩ := mem_bcast.1 hx
          simp only [Prod.mk.injEq] at hs'
          obtain ⟨rfl, rfl⟩ := hs'
          simp [TagOK]
      · intro x hx
        simp only [Config.apply, Multiset.mem_add] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (hI.net x hx)
        · exact Or.inr hx
  · cases dst with
    | wr w =>
      obtain ⟨-, -, hx | ⟨rfl, rfl, -⟩⟩ := receive_wr hrec
      · obtain ⟨s', rfl, hx⟩ := hx
        obtain ⟨ack', hrecd, -, -⟩ := wRecord_spec (Vr := Vr) s' m (C.loc (.wr w)).w
        rw [hrecd] at hx
        have hl : l.w.tag = (C.loc (.wr w)).w.tag ∧ out = 0 ∧
            ∀ val, l.w.phase ≠ .disc val := by
          rcases wWait_spec (R := R) (next := next) w { (C.loc (.wr w)).w with ack := ack' } with
            ⟨-, hw⟩ | ⟨-, val, hph, -⟩ | ⟨-, -, hw⟩
          · rw [hw] at hx
            simp only [Prod.mk.injEq] at hx
            obtain ⟨h1, rfl, -⟩ := hx
            rw [h1]
            exact ⟨rfl, rfl, hI.phase w⟩
          · exact absurd hph (hI.phase w val)
          · rw [hw] at hx
            simp only [Prod.mk.injEq] at hx
            obtain ⟨h1, rfl, -⟩ := hx
            rw [h1]
            exact ⟨rfl, rfl, by simp⟩
        obtain ⟨hl1, rfl, hl3⟩ := hl
        have hw' : ∀ w', (C.apply (.wr w) l 0 (C.net.erase (Node.sv s', Node.wr w, m))).loc
            (.wr w') = l := fun w' => by
          obtain rfl := hsw w w'; simp [Config.apply]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro w' val'; rw [hw']; exact hl3 val'
        · intro w' s''; rw [hw', hl1]; simpa [Config.apply] using hI.srv w s''
        · intro w' x hx; rw [hw', hl1]
          simp only [Config.apply, outMsgs, Multiset.map_zero, add_zero] at hx
          exact hI.msg w x hx
        · intro x hx
          simp only [Config.apply, outMsgs, Multiset.map_zero, add_zero] at hx ⊢
          exact hI.net x (Multiset.mem_of_le (Multiset.erase_le _ _) hx)
      · refine ⟨?_, ?_, ?_, ?_⟩
        · intro w' val'; simpa [Config.apply, Function.update_apply] using hI.phase w' val'
        · intro w' s'
          have := hI.srv w' s'
          by_cases hw : w' = w
          · subst hw; simpa [Config.apply] using this
          · simpa [Config.apply, hw] using this
        · intro w' x hx
          simp only [Config.apply, outMsgs, Multiset.map_zero, add_zero] at hx
          have := hI.msg w' x hx
          by_cases hw : w' = w
          · subst hw; simpa [Config.apply] using this
          · simpa [Config.apply, hw] using this
        · intro x hx
          simp only [Config.apply, outMsgs, Multiset.map_zero, add_zero] at hx ⊢
          exact hI.net x (Multiset.mem_of_le (Multiset.erase_le _ _) hx)
    | rd r0 =>
      obtain ⟨-, -, rfl, -⟩ := receive_rd hrec
      have hw : ∀ w, (C.apply (.rd r0) l 0 (C.net.erase (src, Node.rd r0, m))).loc (.wr w) =
          C.loc (.wr w) := fun w => by simp [Config.apply]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro w' val'; rw [hw]; exact hI.phase w' val'
      · intro w' s'; rw [hw]; simpa [Config.apply] using hI.srv w' s'
      · intro w' x hx
        rw [hw]
        simp only [Config.apply, outMsgs, Multiset.map_zero, add_zero] at hx
        exact hI.msg w' x hx
      · intro x hx
        simp only [Config.apply, outMsgs, Multiset.map_zero, add_zero] at hx ⊢
        exact hI.net x (Multiset.mem_of_le (Multiset.erase_le _ _) hx)
    | sv s0 =>
      obtain ⟨-, -, -, hx⟩ := receive_sv hrec
      have hmsg := fun w => hI.msg w _ (hI.net _ hmem)
      rcases sRecv_spec (Vr := Vr) src m (C.loc (.sv s0)).s with
        ⟨r, k, rfl, rfl, he⟩ | ⟨sj, t, v, r, k, rfl, rfl, he⟩ | ⟨w, t, v, op, rfl, rfl, he⟩ |
        ⟨w, op, rfl, rfl, he⟩ | he <;> rw [he] at hx <;> simp only [Prod.ext_iff] at hx <;>
        obtain ⟨hls, rfl⟩ := hx
      · refine hI.of_server hmw hsw hlt (Multiset.erase_le _ _) ?_ (fun w => by
          rw [hls]; exact hI.srv w s0)
        rintro w ⟨a, b, c⟩ hx
        simp only [mem_outMsgs] at hx
        obtain ⟨rfl, hx⟩ := hx
        simp only [Multiset.mem_add] at hx
        rcases hx with hx | hx
        · obtain ⟨s', hs'⟩ := mem_bcast.1 hx
          simp only [Prod.mk.injEq] at hs'
          obtain ⟨rfl, rfl⟩ := hs'
          simpa [TagOK] using hI.srv w s0
        · split_ifs at hx
          · simp only [Multiset.mem_singleton, Prod.mk.injEq] at hx
            obtain ⟨rfl, rfl⟩ := hx
            simpa [TagOK] using hI.srv w s0
          · simp at hx
      · refine hI.of_server hmw hsw hlt (Multiset.erase_le _ _) ?_ (fun w => ?_)
        · rintro w ⟨a, b, c⟩ hx
          simp only [mem_outMsgs] at hx
          obtain ⟨rfl, hx⟩ := hx
          obtain ⟨t', v', hx'⟩ := sRelay_out_mem hx
          simp only [Prod.mk.injEq] at hx'
          obtain ⟨rfl, rfl⟩ := hx'
          simp [TagOK]
        · rw [hls, sRelay_tag]
          have := hmsg w
          simp only [TagOK] at this
          split_ifs
          · exact this
          · exact hI.srv w s0
      · obtain ⟨-, -, -, h4, h5⟩ := sWrite_spec (Vr := Vr) (w := w) (t := t) (v := v) (op := op)
          (L := (C.loc (.sv s0)).s)
        refine hI.of_server hmw hsw hlt (Multiset.erase_le _ _) ?_ (fun w' => ?_)
        · rintro w' ⟨a, b, c⟩ hx
          simp only [mem_outMsgs] at hx
          obtain ⟨rfl, hx⟩ := hx
          rw [h4] at hx
          simp only [Multiset.mem_singleton, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          simp [TagOK]
        · rw [hls, h5 hmw]
          have := hmsg w'
          simp only [TagOK] at this
          split_ifs
          · exact this
          · exact hI.srv w' s0
      · refine hI.of_server hmw hsw hlt (Multiset.erase_le _ _) ?_ (fun w => by
          rw [hls]; exact hI.srv w s0)
        rintro w' ⟨a, b, c⟩ hx
        simp only [mem_outMsgs] at hx
        obtain ⟨rfl, hx⟩ := hx
        simp only [Multiset.mem_singleton, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        simp [TagOK]
      · refine hI.of_server hmw hsw hlt (Multiset.erase_le _ _) (by simp [outMsgs]) (fun w => by
          rw [hls]; exact hI.srv w s0)

lemma tInv_of_reach {h : List (Label (Node W R S) (register V v₀))}
    (hr : (proto Vr next v₀).Reach C h) : TInv C := by
  induction hr with
  | init =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Protocol.initCfg, proto, initLoc]
  | step _ hs ih => exact tInv_step hmw hsw hlt ih hs

end SW

end Podc.OhRAM.Liveness
