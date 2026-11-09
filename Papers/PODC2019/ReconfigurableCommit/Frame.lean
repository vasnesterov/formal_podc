/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Inv

/-!
# Frame lemmas for the protocol steps

How sending messages and updating local states act on the components of the state and on the
derived notions of `Inv.lean`.
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

namespace State

variable (st : State T Pl S P) (src : P) (out : P → Option (Msg T Pl S P))

@[simp] theorem send_loc : (st.send src out).loc = st.loc := rfl
@[simp] theorem send_cs : (st.send src out).cs = st.cs := rfl
@[simp] theorem send_hist : (st.send src out).hist = st.hist := rfl
@[simp] theorem send_started : (st.send src out).started = st.started := rfl
@[simp] theorem send_elog : (st.send src out).elog = st.elog := rfl
@[simp] theorem send_base : (st.send src out).base = st.base := rfl
@[simp] theorem send_vinfo : (st.send src out).vinfo = st.vinfo := rfl

theorem send_sent (a b : P) : (st.send src out).sent a b =
    if a = src then st.sent a b ++ (out b).toList else st.sent a b := by
  unfold send
  simp only
  split_ifs <;> cases out b <;> simp

theorem send_net (a b : P) : (st.send src out).net a b =
    if a = src then st.net a b ++ (out b).toList else st.net a b := by
  unfold send
  simp only
  split_ifs <;> cases out b <;> simp

theorem mem_send_sent {m : Msg T Pl S P} {a b : P} :
    m ∈ (st.send src out).sent a b ↔ m ∈ st.sent a b ∨ (a = src ∧ out b = some m) := by
  rw [send_sent]
  split_ifs with h <;> simp [h, Option.mem_toList, eq_comm]

theorem mem_send_net {m : Msg T Pl S P} {a b : P} :
    m ∈ (st.send src out).net a b ↔ m ∈ st.net a b ∨ (a = src ∧ out b = some m) := by
  rw [send_net]
  split_ifs with h <;> simp [h, Option.mem_toList, eq_comm]

variable (p : P) (ls : LState T Pl S P)

@[simp] theorem setLoc_cs : (st.setLoc p ls).cs = st.cs := rfl
@[simp] theorem setLoc_hist : (st.setLoc p ls).hist = st.hist := rfl
@[simp] theorem setLoc_sent : (st.setLoc p ls).sent = st.sent := rfl
@[simp] theorem setLoc_net : (st.setLoc p ls).net = st.net := rfl
@[simp] theorem setLoc_started : (st.setLoc p ls).started = st.started := rfl
@[simp] theorem setLoc_elog : (st.setLoc p ls).elog = st.elog := rfl
@[simp] theorem setLoc_base : (st.setLoc p ls).base = st.base := rfl
@[simp] theorem setLoc_vinfo : (st.setLoc p ls).vinfo = st.vinfo := rfl
@[simp] theorem setLoc_loc_self : (st.setLoc p ls).loc p = ls := by simp [setLoc]
theorem setLoc_loc_ne {q : P} (h : q ≠ p) : (st.setLoc p ls).loc q = st.loc q := by
  simp [setLoc, h]
theorem setLoc_loc (q : P) : (st.setLoc p ls).loc q = if q = p then ls else st.loc q := by
  by_cases h : q = p
  · subst h; simp
  · simp [setLoc, h]

end State

section Derived

variable (st : State T Pl S P) (src : P) (out : P → Option (Msg T Pl S P))

@[simp] theorem cfg_send : cfg (st.send src out) = cfg st := rfl
@[simp] theorem cfg_setLoc (p : P) (ls : LState T Pl S P) : cfg (st.setLoc p ls) = cfg st := rfl

/-- `out` sends no `ACCEPT_ACK`. -/
def NoAcceptAck (out : P → Option (Msg T Pl S P)) : Prop :=
  ∀ b s e k t d, out b ≠ some (Msg.acceptAck s e k t d)

/-- `out` sends no `PROBE_ACK`. -/
def NoProbeAck (out : P → Option (Msg T Pl S P)) : Prop :=
  ∀ b b' E s, out b ≠ some (Msg.probeAck b' E s)

theorem acked_send (h : NoAcceptAck out) : Acked (st.send src out) = Acked st := by
  funext q s e k t d
  apply propext
  unfold Acked
  simp only [State.mem_send_sent]
  constructor
  · rintro ⟨r, hr | ⟨-, hr⟩⟩
    · exact ⟨r, hr⟩
    · exact absurd hr (h _ _ _ _ _ _)
  · rintro ⟨r, hr⟩
    exact ⟨r, Or.inl hr⟩

theorem replied_send (h : NoProbeAck out) : Replied (st.send src out) = Replied st := by
  funext q b E s
  apply propext
  unfold Replied
  simp only [State.mem_send_sent]
  constructor
  · rintro ⟨r, hr | ⟨-, hr⟩⟩
    · exact ⟨r, hr⟩
    · exact absurd hr (h _ _ _ _)
  · rintro ⟨r, hr⟩
    exact ⟨r, Or.inl hr⟩

theorem dead_send (h : NoAcceptAck out) : Dead (st.send src out) = Dead st := by
  unfold Dead; rw [acked_send st src out h]; rfl

theorem aliveK_send (h : NoAcceptAck out) : AliveK (st.send src out) = AliveK st := by
  unfold AliveK; rw [acked_send st src out h]; rfl

theorem accL_send (h : NoAcceptAck out) : AccL (st.send src out) = AccL st := by
  unfold AccL; rw [acked_send st src out h]; rfl

theorem decided_send (Pa : Params T Pl S P) (h : NoAcceptAck out) :
    Decided Pa (st.send src out) = Decided Pa st := by
  unfold Decided; rw [accL_send st src out h]

@[simp] theorem fresh_send : Fresh (st.send src out) = Fresh st := rfl
@[simp] theorem cand_send : cand (st.send src out) = cand st := rfl
@[simp] theorem plAt_send (Pa : Params T Pl S P) : plAt Pa (st.send src out) = plAt Pa st := rfl
@[simp] theorem decIn_send : DecIn (st.send src out) = DecIn st := rfl

theorem acked_mono_send {q s e k t d} (h : Acked st q s e k t d) :
    Acked (st.send src out) q s e k t d := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, (State.mem_send_sent st src out).2 (Or.inl hr)⟩

theorem replied_mono_send {q b E s} (h : Replied st q b E s) :
    Replied (st.send src out) q b E s := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, (State.mem_send_sent st src out).2 (Or.inl hr)⟩

end Derived

end Podc.ReconfigurableCommit
