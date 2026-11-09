import Papers.PODC2016.OhRAMAtomicMemory.Model

/-!
# Step lemmas for the safety proof

Classification of the steps of `proto Vr next v₀` (`step_cases`), the effect of the local
transitions on the variables used in the safety proof, and the messages they send.
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]

/-- Configurations of the protocol. -/
abbrev Cfg (W R S T V : Type) := Config (Node W R S) (Loc W R S T V) (Msg R T V)

/-- The local state of writer `w`. -/
def Cfg.wl (C : Cfg W R S T V) (w : W) : WLoc S T V := (C.loc (.wr w)).w
/-- The local state of reader `r`. -/
def Cfg.rl (C : Cfg W R S T V) (r : R) : RLoc S T V := (C.loc (.rd r)).r
/-- The local state of server `s`. -/
def Cfg.sl (C : Cfg W R S T V) (s : S) : SLoc W R S T V := (C.loc (.sv s)).s

/-- The tag and value carried by a message (if any). -/
def Msg.tv : Msg R T V → Option (T × V)
  | .readRelay t v _ _ => some (t, v)
  | .readAck t v _ => some (t, v)
  | .writeRequest t v _ => some (t, v)
  | .writeAck t v _ => some (t, v)
  | .discoverAck t v _ => some (t, v)
  | _ => none

@[simp] lemma Msg.tv_readRelay (t : T) (v : V) (r : R) (k : ℕ) :
    (Msg.readRelay t v r k).tv = some (t, v) := rfl
@[simp] lemma Msg.tv_readAck (t : T) (v : V) (k : ℕ) :
    (Msg.readAck t v k : Msg R T V).tv = some (t, v) := rfl
@[simp] lemma Msg.tv_writeRequest (t : T) (v : V) (k : ℕ) :
    (Msg.writeRequest t v k : Msg R T V).tv = some (t, v) := rfl
@[simp] lemma Msg.tv_writeAck (t : T) (v : V) (k : ℕ) :
    (Msg.writeAck t v k : Msg R T V).tv = some (t, v) := rfl
@[simp] lemma Msg.tv_discoverAck (t : T) (v : V) (k : ℕ) :
    (Msg.discoverAck t v k : Msg R T V).tv = some (t, v) := rfl
@[simp] lemma Msg.tv_readRequest (k : ℕ) : (Msg.readRequest k : Msg R T V).tv = none := rfl
@[simp] lemma Msg.tv_discover (k : ℕ) : (Msg.discover k : Msg R T V).tv = none := rfl

/-! ## Updating one process -/

/-- Writer `w` takes a step to `l`, sending `out`; `net` is the network before sending. -/
def Cfg.setW (C : Cfg W R S T V) (w : W) (l : WLoc S T V) (out : Multiset (Node W R S × Msg R T V))
    (net : Multiset (Node W R S × Node W R S × Msg R T V)) : Cfg W R S T V :=
  C.apply (.wr w) { C.loc (.wr w) with w := l } out net

/-- Reader `r` takes a step to `l`. -/
def Cfg.setR (C : Cfg W R S T V) (r : R) (l : RLoc S T V) (out : Multiset (Node W R S × Msg R T V))
    (net : Multiset (Node W R S × Node W R S × Msg R T V)) : Cfg W R S T V :=
  C.apply (.rd r) { C.loc (.rd r) with r := l } out net

/-- Server `s` takes a step to `l`. -/
def Cfg.setS (C : Cfg W R S T V) (s : S) (l : SLoc W R S T V)
    (out : Multiset (Node W R S × Msg R T V))
    (net : Multiset (Node W R S × Node W R S × Msg R T V)) : Cfg W R S T V :=
  C.apply (.sv s) { C.loc (.sv s) with s := l } out net

section SetLemmas

variable (C : Cfg W R S T V) (out : Multiset (Node W R S × Msg R T V))
  (net : Multiset (Node W R S × Node W R S × Msg R T V))

@[simp] lemma setW_wl (w w' : W) (l : WLoc S T V) :
    (C.setW w l out net).wl w' = if w' = w then l else C.wl w' := by
  by_cases h : w' = w
  · subst h; simp [Cfg.setW, Cfg.wl, Config.apply]
  · simp [Cfg.setW, Cfg.wl, Config.apply, h]
@[simp] lemma setW_rl (w : W) (l : WLoc S T V) (r : R) :
    (C.setW w l out net).rl r = C.rl r := by simp [Cfg.setW, Cfg.rl, Config.apply]
@[simp] lemma setW_sl (w : W) (l : WLoc S T V) (s : S) :
    (C.setW w l out net).sl s = C.sl s := by simp [Cfg.setW, Cfg.sl, Config.apply]
@[simp] lemma setW_sent (w : W) (l : WLoc S T V) :
    (C.setW w l out net).sent = C.sent + outMsgs (.wr w) out := rfl
@[simp] lemma setW_net (w : W) (l : WLoc S T V) :
    (C.setW w l out net).net = net + outMsgs (.wr w) out := rfl

@[simp] lemma setR_wl (r : R) (l : RLoc S T V) (w : W) :
    (C.setR r l out net).wl w = C.wl w := by simp [Cfg.setR, Cfg.wl, Config.apply]
@[simp] lemma setR_rl (r r' : R) (l : RLoc S T V) :
    (C.setR r l out net).rl r' = if r' = r then l else C.rl r' := by
  by_cases h : r' = r
  · subst h; simp [Cfg.setR, Cfg.rl, Config.apply]
  · simp [Cfg.setR, Cfg.rl, Config.apply, h]
@[simp] lemma setR_sl (r : R) (l : RLoc S T V) (s : S) :
    (C.setR r l out net).sl s = C.sl s := by simp [Cfg.setR, Cfg.sl, Config.apply]
@[simp] lemma setR_sent (r : R) (l : RLoc S T V) :
    (C.setR r l out net).sent = C.sent + outMsgs (.rd r) out := rfl
@[simp] lemma setR_net (r : R) (l : RLoc S T V) :
    (C.setR r l out net).net = net + outMsgs (.rd r) out := rfl

@[simp] lemma setS_wl (s : S) (l : SLoc W R S T V) (w : W) :
    (C.setS s l out net).wl w = C.wl w := by simp [Cfg.setS, Cfg.wl, Config.apply]
@[simp] lemma setS_rl (s : S) (l : SLoc W R S T V) (r : R) :
    (C.setS s l out net).rl r = C.rl r := by simp [Cfg.setS, Cfg.rl, Config.apply]
@[simp] lemma setS_sl (s s' : S) (l : SLoc W R S T V) :
    (C.setS s l out net).sl s' = if s' = s then l else C.sl s' := by
  by_cases h : s' = s
  · subst h; simp [Cfg.setS, Cfg.sl, Config.apply]
  · simp [Cfg.setS, Cfg.sl, Config.apply, h]
@[simp] lemma setS_sent (s : S) (l : SLoc W R S T V) :
    (C.setS s l out net).sent = C.sent + outMsgs (.sv s) out := rfl
@[simp] lemma setS_net (s : S) (l : SLoc W R S T V) :
    (C.setS s l out net).net = net + outMsgs (.sv s) out := rfl

end SetLemmas

/-! ## Classification of steps -/

variable {Vr : Variant} {next : W → T → T} {v₀ : V}

/-- Every step is silent (local states and sent messages unchanged, network shrinks), an
invocation of a writer or a reader, or a reception by a writer, a reader or a server (of a
message from a server, for writers and readers). -/
lemma step_cases {C C' : Cfg W R S T V} {st : Step (Node W R S) (register V v₀) (Msg R T V) Empty}
    {ℓ : Option (Label (Node W R S) (register V v₀))}
    (h : (proto Vr next v₀).step C st = some (C', ℓ)) :
    (C'.loc = C.loc ∧ C'.sent = C.sent ∧ ℓ = none ∧ C'.net ≤ C.net) ∨
    (∃ w v l out, wInvoke Vr next w v (C.wl w) = some (l, out) ∧ C' = C.setW w l out C.net ∧
      ℓ = some (.inv (.wr w) (.write v))) ∨
    (∃ r l out, rInvoke (C.rl r) = some (l, out) ∧ C' = C.setR r l out C.net ∧
      ℓ = some (.inv (.rd r) .read)) ∨
    (∃ w s m, (Node.sv s, Node.wr w, m) ∈ C.net ∧
      C' = C.setW w (wWait (R := R) next w (wRecord Vr s m (C.wl w))).1
        (wWait (R := R) next w (wRecord Vr s m (C.wl w))).2.1
        (C.net.erase (.sv s, .wr w, m)) ∧
      ℓ = (wWait (R := R) next w (wRecord Vr s m (C.wl w))).2.2.map (Label.ret (.wr w))) ∨
    (∃ r s m, (Node.sv s, Node.rd r, m) ∈ C.net ∧
      C' = C.setR r (rWait Vr v₀ (rRecord Vr s m (C.rl r))).1 0
        (C.net.erase (.sv s, .rd r, m)) ∧
      ℓ = (rWait Vr v₀ (rRecord Vr s m (C.rl r))).2.map (Label.ret (.rd r))) ∨
    (∃ s q m, (q, Node.sv s, m) ∈ C.net ∧
      C' = C.setS s (sRecv Vr q m (C.sl s)).1 (sRecv Vr q m (C.sl s)).2
        (C.net.erase (q, .sv s, m)) ∧ ℓ = none) := by
  cases st with
  | inv p o =>
    simp only [Protocol.step] at h
    split_ifs at h
    obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [proto] at hx
    split at hx
    · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
      exact Or.inr (Or.inl ⟨_, _, y.1, y.2, hy, rfl, rfl⟩)
    · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
      exact Or.inr (Or.inr (Or.inl ⟨_, y.1, y.2, hy, rfl, rfl⟩))
    · simp at hx
  | internal p a => exact a.elim
  | recv src dst m =>
    simp only [Protocol.step] at h
    split_ifs at h with hc
    push Not at hc
    obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [proto] at hx
    split at hx
    · simp only [Option.some.injEq] at hx; subst hx
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, hc.2, rfl, rfl⟩)))
    · simp only [Option.some.injEq] at hx; subst hx
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, hc.2, rfl, rfl⟩))))
    · simp only [Option.some.injEq] at hx; subst hx
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, hc.2, rfl, rfl⟩))))
    · simp only [Option.some.injEq] at hx; subst hx
      refine Or.inl ⟨?_, by simp [Config.apply, outMsgs], rfl, ?_⟩
      · simp [Config.apply]
      · simp only [Config.apply, outMsgs, Multiset.map_zero, add_zero]
        exact Multiset.erase_le _ _
  | drop src dst m =>
    simp only [Protocol.step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, rfl, Multiset.erase_le _ _⟩
  | crash p =>
    simp only [Protocol.step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, rfl, le_rfl⟩
  | skip =>
    simp only [Protocol.step, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, rfl, le_rfl⟩

/-! ## Sent messages -/

omit [LinearOrder T] [OrderBot T] in
lemma outMsgs_bcast (p : Node W R S) (m : Msg R T V) :
    outMsgs p (bcast m) = (Finset.univ : Finset S).val.map (fun s => (p, Node.sv s, m)) := by
  simp [outMsgs, bcast, Multiset.map_map]

omit [LinearOrder T] [OrderBot T] in
@[simp] lemma mem_outMsgs_bcast {p : Node W R S} {m : Msg R T V}
    {x : Node W R S × Node W R S × Msg R T V} :
    x ∈ outMsgs p (bcast m) ↔ x.1 = p ∧ (∃ s, x.2.1 = .sv s) ∧ x.2.2 = m := by
  obtain ⟨a, b, c⟩ := x
  rw [outMsgs_bcast]
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨s, rfl, rfl, rfl⟩; exact ⟨rfl, ⟨s, rfl⟩, rfl⟩
  · rintro ⟨rfl, ⟨s, rfl⟩, rfl⟩; exact ⟨s, rfl, rfl, rfl⟩

omit [LinearOrder T] [OrderBot T] in
@[simp] lemma outMsgs_single (p q : Node W R S) (m : Msg R T V) :
    outMsgs p ({(q, m)} : Multiset (Node W R S × Msg R T V)) = {(p, q, m)} := rfl

omit [LinearOrder T] [OrderBot T] in
@[simp] lemma outMsgs_zero' (p : Node W R S) :
    outMsgs p (0 : Multiset (Node W R S × Msg R T V)) = 0 := rfl

omit [LinearOrder T] [OrderBot T] in
@[simp] lemma outMsgs_add (p : Node W R S) (a b : Multiset (Node W R S × Msg R T V)) :
    outMsgs p (a + b) = outMsgs p a + outMsgs p b := by simp [outMsgs]

omit [LinearOrder T] [OrderBot T] in
lemma countP_outMsgs_bcast (P : Node W R S × Node W R S × Msg R T V → Prop) [DecidablePred P]
    (p : Node W R S) (m : Msg R T V) :
    (outMsgs p (bcast m)).countP P =
      ((Finset.univ : Finset S).filter (fun s => P (p, .sv s, m))).card := by
  rw [outMsgs_bcast, Multiset.countP_map, Finset.card_def, Finset.filter_val]

/-- Counting after receiving `x` and sending `o`. -/
lemma countP_erase_add (P : Node W R S × Node W R S × Msg R T V → Prop) [DecidablePred P]
    {net o : Multiset (Node W R S × Node W R S × Msg R T V)} {x : Node W R S × Node W R S × Msg R T V}
    (hx : x ∈ net) :
    (net.erase x + o).countP P + (if P x then 1 else 0) = net.countP P + o.countP P := by
  conv_rhs => rw [← Multiset.cons_erase hx]
  rw [Multiset.countP_add, Multiset.countP_cons]
  omega

/-! ## Writer transitions -/

/-- Writer in state `l` accepts the message `m` with tag `t` and value `v` (lines 29–31 /
92–94). -/
def WAcc (Vr : Variant) (l : WLoc S T V) (m : Msg R T V) (t : T) (v : V) : Prop :=
  (∃ k, m = .writeAck t v k ∧ (if Vr.mw then k = l.op else t = l.tag)) ∨
  (∃ k, m = .discoverAck t v k ∧ Vr.mw = true ∧ k = l.op)

omit [Fintype S] in
lemma wRecord_cases (Vr : Variant) (s : S) (m : Msg R T V) (l : WLoc S T V) :
    wRecord Vr s m l = l ∨
      ∃ t v, WAcc Vr l m t v ∧ wRecord Vr s m l = { l with ack := l.ack.insert (s, t, v) } := by
  unfold wRecord
  split
  · rename_i t v k
    by_cases hc : (if Vr.mw then k = l.op else t = l.tag)
    · rw [ite_eq_left hc]; exact Or.inr ⟨t, v, Or.inl ⟨k, rfl, hc⟩, rfl⟩
    · rw [ite_eq_right hc]; exact Or.inl rfl
  · rename_i t v k
    split_ifs with hc
    · exact Or.inr ⟨t, v, Or.inr ⟨k, rfl, hc.1, hc.2⟩, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

omit [Fintype S] in
@[simp] lemma wRecord_tag (s : S) (m : Msg R T V) (l : WLoc S T V) :
    (wRecord Vr s m l).tag = l.tag := by
  rcases wRecord_cases Vr s m l with h | ⟨t, v, -, h⟩ <;> rw [h]
omit [Fintype S] in
@[simp] lemma wRecord_val (s : S) (m : Msg R T V) (l : WLoc S T V) :
    (wRecord Vr s m l).val = l.val := by
  rcases wRecord_cases Vr s m l with h | ⟨t, v, -, h⟩ <;> rw [h]
omit [Fintype S] in
@[simp] lemma wRecord_op (s : S) (m : Msg R T V) (l : WLoc S T V) :
    (wRecord Vr s m l).op = l.op := by
  rcases wRecord_cases Vr s m l with h | ⟨t, v, -, h⟩ <;> rw [h]
omit [Fintype S] in
@[simp] lemma wRecord_phase (s : S) (m : Msg R T V) (l : WLoc S T V) :
    (wRecord Vr s m l).phase = l.phase := by
  rcases wRecord_cases Vr s m l with h | ⟨t, v, -, h⟩ <;> rw [h]

/-- The outcomes of the waits of the writer. -/
lemma wWait_cases (w : W) (l : WLoc S T V) :
    wWait (R := R) next w l = (l, 0, none) ∨
    (∃ val, l.ack.length = maj S ∧ l.phase = .disc val ∧
      wWait (R := R) next w l =
        ({ l with tag := next w (maxTag l.ack), val := val, op := l.op + 1, ack := [], phase := .upd },
        bcast (.writeRequest (next w (maxTag l.ack)) val (l.op + 1)), none)) ∨
    (l.ack.length = maj S ∧ l.phase = .upd ∧
      wWait (R := R) next w l = ({ l with phase := .idle }, 0, some l.val)) := by
  unfold wWait
  split_ifs with h
  · split
    · rename_i val hph
      exact Or.inr (Or.inl ⟨val, h, hph, rfl⟩)
    · rename_i hph
      exact Or.inr (Or.inr ⟨h, hph, rfl⟩)
    · exact Or.inl rfl
  · exact Or.inl rfl

lemma wInvoke_cases {w : W} {val : V} {l l' : WLoc S T V} {out : Multiset (Node W R S × Msg R T V)}
    (h : wInvoke Vr next w val l = some (l', out)) :
    l.phase = .idle ∧
    ((Vr.mw = true ∧ l' = { l with op := l.op + 1, ack := [], phase := .disc val } ∧
        out = bcast (.discover (l.op + 1))) ∨
     (Vr.mw = false ∧ l' = { l with tag := next w l.tag, val := val, ack := [], phase := .upd } ∧
        out = bcast (.writeRequest (next w l.tag) val 0))) := by
  unfold wInvoke at h
  split at h
  · rename_i hph
    split_ifs at h with hmw
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hph, Or.inl ⟨hmw, rfl, rfl⟩⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hph, Or.inr ⟨by simpa using hmw, rfl, rfl⟩⟩
  · simp at h

/-! ## Reader transitions -/

omit [Fintype S] in
lemma rRecord_cases (Vr : Variant) (s : S) (m : Msg R T V) (l : RLoc S T V) :
    rRecord Vr s m l = l ∨
    (∃ t v, m = .readAck t v l.op ∧ rRecord Vr s m l = { l with ack := l.ack.insert (s, t, v) }) ∨
    (∃ t v r', Vr.fast = true ∧ m = .readRelay t v r' l.op ∧
      rRecord Vr s m l = { l with relay := l.relay.insert (s, t, v) }) := by
  unfold rRecord
  split
  · rename_i t v k
    split_ifs with hc
    · subst hc; exact Or.inr (Or.inl ⟨t, v, rfl, rfl⟩)
    · exact Or.inl rfl
  · rename_i t v r' k
    split_ifs with hc
    · obtain ⟨h1, rfl⟩ := hc
      exact Or.inr (Or.inr ⟨t, v, r', h1, rfl, rfl⟩)
    · exact Or.inl rfl
  · exact Or.inl rfl

omit [Fintype S] in
@[simp] lemma rRecord_op (s : S) (m : Msg R T V) (l : RLoc S T V) :
    (rRecord Vr s m l).op = l.op := by
  rcases rRecord_cases Vr s m l with h | ⟨t, v, -, h⟩ | ⟨t, v, r', -, -, h⟩ <;> rw [h]
omit [Fintype S] in
@[simp] lemma rRecord_pending (s : S) (m : Msg R T V) (l : RLoc S T V) :
    (rRecord Vr s m l).pending = l.pending := by
  rcases rRecord_cases Vr s m l with h | ⟨t, v, -, h⟩ | ⟨t, v, r', -, -, h⟩ <;> rw [h]

/-- The outcomes of the wait of the reader. -/
lemma rWait_cases (l : RLoc S T V) :
    rWait Vr v₀ l = (l, none) ∨
    (l.pending = true ∧ l.ack.length = maj S ∧
      rWait Vr v₀ l = ({ l with pending := false }, some (minVal v₀ l.ack))) ∨
    (∃ v, l.pending = true ∧ Vr.fast = true ∧ fastVal l.relay = some v ∧
      rWait Vr v₀ l = ({ l with pending := false }, some v)) := by
  unfold rWait
  split_ifs with h1 h2 h3
  · exact Or.inr (Or.inl ⟨h1, h2, rfl⟩)
  · split
    · rename_i v hv
      exact Or.inr (Or.inr ⟨v, h1, h3, hv, rfl⟩)
    · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

@[simp] lemma rWait_op (l : RLoc S T V) : (rWait Vr v₀ l).1.op = l.op := by
  rcases rWait_cases (Vr := Vr) (v₀ := v₀) l with h | ⟨-, -, h⟩ | ⟨v, -, -, -, h⟩ <;> rw [h]
@[simp] lemma rWait_ack (l : RLoc S T V) : (rWait Vr v₀ l).1.ack = l.ack := by
  rcases rWait_cases (Vr := Vr) (v₀ := v₀) l with h | ⟨-, -, h⟩ | ⟨v, -, -, -, h⟩ <;> rw [h]
@[simp] lemma rWait_relay (l : RLoc S T V) : (rWait Vr v₀ l).1.relay = l.relay := by
  rcases rWait_cases (Vr := Vr) (v₀ := v₀) l with h | ⟨-, -, h⟩ | ⟨v, -, -, -, h⟩ <;> rw [h]

lemma rInvoke_eq {l l' : RLoc S T V} {out : Multiset (Node W R S × Msg R T V)}
    (h : rInvoke l = some (l', out)) :
    l.pending = false ∧ l' = ⟨l.op + 1, true, [], []⟩ ∧ out = bcast (.readRequest (l.op + 1)) := by
  unfold rInvoke at h
  split_ifs at h with hp
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨by simpa using hp, rfl, rfl⟩

/-! ## Server transitions -/

section Server

variable (Vr) (sj : S) (t : T) (v : V) (r : R) (k : ℕ) (l : SLoc W R S T V)

lemma sRelay_tag : (sRelay Vr sj t v r k l).1.tag = if l.tag < t then t else l.tag := by
  simp only [sRelay]; split_ifs <;> simp_all
lemma sRelay_val : (sRelay Vr sj t v r k l).1.val = if l.tag < t then v else l.val := by
  simp only [sRelay]; split_ifs <;> simp_all
lemma sRelay_wops : (sRelay Vr sj t v r k l).1.wops = l.wops := by
  simp only [sRelay]; split_ifs <;> simp_all
lemma sRelay_ops (r' : R) :
    (sRelay Vr sj t v r k l).1.ops r' = if r' = r then max (l.ops r) k else l.ops r' := by
  simp only [sRelay]
  by_cases hr : r' = r
  · subst hr; split_ifs <;> simp_all <;> omega
  · split_ifs <;> simp_all
lemma sRelay_relays (r' : R) :
    (sRelay Vr sj t v r k l).1.relays r' =
      if r' = r then (if l.ops r < k then 1 else if l.ops r = k then l.relays r + 1 else l.relays r)
      else l.relays r' := by
  simp only [sRelay]
  by_cases hr : r' = r
  · subst hr; split_ifs <;> simp_all
  · split_ifs <;> simp_all
lemma sRelay_got (r' : R) :
    (sRelay Vr sj t v r k l).1.got r' =
      if r' = r then (if l.ops r < k then {sj} else if l.ops r = k then insert sj (l.got r)
        else l.got r)
      else l.got r' := by
  simp only [sRelay]
  by_cases hr : r' = r
  · subst hr; split_ifs <;> simp_all
  · split_ifs <;> simp_all
lemma sRelay_out : (sRelay Vr sj t v r k l).2 =
    if (Vr.fixAck = false ∨ (sRelay Vr sj t v r k l).1.ops r = k) ∧
        (sRelay Vr sj t v r k l).1.relays r = maj S then
      {(Node.rd r, Msg.readAck (sRelay Vr sj t v r k l).1.tag (sRelay Vr sj t v r k l).1.val k)}
    else 0 := rfl

omit [Fintype S] in
lemma sWrite_fst (w : W) (op : ℕ) :
    (sWrite (R := R) Vr w t v op l).1 = if Vr.mw then
      (if l.tag < t ∧ l.wops w < op then
        { l with tag := t, val := v, wops := Function.update l.wops w op } else l)
      else (if l.tag < t then { l with tag := t, val := v } else l) := rfl
omit [Fintype S] in
lemma sWrite_snd (w : W) (op : ℕ) :
    (sWrite (R := R) Vr w t v op l).2 = {(Node.wr w, Msg.writeAck (sWrite (R := R) Vr w t v op l).1.tag
      (sWrite (R := R) Vr w t v op l).1.val op)} := rfl

end Server

/-- The outcomes of a server reception. -/
lemma sRecv_cases (q : Node W R S) (m : Msg R T V) (l : SLoc W R S T V) :
    (∃ r k, q = .rd r ∧ m = .readRequest k ∧ sRecv Vr q m l = (l, bcast (.readRelay l.tag l.val r k) +
      if Vr.fast then {(Node.rd r, Msg.readRelay l.tag l.val r k)} else 0)) ∨
    (∃ sj t v r k, q = .sv sj ∧ m = .readRelay t v r k ∧ sRecv Vr q m l = sRelay Vr sj t v r k l) ∨
    (∃ w t v op, q = .wr w ∧ m = .writeRequest t v op ∧ sRecv Vr q m l = sWrite Vr w t v op l) ∨
    (∃ w op, q = .wr w ∧ m = .discover op ∧
      sRecv Vr q m l = (l, {(Node.wr w, Msg.discoverAck l.tag l.val op)})) ∨
    sRecv Vr q m l = (l, 0) := by
  unfold sRecv
  split
  · exact Or.inl ⟨_, _, rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- **Lemmas 1, 6, 13, 17** (one step): the tag of a server never decreases. -/
lemma sRecv_tag_mono (q : Node W R S) (m : Msg R T V) (l : SLoc W R S T V) :
    l.tag ≤ (sRecv Vr q m l).1.tag := by
  rcases sRecv_cases (Vr := Vr) q m l with ⟨r, k, -, -, h⟩ | ⟨sj, t, v, r, k, -, -, h⟩ |
    ⟨w, t, v, op, -, -, h⟩ | ⟨w, op, -, -, h⟩ | h <;> rw [h]
  · rw [sRelay_tag]; split_ifs with h1
    · exact h1.le
    · exact le_rfl
  · rw [sWrite_fst]; split_ifs with h1 h2 h2
    · exact h2.1.le
    · exact le_rfl
    · exact h2.le
    · exact le_rfl

/-- The new tag and value of a server are the old ones or those of the received message. -/
lemma sRecv_tv (q : Node W R S) (m : Msg R T V) (l : SLoc W R S T V) :
    ((sRecv Vr q m l).1.tag = l.tag ∧ (sRecv Vr q m l).1.val = l.val) ∨
      m.tv = some ((sRecv Vr q m l).1.tag, (sRecv Vr q m l).1.val) := by
  rcases sRecv_cases (Vr := Vr) q m l with ⟨r, k, -, -, h⟩ | ⟨sj, t, v, r, k, -, hm, h⟩ |
    ⟨w, t, v, op, -, hm, h⟩ | ⟨w, op, -, -, h⟩ | h <;> rw [h]
  · exact Or.inl ⟨rfl, rfl⟩
  · rw [sRelay_tag, sRelay_val, hm]; split_ifs
    · exact Or.inr rfl
    · exact Or.inl ⟨rfl, rfl⟩
  · rw [sWrite_fst, hm]; split_ifs <;> simp
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-- Every message sent by a server carries its new tag and value. -/
lemma sRecv_out_tv (q : Node W R S) (m : Msg R T V) (l : SLoc W R S T V) :
    ∀ x ∈ (sRecv Vr q m l).2,
      x.2.tv = some ((sRecv Vr q m l).1.tag, (sRecv Vr q m l).1.val) := by
  rcases sRecv_cases (Vr := Vr) q m l with ⟨r, k, -, -, h⟩ | ⟨sj, t, v, r, k, -, hm, h⟩ |
    ⟨w, t, v, op, -, hm, h⟩ | ⟨w, op, -, -, h⟩ | h <;> rw [h]
  · intro x hx
    simp only [Multiset.mem_add, bcast, Multiset.mem_map] at hx
    rcases hx with ⟨s, -, rfl⟩ | hx
    · rfl
    · split_ifs at hx
      · rw [Multiset.mem_singleton] at hx; subst hx; rfl
      · simp at hx
  · intro x hx
    rw [sRelay_out] at hx
    split_ifs at hx
    · rw [Multiset.mem_singleton] at hx; subst hx; rfl
    · simp at hx
  · intro x hx
    rw [sWrite_snd, Multiset.mem_singleton] at hx; subst hx; rfl
  · intro x hx
    rw [Multiset.mem_singleton] at hx; subst hx; rfl
  · intro x hx; simp at hx

end Podc.OhRAM
