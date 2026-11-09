import Papers.PODC2016.OhRAMAtomicMemory.Statements

/-!
# Step lemmas for the liveness proof

Characterizations of the transitions of `proto Vr next v₀`, generic facts on executions
(eventual reception of a message between correct processes, every message of `sent` was once in
`net`) and the local transitions of writers, readers and servers.
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM.Liveness

open Cslib.SharedMemory Cslib.AsyncMP

/-! ## Generic facts on executions

Protocol-independent lemmas on `Cslib.AsyncMP` executions.
-/

-- CSLib candidate: the whole `Generic` section (namespace `Cslib.AsyncMP.Protocol.Exec`).

section Generic

variable {P : Type} {A : ObjSpec} {L M Act : Type} [DecidableEq P] [DecidableEq M]
variable {Pr : Protocol P A L M Act}

/-- Every step either leaves `sent` unchanged or applies a local transition. -/
lemma step_shape {C C' : Config P L M} {s : Step P A M Act} {ℓ : Option (Label P A)}
    (h : Pr.step C s = some (C', ℓ)) :
    (C'.sent = C.sent ∧ C'.net ≤ C.net ∧ C'.loc = C.loc) ∨
      ∃ p l out net, net ≤ C.net ∧ C' = C.apply p l out net := by
  cases s with
  | inv p o =>
    simp only [Protocol.step] at h
    split_ifs at h
    obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at hx
    exact Or.inr ⟨p, x.1, x.2, C.net, le_rfl, hx.1.symm⟩
  | internal p a =>
    simp only [Protocol.step] at h
    split_ifs at h
    obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at hx
    exact Or.inr ⟨p, x.1, x.2.1, C.net, le_rfl, hx.1.symm⟩
  | recv src dst m =>
    simp only [Protocol.step] at h
    split_ifs at h
    obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at hx
    exact Or.inr ⟨dst, x.1, x.2.1, _, Multiset.erase_le _ _, hx.1.symm⟩
  | drop src dst m =>
    simp only [Protocol.step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact Or.inl ⟨rfl, Multiset.erase_le _ _, rfl⟩
  | crash p =>
    simp only [Protocol.step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact Or.inl ⟨rfl, le_rfl, rfl⟩
  | skip =>
    simp only [Protocol.step, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact Or.inl ⟨rfl, le_rfl, rfl⟩

/-- A message in transit stays in transit unless it is received or its (crashed) sender's message
is dropped. -/
lemma mem_net_step {C C' : Config P L M} {s : Step P A M Act} {ℓ : Option (Label P A)}
    (h : Pr.step C s = some (C', ℓ)) {x : P × P × M} (hx : x ∈ C.net)
    (hs : x.1 ∉ C.crashed) (hr : s ≠ .recv x.1 x.2.1 x.2.2) : x ∈ C'.net := by
  obtain ⟨src, dst, m⟩ := x
  cases s with
  | inv p o =>
    simp only [Protocol.step] at h
    split_ifs at h
    obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at hy
    rw [← hy.1]
    exact Multiset.mem_add.2 (Or.inl hx)
  | internal p a =>
    simp only [Protocol.step] at h
    split_ifs at h
    obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at hy
    rw [← hy.1]
    exact Multiset.mem_add.2 (Or.inl hx)
  | recv src' dst' m' =>
    simp only [Protocol.step] at h
    split_ifs at h
    obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at hy
    rw [← hy.1]
    refine Multiset.mem_add.2 (Or.inl ?_)
    have hne : (src, dst, m) ≠ (src', dst', m') := by
      rintro ⟨⟩; exact hr rfl
    exact (Multiset.mem_erase_of_ne hne).2 hx
  | drop src' dst' m' =>
    simp only [Protocol.step] at h
    split_ifs at h with hd
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    have hne : (src, dst, m) ≠ (src', dst', m') := by
      rintro ⟨⟩; exact hs hd.1
    exact (Multiset.mem_erase_of_ne hne).2 hx
  | crash p =>
    simp only [Protocol.step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hx
  | skip =>
    simp only [Protocol.step, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hx

namespace Exec

variable (e : Pr.Exec)

/-- **Reliable channels.** A message between two correct processes that is in transit at time
`a` is eventually received, provided its reception is always enabled. -/
lemma eventually_recv (hf : e.Fair) {src dst : P} {m : M} (hsrc : e.Correct src)
    (hdst : e.Correct dst) (hen : ∀ l, (Pr.receive dst src m l).isSome) {a : ℕ}
    (ha : (src, dst, m) ∈ (e.cfg a).net) : ∃ t ≥ a, e.stp t = .recv src dst m := by
  by_contra hcon
  push Not at hcon
  have hin : ∀ t ≥ a, (src, dst, m) ∈ (e.cfg t).net := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ha
    | succ t ht ih => exact mem_net_step (e.step t) ih (hsrc t) (hcon t ht)
  obtain ⟨t, ht, hst⟩ := hf (.recv src dst m) dst rfl hdst a (fun t ht => by
    have h1 := hin t ht
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hen ((e.cfg t).loc dst))
    simp [Protocol.Enabled, Protocol.step, hdst t, h1, hx])
  exact hcon t ht hst

/-- Every message ever sent was in transit right after some step. -/
lemma exists_net_of_sent {x : P × P × M} {t : ℕ} (hx : x ∈ (e.cfg t).sent) :
    ∃ t' < t, x ∈ (e.cfg (t' + 1)).net := by
  induction t with
  | zero => simp [e.init, Protocol.initCfg] at hx
  | succ t ih =>
    rcases step_shape (e.step t) with ⟨h1, -, -⟩ | ⟨p, l, out, net, -, h⟩
    · rw [h1] at hx
      obtain ⟨t', ht', h'⟩ := ih hx
      exact ⟨t', by omega, h'⟩
    · rw [h] at hx
      simp only [Config.apply, Multiset.mem_add] at hx
      rcases hx with hx | hx
      · obtain ⟨t', ht', h'⟩ := ih hx
        exact ⟨t', by omega, h'⟩
      · refine ⟨t, by omega, ?_⟩
        rw [h]
        exact Multiset.mem_add.2 (Or.inr hx)

/-- Messages in transit have been sent. -/
lemma net_sub_sent (t : ℕ) {x : P × P × M} (hx : x ∈ (e.cfg t).net) : x ∈ (e.cfg t).sent := by
  induction t generalizing x with
  | zero => simp [e.init, Protocol.initCfg] at hx
  | succ t ih =>
    rcases step_shape (e.step t) with ⟨h1, h2, -⟩ | ⟨p, l, out, net, hle, h⟩
    · rw [h1]; exact ih (Multiset.mem_of_le h2 hx)
    · rw [h] at hx ⊢
      simp only [Config.apply, Multiset.mem_add] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ih (Multiset.mem_of_le hle hx))
      · exact Or.inr hx

lemma sent_mono {a b : ℕ} (hab : a ≤ b) : (e.cfg a).sent ≤ (e.cfg b).sent := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
    refine ih.trans ?_
    rcases step_shape (e.step b) with ⟨h1, -, -⟩ | ⟨p, l, out, net, -, h⟩
    · rw [h1]
    · rw [h]; exact Multiset.le_add_right _ _

lemma resps_le {a b : ℕ} (hab : a ≤ b) (p : P) :
    (respsOf (e.hist a) p).length ≤ (respsOf (e.hist b) p).length := by
  obtain ⟨β, hβ⟩ := e.hist_prefix hab
  rw [hβ, respsOf_append, List.length_append]; omega

lemma ops_le {a b : ℕ} (hab : a ≤ b) (p : P) :
    (opsOf (e.hist a) p).length ≤ (opsOf (e.hist b) p).length := by
  obtain ⟨β, hβ⟩ := e.hist_prefix hab
  rw [hβ, opsOf_append, List.length_append]; omega

end Exec

end Generic

/-! ## Transitions of `proto` -/

section Proto

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]
variable {Vr : Variant} {next : W → T → T} {v₀ : V}

/-- Configurations of `proto`. -/
abbrev Cfg (W R S T V : Type) := Config (Node W R S) (Loc W R S T V) (Msg R T V)

variable {C C' : Cfg W R S T V} {ℓ : Option (Label (Node W R S) (register V v₀))}
  {s : Step (Node W R S) (register V v₀) (Msg R T V) Empty}

/-- The three kinds of steps: steps without local transition, invocations and receptions. -/
lemma step_cases (h : (proto Vr next v₀).step C s = some (C', ℓ)) :
    (C'.loc = C.loc ∧ C'.sent = C.sent ∧ C'.net ≤ C.net ∧ ℓ = none ∧
      ∀ src dst m, s ≠ .recv src dst m) ∨
    (∃ p o l out, s = .inv p o ∧ p ∉ C.crashed ∧ ℓ = some (.inv p o) ∧
      (proto Vr next v₀).invoke p o (C.loc p) = some (l, out) ∧ C' = C.apply p l out C.net) ∨
    (∃ src dst m l out r, s = .recv src dst m ∧ dst ∉ C.crashed ∧ (src, dst, m) ∈ C.net ∧
      (proto Vr next v₀).receive dst src m (C.loc dst) = some (l, out, r) ∧
      C' = C.apply dst l out (C.net.erase (src, dst, m)) ∧ ℓ = r.map (Label.ret dst)) := by
  cases s with
  | inv p o =>
    simp only [Protocol.step] at h
    split_ifs at h with hp
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨l, out⟩, h1, rfl, rfl⟩ := h
    exact Or.inr (Or.inl ⟨p, o, l, out, rfl, hp, rfl, h1, rfl⟩)
  | internal p a => exact a.elim
  | recv src dst m =>
    simp only [Protocol.step] at h
    split_ifs at h with hp
    push Not at hp
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨l, out, r⟩, h1, rfl, rfl⟩ := h
    exact Or.inr (Or.inr ⟨src, dst, m, l, out, r, rfl, hp.1, hp.2, h1, rfl, rfl⟩)
  | drop src dst m =>
    simp only [Protocol.step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, Multiset.erase_le _ _, rfl, by simp⟩
  | crash p =>
    simp only [Protocol.step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, le_rfl, rfl, by simp⟩
  | skip =>
    simp only [Protocol.step, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, le_rfl, rfl, by simp⟩

lemma receive_isSome (p q : Node W R S) (m : Msg R T V) (L : Loc W R S T V) :
    ((proto Vr next v₀).receive p q m L).isSome := by
  cases p <;> cases q <;> simp [proto]

lemma invoke_wr {w : W} {o : RWOp V} {L l : Loc W R S T V} {out : Multiset (Node W R S × Msg R T V)}
    (h : (proto Vr next v₀).invoke (.wr w) o L = some (l, out)) :
    ∃ val, o = .write val ∧ wInvoke Vr next w val L.w = some (l.w, out) ∧ l.r = L.r ∧
      l.s = L.s := by
  cases o with
  | read => simp [proto] at h
  | write val =>
    simp only [proto, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨x, h1, rfl, rfl⟩ := h
    exact ⟨val, rfl, h1, rfl, rfl⟩

lemma invoke_rd {r : R} {o : RWOp V} {L l : Loc W R S T V} {out : Multiset (Node W R S × Msg R T V)}
    (h : (proto Vr next v₀).invoke (.rd r) o L = some (l, out)) :
    o = .read ∧ rInvoke L.r = some (l.r, out) ∧ l.w = L.w ∧ l.s = L.s := by
  cases o with
  | write val => simp [proto] at h
  | read =>
    simp only [proto, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨x, h1, rfl, rfl⟩ := h
    exact ⟨rfl, h1, rfl, rfl⟩

lemma invoke_sv {sv : S} {o : RWOp V} {L : Loc W R S T V} :
    (proto Vr next v₀).invoke (.sv sv) o L = none := by
  cases o <;> rfl

lemma receive_wr {w : W} {src : Node W R S} {m : Msg R T V} {L l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)} {r : Option V}
    (h : (proto Vr next v₀).receive (.wr w) src m L = some (l, out, r)) :
    l.r = L.r ∧ l.s = L.s ∧
      ((∃ s, src = .sv s ∧ (l.w, out, r) = wWait next w (wRecord Vr s m L.w)) ∨
        (l = L ∧ out = 0 ∧ r = none)) := by
  cases src with
  | sv s =>
    simp only [proto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, Or.inl ⟨s, rfl, rfl⟩⟩
  | wr _ =>
    simp only [proto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩
  | rd _ =>
    simp only [proto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩

lemma receive_wr_sv {w : W} {s : S} {m : Msg R T V} {L l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)} {r : Option V}
    (h : (proto Vr next v₀).receive (.wr w) (.sv s) m L = some (l, out, r)) :
    l.r = L.r ∧ l.s = L.s ∧ (l.w, out, r) = wWait next w (wRecord Vr s m L.w) := by
  simp only [proto, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

lemma receive_rd_sv {rr : R} {s : S} {m : Msg R T V} {L l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)} {r : Option V}
    (h : (proto Vr next v₀).receive (.rd rr) (.sv s) m L = some (l, out, r)) :
    l.w = L.w ∧ l.s = L.s ∧ out = 0 ∧ (l.r, r) = rWait Vr v₀ (rRecord Vr s m L.r) := by
  simp only [proto, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl⟩

lemma receive_rd {rr : R} {src : Node W R S} {m : Msg R T V} {L l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)} {r : Option V}
    (h : (proto Vr next v₀).receive (.rd rr) src m L = some (l, out, r)) :
    l.w = L.w ∧ l.s = L.s ∧ out = 0 ∧
      ((∃ s, src = .sv s ∧ (l.r, r) = rWait Vr v₀ (rRecord Vr s m L.r)) ∨
        (l = L ∧ r = none)) := by
  cases src with
  | sv s =>
    simp only [proto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, Or.inl ⟨s, rfl, rfl⟩⟩
  | wr _ =>
    simp only [proto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
  | rd _ =>
    simp only [proto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩

lemma receive_sv {sv : S} {src : Node W R S} {m : Msg R T V} {L l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)} {r : Option V}
    (h : (proto Vr next v₀).receive (.sv sv) src m L = some (l, out, r)) :
    l.w = L.w ∧ l.r = L.r ∧ r = none ∧ (l.s, out) = sRecv Vr src m L.s := by
  simp only [proto, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Local transitions -/

section Local

variable {w : W} {val : V} {L l : WLoc S T V} {out : Multiset (Node W R S × Msg R T V)}

lemma wInvoke_spec (h : wInvoke Vr next w val L = some (l, out)) :
    L.phase = .idle ∧
      ((Vr.mw = true ∧ l = { L with op := L.op + 1, ack := [], phase := .disc val } ∧
          out = bcast (.discover (L.op + 1))) ∨
        (Vr.mw = false ∧ l = { L with tag := next w L.tag, val := val, ack := [], phase := .upd } ∧
          out = bcast (.writeRequest (next w L.tag) val 0))) := by
  unfold wInvoke at h
  split at h
  · rename_i hph
    cases hmw : Vr.mw <;> simp only [hmw, ite_true, Bool.false_eq_true, ite_false,
      Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
    · exact ⟨hph, Or.inr ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨hph, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · simp at h

lemma length_insert_le {α : Type} [DecidableEq α] (x : α) (l : List α) :
    (l.insert x).length ≤ l.length + 1 := by
  by_cases h : x ∈ l
  · simp [List.insert_of_mem h]
  · simp [List.insert_of_not_mem h]

lemma wRecord_spec (s : S) (m : Msg R T V) (L : WLoc S T V) :
    ∃ ack', wRecord Vr s m L = { L with ack := ack' } ∧ L.ack ⊆ ack' ∧
      ack'.length ≤ L.ack.length + 1 := by
  have hins : ∀ x : S × T × V, L.ack ⊆ L.ack.insert x ∧
      (L.ack.insert x).length ≤ L.ack.length + 1 := fun x =>
    ⟨List.subset_insert _ _, length_insert_le _ _⟩
  unfold wRecord
  split <;> (try split_ifs) <;>
    first | exact ⟨_, rfl, hins _⟩ | exact ⟨L.ack, rfl, List.Subset.refl _, by omega⟩

lemma wWait_spec (w : W) (l : WLoc S T V) :
    ((l.ack.length ≠ maj S ∨ l.phase = .idle) ∧
        wWait (R := R) next w l = (l, 0, none)) ∨
      (l.ack.length = maj S ∧ ∃ val, l.phase = .disc val ∧
        wWait (R := R) next w l =
          ({ l with tag := next w (maxTag l.ack), val := val, op := l.op + 1, ack := [],
                    phase := .upd },
          bcast (.writeRequest (next w (maxTag l.ack)) val (l.op + 1)), none)) ∨
      (l.ack.length = maj S ∧ l.phase = .upd ∧
        wWait (R := R) next w l = ({ l with phase := .idle }, 0, some l.val)) := by
  unfold wWait
  split_ifs with h
  · cases hph : l.phase with
    | idle => exact Or.inl ⟨Or.inr rfl, rfl⟩
    | disc val => exact Or.inr (Or.inl ⟨h, val, rfl, rfl⟩)
    | upd => exact Or.inr (Or.inr ⟨h, rfl, rfl⟩)
  · exact Or.inl ⟨Or.inl h, rfl⟩

variable {r : R} {L : RLoc S T V} {l : RLoc S T V}

lemma rInvoke_spec (h : rInvoke L = some (l, out)) :
    L.pending = false ∧ l = ⟨L.op + 1, true, [], []⟩ ∧ out = bcast (.readRequest (L.op + 1)) := by
  unfold rInvoke at h
  split_ifs at h with hp
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [Bool.not_eq_true] at hp
  exact ⟨hp, rfl, rfl⟩

lemma rRecord_spec (s : S) (m : Msg R T V) (L : RLoc S T V) :
    ∃ ack' relay', rRecord Vr s m L = { L with ack := ack', relay := relay' } ∧ L.ack ⊆ ack' ∧
      ack'.length ≤ L.ack.length + 1 := by
  unfold rRecord
  split
  · split_ifs
    · exact ⟨_, _, rfl, List.subset_insert _ _, length_insert_le _ _⟩
    · exact ⟨L.ack, L.relay, rfl, List.Subset.refl _, by omega⟩
  · split_ifs
    · exact ⟨L.ack, _, rfl, List.Subset.refl _, by omega⟩
    · exact ⟨L.ack, L.relay, rfl, List.Subset.refl _, by omega⟩
  · exact ⟨L.ack, L.relay, rfl, List.Subset.refl _, by omega⟩

lemma rRecord_readAck (s : S) (t : T) (v : V) (L : RLoc S T V) :
    (s, t, v) ∈ (rRecord Vr s (.readAck t v L.op : Msg R T V) L).ack := by
  simp [rRecord, List.mem_insert_iff]

lemma rWait_spec (l : RLoc S T V) :
    ((l.pending = true → l.ack.length ≠ maj S) ∧ rWait Vr v₀ l = (l, none)) ∨
      (l.pending = true ∧ (rWait Vr v₀ l).1 = { l with pending := false } ∧
        (rWait Vr v₀ l).2.isSome) := by
  unfold rWait
  split_ifs with h1 h2 h3
  · exact Or.inr ⟨h1, rfl, rfl⟩
  · split
    · exact Or.inr ⟨h1, rfl, rfl⟩
    · exact Or.inl ⟨fun _ => h2, rfl⟩
  · exact Or.inl ⟨fun _ => h2, rfl⟩
  · exact Or.inl ⟨fun h => absurd h h1, rfl⟩

/-! ### Servers -/

variable {sj : S} {t : T} {v : V} {k : ℕ} {l : SLoc W R S T V}

lemma sRelay_ops (r' : R) :
    (sRelay Vr sj t v r k l).1.ops r' = if r' = r then max (l.ops r) k else l.ops r' := by
  simp only [sRelay]
  split_ifs <;> simp_all <;> omega

lemma sRelay_ne {r' : R} (hr : r' ≠ r) :
    (sRelay Vr sj t v r k l).1.relays r' = l.relays r' ∧
      (sRelay Vr sj t v r k l).1.got r' = l.got r' := by
  simp only [sRelay]
  split_ifs <;> simp_all

lemma sRelay_lt (hk : l.ops r < k) :
    (sRelay Vr sj t v r k l).1.relays r = 1 ∧ (sRelay Vr sj t v r k l).1.got r = {sj} := by
  simp only [sRelay]
  split_ifs <;> simp_all

lemma sRelay_eq (hk : l.ops r = k) :
    (sRelay Vr sj t v r k l).1.relays r = l.relays r + 1 ∧
      (sRelay Vr sj t v r k l).1.got r = insert sj (l.got r) := by
  simp only [sRelay]
  split_ifs <;> simp_all

lemma sRelay_gt (hk : k < l.ops r) :
    (sRelay Vr sj t v r k l).1.relays r = l.relays r ∧
      (sRelay Vr sj t v r k l).1.got r = l.got r := by
  simp only [sRelay]
  split_ifs <;> simp_all <;> omega

lemma sRelay_tag : (sRelay Vr sj t v r k l).1.tag = if l.tag < t then t else l.tag := by
  simp only [sRelay]
  split_ifs <;> simp_all

lemma sRelay_out_mem {x : Node W R S × Msg R T V} (hx : x ∈ (sRelay Vr sj t v r k l).2) :
    ∃ t' v', x = (.rd r, .readAck t' v' k) := by
  simp only [sRelay] at hx
  split_ifs at hx <;> simp_all

lemma sRelay_out_maj (h1 : (sRelay Vr sj t v r k l).1.ops r = k)
    (h2 : (sRelay Vr sj t v r k l).1.relays r = maj S) :
    ∃ t' v', ((.rd r, .readAck t' v' k) : Node W R S × Msg R T V) ∈ (sRelay Vr sj t v r k l).2 := by
  simp only [sRelay] at h1 h2 ⊢
  split_ifs at h1 h2 ⊢ <;> simp_all

lemma mem_bcast {m : Msg R T V} {x : Node W R S × Msg R T V} :
    x ∈ (bcast m : Multiset (Node W R S × Msg R T V)) ↔ ∃ s, x = (.sv s, m) := by
  simp [bcast, eq_comm]

lemma mem_outMsgs {p : Node W R S} {out : Multiset (Node W R S × Msg R T V)}
    {x : Node W R S × Node W R S × Msg R T V} :
    x ∈ outMsgs p out ↔ x.1 = p ∧ (x.2.1, x.2.2) ∈ out := by
  obtain ⟨a, b, c⟩ := x
  simp only [outMsgs, Multiset.mem_map, Prod.exists]
  constructor
  · rintro ⟨b', c', h, h'⟩
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl⟩ := h'
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨b, c, h, rfl⟩

lemma sWrite_spec {w : W} {t : T} {v : V} {op : ℕ} {L : SLoc W R S T V} :
    (sWrite Vr w t v op L).1.ops = L.ops ∧ (sWrite Vr w t v op L).1.relays = L.relays ∧
      (sWrite Vr w t v op L).1.got = L.got ∧
      (sWrite Vr w t v op L).2 = {(.wr w, .writeAck (sWrite Vr w t v op L).1.tag
        (sWrite Vr w t v op L).1.val op)} ∧
      (Vr.mw = false → (sWrite Vr w t v op L).1.tag = if L.tag < t then t else L.tag) := by
  simp only [sWrite]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> simp_all

lemma sRecv_spec (src : Node W R S) (m : Msg R T V) (L : SLoc W R S T V) :
    (∃ r k, src = .rd r ∧ m = .readRequest k ∧ sRecv Vr src m L =
      (L, bcast (.readRelay L.tag L.val r k) +
        if Vr.fast then {(Node.rd r, Msg.readRelay L.tag L.val r k)} else 0)) ∨
    (∃ sj t v r k, src = .sv sj ∧ m = .readRelay t v r k ∧
      sRecv Vr src m L = sRelay Vr sj t v r k L) ∨
    (∃ w t v op, src = .wr w ∧ m = .writeRequest t v op ∧
      sRecv Vr src m L = sWrite Vr w t v op L) ∨
    (∃ w op, src = .wr w ∧ m = .discover op ∧
      sRecv Vr src m L = (L, {(Node.wr w, Msg.discoverAck L.tag L.val op)})) ∨
    sRecv Vr src m L = (L, 0) := by
  cases src <;> cases m <;> simp [sRecv]

end Local

end Proto

end Podc.OhRAM.Liveness
