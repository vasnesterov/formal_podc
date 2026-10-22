import Papers.PODC2020.FastMWMRImpossibility.Model
import Cslib.Computability.Distributed.SharedMemory.LinPoints

/-!
# Sanity check: with `t = 0`, a single server is a correct fast-write register

Theorem 1 (`Podc.FastMWMR.theorem_1`) says that for `t ≥ 1` no W1R2 algorithm implements an
atomic multi-writer register. This file shows that the hypothesis `t ≥ 1` is needed and that the
model `W1R2Alg.protocol` is not degenerate: with `n = 1` server and `t = 0` (clients wait for the
reply of the single server), the obvious algorithm is linearizable, for any sets of writers and
readers.

The algorithm `singleServer W R V v₀`:
* messages `Option V` (`some v`: write `v`; `none`: read), replies `V`, no client state;
* the server replies with the current value of the register (the value of the last `some v` it
  processed, `v₀` if none), *before* processing the new message;
* a write sends `some v`; a read sends `none` in both round-trips and returns the reply of its
  first round-trip.

**Linearization points**: the moment the server processes a write request, resp. the first-round
request of a read. The proof (`single_server_linearizable`) is an invariant (`Inv`) over all
reachable configurations — with arbitrary crashes, message losses from crashed senders, and
interleavings — which carries a ghost linearization `L` (the operations in server-processing order)
and relates it to the server log, the client states and the messages in transit.
-/

set_option linter.unusedSectionVars false

namespace Podc.FastMWMR

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R V : Type}

/-- The current value of the single server's register: the last value written in `log`. -/
def lastVal (v₀ : V) (log : List (Node 1 W R × Option V)) : V :=
  log.foldl (fun acc x => x.2.getD acc) v₀

@[simp] lemma lastVal_concat (v₀ : V) (log : List (Node 1 W R × Option V))
    (x : Node 1 W R × Option V) : lastVal v₀ (log ++ [x]) = x.2.getD (lastVal v₀ log) := by
  simp [lastVal]

/-- A single-server fast-write (W1R2) algorithm: the server stores the register, a write is one
round-trip, a read is two round-trips (the second one is a dummy) and returns the value of the
first one. -/
def singleServer (W R V : Type) (v₀ : V) : W1R2Alg 1 W R V (Option V) V Unit Unit where
  reply _ log _ _ := lastVal v₀ log
  initW _ := ()
  wMsg _ _ v _ := some v
  wEnd _ _ _ _ := ()
  initR _ := ()
  rMsg1 _ _ _ := none
  rMsg2 _ _ _ _ := none
  rEnd _ _ V₁ _ := ((V₁.head?.map Prod.snd).getD v₀, ())

variable [DecidableEq W] [DecidableEq R] [DecidableEq V]

namespace SingleServer

/-- Local invariant of writer `w`: its operation counter `k` matches the history, and a pending
write that got its reply has been linearized. -/
def WrOK {v₀ : V} (h : List (Label (Node 1 W R) (register V v₀)))
    (L : List (OpId (Node 1 W R) × RWOp V)) (w : W) :
    Loc 1 W R V (Option V) V Unit Unit → Prop
  | .wr _ k none => (opsOf h (.wr w)).length = k ∧ (respsOf h (.wr w)).length = k
  | .wr _ k (some (v, acks)) => (opsOf h (.wr w)).length = k ∧
      (respsOf h (.wr w)).length + 1 = k ∧ opOf h (.wr w, k - 1) = some (RWOp.write v) ∧
      (acks ≠ [] → (Node.wr w, k - 1) ∈ L.map Prod.fst)
  | _ => False

/-- Local invariant of reader `r`: its operation counter `k` matches the history, and the first
first-round reply is the response of the read in the linearization. -/
def RdOK {v₀ : V} (h : List (Label (Node 1 W R) (register V v₀)))
    (L : List (OpId (Node 1 W R) × RWOp V)) (r : R) :
    Loc 1 W R V (Option V) V Unit Unit → Prop
  | .rd _ k .idle => (opsOf h (.rd r)).length = k ∧ (respsOf h (.rd r)).length = k
  | .rd _ k (.one acks) => (opsOf h (.rd r)).length = k ∧ (respsOf h (.rd r)).length + 1 = k ∧
      ∀ a ∈ acks.head?, (register V v₀).respIn v₀ L (.rd r, k - 1) = some a.2
  | .rd _ k (.two V₁ _) => (opsOf h (.rd r)).length = k ∧ (respsOf h (.rd r)).length + 1 = k ∧
      ∃ a ∈ V₁.head?, (register V v₀).respIn v₀ L (.rd r, k - 1) = some a.2
  | _ => False

/-- Invariant of a message in transit. A request that is a linearization point (a write, or the
first round-trip of a read) belongs to an invoked operation that is not linearized yet; a reply
to such a request belongs to a linearized operation (for reads: with the reply as response). -/
def MsgOK {v₀ : V} (h : List (Label (Node 1 W R) (register V v₀)))
    (L : List (OpId (Node 1 W R) × RWOp V)) :
    Node 1 W R × Node 1 W R × Pkt (Option V) V → Prop
  | (.wr w, .srv _, .req k i m) => 1 ≤ k ∧ i = 1 ∧ ∃ v, m = some v ∧
      opOf h (.wr w, k - 1) = some (RWOp.write v) ∧ (Node.wr w, k - 1) ∉ L.map Prod.fst
  | (.rd r, .srv _, .req k i m) => m = none ∧ (i = 1 → 1 ≤ k ∧
      opOf h (.rd r, k - 1) = some RWOp.read ∧ (Node.rd r, k - 1) ∉ L.map Prod.fst)
  | (.srv _, .wr w, .rep k i _) => i = 1 → (Node.wr w, k - 1) ∈ L.map Prod.fst
  | (.srv _, .rd r, .rep k i v) => i = 1 → (register V v₀).respIn v₀ L (.rd r, k - 1) = some v
  | _ => False

/-- The invariant: `L` is a linearization of the history, the server's register is the state
after `L`, and the local and message invariants hold. -/
structure Inv {v₀ : V}
    (C : Config (Node 1 W R) (Loc 1 W R V (Option V) V Unit Unit) (Pkt (Option V) V))
    (h : List (Label (Node 1 W R) (register V v₀))) (L : List (OpId (Node 1 W R) × RWOp V)) :
    Prop where
  lin : IsLinearization h L
  srv : ∃ log, C.loc (.srv 0) = .srv log ∧
    lastVal v₀ log = (register V v₀).runOps v₀ (L.map Prod.snd)
  wr : ∀ w, WrOK h L w (C.loc (.wr w))
  rd : ∀ r, RdOK h L r (C.loc (.rd r))
  net : ∀ x ∈ C.net, MsgOK h L x
  uniq : ∀ c s k m, C.net.count (c, Node.srv s, Pkt.req k 1 m) ≤ 1

variable {v₀ : V}

lemma bcast_one (k i : ℕ) (f : Fin 1 → Option V) :
    (bcast k i f : Multiset (Node 1 W R × Pkt (Option V) V)) = {(.srv 0, .req k i (f 0))} := by
  simp [bcast, List.finRange_succ]

lemma invoke_cases {p : Node 1 W R} {o : RWOp V} {l l' : Loc 1 W R V (Option V) V Unit Unit}
    {out : Multiset (Node 1 W R × Pkt (Option V) V)}
    (hi : ((singleServer W R V v₀).protocol 0 v₀).invoke p o l = some (l', out)) :
    (∃ w v k, p = .wr w ∧ o = .write v ∧ l = .wr () k none ∧ l' = .wr () (k + 1) (some (v, [])) ∧
      out = {(.srv 0, .req (k + 1) 1 (some v))}) ∨
    (∃ r k, p = .rd r ∧ o = .read ∧ l = .rd () k .idle ∧ l' = .rd () (k + 1) (.one []) ∧
      out = {(.srv 0, .req (k + 1) 1 none)}) := by
  rcases p with s | w | r <;> rcases o with _ | v <;>
    rcases l with log | ⟨st, k, _ | ⟨v', acks⟩⟩ | ⟨st, k, _ | acks | ⟨V₁, acks⟩⟩ <;>
    simp [W1R2Alg.protocol] at hi
  · obtain ⟨rfl, rfl⟩ := hi
    left; exact ⟨w, v, k, rfl, rfl, rfl, rfl, by simp [bcast_one, singleServer]⟩
  · obtain ⟨rfl, rfl⟩ := hi
    right; exact ⟨r, k, rfl, rfl, rfl, rfl, by simp [bcast_one, singleServer]⟩

lemma internal_cases {p : Node 1 W R} {a : Unit} {l l' : Loc 1 W R V (Option V) V Unit Unit}
    {out : Multiset (Node 1 W R × Pkt (Option V) V)} {res : Option V}
    (hi : ((singleServer W R V v₀).protocol 0 v₀).internal p a l = some (l', out, res)) :
    (∃ w k v acks, p = .wr w ∧ l = .wr () k (some (v, acks)) ∧ acks ≠ [] ∧
      l' = .wr () k none ∧ out = 0 ∧ res = some v) ∨
    (∃ r k acks, p = .rd r ∧ l = .rd () k (.one acks) ∧ acks ≠ [] ∧
      l' = .rd () k (.two acks []) ∧ out = {(.srv 0, .req k 2 none)} ∧ res = none) ∨
    (∃ r k V₁ acks, p = .rd r ∧ l = .rd () k (.two V₁ acks) ∧ l' = .rd () k .idle ∧ out = 0 ∧
      res = some ((V₁.head?.map Prod.snd).getD v₀)) := by
  rcases p with s | w | r <;>
    rcases l with log | ⟨st, k, _ | ⟨v', acks⟩⟩ | ⟨st, k, _ | acks | ⟨V₁, acks⟩⟩ <;>
    simp [W1R2Alg.protocol] at hi
  · obtain ⟨hlen, rfl, rfl, rfl⟩ := hi
    left; exact ⟨w, k, v', acks, rfl, rfl, by rintro rfl; simp at hlen, rfl, rfl, rfl⟩
  · obtain ⟨hlen, rfl, rfl, rfl⟩ := hi
    right; left
    exact ⟨r, k, acks, rfl, rfl, by rintro rfl; simp at hlen, rfl, by simp [bcast_one, singleServer], rfl⟩
  · obtain ⟨hlen, rfl, rfl, rfl⟩ := hi
    right; right; exact ⟨r, k, V₁, acks, rfl, rfl, rfl, rfl, by simp [singleServer]⟩

lemma receive_cases {p q : Node 1 W R} {m : Pkt (Option V) V}
    {l l' : Loc 1 W R V (Option V) V Unit Unit}
    {out : Multiset (Node 1 W R × Pkt (Option V) V)} {res : Option V}
    (hi : ((singleServer W R V v₀).protocol 0 v₀).receive p q m l = some (l', out, res)) :
    res = none ∧
    ((∃ s log k i msg, p = .srv s ∧ m = .req k i msg ∧ l = .srv log ∧ l' = .srv (log ++ [(q, msg)]) ∧
      out = {(q, .rep k i (lastVal v₀ log))}) ∨
    (∃ s k i v, (∀ s', p ≠ .srv s') ∧ q = .srv s ∧ m = .rep k i v ∧ l' = l.absorb s k i v ∧
      out = 0) ∨
    (l' = l ∧ out = 0)) := by
  simp only [W1R2Alg.protocol] at hi
  split at hi
  · simp only [Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl⟩ := hi
    exact ⟨rfl, Or.inl ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, by simp [singleServer]⟩⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl⟩ := hi
    exact ⟨rfl, Or.inr (Or.inl ⟨_, _, _, _, by simp, rfl, rfl, rfl, rfl⟩)⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl⟩ := hi
    exact ⟨rfl, Or.inr (Or.inl ⟨_, _, _, _, by simp, rfl, rfl, rfl, rfl⟩)⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl⟩ := hi
    exact ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

section Frame

variable {h h' : List (Label (Node 1 W R) (register V v₀))}
  {L : List (OpId (Node 1 W R) × RWOp V)}

/-- In a linearization, a linearized write gets its value as response. -/
lemma respIn_write (hL : IsLinearization h L) {x : OpId (Node 1 W R)} {v : V}
    (hx : x ∈ L.map Prod.fst) (ho : opOf h x = some (RWOp.write v)) :
    (register V v₀).respIn v₀ L x = some v := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1
    ((ObjSpec.respIn_isSome_iff (A := register V v₀) (q := v₀)).2 hx)
  obtain ⟨L₁, L₂, o, hs, hr'⟩ := ObjSpec.exists_split_of_respIn_eq_some hr
  have := hL.op_eq (x, o) (by rw [hs]; simp)
  rw [ho] at this
  cases this
  rw [hr]
  simpa using hr'.symm

/-- An operation that is not invoked yet is not linearized. -/
lemma not_mem_of_len (hL : IsLinearization h L) {c : Node 1 W R} {k : ℕ}
    (hk : (opsOf h c).length ≤ k) : (c, k) ∉ L.map Prod.fst := by
  intro hm
  obtain ⟨⟨x, o⟩, hy, rfl⟩ := List.mem_map.1 hm
  have := hL.op_eq _ hy
  simp only [opOf] at this
  rw [List.getElem?_eq_none hk] at this
  cases this

lemma WrOK.mono {w : W} {l : Loc 1 W R V (Option V) V Unit Unit} (hw : WrOK h L w l)
    (hops : opsOf h' (.wr w) = opsOf h (.wr w)) (hresps : respsOf h' (.wr w) = respsOf h (.wr w))
    (M : List (OpId (Node 1 W R) × RWOp V)) : WrOK h' (L ++ M) w l := by
  rcases l with log | ⟨st, k, _ | ⟨v, acks⟩⟩ | ⟨st, k, ph⟩ <;>
    simp only [WrOK, opOf, hops, hresps] at hw ⊢
  · exact hw
  · exact ⟨hw.1, hw.2.1, hw.2.2.1, fun hne => by
      rw [List.map_append]; exact List.mem_append_left _ (hw.2.2.2 hne)⟩

lemma RdOK.mono {r : R} {l : Loc 1 W R V (Option V) V Unit Unit} (hr : RdOK h L r l)
    (hops : opsOf h' (.rd r) = opsOf h (.rd r)) (hresps : respsOf h' (.rd r) = respsOf h (.rd r))
    (M : List (OpId (Node 1 W R) × RWOp V)) : RdOK h' (L ++ M) r l := by
  rcases l with log | ⟨st, k, cur⟩ | ⟨st, k, _ | acks | ⟨V₁, acks⟩⟩ <;>
    simp only [RdOK, hops, hresps] at hr ⊢
  · exact hr
  · exact ⟨hr.1, hr.2.1, fun a ha => ObjSpec.respIn_append_of_eq_some (hr.2.2 a ha) M⟩
  · obtain ⟨h1, h2, a, ha, h3⟩ := hr
    exact ⟨h1, h2, a, ha, ObjSpec.respIn_append_of_eq_some h3 M⟩

lemma MsgOK.mono_hist {x : Node 1 W R × Node 1 W R × Pkt (Option V) V} (hx : MsgOK h L x)
    (hop : ∀ y o, opOf h y = some o → opOf h' y = some o) : MsgOK h' L x := by
  obtain ⟨src, dst, pk⟩ := x
  rcases src with s | w | r <;> rcases dst with s' | w' | r' <;> rcases pk with ⟨k, i, m⟩ | ⟨k, i, v⟩ <;>
    simp only [MsgOK] at hx ⊢
  all_goals first
    | exact hx
    | (obtain ⟨h1, h2, v, h3, h4, h5⟩ := hx; exact ⟨h1, h2, v, h3, hop _ _ h4, h5⟩)
    | exact ⟨hx.1, fun hi => ⟨(hx.2 hi).1, hop _ _ (hx.2 hi).2.1, (hx.2 hi).2.2⟩⟩

lemma MsgOK.append {x : Node 1 W R × Node 1 W R × Pkt (Option V) V} (hx : MsgOK h L x)
    (M : List (OpId (Node 1 W R) × RWOp V))
    (hM : ∀ c s k m, x = (c, .srv s, .req k 1 m) → (c, k - 1) ∉ M.map Prod.fst) :
    MsgOK h (L ++ M) x := by
  obtain ⟨src, dst, pk⟩ := x
  rcases src with s | w | r <;> rcases dst with s' | w' | r' <;> rcases pk with ⟨k, i, m⟩ | ⟨k, i, v⟩ <;>
    simp only [MsgOK, List.map_append, List.mem_append, not_or] at hx ⊢
  all_goals first
    | exact hx
    | (obtain ⟨h1, rfl, v, h3, h4, h5⟩ := hx; exact ⟨h1, rfl, v, h3, h4, h5, hM _ _ _ _ rfl⟩)
    | (refine ⟨hx.1, fun hi => ?_⟩
       subst hi
       exact ⟨(hx.2 rfl).1, (hx.2 rfl).2.1, (hx.2 rfl).2.2, hM _ _ _ _ rfl⟩)
    | exact fun hi => Or.inl (hx hi)
    | exact fun hi => ObjSpec.respIn_append_of_eq_some (hx hi) M

/-- Two linearizing requests of the same operation are the same message. -/
lemma MsgOK.req_eq {c : Node 1 W R} {s s' : Fin 1} {k k' : ℕ} {m m' : Option V}
    (h1 : MsgOK h L (c, .srv s, .req k 1 m)) (h2 : MsgOK h L (c, .srv s', .req k' 1 m'))
    (hk : k - 1 = k' - 1) :
    ((c, .srv s, .req k 1 m) : Node 1 W R × Node 1 W R × Pkt (Option V) V) =
      (c, .srv s', .req k' 1 m') := by
  have hs : s = s' := Subsingleton.elim _ _
  subst hs
  rcases c with s₀ | w | r <;> simp only [MsgOK] at h1 h2
  · obtain ⟨hk1, -, v, rfl, ho, -⟩ := h1
    obtain ⟨hk2, -, v', rfl, ho', -⟩ := h2
    have : k = k' := by omega
    subst this
    rw [ho] at ho'
    cases ho'
    rfl
  · obtain ⟨rfl, h1⟩ := h1
    obtain ⟨rfl, h2⟩ := h2
    have : k = k' := by have := (h1 trivial).1; have := (h2 trivial).1; omega
    subst this
    rfl

end Frame

/-- Configurations of the single-server protocol. -/
abbrev SCfg (W R V : Type) :=
  Config (Node 1 W R) (Loc 1 W R V (Option V) V Unit Unit) (Pkt (Option V) V)

section Steps

variable {C : SCfg W R V} {h : List (Label (Node 1 W R) (register V v₀))}
  {L : List (OpId (Node 1 W R) × RWOp V)}

/-- Steps that do not touch the server, keep the local invariants, and only remove messages. -/
lemma Inv.of_loc_net (hI : Inv C h L) {C' : SCfg W R V}
    (hsrv : C'.loc (.srv 0) = C.loc (.srv 0))
    (hwr : ∀ w, WrOK h L w (C.loc (.wr w)) → WrOK h L w (C'.loc (.wr w)))
    (hrd : ∀ r, RdOK h L r (C.loc (.rd r)) → RdOK h L r (C'.loc (.rd r)))
    (hnet : C'.net ≤ C.net) : Inv C' h L where
  lin := hI.lin
  srv := by rw [hsrv]; exact hI.srv
  wr w := hwr w (hI.wr w)
  rd r := hrd r (hI.rd r)
  net x hx := hI.net x (Multiset.mem_of_le hnet hx)
  uniq c s k m := (Multiset.count_le_of_le _ hnet).trans (hI.uniq c s k m)

/-- A linearizing request is not in the network any more after it is received. -/
lemma Inv.not_mem_erase (hI : Inv C h L) {c : Node 1 W R} {s : Fin 1} {k : ℕ} {m : Option V} :
    ((c, .srv s, .req k 1 m) : Node 1 W R × Node 1 W R × Pkt (Option V) V) ∉
      C.net.erase (c, .srv s, .req k 1 m) := by
  intro hm
  have h1 := Multiset.count_pos.2 hm
  rw [Multiset.count_erase_self] at h1
  have := hI.uniq c s k m
  omega

/-- No request of a not-yet-invoked operation is in transit. -/
lemma Inv.not_mem_fresh (hI : Inv C h L) {c : Node 1 W R} {k : ℕ}
    (hk : (opsOf h c).length = k) (s : Fin 1) (m : Option V) :
    ((c, .srv s, .req (k + 1) 1 m) : Node 1 W R × Node 1 W R × Pkt (Option V) V) ∉ C.net := by
  intro hm
  have := hI.net _ hm
  have hnone : opOf h (c, k) = none := by
    simp only [opOf]; exact List.getElem?_eq_none (by omega)
  rcases c with s₀ | w | r <;> simp only [MsgOK] at this
  · obtain ⟨-, -, v, -, ho, -⟩ := this
    simp [hnone] at ho
  · have := (this.2 trivial).2.1
    simp [hnone] at this

lemma Inv.invoke (hI : Inv C h L) {p : Node 1 W R} {o : RWOp V}
    {l : Loc 1 W R V (Option V) V Unit Unit} {out : Multiset (Node 1 W R × Pkt (Option V) V)}
    (hi : ((singleServer W R V v₀).protocol 0 v₀).invoke p o (C.loc p) = some (l, out)) :
    Inv (C.apply p l out C.net) (h ++ [.inv p o]) L := by
  have hnet : ∀ x ∈ C.net, MsgOK (h ++ [.inv p o]) L x := fun x hx =>
    (hI.net x hx).mono_hist (fun y o hy => opOf_append_of_eq_some hy _)
  rcases invoke_cases hi with ⟨w, v, k, rfl, rfl, hl, rfl, rfl⟩ | ⟨r, k, rfl, rfl, hl, rfl, rfl⟩
  · have hw := hI.wr w
    rw [hl] at hw
    obtain ⟨hops, hresps⟩ := hw
    refine ⟨hI.lin.append_inv _ _, by simpa [Config.apply] using hI.srv, fun w' => ?_,
      fun r' => ?_, fun x hx => ?_, fun c s k' m => ?_⟩
    · by_cases hw' : w' = w
      · subst hw'
        simp only [Config.apply, Function.update_self, WrOK]
        refine ⟨by simp [hops], by simp [hresps], ?_,
          fun h => absurd rfl h⟩
        rw [opOf_concat_inv, ite_eq_left (by simp [hops])]
      · simp only [Config.apply, ne_eq, Node.wr.injEq, hw', not_false_eq_true,
          Function.update_of_ne]
        simpa using (hI.wr w').mono (opsOf_concat_of_ne (by simp [Ne.symm hw']))
          (respsOf_append_inv _ _ _ _) []
    · simp only [Config.apply, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne]
      simpa using (hI.rd r').mono (opsOf_concat_of_ne (by simp))
        (respsOf_append_inv _ _ _ _) []
    · simp only [Config.apply, outMsgs, Multiset.map_singleton, Multiset.mem_add,
        Multiset.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hnet x hx
      · refine ⟨by omega, rfl, v, rfl, ?_, ?_⟩
        · rw [Nat.add_sub_cancel, opOf_concat_inv, ite_eq_left (by simp [hops])]
        · rw [Nat.add_sub_cancel]; exact not_mem_of_len hI.lin (by rw [hops])
    · simp only [Config.apply, outMsgs, Multiset.map_singleton, Multiset.count_add,
        Multiset.count_singleton]
      split_ifs with heq
      · rw [heq, Multiset.count_eq_zero.2 (hI.not_mem_fresh hops 0 _)]
      · simpa using hI.uniq c s k' m
  · have hr := hI.rd r
    rw [hl] at hr
    obtain ⟨hops, hresps⟩ := hr
    refine ⟨hI.lin.append_inv _ _, by simpa [Config.apply] using hI.srv, fun w' => ?_,
      fun r' => ?_, fun x hx => ?_, fun c s k' m => ?_⟩
    · simp only [Config.apply, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne]
      simpa using (hI.wr w').mono (opsOf_concat_of_ne (by simp))
        (respsOf_append_inv _ _ _ _) []
    · by_cases hr' : r' = r
      · subst hr'
        simp only [Config.apply, Function.update_self, RdOK]
        refine ⟨by simp [hops], by simp [hresps], by simp⟩
      · simp only [Config.apply, ne_eq, Node.rd.injEq, hr', not_false_eq_true,
          Function.update_of_ne]
        simpa using (hI.rd r').mono (opsOf_concat_of_ne (by simp [Ne.symm hr']))
          (respsOf_append_inv _ _ _ _) []
    · simp only [Config.apply, outMsgs, Multiset.map_singleton, Multiset.mem_add,
        Multiset.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hnet x hx
      · refine ⟨rfl, fun _ => ⟨by omega, ?_, ?_⟩⟩
        · rw [Nat.add_sub_cancel, opOf_concat_inv, ite_eq_left (by simp [hops])]
        · rw [Nat.add_sub_cancel]; exact not_mem_of_len hI.lin (by rw [hops])
    · simp only [Config.apply, outMsgs, Multiset.map_singleton, Multiset.count_add,
        Multiset.count_singleton]
      split_ifs with heq
      · rw [heq, Multiset.count_eq_zero.2 (hI.not_mem_fresh hops 0 _)]
      · simpa using hI.uniq c s k' m

lemma Inv.internal (hI : Inv C h L) {p : Node 1 W R} {a : Unit}
    {l : Loc 1 W R V (Option V) V Unit Unit} {out : Multiset (Node 1 W R × Pkt (Option V) V)}
    {res : Option V}
    (hi : ((singleServer W R V v₀).protocol 0 v₀).internal p a (C.loc p) = some (l, out, res)) :
    Inv (C.apply p l out C.net) (h ++ (res.map (Label.ret p)).toList) L := by
  rcases internal_cases hi with ⟨w, k, v, acks, rfl, hl, hne, rfl, rfl, rfl⟩ |
    ⟨r, k, acks, rfl, hl, hne, rfl, rfl, rfl⟩ | ⟨r, k, V₁, acks, rfl, hl, rfl, rfl, rfl⟩
  · have hw := hI.wr w
    rw [hl] at hw
    obtain ⟨hops, hresps, hop, hmem⟩ := hw
    simp only [Option.map_some, Option.toList_some]
    refine ⟨hI.lin.append_ret_of_respIn ?_, by simpa [Config.apply] using hI.srv, fun w' => ?_,
      fun r' => ?_, fun x hx => ?_, fun c s k' m => ?_⟩
    · have : (respsOf h (Node.wr w)).length = k - 1 := by omega
      rw [this]; exact respIn_write hI.lin (hmem hne) hop
    · by_cases hw' : w' = w
      · subst hw'
        simp only [Config.apply, Function.update_self, WrOK]
        exact ⟨by rw [opsOf_append_ret, hops], by simp; omega⟩
      · simp only [Config.apply, ne_eq, Node.wr.injEq, hw', not_false_eq_true,
          Function.update_of_ne]
        simpa using (hI.wr w').mono (opsOf_append_ret _ _ _ _)
          (respsOf_append_ret_of_ne _ _ (by simp [hw'])) []
    · simp only [Config.apply, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne]
      simpa using (hI.rd r').mono (opsOf_append_ret _ _ _ _)
        (respsOf_append_ret_of_ne _ _ (by simp)) []
    · simp only [Config.apply, outMsgs, Multiset.map_zero, add_zero] at hx
      exact (hI.net x hx).mono_hist (fun y o hy => by rw [opOf_append_ret]; exact hy)
    · simpa [Config.apply, outMsgs] using hI.uniq c s k' m
  · have hr := hI.rd r
    rw [hl] at hr
    obtain ⟨hops, hresps, hhead⟩ := hr
    simp only [Option.map_none, Option.toList_none, List.append_nil]
    refine ⟨hI.lin, by simpa [Config.apply] using hI.srv, fun w' => ?_,
      fun r' => ?_, fun x hx => ?_, fun c s k' m => ?_⟩
    · simpa [Config.apply] using hI.wr w'
    · by_cases hr' : r' = r
      · subst hr'
        simp only [Config.apply, Function.update_self, RdOK]
        refine ⟨hops, hresps, ?_⟩
        cases acks with
        | nil => exact absurd rfl hne
        | cons a _ => exact ⟨a, rfl, hhead a rfl⟩
      · simp only [Config.apply, ne_eq, Node.rd.injEq, hr', not_false_eq_true,
          Function.update_of_ne]
        exact hI.rd r'
    · simp only [Config.apply, outMsgs, Multiset.map_singleton, Multiset.mem_add,
        Multiset.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hI.net x hx
      · exact ⟨rfl, fun h => absurd h (by decide)⟩
    · simpa [Config.apply, outMsgs, Multiset.count_singleton] using hI.uniq c s k' m
  · have hr := hI.rd r
    rw [hl] at hr
    obtain ⟨hops, hresps, a, ha, hresp⟩ := hr
    have hv : (V₁.head?.map Prod.snd).getD v₀ = a.2 := by
      rw [Option.mem_def] at ha; simp [ha]
    simp only [Option.map_some, Option.toList_some, hv]
    refine ⟨hI.lin.append_ret_of_respIn ?_, by simpa [Config.apply] using hI.srv, fun w' => ?_,
      fun r' => ?_, fun x hx => ?_, fun c s k' m => ?_⟩
    · have : (respsOf h (Node.rd r)).length = k - 1 := by omega
      rw [this]; exact hresp
    · simp only [Config.apply, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne]
      simpa using (hI.wr w').mono (opsOf_append_ret _ _ _ _)
        (respsOf_append_ret_of_ne _ _ (by simp)) []
    · by_cases hr' : r' = r
      · subst hr'
        simp only [Config.apply, Function.update_self, RdOK]
        exact ⟨by rw [opsOf_append_ret, hops], by simp; omega⟩
      · simp only [Config.apply, ne_eq, Node.rd.injEq, hr', not_false_eq_true,
          Function.update_of_ne]
        simpa using (hI.rd r').mono (opsOf_append_ret _ _ _ _)
          (respsOf_append_ret_of_ne _ _ (by simp [hr'])) []
    · simp only [Config.apply, outMsgs, Multiset.map_zero, add_zero] at hx
      exact (hI.net x hx).mono_hist (fun y o hy => by rw [opOf_append_ret]; exact hy)
    · simpa [Config.apply, outMsgs] using hI.uniq c s k' m

lemma WrOK.absorb {w : W} {l : Loc 1 W R V (Option V) V Unit Unit} {s : Fin 1} {k i : ℕ} {v : V}
    (hw : WrOK h L w l) (hm : MsgOK h L (.srv s, .wr w, .rep k i v)) :
    WrOK h L w (l.absorb s k i v) := by
  rcases l with log | ⟨st, k', _ | ⟨v', acks⟩⟩ | ⟨st, k', ph⟩ <;> simp only [Loc.absorb]
  · exact hw
  · exact hw
  · split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      exact ⟨hw.1, hw.2.1, hw.2.2.1, fun _ => hm rfl⟩
    · exact hw
  · cases ph <;> exact hw.elim

lemma RdOK.absorb {r : R} {l : Loc 1 W R V (Option V) V Unit Unit} {s : Fin 1} {k i : ℕ} {v : V}
    (hr : RdOK h L r l) (hm : MsgOK h L (.srv s, .rd r, .rep k i v)) :
    RdOK h L r (l.absorb s k i v) := by
  rcases l with log | ⟨st, k', cur⟩ | ⟨st, k', _ | acks | ⟨V₁, acks⟩⟩ <;> simp only [Loc.absorb]
  · exact hr
  · cases cur with
    | none => exact hr
    | some x => obtain ⟨v', acks⟩ := x; exact hr.elim
  · exact hr
  · split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨h1, h2, h3⟩ := hr
      refine ⟨h1, h2, fun a ha => ?_⟩
      cases acks with
      | nil =>
        simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at ha
        subst ha; exact hm rfl
      | cons b bs => exact h3 a (by simpa using ha)
    · exact hr
  · split_ifs
    · exact hr
    · exact hr

lemma Inv.recv_srv (hI : Inv C h L) {c : Node 1 W R} {s : Fin 1} {k i : ℕ} {msg : Option V}
    {log : List (Node 1 W R × Option V)}
    (M : List (OpId (Node 1 W R) × RWOp V)) (hlin : IsLinearization h (L ++ M))
    (hval : lastVal v₀ (log ++ [(c, msg)]) =
      (register V v₀).runOps v₀ ((L ++ M).map Prod.snd))
    (hM : ∀ c' s' k' m', (c', Node.srv s', Pkt.req k' 1 m') ∈ C.net.erase (c, .srv s, .req k i msg) →
      (c', k' - 1) ∉ M.map Prod.fst)
    (hrep : MsgOK h (L ++ M) (.srv s, c, .rep k i (lastVal v₀ log))) :
    Inv (C.apply (.srv s) (.srv (log ++ [(c, msg)])) {(c, .rep k i (lastVal v₀ log))}
      (C.net.erase (c, .srv s, .req k i msg))) h (L ++ M) := by
  obtain rfl : s = 0 := Subsingleton.elim _ _
  refine ⟨hlin, ⟨_, by simp [Config.apply], hval⟩, fun w => ?_, fun r => ?_, fun x hx => ?_,
    fun c' s' k' m' => ?_⟩
  · simpa [Config.apply] using (hI.wr w).mono rfl rfl M
  · simpa [Config.apply] using (hI.rd r).mono rfl rfl M
  · simp only [Config.apply, outMsgs, Multiset.map_singleton, Multiset.mem_add,
      Multiset.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact (hI.net x (Multiset.mem_of_mem_erase hx)).append M
        (fun c' s' k' m' hx' => hM c' s' k' m' (hx' ▸ hx))
    · exact hrep
  · simp only [Config.apply, outMsgs, Multiset.map_singleton, Multiset.count_add,
      Multiset.count_singleton]
    rw [ite_eq_right (by simp)]
    exact (Multiset.count_le_of_le _ (Multiset.erase_le _ _)).trans (hI.uniq c' s' k' m')

lemma Inv.receive (hI : Inv C h L) {src dst : Node 1 W R} {m : Pkt (Option V) V}
    {l : Loc 1 W R V (Option V) V Unit Unit} {out : Multiset (Node 1 W R × Pkt (Option V) V)}
    {res : Option V} (hx : (src, dst, m) ∈ C.net)
    (hi : ((singleServer W R V v₀).protocol 0 v₀).receive dst src m (C.loc dst) =
      some (l, out, res)) :
    ∃ L', Inv (C.apply dst l out (C.net.erase (src, dst, m)))
      (h ++ (res.map (Label.ret dst)).toList) L' := by
  rcases receive_cases hi with ⟨rfl, ⟨s, log, k, i, msg, rfl, rfl, hl, rfl, rfl⟩ |
    ⟨s, k, i, v, hp, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · simp only [Option.map_none, Option.toList_none, List.append_nil]
    obtain rfl : s = 0 := Subsingleton.elim _ _
    obtain ⟨log₀, hlog₀, hval₀⟩ := hI.srv
    rw [hl] at hlog₀
    cases hlog₀
    have hmsg := hI.net _ hx
    -- other linearizing requests do not belong to the processed operation
    have hM : ∀ (o : RWOp V), msg = msg → i = 1 → ∀ c' s' k' m',
        (c', Node.srv s', Pkt.req k' 1 m') ∈ C.net.erase (src, .srv 0, .req k i msg) →
        (c', k' - 1) ∉ [((src, k - 1), o)].map Prod.fst := by
      rintro o - rfl c' s' k' m' hy hmem
      simp only [List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨rfl, hk⟩ := hmem
      have := MsgOK.req_eq hmsg (hI.net _ (Multiset.mem_of_mem_erase hy)) hk.symm
      rw [← this] at hy
      exact hI.not_mem_erase hy
    rcases src with s₀ | w | r
    · exact hmsg.elim
    · obtain ⟨hk1, rfl, v, rfl, hop, hnot⟩ := hmsg
      refine ⟨_, hI.recv_srv (log := log) [((.wr w, k - 1), .write v)]
        (hI.lin.push hop hnot (fun hc => hnot (hI.lin.complete _ hc))) ?_ (hM _ rfl rfl)
        (fun _ => by simp)⟩
      simp [ObjSpec.runOps, List.foldl_append]
    · obtain ⟨rfl, hi1⟩ := hmsg
      by_cases hi : i = 1
      · subst hi
        obtain ⟨hk1, hop, hnot⟩ := hi1 rfl
        refine ⟨_, hI.recv_srv (log := log) [((.rd r, k - 1), .read)]
          (hI.lin.push hop hnot (fun hc => hnot (hI.lin.complete _ hc))) ?_ (hM _ rfl rfl)
          (fun _ => ?_)⟩
        · rw [lastVal_concat, hval₀]
          simp [ObjSpec.runOps, List.foldl_append]
        · rw [ObjSpec.respIn_concat_self hnot, hval₀]
      · refine ⟨_, hI.recv_srv (log := log) [] (by simpa using hI.lin) ?_ (by simp)
          (fun h => absurd h hi)⟩
        rw [lastVal_concat, hval₀]
        simp
  · simp only [Option.map_none, Option.toList_none, List.append_nil]
    have hmsg := hI.net _ hx
    refine ⟨L, hI.of_loc_net ?_ (fun w hw => ?_) (fun r hr => ?_) ?_⟩
    · simp [Config.apply, Function.update_of_ne (Ne.symm (hp 0))]
    · simp only [Config.apply]
      by_cases hd : dst = .wr w
      · subst hd; rw [Function.update_self]; exact hw.absorb hmsg
      · rw [Function.update_of_ne (Ne.symm hd)]; exact hw
    · simp only [Config.apply]
      by_cases hd : dst = .rd r
      · subst hd; rw [Function.update_self]; exact hr.absorb hmsg
      · rw [Function.update_of_ne (Ne.symm hd)]; exact hr
    · simpa [Config.apply, outMsgs] using Multiset.erase_le _ _
  · simp only [Option.map_none, Option.toList_none, List.append_nil]
    refine ⟨L, hI.of_loc_net (by simp [Config.apply]) (fun w hw => by simpa [Config.apply] using hw)
      (fun r hr => by simpa [Config.apply] using hr) ?_⟩
    simpa [Config.apply, outMsgs] using Multiset.erase_le _ _

/-- The invariant is preserved by every step. -/
lemma Inv.step (hI : Inv C h L) {st : Step (Node 1 W R) (register V v₀) (Pkt (Option V) V) Unit}
    {C' : SCfg W R V} {ℓ : Option (Label (Node 1 W R) (register V v₀))}
    (hs : ((singleServer W R V v₀).protocol 0 v₀).step C st = some (C', ℓ)) :
    ∃ L', Inv C' (h ++ ℓ.toList) L' := by
  cases st with
  | inv p o =>
    simp only [Protocol.step] at hs
    split_ifs at hs
    obtain ⟨⟨l, out⟩, hi, he⟩ := Option.map_eq_some_iff.1 hs
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨L, hI.invoke hi⟩
  | internal p a =>
    simp only [Protocol.step] at hs
    split_ifs at hs
    obtain ⟨⟨l, out, res⟩, hi, he⟩ := Option.map_eq_some_iff.1 hs
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨L, hI.internal hi⟩
  | recv src dst m =>
    simp only [Protocol.step] at hs
    split_ifs at hs with hc
    obtain ⟨⟨l, out, res⟩, hi, he⟩ := Option.map_eq_some_iff.1 hs
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hI.receive (by tauto) hi
  | drop src dst m =>
    simp only [Protocol.step] at hs
    split_ifs at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simp only [Option.toList_none, List.append_nil]
    exact ⟨L, hI.of_loc_net (C' := ⟨C.loc, C.net.erase (src, dst, m), C.sent, C.crashed⟩) rfl
      (fun _ h => h) (fun _ h => h) (Multiset.erase_le _ _)⟩
  | crash p =>
    simp only [Protocol.step] at hs
    split_ifs at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simp only [Option.toList_none, List.append_nil]
    exact ⟨L, hI.of_loc_net (C' := ⟨C.loc, C.net, C.sent, insert p C.crashed⟩) rfl
      (fun _ h => h) (fun _ h => h) le_rfl⟩
  | skip =>
    simp only [Protocol.step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨L, by simpa using hI⟩

lemma inv_init :
    Inv ((singleServer W R V v₀).protocol 0 v₀).initCfg ([] : List (Label _ (register V v₀))) [] where
  lin := isLinearization_nil
  srv := ⟨[], rfl, rfl⟩
  wr w := by simp [Protocol.initCfg, W1R2Alg.protocol, WrOK]
  rd r := by simp [Protocol.initCfg, W1R2Alg.protocol, RdOK]
  net x hx := by simp [Protocol.initCfg] at hx
  uniq := by simp [Protocol.initCfg]

end Steps

end SingleServer

open SingleServer in
/-- **Sanity check of the model of Theorem 1.** With one server and `t = 0`, the single-server
fast-write algorithm `singleServer` (writes: one round-trip; reads: two round-trips) is a
linearizable implementation of a multi-writer multi-reader register, for any sets of writers and
readers. Hence the hypothesis `1 ≤ t` of `Podc.FastMWMR.theorem_1` cannot be dropped. -/
theorem single_server_linearizable (W R V : Type) [DecidableEq W] [DecidableEq R]
    [DecidableEq V] (v₀ : V) : ((singleServer W R V v₀).protocol 0 v₀).Linearizable := by
  suffices ∀ C h, ((singleServer W R V v₀).protocol 0 v₀).Reach C h → ∃ L, Inv C h L by
    intro C h hR
    obtain ⟨L, hI⟩ := this C h hR
    exact ⟨L, hI.lin⟩
  intro C h hR
  induction hR with
  | init => exact ⟨[], inv_init⟩
  | step _ hs ih =>
    obtain ⟨L, hI⟩ := ih
    exact hI.step hs

end Podc.FastMWMR
