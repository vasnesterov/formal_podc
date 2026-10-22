import Papers.PODC2022.FullyDefective.Protocol
import Papers.PODC2022.FullyDefective.Cycle.Invariant

/-!
# Theorem 4 of [CCGS22] (= Theorem 6 of the full version): simulating `π` on a cycle

The simulator `π̂` of Algorithm 1: every node `v` runs the ring layer of `Cycle/Model.lean` and a
copy of the simulated protocol `π`. Whenever `π` at `v` sends a message `m` to `w`, the simulator
enqueues the unary length `enc (v, w, m)` of its encoding in `Q_v`; whenever `v` completes an
epoch and decodes a triple `(u', v', m')` with `v' = v`, it delivers `m'` (from `u'`) to `π`
(Line 28). `π` processes delivered messages one by one, each after an arbitrary finite delay
(an explicit `proc` step), atomically producing its outgoing messages: "`π`'s actions take finite
arbitrary time unknown to and independent of the simulator".

**Theorem (`simulation`).** For every reachable configuration `C` of the simulator over the
fully-defective cycle there is a reachable configuration `D` of `π` over the noiseless network in
which every node has the same state and the same local transcript as the copy of `π` it runs in
`C`; moreover the messages in transit in `D` are exactly the messages sent by `π` in `C` and not
yet processed by their recipient.
-/

namespace Podc.FullyDefective

/-- An injective encoding of the triples `(source, destination, message)` by positive natural
numbers (the length of the unary encoding `1^d`, Line 19). -/
structure Coding (V M : Type*) where
  /-- The encoding. -/
  enc : V × V × M → ℕ
  /-- The decoding (Line 27). -/
  dec : ℕ → Option (V × V × M)
  enc_pos : ∀ x, 0 < enc x
  dec_enc : ∀ x, dec (enc x) = some x

/-- The coding given by `Encodable` instances. -/
def Coding.ofEncodable (V M : Type*) [Encodable V] [Encodable M] : Coding V M where
  enc x := Encodable.encode x + 1
  dec a := Encodable.decode (a - 1)
  enc_pos _ := Nat.succ_pos _
  dec_enc x := by simp

namespace Cycle

variable {n : ℕ} {M : Type*} (P : Protocol (ZMod n) M) (K : Coding (ZMod n) M)

/-- Configurations of the simulator: the ring layer, and at every node the state of `π`, the
number of delivered messages `π` has processed, the local transcript of `π`, and (ghost) the
messages `π` has sent so far. -/
structure SimConfig where
  /-- The ring layer. -/
  ring : Config n
  /-- The state of `π` at each node. -/
  pst : ZMod n → P.State
  /-- The number of delivered messages that `π` has processed. -/
  nproc : ZMod n → ℕ
  /-- The local transcript of `π`. -/
  tr : ZMod n → List (Event (ZMod n) M)
  /-- Ghost: the messages `(destination, content)` sent by `π`. -/
  out : ZMod n → List (ZMod n × M)

variable {P K}

variable (K) in
/-- The messages delivered to `π` at `v` so far (Lines 26–28): the decoded payloads of the
completed epochs whose destination is `v`. -/
def SimConfig.rcv (C : SimConfig P) (v : ZMod n) : List (ZMod n × ZMod n × M) :=
  ((C.ring.node v).log.filterMap K.dec).filter (fun x => x.2.1 = v)

variable (K) in
/-- The payloads enqueued for the messages `out` sent by `v`. -/
def encOut (v : ZMod n) (out : List (ZMod n × M)) : List ℕ := out.map fun o => K.enc (v, o.1, o.2)

/-- Append payloads to `Q_v`. -/
def pushAll (c : Config n) (v : ZMod n) (l : List ℕ) : Config n :=
  { c with node := Function.update c.node v { c.node v with q := (c.node v).q ++ l } }

/-- Steps of the simulator: a step of the ring layer (pushes only come from `π`), or `π`
processing the next delivered message at `v`. -/
inductive SimLabel (n : ℕ) where
  /-- A step of the ring layer (`start`, `cw` or `ccw`). -/
  | ring (l : Label n)
  /-- `π` at `v` processes its next delivered message. -/
  | proc (v : ZMod n)

variable (K) in
/-- Whether a step of the simulator is enabled. -/
def SimEnabled (C : SimConfig P) : SimLabel n → Prop
  | .ring (.push _ _) => False
  | .ring l => Enabled C.ring l
  | .proc v => C.nproc v < (C.rcv K v).length

variable [DecidableEq M]

variable (K) in
/-- The simulator configuration after a step. -/
def simNext (C : SimConfig P) : SimLabel n → SimConfig P
  | .ring l => { C with ring := next C.ring l }
  | .proc v =>
    if h : C.nproc v < (C.rcv K v).length then
      let x := (C.rcv K v)[C.nproc v]
      let r := P.recv v (C.pst v) x.1 x.2.2
      { ring := pushAll C.ring v (encOut K v r.2)
        pst := Function.update C.pst v r.1
        nproc := Function.update C.nproc v (C.nproc v + 1)
        tr := Function.update C.tr v (C.tr v ++ [.recv x.1 x.2.2] ++ Protocol.sends r.2)
        out := Function.update C.out v (C.out v ++ r.2) }
    else C

variable (K) in
/-- One step of the simulator. -/
def SimStep (C C' : SimConfig P) : Prop := ∃ l, SimEnabled K C l ∧ C' = simNext K C l

variable (P K) in
/-- The initial configuration of the simulator: `π` has performed its start-up action at every
node and the corresponding payloads are in the queues; `T₀` holds the token. -/
def simInit (T₀ : ZMod n) : SimConfig P where
  ring := init T₀ (fun v => encOut K v (P.init v).2)
  pst v := (P.init v).1
  nproc _ := 0
  tr v := Protocol.sends (P.init v).2
  out v := (P.init v).2

variable (P K) in
/-- Reachable configurations of the simulator. -/
def SimReach (T₀ : ZMod n) (C : SimConfig P) : Prop :=
  Relation.ReflTransGen (SimStep K) (simInit P K T₀) C

/-! ### Bookkeeping -/

/-- All messages sent by `π` so far. -/
def SimConfig.sentMS [NeZero n] (C : SimConfig P) : Multiset (ZMod n × ZMod n × M) :=
  ∑ v, Protocol.tag v (C.out v)

variable (K) in
/-- All messages processed by `π` so far. -/
def SimConfig.procMS [NeZero n] (C : SimConfig P) : Multiset (ZMod n × ZMod n × M) :=
  ∑ v, (((C.rcv K v).take (C.nproc v) : List _) : Multiset _)

variable (K) in
/-- Decode a list of payloads. -/
def decs (l : List ℕ) : List (ZMod n × ZMod n × M) := l.filterMap K.dec

/-! ### The ring layer under the simulator's steps -/

section ringFacts

variable {c : Config n}

lemma pushAll_cons (c : Config n) (v : ZMod n) (a : ℕ) (l : List ℕ) :
    pushAll c v (a :: l) = pushAll (next c (.push v a)) v l := by
  simp only [pushAll, next]
  congr 1; funext w
  by_cases hw : w = v
  · subst hw; simp
  · simp [Function.update_apply, hw]

lemma Reach.pushAll {T₀ : ZMod n} {qs : ZMod n → List ℕ} (h : Reach T₀ qs c) (v : ZMod n)
    {l : List ℕ} (hl : ∀ a ∈ l, 0 < a) : Reach T₀ qs (pushAll c v l) := by
  induction l generalizing c with
  | nil =>
    have : pushAll c v [] = c := by
      simp only [pushAll, List.append_nil]; cases c; simp
    rw [this]; exact h
  | cons a l ih =>
    rw [pushAll_cons]
    exact ih (h.tail ⟨.push v a, hl a (by simp), rfl⟩) (fun b hb => hl b (by simp [hb]))

/-- Ring steps only append to logs. -/
lemma log_prefix_next (l : Label n) (v : ZMod n) :
    (c.node v).log <+: ((next c l).node v).log := by
  cases l with
  | push u a => by_cases hv : v = u <;> simp [hv]
  | start u => by_cases hv : v = u <;> simp [hv]
  | cw u => by_cases hv : v = u <;> simp [hv]
  | ccw u =>
    by_cases hv : v = u
    · subst hv; simp only [next_ccw_node, ↓reduceIte]
      rcases hs : c.node v with ⟨ph, tok, q, log⟩
      cases ph <;> simp [onCCW]
      split <;> simp
    · simp [hv]

/-- Ring steps other than `push` move payloads from the queues to `ds` and never create or
destroy them. -/
lemma mass_next [NeZero n] (l : Label n) (hl : ∀ u a, l ≠ .push u a) :
    ((next c l).ds : Multiset ℕ) + ∑ v, (((next c l).node v).q : Multiset ℕ) =
      (c.ds : Multiset ℕ) + ∑ v, ((c.node v).q : Multiset ℕ) := by
  cases l with
  | push u a => exact absurd rfl (hl u a)
  | start u =>
    congr 1; refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v = u <;> simp [hv]
  | cw u =>
    congr 1; refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v = u <;> simp [hv]
  | ccw u =>
    rcases hs : c.node u with ⟨ph, tok, q, log⟩
    have hq : ∀ v, v ≠ u → ((next c (.ccw u)).node v).q = (c.node v).q := fun v hv => by simp [hv]
    cases ph with
    | ready =>
      cases q with
      | nil =>
        simp only [next_ccw_ds, hs, capture?]
        congr 1; refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv : v = u
        · subst hv; simp [hs, onCCW]
        · rw [hq v hv]
      | cons a q =>
        simp only [next_ccw_ds, hs, capture?]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
        rw [Finset.sum_congr rfl fun v hv => by rw [hq v (Finset.ne_of_mem_erase hv)]]
        simp [hs, onCCW]
        have e1 : ((a :: q : List ℕ) : Multiset ℕ) = {a} + ↑q := by simp
        have e2 : ((c.ds ++ [a] : List ℕ) : Multiset ℕ) = ↑c.ds + {a} := by
          rw [← Multiset.coe_add]; rfl
        rw [e1, e2]; abel
    | _ =>
      simp only [next_ccw_ds, hs, capture?]
      congr 1; refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v = u
      · subst hv; simp [hs, onCCW]
      · rw [hq v hv]

end ringFacts

/-! ### The simulation invariant -/

omit [DecidableEq M] in
lemma _root_.Podc.FullyDefective.Coding.enc_injective {V : Type*} (K : Coding V M) :
    Function.Injective K.enc := by
  intro x y h; have := K.dec_enc x; rw [h, K.dec_enc] at this; exact (Option.some.inj this).symm

lemma map_enc_tag (v : ZMod n) (out : List (ZMod n × M)) :
    Multiset.map K.enc (Protocol.tag v out) = (encOut K v out : Multiset ℕ) := by
  simp [Protocol.tag, encOut, Function.comp_def]

lemma count_filterMap_dec {l : List ℕ} (hl : ∀ a ∈ l, ∃ y, a = K.enc y) (x : ZMod n × ZMod n × M) :
    (l.filterMap K.dec).count x = l.count (K.enc x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨y, rfl⟩ := hl a (by simp)
    rw [List.filterMap_cons, K.dec_enc]
    simp only [List.count_cons, ih (fun b hb => hl b (by simp [hb]))]
    congr 1
    by_cases hxy : x = y
    · subst hxy; simp
    · have h2 := K.enc_injective.ne (Ne.symm hxy)
      simp [Ne.symm hxy, h2]

lemma rcv_dst {C : SimConfig P} {v : ZMod n} {y : ZMod n × ZMod n × M} (hy : y ∈ C.rcv K v) :
    y.2.1 = v := by
  simp only [SimConfig.rcv, List.mem_filter, decide_eq_true_eq] at hy; exact hy.2

variable [NeZero n]

variable (K) in
/-- The invariant of the simulator. -/
structure SimInv (T₀ : ZMod n) (C : SimConfig P) : Prop where
  ring : Reach T₀ (fun v => encOut K v (P.init v).2) C.ring
  nproc_le : ∀ v, C.nproc v ≤ (C.rcv K v).length
  mass : Multiset.map K.enc C.sentMS =
    (C.ring.ds : Multiset ℕ) + ∑ v, ((C.ring.node v).q : Multiset ℕ)
  sim : ∃ D : P.Config, P.Reach D ∧ D.st = C.pst ∧ D.tr = C.tr ∧ D.net + C.procMS K = C.sentMS

lemma SimInv.inv {T₀ : ZMod n} {C : SimConfig P} (h : SimInv K T₀ C) : Inv C.ring :=
  h.ring.inv fun v a ha => by
    simp only [encOut, List.mem_map] at ha; obtain ⟨o, -, rfl⟩ := ha; exact K.enc_pos _

lemma simInv_init (T₀ : ZMod n) : SimInv K T₀ (simInit P K T₀) := by
  refine ⟨Relation.ReflTransGen.refl, fun v => by simp [simInit], ?_, ⟨P.initCfg, .refl, rfl, rfl, ?_⟩⟩
  · have := map_sum (Multiset.mapAddMonoidHom K.enc) (fun v => Protocol.tag v (P.init v).2)
      Finset.univ
    simp only [Multiset.mapAddMonoidHom_apply] at this
    simp [SimConfig.sentMS, simInit, init, this, map_enc_tag]
  · simp [SimConfig.procMS, SimConfig.sentMS, simInit, Protocol.initCfg]

/-- The key counting step: the next message to process at `v` is still in transit in the
noiseless execution. -/
lemma SimInv.count_lt {T₀ : ZMod n} {C : SimConfig P} (hI : SimInv K T₀ C) {v : ZMod n}
    (h : C.nproc v < (C.rcv K v).length) :
    (C.procMS K).count (C.rcv K v)[C.nproc v] < C.sentMS.count (C.rcv K v)[C.nproc v] := by
  set x := (C.rcv K v)[C.nproc v]
  have hxv : x.2.1 = v := rcv_dst (List.getElem_mem h)
  -- the processed copies of `x` are at `v`
  have h1 : (C.procMS K).count x = ((C.rcv K v).take (C.nproc v)).count x := by
    simp only [SimConfig.procMS, Multiset.count_sum', Multiset.coe_count]
    rw [Finset.sum_eq_single v]
    · intro w _ hw
      rw [List.count_eq_zero]
      intro hx; exact hw (by rw [← rcv_dst (List.mem_of_mem_take hx), hxv])
    · simp
  have h2 : (C.rcv K v).take (C.nproc v + 1) = (C.rcv K v).take (C.nproc v) ++ [x] := by
    rw [List.take_succ, List.getElem?_eq_getElem h]; rfl
  -- the range of the encoding
  have hrange : ∀ a ∈ C.ring.ds, ∃ y, a = K.enc y := by
    intro a ha
    have : a ∈ Multiset.map K.enc C.sentMS := by
      rw [hI.mass]; exact Multiset.mem_add.2 (Or.inl (by simpa using ha))
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 this; exact ⟨y, rfl⟩
  have hpre : (C.ring.node v).log <+: C.ring.ds := hI.inv.log_prefix v
  have h3 : ((C.rcv K v).take (C.nproc v + 1)).count x ≤ C.ring.ds.count (K.enc x) := by
    rw [← count_filterMap_dec hrange]
    refine List.Sublist.count_le _ ?_
    refine (List.take_sublist _ _).trans ?_
    refine (List.filter_sublist).trans ?_
    exact (hpre.filterMap K.dec).sublist
  have h4 : C.ring.ds.count (K.enc x) ≤ C.sentMS.count x := by
    rw [← Multiset.count_map_eq_count' _ _ K.enc_injective, hI.mass, Multiset.count_add]
    simp
  rw [h1]; rw [h2, List.count_append] at h3; simp at h3; omega

lemma take_eq_of_prefix {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) {k : ℕ} (hk : k ≤ l₁.length) :
    l₂.take k = l₁.take k := by
  obtain ⟨t, rfl⟩ := h; exact List.take_append_of_le_length hk

lemma tag_append (v : ZMod n) (l₁ l₂ : List (ZMod n × M)) :
    Protocol.tag v (l₁ ++ l₂) = Protocol.tag v l₁ + Protocol.tag v l₂ := by
  simp [Protocol.tag]

lemma simInv_ring {T₀ : ZMod n} {C : SimConfig P} (hI : SimInv K T₀ C) {l : Label n}
    (hen : SimEnabled K C (.ring l)) : SimInv K T₀ (simNext K C (.ring l)) := by
  have hpush : ∀ u a, l ≠ .push u a := by rintro u a rfl; exact hen
  have hen' : Enabled C.ring l := by cases l <;> first | exact hen | exact absurd rfl (hpush _ _)
  set C' := simNext K C (.ring l)
  have hring : C'.ring = next C.ring l := rfl
  have hrcv : ∀ v, C.rcv K v <+: C'.rcv K v := fun v =>
    ((log_prefix_next l v).filterMap K.dec).filter _
  have hproc : C'.procMS K = C.procMS K := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [show C'.nproc v = C.nproc v from rfl, take_eq_of_prefix (hrcv v) (hI.nproc_le v)]
  obtain ⟨D, hD, hst, htr, hnet⟩ := hI.sim
  exact ⟨hI.ring.tail ⟨l, hen', rfl⟩, fun v => (hI.nproc_le v).trans (hrcv v).length_le,
    by rw [show C'.sentMS = C.sentMS from rfl, hI.mass, hring, mass_next l hpush],
    ⟨D, hD, hst, htr, by rw [hproc]; exact hnet⟩⟩

lemma pushAll_log (c : Config n) (v w : ZMod n) (l : List ℕ) :
    ((pushAll c v l).node w).log = (c.node w).log := by
  by_cases hw : w = v
  · subst hw; simp [pushAll]
  · simp [pushAll, hw]

lemma simInv_proc {T₀ : ZMod n} {C : SimConfig P} (hI : SimInv K T₀ C) {v : ZMod n}
    (h : C.nproc v < (C.rcv K v).length) : SimInv K T₀ (simNext K C (.proc v)) := by
  set x := (C.rcv K v)[C.nproc v] with hxdef
  have hxv : x.2.1 = v := rcv_dst (List.getElem_mem h)
  set r := P.recv v (C.pst v) x.1 x.2.2 with hr
  have hC' : simNext K C (.proc v) =
      { ring := pushAll C.ring v (encOut K v r.2)
        pst := Function.update C.pst v r.1
        nproc := Function.update C.nproc v (C.nproc v + 1)
        tr := Function.update C.tr v (C.tr v ++ [.recv x.1 x.2.2] ++ Protocol.sends r.2)
        out := Function.update C.out v (C.out v ++ r.2) } := by
    simp only [simNext, dif_pos h]; rfl
  set C' := simNext K C (.proc v)
  have e_ring : C'.ring = pushAll C.ring v (encOut K v r.2) := by rw [hC']
  have e_pst : C'.pst = Function.update C.pst v r.1 := by rw [hC']
  have e_nproc : C'.nproc = Function.update C.nproc v (C.nproc v + 1) := by rw [hC']
  have e_tr : C'.tr =
      Function.update C.tr v (C.tr v ++ [.recv x.1 x.2.2] ++ Protocol.sends r.2) := by rw [hC']
  have e_out : C'.out = Function.update C.out v (C.out v ++ r.2) := by rw [hC']
  have hrcv : ∀ w, C'.rcv K w = C.rcv K w := fun w => by
    simp only [SimConfig.rcv, e_ring, pushAll_log]
  have hsent : C'.sentMS = C.sentMS + Protocol.tag v r.2 := by
    simp only [SimConfig.sentMS, e_out]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v), ← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    rw [Finset.sum_congr rfl fun w hw => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]]
    simp [tag_append, add_assoc]
  have hproc : C'.procMS K = C.procMS K + {x} := by
    simp only [SimConfig.procMS, hrcv]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v), ← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    rw [Finset.sum_congr rfl fun w hw => by
      rw [e_nproc, Function.update_of_ne (Finset.ne_of_mem_erase hw)]]
    have htk : (((C.rcv K v).take (C.nproc v + 1) : List _) : Multiset _) =
        ((C.rcv K v).take (C.nproc v) : Multiset _) + {x} := by
      rw [List.take_succ, List.getElem?_eq_getElem h, ← Multiset.coe_add]; rfl
    rw [e_nproc, Function.update_self, htk, add_assoc]
  obtain ⟨D, hD, hst, htr, hnet⟩ := hI.sim
  have hx : x ∈ D.net := by
    have h1 := hI.count_lt h
    rw [← hxdef, ← hnet, Multiset.count_add] at h1
    exact Multiset.count_pos.1 (by omega)
  refine ⟨by
      rw [e_ring]
      exact hI.ring.pushAll v (fun a ha => by
        simp only [encOut, List.mem_map] at ha; obtain ⟨o, -, rfl⟩ := ha; exact K.enc_pos _),
    fun w => ?_, ?_, ⟨P.deliver D x, hD.tail (Protocol.Step.mk D x hx), ?_, ?_, ?_⟩⟩
  · rw [hrcv]; by_cases hw : w = v
    · subst hw; simp only [e_nproc, Function.update_self]; omega
    · simp only [e_nproc, Function.update_of_ne hw]; exact hI.nproc_le w
  · rw [hsent, Multiset.map_add, hI.mass, map_enc_tag, e_ring]
    have hq : ∀ w, (((pushAll C.ring v (encOut K v r.2)).node w).q : Multiset ℕ) =
        (C.ring.node w).q + if w = v then (encOut K v r.2 : Multiset ℕ) else 0 := by
      intro w; by_cases hw : w = v
      · subst hw; simp [pushAll]
      · simp [pushAll, hw]
    rw [Finset.sum_congr rfl (fun w _ => hq w), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [pushAll, add_assoc]
  · rw [e_pst]; simp only [Protocol.deliver, hxv, hst, ← hr]
  · rw [e_tr]; simp only [Protocol.deliver, hxv, htr, hst, ← hr]
  · have hn : (P.deliver D x).net = D.net.erase x + Protocol.tag v r.2 := by
      simp only [Protocol.deliver]; rw [hxv, hst]
    rw [hn, hsent, hproc, ← hnet]
    have e : D.net.erase x + {x} = D.net := by
      rw [add_comm, Multiset.singleton_add]; exact Multiset.cons_erase hx
    calc D.net.erase x + Protocol.tag v r.2 + (C.procMS K + {x})
        = (D.net.erase x + {x}) + C.procMS K + Protocol.tag v r.2 := by abel
      _ = D.net + C.procMS K + Protocol.tag v r.2 := by rw [e]

theorem SimReach.inv {T₀ : ZMod n} {C : SimConfig P} (h : SimReach P K T₀ C) : SimInv K T₀ C := by
  induction h with
  | refl => exact simInv_init T₀
  | tail _ hs ih =>
    obtain ⟨l, hen, rfl⟩ := hs
    cases l with
    | ring l => exact simInv_ring ih hen
    | proc v => exact simInv_proc ih hen

/-- **Theorem 4 of [CCGS22] (= Theorem 6 of the full version), safety: Algorithm 1 simulates `π`.**
In every reachable configuration `C` of the simulator `π̂` (Algorithm 1 with the black box `π`) on
the fully-defective oriented cycle, every node's copy of `π` has the state and the local transcript
of the same node in some reachable configuration `D` of `π` over the noiseless network; the
messages in transit in `D` are exactly the messages sent by `π` in `C` and not yet processed by
their destination. (Liveness is in `Cycle/Progress.lean`.) -/
theorem simulation {T₀ : ZMod n} {C : SimConfig P} (h : SimReach P K T₀ C) :
    ∃ D : P.Config, P.Reach D ∧ (∀ v, D.st v = C.pst v ∧ D.tr v = C.tr v) ∧
      D.net + C.procMS K = C.sentMS := by
  obtain ⟨D, hD, hst, htr, hnet⟩ := h.inv.sim
  exact ⟨D, hD, fun v => ⟨congrFun hst v, congrFun htr v⟩, hnet⟩

end Cycle

end Podc.FullyDefective
