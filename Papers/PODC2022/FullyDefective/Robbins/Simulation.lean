import Papers.PODC2022.FullyDefective.Cycle.Simulation
import Papers.PODC2022.FullyDefective.Robbins.Preservation

/-!
# Theorem 6 of [CCGS22] (= Theorems 10/12 of the full version): simulating `π` over a Robbins cycle

The simulator `π̂` of Algorithm 3: every node `v` of `G` runs the network layer of
`Robbins/Model.lean` and a copy of the simulated protocol `π`. Whenever `π` at `v` sends a message
`m` to `w`, the simulator enqueues the unary length `enc (v, w, m)` of its encoding in `Q_v`;
whenever `v` completes an epoch and decodes a triple `(u', v', m')` with `v' = v`, it delivers `m'`
(from `u'`) to `π` (Line 40). `π` processes delivered messages one by one, each after an
arbitrary finite delay (an explicit `proc` step). This is the composition of `Cycle/Simulation.lean`
with the network layer of Algorithm 3; the proof only uses that the reachable configurations are
closed under enqueueing positive payloads, that logs only grow, that the network steps move
payloads from the queues to `ds` without creating or destroying them, and Lemma 11(3)
(`Inv.log_prefix`).

**Theorem (`simulation`).** For every reachable configuration `C` of the simulator over the
fully-defective graph `G` with Robbins cycle `R` there is a reachable configuration `D` of `π` over
the noiseless network in which every node has the same state and the same local transcript as the
copy of `π` it runs in `C`; moreover the messages in transit in `D` are exactly the messages sent
by `π` in `C` and not yet processed by their recipient.
-/

set_option linter.unusedSectionVars false

namespace Podc.FullyDefective.RobbinsSim

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {R : RobbinsCycle G}
variable {M : Type*} (P : Protocol V M) (K : Coding V M)

variable (R) in
/-- Configurations of the simulator: the network layer, and at every node the state of `π`, the
number of delivered messages `π` has processed, the local transcript of `π`, and (ghost) the
messages `π` has sent so far. -/
structure SimConfig where
  /-- The network layer. -/
  ring : Config V R.L
  /-- The state of `π` at each node. -/
  pst : V → P.State
  /-- The number of delivered messages that `π` has processed. -/
  nproc : V → ℕ
  /-- The local transcript of `π`. -/
  tr : V → List (Event V M)
  /-- Ghost: the messages `(destination, content)` sent by `π`. -/
  out : V → List (V × M)

variable {P K}

variable (K) in
/-- The messages delivered to `π` at `v` so far (Lines 38–40): the decoded payloads of the
completed epochs whose destination is `v`. -/
def SimConfig.dlv (C : SimConfig R P) (v : V) : List (V × V × M) :=
  ((C.ring.node v).log.filterMap K.dec).filter (fun x => x.2.1 = v)

variable (K) in
/-- The payloads enqueued for the messages `out` sent by `v`. -/
def encOut (v : V) (out : List (V × M)) : List ℕ := out.map fun o => K.enc (v, o.1, o.2)

/-- Append payloads to `Q_v`. -/
def pushAll (c : Config V R.L) (v : V) (l : List ℕ) : Config V R.L :=
  { c with node := Function.update c.node v { c.node v with q := (c.node v).q ++ l } }

/-- Steps of the simulator: a step of the network layer (pushes only come from `π`), or `π`
processing the next delivered message at `v`. -/
inductive SimLabel (V : Type*) where
  /-- A step of the network layer (`start` or `recv`). -/
  | ring (l : Label V)
  /-- `π` at `v` processes its next delivered message. -/
  | proc (v : V)

variable (K) in
/-- Whether a step of the simulator is enabled. -/
def SimEnabled (C : SimConfig R P) : SimLabel V → Prop
  | .ring (.push _ _) => False
  | .ring l => Enabled R C.ring l
  | .proc v => C.nproc v < (C.dlv K v).length

variable [DecidableEq M]

variable (K) in
/-- The simulator configuration after a step. -/
def simNext (C : SimConfig R P) : SimLabel V → SimConfig R P
  | .ring l => { C with ring := next R C.ring l }
  | .proc v =>
    if h : C.nproc v < (C.dlv K v).length then
      let x := (C.dlv K v)[C.nproc v]
      let r := P.recv v (C.pst v) x.1 x.2.2
      { ring := pushAll C.ring v (encOut K v r.2)
        pst := Function.update C.pst v r.1
        nproc := Function.update C.nproc v (C.nproc v + 1)
        tr := Function.update C.tr v (C.tr v ++ [.recv x.1 x.2.2] ++ Protocol.sends r.2)
        out := Function.update C.out v (C.out v ++ r.2) }
    else C

variable (K) in
/-- One step of the simulator. -/
def SimStep (C C' : SimConfig R P) : Prop := ∃ l, SimEnabled K C l ∧ C' = simNext K C l

variable (R P K) in
/-- The initial configuration of the simulator: `π` has performed its start-up action at every
node and the corresponding payloads are in the queues; the occurrence at position `τ₀` holds the
token. -/
def simInit (τ₀ : ZMod R.L) : SimConfig R P where
  ring := init R τ₀ (fun v => encOut K v (P.init v).2)
  pst v := (P.init v).1
  nproc _ := 0
  tr v := Protocol.sends (P.init v).2
  out v := (P.init v).2

variable (R P K) in
/-- Reachable configurations of the simulator. -/
def SimReach (τ₀ : ZMod R.L) (C : SimConfig R P) : Prop :=
  Relation.ReflTransGen (SimStep K) (simInit R P K τ₀) C

/-! ### Bookkeeping -/

/-- All messages sent by `π` so far. -/
def SimConfig.sentMS (C : SimConfig R P) : Multiset (V × V × M) :=
  ∑ v, Protocol.tag v (C.out v)

variable (K) in
/-- All messages processed by `π` so far. -/
def SimConfig.procMS (C : SimConfig R P) : Multiset (V × V × M) :=
  ∑ v, (((C.dlv K v).take (C.nproc v) : List _) : Multiset _)

/-! ### The network layer under the simulator's steps -/

section ringFacts

variable {c : Config V R.L}

lemma pushAll_cons (c : Config V R.L) (v : V) (a : ℕ) (l : List ℕ) :
    pushAll c v (a :: l) = pushAll (next R c (.push v a)) v l := by
  simp only [pushAll, next]
  congr 1; funext w
  by_cases hw : w = v
  · subst hw; simp
  · simp [Function.update_apply, hw]

lemma Reach.pushAll {τ₀ : ZMod R.L} {qs : V → List ℕ} (h : Reach R τ₀ qs c) (v : V)
    {l : List ℕ} (hl : ∀ a ∈ l, 0 < a) : Reach R τ₀ qs (pushAll c v l) := by
  induction l generalizing c with
  | nil =>
    have : pushAll c v [] = c := by
      simp only [pushAll, List.append_nil]; cases c; simp
    rw [this]; exact h
  | cons a l ih =>
    rw [pushAll_cons]
    exact ih (h.tail ⟨.push v a, hl a (by simp), rfl⟩) (fun b hb => hl b (by simp [hb]))

lemma react_log_prefix (u x : V) (s : Node V R.L) : s.log <+: (react R u s x).s.log := by
  rcases s with ⟨ph, tok, q, log, o⟩
  cases ph with
  | idle | waitReq _ => simp [react]
  | ready => simp only [react]; split_ifs <;> [split; skip] <;> simp
  | _ => simp only [react] <;> (try split_ifs) <;> simp

/-- Network steps only append to logs. -/
lemma log_prefix_next (l : Label V) (v : V) :
    (c.node v).log <+: ((next R c l).node v).log := by
  cases l with
  | push u a => by_cases hv : v = u <;> simp [next, Function.update_apply, hv]
  | start u => by_cases hv : v = u <;> simp [next, Function.update_apply, hv]
  | recv u x =>
    rw [next_recv_node]; split_ifs with hv
    · subst hv; exact react_log_prefix _ _ _
    · exact List.prefix_refl _

lemma react_q_of {u x : V} {s : Node V R.L} (h : tokRecv R u s x = false) :
    (react R u s x).s.q = s.q := by
  rcases s with ⟨ph, tok, q, log, o⟩
  cases ph with
  | idle | waitReq _ => simp [react]
  | ready =>
    simp only [tokRecv, Phase.isReady, Bool.true_and, decide_eq_false_iff_not, not_lt,
      Nat.le_zero] at h
    simp [react, h]
  | _ => simp only [react] <;> (try split_ifs) <;> try rfl

/-- Network steps other than `push` move payloads from the queues to `ds` and never create or
destroy them. -/
lemma mass_next (l : Label V) (hl : ∀ u a, l ≠ .push u a) :
    ((next R c l).ds : Multiset ℕ) + ∑ v, (((next R c l).node v).q : Multiset ℕ) =
      (c.ds : Multiset ℕ) + ∑ v, ((c.node v).q : Multiset ℕ) := by
  cases l with
  | push u a => exact absurd rfl (hl u a)
  | start u =>
    show (c.ds : Multiset ℕ) + _ = _
    congr 1; refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v = u <;> simp [next, Function.update_apply, hv]
  | recv u x =>
    have hq : ∀ v, v ≠ u → ((next R c (.recv u x)).node v).q = (c.node v).q := fun v hv => by
      rw [next_recv_node_ne _ _ hv]
    rcases htr : tokRecv R u (c.node u) x
    · rw [next_ds_of htr]
      congr 1; refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v = u
      · subst hv; rw [next_recv_node_self, react_q_of htr]
      · rw [hq v hv]
    · have hready : (c.node u).ph = .ready := by
        revert htr; simp only [tokRecv, Bool.and_eq_true, decide_eq_true_eq]
        rcases (c.node u).ph <;> simp [Phase.isReady]
      have hmux : 0 < mult R u x := by
        revert htr; simp [tokRecv]
      rw [next_recv_ds, htr, ite_eq_left rfl]
      rcases hqq : (c.node u).q with _ | ⟨a, rest⟩
      · simp only
        congr 1; refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv : v = u
        · subst hv; rw [next_recv_node_self]; simp [react, hready, hmux, hqq]
        · rw [hq v hv]
      · simp only
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
        rw [Finset.sum_congr rfl fun v hv => by rw [hq v (Finset.ne_of_mem_erase hv)]]
        rw [next_recv_node_self]
        simp only [react, hready, hmux, ite_true, hqq]
        have e1 : ((a :: rest : List ℕ) : Multiset ℕ) = {a} + ↑rest := by simp
        have e2 : ((c.ds ++ [a] : List ℕ) : Multiset ℕ) = ↑c.ds + {a} := by
          rw [← Multiset.coe_add]; rfl
        rw [e1, e2]; abel

end ringFacts

/-! ### The simulation invariant -/

lemma map_enc_tag (v : V) (out : List (V × M)) :
    Multiset.map K.enc (Protocol.tag v out) = (encOut K v out : Multiset ℕ) := by
  simp [Protocol.tag, encOut, Function.comp_def]

lemma count_filterMap_dec {l : List ℕ} (hl : ∀ a ∈ l, ∃ y, a = K.enc y) (x : V × V × M) :
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

lemma dlv_dst {C : SimConfig R P} {v : V} {y : V × V × M} (hy : y ∈ C.dlv K v) : y.2.1 = v := by
  simp only [SimConfig.dlv, List.mem_filter, decide_eq_true_eq] at hy; exact hy.2

variable (K) in
/-- The invariant of the simulator. -/
structure SimInv (τ₀ : ZMod R.L) (C : SimConfig R P) : Prop where
  ring : Reach R τ₀ (fun v => encOut K v (P.init v).2) C.ring
  nproc_le : ∀ v, C.nproc v ≤ (C.dlv K v).length
  mass : Multiset.map K.enc C.sentMS =
    (C.ring.ds : Multiset ℕ) + ∑ v, ((C.ring.node v).q : Multiset ℕ)
  sim : ∃ D : P.Config, P.Reach D ∧ D.st = C.pst ∧ D.tr = C.tr ∧ D.net + C.procMS K = C.sentMS

lemma SimInv.inv {τ₀ : ZMod R.L} {C : SimConfig R P} (h : SimInv K τ₀ C) : Inv C.ring :=
  h.ring.inv fun v a ha => by
    simp only [encOut, List.mem_map] at ha; obtain ⟨o, -, rfl⟩ := ha; exact K.enc_pos _

lemma simInv_init (τ₀ : ZMod R.L) : SimInv K τ₀ (simInit R P K τ₀) := by
  refine ⟨Relation.ReflTransGen.refl, fun v => by simp [simInit, SimConfig.dlv, init], ?_,
    ⟨P.initCfg, .refl, rfl, rfl, ?_⟩⟩
  · have := map_sum (Multiset.mapAddMonoidHom K.enc) (fun v => Protocol.tag v (P.init v).2)
      Finset.univ
    simp only [Multiset.mapAddMonoidHom_apply] at this
    simp [SimConfig.sentMS, simInit, init, this, map_enc_tag]
  · simp [SimConfig.procMS, SimConfig.sentMS, simInit, Protocol.initCfg]

/-- The key counting step: the next message to process at `v` is still in transit in the
noiseless execution. -/
lemma SimInv.count_lt {τ₀ : ZMod R.L} {C : SimConfig R P} (hI : SimInv K τ₀ C) {v : V}
    (h : C.nproc v < (C.dlv K v).length) :
    (C.procMS K).count (C.dlv K v)[C.nproc v] < C.sentMS.count (C.dlv K v)[C.nproc v] := by
  set x := (C.dlv K v)[C.nproc v]
  have hxv : x.2.1 = v := dlv_dst (List.getElem_mem h)
  have h1 : (C.procMS K).count x = ((C.dlv K v).take (C.nproc v)).count x := by
    simp only [SimConfig.procMS, Multiset.count_sum', Multiset.coe_count]
    rw [Finset.sum_eq_single v]
    · intro w _ hw
      rw [List.count_eq_zero]
      intro hx; exact hw (by rw [← dlv_dst (List.mem_of_mem_take hx), hxv])
    · simp
  have h2 : (C.dlv K v).take (C.nproc v + 1) = (C.dlv K v).take (C.nproc v) ++ [x] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl
  have hrange : ∀ a ∈ C.ring.ds, ∃ y, a = K.enc y := by
    intro a ha
    have : a ∈ Multiset.map K.enc C.sentMS := by
      rw [hI.mass]; exact Multiset.mem_add.2 (Or.inl (by simpa using ha))
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 this; exact ⟨y, rfl⟩
  have hpre : (C.ring.node v).log <+: C.ring.ds := hI.inv.log_prefix v
  have h3 : ((C.dlv K v).take (C.nproc v + 1)).count x ≤ C.ring.ds.count (K.enc x) := by
    rw [← count_filterMap_dec hrange]
    refine List.Sublist.count_le _ ?_
    refine (List.take_sublist _ _).trans ?_
    refine (List.filter_sublist).trans ?_
    exact (hpre.filterMap K.dec).sublist
  have h4 : C.ring.ds.count (K.enc x) ≤ C.sentMS.count x := by
    rw [← Multiset.count_map_eq_count' _ _ K.enc_injective, hI.mass, Multiset.count_add]
    simp
  rw [h1]; rw [h2, List.count_append] at h3; simp at h3; omega

lemma take_eq_of_prefix' {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) {k : ℕ}
    (hk : k ≤ l₁.length) : l₂.take k = l₁.take k := by
  obtain ⟨t, rfl⟩ := h; exact List.take_append_of_le_length hk

lemma tag_append (v : V) (l₁ l₂ : List (V × M)) :
    Protocol.tag v (l₁ ++ l₂) = Protocol.tag v l₁ + Protocol.tag v l₂ := by
  simp [Protocol.tag]

lemma simInv_ring {τ₀ : ZMod R.L} {C : SimConfig R P} (hI : SimInv K τ₀ C) {l : Label V}
    (hen : SimEnabled K C (.ring l)) : SimInv K τ₀ (simNext K C (.ring l)) := by
  have hpush : ∀ u a, l ≠ .push u a := by rintro u a rfl; exact hen
  have hen' : Enabled R C.ring l := by cases l <;> first | exact hen | exact absurd rfl (hpush _ _)
  set C' := simNext K C (.ring l)
  have hring : C'.ring = next R C.ring l := rfl
  have hdlv : ∀ v, C.dlv K v <+: C'.dlv K v := fun v =>
    ((log_prefix_next l v).filterMap K.dec).filter _
  have hproc : C'.procMS K = C.procMS K := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [show C'.nproc v = C.nproc v from rfl, take_eq_of_prefix' (hdlv v) (hI.nproc_le v)]
  obtain ⟨D, hD, hst, htr, hnet⟩ := hI.sim
  exact ⟨hI.ring.tail ⟨l, hen', rfl⟩, fun v => (hI.nproc_le v).trans (hdlv v).length_le,
    by rw [show C'.sentMS = C.sentMS from rfl, hI.mass, hring, mass_next l hpush],
    ⟨D, hD, hst, htr, by rw [hproc]; exact hnet⟩⟩

lemma pushAll_log (c : Config V R.L) (v w : V) (l : List ℕ) :
    ((pushAll c v l).node w).log = (c.node w).log := by
  by_cases hw : w = v
  · subst hw; simp [pushAll]
  · simp [pushAll, hw]

lemma simInv_proc {τ₀ : ZMod R.L} {C : SimConfig R P} (hI : SimInv K τ₀ C) {v : V}
    (h : C.nproc v < (C.dlv K v).length) : SimInv K τ₀ (simNext K C (.proc v)) := by
  set x := (C.dlv K v)[C.nproc v] with hxdef
  have hxv : x.2.1 = v := dlv_dst (List.getElem_mem h)
  set r := P.recv v (C.pst v) x.1 x.2.2 with hr
  have hC' : simNext K C (.proc v) =
      { ring := pushAll C.ring v (encOut K v r.2)
        pst := Function.update C.pst v r.1
        nproc := Function.update C.nproc v (C.nproc v + 1)
        tr := Function.update C.tr v (C.tr v ++ [.recv x.1 x.2.2] ++ Protocol.sends r.2)
        out := Function.update C.out v (C.out v ++ r.2) } := by
    simp only [simNext, dite_eq_left h]; rfl
  set C' := simNext K C (.proc v)
  have e_ring : C'.ring = pushAll C.ring v (encOut K v r.2) := by rw [hC']
  have e_pst : C'.pst = Function.update C.pst v r.1 := by rw [hC']
  have e_nproc : C'.nproc = Function.update C.nproc v (C.nproc v + 1) := by rw [hC']
  have e_tr : C'.tr =
      Function.update C.tr v (C.tr v ++ [.recv x.1 x.2.2] ++ Protocol.sends r.2) := by rw [hC']
  have e_out : C'.out = Function.update C.out v (C.out v ++ r.2) := by rw [hC']
  have hdlv : ∀ w, C'.dlv K w = C.dlv K w := fun w => by
    simp only [SimConfig.dlv, e_ring, pushAll_log]
  have hsent : C'.sentMS = C.sentMS + Protocol.tag v r.2 := by
    simp only [SimConfig.sentMS, e_out]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    rw [Finset.sum_congr rfl fun w hw => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]]
    simp [tag_append, add_assoc]
  have hproc : C'.procMS K = C.procMS K + {x} := by
    simp only [SimConfig.procMS, hdlv]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    rw [Finset.sum_congr rfl fun w hw => by
      rw [e_nproc, Function.update_of_ne (Finset.ne_of_mem_erase hw)]]
    have htk : (((C.dlv K v).take (C.nproc v + 1) : List _) : Multiset _) =
        ((C.dlv K v).take (C.nproc v) : Multiset _) + {x} := by
      rw [List.take_add_one, List.getElem?_eq_getElem h, ← Multiset.coe_add]; rfl
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
  · rw [hdlv]; by_cases hw : w = v
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

theorem SimReach.inv {τ₀ : ZMod R.L} {C : SimConfig R P} (h : SimReach R P K τ₀ C) :
    SimInv K τ₀ C := by
  induction h with
  | refl => exact simInv_init τ₀
  | tail _ hs ih =>
    obtain ⟨l, hen, rfl⟩ := hs
    cases l with
    | ring l => exact simInv_ring ih hen
    | proc v => exact simInv_proc ih hen

/-- **Theorem 6 of [CCGS22] (= Theorem 12 of the full version), safety: Algorithm 3 simulates
`π` over the fully-defective graph `G` given a Robbins cycle.** In every reachable configuration
`C` of the simulator `π̂` (Algorithm 3 with the black box `π`), every node's copy of `π` has the
state and the local transcript of the same node in some reachable configuration `D` of `π` over
the noiseless network; the messages in transit in `D` are exactly the messages sent by `π` in `C`
and not yet processed by their destination. -/
theorem simulation {τ₀ : ZMod R.L} {C : SimConfig R P} (h : SimReach R P K τ₀ C) :
    ∃ D : P.Config, P.Reach D ∧ (∀ v, D.st v = C.pst v ∧ D.tr v = C.tr v) ∧
      D.net + C.procMS K = C.sentMS := by
  obtain ⟨D, hD, hst, htr, hnet⟩ := h.inv.sim
  exact ⟨D, hD, fun v => ⟨congrFun hst v, congrFun htr v⟩, hnet⟩

end Podc.FullyDefective.RobbinsSim
