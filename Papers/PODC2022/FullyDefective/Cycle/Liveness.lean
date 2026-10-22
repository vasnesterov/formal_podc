import Papers.PODC2022.FullyDefective.Cycle.Simulation
import Papers.PODC2022.FullyDefective.Cycle.Progress
import Cslib.Foundations.Data.Nat.Descent

/-!
# Theorem 4 of [CCGS22] (= Theorem 6 of the full version), liveness; Lemma 5(1), Remark 2

Executions of the simulator (Algorithm 1 with the black box `π`) are infinite sequences of
configurations in which every step is a step of the simulator or a stutter. They are *weakly
fair*: a step (a step of the ring layer at a node, or `π` processing a delivered message) that is
enabled from some time on is eventually taken. This is the paper's assumption that every pulse is
eventually delivered and that `π`'s actions take finite time.

* `rank_unbounded` (Lemma 5(1), progress): while some queue is non-empty, epochs keep being
  completed.
* `no_starvation` (Remark 2): every message in a queue is eventually broadcast.
* `liveness` (Theorem 6, liveness): every message sent by `π` is eventually processed by its
  destination. Together with `simulation`, every fair execution of the simulator simulates a fair
  execution of `π` over the noiseless network.
* `quiescence` (end of the proof of Theorem 6): when no step of the simulator is enabled, `π` has
  reached quiescence in the simulated noiseless execution too.
-/

namespace Podc.FullyDefective.Cycle

variable {n : ℕ} [NeZero n]

/-! ### Pushes do not affect the ring's control state -/

section pushAll

variable {c : Config n} {v : ZMod n} {l : List ℕ}

@[simp] lemma pushAll_ph (w : ZMod n) : ((pushAll c v l).node w).ph = (c.node w).ph := by
  by_cases hw : w = v
  · subst hw; simp [pushAll]
  · simp [pushAll, hw]

@[simp] lemma pushAll_tok (w : ZMod n) : ((pushAll c v l).node w).tok = (c.node w).tok := by
  by_cases hw : w = v
  · subst hw; simp [pushAll]
  · simp [pushAll, hw]

@[simp] lemma pushAll_cwS : (pushAll c v l).cwS = c.cwS := rfl
@[simp] lemma pushAll_cwR : (pushAll c v l).cwR = c.cwR := rfl
@[simp] lemma pushAll_ccwS : (pushAll c v l).ccwS = c.ccwS := rfl
@[simp] lemma pushAll_ccwR : (pushAll c v l).ccwR = c.ccwR := rfl
@[simp] lemma pushAll_ds : (pushAll c v l).ds = c.ds := rfl
@[simp] lemma pushAll_hold : (pushAll c v l).hold = c.hold := rfl

lemma pushAll_q (w : ZMod n) :
    ((pushAll c v l).node w).q = (c.node w).q ++ if w = v then l else [] := by
  by_cases hw : w = v
  · subst hw; simp [pushAll]
  · simp [pushAll, hw]

lemma rank_pushAll : rank (pushAll c v l) = rank c := by simp [rank]

lemma μ_pushAll : μ (pushAll c v l) = μ c := by
  unfold μ ccwPot cwTop; simp; rfl

lemma enabled_pushAll {l' : Label n} (hl : ∀ u a, l' ≠ .push u a) (h : Enabled c l') :
    Enabled (pushAll c v l) l' := by
  cases l' with
  | push u a => exact absurd rfl (hl u a)
  | start u =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨by rw [pushAll_ph]; exact h1, ?_⟩
    rw [pushAll_q]; simp [h2]
  | cw u => obtain ⟨h1, h2⟩ := h; exact ⟨by rw [pushAll_ph]; exact h1, h2⟩
  | ccw u => obtain ⟨h1, h2⟩ := h; exact ⟨by rw [pushAll_ph]; exact h1, h2⟩

end pushAll

/-! ### The token does not pass a node with a non-empty queue (Remark 2) -/

section ahead

variable {c : Config n}

/-- The released token has not passed `w`. -/
def TokenAhead (w : ZMod n) (c : Config n) : Prop :=
  TokStage c → (c.node c.hold).tok = false → ∃ p, c.ccwIn p ∧ cdist c.hold p ≤ cdist c.hold w

lemma cdist_lt_of {T w u : ZMod n} (h : cdist T w ≤ cdist T u) (hwu : w ≠ u) :
    cdist w u < cdist T u := by
  have hlt : cdist T w < cdist T u := lt_of_le_of_ne h (fun e => hwu (cdist_injective _ e))
  have hwT : w ≠ T := by
    rintro rfl; have := cdist_le w u; rw [cdist_self] at hlt; omega
  have hw : cdist T w = (T - w).val := by simp [cdist, hwT]
  have hpos := cdist_pos T w
  have hu' : ∀ huT : u ≠ T, cdist T u = (T - u).val := fun huT => by simp [cdist, huT]
  unfold cdist; rw [if_neg (Ne.symm hwu)]
  by_cases huT : u = T
  · rw [if_pos huT]; exact ZMod.val_lt _
  · rw [if_neg huT]
    rw [hu' huT] at hlt; rw [hw] at hlt hpos
    have e : w - u = (T - u) - (T - w) := by ring
    rw [e, ZMod.val_sub hlt.le]; omega

lemma tokenAhead_of_not_tok (h : Inv c) (hT : ¬ TokStage c) (w : ZMod n) : TokenAhead w c :=
  fun H => absurd H hT

/-- `TokenAhead w` is preserved by every step of the ring layer, as long as `w` keeps a non-empty
queue. -/
lemma tokenAhead_step (h : Inv c) {w : ZMod n} (hw : (c.node w).q ≠ []) (hA : TokenAhead w c)
    {l : Label n} (hen : Enabled c l) : TokenAhead w (next c l) := by
  have h' := inv_step h hen
  cases l with
  | push u a =>
    intro H ht
    have hn : ∀ v, ((next c (.push u a)).node v).ph = (c.node v).ph ∧
        ((next c (.push u a)).node v).tok = (c.node v).tok := by
      intro v; by_cases hv : v = u <;> simp [hv]
    have H' : TokStage c := by
      rw [h.tokStage_iff]; rw [h'.tokStage_iff, next_push_hold, (hn _).1] at H; exact H
    obtain ⟨p, hp, hd⟩ := hA H' (by rw [next_push_hold, (hn _).2] at ht; exact ht)
    exact ⟨p, hp, hd⟩
  | start u =>
    intro H ht
    have hidle := hen.1
    have H' : TokStage c := by
      rw [h.tokStage_iff]; rw [h'.tokStage_iff] at H
      by_cases hTu : c.hold = u
      · rw [hTu, hidle]; trivial
      · simpa [hTu] using H
    have htok : (c.node c.hold).tok = false := by
      by_cases hTu : c.hold = u
      · simpa [hTu] using ht
      · simpa [hTu] using ht
    exact hA H' htok
  | cw u =>
    intro H ht
    obtain ⟨hr, hin⟩ := hen
    set c' := next c (.cw u)
    have hnode : ∀ v, v ≠ u → c'.node v = c.node v := fun v hv => cw_node_ne hv
    have hTok : TokStage c := by
      rw [h.tokStage_iff]; rw [h'.tokStage_iff, show c'.hold = c.hold from rfl] at H
      by_cases hTu : c.hold = u
      · rw [hTu] at H ⊢
        simp only [c', next_cw_node, ↓reduceIte] at H
        rcases hs : (c.node u).ph with _ | _ | _ | k | ⟨d, r⟩ | d <;>
          simp only [onCW, hs] at H <;> simp [Phase.IsTok] at H ⊢
        split_ifs at H <;> exact H
      · rwa [hnode _ hTu] at H
    cases htok : (c.node c.hold).tok
    · obtain ⟨p, hp, hd⟩ := hA hTok htok
      exact ⟨p, cw_ccwIn_of hp, hd⟩
    · -- release of the token by `T = u`
      have hTu : c.hold = u := by
        by_contra hTu; rw [show c'.hold = c.hold from rfl, hnode _ hTu, htok] at ht; cases ht
      have hph : (c.node u).ph = .idle ∨ (c.node u).ph = .waitReq := by
        have h1 := hTok.isTok u
        have h2 := ((h.1.tok u).1 (hTu ▸ htok)).2
        revert h1 h2; rcases (c.node u).ph <;> simp [Phase.IsTok, Phase.Holding]
      have h1 : (onCW (c.node u)).2.2 = 1 := by
        rw [← hTu] at hph ⊢; rcases hph with hp | hp <;> simp [onCW, hp, htok]
      refine ⟨c.hold - 1, ?_, ?_⟩
      · exact (cw_release_ccwIn (hTok.held htok) h1 h.1 _).2 (by rw [hTu])
      · rw [show c'.hold = c.hold from rfl, cdist_sub_one_self]; exact cdist_pos _ _
  | ccw u =>
    intro H ht
    obtain ⟨hr, hin⟩ := hen
    set c' := next c (.ccw u)
    by_cases hcap : ∃ a, capture? (c.node u) = some a
    · exfalso
      obtain ⟨a, ha⟩ := hcap
      have hh : c'.hold = u := by simp only [c', next_ccw_hold, ha]
      have hph : (c.node u).ph = .ready := by
        unfold capture? at ha; split at ha
        · assumption
        · cases ha
      obtain ⟨a', q', hq'⟩ : ∃ a' q', (c.node u).q = a' :: q' := by
        unfold capture? at ha; rw [hph] at ha; split at ha
        · exact ⟨_, _, by assumption⟩
        · cases ha
      have : (c'.node u).ph = .send a' 0 := by simp [c', onCCW, hph, hq']
      rw [h'.tokStage_iff, hh, this] at H; exact H
    · have hcap' : capture? (c.node u) = none := by
        cases hc : capture? (c.node u) with
        | none => rfl
        | some a => exact absurd ⟨a, hc⟩ hcap
      have hh : c'.hold = c.hold := by simp only [c', next_ccw_hold, hcap']
      rw [h'.tokStage_iff, hh] at H
      rcases h.2 with ⟨pre, d, r, H0⟩ | ⟨pre, d, H0⟩ | H0
      · exact absurd hin (H0.noIn u)
      · exfalso
        by_cases hTu : c.hold = u
        · have ho : (onCCW (c.node u)).1.tok = (c.node u).tok := by
            rw [← hTu]; simp [onCCW, H0.ph_hold]
          have ht' : (c'.node u).tok = false := by rw [← hTu, ← hh]; exact ht
          simp only [c', next_ccw_node, ↓reduceIte, ho] at ht'
          have := (h.1.tok c.hold).2 ⟨rfl, by rw [H0.ph_hold]; trivial⟩
          rw [hTu] at this; rw [this] at ht'; cases ht'
        · rw [ccw_node_ne hTu, H0.ph_hold] at H; exact H
      · have hphu : (c.node u).ph = .ready := by
          have := H0.isTok u; revert this hr
          rcases (c.node u).ph <;> simp [Phase.IsTok, Phase.ccwReady]
        have hqe : (c.node u).q = [] := by
          cases hq : (c.node u).q
          · rfl
          · simp [capture?, hphu, hq] at hcap'
        have htokT : (c.node c.hold).tok = false := by
          cases ht' : (c.node c.hold).tok
          · rfl
          · exact absurd hin (H0.held ht' u)
        obtain ⟨p, hp, hd⟩ := hA H0 htokT
        have hpu : p = u := h.1.ccwUniq p u hp hin
        subst hpu
        have hwp : w ≠ p := by rintro rfl; exact hw hqe
        have hlt : cdist c.hold p < cdist c.hold w :=
          lt_of_le_of_ne hd (fun e => hwp (cdist_injective _ e).symm)
        have hpT : p ≠ c.hold := by
          rintro rfl; have := cdist_le c.hold w; rw [cdist_self] at hlt; omega
        have h1 : (onCCW (c.node p)).2.2 = 1 := by simp [onCCW, hphu, hqe]
        refine ⟨p - 1, ccw_send_in h.1 hin h1, ?_⟩
        rw [hh, cdist_sub_one hpT]; omega

/-- A capture by `v` while the token has not passed `w`: `v` is not farther than `w`. -/
lemma capture_cdist (h : Inv c) {w v : ZMod n} (hA : TokenAhead w c) (hen : Enabled c (.ccw v))
    {a : ℕ} (ha : capture? (c.node v) = some a) : cdist c.hold v ≤ cdist c.hold w := by
  obtain ⟨hr, hin⟩ := hen
  have hph : (c.node v).ph = .ready := by
    unfold capture? at ha; split at ha
    · assumption
    · cases ha
  have hTok : TokStage c := by
    rcases h.2 with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
    · exact absurd hin (H.noIn v)
    · exfalso; rcases (H.target v hin).2 with h1 | h1
      · rw [h1, H.ph_hold] at hph; cases hph
      · by_cases hu : v = c.hold
        · rw [hu, H.ph_hold] at hph; cases hph
        · rcases H.others v hu with ⟨-, h3⟩ | ⟨h3, -⟩
          · rw [hph] at h3; cases h3
          · omega
    · exact H
  have htokT : (c.node c.hold).tok = false := by
    cases ht' : (c.node c.hold).tok
    · rfl
    · exact absurd hin (hTok.held ht' v)
  obtain ⟨p, hp, hd⟩ := hA hTok htokT
  rw [← h.1.ccwUniq p v hp hin]; exact hd

/-- `ds` only changes at a capture, which leads to a data stage held by the capturer. -/
lemma ds_change {l : Label n} (hl : ∀ u a, l ≠ .push u a) (hds : (next c l).ds ≠ c.ds) :
    ∃ v a, l = .ccw v ∧ capture? (c.node v) = some a ∧ (next c l).ds = c.ds ++ [a] ∧
      (next c l).hold = v := by
  cases l with
  | push u a => exact absurd rfl (hl u a)
  | start u => exact absurd rfl hds
  | cw u => exact absurd rfl hds
  | ccw v =>
    cases hc : capture? (c.node v) with
    | none => exfalso; apply hds; simp only [next_ccw_ds, hc]
    | some a => exact ⟨v, a, rfl, hc, by simp only [next_ccw_ds, hc],
        by simp only [next_ccw_hold, hc]⟩

end ahead

lemma q_next_of_ds {c : Config n} {l : Label n} (hl : ∀ u a, l ≠ .push u a)
    (hds : (next c l).ds = c.ds) (w : ZMod n) : ((next c l).node w).q = (c.node w).q := by
  cases l with
  | push u a => exact absurd rfl (hl u a)
  | start u => by_cases hw : w = u <;> simp [hw]
  | cw u => by_cases hw : w = u <;> simp [hw]
  | ccw u =>
    by_cases hw : w = u
    · subst hw; simp only [next_ccw_node, ↓reduceIte]
      cases hc : capture? (c.node w) with
      | some a => exfalso; rw [next_ccw_ds, hc] at hds; simpa using hds
      | none =>
        rcases hs : (c.node w).ph <;> simp [onCCW, hs]
        cases hq : (c.node w).q
        · simp [hq]
        · simp [capture?, hs, hq] at hc
    · simp [hw]

/-! ### FIFO queues: the order in which a node's messages are broadcast -/

section fifo

variable {M : Type*} {P : Protocol (ZMod n) M} {K : Coding (ZMod n) M} [DecidableEq M]

variable (K) in
/-- The number of messages of `u` broadcast (captured) so far. -/
def SimConfig.kcap (C : SimConfig P) (u : ZMod n) : ℕ :=
  ((decs K C.ring.ds).filter (fun x => x.1 = u)).length

variable (K) in
/-- FIFO invariant: the messages of `u` broadcast so far are the first `kcap u` messages sent by
`π` at `u`; the others are in `Q_u`, in order. -/
structure SimFifo (C : SimConfig P) : Prop where
  le : ∀ u, C.kcap K u ≤ (C.out u).length
  bc : ∀ u, (decs K C.ring.ds).filter (fun x => x.1 = u) =
    ((C.out u).take (C.kcap K u)).map (fun o => (u, o.1, o.2))
  q : ∀ u, (C.ring.node u).q = encOut K u ((C.out u).drop (C.kcap K u))

lemma decs_append (l l' : List ℕ) : decs K (l ++ l') = decs K l ++ decs K l' := by
  simp [decs]

lemma decs_encOut (v : ZMod n) (out : List (ZMod n × M)) :
    decs K (encOut K v out) = out.map (fun o => (v, o.1, o.2)) := by
  induction out with
  | nil => simp [decs, encOut]
  | cons o out ih => simp only [decs, encOut, List.map_cons, List.filterMap_cons, K.dec_enc] at ih ⊢; rw [ih]

lemma simFifo_init (T₀ : ZMod n) : SimFifo K (simInit P K T₀) := by
  refine ⟨fun u => ?_, fun u => ?_, fun u => ?_⟩ <;>
    simp [SimConfig.kcap, simInit, init, decs]

lemma simFifo_ring {C : SimConfig P} (hF : SimFifo K C) {l : Label n} (hl : ∀ u a, l ≠ .push u a) :
    SimFifo K (simNext K C (.ring l)) := by
  set C' := simNext K C (.ring l)
  have hring : C'.ring = next C.ring l := rfl
  have hout : C'.out = C.out := rfl
  by_cases hds : (next C.ring l).ds = C.ring.ds
  · have hk : ∀ u, C'.kcap K u = C.kcap K u := fun u => by
      simp only [SimConfig.kcap, hring, hds]
    refine ⟨fun u => by rw [hk, hout]; exact hF.le u, fun u => by rw [hk, hout, hring, hds]; exact hF.bc u,
      fun u => by rw [hk, hout, hring, q_next_of_ds hl hds]; exact hF.q u⟩
  · obtain ⟨v, a, rfl, ha, hds', hh'⟩ := ds_change hl hds
    -- the capturer's queue
    have hph : (C.ring.node v).ph = .ready := by
      unfold capture? at ha; split at ha
      · assumption
      · cases ha
    obtain ⟨q', hq'⟩ : ∃ q', (C.ring.node v).q = a :: q' := by
      cases hq : (C.ring.node v).q with
      | nil => simp [capture?, hph, hq] at ha
      | cons a' q'' => simp [capture?, hph, hq] at ha; subst ha; exact ⟨q'', rfl⟩
    have hFq := hF.q v; rw [hq'] at hFq
    obtain ⟨o, rest, hdrop⟩ : ∃ o rest, (C.out v).drop (C.kcap K v) = o :: rest := by
      cases hd : (C.out v).drop (C.kcap K v) with
      | nil => rw [hd] at hFq; simp [encOut] at hFq
      | cons o rest => exact ⟨o, rest, rfl⟩
    rw [hdrop] at hFq; simp only [encOut, List.map_cons, List.cons.injEq] at hFq
    obtain ⟨hao, hq'r⟩ := hFq
    have hdec : decs K C'.ring.ds = decs K C.ring.ds ++ [(v, o.1, o.2)] := by
      rw [hring, hds', decs_append, hao]; simp [decs, K.dec_enc]
    have hk : ∀ u, C'.kcap K u = C.kcap K u + if u = v then 1 else 0 := fun u => by
      simp only [SimConfig.kcap, hdec, List.filter_append, List.length_append]
      by_cases hu : u = v
      · subst hu; simp
      · simp [Ne.symm hu, hu]
    have hlt : C.kcap K v < (C.out v).length := by
      have := congrArg List.length hdrop; simp at this; omega
    refine ⟨fun u => ?_, fun u => ?_, fun u => ?_⟩
    · rw [hk, hout]; by_cases hu : u = v
      · subst hu; simp; omega
      · simp only [hu, ↓reduceIte, add_zero]; exact hF.le u
    · rw [hdec, hk, hout, List.filter_append, hF.bc u]
      by_cases hu : u = v
      · subst hu; simp only [↓reduceIte, List.filter_cons, decide_true, List.filter_nil]
        rw [List.take_succ, List.getElem?_eq_getElem hlt]
        have : (C.out u)[C.kcap K u] = o := by
          have := congrArg List.head? hdrop
          rw [List.head?_drop] at this; simp only [List.head?_cons] at this
          rw [List.getElem?_eq_getElem hlt] at this; exact Option.some.inj this
        simp [this]
      · simp [hu, Ne.symm hu]
    · rw [hk, hout, hring]
      by_cases hu : u = v
      · subst hu
        have : ((next C.ring (.ccw u)).node u).q = q' := by
          simp [onCCW, hph, hq']
        rw [this, hq'r]; simp only [↓reduceIte]
        rw [← List.drop_drop, hdrop]; simp [encOut]
      · rw [ccw_node_ne hu]; simp only [hu, ↓reduceIte, add_zero]; exact hF.q u

lemma simFifo_proc [NeZero n] {C : SimConfig P} (hF : SimFifo K C) {v : ZMod n}
    (h : C.nproc v < (C.rcv K v).length) : SimFifo K (simNext K C (.proc v)) := by
  set x := (C.rcv K v)[C.nproc v]
  set r := P.recv v (C.pst v) x.1 x.2.2
  have hC' : simNext K C (.proc v) =
      { ring := pushAll C.ring v (encOut K v r.2)
        pst := Function.update C.pst v r.1
        nproc := Function.update C.nproc v (C.nproc v + 1)
        tr := Function.update C.tr v (C.tr v ++ [.recv x.1 x.2.2] ++ Protocol.sends r.2)
        out := Function.update C.out v (C.out v ++ r.2) } := by
    simp only [simNext, dif_pos h]; rfl
  have hk : ∀ u, SimConfig.kcap K (simNext K C (.proc v)) u = C.kcap K u := fun u => by
    rw [hC']; rfl
  have hout' : (simNext K C (.proc v)).out = Function.update C.out v (C.out v ++ r.2) := by
    rw [hC']
  have hring' : (simNext K C (.proc v)).ring = pushAll C.ring v (encOut K v r.2) := by rw [hC']
  refine ⟨fun u => ?_, fun u => ?_, fun u => ?_⟩
  · rw [hk, hout']; by_cases hu : u = v
    · subst hu; simp; have := hF.le u; omega
    · simp [hu]; exact hF.le u
  · rw [hk, hout', hring', pushAll_ds]
    by_cases hu : u = v
    · subst hu; simp only [Function.update_self]
      rw [List.take_append_of_le_length (hF.le u)]; exact hF.bc u
    · simp only [Function.update_of_ne hu]; exact hF.bc u
  · rw [hk, hout', hring', pushAll_q]
    by_cases hu : u = v
    · subst hu; simp only [Function.update_self, ↓reduceIte]
      rw [List.drop_append_of_le_length (hF.le u), hF.q u]; simp [encOut]
    · simp only [Function.update_of_ne hu, hu, ↓reduceIte, List.append_nil]; exact hF.q u

end fifo

/-! ### Executions -/

section exec

variable {M : Type*} {P : Protocol (ZMod n) M} {K : Coding (ZMod n) M} [DecidableEq M]

variable (P K) in
/-- An execution of the simulator: it starts in the initial configuration and every step is a
step of the simulator or a stutter. -/
structure SimExec (T₀ : ZMod n) (e : ℕ → SimConfig P) : Prop where
  init : e 0 = simInit P K T₀
  step : ∀ t, SimStep K (e t) (e (t + 1)) ∨ e (t + 1) = e t

variable (K) in
/-- Weak fairness: a step of the simulator (a step of the ring layer at a node, or `π` processing a
delivered message at a node) that is enabled from some time on is eventually taken. -/
def WeakFair (e : ℕ → SimConfig P) : Prop :=
  ∀ l t, (∀ s ≥ t, SimEnabled K (e s) l) →
    ∃ s ≥ t, SimEnabled K (e s) l ∧ e (s + 1) = simNext K (e s) l

variable (K) in
/-- Everything we know about reachable configurations. -/
structure Good (T₀ : ZMod n) (C : SimConfig P) : Prop where
  sim : SimInv K T₀ C
  fifo : SimFifo K C
  inv : Inv C.ring
  inv2 : Inv2 C.ring

lemma good_init (T₀ : ZMod n) : Good K T₀ (simInit P K T₀) := by
  have h := (Reach.inv2 (c := (simInit P K T₀).ring) (T₀ := T₀)
    (qs := fun v => encOut K v (P.init v).2) (fun v a ha => by
      simp only [encOut, List.mem_map] at ha; obtain ⟨o, -, rfl⟩ := ha; exact K.enc_pos _)
    Relation.ReflTransGen.refl)
  exact ⟨simInv_init T₀, simFifo_init T₀, h.1, h.2⟩

lemma Good.step {T₀ : ZMod n} {C C' : SimConfig P} (hG : Good K T₀ C) (hs : SimStep K C C') :
    Good K T₀ C' := by
  obtain ⟨l, hen, rfl⟩ := hs
  cases l with
  | ring l =>
    have hl : ∀ u a, l ≠ .push u a := by rintro u a rfl; exact hen
    have hen' : Enabled C.ring l := by cases l <;> first | exact hen | exact absurd rfl (hl _ _)
    exact ⟨simInv_ring hG.sim hen, simFifo_ring hG.fifo hl, inv_step hG.inv hen',
      inv2_step hG.inv hG.inv2 hen'⟩
  | proc v =>
    have hI := simInv_proc hG.sim hen
    have h := hI.ring.inv2 (fun v a ha => by
      simp only [encOut, List.mem_map] at ha; obtain ⟨o, -, rfl⟩ := ha; exact K.enc_pos _)
    exact ⟨hI, simFifo_proc hG.fifo hen, h.1, h.2⟩

lemma SimExec.good {T₀ : ZMod n} {e : ℕ → SimConfig P} (he : SimExec P K T₀ e) (t : ℕ) :
    Good K T₀ (e t) := by
  induction t with
  | zero => rw [he.init]; exact good_init T₀
  | succ t ih =>
    rcases he.step t with hs | hs
    · exact ih.step hs
    · rw [hs]; exact ih

/-- The three kinds of steps of an execution. -/
lemma SimExec.cases {T₀ : ZMod n} {e : ℕ → SimConfig P} (he : SimExec P K T₀ e) (t : ℕ) :
    e (t + 1) = e t ∨
    (∃ l, (∀ u a, l ≠ .push u a) ∧ Enabled (e t).ring l ∧ e (t + 1) = simNext K (e t) (.ring l)) ∨
    (∃ v outs, (e (t + 1)).ring = pushAll (e t).ring v outs ∧
      (∀ w, (e t).nproc w ≤ (e (t + 1)).nproc w) ∧
      (∀ w, (e t).out w <+: (e (t + 1)).out w) ∧
      ((e t).nproc v < (e (t + 1)).nproc v)) := by
  rcases he.step t with ⟨l, hen, hs⟩ | hs
  · cases l with
    | ring l =>
      have hl : ∀ u a, l ≠ .push u a := by rintro u a rfl; exact hen
      have hen' : Enabled (e t).ring l := by
        cases l <;> first | exact hen | exact absurd rfl (hl _ _)
      exact Or.inr (Or.inl ⟨l, hl, hen', hs⟩)
    | proc v =>
      right; right
      have hen' : (e t).nproc v < ((e t).rcv K v).length := hen
      simp only [simNext] at hs; rw [dif_pos hen'] at hs
      refine ⟨v, _, by rw [hs], fun w => ?_, fun w => ?_, by rw [hs]; simp⟩
      · rw [hs]; by_cases hw : w = v
        · subst hw; simp
        · simp [hw]
      · rw [hs]; by_cases hw : w = v
        · subst hw; simp
        · simp [hw]
  · exact Or.inl hs

lemma simEnabled_ring_iff {C : SimConfig P} {l : Label n} (hl : ∀ u a, l ≠ .push u a) :
    SimEnabled K C (.ring l) ↔ Enabled C.ring l := by
  cases l with
  | push u a => exact absurd rfl (hl u a)
  | _ => exact Iff.rfl

section mono

variable {T₀ : ZMod n} {e : ℕ → SimConfig P} (he : SimExec P K T₀ e)
include he

/-- Rank and potential along an execution. -/
lemma SimExec.rank_mu_step (t : ℕ) :
    rank (e t).ring < rank (e (t + 1)).ring ∨
      (rank (e (t + 1)).ring = rank (e t).ring ∧ μ (e (t + 1)).ring ≤ μ (e t).ring) := by
  have hG := he.good t
  rcases he.cases t with hs | ⟨l, hl, hen, hs⟩ | ⟨v, outs, hr, -⟩
  · rw [hs]; exact Or.inr ⟨rfl, le_rfl⟩
  · rw [hs]
    rcases progress_step hG.inv hG.inv2 hl hen with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2.le⟩
  · rw [hr, rank_pushAll, μ_pushAll]; exact Or.inr ⟨rfl, le_rfl⟩

lemma SimExec.rank_mono {t s : ℕ} (h : t ≤ s) : rank (e t).ring ≤ rank (e s).ring := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rcases he.rank_mu_step _ with h | h
    · exact ih.trans h.le
    · exact ih.trans h.1.ge

lemma SimExec.ds_prefix_step (t : ℕ) : (e t).ring.ds <+: (e (t + 1)).ring.ds := by
  rcases he.cases t with hs | ⟨l, hl, hen, hs⟩ | ⟨v, outs, hr, -⟩
  · rw [hs]
  · rw [hs]
    by_cases hds : (next (e t).ring l).ds = (e t).ring.ds
    · show _ <+: (next (e t).ring l).ds; rw [hds]
    · obtain ⟨v, a, -, -, hds', -⟩ := ds_change hl hds
      show _ <+: (next (e t).ring l).ds; rw [hds']; exact List.prefix_append _ _
  · rw [hr, pushAll_ds]

lemma SimExec.ds_prefix {t s : ℕ} (h : t ≤ s) : (e t).ring.ds <+: (e s).ring.ds := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (he.ds_prefix_step _)

lemma SimExec.log_prefix_step (t : ℕ) (v : ZMod n) :
    ((e t).ring.node v).log <+: ((e (t + 1)).ring.node v).log := by
  rcases he.cases t with hs | ⟨l, hl, hen, hs⟩ | ⟨w, outs, hr, -⟩
  · rw [hs]
  · rw [hs]; exact log_prefix_next l v
  · rw [hr, pushAll_log]

lemma SimExec.rcv_prefix {t s : ℕ} (h : t ≤ s) (v : ZMod n) :
    (e t).rcv K v <+: (e s).rcv K v := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (((he.log_prefix_step _ v).filterMap K.dec).filter _)

lemma SimExec.nproc_mono {t s : ℕ} (h : t ≤ s) (v : ZMod n) : (e t).nproc v ≤ (e s).nproc v := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine ih.trans ?_
    rcases he.cases _ with hs | ⟨l, hl, hen, hs⟩ | ⟨w, outs, -, hn, -⟩
    · rw [hs]
    · rw [hs]; exact le_rfl
    · exact hn v

lemma SimExec.out_prefix {t s : ℕ} (h : t ≤ s) (v : ZMod n) : (e t).out v <+: (e s).out v := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    refine ih.trans ?_
    rcases he.cases _ with hs | ⟨l, hl, hen, hs⟩ | ⟨w, outs, -, -, ho, -⟩
    · rw [hs]
    · rw [hs]; exact List.prefix_refl _
    · exact ho v

end mono

/-- **Lemma 5(1), progress.** In a weakly fair execution, the ring layer keeps moving to later
stages (token stage → data stage → end stage → next token stage) unless it becomes quiet. -/
theorem rank_progress {T₀ : ZMod n} {e : ℕ → SimConfig P} (he : SimExec P K T₀ e)
    (hf : WeakFair K e) (t : ℕ) :
    (∃ s ≥ t, rank (e t).ring < rank (e s).ring) ∨ ∃ s ≥ t, Quiet (e s).ring := by
  by_contra hcon
  simp only [not_or, not_exists, not_and, not_lt] at hcon
  obtain ⟨hrk, hq⟩ := hcon
  have hrank : ∀ s ≥ t, rank (e s).ring = rank (e t).ring := fun s hs =>
    le_antisymm (hrk s hs) (he.rank_mono hs)
  have hmu : ∀ s ≥ t, μ (e (s + 1)).ring ≤ μ (e s).ring := by
    intro s hs
    rcases he.rank_mu_step s with h | h
    · have := hrank (s + 1) (by omega); rw [hrank s hs] at h; omega
    · exact h.2
  obtain ⟨s0, hs0, hconst⟩ := Nat.eventually_const_of_succ_le (f := fun s => μ (e s).ring) hmu
  -- after `s0` no step of the ring layer happens
  have hnoring : ∀ s ≥ s0, ∀ l, (∀ u a, l ≠ .push u a) → Enabled (e s).ring l →
      e (s + 1) ≠ simNext K (e s) (.ring l) := by
    intro s hs l hl hen heq
    have hG := (he.good s)
    rcases progress_step hG.inv hG.inv2 hl hen with h | ⟨-, h⟩
    · have h1 := hrank s (by omega); have h2 := hrank (s + 1) (by omega)
      rw [heq] at h2; simp only [simNext] at h2; omega
    · have h1 := hconst s hs; have h2 := hconst (s + 1) (by omega)
      rw [heq] at h2; simp only [simNext] at h2; omega
  obtain ⟨l, hl, hen⟩ := ((he.good s0).inv.enabled_or_quiet).resolve_right (hq s0 hs0)
  have hpersist : ∀ s ≥ s0, Enabled (e s).ring l := by
    intro s hs
    induction hs with
    | refl => exact hen
    | step hle ih =>
      rename_i m
      rcases he.cases m with h | ⟨l', hl', hen', h⟩ | ⟨v, outs, hr, -⟩
      · rw [h]; exact ih
      · exact absurd h (hnoring m hle l' hl' hen')
      · rw [hr]; exact enabled_pushAll hl ih
  obtain ⟨s, hs, -, heq⟩ := hf (.ring l) s0 fun s hs =>
    (simEnabled_ring_iff hl).2 (hpersist s hs)
  exact hnoring s hs l hl (hpersist s hs) heq

lemma rank_ge (c : Config n) : 3 * c.ds.length ≤ rank c := by unfold rank; omega

lemma rank_le (c : Config n) : rank c ≤ 3 * c.ds.length + 2 := by
  unfold rank; have : (c.node c.hold).ph.cls ≤ 2 := by
    cases (c.node c.hold).ph <;> simp [Phase.cls]
  omega

lemma Inv.ep_of_rank {c : Config n} (h : Inv c) {K : ℕ} (hK : K ≤ c.ds.length)
    (hr : 3 * K + 2 ≤ rank c) (v : ZMod n) : K ≤ c.ep v := by
  by_cases hd : K + 1 ≤ c.ds.length
  · have := h.ep_ge v; omega
  · have hK' : c.ds.length = K := by omega
    have hcls : (c.node c.hold).ph.cls = 2 := by
      unfold rank at hr; rw [hK'] at hr
      have : (c.node c.hold).ph.cls ≤ 2 := by cases (c.node c.hold).ph <;> simp [Phase.cls]
      omega
    have hT : TokStage c := by
      rcases h.2 with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
      · rw [H.ph_hold] at hcls; simp [Phase.cls] at hcls
      · rw [H.ph_hold] at hcls; simp [Phase.cls] at hcls
      · exact H
    rw [hT.ep_all, hK']

/-- Iterated progress: the rank grows by `m` unless the ring layer becomes quiet. -/
lemma rank_progress_iter {T₀ : ZMod n} {e : ℕ → SimConfig P} (he : SimExec P K T₀ e)
    (hf : WeakFair K e) (t m : ℕ) :
    ∃ s ≥ t, rank (e t).ring + m ≤ rank (e s).ring ∨ Quiet (e s).ring := by
  induction m with
  | zero => exact ⟨t, le_rfl, Or.inl (by omega)⟩
  | succ m ih =>
    obtain ⟨s, hs, h | h⟩ := ih
    · rcases rank_progress he hf s with ⟨s', hs', h'⟩ | ⟨s', hs', h'⟩
      · exact ⟨s', by omega, Or.inl (by omega)⟩
      · exact ⟨s', by omega, Or.inr h'⟩
    · exact ⟨s, hs, Or.inr h⟩

/-- **Lemma 5(1), progress (epochs).** In a weakly fair execution, every node eventually
completes every epoch started so far. -/
theorem epoch_completion {T₀ : ZMod n} {e : ℕ → SimConfig P} (he : SimExec P K T₀ e)
    (hf : WeakFair K e) (t : ℕ) : ∃ s ≥ t, ∀ v, (e t).ring.ds.length ≤ (e s).ring.ep v := by
  obtain ⟨s, hs, h | h⟩ := rank_progress_iter he hf t 2
  · refine ⟨s, hs, fun v => (he.good s).inv.ep_of_rank ((he.ds_prefix hs).length_le) ?_ v⟩
    have := rank_ge (e t).ring; omega
  · refine ⟨s, hs, fun v => ?_⟩
    rw [h.tok.ep_all]; exact (he.ds_prefix hs).length_le

/-- Every message delivered to `π` is eventually processed. -/
theorem processing {T₀ : ZMod n} {e : ℕ → SimConfig P} (he : SimExec P K T₀ e)
    (hf : WeakFair K e) (t : ℕ) (v : ZMod n) :
    ∃ s ≥ t, ((e t).rcv K v).length ≤ (e s).nproc v := by
  suffices ∀ d t', t ≤ t' → ((e t).rcv K v).length - (e t').nproc v ≤ d →
      ∃ s ≥ t', ((e t).rcv K v).length ≤ (e s).nproc v by
    obtain ⟨s, hs, h⟩ := this _ t le_rfl le_rfl; exact ⟨s, hs, h⟩
  intro d
  induction d with
  | zero => intro t' _ h; exact ⟨t', le_rfl, by omega⟩
  | succ d ih =>
    intro t' ht' hd
    by_cases hdone : ((e t).rcv K v).length ≤ (e t').nproc v
    · exact ⟨t', le_rfl, hdone⟩
    have hinc : ∃ s ≥ t', (e t').nproc v < (e s).nproc v := by
      by_contra hcon; push_neg at hcon
      have hc : ∀ s ≥ t', (e s).nproc v = (e t').nproc v := fun s hs =>
        le_antisymm (hcon s hs) (he.nproc_mono hs v)
      have hen : ∀ s ≥ t', SimEnabled K (e s) (.proc v) := by
        intro s hs
        show (e s).nproc v < ((e s).rcv K v).length
        rw [hc s hs]; have := (he.rcv_prefix (ht'.trans hs) v).length_le; omega
      obtain ⟨s, hs, hen', heq⟩ := hf (.proc v) t' hen
      have h1 := hc (s + 1) (by omega); have h2 := hc s hs
      have hen'' : (e s).nproc v < ((e s).rcv K v).length := hen'
      rw [heq] at h1; simp only [simNext, dif_pos hen'', Function.update_self] at h1; omega
    obtain ⟨s, hs, hlt⟩ := hinc
    obtain ⟨s', hs', h⟩ := ih s (ht'.trans hs) (by omega)
    exact ⟨s', by omega, h⟩

lemma tokenAhead_pushAll {c : Config n} {v w : ZMod n} {l : List ℕ} (h : TokenAhead w c) :
    TokenAhead w (pushAll c v l) := by
  intro H ht
  have H' : TokStage c := ⟨fun u => by
      have := H.ep_all u; simpa [Config.ep, pushAll_log] using this,
    fun u => by have := H.isTok u; simpa using this,
    fun ht' => by have := H.held (by simpa using ht'); exact this,
    fun ht' => by have := H.released (by simpa using ht'); exact this⟩
  exact h H' (by simpa using ht)

lemma capture_payload {C : SimConfig P} (hF : SimFifo K C) {v : ZMod n} {a : ℕ}
    (ha : capture? (C.ring.node v) = some a) : ∃ o : ZMod n × M, a = K.enc (v, o.1, o.2) := by
  have hph : (C.ring.node v).ph = .ready := by
    unfold capture? at ha; split at ha
    · assumption
    · cases ha
  obtain ⟨q', hq'⟩ : ∃ q', (C.ring.node v).q = a :: q' := by
    cases hq : (C.ring.node v).q with
    | nil => simp [capture?, hph, hq] at ha
    | cons a' q'' => simp [capture?, hph, hq] at ha; subst ha; exact ⟨q'', rfl⟩
  have hFq := hF.q v; rw [hq'] at hFq
  cases hd : (C.out v).drop (C.kcap K v) with
  | nil => rw [hd] at hFq; simp [encOut] at hFq
  | cons o rest =>
    rw [hd] at hFq; simp only [encOut, List.map_cons, List.cons.injEq] at hFq
    exact ⟨o, hFq.1⟩

lemma kcap_mono_of_prefix {C C' : SimConfig P} (h : C.ring.ds <+: C'.ring.ds) (u : ZMod n) :
    C.kcap K u ≤ C'.kcap K u :=
  ((h.filterMap K.dec).filter _).length_le

/-- **Remark 2, no starvation.** In a weakly fair execution, a node with a non-empty queue
eventually broadcasts the message at its head. -/
theorem no_starvation {T₀ : ZMod n} {e : ℕ → SimConfig P} (he : SimExec P K T₀ e)
    (hf : WeakFair K e) (t : ℕ) (u : ZMod n) (hq : ((e t).ring.node u).q ≠ []) :
    ∃ s ≥ t, (e t).kcap K u < (e s).kcap K u := by
  by_contra hcon; push_neg at hcon
  have hk : ∀ s ≥ t, (e s).kcap K u = (e t).kcap K u := fun s hs =>
    le_antisymm (hcon s hs) (kcap_mono_of_prefix (he.ds_prefix hs) u)
  -- `u` keeps a non-empty queue
  have hq' : ∀ s ≥ t, ((e s).ring.node u).q ≠ [] := by
    intro s hs
    have h1 := (he.good t).fifo.q u; have h2 := (he.good s).fifo.q u
    rw [h2, hk s hs]; rw [h1] at hq
    intro h3
    simp only [encOut, List.map_eq_nil_iff, List.drop_eq_nil_iff] at h3
    rw [encOut, Ne, List.map_eq_nil_iff, List.drop_eq_nil_iff] at hq
    have := (he.out_prefix hs u).length_le; omega
  have hnq : ∀ s ≥ t, ¬ Quiet (e s).ring := fun s hs hQ => hq' s hs (hQ.empty u)
  -- the number of epochs is unbounded
  have hunb : ∀ m, ∃ s ≥ t, m ≤ (e s).ring.ds.length := by
    intro m
    obtain ⟨s, hs, h | h⟩ := rank_progress_iter he hf t (3 * m)
    · refine ⟨s, hs, ?_⟩
      have := rank_le (e s).ring; omega
    · exact absurd h (hnq s hs)
  -- a first capture after `t`
  obtain ⟨s1, hs1, hgrow⟩ : ∃ m ≥ t, (e m).ring.ds.length < (e (m + 1)).ring.ds.length := by
    obtain ⟨s, hs, hlen⟩ := hunb ((e t).ring.ds.length + 1)
    by_contra hcon'; push_neg at hcon'
    have : ∀ m ≥ t, (e m).ring.ds.length ≤ (e t).ring.ds.length := by
      intro m hm
      induction hm with
      | refl => exact le_rfl
      | step hle ih => exact (hcon' _ hle).trans ih
    have := this s hs; omega
  -- a step that changes `ds` is a capture, after which the token stage is over
  have hcapstep : ∀ m, (e m).ring.ds ≠ (e (m + 1)).ring.ds →
      ∃ l v a, (∀ u a, l ≠ .push u a) ∧ Enabled (e m).ring (.ccw v) ∧ l = .ccw v ∧
        capture? ((e m).ring.node v) = some a ∧ e (m + 1) = simNext K (e m) (.ring l) ∧
        (e (m + 1)).ring.ds = (e m).ring.ds ++ [a] ∧ (e (m + 1)).ring.hold = v := by
    intro m hne
    rcases he.cases m with hs | ⟨l, hl, hen, hs⟩ | ⟨v, outs, hr, -⟩
    · rw [hs] at hne; exact absurd rfl hne
    · rw [hs] at hne ⊢
      obtain ⟨v, a, rfl, ha, hds, hh⟩ := ds_change hl (Ne.symm hne)
      exact ⟨.ccw v, v, a, hl, hen, rfl, ha, rfl, hds, hh⟩
    · rw [hr, pushAll_ds] at hne; exact absurd rfl hne
  have hAhead1 : TokenAhead u (e (s1 + 1)).ring := by
    obtain ⟨l, v, a, hl, hen, rfl, ha, heq, hds, hh⟩ :=
      hcapstep s1 (fun h => by rw [h] at hgrow; omega)
    intro H
    exfalso
    have hph : (e (s1 + 1)).ring.node v = ((next (e s1).ring (.ccw v)).node v) := by rw [heq]; rfl
    have hph' : ((next (e s1).ring (.ccw v)).node v).ph = .send a 0 := by
      have hph0 : ((e s1).ring.node v).ph = .ready := by
        unfold capture? at ha; split at ha
        · assumption
        · cases ha
      cases hq0 : ((e s1).ring.node v).q with
      | nil => simp [capture?, hph0, hq0] at ha
      | cons a' q'' =>
        simp [capture?, hph0, hq0] at ha; subst ha
        simp [onCCW, hph0, hq0]
    rw [(he.good (s1 + 1)).inv.tokStage_iff, hh, hph, hph'] at H; exact H
  -- the potential `cdist hold u + |ds|` never increases from `s1 + 1` on
  have key : ∀ s ≥ s1 + 1, TokenAhead u (e s).ring ∧
      cdist (e s).ring.hold u + (e s).ring.ds.length ≤
        cdist (e (s1 + 1)).ring.hold u + (e (s1 + 1)).ring.ds.length := by
    intro s hs
    induction hs with
    | refl => exact ⟨hAhead1, le_rfl⟩
    | step hle ih =>
      rename_i m
      have hle' : s1 + 1 ≤ m := hle
      obtain ⟨hA, hpot⟩ := ih
      have hG := he.good m
      by_cases hds : (e m).ring.ds = (e (m + 1)).ring.ds
      · rcases he.cases m with h | ⟨l, hl, hen, h⟩ | ⟨v, outs, hr, -⟩
        · rw [h]; exact ⟨hA, hpot⟩
        · have hh : (e (m + 1)).ring.hold = (e m).ring.hold := by
            rw [h]; show (next (e m).ring l).hold = _
            cases l with
            | ccw v =>
              have : capture? ((e m).ring.node v) = none := by
                cases hc : capture? ((e m).ring.node v) with
                | none => rfl
                | some a =>
                  exfalso
                  have h5 : (e (m + 1)).ring.ds = (e m).ring.ds ++ [a] := by
                    rw [h]; show (next (e m).ring (.ccw v)).ds = _; rw [next_ccw_ds, hc]
                  rw [h5] at hds; simp at hds
              rw [next_ccw_hold, this]
            | _ => rfl
          refine ⟨?_, by rw [hh, ← hds]; exact hpot⟩
          rw [h]; exact tokenAhead_step hG.inv (hq' m (by omega)) hA hen
        · rw [hr]; exact ⟨tokenAhead_pushAll hA, by simpa using hpot⟩
      · obtain ⟨l, v, a, hl, hen, rfl, ha, heq, hds', hh⟩ := hcapstep m hds
        -- the capturer is not `u`
        obtain ⟨o, hao⟩ := capture_payload hG.fifo ha
        have hvu : v ≠ u := by
          rintro rfl
          have h1 := hk m (by omega); have h2 := hk (m + 1) (by omega)
          have : (e (m + 1)).kcap K v = (e m).kcap K v + 1 := by
            simp only [SimConfig.kcap, hds', decs_append, hao, List.filter_append,
              List.length_append]
            simp [decs, K.dec_enc]
          omega
        have hc := capture_cdist hG.inv hA hen ha
        have hlt := cdist_lt_of hc hvu
        refine ⟨?_, ?_⟩
        · intro H; exfalso
          have hph0 : ((e m).ring.node v).ph = .ready := by
            unfold capture? at ha; split at ha
            · assumption
            · cases ha
          have hph' : ((e (m + 1)).ring.node v).ph = .send a 0 := by
            rw [heq]
            cases hq0 : ((e m).ring.node v).q with
            | nil => simp [capture?, hph0, hq0] at ha
            | cons a' q'' =>
              simp [capture?, hph0, hq0] at ha; subst ha
              simp [simNext, onCCW, hph0, hq0]
          rw [(he.good (m + 1)).inv.tokStage_iff, hh, hph'] at H; exact H
        · rw [hh, hds']; simp only [List.length_append, List.length_singleton]; omega
  -- hence the number of epochs is bounded: a contradiction
  obtain ⟨s, hs, hlen⟩ := hunb (cdist (e (s1 + 1)).ring.hold u + (e (s1 + 1)).ring.ds.length + 1)
  have h1 := (key (max s (s1 + 1)) (le_max_right _ _)).2
  have h2 := (he.ds_prefix (le_max_left s (s1 + 1))).length_le
  have := cdist_pos (e (max s (s1 + 1))).ring.hold u
  omega

lemma sum_filter_eq (f : ZMod n × ZMod n × M → ZMod n) (L : List (ZMod n × ZMod n × M)) :
    ∑ u, (↑(L.filter (fun x => f x = u)) : Multiset (ZMod n × ZMod n × M)) =
      (↑L : Multiset (ZMod n × ZMod n × M)) := by
  ext y
  rw [Multiset.count_sum']
  simp only [Multiset.coe_count, List.count_filter]
  rw [Finset.sum_eq_single (f y)]
  · simp
  · intro b _ hb
    rw [List.count_eq_zero]; intro hy; rw [List.mem_filter] at hy
    simp only [decide_eq_true_eq] at hy; exact hb hy.2.symm
  · simp

/-- Every message sent by `u` is eventually broadcast. -/
lemma all_captured {T₀ : ZMod n} {e : ℕ → SimConfig P} (he : SimExec P K T₀ e)
    (hf : WeakFair K e) (t : ℕ) (u : ZMod n) :
    ∃ s ≥ t, ((e t).out u).length ≤ (e s).kcap K u := by
  suffices ∀ d t', t ≤ t' → ((e t).out u).length - (e t').kcap K u ≤ d →
      ∃ s ≥ t', ((e t).out u).length ≤ (e s).kcap K u by
    obtain ⟨s, hs, h⟩ := this _ t le_rfl le_rfl; exact ⟨s, hs, h⟩
  intro d
  induction d with
  | zero => intro t' _ h; exact ⟨t', le_rfl, by omega⟩
  | succ d ih =>
    intro t' ht' hd
    by_cases hdone : ((e t).out u).length ≤ (e t').kcap K u
    · exact ⟨t', le_rfl, hdone⟩
    have hq : ((e t').ring.node u).q ≠ [] := by
      rw [(he.good t').fifo.q u, encOut, Ne, List.map_eq_nil_iff, List.drop_eq_nil_iff]
      have := (he.out_prefix ht' u).length_le; omega
    obtain ⟨s, hs, hlt⟩ := no_starvation he hf t' u hq
    obtain ⟨s', hs', h⟩ := ih s (ht'.trans hs) (by omega)
    exact ⟨s', by omega, h⟩

lemma exists_common {p : ZMod n → ℕ → Prop} (hmono : ∀ u s s', s ≤ s' → p u s → p u s')
    (t : ℕ) (h : ∀ u, ∃ s ≥ t, p u s) : ∃ s ≥ t, ∀ u, p u s := by
  choose f hf1 hf2 using h
  refine ⟨t + Finset.univ.sup f, by omega, fun u => hmono u _ _ ?_ (hf2 u)⟩
  have := Finset.le_sup (f := f) (Finset.mem_univ u); omega

/-- **Theorem 4 / Theorem 6 of [CCGS22], liveness.** In every weakly fair execution of the
simulator, every message sent by `π` is eventually processed by its destination: for every time
`t` there is a later time at which all messages sent by time `t` have been processed. -/
theorem liveness {T₀ : ZMod n} {e : ℕ → SimConfig P} (he : SimExec P K T₀ e)
    (hf : WeakFair K e) (t : ℕ) : ∃ s ≥ t, (e t).sentMS ≤ (e s).procMS K := by
  -- every message sent by time `t` is broadcast by time `s1`
  obtain ⟨s1, hs1, h1⟩ := exists_common (p := fun u s => ((e t).out u).length ≤ (e s).kcap K u)
    (fun u s s' hss' h => h.trans (kcap_mono_of_prefix (he.ds_prefix hss') u)) t
    (all_captured he hf t)
  -- every node completes these epochs by time `s2`
  obtain ⟨s2, hs2, h2⟩ := epoch_completion he hf s1
  -- and processes the delivered messages by time `s3`
  obtain ⟨s3, hs3, h3⟩ := exists_common (p := fun v s => ((e s2).rcv K v).length ≤ (e s).nproc v)
    (fun v s s' hss' h => h.trans (he.nproc_mono hss' v)) s2 (fun v => processing he hf s2 v)
  refine ⟨s3, by omega, ?_⟩
  set L := decs K (e s1).ring.ds
  -- sent messages ≤ the broadcast ones
  have hA : (e t).sentMS ≤ (↑L : Multiset (ZMod n × ZMod n × M)) := by
    rw [← sum_filter_eq (fun x => x.1) L]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [(he.good s1).fifo.bc u]
    have hp : (e t).out u <+: ((e s1).out u).take ((e s1).kcap K u) := by
      have hpre := he.out_prefix hs1 u
      rw [List.prefix_iff_eq_take] at hpre ⊢
      rw [List.take_take, min_eq_left (h1 u)]; exact hpre
    exact Multiset.coe_le.2 (hp.sublist.map _).subperm
  -- broadcast messages ≤ processed ones
  have hB : (↑L : Multiset (ZMod n × ZMod n × M)) ≤ (e s3).procMS K := by
    rw [← sum_filter_eq (fun x => x.2.1) L]
    refine Finset.sum_le_sum fun v _ => ?_
    have hlog : (e s1).ring.ds <+: ((e s2).ring.node v).log := by
      rw [(he.good s2).inv.1.log v]
      have hpre := he.ds_prefix hs2
      rw [List.prefix_iff_eq_take] at hpre
      rw [hpre]; exact List.take_prefix_take_left (h2 v)
    have hr2 : L.filter (fun x => x.2.1 = v) <+: (e s2).rcv K v :=
      ((hlog.filterMap K.dec).filter _)
    have hr3 : (e s2).rcv K v <+: ((e s3).rcv K v).take ((e s3).nproc v) := by
      have hpre := he.rcv_prefix hs3 v
      rw [List.prefix_iff_eq_take] at hpre
      rw [hpre]; exact List.take_prefix_take_left (h3 v)
    exact Multiset.coe_le.2 (hr2.trans hr3).sublist.subperm
  exact hA.trans hB

lemma SimReach.good {T₀ : ZMod n} {C : SimConfig P} (h : SimReach P K T₀ C) : Good K T₀ C := by
  induction h with
  | refl => exact good_init T₀
  | tail _ hs ih => exact ih.step hs

/-- **Quiescence (end of the proof of Theorem 6).** If no step of the simulator is enabled, every
queue is empty and every message sent by `π` has been processed by its destination. -/
theorem quiescence {T₀ : ZMod n} {C : SimConfig P} (h : SimReach P K T₀ C)
    (hfin : ∀ l, ¬ SimEnabled K C l) :
    (∀ u, (C.ring.node u).q = []) ∧ C.sentMS = C.procMS K := by
  have hG := h.good
  have hQ : Quiet C.ring := by
    rcases hG.inv.enabled_or_quiet with ⟨l, hl, hen⟩ | hQ
    · exact absurd ((simEnabled_ring_iff hl).2 hen) (hfin _)
    · exact hQ
  refine ⟨hQ.empty, ?_⟩
  set L := decs K C.ring.ds
  have hS : C.sentMS = (↑L : Multiset (ZMod n × ZMod n × M)) := by
    rw [← sum_filter_eq (fun x => x.1) L]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hG.fifo.bc u]
    have hq := hG.fifo.q u
    rw [hQ.empty u, eq_comm, encOut, List.map_eq_nil_iff, List.drop_eq_nil_iff] at hq
    rw [List.take_of_length_le hq]; rfl
  have hP : C.procMS K = (↑L : Multiset (ZMod n × ZMod n × M)) := by
    rw [← sum_filter_eq (fun x => x.2.1) L]
    refine Finset.sum_congr rfl fun v _ => ?_
    have h1 : ¬ C.nproc v < (C.rcv K v).length := hfin (.proc v)
    rw [List.take_of_length_le (by omega)]
    simp only [SimConfig.rcv, L]
    rw [hG.inv.1.log v, hQ.tok.ep_all v, List.take_length]; rfl
  rw [hS, hP]

/-- Quiescence of the simulator implies quiescence of the simulated noiseless execution. -/
theorem quiescence_simulation {T₀ : ZMod n} {C : SimConfig P} (h : SimReach P K T₀ C)
    (hfin : ∀ l, ¬ SimEnabled K C l) :
    ∃ D : P.Config, P.Reach D ∧ (∀ v, D.st v = C.pst v ∧ D.tr v = C.tr v) ∧ P.Quiescent D := by
  obtain ⟨D, hD, hst, hnet⟩ := simulation h
  refine ⟨D, hD, hst, ?_⟩
  have := (quiescence h hfin).2
  rw [this] at hnet
  exact add_eq_right.1 hnet

/-! ### Non-vacuity: a round-robin scheduler is weakly fair -/

/-- All step labels of the simulator that can ever be enabled. -/
noncomputable def allLabels (n : ℕ) [NeZero n] : List (SimLabel n) :=
  (Finset.univ : Finset (ZMod n)).toList.flatMap
    fun u => [.ring (.start u), .ring (.cw u), .ring (.ccw u), .proc u]

lemma mem_allLabels {l : SimLabel n} (hl : ∀ u a, l ≠ .ring (.push u a)) : l ∈ allLabels n := by
  simp only [allLabels, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and,
    List.mem_cons, List.not_mem_nil, or_false]
  cases l with
  | ring l =>
    cases l with
    | push u a => exact absurd rfl (hl u a)
    | start u => exact ⟨u, Or.inl rfl⟩
    | cw u => exact ⟨u, Or.inr (Or.inl rfl)⟩
    | ccw u => exact ⟨u, Or.inr (Or.inr (Or.inl rfl))⟩
  | proc u => exact ⟨u, Or.inr (Or.inr (Or.inr rfl))⟩

lemma allLabels_ne_nil : allLabels n ≠ [] :=
  List.ne_nil_of_mem (mem_allLabels (l := .proc 0) (by intro _ _ h; cases h))

open Classical in
variable (P K) in
/-- The round-robin execution: at time `t`, take the `t`-th label (cyclically) if enabled. -/
noncomputable def roundRobin (T₀ : ZMod n) : ℕ → SimConfig P
  | 0 => simInit P K T₀
  | t + 1 =>
    let l := (allLabels n)[t % (allLabels n).length]'(Nat.mod_lt _
      (List.length_pos_iff.2 allLabels_ne_nil))
    if SimEnabled K (roundRobin T₀ t) l then simNext K (roundRobin T₀ t) l else roundRobin T₀ t

/-- **Non-vacuity.** The round-robin execution is a weakly fair execution of the simulator. -/
theorem roundRobin_fair (T₀ : ZMod n) :
    SimExec P K T₀ (roundRobin P K T₀) ∧ WeakFair K (roundRobin P K T₀) := by
  classical
  have hN : 0 < (allLabels n).length := List.length_pos_iff.2 allLabels_ne_nil
  refine ⟨⟨rfl, fun t => ?_⟩, fun l t hen => ?_⟩
  · simp only [roundRobin]
    split_ifs with h
    · exact Or.inl ⟨_, h, rfl⟩
    · exact Or.inr rfl
  · have hl : ∀ u a, l ≠ .ring (.push u a) := by
      rintro u a rfl; exact hen t le_rfl
    obtain ⟨i, hi, hli⟩ := List.mem_iff_getElem.1 (mem_allLabels hl)
    set s := (allLabels n).length * (t + 1) + i
    have hs : s % (allLabels n).length = i := by
      simp only [s, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    have hts : t ≤ s := by
      have : t + 1 ≤ (allLabels n).length * (t + 1) := Nat.le_mul_of_pos_left _ hN
      omega
    refine ⟨s, hts, hen s hts, ?_⟩
    have hl' : (allLabels n)[s % (allLabels n).length]'(Nat.mod_lt _ hN) = l := by
      simp only [hs]; exact hli
    show roundRobin P K T₀ (s + 1) = _
    simp only [roundRobin, hl', if_pos (hen s hts)]

/-- **Theorem 4 of [CCGS22] (= Theorem 6 of the full version), correctness part.** Algorithm 1
with the black box `π` is a noise-resilient simulator of `π` on the fully-defective oriented
cycle `ZMod n`, for every protocol `π` and every injective unary coding of messages:
1. (safety) every reachable configuration of the simulator corresponds to a reachable
   configuration of `π` over the noiseless network with the same states and local transcripts,
   whose messages in transit are those sent and not yet processed;
2. (liveness) in every weakly fair execution, every message sent by `π` is eventually processed
   by its destination;
3. (quiescence) if no step of the simulator is enabled, the simulated execution is quiescent;
4. (non-vacuity) weakly fair executions exist. -/
theorem theorem4 (T₀ : ZMod n) :
    (∀ C, SimReach P K T₀ C → ∃ D : P.Config, P.Reach D ∧
      (∀ v, D.st v = C.pst v ∧ D.tr v = C.tr v) ∧ D.net + C.procMS K = C.sentMS) ∧
    (∀ e, SimExec P K T₀ e → WeakFair K e → ∀ t, ∃ s ≥ t, (e t).sentMS ≤ (e s).procMS K) ∧
    (∀ C, SimReach P K T₀ C → (∀ l, ¬ SimEnabled K C l) → ∃ D : P.Config, P.Reach D ∧
      (∀ v, D.st v = C.pst v ∧ D.tr v = C.tr v) ∧ P.Quiescent D) ∧
    (∃ e, SimExec P K T₀ e ∧ WeakFair K e) :=
  ⟨fun _ h => simulation h, fun _ he hf t => liveness he hf t,
    fun _ h hfin => quiescence_simulation h hfin, ⟨_, roundRobin_fair T₀⟩⟩

end exec

end Podc.FullyDefective.Cycle
