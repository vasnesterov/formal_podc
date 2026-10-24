import Papers.PODC2016.StorageCostLowerBounds.StreamSafe
import Papers.PODC2016.StorageCostLowerBounds.RelayLive

/-!
# Liveness of the streaming relay

With quorum size `qs = n - f` and `2 f < n`, every operation of a non-crashed client returns in
every fair execution with at most `f` server failures (`isLive`).

* Write. While a write is pending and does not return, the stream stays fixed and every
  acknowledgement counter `ackc i` is monotone. For a correct server `i` with `ackc i < |strm|`,
  the outstanding bit is in transit (it is delivered, `Fair.delivered`, and sets `pa`), or pending
  at the server (`pa`; the server emits the forward and then the acknowledgement within a bounded
  number of its own ticks: the potential `potW`), or acknowledged in transit (delivered: `ackc i`
  increases). Hence every correct server eventually acknowledges the whole stream, which
  contradicts `Inv.wdone`.
* Read. The outstanding query of a correct server `i` is in transit, pending (`pd`; answered
  within three ticks: the potential `potR`), or answered in transit; the answer is delivered. A
  stale answer makes the reader send a fresh query, whose answer puts `i` into `resp`. Hence
  every correct server eventually answers the current read, which contradicts `Inv.rcur`.
-/

namespace Podc.StorageCost.Stream

open Cslib.ChannelFailures Cslib.SharedMemory

namespace Live

variable {n B : ℕ} (qs : ℕ)

/-! ### A generic potential argument -/

/-- If `Q` persists (with a non-increasing potential that strictly decreases at the infinitely
many `R`-times) unless `G` happens, then `G` eventually happens. -/
lemma potential {Q G R : ℕ → Prop} (φ : ℕ → ℕ) (hR : ∀ T, ∃ t ≥ T, R t)
    (h : ∀ t, Q t → G (t + 1) ∨ (Q (t + 1) ∧ φ (t + 1) ≤ φ t ∧ (R t → φ (t + 1) < φ t))) :
    ∀ t, Q t → ∃ t' > t, G t' := by
  intro t hQ
  by_contra hn
  push Not at hn
  have hall : ∀ u ≥ t, Q u ∧ ∀ v, t ≤ v → v ≤ u → φ u ≤ φ v := by
    intro u hu
    induction u, hu using Nat.le_induction with
    | base => exact ⟨hQ, fun v h1 h2 => by rw [show v = t by omega]⟩
    | succ u hu ih =>
      rcases h u ih.1 with hG | ⟨hQ', hle, -⟩
      · exact absurd hG (hn (u + 1) (by omega))
      · refine ⟨hQ', fun v h1 h2 => ?_⟩
        rcases Nat.lt_or_ge v (u + 1) with h3 | h3
        · exact hle.trans (ih.2 v h1 (by omega))
        · rw [show v = u + 1 by omega]
  have key : ∀ k, ∃ u ≥ t, φ u + k ≤ φ t := by
    intro k
    induction k with
    | zero => exact ⟨t, le_rfl, by simp⟩
    | succ k ih =>
      obtain ⟨u, hu, hk⟩ := ih
      obtain ⟨v, hv, hRv⟩ := hR u
      have h1 := (hall v (by omega)).2 u hu hv
      rcases h v (hall v (by omega)).1 with hG | ⟨-, -, hlt⟩
      · exact absurd hG (hn (v + 1) (by omega))
      · exact ⟨v + 1, by omega, by have := hlt hRv; omega⟩
  obtain ⟨u, -, hu⟩ := key (φ t + 1)
  omega

/-- A counter that, while below `N`, eventually increases, eventually reaches `N`. -/
lemma reach {f : ℕ → ℕ} {N t₁ : ℕ} (h : ∀ t ≥ t₁, f t < N → ∃ t' > t, f t < f t') :
    ∃ T ≥ t₁, N ≤ f T := by
  have key : ∀ k, ∃ T ≥ t₁, k ≤ f T ∨ N ≤ f T := by
    intro k
    induction k with
    | zero => exact ⟨t₁, le_rfl, Or.inl (Nat.zero_le _)⟩
    | succ k ih =>
      obtain ⟨T, hT, hk⟩ := ih
      by_cases hN : N ≤ f T
      · exact ⟨T, hT, Or.inr hN⟩
      · obtain ⟨t', ht', hlt⟩ := h T hT (by omega)
        refine ⟨t', by omega, Or.inl ?_⟩
        rcases hk with hk | hk <;> omega
  obtain ⟨T, hT, h | h⟩ := key N <;> exact ⟨T, hT, h⟩

/-! ### One-step facts -/

lemma step_deliver_eq (C : Cfg n B) {a b : Node n} {m : Msg} {rest : List Msg}
    (hc : C.chan a b = m :: rest) :
    (alg qs).step C (.deliver a b) = (C.pop a b rest).apply b (handle qs b (.recv a m) (C.loc b)) := by
  simp [Algorithm.step, hc, alg]

lemma loc_apply (C : Cfg n B) (p : Node n) (r : LSt n B × List (Node n × Msg) × Option (Val B)) :
    (C.apply p r).1.loc p = r.1 := by
  simp [Config.apply]


lemma handle_srv_tick (i : Fin n) (c : ℕ) (l : LSt n B) :
    handle qs (.srv i) (.tick c) l = ((l.1, l.2.1, (sTick (n := n) l.2.2).1), (sTick (n := n) l.2.2).2, none) :=
  rfl

lemma handle_srv_W (i : Fin n) (b : Bool) (l : LSt n B) :
    handle qs (.srv i) (.recv .wr (.W b)) l = ((l.1, l.2.1, (some b, true, l.2.2.2.2)), [], none) :=
  rfl

lemma handle_srv_Q (i : Fin n) (l : LSt n B) :
    handle qs (.srv i) (.recv .rd .Q) l =
      ((l.1, l.2.1, (l.2.2.1, l.2.2.2.1, true, l.2.2.2.2.2)), [], none) :=
  rfl

lemma handle_srv_invoke (i : Fin n) (o : RWOp (Val B)) (l : LSt n B) :
    handle qs (.srv i) (.invoke o) l = (l, [], none) := by
  rcases o with _ | _ <;> rfl

lemma handle_srv_other (i : Fin n) (a : Node n) (m : Msg) (l : LSt n B)
    (h1 : ∀ b, ¬ (a = .wr ∧ m = .W b)) (h2 : ¬ (a = .rd ∧ m = .Q)) :
    handle qs (.srv i) (.recv a m) l = (l, [], none) := by
  rcases a with j | _ | _ <;> rcases m with b | _ | b | _ | _ <;> simp_all <;> rfl

lemma handle_srv_recv_out (i : Fin n) (a : Node n) (m : Msg) (l : LSt n B) :
    (handle qs (.srv i) (.recv a m) l).2 = ([], none) := by
  rcases a with j | _ | _ <;> rcases m with b | _ | b | _ | _ <;> rfl

/-- How a step changes the state of server `i`. -/
lemma ss_step (C : Cfg n B) (e : Event (Node n) (register (Val B) (fun _ => false))) (i : Fin n) :
    ss ((alg qs).step C e).1 i = ss C i ∨
    (∃ c, e = .tick (.srv i) c ∧ ss ((alg qs).step C e).1 i = (sTick (n := n) (ss C i)).1) ∨
    (∃ b rest, e = .deliver .wr (.srv i) ∧ C.chan .wr (.srv i) = .W b :: rest ∧
      ss ((alg qs).step C e).1 i = (some b, true, (ss C i).2.2)) ∨
    (e = .deliver .rd (.srv i) ∧
      ss ((alg qs).step C e).1 i = ((ss C i).1, (ss C i).2.1, true, (ss C i).2.2.2)) := by
  by_cases ho : e.owner = .srv i
  swap
  · left; simp only [ss]; rw [loc_step_ne _ _ _ (Ne.symm ho)]
  cases e with
  | invoke p o =>
    simp only [Event.owner] at ho; subst ho
    left; simp only [Algorithm.step]; split
    · rfl
    · simp [ss, Config.apply, alg, handle_srv_invoke]
  | tick p c =>
    simp only [Event.owner] at ho; subst ho
    right; left; exact ⟨c, rfl, by simp [Algorithm.step, ss, Config.apply, alg, handle_srv_tick]⟩
  | deliver a p =>
    simp only [Event.owner] at ho; subst ho
    rcases hc : C.chan a (.srv i) with _ | ⟨m, rest⟩
    · left; simp [Algorithm.step, hc]
    rw [step_deliver_eq qs C hc]
    by_cases h1 : ∃ b, a = .wr ∧ m = .W b
    · obtain ⟨b, rfl, rfl⟩ := h1
      right; right; left
      exact ⟨b, rest, rfl, hc, by simp [ss, loc_apply, handle_srv_W, Config.pop]⟩
    by_cases h2 : a = .rd ∧ m = .Q
    · obtain ⟨rfl, rfl⟩ := h2
      right; right; right
      exact ⟨rfl, by simp [ss, loc_apply, handle_srv_Q, Config.pop]⟩
    left
    push Not at h1
    rw [handle_srv_other qs i a m _ (fun b h => h1 b h.1 h.2) h2]
    simp [ss, loc_apply, Config.pop]

/-- How a step changes the channels from server `i` (other than by a delivery on them). -/
lemma chan_srv_step (C : Cfg n B) (e : Event (Node n) (register (Val B) (fun _ => false)))
    (i : Fin n) (x : Node n) (hx : e ≠ .deliver (.srv i) x) :
    ((alg qs).step C e).1.chan (.srv i) x = C.chan (.srv i) x ∨
    ∃ c, e = .tick (.srv i) c ∧ ((alg qs).step C e).1.chan (.srv i) x =
      C.chan (.srv i) x ++ msgsTo (sTick (n := n) (ss C i)).2 x := by
  by_cases ho : e.owner = .srv i
  swap
  · left; exact chan_step_of_ne _ C e ho hx
  cases e with
  | invoke p o =>
    simp only [Event.owner] at ho; subst ho
    left; simp only [Algorithm.step]; split
    · rfl
    · simp [Config.apply, alg, handle_srv_invoke, msgsTo]
  | tick p c =>
    simp only [Event.owner] at ho; subst ho
    right; exact ⟨c, rfl, by simp [Algorithm.step, ss, Config.apply, alg, handle_srv_tick]⟩
  | deliver a p =>
    simp only [Event.owner] at ho; subst ho
    left
    rcases hc : C.chan a (.srv i) with _ | ⟨m, rest⟩
    · simp [Algorithm.step, hc]
    rw [step_deliver_eq qs C hc]
    have hout := handle_srv_recv_out qs i a m (C.loc (.srv i))
    have hax : ¬ (a = .srv i ∧ x = .srv i) := by
      rintro ⟨rfl, rfl⟩; exact hx rfl
    simp only [Config.apply, Config.pop, ite_true, hout, msgsTo, List.filter_nil, List.map_nil,
      List.append_nil]
    split_ifs with h
    · exact absurd ⟨h.1.symm, h.2⟩ hax
    · rfl

/-! ### The writer and the reader -/

lemma handle_wr_other (a : Node n) (m : Msg) (l : LSt n B) (h : ∀ j, ¬ (a = .srv j ∧ m = .A)) :
    handle qs .wr (.recv a m) l = (l, [], none) := by
  rcases a with j | _ | _ <;> rcases m with b | _ | b | _ | _ <;> simp_all <;> rfl

lemma handle_rd_other (a : Node n) (m : Msg) (l : LSt n B)
    (h1 : ∀ j b, ¬ (a = .srv j ∧ m = .F b)) (h2 : ∀ j, ¬ (a = .srv j ∧ m = .D)) :
    handle qs .rd (.recv a m) l = (l, [], none) := by
  rcases a with j | _ | _ <;> rcases m with b | _ | b | _ | _ <;> simp_all <;> rfl

/-- How a step changes the writer's state. -/
lemma ws_step (C : Cfg n B) (e : Event (Node n) (register (Val B) (fun _ => false))) :
    ws ((alg qs).step C e).1 = ws C ∨
    (∃ v, e = .invoke .wr (.write v) ∧ C.pend .wr = none ∧
      ws ((alg qs).step C e).1 = (wInvoke (ws C) v).1) ∨
    (∃ j rest, e = .deliver (.srv j) .wr ∧ C.chan (.srv j) .wr = .A :: rest ∧
      ws ((alg qs).step C e).1 = (wAck qs (ws C) j).1 ∧
      ((alg qs).step C e).2 = respOut .wr (C.pend .wr) (wAck qs (ws C) j).2.2) := by
  by_cases ho : e.owner = .wr
  swap
  · left; simp only [ws]; rw [loc_step_ne _ _ _ (Ne.symm ho)]
  cases e with
  | invoke p o =>
    simp only [Event.owner] at ho; subst ho
    rcases hp : C.pend .wr with _ | o'
    · rcases o with _ | v
      · left; simp [Algorithm.step, hp, ws, Config.apply, alg, handle]
      · right; left
        exact ⟨v, rfl, rfl, by simp [Algorithm.step, hp, ws, Config.apply, alg, handle]⟩
    · left; simp [Algorithm.step, hp]
  | tick p c =>
    simp only [Event.owner] at ho; subst ho
    left; simp [Algorithm.step, ws, Config.apply, alg, handle]
  | deliver a p =>
    simp only [Event.owner] at ho; subst ho
    rcases hc : C.chan a .wr with _ | ⟨m, rest⟩
    · left; simp [Algorithm.step, hc]
    rw [step_deliver_eq qs C hc]
    by_cases h1 : ∃ j, a = .srv j ∧ m = .A
    · obtain ⟨j, rfl, rfl⟩ := h1
      right; right
      exact ⟨j, rest, rfl, hc, by simp [ws, Config.apply, Config.pop, handle],
        by simp [Config.apply, Config.pop, handle]⟩
    · left
      push Not at h1
      rw [handle_wr_other qs a m _ (fun j h => h1 j h.1 h.2)]
      simp [ws, loc_apply, Config.pop]

/-- How a step changes the reader's state. -/
lemma rs_step (C : Cfg n B) (e : Event (Node n) (register (Val B) (fun _ => false))) :
    rs ((alg qs).step C e).1 = rs C ∨
    (e = .invoke .rd .read ∧ C.pend .rd = none ∧ rs ((alg qs).step C e).1 = (rInvoke (rs C)).1) ∨
    (∃ j b rest, e = .deliver (.srv j) .rd ∧ C.chan (.srv j) .rd = .F b :: rest ∧
      rs ((alg qs).step C e).1 = rBit (rs C) j b) ∨
    (∃ j rest, e = .deliver (.srv j) .rd ∧ C.chan (.srv j) .rd = .D :: rest ∧
      rs ((alg qs).step C e).1 = (rAns qs (rs C) j).1 ∧
      ((alg qs).step C e).2 = respOut .rd (C.pend .rd) (rAns qs (rs C) j).2.2) := by
  by_cases ho : e.owner = .rd
  swap
  · left; simp only [rs]; rw [loc_step_ne _ _ _ (Ne.symm ho)]
  cases e with
  | invoke p o =>
    simp only [Event.owner] at ho; subst ho
    rcases hp : C.pend .rd with _ | o'
    · rcases o with _ | v
      · right; left
        exact ⟨rfl, rfl, by simp [Algorithm.step, hp, rs, Config.apply, alg, handle]⟩
      · left; simp [Algorithm.step, hp, rs, Config.apply, alg, handle]
    · left; simp [Algorithm.step, hp]
  | tick p c =>
    simp only [Event.owner] at ho; subst ho
    left; simp [Algorithm.step, rs, Config.apply, alg, handle]
  | deliver a p =>
    simp only [Event.owner] at ho; subst ho
    rcases hc : C.chan a .rd with _ | ⟨m, rest⟩
    · left; simp [Algorithm.step, hc]
    rw [step_deliver_eq qs C hc]
    by_cases h1 : ∃ j b, a = .srv j ∧ m = .F b
    · obtain ⟨j, b, rfl, rfl⟩ := h1
      right; right; left
      exact ⟨j, b, rest, rfl, hc, by simp [rs, Config.apply, Config.pop, handle]⟩
    by_cases h2 : ∃ j, a = .srv j ∧ m = .D
    · obtain ⟨j, rfl, rfl⟩ := h2
      right; right; right
      exact ⟨j, rest, rfl, hc, by simp [rs, Config.apply, Config.pop, handle],
        by simp [Config.apply, Config.pop, handle]⟩
    left
    push Not at h1 h2
    rw [handle_rd_other qs a m _ (fun j b h => h1 j b h.1 h.2) (fun j h => h2 j h.1 h.2)]
    simp [rs, loc_apply, Config.pop]

lemma wAck_ackc (w : WSt n B) (j : Fin n) :
    (wAck qs w j).1.ackc = Function.update w.ackc j (w.ackc j + 1) := by
  unfold wAck; dsimp only; split_ifs <;> rfl

lemma wAck_of_none {w : WSt n B} {j : Fin n} (h : (wAck qs w j).2.2 = none) :
    (wAck qs w j).1.busy = w.busy ∧ (wAck qs w j).1.strm = w.strm := by
  unfold wAck at h ⊢; dsimp only at h ⊢; split_ifs at h ⊢ <;> simp_all

lemma rBit_eq (r : RSt n B) (j : Fin n) (b : Bool) :
    (rBit r j b).q = r.q ∧ (rBit r j b).busy = r.busy ∧ (rBit r j b).sentAt = r.sentAt ∧
      (rBit r j b).resp = r.resp := by
  unfold rBit; dsimp only; split_ifs <;> simp

lemma rAns_of_none {r : RSt n B} {j : Fin n} (hb : r.busy = true) (h : (rAns qs r j).2.2 = none) :
    (rAns qs r j).1.busy = true ∧ (rAns qs r j).1.q = r.q ∧ r.resp ⊆ (rAns qs r j).1.resp ∧
      (r.sentAt j = some r.q → j ∈ (rAns qs r j).1.resp) ∧
      (r.sentAt j ≠ some r.q → (rAns qs r j).1.sentAt j = some r.q) ∧
      ∀ k, k ≠ j → (rAns qs r j).1.sentAt k = r.sentAt k := by
  unfold rAns at h ⊢
  simp only [hb, ite_true] at h ⊢
  by_cases h1 : r.sentAt j = some r.q
  · by_cases h2 : qs ≤ (insert j r.resp).card
    · simp [h1, h2] at h
    · simp only [h1, h2, ↓reduceIte]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Finset.subset_insert]
  · simp only [h1, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

/-- The acknowledgement counters never decrease. -/
lemma ackc_step (C : Cfg n B) (e : Event (Node n) (register (Val B) (fun _ => false))) (j : Fin n) :
    (ws C).ackc j ≤ (ws ((alg qs).step C e).1).ackc j := by
  rcases ws_step qs C e with h | ⟨v, -, -, h⟩ | ⟨k, rest, -, -, h, -⟩ <;> rw [h]
  · simp [wInvoke]
  · rw [wAck_ackc]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [Function.update_of_ne hjk]

/-- Delivering an acknowledgement of server `j` increments `ackc j`. -/
lemma ackc_deliver (C : Cfg n B) {j : Fin n} {rest : List Msg} (h : C.chan (.srv j) .wr = .A :: rest) :
    (ws ((alg qs).step C (.deliver (.srv j) .wr)).1).ackc j = (ws C).ackc j + 1 := by
  rw [step_deliver_eq qs C h]
  simp [ws, Config.apply, Config.pop, handle, wAck_ackc]

/-- While a write is pending and does not return, it stays pending and the stream is fixed. -/
lemma wr_stable {C : Cfg n B} {α : Hist n B} (hI : Inv qs C α) (hb : (ws C).busy = true)
    (e : Event (Node n) (register (Val B) (fun _ => false)))
    (hnr : ∀ x, Label.ret .wr x ∉ ((alg qs).step C e).2) :
    (ws ((alg qs).step C e).1).busy = true ∧ (ws ((alg qs).step C e).1).strm = (ws C).strm := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 (hI.wbusy.1 hb)
  rcases ws_step qs C e with h | ⟨v, -, hp, -⟩ | ⟨k, rest, -, -, h, hl⟩
  · rw [h]; exact ⟨hb, rfl⟩
  · rw [ho] at hp; simp at hp
  · rw [h]
    rcases hr : (wAck qs (ws C) k).2.2 with _ | x
    · rw [(wAck_of_none qs hr).1, (wAck_of_none qs hr).2]; exact ⟨hb, rfl⟩
    · exact absurd (by rw [hl, ho, hr]; simp [respOut]) (hnr x)

/-- Delivering an answer of server `j` to the reader. -/
lemma rd_deliver_D (C : Cfg n B) {j : Fin n} {rest : List Msg} (h : C.chan (.srv j) .rd = .D :: rest) :
    rs ((alg qs).step C (.deliver (.srv j) .rd)).1 = (rAns qs (rs C) j).1 ∧
      ((alg qs).step C (.deliver (.srv j) .rd)).2 = respOut .rd (C.pend .rd) (rAns qs (rs C) j).2.2 := by
  rw [step_deliver_eq qs C h]
  exact ⟨by simp [rs, Config.apply, Config.pop, handle], by simp [Config.apply, Config.pop, handle]⟩

/-- While a read is pending and does not return: it stays pending with the same index, the set
of answers grows, and an outstanding query changes only to a query of the current read (or the
server answers the current read). -/
lemma rd_stable {C : Cfg n B} {α : Hist n B} (hI : Inv qs C α) (hb : (rs C).busy = true)
    (e : Event (Node n) (register (Val B) (fun _ => false)))
    (hnr : ∀ x, Label.ret .rd x ∉ ((alg qs).step C e).2) :
    (rs ((alg qs).step C e).1).busy = true ∧ (rs ((alg qs).step C e).1).q = (rs C).q ∧
      (rs C).resp ⊆ (rs ((alg qs).step C e).1).resp ∧
      ∀ j, (rs ((alg qs).step C e).1).sentAt j = (rs C).sentAt j ∨
        j ∈ (rs ((alg qs).step C e).1).resp ∨
        (rs ((alg qs).step C e).1).sentAt j = some (rs C).q := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 (hI.rbusy.1 hb)
  rcases rs_step qs C e with h | ⟨-, hp, -⟩ | ⟨k, b, rest, -, -, h⟩ | ⟨k, rest, -, -, h, hl⟩
  · rw [h]; exact ⟨hb, rfl, subset_rfl, fun j => Or.inl rfl⟩
  · rw [ho] at hp; simp at hp
  · rw [h]; obtain ⟨h1, h2, h3, h4⟩ := rBit_eq (rs C) k b
    rw [h1, h2, h3, h4]; exact ⟨hb, rfl, subset_rfl, fun j => Or.inl rfl⟩
  · rw [h]
    rcases hr : (rAns qs (rs C) k).2.2 with _ | x
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rAns_of_none qs hb hr
      refine ⟨h1, h2, h3, fun j => ?_⟩
      by_cases hjk : j = k
      · subst hjk
        by_cases hs : (rs C).sentAt j = some (rs C).q
        · exact Or.inr (Or.inl (h4 hs))
        · exact Or.inr (Or.inr (h5 hs))
      · exact Or.inl (h6 j hjk)
    · exact absurd (by rw [hl, ho, hr]; simp [respOut]) (hnr x)

/-! ### Consequences of the invariant -/

section InvFacts

variable {qs} {C : Cfg n B} {α : Hist n B}

lemma chan_wr_srv (hI : Inv qs C α) (i : Fin n) :
    C.chan .wr (.srv i) = [] ∨ ∃ b, C.chan .wr (.srv i) = [.W b] := by
  obtain ⟨-, -, -, -, h⟩ := hI.tokW i
  rcases h with h | h | h | h <;> simp_all

lemma chan_srv_wr (hI : Inv qs C α) (i : Fin n) :
    C.chan (.srv i) .wr = [] ∨ C.chan (.srv i) .wr = [.A] := by
  obtain ⟨-, -, -, -, h⟩ := hI.tokW i
  rcases h with h | h | h | h <;> simp_all

lemma tokW_pa (hI : Inv qs C α) {i : Fin n} (hpa : (ss C i).2.1 = true) :
    C.chan .wr (.srv i) = [] := by
  obtain ⟨-, -, -, -, h⟩ := hI.tokW i
  rcases h with h | h | h | h <;> simp_all

lemma tokW_cases (hI : Inv qs C α) {i : Fin n} (hlt : (ws C).ackc i < (ws C).strm.length) :
    (∃ b, C.chan .wr (.srv i) = [.W b]) ∨ (ss C i).2.1 = true ∨ C.chan (.srv i) .wr = [.A] := by
  obtain ⟨-, -, -, h4, h⟩ := hI.tokW i
  rw [hI.wS] at hlt
  rcases h with h | h | h | h
  · exact absurd (h4 h.1) (by omega)
  · exact Or.inl ⟨_, h.2.2.1⟩
  · exact Or.inr (Or.inl h.2.2.2.1)
  · exact Or.inr (Or.inr h.2.2.2.2.2)

lemma chan_rd_srv (hI : Inv qs C α) (i : Fin n) :
    C.chan .rd (.srv i) = [] ∨ C.chan .rd (.srv i) = [.Q] := by
  rcases hI.tokQ i with h | ⟨j, -, -, h | h | h⟩ <;> simp_all

lemma tokQ_cases (hI : Inv qs C α) {i : Fin n} (h : (rs C).sentAt i ≠ none) :
    C.chan .rd (.srv i) = [.Q] ∨ (ss C i).2.2.1 = true ∨ .D ∈ C.chan (.srv i) .rd := by
  rcases hI.tokQ i with h' | ⟨j, -, -, h' | h' | h'⟩
  · exact absurd h'.1 h
  · exact Or.inl h'.1
  · exact Or.inr (Or.inl h'.2.1)
  · refine Or.inr (Or.inr ?_)
    have : 0 < (C.chan (.srv i) .rd).count .D := by
      have := h'.2.2; simp only [nD] at this; omega
    exact List.count_pos_iff.1 this

end InvFacts

/-! ### Server steps -/

lemma tick_srv (C : Cfg n B) (i : Fin n) (c : ℕ) :
    ss ((alg qs).step C (.tick (.srv i) c)).1 i = (sTick (n := n) (ss C i)).1 ∧
      ∀ x, ((alg qs).step C (.tick (.srv i) c)).1.chan (.srv i) x =
        C.chan (.srv i) x ++ msgsTo (sTick (n := n) (ss C i)).2 x := by
  refine ⟨by simp [Algorithm.step, ss, Config.apply, alg, handle_srv_tick], fun x => ?_⟩
  simp [Algorithm.step, ss, Config.apply, alg, handle_srv_tick]

lemma deliver_W_pa (C : Cfg n B) {i : Fin n} {b : Bool} {rest : List Msg}
    (h : C.chan .wr (.srv i) = .W b :: rest) :
    (ss ((alg qs).step C (.deliver .wr (.srv i))).1 i).2.1 = true := by
  rw [step_deliver_eq qs C h]; simp [ss, loc_apply, handle_srv_W, Config.pop]

lemma deliver_Q_pd (C : Cfg n B) {i : Fin n} {rest : List Msg}
    (h : C.chan .rd (.srv i) = .Q :: rest) :
    (ss ((alg qs).step C (.deliver .rd (.srv i))).1 i).2.2.1 = true := by
  rw [step_deliver_eq qs C h]; simp [ss, loc_apply, handle_srv_Q, Config.pop]

/-- Potential of a server with a pending acknowledgement: the number of its ticks until it
sends the acknowledgement. -/
def potW (s : SSt) : ℕ :=
  if s.1 = none then (if s.2.2.2 = 0 then 2 else if s.2.2.2 = 1 then 1 else 3)
  else (if s.2.2.2 = 0 then 2 else if s.2.2.2 = 1 then 4 else 3)

/-- Potential of a server with a pending answer: the number of its ticks until it answers. -/
def potR (s : SSt) : ℕ := 2 - s.2.2.2.val

lemma potW_step {C : Cfg n B} {α : Hist n B} (hI : Inv qs C α) {i : Fin n}
    (hpa : (ss C i).2.1 = true) (hch : C.chan (.srv i) .wr = [])
    (e : Event (Node n) (register (Val B) (fun _ => false))) :
    ((alg qs).step C e).1.chan (.srv i) .wr ≠ [] ∨
      ((ss ((alg qs).step C e).1 i).2.1 = true ∧ ((alg qs).step C e).1.chan (.srv i) .wr = [] ∧
        potW (ss ((alg qs).step C e).1 i) ≤ potW (ss C i) ∧
        ((∃ c, e = .tick (.srv i) c) → potW (ss ((alg qs).step C e).1 i) < potW (ss C i))) := by
  by_cases ht : ∃ c, e = .tick (.srv i) c
  · obtain ⟨c, rfl⟩ := ht
    obtain ⟨h1, h2⟩ := tick_srv qs C i c
    rw [h1, h2, hch]
    generalize ss C i = s at hpa
    obtain ⟨pf, pa, pd, t⟩ := s
    simp only at hpa; subst hpa
    rcases pf with _ | b <;> rcases pd <;> fin_cases t <;> simp [sTick, potW, msgsTo]
  by_cases hd : e = .deliver (.srv i) .wr
  · subst hd
    have : (alg qs).step C (.deliver (.srv i) .wr) = (C, []) := by simp [Algorithm.step, hch]
    rw [this]; exact Or.inr ⟨hpa, hch, le_rfl, fun h => absurd h ht⟩
  have hc : ((alg qs).step C e).1.chan (.srv i) .wr = [] := by
    rcases chan_srv_step qs C e i .wr hd with h | ⟨c, hc, -⟩
    · rw [h, hch]
    · exact absurd ⟨c, hc⟩ ht
  right
  rcases ss_step qs C e i with h | ⟨c, hc', -⟩ | ⟨b, rest, -, hw, -⟩ | ⟨-, h⟩
  · rw [h]; exact ⟨hpa, hc, le_rfl, fun h => absurd h ht⟩
  · exact absurd ⟨c, hc'⟩ ht
  · rw [tokW_pa hI hpa] at hw; simp at hw
  · rw [h]; exact ⟨hpa, hc, by simp [potW], fun h => absurd h ht⟩

lemma potR_step (C : Cfg n B) {i : Fin n} (hpd : (ss C i).2.2.1 = true)
    (e : Event (Node n) (register (Val B) (fun _ => false))) :
    .D ∈ ((alg qs).step C e).1.chan (.srv i) .rd ∨
      ((ss ((alg qs).step C e).1 i).2.2.1 = true ∧
        potR (ss ((alg qs).step C e).1 i) ≤ potR (ss C i) ∧
        ((∃ c, e = .tick (.srv i) c) → potR (ss ((alg qs).step C e).1 i) < potR (ss C i))) := by
  by_cases ht : ∃ c, e = .tick (.srv i) c
  · obtain ⟨c, rfl⟩ := ht
    obtain ⟨h1, h2⟩ := tick_srv qs C i c
    rw [h1, h2]
    generalize ss C i = s at hpd
    obtain ⟨pf, pa, pd, t⟩ := s
    simp only at hpd; subst hpd
    rcases pf with _ | b <;> rcases pa <;> fin_cases t <;> simp [sTick, potR, msgsTo]
  right
  rcases ss_step qs C e i with h | ⟨c, hc', -⟩ | ⟨b, rest, -, -, h⟩ | ⟨-, h⟩
  · rw [h]; exact ⟨hpd, le_rfl, fun h => absurd h ht⟩
  · exact absurd ⟨c, hc'⟩ ht
  · rw [h]; exact ⟨hpd, by simp [potR], fun h => absurd h ht⟩
  · rw [h]; exact ⟨rfl, by simp [potR], fun h => absurd h ht⟩

/-! ### Executions -/

/-- The configuration at time `t`. -/
abbrev cfg (ev : ℕ → Event (Node n) (register (Val B) (fun _ => false))) (t : ℕ) : Cfg n B :=
  (alg qs).cfgAt ev t

section Exec

variable {qs} {ev : ℕ → Event (Node n) (register (Val B) (fun _ => false))}
  {fp : FailurePattern (Node n)}

lemma cfg_succ (t : ℕ) : cfg qs ev (t + 1) = ((alg qs).step (cfg qs ev t) (ev t)).1 := rfl

lemma ackc_mono (i : Fin n) {t t' : ℕ} (h : t ≤ t') :
    (ws (cfg qs ev t)).ackc i ≤ (ws (cfg qs ev t')).ackc i := by
  induction t', h using Nat.le_induction with
  | base => exact le_rfl
  | succ t' _ ih => exact ih.trans (ackc_step qs _ _ i)

lemma exists_head {l : List Msg} {m : Msg} (h : l.head? = some m) : ∃ rest, l = m :: rest := by
  cases l with
  | nil => simp at h
  | cons a rest => simp at h; exact ⟨rest, by rw [h]⟩

/-- A pending acknowledgement is eventually sent. -/
lemma pa_to_A (hI : ∀ t, ∃ α, Inv qs (cfg qs ev t) α) {i : Fin n}
    (htick : ∀ T, ∃ t ≥ T, ∃ c, ev t = .tick (.srv i) c) (t : ℕ)
    (hpa : (ss (cfg qs ev t) i).2.1 = true) :
    ∃ t' ≥ t, (cfg qs ev t').chan (.srv i) .wr ≠ [] := by
  by_cases h0 : (cfg qs ev t).chan (.srv i) .wr = []
  · obtain ⟨t', ht', hG⟩ := potential
      (Q := fun u => (ss (cfg qs ev u) i).2.1 = true ∧ (cfg qs ev u).chan (.srv i) .wr = [])
      (G := fun u => (cfg qs ev u).chan (.srv i) .wr ≠ [])
      (R := fun u => ∃ c, ev u = .tick (.srv i) c) (fun u => potW (ss (cfg qs ev u) i)) htick
      (fun u hu => by
        obtain ⟨α, hα⟩ := hI u
        rcases potW_step qs hα hu.1 hu.2 (ev u) with h | ⟨h1, h2, h3, h4⟩
        · exact Or.inl h
        · exact Or.inr ⟨⟨h1, h2⟩, h3, h4⟩) t ⟨hpa, h0⟩
    exact ⟨t', ht'.le, hG⟩
  · exact ⟨t, le_rfl, h0⟩

/-- An acknowledgement in transit is eventually delivered, incrementing `ackc`. -/
lemma A_progress (hfair : (alg qs).Fair fp ev) {i : Fin n}
    (hw : ¬ Algorithm.Crashed fp ev .wr) (hs : ¬ Algorithm.Crashed fp ev (.srv i))
    (hch : (Node.srv i, Node.wr) ∉ fp.chans) (hI : ∀ t, ∃ α, Inv qs (cfg qs ev t) α) (t : ℕ)
    (h : (cfg qs ev t).chan (.srv i) .wr ≠ []) :
    ∃ t' > t, (ws (cfg qs ev t)).ackc i < (ws (cfg qs ev t')).ackc i := by
  obtain ⟨m, rest, hm⟩ := List.exists_cons_of_ne_nil h
  obtain ⟨t₂, ht₂, he, hh⟩ := hfair.delivered hs hw hch 0 t m (by rw [hm]; rfl)
  obtain ⟨α, hα⟩ := hI t₂
  have hA : (cfg qs ev t₂).chan (.srv i) .wr = [.A] := by
    rcases chan_srv_wr hα i with h' | h'
    · rw [h'] at hh; simp at hh
    · exact h'
  refine ⟨t₂ + 1, by omega, ?_⟩
  rw [cfg_succ, he, ackc_deliver qs _ hA]
  have := ackc_mono (qs := qs) (ev := ev) i ht₂
  omega

/-- While below the stream length, the acknowledgement counter of a correct server eventually
increases. -/
lemma ack_progress (hfair : (alg qs).Fair fp ev) {i : Fin n}
    (hw : ¬ Algorithm.Crashed fp ev .wr) (hs : ¬ Algorithm.Crashed fp ev (.srv i))
    (hch : fp.chans = ∅) (hI : ∀ t, ∃ α, Inv qs (cfg qs ev t) α) (t : ℕ)
    (hlt : (ws (cfg qs ev t)).ackc i < (ws (cfg qs ev t)).strm.length) :
    ∃ t' > t, (ws (cfg qs ev t)).ackc i < (ws (cfg qs ev t')).ackc i := by
  have htick := hfair.1 _ hs
  have hnoch : ∀ a b, (a, b) ∉ fp.chans := by intro a b; rw [hch]; simp
  obtain ⟨α, hα⟩ := hI t
  have fin : ∀ t', t ≤ t' → (cfg qs ev t').chan (.srv i) .wr ≠ [] →
      ∃ t'' > t, (ws (cfg qs ev t)).ackc i < (ws (cfg qs ev t'')).ackc i := by
    intro t' ht' hne
    obtain ⟨t'', ht'', hlt'⟩ := A_progress hfair hw hs (hnoch _ _) hI t' hne
    exact ⟨t'', by omega, lt_of_le_of_lt (ackc_mono i ht') hlt'⟩
  rcases tokW_cases hα hlt with ⟨b, hb⟩ | hpa | hA
  · obtain ⟨t₁, ht₁, he, hh⟩ := hfair.delivered hw hs (hnoch _ _) 0 t (.W b) (by rw [hb]; rfl)
    obtain ⟨α₁, hα₁⟩ := hI t₁
    obtain ⟨b', hb'⟩ : ∃ b', (cfg qs ev t₁).chan .wr (.srv i) = [.W b'] := by
      rcases chan_wr_srv hα₁ i with h' | h'
      · rw [h'] at hh; simp at hh
      · exact h'
    have hpa : (ss (cfg qs ev (t₁ + 1)) i).2.1 = true := by
      rw [cfg_succ, he]; exact deliver_W_pa qs _ hb'
    obtain ⟨t', ht', hne⟩ := pa_to_A hI htick _ hpa
    exact fin t' (by omega) hne
  · obtain ⟨t', ht', hne⟩ := pa_to_A hI htick _ hpa
    exact fin t' ht' hne
  · exact fin t le_rfl (by rw [hA]; simp)

/-- A pending answer is eventually sent. -/
lemma pd_to_D {i : Fin n} (htick : ∀ T, ∃ t ≥ T, ∃ c, ev t = .tick (.srv i) c) (t : ℕ)
    (hpd : (ss (cfg qs ev t) i).2.2.1 = true) :
    ∃ t' > t, .D ∈ (cfg qs ev t').chan (.srv i) .rd :=
  potential (Q := fun u => (ss (cfg qs ev u) i).2.2.1 = true)
    (G := fun u => .D ∈ (cfg qs ev u).chan (.srv i) .rd)
    (R := fun u => ∃ c, ev u = .tick (.srv i) c) (fun u => potR (ss (cfg qs ev u) i)) htick
    (fun u hu => potR_step qs _ hu (ev u)) t hpd

/-- An outstanding query is eventually answered (the answer is in transit). -/
lemma sent_to_D (hfair : (alg qs).Fair fp ev) {i : Fin n}
    (hr : ¬ Algorithm.Crashed fp ev .rd) (hs : ¬ Algorithm.Crashed fp ev (.srv i))
    (hch : fp.chans = ∅) (hI : ∀ t, ∃ α, Inv qs (cfg qs ev t) α) (t : ℕ)
    (h : (rs (cfg qs ev t)).sentAt i ≠ none) :
    ∃ t' ≥ t, .D ∈ (cfg qs ev t').chan (.srv i) .rd := by
  have htick := hfair.1 _ hs
  have hnoch : ∀ a b, (a, b) ∉ fp.chans := by intro a b; rw [hch]; simp
  obtain ⟨α, hα⟩ := hI t
  rcases tokQ_cases hα h with hQ | hpd | hD
  · obtain ⟨t₁, ht₁, he, hh⟩ := hfair.delivered hr hs (hnoch _ _) 0 t .Q (by rw [hQ]; rfl)
    obtain ⟨α₁, hα₁⟩ := hI t₁
    have hQ' : (cfg qs ev t₁).chan .rd (.srv i) = [.Q] := by
      rcases chan_rd_srv hα₁ i with h' | h'
      · rw [h'] at hh; simp at hh
      · exact h'
    have hpd : (ss (cfg qs ev (t₁ + 1)) i).2.2.1 = true := by
      rw [cfg_succ, he]; exact deliver_Q_pd qs _ hQ'
    obtain ⟨t', ht', hD⟩ := pd_to_D htick _ hpd
    exact ⟨t', by omega, hD⟩
  · obtain ⟨t', ht', hD⟩ := pd_to_D htick _ hpd
    exact ⟨t', ht'.le, hD⟩
  · exact ⟨t, le_rfl, hD⟩

/-- An answer in transit is eventually delivered. -/
lemma D_delivered (hfair : (alg qs).Fair fp ev) {i : Fin n}
    (hr : ¬ Algorithm.Crashed fp ev .rd) (hs : ¬ Algorithm.Crashed fp ev (.srv i))
    (hch : fp.chans = ∅) (t : ℕ) (h : .D ∈ (cfg qs ev t).chan (.srv i) .rd) :
    ∃ t₂ ≥ t, ev t₂ = .deliver (.srv i) .rd ∧ ∃ rest, (cfg qs ev t₂).chan (.srv i) .rd = .D :: rest := by
  have hnoch : ∀ a b, (a, b) ∉ fp.chans := by intro a b; rw [hch]; simp
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
  obtain ⟨t₂, ht₂, he, hh⟩ := hfair.delivered hs hr (hnoch _ _) j t .D hj
  exact ⟨t₂, ht₂, he, exists_head hh⟩

end Exec

/-! ### Liveness from the invariant -/

open Classical in
/-- Liveness of the streaming relay, assuming the invariant holds along every execution in the
SWSR environment and `qs ≤ n - f`. -/
theorem live_of_inv {f : ℕ} (hqs : qs ≤ n - f)
    (hInv : ∀ ev : ℕ → Event (Node n) (register (Val B) (fun _ => false)), (∀ t, EvOk (ev t)) →
      ∀ t, ∃ α, Inv qs (cfg qs ev t) α) :
    Live (alg (n := n) (B := B) qs) f := by
  intro fp hch hfail ev hfair hev p hp t₀ o hinv hpend
  have hI := hInv ev hev
  set Cor := Finset.univ.filter fun i => ¬ Algorithm.Crashed fp ev (Node.srv i)
  have hCor : n - f ≤ Cor.card := Relay.card_correct hfail ev
  have hcq : ∀ i ∈ Cor, ¬ Algorithm.Crashed fp ev (Node.srv i) := by
    intro i hi; simpa [Cor] using hi
  by_contra hnr
  have hnr' : ∀ t ≥ t₀, ∀ x, Label.ret p x ∉ ((alg qs).step (cfg qs ev t) (ev t)).2 := by
    intro t ht x hx; exact hnr ⟨t, ht, x, hx⟩
  rcases hev t₀ p o hinv with ⟨rfl, v, rfl⟩ | ⟨rfl, rfl⟩
  · -- a write
    have h1 : (ws (cfg qs ev (t₀ + 1))).busy = true := by
      rw [cfg_succ, hinv]; simp [Algorithm.step, hpend, ws, Config.apply, alg, handle, wInvoke]
    have hst : ∀ t ≥ t₀ + 1, (ws (cfg qs ev t)).busy = true ∧
        (ws (cfg qs ev t)).strm = (ws (cfg qs ev (t₀ + 1))).strm := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact ⟨h1, rfl⟩
      | succ t ht ih =>
        obtain ⟨α, hα⟩ := hI t
        have := wr_stable qs hα ih.1 (ev t) (hnr' t (by omega))
        rw [cfg_succ]; exact ⟨this.1, this.2.trans ih.2⟩
    set N := (ws (cfg qs ev (t₀ + 1))).strm.length
    have hreach : ∀ i ∈ Cor, ∃ T ≥ t₀ + 1, N ≤ (ws (cfg qs ev T)).ackc i := by
      intro i hi
      exact reach (f := fun t => (ws (cfg qs ev t)).ackc i) fun t ht hlt =>
        ack_progress hfair hp (hcq i hi) hch hI t (by rw [(hst t ht).2]; exact hlt)
    choose! T hT1 hT2 using hreach
    set T₀ := Cor.sup T + (t₀ + 1)
    obtain ⟨α, hα⟩ := hI T₀
    have hb := hst T₀ (by omega)
    have hd := hα.wdone hb.1
    rw [← hα.wS, hb.2] at hd
    change (Finset.univ.filter fun i => N ≤ (ws (cfg qs ev T₀)).ackc i).card < qs at hd
    have hsub : Cor ⊆ Finset.univ.filter fun i => N ≤ (ws (cfg qs ev T₀)).ackc i := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hT2 i hi).trans (ackc_mono i (by have := Finset.le_sup (f := T) hi; omega))
    have := Finset.card_le_card hsub
    omega
  · -- a read
    have h1 : (rs (cfg qs ev (t₀ + 1))).busy = true ∧
        ∀ i, (rs (cfg qs ev (t₀ + 1))).sentAt i ≠ none := by
      rw [cfg_succ, hinv]
      refine ⟨by simp [Algorithm.step, hpend, rs, Config.apply, alg, handle, rInvoke], fun i => ?_⟩
      simp only [Algorithm.step, hpend, rs, Config.apply, alg, handle, rInvoke,
        Function.update_self]
      split_ifs <;> simp_all
    set q₀ := (rs (cfg qs ev (t₀ + 1))).q
    have hst : ∀ t ≥ t₀ + 1, (rs (cfg qs ev t)).busy = true ∧ (rs (cfg qs ev t)).q = q₀ := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact ⟨h1.1, rfl⟩
      | succ t ht ih =>
        obtain ⟨α, hα⟩ := hI t
        have := rd_stable qs hα ih.1 (ev t) (hnr' t (by omega))
        rw [cfg_succ]; exact ⟨this.1, this.2.1.trans ih.2⟩
    have hstab : ∀ t ≥ t₀ + 1, (rs (cfg qs ev t)).resp ⊆ (rs (cfg qs ev (t + 1))).resp ∧
        ∀ j, (rs (cfg qs ev (t + 1))).sentAt j = (rs (cfg qs ev t)).sentAt j ∨
          j ∈ (rs (cfg qs ev (t + 1))).resp ∨ (rs (cfg qs ev (t + 1))).sentAt j = some q₀ := by
      intro t ht
      obtain ⟨α, hα⟩ := hI t
      have := rd_stable qs hα (hst t ht).1 (ev t) (hnr' t (by omega))
      rw [(hst t ht).2] at this
      exact ⟨this.2.2.1, this.2.2.2⟩
    -- delivery of an answer of server `i`
    have hans : ∀ i t₂ rest, t₀ + 1 ≤ t₂ → ev t₂ = .deliver (.srv i) .rd →
        (cfg qs ev t₂).chan (.srv i) .rd = .D :: rest →
        ((rs (cfg qs ev t₂)).sentAt i = some q₀ → i ∈ (rs (cfg qs ev (t₂ + 1))).resp) ∧
        ((rs (cfg qs ev t₂)).sentAt i ≠ some q₀ → (rs (cfg qs ev (t₂ + 1))).sentAt i = some q₀) := by
      intro i t₂ rest ht₂ he hc
      obtain ⟨α, hα⟩ := hI t₂
      obtain ⟨hrs, hl⟩ := rd_deliver_D qs _ hc
      obtain ⟨o', ho'⟩ := Option.ne_none_iff_exists'.1 (hα.rbusy.1 (hst t₂ ht₂).1)
      rcases hr : (rAns qs (rs (cfg qs ev t₂)) i).2.2 with _ | x
      · obtain ⟨-, -, -, h4, h5, -⟩ := rAns_of_none qs (hst t₂ ht₂).1 hr
        rw [cfg_succ, he, hrs]
        rw [(hst t₂ ht₂).2] at h4 h5
        exact ⟨h4, h5⟩
      · exact absurd (by rw [he, hl, ho', hr]; simp [respOut]) (hnr' t₂ (by omega) x)
    have hresp : ∀ i ∈ Cor, ∃ T ≥ t₀ + 1, i ∈ (rs (cfg qs ev T)).resp := by
      intro i hi
      by_contra hni
      push Not at hni
      have P1 : ∀ t ≥ t₀ + 1, (rs (cfg qs ev t)).sentAt i ≠ none := by
        intro t ht
        induction t, ht using Nat.le_induction with
        | base => exact h1.2 i
        | succ t ht ih =>
          rcases (hstab t ht).2 i with h | h | h
          · rw [h]; exact ih
          · exact absurd h (hni _ (by omega))
          · rw [h]; simp
      obtain ⟨t', ht', hD⟩ := sent_to_D hfair hp (hcq i hi) hch hI _ (P1 _ le_rfl)
      obtain ⟨t₂, ht₂, he, rest, hc⟩ := D_delivered hfair hp (hcq i hi) hch _ hD
      have hs₂ : (rs (cfg qs ev (t₂ + 1))).sentAt i = some q₀ := by
        have := hans i t₂ rest (by omega) he hc
        by_cases hs : (rs (cfg qs ev t₂)).sentAt i = some q₀
        · exact absurd (this.1 hs) (hni _ (by omega))
        · exact this.2 hs
      have P2 : ∀ t ≥ t₂ + 1, (rs (cfg qs ev t)).sentAt i = some q₀ := by
        intro t ht
        induction t, ht using Nat.le_induction with
        | base => exact hs₂
        | succ t ht ih =>
          rcases (hstab t (by omega)).2 i with h | h | h
          · rw [h]; exact ih
          · exact absurd h (hni _ (by omega))
          · exact h
      obtain ⟨t₃, ht₃, hD₃⟩ := sent_to_D hfair hp (hcq i hi) hch hI (t₂ + 1) (by rw [hs₂]; simp)
      obtain ⟨t₄, ht₄, he₄, rest₄, hc₄⟩ := D_delivered hfair hp (hcq i hi) hch _ hD₃
      exact hni _ (by omega) ((hans i t₄ rest₄ (by omega) he₄ hc₄).1 (P2 t₄ (by omega)))
    choose! T hT1 hT2 using hresp
    set T₀ := Cor.sup T + (t₀ + 1)
    have hmono : ∀ t ≥ t₀ + 1, (rs (cfg qs ev t)).resp ⊆ (rs (cfg qs ev (t + 1))).resp :=
      fun t ht => (hstab t ht).1
    have hall : Cor ⊆ (rs (cfg qs ev T₀)).resp := by
      intro i hi
      exact Relay.subset_of_le hmono (T i) T₀ (hT1 i hi)
        (by have := Finset.le_sup (f := T) hi; omega) (hT2 i hi)
    obtain ⟨α, hα⟩ := hI T₀
    have := (hα.rcur (hst T₀ (by omega)).1).1
    have := Finset.card_le_card hall
    omega

end Live

/-- **The streaming relay is live** with quorum size `qs = n - f`, `2 f < n` and `B > 0`. -/
theorem isLive {f : ℕ} (hf : 2 * f < n) (hB : 0 < B) :
    Live (alg (n := n) (B := B) (n - f)) f :=
  Live.live_of_inv (n - f) le_rfl fun ev hev t => ⟨_, by
    rw [Live.cfg, Algorithm.cfgAt_eq_run]
    exact inv_reach (n - f) (by omega) (by omega) hB _ (fun e he => by
      simp only [Algorithm.pre, List.mem_map] at he; obtain ⟨u, -, rfl⟩ := he; exact hev u)⟩

end Podc.StorageCost.Stream
