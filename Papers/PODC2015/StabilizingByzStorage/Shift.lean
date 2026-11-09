import Papers.PODC2015.StabilizingByzStorage.Atomic

/-!
# Translation invariance of Fig. 3

Adding `c` to every sequence number (mod `m`) and to every value (in `ℕ`) maps steps to steps
(`Step.shift`). Used to repeat the counterexample cycle forever.
-/

namespace Podc.StabilizingByzStorage

variable {n : ℕ}

namespace WMsg
variable {D E : Type}
/-- Apply `f` to the payload. -/
def map (f : D → E) : WMsg D → WMsg E
  | .write d => .write (f d)
  | .newHelp d => .newHelp (f d)
end WMsg

namespace Server
variable {D E : Type}

/-- Apply `f` to every payload in a server state (including the links and reply slots). -/
def map (f : D → E) (s : Server D) : Server E :=
  ⟨f s.last, s.help.map f, s.wq.map (WMsg.map f), s.rq, s.wack.map (Option.map f),
    s.rack.map (fun p => (f p.1, p.2.map f))⟩

lemma map_deliverW (f : D → E) (s : Server D) : (s.map f).deliverW = s.deliverW.map f := by
  rcases s with ⟨l, h, wq, rq, wa, ra⟩
  cases wq with
  | nil => rfl
  | cons x rest =>
    cases x with
    | write d =>
      simp only [map, deliverW, List.map_cons, WMsg.map, List.map_eq_nil_iff]
      split_ifs <;> simp
    | newHelp d => simp [map, deliverW, WMsg.map]

lemma map_deliverR (f : D → E) (s : Server D) : (s.map f).deliverR = s.deliverR.map f := by
  rcases s with ⟨l, h, wq, rq, wa, ra⟩
  cases rq with
  | nil => rfl
  | cons b rest =>
    cases b <;> simp only [map, deliverR] <;> split_ifs <;> simp

lemma map_bcastW (f : D → E) (m : WMsg D) (s : Server D) :
    (s.map f).bcastW (m.map f) = (s.bcastW m).map f := by
  simp [map, bcastW]

lemma map_bcastR (f : D → E) (b : Bool) (s : Server D) :
    (s.map f).bcastR b = (s.bcastR b).map f := by
  simp [map, bcastR]

@[simp] lemma map_wq_eq_nil (f : D → E) (s : Server D) : (s.map f).wq = [] ↔ s.wq = [] := by
  simp [map]

@[simp] lemma map_rq (f : D → E) (s : Server D) : (s.map f).rq = s.rq := rfl

@[simp] lemma map_wack (f : D → E) (s : Server D) : (s.map f).wack = s.wack.map (Option.map f) :=
  rfl

@[simp] lemma map_rack (f : D → E) (s : Server D) :
    (s.map f).rack = s.rack.map (fun p => (f p.1, p.2.map f)) := rfl

end Server

lemma syncW_map {D E : Type} (B : Finset (Fin n)) (f : D → E) (srv : Fin n → Server D) :
    syncW B (fun s => (srv s).map f) = syncW B srv := by
  simp [syncW]

lemma syncR_map {D E : Type} (B : Finset (Fin n)) (f : D → E) (srv : Fin n → Server D) :
    syncR B (fun s => (srv s).map f) = syncR B srv := rfl

lemma cnt_comp {α β : Type} [DecidableEq α] [DecidableEq β] (Q : Finset (Fin n)) (g : Fin n → α)
    {f : α → β} (hf : Function.Injective f) (a : α) : cnt Q (f ∘ g) (f a) = cnt Q g a := by
  simp [cnt, hf.eq_iff]

lemma exists_le_cnt_comp {α β : Type} [DecidableEq α] [DecidableEq β] (Q : Finset (Fin n))
    (g : Fin n → α) {f : α → β} (hf : Function.Injective f) {k : ℕ} (hk : 1 ≤ k) :
    (∃ b, k ≤ cnt Q (f ∘ g) b) ↔ ∃ a, k ≤ cnt Q g a := by
  rw [exists_le_cnt_iff _ _ hk, exists_le_cnt_iff _ _ hk]
  simp only [Function.comp_apply, cnt_comp Q g hf]

lemma exists_le_cnt_some_comp {α β : Type} [DecidableEq α] [DecidableEq β] (Q : Finset (Fin n))
    (g : Fin n → Option α) {f : α → β} (hf : Function.Injective f) {k : ℕ} (hk : 1 ≤ k) :
    (∃ b, k ≤ cnt Q (Option.map f ∘ g) (some b)) ↔ ∃ a, k ≤ cnt Q g (some a) := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨s, hs⟩ : (Q.filter fun s => (Option.map f ∘ g) s = some b).Nonempty := by
      rw [← Finset.card_pos]; unfold cnt at hb; omega
    simp only [Finset.mem_filter, Function.comp_apply, Option.map_eq_some_iff] at hs
    obtain ⟨-, a, ha, rfl⟩ := hs
    refine ⟨a, ?_⟩
    rwa [← Option.map_some, cnt_comp Q g (Option.map_injective hf)] at hb
  · rintro ⟨a, ha⟩
    exact ⟨f a, by rwa [← Option.map_some, cnt_comp Q g (Option.map_injective hf)]⟩

lemma exists_le_cnt_some_comp' {α β : Type} [DecidableEq α] [DecidableEq β] (Q : Finset (Fin n))
    (g : Fin n → Option α) {f : α → β} (hf : Function.Injective f) {k : ℕ} (hk : 1 ≤ k) :
    (∃ b, k ≤ cnt Q (fun s => Option.map f (g s)) (some b)) ↔ ∃ a, k ≤ cnt Q g (some a) :=
  exists_le_cnt_some_comp Q g hf hk

namespace Atomic

variable {m : ℕ} [NeZero m]

/-- Shift a payload: sequence number `+ c (mod m)`, value `+ c`. -/
def shD (c : ℕ) (d : Fin m × ℕ) : Fin m × ℕ := (d.1 + Fin.ofNat m c, d.2 + c)

lemma shD_injective (c : ℕ) : Function.Injective (shD (m := m) c) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [shD, Prod.mk.injEq, add_left_inj] at h
  rw [h.1, h.2]

lemma gtcd_add (x y z : Fin m) : gtcd (x + z) (y + z) ↔ gtcd x y := by
  simp [gtcd, add_sub_add_right_eq_sub]

def WPhase.shift (c : ℕ) : WPhase ℕ → WPhase ℕ
  | .idle => .idle
  | .bcastWrite v => .bcastWrite (v + c)
  | .waitAck v => .waitAck (v + c)
  | .bcastHelp => .bcastHelp

/-- Shift a whole configuration. -/
def State.shift (c : ℕ) (σ : State n m ℕ) : State n m ℕ :=
  ⟨fun s => (σ.srv s).map (shD c), ⟨σ.w.wsn + Fin.ofNat m c, σ.w.phase.shift c⟩,
    ⟨σ.r.pwsn + Fin.ofNat m c, σ.r.pv + c, σ.r.phase⟩⟩

def Label.shift (c : ℕ) : Label ℕ → Label ℕ
  | .invWrite v => .invWrite (v + c)
  | .retWrite => .retWrite
  | .invRead => .invRead
  | .retRead v => .retRead (v + c)
  | .tau => .tau

variable (t : ℕ) (B : Finset (Fin n))

lemma shift_update (c : ℕ) (σ : State n m ℕ) (s : Fin n) (x : Server (Fin m × ℕ)) :
    (fun s' => (Function.update σ.srv s x s').map (shD c)) =
      Function.update (fun s' => (σ.srv s').map (shD c)) s (x.map (shD c)) := by
  funext s'; by_cases h : s' = s <;> simp [h]

/-- Steps are invariant under shifting sequence numbers and values. -/
theorem Step.shift (c : ℕ) {σ σ' : State n m ℕ} {ℓ : Label ℕ} (h : Step t B σ ℓ σ') :
    Step t B (σ.shift c) (ℓ.shift c) (σ'.shift c) := by
  have hi := shD_injective (m := m) c
  have hoi : Function.Injective (Option.map (shD (m := m) c)) := Option.map_injective hi
  cases h with
  | delivW s h =>
    have := Step.delivW (t := t) (B := B) (σ.shift c) s (by simpa [State.shift, Server.map] using h)
    simpa [State.shift, Label.shift, shift_update, Server.map_deliverW] using this
  | delivR s h =>
    have := Step.delivR (t := t) (B := B) (σ.shift c) s (by simpa [State.shift] using h)
    simpa [State.shift, Label.shift, shift_update, Server.map_deliverR] using this
  | invWrite v h =>
    have := Step.invWrite (t := t) (B := B) (σ.shift c) (v + c) (by simp [State.shift, h, WPhase.shift])
    convert this using 1 <;> try rfl
    simp only [State.shift, State.bcastW, WPhase.shift, State.mk.injEq, Writer.mk.injEq, and_true]
    refine ⟨funext fun s => ?_, add_right_comm _ _ _⟩
    rw [← Server.map_bcastW]
    simp only [WMsg.map, shD, State.bcastW, add_right_comm]
  | endWrite v h hs =>
    have := Step.endWrite (t := t) (B := B) (σ.shift c) (v + c) (by simp [State.shift, h, WPhase.shift])
      (by simpa [State.shift, syncW_map] using hs)
    simpa [State.shift, WPhase.shift, Label.shift] using this
  | ackDone v h Q acks hQ hacks hc =>
    have := Step.ackDone (t := t) (B := B) (σ.shift c) (v + c)
      (by simp [State.shift, h, WPhase.shift]) Q (fun s => (acks s).map (shD c)) hQ
      (fun s hs hb => by simp [State.shift, hacks s hs hb])
      (by rw [exists_le_cnt_some_comp' Q acks hi (by omega)]; exact hc)
    simpa [State.shift, WPhase.shift, Label.shift] using this
  | ackHelp v h Q acks hQ hacks hc =>
    have := Step.ackHelp (t := t) (B := B) (σ.shift c) (v + c)
      (by simp [State.shift, h, WPhase.shift]) Q (fun s => (acks s).map (shD c)) hQ
      (fun s hs hb => by simp [State.shift, hacks s hs hb])
      (by rw [exists_le_cnt_some_comp' Q acks hi (by omega)]; exact hc)
    convert this using 1 <;> try rfl
    simp only [State.shift, State.bcastW, WPhase.shift, State.mk.injEq, and_true]
    funext s
    rw [← Server.map_bcastW]; rfl
  | endHelp h hs =>
    have := Step.endHelp (t := t) (B := B) (σ.shift c) (by simp [State.shift, h, WPhase.shift])
      (by simpa [State.shift, syncW_map] using hs)
    simpa [State.shift, WPhase.shift, Label.shift] using this
  | invRead h =>
    have := Step.invRead (t := t) (B := B) (σ.shift c) (by simpa [State.shift] using h)
    convert this using 1 <;> try rfl
  | endPre h hs =>
    have := Step.endPre (t := t) (B := B) (σ.shift c) (by simpa [State.shift] using h)
      (by simpa [State.shift, syncR_map] using hs)
    simpa [State.shift, Label.shift] using this
  | preAdopt h Q reps hQ hreps d hd =>
    have := Step.preAdopt (t := t) (B := B) (σ.shift c) (by simpa [State.shift] using h) Q
      (fun s => (shD c (reps s).1, (reps s).2.map (shD c))) hQ
      (fun s hs hb => by simp [State.shift, hreps s hs hb]) (shD c d)
      (by
        have := cnt_comp Q (fun s => (reps s).2) hoi (some d)
        simp only [Function.comp_def, Option.map_some] at this
        rw [this]; exact hd)
    convert this using 1 <;> try rfl
    simp only [State.shift, State.bcastR, State.mk.injEq, true_and]
    refine ⟨funext fun s => by rw [← Server.map_bcastR]; rfl, ?_⟩
    simp only [shD, gtcd_add]
    split_ifs <;> rfl
  | preNone h Q reps hQ hreps hd =>
    have := Step.preNone (t := t) (B := B) (σ.shift c) (by simpa [State.shift] using h) Q
      (fun s => (shD c (reps s).1, (reps s).2.map (shD c))) hQ
      (fun s hs hb => by simp [State.shift, hreps s hs hb])
      (by
        have := exists_le_cnt_some_comp' Q (fun s => (reps s).2) hi (k := 2 * t + 1) (by omega)
        simp only at this ⊢; rw [this]; exact hd)
    convert this using 1 <;> try rfl
  | endLoop h hs =>
    have := Step.endLoop (t := t) (B := B) (σ.shift c) (by simpa [State.shift] using h)
      (by simpa [State.shift, syncR_map] using hs)
    simpa [State.shift, Label.shift] using this
  | retLast h Q reps hQ hreps d hd =>
    have := Step.retLast (t := t) (B := B) (σ.shift c) (by simpa [State.shift] using h) Q
      (fun s => (shD c (reps s).1, (reps s).2.map (shD c))) hQ
      (fun s hs hb => by simp [State.shift, hreps s hs hb]) (shD c d)
      (by
        have := cnt_comp Q (fun s => (reps s).1) hi d
        simp only [Function.comp_def] at this
        rw [this]; exact hd)
    convert this using 1
    · simp only [Label.shift, shD, State.shift, gtcd_add]; split_ifs <;> rfl
    · simp only [State.shift, shD, gtcd_add]; split_ifs <;> rfl
  | retHelp h Q reps hQ hreps hl d hd =>
    have := Step.retHelp (t := t) (B := B) (σ.shift c) (by simpa [State.shift] using h) Q
      (fun s => (shD c (reps s).1, (reps s).2.map (shD c))) hQ
      (fun s hs hb => by simp [State.shift, hreps s hs hb])
      (by
        have := exists_le_cnt_comp Q (fun s => (reps s).1) hi (k := 2 * t + 1) (by omega)
        simp only [Function.comp_def] at this; rw [this]; exact hl)
      (shD c d)
      (by
        have := cnt_comp Q (fun s => (reps s).2) hoi (some d)
        simp only [Function.comp_def, Option.map_some] at this
        rw [this]; exact hd)
    simpa [State.shift, Label.shift, shD] using this
  | retry h Q reps hQ hreps hl hh =>
    have := Step.retry (t := t) (B := B) (σ.shift c) (by simpa [State.shift] using h) Q
      (fun s => (shD c (reps s).1, (reps s).2.map (shD c))) hQ
      (fun s hs hb => by simp [State.shift, hreps s hs hb])
      (by
        have := exists_le_cnt_comp Q (fun s => (reps s).1) hi (k := 2 * t + 1) (by omega)
        simp only [Function.comp_def] at this; rw [this]; exact hl)
      (by
        have := exists_le_cnt_some_comp' Q (fun s => (reps s).2) hi (k := 2 * t + 1) (by omega)
        simp only at this ⊢; rw [this]; exact hh)
    convert this using 1 <;> try rfl

end Atomic
end Podc.StabilizingByzStorage
