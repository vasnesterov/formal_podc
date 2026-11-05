import Papers.PODC2013.MessageAdversariesVsFD.Async
import Papers.PODC2013.MessageAdversariesVsFD.Tasks

/-!
# `Tseen` is solvable in `AMP_{3,2}[fd : Σ]`

Counterexample to Lemma 6 and Theorem 4 of Raynal–Stainer (PODC 2013), positive half: the task
`Tseen` ("at least one of `p₁`, `p₂` sees the input of the other"; not from the paper) is solvable
in `AMP_{n,n-1}[fd : Σ]`, by the read/write algorithm "write your input, then read" on top of an
ABD-like register emulation whose quorums are given by `Σ`. We give a self-contained algorithm and
a complete proof.

## Algorithm (every process runs it; processes are `0, 1, 2`)

Every process broadcasts its whole local state at each of its steps. A local state records
* `v`: the inputs it knows (initially its own; merged with the `v` of every received message),
* `rd`: the processes from which it received a message sent in their *read phase*,
* `acks`: the senders of received messages that knew its own input (write acknowledgements),
* `resps`: the senders of received messages whose `rd` contained it (read responses),
* `phase`: `0` (writing), `1` (reading), `2` (done).

At a step, after processing the received message (if any), a process in phase `0` moves to
phase `1` if its current `Σ` output `d` satisfies `d ⊆ acks` (its write is complete), and a
process in phase `1` moves to phase `2` if `d ⊆ resps` (its read is complete); it then outputs
`pair x₀ x₁` if it knows both inputs, `alone` otherwise.

## Proof idea

*Safety* (not both `0` and `1` output `alone`): let `w_p` be the time at which `p` completes its
write. If `p` outputs `alone`, take `k` in the intersection of `p`'s read quorum and `q`'s write
quorum; `k`'s response to `p` was sent after `w_p` (it follows the reception of a read-phase
message of `p`) and did not contain `x_q`, while `k`'s acknowledgement to `q` contained `x_q` and
was sent before `w_q`; as knowledge is monotone, `w_p < w_q`. Both outputting `alone` would give
`w₀ < w₁ < w₀`.

*Liveness*: reliable delivery, infinitely many time-outs of correct processes, and the liveness of
`Σ` (eventually the quorums of a correct process contain only correct processes).
-/

namespace Podc.MessageAdversariesVsFD

namespace SigmaSeen

open Cslib.FailureDetectors

/-- Local state (also the message type: processes broadcast their whole state). -/
structure LSt where
  /-- Known inputs. -/
  v : Fin 3 → Option Bool
  /-- Processes from which a read-phase message was received. -/
  rd : Set (Fin 3)
  /-- Write acknowledgements received. -/
  acks : Set (Fin 3)
  /-- Read responses received. -/
  resps : Set (Fin 3)
  /-- `0`: writing, `1`: reading, `2`: done. -/
  phase : ℕ

/-- Process `p` receives the state `m` broadcast by `k`. -/
def recvMsg (p k : Fin 3) (m s : LSt) : LSt where
  v q := (s.v q).or (m.v q)
  rd := s.rd ∪ {j | j = k ∧ 1 ≤ m.phase}
  acks := s.acks ∪ {j | j = k ∧ (m.v p).isSome}
  resps := s.resps ∪ {j | j = k ∧ p ∈ m.rd}
  phase := s.phase

/-- Processing the event consumed by a step of `p`. -/
def receive (p : Fin 3) : Event (Fin 3) LSt Empty → LSt → LSt
  | .recv k m, s => recvMsg p k m s
  | .tick, s => s
  | .input i, _ => i.elim

open Classical in
/-- Phase change with the current `Σ` output `d`. -/
noncomputable def advance (d : Set (Fin 3)) (s : LSt) : LSt :=
  if s.phase = 0 ∧ d ⊆ s.acks then { s with phase := 1 }
  else if s.phase = 1 ∧ d ⊆ s.resps then { s with phase := 2 } else s

/-- The value output: the pair of inputs if both are known, `alone` otherwise. -/
def answer (s : LSt) : Seen :=
  match s.v 0, s.v 1 with
  | some a, some b => .pair a b
  | _, _ => .alone

/-- The algorithm (identical code for the three processes). -/
noncomputable def alg : AlgAMP (Fin 3) (Set (Fin 3)) LSt Bool Seen LSt where
  init p b := ⟨fun q => if q = p then some b else none, ∅, ∅, ∅, 0⟩
  step p d s e :=
    (advance d (receive p e s), some (advance d (receive p e s)),
      if s.phase = 1 ∧ (advance d (receive p e s)).phase = 2 then [answer (advance d (receive p e s))]
      else [])

/-! ### Local facts about steps -/

/-- Knowledge order on local states. -/
def Le (s s' : LSt) : Prop :=
  (∀ q b, s.v q = some b → s'.v q = some b) ∧ s.rd ⊆ s'.rd ∧ s.acks ⊆ s'.acks ∧
    s.resps ⊆ s'.resps ∧ s.phase ≤ s'.phase

lemma Le.refl (s : LSt) : Le s s := ⟨fun _ _ h => h, subset_rfl, subset_rfl, subset_rfl, le_rfl⟩

lemma Le.trans {a b c : LSt} (h₁ : Le a b) (h₂ : Le b c) : Le a c :=
  ⟨fun q y h => h₂.1 q y (h₁.1 q y h), h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    h₁.2.2.2.1.trans h₂.2.2.2.1, h₁.2.2.2.2.trans h₂.2.2.2.2⟩

lemma advance_v (d : Set (Fin 3)) (s : LSt) : (advance d s).v = s.v := by
  unfold advance; split_ifs <;> rfl

lemma advance_rd (d : Set (Fin 3)) (s : LSt) : (advance d s).rd = s.rd := by
  unfold advance; split_ifs <;> rfl

lemma advance_acks (d : Set (Fin 3)) (s : LSt) : (advance d s).acks = s.acks := by
  unfold advance; split_ifs <;> rfl

lemma advance_resps (d : Set (Fin 3)) (s : LSt) : (advance d s).resps = s.resps := by
  unfold advance; split_ifs <;> rfl

lemma le_advance (d : Set (Fin 3)) (s : LSt) : Le s (advance d s) := by
  unfold advance; split_ifs with h₁ h₂
  · exact ⟨fun _ _ h => h, subset_rfl, subset_rfl, subset_rfl, by simp [h₁.1]⟩
  · exact ⟨fun _ _ h => h, subset_rfl, subset_rfl, subset_rfl, by simp [h₂.1]⟩
  · exact Le.refl s

/-- The phase changes only `0 → 1` (write complete) or `1 → 2` (read complete). -/
lemma advance_phase (d : Set (Fin 3)) (s : LSt) :
    (advance d s).phase = s.phase ∨ (s.phase = 0 ∧ d ⊆ s.acks ∧ (advance d s).phase = 1) ∨
      (s.phase = 1 ∧ d ⊆ s.resps ∧ (advance d s).phase = 2) := by
  unfold advance; split_ifs with h₁ h₂
  · exact Or.inr (Or.inl ⟨h₁.1, h₁.2, rfl⟩)
  · exact Or.inr (Or.inr ⟨h₂.1, h₂.2, rfl⟩)
  · exact Or.inl rfl

lemma le_receive (p : Fin 3) (e : Event (Fin 3) LSt Empty) (s : LSt) : Le s (receive p e s) := by
  cases e with
  | recv k m =>
    refine ⟨fun q b h => by simp [receive, recvMsg, h], Set.subset_union_left,
      Set.subset_union_left, Set.subset_union_left, le_rfl⟩
  | tick => exact Le.refl s
  | input i => exact i.elim

lemma receive_phase (p : Fin 3) (e : Event (Fin 3) LSt Empty) (s : LSt) :
    (receive p e s).phase = s.phase := by
  cases e with
  | recv k m => rfl
  | tick => rfl
  | input i => exact i.elim

lemma le_step (p : Fin 3) (d : Set (Fin 3)) (e : Event (Fin 3) LSt Empty) (s : LSt) :
    Le s (advance d (receive p e s)) :=
  (le_receive p e s).trans (le_advance d _)

lemma answer_ok (x : Fin 3 → Bool) (s : LSt) (hs : ∀ q b, s.v q = some b → b = x q) :
    Seen.Ok x (answer s) := by
  unfold answer
  rcases h0 : s.v 0 with _ | a <;> rcases h1 : s.v 1 with _ | b <;> simp [Seen.Ok]
  exact ⟨hs 0 a h0, hs 1 b h1⟩

lemma answer_alone {s : LSt} (h : answer s = .alone) (hs : (s.v 0).isSome) : s.v 1 = none := by
  unfold answer at h
  rcases h0 : s.v 0 with _ | a
  · simp [h0] at hs
  · rcases h1 : s.v 1 with _ | b
    · rfl
    · simp [h0, h1] at h

lemma answer_alone' {s : LSt} (h : answer s = .alone) (hs : (s.v 1).isSome) : s.v 0 = none := by
  unfold answer at h
  rcases h1 : s.v 1 with _ | b
  · simp [h1] at hs
  · rcases h0 : s.v 0 with _ | a
    · rfl
    · simp [h0, h1] at h

/-! ### Runs -/

variable (x : Fin 3 → Bool) (r : Run (Fin 3) (Set (Fin 3)) Empty)

/-- Local state of `p` before time `t`. -/
noncomputable abbrev stt (p : Fin 3) (t : ℕ) : LSt := (alg.toAlg x).st r p t

/-- A stored message is the state of its sender right after its sending step. -/
lemma msg_eq {t a : ℕ} {k : Fin 3} {m : LSt} (h : ((alg.toAlg x).cfg r t).msg a = some (k, m)) :
    a < t ∧ m = stt x r k (a + 1) := by
  refine ⟨?_, ?_⟩
  · by_contra hc
    rw [Algorithm.msg_eq_none_of_le r t a (by omega)] at h
    simp at h
  · obtain ⟨c, e, hσ, he, hb⟩ := Algorithm.msg_spec r h
    rw [stt, (Algorithm.cfg_succ_of_event r a k c e hσ he).1]
    exact (Option.some.inj hb).symm

/-- How a local state evolves in one time unit. -/
lemma st_succ_cases (t : ℕ) (p : Fin 3) :
    stt x r p (t + 1) = stt x r p t ∨
    ∃ c e, r.σ t = some (p, c) ∧ ((alg.toAlg x).cfg r t).event c = some e ∧
      stt x r p (t + 1) = advance (r.H p t) (receive p e (stt x r p t)) ∧
      (e = .tick ∨ ∃ k a, a < t ∧ e = .recv k (stt x r k (a + 1))) := by
  rcases hσ : r.σ t with _ | ⟨q, c⟩
  · left; exact Algorithm.loc_succ_of_ne r t p (by simp [hσ])
  · by_cases hq : q = p
    · subst hq
      rcases he : ((alg.toAlg x).cfg r t).event c with _ | e
      · left; simp [stt, Algorithm.st, (Algorithm.cfg_succ_of_event_none r t q c hσ he).1]
      · right
        refine ⟨c, e, rfl, he, (Algorithm.cfg_succ_of_event r t q c e hσ he).1, ?_⟩
        cases e with
        | tick => left; rfl
        | input i => exact i.elim
        | recv k m =>
          right
          obtain ⟨a, rfl, hm⟩ := Algorithm.event_eq_recv he
          obtain ⟨ha, rfl⟩ := msg_eq x r hm
          exact ⟨k, a, ha, rfl⟩
    · left
      exact Algorithm.loc_succ_of_ne r t p
        (by intro c' h; rw [hσ] at h; simp at h; exact hq h.1)

lemma st_succ_le (t : ℕ) (p : Fin 3) : Le (stt x r p t) (stt x r p (t + 1)) := by
  rcases st_succ_cases x r t p with h | ⟨c, e, -, -, h, -⟩
  · rw [h]; exact Le.refl _
  · rw [h]; exact le_step p _ e _

/-- Knowledge only grows. -/
lemma st_mono (p : Fin 3) {t t' : ℕ} (h : t ≤ t') : Le (stt x r p t) (stt x r p t') := by
  induction t', h using Nat.le_induction with
  | base => exact Le.refl _
  | succ t' _ ih => exact ih.trans (st_succ_le x r t' p)

lemma st_zero (p : Fin 3) : stt x r p 0 = alg.init p (x p) := rfl

/-- A process knows its own input. -/
lemma v_self (p : Fin 3) (t : ℕ) : (stt x r p t).v p = some (x p) :=
  (st_mono x r p (Nat.zero_le t)).1 p (x p) (by simp [st_zero, alg])

/-- Known inputs are correct. -/
lemma v_correct : ∀ t p q b, (stt x r p t).v q = some b → b = x q := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro p q b h
    rcases t with _ | t
    · simp only [st_zero, alg] at h
      split_ifs at h with hq
      · subst hq; exact (Option.some.inj h).symm
    · rcases st_succ_cases x r t p with hs | ⟨c, e, -, -, hs, he⟩
      · rw [hs] at h; exact ih t (by omega) p q b h
      · rw [hs, advance_v] at h
        rcases he with rfl | ⟨k, a, ha, rfl⟩
        · exact ih t (by omega) p q b h
        · simp only [receive, recvMsg] at h
          rcases h' : (stt x r p t).v q with _ | b'
          · rw [h'] at h
            exact ih (a + 1) (by omega) k q b (by simpa using h)
          · rw [h'] at h
            have hb : b' = b := by simpa using h
            rw [← hb]; exact ih t (by omega) p q b' h'

/-- Write acknowledgements come from processes that knew the input. -/
lemma acks_spec : ∀ t p k, k ∈ (stt x r p t).acks → ∃ a < t, ((stt x r k (a + 1)).v p).isSome := by
  intro t
  induction t with
  | zero => intro p k h; simp [st_zero, alg] at h
  | succ t ih =>
    intro p k h
    rcases st_succ_cases x r t p with hs | ⟨c, e, -, -, hs, he⟩
    · rw [hs] at h
      obtain ⟨a, ha, h'⟩ := ih p k h; exact ⟨a, by omega, h'⟩
    · rw [hs, advance_acks] at h
      rcases he with rfl | ⟨k', a, ha, rfl⟩
      · obtain ⟨a, ha, h'⟩ := ih p k h; exact ⟨a, by omega, h'⟩
      · simp only [receive, recvMsg, Set.mem_union, Set.mem_ofPred_eq] at h
        rcases h with h | ⟨rfl, h⟩
        · obtain ⟨a, ha, h'⟩ := ih p k h; exact ⟨a, by omega, h'⟩
        · exact ⟨a, by omega, h⟩

/-- Read-phase messages: `p ∈ rd` of `k` only after `p` entered its read phase. -/
lemma rd_spec : ∀ t k p, p ∈ (stt x r k t).rd → ∃ a < t, 1 ≤ (stt x r p (a + 1)).phase := by
  intro t
  induction t with
  | zero => intro k p h; simp [st_zero, alg] at h
  | succ t ih =>
    intro k p h
    rcases st_succ_cases x r t k with hs | ⟨c, e, -, -, hs, he⟩
    · rw [hs] at h
      obtain ⟨a, ha, h'⟩ := ih k p h; exact ⟨a, by omega, h'⟩
    · rw [hs, advance_rd] at h
      rcases he with rfl | ⟨k', a, ha, rfl⟩
      · obtain ⟨a, ha, h'⟩ := ih k p h; exact ⟨a, by omega, h'⟩
      · simp only [receive, recvMsg, Set.mem_union, Set.mem_ofPred_eq] at h
        rcases h with h | ⟨rfl, h⟩
        · obtain ⟨a, ha, h'⟩ := ih k p h; exact ⟨a, by omega, h'⟩
        · exact ⟨a, by omega, h⟩

/-- Read responses: a response of `k` to `p` was sent by `k` after `p` entered its read phase
(`p ∈ rd`), and every input unknown to `p` was unknown to `k` when it sent the response. -/
lemma resps_spec : ∀ t p k, k ∈ (stt x r p t).resps → ∃ a < t, p ∈ (stt x r k (a + 1)).rd ∧
    ∀ q, (stt x r p t).v q = none → (stt x r k (a + 1)).v q = none := by
  intro t
  induction t with
  | zero => intro p k h; simp [st_zero, alg] at h
  | succ t ih =>
    have hnone : ∀ p q, (stt x r p (t + 1)).v q = none → (stt x r p t).v q = none := by
      intro p q h
      rcases h' : (stt x r p t).v q with _ | b
      · rfl
      · rw [(st_succ_le x r t p).1 q b h'] at h; simp at h
    intro p k h
    rcases st_succ_cases x r t p with hs | ⟨c, e, -, -, hs, he⟩
    · obtain ⟨a, ha, h₁, h₂⟩ := ih p k (hs ▸ h)
      exact ⟨a, by omega, h₁, fun q hq => h₂ q (hnone p q hq)⟩
    · have h' := h
      rw [hs, advance_resps] at h'
      rcases he with rfl | ⟨k', a, ha, he⟩
      · obtain ⟨a, ha, h₁, h₂⟩ := ih p k h'
        exact ⟨a, by omega, h₁, fun q hq => h₂ q (hnone p q hq)⟩
      · rw [he] at h'
        simp only [receive, recvMsg, Set.mem_union, Set.mem_ofPred_eq] at h'
        rcases h' with h' | ⟨rfl, h'⟩
        · obtain ⟨a, ha, h₁, h₂⟩ := ih p k h'
          exact ⟨a, by omega, h₁, fun q hq => h₂ q (hnone p q hq)⟩
        · refine ⟨a, by omega, h', fun q hq => ?_⟩
          rw [hs, advance_v, he] at hq
          simp only [receive, recvMsg, Option.or_eq_none_iff] at hq
          exact hq.2

/-- The end of the write phase of `p`: the unique step `w` at which `p` moves to phase `1`; its
`Σ` output at that step is contained in its acknowledgements. -/
lemma exists_write_end (p : Fin 3) {t : ℕ} (ht : 1 ≤ (stt x r p t).phase) :
    ∃ w, (∀ t', 1 ≤ (stt x r p t').phase ↔ w < t') ∧ r.H p w ⊆ (stt x r p (w + 1)).acks := by
  classical
  have hex : ∃ t, 1 ≤ (stt x r p t).phase := ⟨t, ht⟩
  have h0 : Nat.find hex ≠ 0 := by
    intro h; have := Nat.find_spec hex; rw [h] at this; simp [st_zero, alg] at this
  obtain ⟨w, hw⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have hlt : ¬ 1 ≤ (stt x r p w).phase := Nat.find_min hex (by omega)
  have hspec : 1 ≤ (stt x r p (w + 1)).phase := by
    have := Nat.find_spec hex; rw [hw] at this; exact this
  refine ⟨w, fun t' => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · by_contra hc
    exact Nat.find_min hex (by omega : t' < Nat.find hex) h
  · exact le_trans hspec (st_mono x r p (by omega : w + 1 ≤ t')).2.2.2.2
  · rcases st_succ_cases x r w p with hs | ⟨c, e, -, -, hs, -⟩
    · rw [hs] at hspec; exact absurd hspec hlt
    · rcases advance_phase (r.H p w) (receive p e (stt x r p w)) with h | h | h
      · rw [hs, h, receive_phase] at hspec; exact absurd hspec hlt
      · rw [hs, advance_acks]; exact h.2.1
      · rw [receive_phase] at h; omega

/-- An output step: `p` moves from phase `1` to phase `2`, its `Σ` output is contained in its
read responses, and it outputs `answer` of its new state. -/
lemma out_spec {p : Fin 3} {y : Seen} {t : ℕ} (h : (alg.toAlg x).Out r p y t) :
    (stt x r p t).phase = 1 ∧ (stt x r p (t + 1)).phase = 2 ∧
      r.H p t ⊆ (stt x r p (t + 1)).resps ∧ y = answer (stt x r p (t + 1)) := by
  obtain ⟨c, e, hσ, he, ho⟩ := (Algorithm.out_iff r).1 h
  have hs := (Algorithm.cfg_succ_of_event r t p c e hσ he).1
  change stt x r p (t + 1) = advance (r.H p t) (receive p e (stt x r p t)) at hs
  change y ∈ (if (stt x r p t).phase = 1 ∧ (advance (r.H p t) (receive p e (stt x r p t))).phase = 2
    then [answer (advance (r.H p t) (receive p e (stt x r p t)))] else []) at ho
  rw [← hs] at ho
  split_ifs at ho with hc
  · rw [List.mem_singleton] at ho
    refine ⟨hc.1, hc.2, ?_, ho⟩
    rcases advance_phase (r.H p t) (receive p e (stt x r p t)) with h' | h' | h'
    · rw [← hs, hc.2, receive_phase, hc.1] at h'; simp at h'
    · rw [receive_phase, hc.1] at h'; simp at h'
    · rw [hs, advance_resps]; exact h'.2.1
  · simp at ho

/-! ### Safety -/

/-- Key inequality: if `p` outputs `alone` (not knowing the input of `q`) and both `p` and `q`
completed their writes (at `w_p`, `w_q`), then `p` completed its write before `q`. -/
lemma write_end_lt (hH : r.H ∈ SigmaFD (Fin 3) r.F) {p q : Fin 3} {d wp wq : ℕ}
    (hd : (alg.toAlg x).Out r p .alone d) (hq : (stt x r p (d + 1)).v q = none)
    (hwp : ∀ t', 1 ≤ (stt x r p t').phase ↔ wp < t')
    (hwq : r.H q wq ⊆ (stt x r q (wq + 1)).acks) : wp < wq := by
  obtain ⟨-, -, hres, -⟩ := out_spec x r hd
  obtain ⟨k, hkq, hkp⟩ := hH.2.1 q p wq d
  obtain ⟨a, -, hrd, hv⟩ := resps_spec x r (d + 1) p k (hres hkp)
  obtain ⟨b, hb, hph⟩ := rd_spec x r (a + 1) k p hrd
  have hwb : wp < b + 1 := (hwp _).1 hph
  obtain ⟨c, hc, hvc⟩ := acks_spec x r (wq + 1) q k (hwq hkq)
  have hac : a < c := by
    by_contra hca
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hvc
    have := (st_mono x r k (by omega : c + 1 ≤ a + 1)).1 q y hy
    rw [hv q hq] at this; simp at this
  omega

/-- Safety: processes `0` and `1` do not both output `alone`. -/
lemma not_both_alone (hH : r.H ∈ SigmaFD (Fin 3) r.F) {d₀ d₁ : ℕ}
    (h₀ : (alg.toAlg x).Out r 0 .alone d₀) (h₁ : (alg.toAlg x).Out r 1 .alone d₁) : False := by
  obtain ⟨-, hp₀, -, hy₀⟩ := out_spec x r h₀
  obtain ⟨-, hp₁, -, hy₁⟩ := out_spec x r h₁
  obtain ⟨w₀, hw₀, hk₀⟩ := exists_write_end x r 0 (t := d₀ + 1) (by omega)
  obtain ⟨w₁, hw₁, hk₁⟩ := exists_write_end x r 1 (t := d₁ + 1) (by omega)
  have hv₀ : (stt x r 0 (d₀ + 1)).v 1 = none :=
    answer_alone hy₀.symm (by rw [v_self]; rfl)
  have hv₁ : (stt x r 1 (d₁ + 1)).v 0 = none :=
    answer_alone' hy₁.symm (by rw [v_self]; rfl)
  have := write_end_lt x r hH h₀ hv₀ hw₀ hk₁
  have := write_end_lt x r hH h₁ hv₁ hw₁ hk₀
  omega

/-! ### Liveness -/

lemma advance_one {d : Set (Fin 3)} {s : LSt} (h0 : s.phase = 0) (hd : d ⊆ s.acks) :
    1 ≤ (advance d s).phase := by
  unfold advance; simp [h0, hd]

lemma advance_two {d : Set (Fin 3)} {s : LSt} (h1 : s.phase = 1) (hd : d ⊆ s.resps) :
    2 ≤ (advance d s).phase := by
  unfold advance; simp [h1, hd]

variable {x r}

/-- A correct process takes infinitely many time-out steps, each broadcasting its new state. -/
lemma exists_bcast (hA : (alg.toAlg x).Admissible r) {p : Fin 3} (hp : r.F.Correct p) (T : ℕ) :
    ∃ t ≥ T, stt x r p (t + 1) = advance (r.H p t) (stt x r p t) ∧
      ((alg.toAlg x).cfg r (t + 1)).msg t = some (p, stt x r p (t + 1)) := by
  obtain ⟨t, ht, hσ⟩ := hA.ticks p hp T
  obtain ⟨h₁, h₂, -⟩ := Algorithm.cfg_succ_of_event r t p .tick .tick hσ (Algorithm.event_tick _)
  refine ⟨t, ht, h₁, ?_⟩
  rw [h₂, stt, h₁]; rfl

/-- A message is eventually received by every correct process, which then broadcasts its new
state. -/
lemma exists_recv (hA : (alg.toAlg x).Admissible r) {k j : Fin 3} (hk : r.F.Correct k)
    {t a : ℕ} {m : LSt} (hm : ((alg.toAlg x).cfg r t).msg a = some (j, m)) :
    ∃ t₁, stt x r k (t₁ + 1) = advance (r.H k t₁) (recvMsg k j m (stt x r k t₁)) ∧
      ((alg.toAlg x).cfg r (t₁ + 1)).msg t₁ = some (k, stt x r k (t₁ + 1)) := by
  obtain ⟨t₁, hσ⟩ := hA.delivery k hk t a j m hm
  obtain ⟨m', hm', he⟩ := hA.recv_event hσ
  have : m' = m := by rw [(msg_eq x r hm').2, (msg_eq x r hm).2]
  subst this
  obtain ⟨h₁, h₂, -⟩ := Algorithm.cfg_succ_of_event r t₁ k _ _ hσ he
  refine ⟨t₁, h₁, ?_⟩
  rw [h₂, stt, h₁]; rfl

lemma exists_all {Q : Fin 3 → Prop} {S : Fin 3 → ℕ → Prop}
    (hmono : ∀ k t t', t ≤ t' → S k t → S k t') (h : ∀ k, Q k → ∃ t, S k t) :
    ∃ T, ∀ k, Q k → S k T := by
  classical
  choose f hf using h
  refine ⟨Finset.univ.sup fun k => if hk : Q k then f k hk else 0, fun k hk => ?_⟩
  refine hmono k _ _ ?_ (hf k hk)
  have := Finset.le_sup (f := fun k => if hk : Q k then f k hk else 0) (Finset.mem_univ k)
  simpa [hk] using this

/-- Every correct process eventually holds write acknowledgements from all correct processes. -/
lemma acks_eventually (hA : (alg.toAlg x).Admissible r) {p k : Fin 3} (hp : r.F.Correct p)
    (hk : r.F.Correct k) : ∃ T, k ∈ (stt x r p T).acks := by
  obtain ⟨t₀, -, -, hm₀⟩ := exists_bcast hA hp 0
  obtain ⟨t₁, hs₁, hm₁⟩ := exists_recv hA hk hm₀
  obtain ⟨t₂, hs₂, -⟩ := exists_recv hA hp hm₁
  refine ⟨t₂ + 1, ?_⟩
  rw [hs₂, advance_acks]
  refine Or.inr ⟨rfl, ?_⟩
  rw [hs₁, advance_v]
  simp [recvMsg, v_self]

/-- Once in its read phase, every correct process eventually holds read responses from all
correct processes. -/
lemma resps_eventually (hA : (alg.toAlg x).Admissible r) {p k : Fin 3} (hp : r.F.Correct p)
    (hk : r.F.Correct k) {T : ℕ} (hT : 1 ≤ (stt x r p T).phase) :
    ∃ T, k ∈ (stt x r p T).resps := by
  obtain ⟨t₀, ht₀, -, hm₀⟩ := exists_bcast hA hp T
  obtain ⟨t₁, hs₁, hm₁⟩ := exists_recv hA hk hm₀
  obtain ⟨t₂, hs₂, -⟩ := exists_recv hA hp hm₁
  refine ⟨t₂ + 1, ?_⟩
  rw [hs₂, advance_resps]
  refine Or.inr ⟨rfl, ?_⟩
  rw [hs₁, advance_rd]
  exact Or.inr ⟨rfl, le_trans hT (st_mono x r p (by omega)).2.2.2.2⟩

lemma phase_one_eventually (hA : (alg.toAlg x).Admissible r) (hH : r.H ∈ SigmaFD (Fin 3) r.F)
    {p : Fin 3} (hp : r.F.Correct p) : ∃ T, 1 ≤ (stt x r p T).phase := by
  obtain ⟨T₀, hT₀⟩ := hH.2.2 p hp
  obtain ⟨T₁, hT₁⟩ := exists_all (S := fun k T => k ∈ (stt x r p T).acks)
    (fun k t t' h hk => (st_mono x r p h).2.2.1 hk) (fun k hk => acks_eventually hA hp hk)
  obtain ⟨t, ht, hs, -⟩ := exists_bcast hA hp (max T₀ T₁)
  by_cases h0 : (stt x r p t).phase = 0
  · refine ⟨t + 1, ?_⟩
    rw [hs]
    refine advance_one h0 fun k hk => ?_
    exact (st_mono x r p (by omega)).2.2.1 (hT₁ k (hT₀ t (by omega) hk))
  · exact ⟨t, by omega⟩

lemma phase_two_eventually (hA : (alg.toAlg x).Admissible r) (hH : r.H ∈ SigmaFD (Fin 3) r.F)
    {p : Fin 3} (hp : r.F.Correct p) : ∃ T, 2 ≤ (stt x r p T).phase := by
  obtain ⟨T₀, hT₀⟩ := hH.2.2 p hp
  obtain ⟨T₂, hT₂⟩ := phase_one_eventually hA hH hp
  obtain ⟨T₁, hT₁⟩ := exists_all (S := fun k T => k ∈ (stt x r p T).resps)
    (fun k t t' h hk => (st_mono x r p h).2.2.2.1 hk) (fun k hk => resps_eventually hA hp hk hT₂)
  obtain ⟨t, ht, hs, -⟩ := exists_bcast hA hp (max (max T₀ T₁) T₂)
  have h1 : 1 ≤ (stt x r p t).phase := le_trans hT₂ (st_mono x r p (by omega)).2.2.2.2
  by_cases h0 : (stt x r p t).phase = 1
  · refine ⟨t + 1, ?_⟩
    rw [hs]
    refine advance_two h0 fun k hk => ?_
    exact (st_mono x r p (by omega)).2.2.2.1 (hT₁ k (hT₀ t (by omega) hk))
  · exact ⟨t, by omega⟩

/-- A process that reaches phase `2` has produced an output. -/
lemma decided_of_phase_two {p : Fin 3} {t : ℕ} (ht : 2 ≤ (stt x r p t).phase) :
    alg.Decided x r p := by
  classical
  have hex : ∃ t, 2 ≤ (stt x r p t).phase := ⟨t, ht⟩
  have h0 : Nat.find hex ≠ 0 := by
    intro h; have := Nat.find_spec hex; rw [h] at this; simp [st_zero, alg] at this
  obtain ⟨w, hw⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have hlt : ¬ 2 ≤ (stt x r p w).phase := Nat.find_min hex (by omega)
  have hspec : 2 ≤ (stt x r p (w + 1)).phase := by
    have := Nat.find_spec hex; rw [hw] at this; exact this
  rcases st_succ_cases x r w p with hs | ⟨c, e, hσ, he, hs, -⟩
  · rw [hs] at hspec; exact absurd hspec hlt
  · rcases advance_phase (r.H p w) (receive p e (stt x r p w)) with h | h | h
    · rw [hs, h, receive_phase] at hspec; exact absurd hspec hlt
    · rw [hs, h.2.2] at hspec; omega
    · rw [receive_phase] at h
      refine ⟨w, answer (stt x r p (w + 1)), (Algorithm.out_iff r).2 ⟨c, e, hσ, he, ?_⟩⟩
      change _ ∈ (if (stt x r p w).phase = 1 ∧
        (advance (r.H p w) (receive p e (stt x r p w))).phase = 2
        then [answer (advance (r.H p w) (receive p e (stt x r p w)))] else [])
      simp only [h.1, h.2.2, and_self, ↓reduceIte, hs, List.mem_singleton]

/-! ### Main result -/

lemma output_ok (p : Fin 3) :
    Seen.Ok x ((alg.output x r p).getD (.pair (x 0) (x 1))) := by
  rcases h : alg.output x r p with _ | y
  · simp [Seen.Ok]
  · obtain ⟨t, ht⟩ := AlgAMP.output_spec h
    obtain ⟨-, -, -, rfl⟩ := out_spec x r ht
    exact answer_ok x _ (v_correct x r _ p)

/-- `alg` solves `Tseen` in `AMP_{3,2}[fd : Σ]`. -/
theorem alg_solves : alg.SolvesAMP (SigmaFD (Fin 3)) Tseen := by
  intro x _ r _ hH hA
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨T, hT⟩ := phase_two_eventually hA hH hp
    exact decided_of_phase_two hT
  · refine ⟨fun i => (alg.output x r i).getD (.pair (x 0) (x 1)),
      ⟨output_ok 0, output_ok 1, ?_⟩, fun i y h => by simp [h]⟩
    rcases h₀ : alg.output x r 0 with _ | y₀
    · left; simp [h₀]
    · rcases h₁ : alg.output x r 1 with _ | y₁
      · right; simp [h₁]
      · by_cases hy₀ : y₀ = .alone
        · by_cases hy₁ : y₁ = .alone
          · subst hy₀ hy₁
            obtain ⟨d₀, hd₀⟩ := AlgAMP.output_spec h₀
            obtain ⟨d₁, hd₁⟩ := AlgAMP.output_spec h₁
            exact (not_both_alone x r hH hd₀ hd₁).elim
          · right; simpa [h₁] using hy₁
        · left; simpa [h₀] using hy₀

end SigmaSeen

open Cslib.FailureDetectors in
/-- Counterexample to Lemma 6 / Theorem 4 of Raynal–Stainer (PODC 2013), positive half: the task
`Tseen` is solvable in `AMP_{3,2}[fd : Σ]` (asynchronous message passing, up to two crashes, quorum failure
detector `Σ`). -/
theorem tseen_solvable_amp_sigma : SolvableAMP (SigmaFD (Fin 3)) Tseen :=
  ⟨_, _, SigmaSeen.alg, SigmaSeen.alg_solves⟩

end Podc.MessageAdversariesVsFD
