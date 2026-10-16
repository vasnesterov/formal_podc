import Papers.PODC2026.ContentObliviousCounting.MsgExchangeGeneric

/-!
# Round-by-round simulation of synchronous ring algorithms (Theorem 14), from abstract rounds

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026 (arXiv 2603.28260), Theorem 14.

A synchronous algorithm `A` on the virtual ring of the active processes sends, in every round, a
bit string to each of its two neighbours and updates its state from the two strings it receives.
The content-oblivious simulation runs one message exchange (Algorithms 5–6) per simulated round:
a staged program whose stages are themselves staged programs (nested composition). We show that
after `T` rounds every active process holds exactly the state of the synchronous execution, that
the execution is quiescently terminating and composable, and that simulating a round in which all
messages have at most `b` bits costs at most `15·n·b + 3·n` pulses, i.e. `O(b)` pulses per process.

The round procedures are abstract here (hypothesis `RoundSpec`); see `Simulation.lean`.
-/

namespace Podc.ContentOblivious.Simulation

open Podc.ContentOblivious MsgExchange Finset

/-- A synchronous message-passing algorithm on a ring. `msg s = (to clockwise neighbour,
to counter-clockwise neighbour)`; `step s a b` is the new state after receiving `a` from the
counter-clockwise neighbour and `b` from the clockwise neighbour. -/
structure SyncAlg (S : Type) where
  msg : S → List Bool × List Bool
  step : S → List Bool → List Bool → S

variable {S : Type}

/-- The synchronous execution on the virtual ring given by `nxt` (clockwise active neighbour) and
`prv` (counter-clockwise active neighbour). -/
def SyncAlg.run {V : Type*} (A : SyncAlg S) (nxt prv : V → V) (s0 : V → S) : ℕ → V → S
  | 0 => s0
  | t + 1 => fun v => A.step (A.run nxt prv s0 t v) (A.msg (A.run nxt prv s0 t (prv v))).1
      (A.msg (A.run nxt prv s0 t (nxt v))).2

/-- Local state of the simulation driver. -/
structure SimSt (S : Type) where
  leader : Bool
  active : Bool
  s : S
  t : ℕ
  T : ℕ

/-- Messages handed to the message exchange (relays have none). -/
def outMsgs (A : SyncAlg S) (a : Bool) (s : S) : List Bool × List Bool :=
  if a then A.msg s else ([], [])

/-- The simulation driver: node input = (leader flag, active flag, initial state, number of
rounds). -/
def driver (A : SyncAlg S) : Driver (Bool × Bool × S × ℕ) Input St (SimSt S) where
  start i := (⟨i.1, i.2.1, i.2.2.1, 0, i.2.2.2⟩,
    if 0 < i.2.2.2 then some (i.1, i.2.1, (outMsgs A i.2.1 i.2.2.1).1, (outMsgs A i.2.1 i.2.2.1).2)
    else none)
  next d st :=
    let s' := if d.active then A.step d.s (st.rccw.filterMap id) (st.rcw.filterMap id) else d.s
    (⟨d.leader, d.active, s', d.t + 1, d.T⟩,
      if d.t + 1 < d.T then some (d.leader, d.active, (outMsgs A d.active s').1,
        (outMsgs A d.active s').2) else none)

variable {n : ℕ} [NeZero n]
variable {OR : Proc (Bool × Bool) Bool} {CW CCW : Proc (Bool × Bool × Option Bool) (Option Bool)}

/-- The simulation program. -/
abbrev simProg (OR : Proc (Bool × Bool) Bool) (CW CCW : Proc (Bool × Bool × Option Bool)
    (Option Bool)) (A : SyncAlg S) : Proc (Bool × Bool × S × ℕ) (SimSt S) :=
  (prog OR CW CCW).staged (driver A)

variable [Encodable S] [Inhabited S]
variable (A : SyncAlg S) (lead act : ZMod n → Bool) (nxt prv : ZMod n → ZMod n) (s0 : ZMod n → S)
  (T : ℕ)

/-- State of the simulation at round `k` (relays keep their initial state). -/
def stateAt (k : ℕ) (v : ZMod n) : S := if act v then A.run nxt prv s0 k v else s0 v

/-- Messages to the clockwise / counter-clockwise neighbours in round `k`. -/
def mcwAt (k : ℕ) (v : ZMod n) : List Bool := (outMsgs A (act v) (stateAt A act nxt prv s0 k v)).1
def mccwAt (k : ℕ) (v : ZMod n) : List Bool := (outMsgs A (act v) (stateAt A act nxt prv s0 k v)).2

/-- Length of the longest message of round `k`. -/
abbrev lenAt (k : ℕ) : ℕ := maxLen act (mcwAt A act nxt prv s0 k) (mccwAt A act nxt prv s0 k)

variable {A lead act nxt prv s0 T}

lemma schedule (hR : RoundSpec OR CW CCW lead act nxt prv) (hnxt : ∀ v, act (nxt v) = true)
    (hprv : ∀ v, act (prv v) = true) :
    Schedule (prog OR CW CCW) (driver A) (oriented n) (fun v => (lead v, act v, s0 v, T)) T
      (fun k v => ⟨lead v, act v, stateAt A act nxt prv s0 k v, k, T⟩)
      (fun k v => (lead v, act v, mcwAt A act nxt prv s0 k v, mccwAt A act nxt prv s0 k v))
      (fun k v => dSched lead act (mcwAt A act nxt prv s0 k) (mccwAt A act nxt prv s0 k) nxt prv
        (3 * lenAt A act nxt prv s0 k + 1) v) := by
  refine ⟨fun a => rfl, fun v => ?_, fun k hk v => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [driver]
    congr 1
    · simp [stateAt, SyncAlg.run]
    · split_ifs with h
      · simp [mcwAt, mccwAt, stateAt, SyncAlg.run]
      · rfl
  · have hfin := fun hv => dSched_final (lead := lead) (mcw := mcwAt A act nxt prv s0 k)
      (mccw := mccwAt A act nxt prv s0 k) hnxt hprv (v := v) hv
    have hst : (if act v = true then A.step (stateAt A act nxt prv s0 k v)
        ((dSched lead act (mcwAt A act nxt prv s0 k) (mccwAt A act nxt prv s0 k) nxt prv
          (3 * lenAt A act nxt prv s0 k + 1) v).rccw.filterMap id)
        ((dSched lead act (mcwAt A act nxt prv s0 k) (mccwAt A act nxt prv s0 k) nxt prv
          (3 * lenAt A act nxt prv s0 k + 1) v).rcw.filterMap id)
        else stateAt A act nxt prv s0 k v) = stateAt A act nxt prv s0 (k + 1) v := by
      by_cases hv : act v = true
      · rw [ite_eq_left hv, (hfin hv).2, (hfin hv).1]
        simp [stateAt, hv, SyncAlg.run, mcwAt, mccwAt, outMsgs, hnxt, hprv]
      · simp [stateAt, hv]
    simp only [driver]
    rw [hst]
    rfl
  · exact (theorem_22_of_rounds hR hnxt hprv).2.2
  · exact returns_dSched hR

/-- **Theorem 14 (abstract rounds).** The content-oblivious simulation of `T` rounds of a
synchronous ring algorithm `A` on the virtual ring of the active processes is correct (every
active process ends in the state of the synchronous execution), quiescently terminating and
composable; simulating round `k` costs at most `15·n·b_k + 3·n` pulses, where `b_k` is the length
of the longest message of round `k` (so `O(b_k)` pulses per process). -/
theorem theorem_14_of_rounds (hR : RoundSpec OR CW CCW lead act nxt prv)
    (hnxt : ∀ v, act (nxt v) = true) (hprv : ∀ v, act (prv v) = true) :
    (∀ c, (simProg OR CW CCW A).Reach (oriented n) (fun v => (lead v, act v, s0 v, T)) c →
      (simProg OR CW CCW A).Final (oriented n) c →
      (simProg OR CW CCW A).Quiescent (oriented n) c ∧
        ∀ v, act v = true → (c.st v).1.s = A.run nxt prv s0 T v) ∧
    (∀ c, (simProg OR CW CCW A).Reach (oriented n) (fun v => (lead v, act v, s0 v, T)) c →
      totalSent c ≤ ∑ k ∈ range T, (15 * n * lenAt A act nxt prv s0 k + 3 * n)) ∧
    (simProg OR CW CCW A).Composable (oriented n) (fun v => (lead v, act v, s0 v, T)) := by
  have hS := schedule (A := A) (s0 := s0) (T := T) hR hnxt hprv
  have hB : ∀ k < T, ∀ c, (prog OR CW CCW).Reach (oriented n)
      (fun v => (lead v, act v, mcwAt A act nxt prv s0 k v, mccwAt A act nxt prv s0 k v)) c →
      totalSent c ≤ 15 * n * lenAt A act nxt prv s0 k + 3 * n :=
    fun k _ c hc => (theorem_22_of_rounds hR hnxt hprv).2.1 c hc
  refine ⟨fun c hc hfin => ?_, fun c hc => hS.totalSent_le hB hc, hS.composable hB⟩
  obtain ⟨hq, hst⟩ := hS.final hc hfin
  refine ⟨hq, fun v hv => ?_⟩
  rw [hst v]
  simp [stateAt, hv]

/-- The exact local state returned by the simulation (for nesting it in bigger staged programs). -/
theorem returns_sim (hR : RoundSpec OR CW CCW lead act nxt prv)
    (hnxt : ∀ v, act (nxt v) = true) (hprv : ∀ v, act (prv v) = true) :
    (simProg OR CW CCW A).Returns (oriented n) (fun v => (lead v, act v, s0 v, T))
      (fun v => ⟨lead v, act v, stateAt A act nxt prv s0 T v, T, T⟩) :=
  (schedule (A := A) (s0 := s0) (T := T) hR hnxt hprv).returns

end Podc.ContentOblivious.Simulation
