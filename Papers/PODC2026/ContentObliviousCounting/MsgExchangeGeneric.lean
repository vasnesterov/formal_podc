import Cslib.Computability.Distributed.ContentOblivious.Hom
import Mathlib

/-!
# Message exchange on oriented rings (Algorithms 5–6), from abstract round procedures

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026 (arXiv 2603.28260), Algorithm 5 (`MsgExchange`) and Algorithm 6 (`MsgRelay`),
Theorem 22.

Every node runs the loop
```
while ComputeOR(active ∧ I still have bits) do
  rcvdccw.append(CWBitSending(msgcw[t]));  rcvdcw.append(CCWBitSending(msgccw[t]));  t++
```
(relays: `ComputeOR(false)`, `CWBitRelay`, `CCWBitRelay`). We model it as a staged program
(`Cslib.ContentOblivious.Proc.staged`) whose stage procedure is the sum of the three round
procedures, and derive its correctness from the generic composition theorem
(`Cslib.ContentOblivious.Schedule.final`). In this file the three procedures are abstract: they are
assumed to be composable, to return the right values and to send at most `3n`, `6n`, `6n` pulses
(this is what Theorems 17 and 21 provide; see `MsgExchange.lean` for the instantiation).

Inputs of node `v`: `(isLeader, isActive, msgcw, msgccw)`. Relays (`isActive = false`) have no
messages.
-/

namespace Podc.ContentOblivious.MsgExchange

open Cslib.ContentOblivious Finset

/-- Node input: leader flag, active flag, message to the clockwise and to the counter-clockwise
neighbour. -/
abbrev Input := Bool × Bool × List Bool × List Bool

/-- Inputs of the three round procedures. -/
abbrev J := (Bool × Bool) ⊕ ((Bool × Bool × Option Bool) ⊕ (Bool × Bool × Option Bool))

/-- Results of the three round procedures. -/
abbrev R := Bool ⊕ (Option Bool ⊕ Option Bool)

/-- Local variables of Algorithm 5 (`phase` = `t`). -/
structure St where
  leader : Bool
  active : Bool
  mcw : List Bool
  mccw : List Bool
  t : ℕ
  /-- `rcvdcw`: bits received from the clockwise neighbour (`none` = ⊥). -/
  rcw : List (Option Bool)
  /-- `rcvdccw`: bits received from the counter-clockwise neighbour. -/
  rccw : List (Option Bool)

/-- Does the node still have a bit to send in phase `t` (line 6/13: `active`)? -/
def hasBit (m1 m2 : List Bool) (t : ℕ) : Bool := decide (t < m1.length) || decide (t < m2.length)

/-- The driver of Algorithms 5–6. -/
def driver : Driver Input J R St where
  start i := (⟨i.1, i.2.1, i.2.2.1, i.2.2.2, 0, [], []⟩,
    some (.inl (i.1, i.2.1 && hasBit i.2.2.1 i.2.2.2 0)))
  next d
    | .inl true => (d, some (.inr (.inl (d.leader, d.active, d.mcw[d.t]?))))
    | .inl false => (d, none)
    | .inr (.inl b) => ({ d with rccw := d.rccw ++ [b] },
        some (.inr (.inr (d.leader, d.active, d.mccw[d.t]?))))
    | .inr (.inr b) => ({ d with rcw := d.rcw ++ [b], t := d.t + 1 },
        some (.inl (d.leader, d.active && hasBit d.mcw d.mccw (d.t + 1))))

variable {n : ℕ} [NeZero n]

section abstract

variable (OR : Proc (Bool × Bool) Bool) (CW CCW : Proc (Bool × Bool × Option Bool) (Option Bool))

/-- The combined round procedure. -/
abbrev roundProc : Proc J R := OR.sum (CW.sum CCW)

/-- The message-exchange program (Algorithm 5 for active nodes, Algorithm 6 for relays). -/
abbrev prog : Proc Input St := (roundProc OR CW CCW).staged driver

variable {OR CW CCW}
variable (lead act : ZMod n → Bool) (mcw mccw : ZMod n → List Bool) (nxt prv : ZMod n → ZMod n)

/-- Number of loop iterations: the length of the longest message of an active node. -/
def maxLen : ℕ := univ.sup fun v => if act v then max (mcw v).length (mccw v).length else 0

/-- Bit received in phase `t` from the counter-clockwise active neighbour (by `CWBitSending`). -/
def rvcw (t : ℕ) (v : ZMod n) : Option Bool := if act v then (mcw (prv v))[t]? else none

/-- Bit received in phase `t` from the clockwise active neighbour (by `CCWBitSending`). -/
def rvccw (t : ℕ) (v : ZMod n) : Option Bool := if act v then (mccw (nxt v))[t]? else none

/-- Scheduled local state before stage `k` (stage `3t`: ComputeOR of phase `t`, `3t+1`: CW bit,
`3t+2`: CCW bit). -/
def dSched (k : ℕ) (v : ZMod n) : St :=
  ⟨lead v, act v, mcw v, mccw v, k / 3, (List.range (k / 3)).map fun t => rvccw act mccw nxt t v,
    (List.range (if k % 3 = 2 then k / 3 + 1 else k / 3)).map fun t => rvcw act mcw prv t v⟩

/-- Scheduled stage inputs. -/
def jSched (k : ℕ) (v : ZMod n) : J :=
  if k % 3 = 0 then .inl (lead v, act v && hasBit (mcw v) (mccw v) (k / 3))
  else if k % 3 = 1 then .inr (.inl (lead v, act v, (mcw v)[k / 3]?))
  else .inr (.inr (lead v, act v, (mccw v)[k / 3]?))

/-- Scheduled stage results. -/
def rSched (k : ℕ) (v : ZMod n) : R :=
  if k % 3 = 0 then .inl (decide (k / 3 < maxLen act mcw mccw))
  else if k % 3 = 1 then .inr (.inl (rvcw act mcw prv (k / 3) v))
  else .inr (.inr (rvccw act mccw nxt (k / 3) v))

/-- Hypotheses on the round procedures (Theorems 17 and 21). -/
structure RoundSpec (OR : Proc (Bool × Bool) Bool) (CW CCW : Proc (Bool × Bool × Option Bool)
    (Option Bool)) (lead act : ZMod n → Bool) (nxt prv : ZMod n → ZMod n) : Prop where
  or_init : ∀ a, OR.result (OR.init a).1 = none
  cw_init : ∀ a, CW.result (CW.init a).1 = none
  ccw_init : ∀ a, CCW.result (CCW.init a).1 = none
  or_comp : ∀ b : ZMod n → Bool, OR.Composable (oriented n) (fun v => (lead v, b v))
  or_ret : ∀ b : ZMod n → Bool,
    OR.Returns (oriented n) (fun v => (lead v, b v)) (fun _ => decide (∃ v, b v = true))
  or_bound : ∀ b : ZMod n → Bool, ∀ c, OR.Reach (oriented n) (fun v => (lead v, b v)) c →
    totalSent c ≤ 3 * n
  cw_comp : ∀ bit : ZMod n → Option Bool,
    CW.Composable (oriented n) (fun v => (lead v, act v, bit v))
  cw_ret : ∀ bit : ZMod n → Option Bool, CW.Returns (oriented n) (fun v => (lead v, act v, bit v))
    (fun v => if act v then bit (prv v) else none)
  cw_bound : ∀ bit : ZMod n → Option Bool, ∀ c,
    CW.Reach (oriented n) (fun v => (lead v, act v, bit v)) c → totalSent c ≤ 6 * n
  ccw_comp : ∀ bit : ZMod n → Option Bool,
    CCW.Composable (oriented n) (fun v => (lead v, act v, bit v))
  ccw_ret : ∀ bit : ZMod n → Option Bool,
    CCW.Returns (oriented n) (fun v => (lead v, act v, bit v))
    (fun v => if act v then bit (nxt v) else none)
  ccw_bound : ∀ bit : ZMod n → Option Bool, ∀ c,
    CCW.Reach (oriented n) (fun v => (lead v, act v, bit v)) c → totalSent c ≤ 6 * n

variable {lead act mcw mccw nxt prv}

/-- The input assignment of the message-exchange program. -/
def inputs (lead act : ZMod n → Bool) (mcw mccw : ZMod n → List Bool) (v : ZMod n) : Input :=
  (lead v, act v, mcw v, mccw v)

lemma exists_hasBit_iff (t : ℕ) :
    (∃ v, (act v && hasBit (mcw v) (mccw v) t) = true) ↔ t < maxLen act mcw mccw := by
  unfold maxLen
  rw [Finset.lt_sup_iff]
  simp only [mem_univ, true_and, Bool.and_eq_true, hasBit, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, ?_⟩
    rw [ite_eq_left hv]; rcases h with h | h <;> omega
  · rintro ⟨v, hv⟩
    by_cases ha : act v = true
    · rw [ite_eq_left ha] at hv; exact ⟨v, ha, by omega⟩
    · rw [ite_eq_right ha] at hv; omega

lemma schedule (hR : RoundSpec OR CW CCW lead act nxt prv) :
    Schedule (roundProc OR CW CCW) driver (oriented n) (inputs lead act mcw mccw)
      (3 * maxLen act mcw mccw + 1) (dSched lead act mcw mccw nxt prv) (jSched lead act mcw mccw)
      (rSched act mcw mccw nxt prv) := by
  set L := maxLen act mcw mccw with hL
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro (a | a | a)
    · show (OR.result (OR.init a).1).map Sum.inl = none
      rw [hR.or_init a]; rfl
    · show ((CW.result (CW.init a).1).map Sum.inl).map Sum.inr = none
      rw [hR.cw_init a]; rfl
    · show ((CCW.result (CCW.init a).1).map Sum.inr).map Sum.inr = none
      rw [hR.ccw_init a]; rfl
  · intro v
    simp [driver, dSched, jSched, inputs]
  · intro k hk v
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · by_cases ht : k / 3 < L
      · have e1 : (k + 1) / 3 = k / 3 := by omega
        have e2 : (k + 1) % 3 = 1 := by omega
        have hk1 : k + 1 < 3 * L + 1 := by omega
        simp [rSched, dSched, jSched, driver, h0, e1, e2, ht, hk1, ← hL]
      · have e1 : (k + 1) / 3 = k / 3 := by omega
        have e2 : (k + 1) % 3 = 1 := by omega
        have hk1 : ¬ k + 1 < 3 * L + 1 := by omega
        simp [rSched, dSched, driver, h0, e1, e2, ht, hk1, ← hL]
    · have e1 : (k + 1) / 3 = k / 3 := by omega
      have e2 : (k + 1) % 3 = 2 := by omega
      have hk1 : k + 1 < 3 * L + 1 := by omega
      simp [rSched, dSched, jSched, driver, h1, e1, e2, hk1, List.range_succ]
    · have e1 : (k + 1) / 3 = k / 3 + 1 := by omega
      have e2 : (k + 1) % 3 = 0 := by omega
      have hk1 : k + 1 < 3 * L + 1 := by omega
      simp [rSched, dSched, jSched, driver, h2, e1, e2, hk1, List.range_succ]
  · intro k _
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · have e : jSched lead act mcw mccw k = fun v => (Proc.Hom.inl OR (CW.sum CCW)).g
          (lead v, act v && hasBit (mcw v) (mccw v) (k / 3)) := by
        funext v; simp [jSched, h0, Proc.Hom.inl]
      rw [e]; exact (Proc.Hom.inl _ _).composable (hR.or_comp _)
    · have e : jSched lead act mcw mccw k = fun v => (Proc.Hom.inr OR (CW.sum CCW)).g
          ((Proc.Hom.inl CW CCW).g (lead v, act v, (mcw v)[k / 3]?)) := by
        funext v; simp [jSched, h1, Proc.Hom.inl, Proc.Hom.inr]
      rw [e]
      exact (Proc.Hom.inr _ _).composable ((Proc.Hom.inl _ _).composable (hR.cw_comp _))
    · have e : jSched lead act mcw mccw k = fun v => (Proc.Hom.inr OR (CW.sum CCW)).g
          ((Proc.Hom.inr CW CCW).g (lead v, act v, (mccw v)[k / 3]?)) := by
        funext v; simp [jSched, h2, Proc.Hom.inr]
      rw [e]
      exact (Proc.Hom.inr _ _).composable ((Proc.Hom.inr _ _).composable (hR.ccw_comp _))
  · intro k _
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · have e : jSched lead act mcw mccw k = fun v => (Proc.Hom.inl OR (CW.sum CCW)).g
          (lead v, act v && hasBit (mcw v) (mccw v) (k / 3)) := by
        funext v; simp [jSched, h0, Proc.Hom.inl]
      have er : rSched act mcw mccw nxt prv k = fun v => (Proc.Hom.inl OR (CW.sum CCW)).h
          (decide (∃ w, (act w && hasBit (mcw w) (mccw w) (k / 3)) = true)) := by
        funext v; simp only [rSched, h0, ↓reduceIte, exists_hasBit_iff, ← hL]; rfl
      rw [e, er]; exact (Proc.Hom.inl _ _).returns (hR.or_ret _)
    · have e : jSched lead act mcw mccw k = fun v => (Proc.Hom.inr OR (CW.sum CCW)).g
          ((Proc.Hom.inl CW CCW).g (lead v, act v, (mcw v)[k / 3]?)) := by
        funext v; simp [jSched, h1, Proc.Hom.inl, Proc.Hom.inr]
      have er : rSched act mcw mccw nxt prv k = fun v => (Proc.Hom.inr OR (CW.sum CCW)).h
          ((Proc.Hom.inl CW CCW).h (if act v then (mcw (prv v))[k / 3]? else none)) := by
        funext v; simp [rSched, h1, rvcw, Proc.Hom.inl, Proc.Hom.inr]
      rw [e, er]
      exact (Proc.Hom.inr _ _).returns ((Proc.Hom.inl _ _).returns (hR.cw_ret _))
    · have e : jSched lead act mcw mccw k = fun v => (Proc.Hom.inr OR (CW.sum CCW)).g
          ((Proc.Hom.inr CW CCW).g (lead v, act v, (mccw v)[k / 3]?)) := by
        funext v; simp [jSched, h2, Proc.Hom.inr]
      have er : rSched act mcw mccw nxt prv k = fun v => (Proc.Hom.inr OR (CW.sum CCW)).h
          ((Proc.Hom.inr CW CCW).h (if act v then (mccw (nxt v))[k / 3]? else none)) := by
        funext v; simp [rSched, h2, rvccw, Proc.Hom.inr]
      rw [e, er]
      exact (Proc.Hom.inr _ _).returns ((Proc.Hom.inr _ _).returns (hR.ccw_ret _))

lemma filterMap_range_getElem? (l : List Bool) (L : ℕ) :
    ((List.range L).map fun t => l[t]?).filterMap id = l.take L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.map_append, List.filterMap_append, ih, List.take_add_one]
    cases h : l[L]? <;> simp [h]

omit [NeZero n] in
lemma sum_bound (L : ℕ) :
    ∑ k ∈ range (3 * L + 1), (if k % 3 = 0 then 3 * n else 6 * n) = 15 * n * L + 3 * n := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [show 3 * (L + 1) + 1 = 3 * L + 1 + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ, ih]
    have h1 : (3 * L + 1) % 3 = 1 := by omega
    have h2 : (3 * L + 1 + 1) % 3 = 2 := by omega
    have h3 : (3 * L + 1 + 1 + 1) % 3 = 0 := by omega
    simp only [h1, h2, h3]; simp; ring

lemma stage_bound (hR : RoundSpec OR CW CCW lead act nxt prv) :
    ∀ k < 3 * maxLen act mcw mccw + 1, ∀ c, (roundProc OR CW CCW).Reach (oriented n)
      (jSched lead act mcw mccw k) c → totalSent c ≤ if k % 3 = 0 then 3 * n else 6 * n := by
  intro k _ c hc
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · have e : jSched lead act mcw mccw k = fun v => (Proc.Hom.inl OR (CW.sum CCW)).g
        (lead v, act v && hasBit (mcw v) (mccw v) (k / 3)) := by
      funext v; simp [jSched, h0, Proc.Hom.inl]
    rw [e] at hc; rw [ite_eq_left h0]
    exact (Proc.Hom.inl _ _).totalSent_le (hR.or_bound _) c hc
  · have e : jSched lead act mcw mccw k = fun v => (Proc.Hom.inr OR (CW.sum CCW)).g
        ((Proc.Hom.inl CW CCW).g (lead v, act v, (mcw v)[k / 3]?)) := by
      funext v; simp [jSched, h1, Proc.Hom.inl, Proc.Hom.inr]
    rw [e] at hc; rw [ite_eq_right (by omega)]
    exact (Proc.Hom.inr _ _).totalSent_le ((Proc.Hom.inl _ _).totalSent_le (hR.cw_bound _)) c hc
  · have e : jSched lead act mcw mccw k = fun v => (Proc.Hom.inr OR (CW.sum CCW)).g
        ((Proc.Hom.inr CW CCW).g (lead v, act v, (mccw v)[k / 3]?)) := by
      funext v; simp [jSched, h2, Proc.Hom.inr]
    rw [e] at hc; rw [ite_eq_right (by omega)]
    exact (Proc.Hom.inr _ _).totalSent_le ((Proc.Hom.inr _ _).totalSent_le (hR.ccw_bound _)) c hc

/-- **Theorem 22 (abstract rounds).** If the round procedures satisfy Theorems 17 and 21, then in
every execution of Algorithms 5–6 on an oriented ring: every final configuration is quiescent, every
node has left the loop, and every active node has received exactly the message sent to it by its
clockwise (`rcvdcw`) and counter-clockwise (`rcvdccw`) active neighbours; at most
`15·n·L + 3·n` pulses are sent (`L` = longest message); and the whole exchange is composable. -/
theorem theorem_22_of_rounds (hR : RoundSpec OR CW CCW lead act nxt prv)
    (hnxt : ∀ v, act (nxt v) = true) (hprv : ∀ v, act (prv v) = true) :
    (∀ c, (prog OR CW CCW).Reach (oriented n) (inputs lead act mcw mccw) c →
      (prog OR CW CCW).Final (oriented n) c →
      (prog OR CW CCW).Quiescent (oriented n) c ∧ ∀ v, (c.st v).2 = none ∧
        (act v = true → (c.st v).1.rcw.filterMap id = mccw (nxt v) ∧
          (c.st v).1.rccw.filterMap id = mcw (prv v))) ∧
    (∀ c, (prog OR CW CCW).Reach (oriented n) (inputs lead act mcw mccw) c →
      totalSent c ≤ 15 * n * maxLen act mcw mccw + 3 * n) ∧
    (prog OR CW CCW).Composable (oriented n) (inputs lead act mcw mccw) := by
  have hS := schedule (mcw := mcw) (mccw := mccw) hR
  set L := maxLen act mcw mccw with hL
  have hlen : ∀ w, act w = true → (mcw w).length ≤ L ∧ (mccw w).length ≤ L := by
    intro w hw
    have := Finset.le_sup (f := fun v => if act v then max (mcw v).length (mccw v).length else 0)
      (mem_univ w)
    simp only [hw, ite_true] at this
    exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩
  refine ⟨fun c hc hfin => ?_, fun c hc => ?_, hS.composable (stage_bound hR)⟩
  · obtain ⟨hq, hst⟩ := hS.final hc hfin
    refine ⟨hq, fun v => ⟨by rw [hst v], fun hv => ?_⟩⟩
    rw [hst v]
    have e1 : (3 * L + 1) / 3 = L := by omega
    have e2 : (3 * L + 1) % 3 = 1 := by omega
    simp only [dSched, e1, e2, rvccw, rvcw, hv, ite_true, show (1 : ℕ) ≠ 2 by omega, ite_false]
    rw [filterMap_range_getElem?, filterMap_range_getElem?,
      List.take_of_length_le (hlen _ (hnxt v)).2, List.take_of_length_le (hlen _ (hprv v)).1]
    exact ⟨rfl, rfl⟩
  · have := hS.totalSent_le (stage_bound hR) hc
    rwa [sum_bound] at this

/-- The local state returned by the message exchange (used when it is nested in a bigger staged
program, e.g. the round-by-round simulation of Theorem 14). -/
theorem returns_dSched (hR : RoundSpec OR CW CCW lead act nxt prv) :
    (prog OR CW CCW).Returns (oriented n) (inputs lead act mcw mccw)
      (dSched lead act mcw mccw nxt prv (3 * maxLen act mcw mccw + 1)) :=
  (schedule hR).returns

/-- What an active node has received at the end of the exchange. -/
lemma dSched_final (hnxt : ∀ v, act (nxt v) = true) (hprv : ∀ v, act (prv v) = true) {v : ZMod n}
    (hv : act v = true) :
    (dSched lead act mcw mccw nxt prv (3 * maxLen act mcw mccw + 1) v).rcw.filterMap id =
      mccw (nxt v) ∧
    (dSched lead act mcw mccw nxt prv (3 * maxLen act mcw mccw + 1) v).rccw.filterMap id =
      mcw (prv v) := by
  set L := maxLen act mcw mccw with hL
  have hlen : ∀ w, act w = true → (mcw w).length ≤ L ∧ (mccw w).length ≤ L := by
    intro w hw
    have := Finset.le_sup (f := fun v => if act v then max (mcw v).length (mccw v).length else 0)
      (mem_univ w)
    simp only [hw, ite_true] at this
    exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩
  have e1 : (3 * L + 1) / 3 = L := by omega
  have e2 : (3 * L + 1) % 3 = 1 := by omega
  simp only [dSched, e1, e2, rvccw, rvcw, hv, ite_true, show (1 : ℕ) ≠ 2 by omega, ite_false]
  rw [filterMap_range_getElem?, filterMap_range_getElem?,
    List.take_of_length_le (hlen _ (hnxt v)).2, List.take_of_length_le (hlen _ (hprv v)).1]
  exact ⟨rfl, rfl⟩

omit [NeZero n] in
/-- The state components that the exchange does not touch. -/
lemma dSched_fields (k : ℕ) (v : ZMod n) :
    (dSched lead act mcw mccw nxt prv k v).leader = lead v ∧
    (dSched lead act mcw mccw nxt prv k v).active = act v := ⟨rfl, rfl⟩

end abstract

end Podc.ContentOblivious.MsgExchange
