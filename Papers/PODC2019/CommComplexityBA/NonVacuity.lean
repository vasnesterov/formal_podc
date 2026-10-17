import Papers.PODC2019.CommComplexityBA.Basic

/-!
# Non-vacuity of `SolvesBB`

A sanity check of the model: the hypothesis `SolvesBB` of the lower bound is satisfiable by a
simple deterministic protocol. With `n = 3` nodes, sender `0` and `f = 1` omission fault, the
"send, then relay" protocol solves Byzantine broadcast with probability `1`:

* round 0: the sender sends its input to everybody;
* round 1: every node relays what it received from the sender in round 0;
* after two rounds a node decides its own input if it has one, else the value received from the
  sender, else any value relayed to it in round 1, else `false`.

Since an omission adversary can only drop messages, every delivered message carries the sender's
input. If the sender is forever-honest, every forever-honest node receives its input in round 0.
Otherwise both other nodes are forever-honest and the relay round between them is never dropped.
-/

open MeasureTheory
open Cslib.Byzantine.LockStep (Inbox firstSome?_eq_some_iff)

namespace CommComplexityBA

/-- The first `some` entry of an inbox over `Fin 3`, if any. -/
def anyMsg (i : Inbox (Fin 3) Bool) : Option Bool :=
  (i 0).orElse fun _ => (i 1).orElse fun _ => i 2

/-- Decision rule of the relay protocol: own input, else the sender's round-0 message, else any
round-1 message, else `false`. -/
def relayDecide (x : Option Bool) (i0 i1 : Inbox (Fin 3) Bool) : Bool :=
  x.getD ((i0 0).getD ((anyMsg i1).getD false))

/-- The deterministic "send, then relay" broadcast protocol on three nodes (sender `0`). -/
def relayProtocol : Protocol (Fin 3) (Option Bool) Bool Unit where
  send _ x _ h _ := match h with
    | [] => x
    | [i0] => i0 0
    | _ => none
  decide _ x _ h := match h with
    | i0 :: i1 :: _ => some (relayDecide x i0 i1)
    | _ => none

/-- The relay protocol is (trivially) measurable. -/
theorem relay_isMeasurable : relayProtocol.IsMeasurable :=
  ⟨fun _ _ _ _ _ => Subsingleton.measurableSet, fun _ _ _ _ => Subsingleton.measurableSet⟩

section

variable (A : Adversary (Fin 3) 1) (b : Bool)

private lemma relay_hist (p : Fin 3) :
    (relayProtocol.run (bbInput 0 b) () A 2).1 p =
      [fun q => if A.drop (relayProtocol.run (bbInput 0 b) () A 1).2 q p then none
          else if q = p then none else bbInput 0 b q,
       fun q => if A.drop (relayProtocol.run (bbInput 0 b) () A 2).2 q p then none
          else if q = p then none else
            (if A.drop (relayProtocol.run (bbInput 0 b) () A 1).2 0 q then none
              else if (0 : Fin 3) = q then none else bbInput 0 b 0)] := rfl

private lemma relay_output (p : Fin 3) :
    relayProtocol.output (bbInput 0 b) () A p =
      some (relayDecide (bbInput 0 b p)
        (fun q => if A.drop (relayProtocol.run (bbInput 0 b) () A 1).2 q p then none
          else if q = p then none else bbInput 0 b q)
        (fun q => if A.drop (relayProtocol.run (bbInput 0 b) () A 2).2 q p then none
          else if q = p then none else
            (if A.drop (relayProtocol.run (bbInput 0 b) () A 1).2 0 q then none
              else if (0 : Fin 3) = q then none else bbInput 0 b 0))) := by
  rw [Protocol.output, firstSome?_eq_some_iff]
  refine ⟨2, ?_, fun r' hr' => ?_⟩
  · dsimp only; rw [relay_hist]; rfl
  · interval_cases r' <;> rfl

/-- Against every omission adversary corrupting at most one node, the relay protocol achieves
Byzantine broadcast (in the unique execution). -/
theorem relay_good : BBGood relayProtocol 0 b A () := by
  have hH : ∀ p, relayProtocol.Honest (bbInput 0 b) () A p →
      p ∉ A.corrupt (relayProtocol.run (bbInput 0 b) () A 1).2 ∧
        p ∉ A.corrupt (relayProtocol.run (bbInput 0 b) () A 2).2 := fun p hp => ⟨hp 0, hp 1⟩
  have hC : A.corrupt (relayProtocol.run (bbInput 0 b) () A 1).2 ⊆
      A.corrupt (relayProtocol.run (bbInput 0 b) () A 2).2 :=
    Protocol.corrupt_run_mono _ _ _ A (r := 0) (r' := 1) (Nat.zero_le 1)
  have hcard := A.card_corrupt (relayProtocol.run (bbInput 0 b) () A 2).2
  have hD1 := A.drop_spec (relayProtocol.run (bbInput 0 b) () A 1).2
  have hD2 := A.drop_spec (relayProtocol.run (bbInput 0 b) () A 2).2
  simp only [BBGood, TermCons, relay_output, Option.isSome_some, implies_true,
    Option.some.injEq, true_and]
  generalize relayProtocol.Honest (bbInput 0 b) () A = H at hH
  generalize A.drop (relayProtocol.run (bbInput 0 b) () A 1).2 = D1 at hD1 ⊢
  generalize A.drop (relayProtocol.run (bbInput 0 b) () A 2).2 = D2 at hD2 ⊢
  generalize A.corrupt (relayProtocol.run (bbInput 0 b) () A 1).2 = C1 at hD1 hC hH
  generalize A.corrupt (relayProtocol.run (bbInput 0 b) () A 2).2 = C2 at hD2 hC hH hcard
  -- validity: if the sender is not corrupted after round 0, everybody uncorrupted decides `b`
  have hval : (0 : Fin 3) ∉ C1 → ∀ p, p ∉ C1 →
      relayDecide (bbInput 0 b p)
        (fun q => if D1 q p = true then none else if q = p then none else bbInput 0 b q)
        (fun q => if D2 q p = true then none else if q = p then none else
          if D1 0 q = true then none else if (0 : Fin 3) = q then none else bbInput 0 b 0) = b := by
    intro h0 p hp
    have : D1 0 p = false := by
      by_contra hd
      rcases hD1 0 p (by simpa using hd) with h | h
      · exact h0 h
      · exact hp h
    fin_cases p <;> simp_all [relayDecide, bbInput]
  refine ⟨?_, fun h0 p hp => hval (hH 0 h0).1 p (hH p hp).1⟩
  rintro p q x y hp hq rfl rfl
  by_cases h0 : (0 : Fin 3) ∈ C1
  · -- the sender is corrupted: the two other nodes are not, and they relay to each other
    have h0' : (0 : Fin 3) ∈ C2 := hC h0
    have hnot : ∀ i : Fin 3, i ≠ 0 → i ∉ C2 := by
      intro i hi hiC
      have : ({0, i} : Finset (Fin 3)) ⊆ C2 := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl <;> assumption
      have := (Finset.card_le_card this).trans hcard
      rw [Finset.card_pair hi.symm] at this
      omega
    have h12 : D2 1 2 = false := by
      by_contra hd
      rcases hD2 1 2 (by simpa using hd) with h | h
      · exact hnot 1 (by decide) h
      · exact hnot 2 (by decide) h
    have h21 : D2 2 1 = false := by
      by_contra hd
      rcases hD2 2 1 (by simpa using hd) with h | h
      · exact hnot 2 (by decide) h
      · exact hnot 1 (by decide) h
    have hp0 : p ≠ 0 := fun h => (hH p hp).2 (h ▸ h0')
    have hq0 : q ≠ 0 := fun h => (hH q hq).2 (h ▸ h0')
    fin_cases p <;> fin_cases q <;> simp at hp0 hq0 <;>
      cases h01 : D1 0 1 <;> cases h02 : D1 0 2 <;>
      simp [relayDecide, anyMsg, bbInput, h12, h21, h01, h02]
  · rw [hval h0 p (fun h => (hH p hp).1 h), hval h0 q (fun h => (hH q hq).1 h)]

end

/-- **Non-vacuity of `SolvesBB`.** The relay protocol solves Byzantine broadcast on `3` nodes
(sender `0`) with probability `1` against every strongly adaptive omission adversary corrupting at
most one node. -/
theorem relay_solvesBB : SolvesBB relayProtocol (Measure.dirac ()) 0 1 1 := by
  intro A b
  have : {ω : Unit | ¬ BBGood relayProtocol 0 b A ω} = ∅ := by
    ext ⟨⟩
    simpa using relay_good A b
  simp [this]

end CommComplexityBA
