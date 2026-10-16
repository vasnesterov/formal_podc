import Papers.PODC2022.HybridApproxAgreement.RBC

/-!
# The Overlap All-to-All Broadcast protocol `Π_oBC` (Section 4.2) and `Π_AA` with one iteration

`Π_oBC`, code for party `P` with input `v` (`τ_start = 0`):

```
 3: invoke Π_rBC with input v; join the Π_rBC instance of every party P'
 4: repeat
 5:   upon obtaining v via Π_rBC with sender P': FIFO-send (report, v, P'); add (v, P') to O
 8:   upon FIFO-receiving (report, v, P') from P'': add (v, P') to R_P''
10: until τ_now > 3Δ and |O| ≥ n - tₛ
11: repeat
12:   upon obtaining v via Π_rBC with sender P': add (v, P') to O
14:   upon FIFO-receiving (report, v, P') from P'': add (v, P') to R_P''
16:   W := {P' | R_P' ⊆ O and |R_P'| ≥ n - tₛ}
17: until τ_now > 4Δ and |W| ≥ n - tₛ
18: output O and terminate
```

Encoding (on top of `RBC.lean`): one `RBC.St` per sender; messages `inst s m` (message `m` of the
instance with sender `s`) and `report k v s` (the `k`-th report of the sender, FIFO channels simulated
with sequence numbers as suggested in the paper: `R_P''` is the longest gap-free prefix of the reports
received from `P''`). `O` is a partial map sender ↦ value (as in `Iteration.lean`). Within one step,
the instances are stepped first (in the order of the senders), then reports are filed, then the exit
conditions of the two loops are checked. A terminated party stops.

`Π_AA` with `S = 1` iteration (`S = ⌈log₂(δmax/ε)⌉ = 1` iff `ε < δmax ≤ 2ε`): run `Π_oBC` on the input
and output `aaStep tₛ tₐ O` (lines 4–7 of `Π_AA`) on termination (`aaAlg`).
-/

open Cslib.Byzantine.PartialSync

namespace HybridApproxAgreement.OBC

variable {n : ℕ} {V : Type} [DecidableEq V]

/-- Messages of `Π_oBC`. -/
inductive Msg (n : ℕ) (V : Type) where
  /-- a message of the `Π_rBC` instance with sender `s` -/
  | inst (s : Fin n) (m : RBC.Msg n V)
  /-- the `k`-th FIFO report `(report, v, s)` -/
  | report (k : ℕ) (v : V) (s : Fin n)
  deriving DecidableEq

/-- Local state of `Π_oBC`. -/
structure St (n : ℕ) (V : Type) where
  /-- the clock (`τ_now - τ_start`) -/
  clock : ℕ
  /-- the `Π_rBC` instance with sender `s` -/
  rbc : Fin n → RBC.St n V
  /-- the set `O` of value–sender pairs, as a partial map -/
  O : Fin n → Option V
  /-- number of reports sent so far -/
  nrep : ℕ
  /-- reports received from each party, with sequence numbers -/
  buf : Fin n → List (ℕ × V × Fin n)
  /-- `1`: first loop, `2`: second loop, `3`: terminated -/
  phase : ℕ
  /-- messages to broadcast at the next tick -/
  outbox : List (Msg n V)
  deriving DecidableEq

/-- The longest gap-free prefix `0, 1, …` of received reports (FIFO delivery). -/
def fifoPrefix (b : List (ℕ × V × Fin n)) : List (V × Fin n) :=
  go 0 (b.length + 1)
where
  go (k : ℕ) : ℕ → List (V × Fin n)
    | 0 => []
    | fuel + 1 => match b.find? (fun e => e.1 = k) with
      | some e => e.2 :: go (k + 1) fuel
      | none => []

/-- `R_P'` from the received reports. -/
def reportsOf (s : St n V) (p' : Fin n) : List (V × Fin n) := fifoPrefix (s.buf p')

/-- The number of senders in `O`. -/
def cardO (O : Fin n → Option V) : ℕ := ((List.finRange n).filter fun s => (O s).isSome).length

/-- `P'` is a witness: `R_P' ⊆ O` and `|R_P'| ≥ q`. -/
def isWitness (q : ℕ) (s : St n V) (p' : Fin n) : Bool :=
  ((reportsOf s p').all fun e => decide (s.O e.2 = some e.1)) &&
    decide (q ≤ (reportsOf s p').dedup.length)

/-- The witness set `W`, as a list. -/
def witnesses (q : ℕ) (s : St n V) : List (Fin n) := (List.finRange n).filter (isWitness q s)

/-- Messages of the instance with sender `s` among the received ones. -/
def instMsgs (ms : List (Msg n V)) (s : Fin n) : List (RBC.Msg n V) :=
  ms.filterMap fun | .inst s' m => if s' = s then some m else none | _ => none

/-- Step all `Π_rBC` instances (lines 5/12: new outputs are added to `O` and, in the first loop,
reported). Returns the new state and the produced messages. -/
def stepInstances (Δ q : ℕ) (self : Fin n) (s : St n V) (ms : List (Msg n V)) :
    St n V × List (Msg n V) :=
  (List.finRange n).foldl (fun (acc : St n V × List (Msg n V)) snd =>
    let st := acc.1
    let r := RBC.stepI Δ q st.clock self (st.rbc snd) (instMsgs ms snd)
    let st1 := { st with rbc := Function.update st.rbc snd r.1 }
    let msgs := r.2.map (.inst snd)
    match (st.rbc snd).out, r.1.out with
    | none, some v =>
      if st.phase = 1 then
        ({ st1 with O := Function.update st.O snd (some v), nrep := st.nrep + 1 },
          acc.2 ++ msgs ++ [.report st.nrep v snd])
      else ({ st1 with O := Function.update st.O snd (some v) }, acc.2 ++ msgs)
    | _, _ => (st1, acc.2 ++ msgs)) (s, [])

/-- File the received reports (lines 8/14). -/
def fileReports (s : St n V) (inbox : Fin n → List (Msg n V)) : St n V :=
  { s with buf := fun p'' => ((inbox p'').filterMap fun
      | .report k v snd => some (k, v, snd) | _ => none).reverse ++ s.buf p'' }

/-- Exit conditions of the two loops (lines 10, 17–18). -/
def checkExit (Δ q : ℕ) (s : St n V) : St n V :=
  if s.phase = 1 ∧ 3 * Δ < s.clock ∧ q ≤ cardO s.O then { s with phase := 2 }
  else if s.phase = 2 ∧ 4 * Δ < s.clock ∧ q ≤ (witnesses q s).length then { s with phase := 3 }
  else s

/-- `Π_oBC` with time unit `Δ` and threshold `q = n - tₛ` as a PSync algorithm (input: own value;
decision: the output `O`). -/
def alg (Δ q : ℕ) : Algorithm (Fin n) (Msg n V) (St n V) V (Fin n → Option V) where
  init p v := ⟨0, fun _ => {}, fun _ => none, 0, fun _ => [], 1, [.inst p (.propose v)]⟩
  step p s inbox :=
    if s.phase = 3 then { s with clock := s.clock + 1, outbox := [] } else
      let ms := (List.finRange n).flatMap inbox
      let r := stepInstances Δ q p s ms
      let s2 := fileReports r.1 inbox
      let s3 := checkExit Δ q s2
      { s3 with clock := s.clock + 1, outbox := r.2 }
  send _ s _ := s.outbox
  decide _ s := if s.phase = 3 then some s.O else none

end HybridApproxAgreement.OBC
