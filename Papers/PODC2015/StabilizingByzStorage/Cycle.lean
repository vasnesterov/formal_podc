import Papers.PODC2015.StabilizingByzStorage.Exec

/-!
# One cycle of the counterexample to Theorem 3 (Fig. 3)

`n = 9`, `t = 1` (so `t < n/8`), server `8` Byzantine, sequence numbers modulo `m = 2^64 + 1`,
values in `ℕ`. The `j`-th write writes the value `j` (with sequence number `j`).
-/

namespace Podc.StabilizingByzStorage.Atomic.Cex

open Podc.StabilizingByzStorage

set_option maxRecDepth 100000

abbrev N : ℕ := 9
abbrev M : ℕ := 2 ^ 64 + 1
abbrev T : ℕ := 1
abbrev Byz : Finset (Fin N) := {8}

abbrev D := Fin M × ℕ

/-- The sequence number `k mod m`. -/
def sq (k : ℕ) : Fin M := Fin.ofNat M k

/-- A server in a quiescent state holding `last_val = (k, k)`, `helping_val = ⊥`. -/
def srv0 (k : ℕ) : Server D :=
  ⟨(sq k, k), none, [], [], none, some ((sq k, k), none)⟩

/-- Start of a cycle: everything quiescent, last write wrote `k`, last read returned `k`. -/
def st0 (k : ℕ) : State N M ℕ :=
  ⟨fun _ => srv0 k, ⟨sq k, .idle⟩, ⟨sq k, k, .idle⟩⟩

def d (k : ℕ) : D := (sq k, k)

def allS : List (Fin N) := List.finRange N

def dWs (l : List (Fin N)) : List (Act N M ℕ) := l.map .dW
def dRs (l : List (Fin N)) : List (Act N M ℕ) := l.map .dR

/-- Byzantine read reply. -/
def br (x : D) (h : Option D) : Fin N → D × Option D := fun _ => (x, h)
/-- Byzantine write ack. -/
def ba (h : Option D) : Fin N → Option D := fun _ => h

/-- The actions of one cycle starting from `st0 k`. -/
def cycle (k : ℕ) : List (Act N M ℕ) :=
  -- R1: line N2
  [.invR] ++ dRs allS ++ [.endPre, .preNone {0,1,2,3,4,5,6,7} (br (d k) none)] ++
  -- R1: READ(true) reaches s0, s1
  dRs [0, 1] ++
  -- W1 (refreshes the helping values)
  [.invW (k+1)] ++ dWs allS ++ [.endW, .ack {0,1,2,3,4,5,6,7} (ba none)] ++ dWs allS ++ [.endH] ++
  dRs [2, 3] ++
  -- W2 (no refresh)
  [.invW (k+2)] ++ dWs allS ++ [.endW, .ack {0,1,2,3,4,5,6,7} (ba none)] ++
  dRs [4, 5] ++
  -- W3 = W_z (refresh, the Byzantine server acks ⊥)
  [.invW (k+3)] ++ dWs allS ++ [.endW, .ack {0,1,2,3,4,5,6,7} (ba none)] ++
  dRs [6] ++ dWs allS ++ [.endH] ++
  -- R1 first iteration fails
  [.endLoop, .retry {0,1,2,3,4,5,6,8} (br (d (k+3)) none)] ++
  -- W4 = W_y: WRITE reaches s0, s1 only
  [.invW (k+4)] ++ dWs [0, 1] ++
  -- R1 second iteration
  dRs [0, 1, 2, 3, 4, 5, 6, 7, 7, 8, 8] ++
  [.endLoop, .retLast {0,1,2,3,4,5,6,8} (br (d (k+4)) none) (d (k+4))] ++
  -- R2: N2, the sanity check adopts (k+3)
  [.invR] ++ dRs [0, 1, 2, 3, 4, 5, 6, 7, 8] ++
  [.endPre, .preAdopt {0,1,2,3,4,5,6,7} (br (d (k+3)) none) (d (k+3))] ++
  -- R2: READ(true) reaches s1..s7
  dRs [1, 2, 3, 4, 5, 6, 7, 8] ++
  [.endLoop, .retLast {1,2,3,4,5,6,7,8} (br (d (k+3)) none) (d (k+3))] ++
  -- completion of W4
  dRs [0] ++ dWs [2, 3, 4, 5, 6, 7, 8] ++ [.endW, .ack {0,1,2,3,4,5,6,7} (ba none)] ++
  dWs allS ++ [.endH] ++
  -- R3: a read alone
  [.invR] ++ dRs allS ++ [.endPre, .preAdopt {0,1,2,3,4,5,6,7} (br (d (k+4)) none) (d (k+4))] ++
  dRs allS ++ [.endLoop, .retLast {0,1,2,3,4,5,6,7} (br (d (k+4)) none) (d (k+4))]

def runCycle (k : ℕ) := run T Byz (st0 k) (cycle k)

theorem runCycle_isSome : (runCycle 0).isSome = true := by decide

/-- The trace of the cycle started in `st0 0` (labels and states after each step). -/
def trace0 : List (Label ℕ × State N M ℕ) := (runCycle 0).get runCycle_isSome

theorem runCycle_eq : runCycle 0 = some trace0 := by simp [trace0]

/-- Length of the cycle. -/
abbrev L : ℕ := 158

/-- The visible events of the cycle. -/
def expLab : ℕ → Label ℕ
  | 0 => .invRead | 14 => .invWrite 1 | 35 => .retWrite | 38 => .invWrite 2 | 49 => .retWrite
  | 52 => .invWrite 3 | 74 => .retWrite | 77 => .invWrite 4 | 92 => .retRead 4 | 93 => .invRead
  | 114 => .retRead 3 | 134 => .retWrite | 135 => .invRead | 157 => .retRead 4 | _ => .tau

theorem labs0_eq : trace0.map Prod.fst = (List.range L).map expLab := by decide

/-- Boolean check that the cycle ends in `st0 4`. -/
def finalOK : Bool :=
  match trace0.getLast? with
  | some (_, σ) => decide ((∀ s, σ.srv s = srv0 4) ∧ σ.w = (st0 4).w ∧ σ.r = (st0 4).r)
  | none => false

theorem finalOK_eq : finalOK = true := by decide

/-- The choice made by an action at a threshold test is the "freshest" one: at line 12 the chosen
`last_val` has the largest sequence number (for `≥cd`) among the values with `2t + 1` copies; at
line N4 the chosen helping value is the only one with `2t + 1` copies. -/
def freshChoice (σ : State N M ℕ) : Act N M ℕ → Bool
  | .retLast Q byz d =>
    decide (∀ s ∈ Q, 2 * T + 1 ≤ cnt Q (fun s => (repVec Byz σ byz s).1) (repVec Byz σ byz s).1 →
      ¬ gtcd (repVec Byz σ byz s).1.1 d.1)
  | .preAdopt Q byz d =>
    decide (∀ s ∈ Q, ∀ x, (repVec Byz σ byz s).2 = some x →
      2 * T + 1 ≤ cnt Q (fun s => (repVec Byz σ byz s).2) (some x) → x = d)
  | _ => true

/-- `freshChoice` holds at every action of a run. -/
def allFresh (σ : State N M ℕ) : List (Act N M ℕ) → Bool
  | [] => true
  | a :: as => freshChoice σ a && match apply T Byz σ a with
    | some (_, σ') => allFresh σ' as
    | none => false

/-- In the counterexample cycle, every value chosen at a threshold test is the freshest candidate:
the counterexample does not depend on resolving the ambiguity of line 12 in an unnatural way. -/
theorem cycle_allFresh : allFresh (st0 0) (cycle 0) = true := by decide

end Podc.StabilizingByzStorage.Atomic.Cex
