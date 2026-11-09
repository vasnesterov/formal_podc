import Papers.PODC2015.StabilizingByzStorage.Cycle

/-!
# The inversion does not depend on how line 12 picks among several candidates

In `Cex.cycle`, the second iteration of `R1` sees two `last_val`s with `2t + 1` copies, `(4, 4)` three
times and `(3, 3)` five times, and takes the fresher `(4, 4)`. A rule "take the most frequent value"
would take `(3, 3)` there. This file gives a variant (a finite execution from the same clean
configuration `st0 0`, `n = 9`, `t = 1`) in which correct server `6` lags on the writer's link: there
the value taken at every threshold test is both the freshest and the *strictly most frequent*
candidate, and `R1` returns `4` while the later `R2` returns `3` (`W3` completed before `W4` started).
So the new/old inversion arises for both natural resolutions of the ambiguity of line 12.
-/

namespace Podc.StabilizingByzStorage.Atomic.Cex

open Podc.StabilizingByzStorage

set_option maxRecDepth 100000

/-- The variant execution (a prefix up to the inverted read `R2`). -/
def variant : List (Act N M ℕ) :=
  -- R1: lines N2–N7
  [.invR] ++ dRs allS ++ [.endPre, .preNone {0,1,2,3,4,5,6,7} (br (d 0) none)] ++
  dRs [0, 1] ++
  -- W1 (refresh), W2 (no refresh)
  [.invW 1] ++ dWs allS ++ [.endW, .ack {0,1,2,3,4,5,6,7} (ba none)] ++ dWs allS ++ [.endH] ++
  dRs [2, 3] ++
  [.invW 2] ++ dWs allS ++ [.endW, .ack {0,1,2,3,4,5,6,7} (ba none)] ++
  dRs [4, 5] ++
  -- W3 (refresh); server 6 does not deliver it yet
  [.invW 3] ++ dWs [0, 1, 2, 3, 4, 5, 7, 8] ++ [.endW, .ack {0,1,2,3,4,5,7,8} (ba none)] ++
  dRs [7] ++ dWs [0, 1, 2, 3, 4, 5, 7, 8] ++ [.endH] ++
  -- R1 first iteration fails
  [.endLoop, .retry {0,1,2,3,4,5,7,8} (br (d 3) none)] ++
  -- W4: WRITE reaches s0, s1, s2
  [.invW 4] ++ dWs [0, 1, 2] ++
  -- R1 second iteration: (4, 4) four times, (3, 3) three times, (2, 2) once
  dRs [0, 1, 2, 3, 4, 5, 7, 6, 6] ++
  [.endLoop, .retLast {0,1,2,3,4,5,6,8} (br (d 4) none) (d 4)] ++
  -- R2: the sanity check adopts (3, 3); the loop sees (3, 3) as the only candidate
  [.invR] ++ dRs allS ++ [.endPre, .preAdopt {0,1,2,3,4,5,6,7} (br (d 4) none) (d 3)] ++
  dRs [1, 2, 3, 4, 5, 6, 7, 8] ++
  [.endLoop, .retLast {1,2,3,4,5,6,7,8} (br (d 3) none) (d 3)]

/-- At a threshold test, the chosen value is the freshest candidate (`freshChoice`) and, at line 12,
strictly more frequent than every other `last_val` in the collection. -/
def mostFrequentChoice (σ : State N M ℕ) : Act N M ℕ → Bool
  | .retLast Q byz d =>
    decide (∀ s ∈ Q, (repVec Byz σ byz s).1 ≠ d →
      cnt Q (fun s => (repVec Byz σ byz s).1) (repVec Byz σ byz s).1 <
        cnt Q (fun s => (repVec Byz σ byz s).1) d) && freshChoice σ (.retLast Q byz d)
  | a => freshChoice σ a

/-- `mostFrequentChoice` holds at every action of a run. -/
def allMostFrequent (σ : State N M ℕ) : List (Act N M ℕ) → Bool
  | [] => true
  | a :: as => mostFrequentChoice σ a && match apply T Byz σ a with
    | some (_, σ') => allMostFrequent σ' as
    | none => false

/-- The variant is an execution of Fig. 3 whose visible events are
`R1 ∥ (W1; W2; W3; W4 …)`, `R1` returns `4`, then `R2` returns `3`: a new/old inversion. -/
theorem variant_labels :
    (run T Byz (st0 0) variant).map (fun tr => (tr.map Prod.fst).filter (· ≠ .tau)) =
      some [.invRead, .invWrite 1, .retWrite, .invWrite 2, .retWrite, .invWrite 3, .retWrite,
        .invWrite 4, .retRead 4, .invRead, .retRead 3] := by decide

/-- In the variant every threshold choice is both the freshest and the most frequent candidate. -/
theorem variant_allMostFrequent : allMostFrequent (st0 0) variant = true := by decide

end Podc.StabilizingByzStorage.Atomic.Cex
