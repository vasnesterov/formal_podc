import Papers.PODC2012.OrderPreservingByzRenaming.Alg5

/-!
# The pseudocode of Rounds 2–3 of Algorithm 5 breaks Lemmas 29–30

Lines 10–11 of Algorithm 5 *add* the ids echoed `n - t` times to `Ids`, which still contains the
Round-1 ids, and Lines 13–14 broadcast Ready for all of `Ids`. The text of §6.1.1 ("Only ids that have
been echoed at least `n - t` times are considered for the following round") and the proof of
Lemma 29 use only the echoed ids; `Alg5.step` follows the text. With the pseudocode, a correct process
sends Ready for every id it received in Round 1, and with `n = 3t + 1` (so `n - 2t = t + 1`) one
correct Ready plus `t` Byzantine ones get an id accepted.

Concrete instance: `n = 4`, `t = 1`, Byzantine process `3` sends the fake ids `10, 11, 12` to the
correct processes `0, 1, 2` in Round 1 and Ready for all of them in Round 3. Every correct process
accepts 6 ids, more than the bound `n + ⌊t²/(n-2t)⌋ = 4` of Lemma 30 and the namespace
`n + t - 1 = 4` of Theorem 39.
-/

namespace Podc.OrderPreservingByzRenaming.Alg5

variable (n t : ℕ) (sel : ℕ → List ℚ → List ℚ)

/-- The transition of Algorithm 5 with Lines 10–11 read literally (`Ids := Ids ∪ …`). -/
def stepPC (r : ℕ) (st : St) (ib : Fin n → Option Msg) : St :=
  match r with
  | 1 => { st with rdy := st.ids ∪ atLeast n (fun j => echoOf (ib j)) (n - t) }
  | r => step n t sel r st ib

/-- Runs of the literal pseudocode. -/
def runPC (F : Finset (Fin n)) (x : Fin n → ℕ) (adv : ℕ → Fin n → Fin n → Option Msg) :
    ℕ → Fin n → St
  | 0, _ => {}
  | r + 1, p => stepPC n t sel r (runPC F x adv r p) fun j =>
      if j = p then out (x p) (runPC F x adv r p) r
      else if j ∈ F then adv r j p else out (x j) (runPC F x adv r j) r

namespace CexPC

/-- The adversary: fake id `10 + p` to process `p` in Round 1, Ready for all fake ids in Round 3. -/
def adv (r : ℕ) (_b p : Fin 4) : Option Msg :=
  match r with
  | 0 => some (.ident (10 + p.val))
  | 2 => some (.ready {10, 11, 12})
  | _ => none

/-- With the literal pseudocode, correct process `0` accepts 6 ids. -/
lemma acc_card : (runPC 4 1 selPaper {3} (fun j => j.val) adv 3 0).acc = {0, 1, 2, 10, 11, 12} := by
  decide +kernel

/-- With the text's reading (`Alg5.run`), the fake ids are not accepted. -/
lemma acc_card_text : (run 4 1 selPaper {3} (fun j => j.val) adv 3 0).acc = {0, 1, 2} := by
  decide +kernel

end CexPC

/-- **Lemma 30 fails for the literal pseudocode**: `6 > n + ⌊t²/(n - 2t)⌋ = 4 = n + t - 1`. -/
theorem lemma_30_false_pseudocode :
    (runPC 4 1 selPaper {3} (fun j => j.val) CexPC.adv 3 0).acc.card > 4 + 1 ^ 2 / (4 - 2 * 1) ∧
    (runPC 4 1 selPaper {3} (fun j => j.val) CexPC.adv 3 0).acc.card > 4 + 1 - 1 := by
  rw [CexPC.acc_card]; decide

end Podc.OrderPreservingByzRenaming.Alg5
