import Papers.PODC2011.AtMostOnceEffectiveness.Model

/-!
# Algorithm `KK_β` (Figures 1 and 2 of the paper)

Processes are `Fin m`; process `p` has paper identifier `p.val + 1`. Jobs are the numbers
`1, …, n`; the value `0` in a register means "no job".

Shared variables:
* `next q` (`next_{q+1}` of the paper, initially `0`): the job process `q` is about to perform;
* `done q j` (`done_{q+1, j}`, `j ≥ 1`, initially `0`): the `j`-th job performed by process `q`.

Local state of process `p` (`LState`): `STATUS_p`, `DONE_p`, `TRY_p`, `POS_p` (indexed by
`0`-based process numbers), `NEXT_p` and the loop index `Q_p` (`0`-based, so the paper's `Q_p = 1`
is `q = 0`). The paper's `FREE_p` is not stored: since `FREE_p` starts as `J` and every
update removes from `FREE_p` exactly the element added to `DONE_p`, `FREE_p = J \ DONE_p` always,
and we use this as the definition (`free`). `TMP_p` only carries values inside one action and is
not stored.

`compNext`: if `|FREE_p \ TRY_p| ≥ β`, the paper sets
`TMP_p = (|FREE_p| − (m−1)) / m` (a rational number) and picks the element of rank
`⌊(p−1)·TMP_p⌋ + 1` of `FREE_p \ TRY_p` if `TMP_p ≥ 1`, and the element of rank `p` otherwise
(`kIdx`; with `0`-based `p` and `F = |FREE_p|`, `TMP_p ≥ 1 ↔ F ≥ 2m − 1` and
`⌊(p−1)·TMP_p⌋ = ⌊(p−1)(F − (m−1)) / m⌋`).

`rank S k` is the element of `S` of rank `k` (the `k`-th smallest, `k ≥ 1`). The paper leaves it
undefined for `k > |S|`; this can only happen when `β < m`. We clamp `k` to `|S|`, so that
`NEXT_p ∈ FREE_p \ TRY_p` whenever this set is nonempty.
-/

set_option linter.unusedSectionVars false

namespace Podc.AtMostOnceEffectiveness

/-- `STATUS_p` (the paper's `stop` is modelled by fairness exemptions, see `Model.lean`). -/
inductive Status where
  | compNext | setNext | gatherTry | gatherDone | check | doIt | done | finished
  deriving DecidableEq

/-- The local state of a process. -/
structure LState where
  /-- `STATUS_p`. -/
  status : Status
  /-- `DONE_p`. -/
  doneS : Finset ℕ
  /-- `TRY_p`. -/
  tryS : Finset ℕ
  /-- `POS_p` (indexed by `0`-based process numbers; positions are `1`-based). -/
  pos : ℕ → ℕ
  /-- `NEXT_p`. -/
  nxt : ℕ
  /-- `Q_p − 1` (the loop index, `0`-based). -/
  q : ℕ

/-- Shared registers. -/
inductive Reg where
  /-- `next_{q+1}`. -/
  | next (q : ℕ)
  /-- `done_{q+1, j}`. -/
  | done (q j : ℕ)
  deriving DecidableEq

/-- `rank S k`: the element of rank `k` (`k`-th smallest, `1 ≤ k ≤ |S|`) of `S`; `k` is clamped
to `|S|`. -/
noncomputable def rank (S : Finset ℕ) (k : ℕ) : ℕ := Nat.nth (· ∈ S) (min k S.card - 1)

/-- The rank (`1`-based) chosen by the `0`-based process `p` when `|FREE_p| = F`. -/
def kIdx (m p F : ℕ) : ℕ := if 2 * m - 1 ≤ F then p * (F - (m - 1)) / m + 1 else p + 1

/-- `FREE_p = J \ DONE_p`. -/
def free (n : ℕ) (s : LState) : Finset ℕ := Finset.Icc 1 n \ s.doneS

/-- The initial local state. -/
def LState.init : LState := ⟨.compNext, ∅, ∅, fun _ => 1, 0, 0⟩

/-- End of one iteration of the `gatherTry`/`gatherDone` loops: `Q_p ← Q_p + 1`, and when the
loop is over, `Q_p ← 1` and `STATUS_p ← st`. -/
def LState.adv (m : ℕ) (s : LState) (st : Status) : LState :=
  if s.q + 1 < m then { s with q := s.q + 1 } else { s with q := 0, status := st }

/-- `TRY_p` after reading the value `v` from `next_Q`: `v` is added if `v > 0`. -/
def addTry (v : ℕ) (t : Finset ℕ) : Finset ℕ := if 0 < v then insert v t else t

/-- The transitions of Figure 2. -/
noncomputable def kkNext (m n β : ℕ) (p : Fin m) (s : LState) : Step Reg ℕ LState :=
  match s.status with
  | .compNext =>
    if β ≤ (free n s \ s.tryS).card then
      .internal { s with status := .setNext, q := 0, tryS := ∅,
                         nxt := rank (free n s \ s.tryS) (kIdx m p (free n s).card) }
    else .internal { s with status := .finished }
  | .setNext => .write (.next p) s.nxt { s with status := .gatherTry }
  | .gatherTry =>
    if s.q ≠ p.val then
      .read (.next s.q) (fun v => ({ s with tryS := addTry v s.tryS }).adv m .gatherDone)
    else .internal (s.adv m .gatherDone)
  | .gatherDone =>
    if s.q ≠ p.val then
      .read (.done s.q (s.pos s.q)) (fun v =>
        if s.pos s.q ≤ n ∧ 0 < v then
          { s with doneS := insert v s.doneS,
                   pos := Function.update s.pos s.q (s.pos s.q + 1) }
        else s.adv m .check)
    else .internal (s.adv m .check)
  | .check =>
    .internal (if s.nxt ∉ s.tryS ∧ s.nxt ∉ s.doneS then { s with status := .doIt }
               else { s with status := .compNext })
  | .doIt => .perform s.nxt { s with status := .done }
  | .done =>
    .write (.done p (s.pos p)) s.nxt
      { s with doneS := insert s.nxt s.doneS,
               pos := Function.update s.pos p (s.pos p + 1), status := .compNext }
  | .finished => .halt

/-- Algorithm `KK_β` for `m` processes and `n` jobs. -/
noncomputable def kk (m n β : ℕ) : Alg m Reg ℕ LState where
  memInit := fun _ => 0
  locInit := fun _ => LState.init
  next := kkNext m n β

end Podc.AtMostOnceEffectiveness
