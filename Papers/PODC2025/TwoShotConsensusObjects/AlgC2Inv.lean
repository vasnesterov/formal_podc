import Papers.PODC2025.TwoShotConsensusObjects.AlgC2Decide

/-!
# Class `C₂`, sufficiency: the invariant of Algorithm 3

The invariant `Inv C h` of the reachable configurations `C` of Algorithm 3, where `h` is the
(ghost) history of the operations applied to the object `O`:

* the registers hold the values determined by the local states (`regOf`);
* the object `O` is in state `after O s h`; the operations of `p` in `h` and their responses
  are the ones recorded in the local state of `p` (`opsL`, `respL`);
* the round protocol: every value seen is the other's value at the start of the round, and in
  no round both processes miss each other (`seen`, `unseen`, used for Lemma 3);
* temporal facts recorded when reads happen (`t1`, `w`, `t2`);
* decisions: the decision index is the process whose first operation on `O` is first in `h`.
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

section Defs

variable {ρ : Type}

/-- The number of rounds whose register `Round[i][r]` has been written by the process. -/
def LS.wr (l : LS ρ) : ℕ :=
  if l.pc < 3 then 0 else if l.pc = 4 then l.rs.length + 1 else l.rs.length

/-- The owner (writer) of a register. -/
def Reg.owner : Reg → Fin 2
  | .val p => p
  | .ret p => p
  | .round p _ => p
  | .next p => p

/-- The value of a register as determined by the local state of its owner. -/
def regLoc (l : LS ρ) : Reg → RV ρ
  | .val _ => if 1 ≤ l.pc then .b l.inp else .bot
  | .ret _ => if 3 ≤ l.pc then .r l.r0 else .bot
  | .round p r => if r < l.wr then .n (opOf p (l.rs.take r)) else .bot
  | .next p => if 6 ≤ l.pc then .n (opOf p l.rs) else .bot

/-- The value of a register as determined by the local states. -/
def regOf (L : Fin 2 → LS ρ) (j : Reg) : RV ρ := regLoc (L j.owner) j

/-- The responses obtained by a process from `O`, as recorded in its local state. -/
def respL (l : LS ρ) : List (Option ρ) :=
  (if 2 ≤ l.pc then [l.r0] else []) ++ (if 7 ≤ l.pc then [l.r1] else [])

end Defs

variable {O : ObjSpec} (s : O.State) (f g : O.Op) (c : ℕ → O.Op) (k : ℕ)

/-- The operations applied to `O` by process `p`, as recorded in its local state. -/
def opsL (p : Fin 2) (l : LS O.Resp) : List (Fin 2 × O.Op) :=
  (if 2 ≤ l.pc then [(p, if p = 0 then f else g)] else []) ++
    (if 7 ≤ l.pc then [(p, c (opOf p l.rs))] else [])

/-- **The invariant of Algorithm 3** on the local states `L` (inputs `x`), with ghost history
`h` of the object `O`. -/
structure InvL (x : Fin 2 → Bool) (L : Fin 2 → LS O.Resp) (h : List (Fin 2 × O.Op)) : Prop where
  id : ∀ p, (L p).id = p
  inp : ∀ p, (L p).inp = x p
  pc : ∀ p, (L p).pc ≤ 10
  len0 : ∀ p, (L p).pc ≤ 2 → (L p).rs = []
  len1 : ∀ p, (L p).pc ≤ 4 → (L p).rs.length < k
  len2 : ∀ p, 5 ≤ (L p).pc → (L p).rs.length = k
  hist : ∀ p, h.filter (·.1 = p) = opsL f g c p (L p)
  vw : ∀ p, (view O s h p).map some = respL (L p)
  seen : ∀ (p : Fin 2) (r x : ℕ), (L p).rs[r]? = some (some x) →
    r < (L (1 - p)).wr ∧ x = opOf (1 - p) ((L (1 - p)).rs.take r)
  unseen : ∀ r : ℕ, (L 0).rs[r]? = some none → (L 1).rs[r]? ≠ some none
  bnd : ∀ p r, opOf p ((L p).rs.take r) ≤ 3 ^ r
  t1 : ∀ p, (h.take 2).map Prod.fst = [p, p] → ∀ o ∈ (L p).rs, o = none
  w : ∀ p, 8 ≤ (L p).pc → (L p).w = none ∨ (L p).w = (view O s h (1 - p)).head?
  t2 : ∀ p, 8 ≤ (L p).pc → (L p).w = none →
    ∃ u v, h = u ++ v ∧ (u.filter (·.1 = 1 - p)).length ≤ 1 ∧ ∀ e ∈ v, e.1 = 1 - p
  dec : ∀ p, 9 ≤ (L p).pc → h.head?.map Prod.fst = some (L p).dec
  out : ∀ p, (L p).pc = 10 → (L p).out = x (L p).dec

/-- **The invariant of Algorithm 3** on configurations, with ghost history `h` of `O`. -/
def Inv (C : Cfg (algC2 s f g c k)) (h : List (Fin 2 × O.Op)) : Prop :=
  InvL s f g c k C.inp C.loc h ∧ (∀ j, C.mem (.inl j) = regOf C.loc j) ∧
    C.mem (.inr ()) = after O s h

variable {s f g c k}

lemma inv_init (hk : 1 ≤ k) (x : Fin 2 → Bool) :
    Inv s f g c k (initCfg (algC2 s f g c k) x) [] := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [initCfg, algC2, regOf, regLoc, LS.wr, opsL, respL, view, resps, opOf]
  all_goals first
    | omega
    | (intro r; exact Nat.one_le_pow _ _ (by norm_num))
    | (intro j; cases j <;> rfl)

end TwoShotCons
