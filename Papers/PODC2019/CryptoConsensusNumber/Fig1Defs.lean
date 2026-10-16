import Papers.PODC2019.CryptoConsensusNumber.Defs
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Podc.SharedMemory.Potential

/-!
# Figure 1: asset transfer from an atomic snapshot (definitions)

Guerraoui et al., *The Consensus Number of a Cryptocurrency*, PODC 2019, Figure 1.

Every process `p` owns component `p` of an atomic snapshot object `AS` and stores there the
transfers it has performed successfully. `balance(a, S)` is the initial balance of `a` plus the
incoming minus the outgoing amounts recorded in the snapshot `S`.

* `transfer(a, b, x)` by `p`: `S := AS.snapshot()`; if `p ∉ μ(a)` or `balance(a, S) < x` return
  `false`; otherwise add `(a, b, x)` to `ops_p`, `AS.update(ops_p)`, return `true`;
* `read(a)`: `S := AS.snapshot()`, return `balance(a, S)`.

The paper's `ops_p` is a *set*. We define the implementation generically in the operation
`add : ops → transfer → ops` that records a new transfer:

* `impl` uses `add ops t = ops ++ [t]` (a sequence: repeated identical transfers are recorded
  repeatedly) — the **fixed** algorithm, which is linearizable (`Fig1.lean`);
* `literalImpl` uses `add ops t = ops.insert t` (insert if absent, i.e. set union) — the
  algorithm **as written** in Figure 1, which is not linearizable (`Fig1Bug.lean`).

Local computation is folded into the continuations of the base-object accesses.
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig1

open Cslib.SharedMemory

/-- A recorded transfer `(a, b, x)`: source, destination, amount. -/
abbrev Tr (Acct : Type) := Acct × Acct × ℕ

/-- The base object: an atomic snapshot whose components (one per process) are lists of
recorded transfers, initially empty. -/
abbrev Mem (P Acct : Type) [DecidableEq P] : Unit → ObjSpec :=
  fun _ => snapObj P (List (Tr Acct)) []

/-! ## Balances computed from a snapshot -/

section Balance

variable {P Acct : Type} [Fintype P] [DecidableEq Acct]

/-- Amount received by `c` in a list of transfers. -/
def inAmt (c : Acct) (l : List (Tr Acct)) : ℕ := (l.map fun t => if t.2.1 = c then t.2.2 else 0).sum

/-- Amount sent from `c` in a list of transfers. -/
def outAmt (c : Acct) (l : List (Tr Acct)) : ℕ := (l.map fun t => if t.1 = c then t.2.2 else 0).sum

/-- Total incoming amount of `c` recorded in the snapshot `S`. -/
def inflow (c : Acct) (S : P → List (Tr Acct)) : ℕ := ∑ q, inAmt c (S q)

/-- Total outgoing amount of `c` recorded in the snapshot `S`. -/
def outflow (c : Acct) (S : P → List (Tr Acct)) : ℕ := ∑ q, outAmt c (S q)

/-- `balance(a, S)`: initial balance plus incoming minus outgoing amounts (truncated
subtraction; the invariant shows that no truncation happens). -/
def balance (q₀ : Acct → ℕ) (c : Acct) (S : P → List (Tr Acct)) : ℕ :=
  q₀ c + inflow c S - outflow c S

end Balance

/-! ## The implementation -/

/-- Program counter of a process. -/
inductive PC (Acct : Type) where
  /-- No pending operation. -/
  | idle
  /-- `transfer(a, b, x)`: about to take the snapshot (line 1). -/
  | scanT (a b : Acct) (x : ℕ)
  /-- `transfer(a, b, x)`: the check passed, about to update (lines 4–5). -/
  | upd (a b : Acct) (x : ℕ)
  /-- `read(a)`: about to take the snapshot (line 7). -/
  | scanR (a : Acct)
  /-- About to return `r`. -/
  | done (r : Bool ⊕ ℕ)

/-- Local state: the local copy `ops_p` of the own component and the program counter. -/
structure Loc (Acct : Type) where
  /-- `ops_p`. -/
  ops : List (Tr Acct)
  /-- Program counter. -/
  pc : PC Acct

variable {P Acct : Type} [Fintype P] [DecidableEq P] [DecidableEq Acct]

/-- Processes invoke transfers only under their own identity. -/
def allowedOp (p : P) : ATOp P Acct → Prop
  | .transfer p' _ _ _ => p' = p
  | .read _ => True

/-- Figure 1, parametrized by the way `ops_p` records a new successful transfer. -/
def implGen (μ : Acct → Finset P) (q₀ : Acct → ℕ) (add : List (Tr Acct) → Tr Acct → List (Tr Acct)) :
    Impl (atSpec P Acct μ q₀) (Mem P Acct) P (Loc Acct) where
  memInit _ := fun _ => []
  locInit _ := ⟨[], .idle⟩
  invoke _ l o := match o with
    | .transfer _ a b x => ⟨l.ops, .scanT a b x⟩
    | .read a => ⟨l.ops, .scanR a⟩
  act p l := match l.pc with
    | .idle => .ret (.inl false) l
    | .scanT a b x => .access () .scan (fun r =>
        match r with
        | some S => if p ∈ μ a ∧ x ≤ balance q₀ a S then ⟨l.ops, .upd a b x⟩
          else ⟨l.ops, .done (.inl false)⟩
        | none => ⟨l.ops, .done (.inl false)⟩)
    | .upd a b x => .access () (.update p (add l.ops (a, b, x)))
        (fun _ => ⟨add l.ops (a, b, x), .done (.inl true)⟩)
    | .scanR a => .access () .scan (fun r =>
        ⟨l.ops, .done (.inr (balance q₀ a ((r.getD fun _ => []))))⟩)
    | .done r => .ret r ⟨l.ops, .idle⟩
  allowed := allowedOp

/-- **Figure 1, fixed**: `ops_p` is the *sequence* of `p`'s successful transfers. -/
def impl (μ : Acct → Finset P) (q₀ : Acct → ℕ) :
    Impl (atSpec P Acct μ q₀) (Mem P Acct) P (Loc Acct) :=
  implGen μ q₀ (fun ops t => ops ++ [t])

/-- **Figure 1, literally**: `ops_p` is a *set* (`ops_p := ops_p ∪ {(a, b, x)}`, realized as
"insert if absent" on a duplicate-free list). -/
def literalImpl (μ : Acct → Finset P) (q₀ : Acct → ℕ) :
    Impl (atSpec P Acct μ q₀) (Mem P Acct) P (Loc Acct) :=
  implGen μ q₀ (fun ops t => ops.insert t)

/-! ## Step lemmas -/

section Steps

variable {μ : Acct → Finset P} {q₀ : Acct → ℕ} {add : List (Tr Acct) → Tr Acct → List (Tr Acct)}

abbrev Cfg (μ : Acct → Finset P) (q₀ : Acct → ℕ) :=
  Config (atSpec P Acct μ q₀) (Mem P Acct) P (Loc Acct)

lemma step_inv_eq (C : Cfg μ q₀) (p : P) (o : ATOp P Acct) (h0 : C.pend p = none)
    (ha : allowedOp p o) :
    (implGen μ q₀ add).step C (.inv p o) = some { C with
      pend := Function.update C.pend p (some o),
      loc := Function.update C.loc p ((implGen μ q₀ add).invoke p (C.loc p) o) } := by
  simp [Impl.step, h0, implGen, ha]

lemma step_scanT (C : Cfg μ q₀) (p : P) (a b : Acct) (x : ℕ) (h0 : C.pend p ≠ none)
    (hpc : (C.loc p).pc = .scanT a b x) :
    (implGen μ q₀ add).step C (.tau p) = some { C with
      loc := Function.update C.loc p
        (if p ∈ μ a ∧ x ≤ balance q₀ a (C.mem ()) then ⟨(C.loc p).ops, .upd a b x⟩
          else ⟨(C.loc p).ops, .done (.inl false)⟩) } := by
  simp [Impl.step, h0, implGen, hpc, Mem, snapObj]
  congr 1

lemma step_upd (C : Cfg μ q₀) (p : P) (a b : Acct) (x : ℕ) (h0 : C.pend p ≠ none)
    (hpc : (C.loc p).pc = .upd a b x) :
    (implGen μ q₀ add).step C (.tau p) = some { C with
      mem := fun _ => Function.update (C.mem ()) p (add (C.loc p).ops (a, b, x)),
      loc := Function.update C.loc p ⟨add (C.loc p).ops (a, b, x), .done (.inl true)⟩ } := by
  simp only [Impl.step, h0, implGen, hpc, Mem, snapObj, ite_false]
  congr 2

lemma step_scanR (C : Cfg μ q₀) (p : P) (a : Acct) (h0 : C.pend p ≠ none)
    (hpc : (C.loc p).pc = .scanR a) :
    (implGen μ q₀ add).step C (.tau p) = some { C with
      loc := Function.update C.loc p ⟨(C.loc p).ops, .done (.inr (balance q₀ a (C.mem ())))⟩ } := by
  simp [Impl.step, h0, implGen, hpc, Mem, snapObj]
  congr 1

lemma step_ret_eq {C C' : Cfg μ q₀} {p : P} {r : Bool ⊕ ℕ}
    (h : (implGen μ q₀ add).step C (.ret p r) = some C')
    (hidle : (C.loc p).pc = .idle → C.pend p = none) :
    C.pend p ≠ none ∧ (C.loc p).pc = .done r ∧
      C' = { C with pend := Function.update C.pend p none,
                    loc := Function.update C.loc p ⟨(C.loc p).ops, .idle⟩ } := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  refine ⟨h0, ?_⟩
  cases hpc : (C.loc p).pc with
  | idle => exact absurd (hidle hpc) h0
  | scanT => simp [implGen, hpc] at hact
  | upd => simp [implGen, hpc] at hact
  | scanR => simp [implGen, hpc] at hact
  | done r' =>
    simp only [implGen, hpc] at hact
    obtain ⟨rfl, rfl⟩ := hact
    refine ⟨rfl, ?_⟩
    cases C'; simp_all

end Steps

/-! ## Flows -/

section Flows

variable {P Acct : Type} [Fintype P] [DecidableEq P] [DecidableEq Acct]

@[simp] lemma inAmt_nil (c : Acct) : inAmt c [] = 0 := rfl
@[simp] lemma outAmt_nil (c : Acct) : outAmt c [] = 0 := rfl

@[simp] lemma inAmt_append_singleton (c : Acct) (l : List (Tr Acct)) (t : Tr Acct) :
    inAmt c (l ++ [t]) = inAmt c l + if t.2.1 = c then t.2.2 else 0 := by
  simp [inAmt]

@[simp] lemma outAmt_append_singleton (c : Acct) (l : List (Tr Acct)) (t : Tr Acct) :
    outAmt c (l ++ [t]) = outAmt c l + if t.1 = c then t.2.2 else 0 := by
  simp [outAmt]

@[simp] lemma inflow_empty (c : Acct) : inflow c (fun _ : P => ([] : List (Tr Acct))) = 0 := by
  simp [inflow]

@[simp] lemma outflow_empty (c : Acct) : outflow c (fun _ : P => ([] : List (Tr Acct))) = 0 := by
  simp [outflow]

-- CSLib candidate (sum of a function over an updated argument)
lemma sum_update_eq {β : Type} (f : β → ℕ) (S : P → β) (p : P) (v : β) :
    ∑ q, f (Function.update S p v q) + f (S p) = ∑ q, f (S q) + f v := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  have : ∑ x ∈ Finset.univ.erase p, f (Function.update S p v x) = ∑ x ∈ Finset.univ.erase p, f (S x) :=
    Finset.sum_congr rfl fun q hq => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
  rw [this, Function.update_self]; ring

lemma inflow_update_append (c : Acct) (S : P → List (Tr Acct)) (p : P) (t : Tr Acct) :
    inflow c (Function.update S p (S p ++ [t])) = inflow c S + if t.2.1 = c then t.2.2 else 0 := by
  have := sum_update_eq (inAmt c) S p (S p ++ [t])
  simp only [inAmt_append_singleton] at this
  simp only [inflow]; omega

lemma outflow_update_append (c : Acct) (S : P → List (Tr Acct)) (p : P) (t : Tr Acct) :
    outflow c (Function.update S p (S p ++ [t])) = outflow c S + if t.1 = c then t.2.2 else 0 := by
  have := sum_update_eq (outAmt c) S p (S p ++ [t])
  simp only [outAmt_append_singleton] at this
  simp only [outflow]; omega

end Flows

end CryptoCons.Fig1
