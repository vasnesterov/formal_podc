import Papers.PODC2019.CryptoConsensusNumber.Defs
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Model

/-!
# Figure 3: `k`-shared asset transfer from snapshot, registers and `k`-consensus (definitions)

Guerraoui et al., *The Consensus Number of a Cryptocurrency*, PODC 2019, Figure 3 (Lemma 2).

Processes are `Fin n` (process identifiers break ties in "the oldest transfer"). Base objects
(index type `Idx n Acct`):

* `.inl ()` — the atomic snapshot object `AS`; component `p` holds `hist_p`, a set of
  `(transfer tuple, result)` pairs;
* `.inr (.inl (a, i))` — the register `R_a[i]` (initially `⊥ = none`);
* `.inr (.inr (a, r))` — the `k`-consensus object `kC_a[r]`.

A transfer tuple is `(a, b, x, p, r)`: source, destination, amount, originator and the
originator's `round_a` when it invoked the transfer.

Code for process `p` (local variables `hist`, `committed_a`, `round_a`; local computation is
folded into the continuations of the base-object accesses, one access per atomic step):

```
transfer(a, b, x):
 1  if p ∉ μ(a) then return false
 3  tx = (a, b, x, p, round_a)
 4  R_a[p].write(tx)
 5  collected = collect(a) \ committed_a          -- n register reads, one per step
 6  while tx ∈ collected do
 7    req = the oldest transfer in collected
 8    prop = proposal(req, AS.snapshot())
 9    decision = kC_a[round_a].propose(prop)
10    hist = hist ∪ {decision}
11    AS.update(hist)
12    committed_a = committed_a ∪ {t : decision = (t, *)}
13    collected = collected \ committed_a
14    round_a = round_a + 1
15  return ((tx, success) ∈ hist)
read(a):
19  return balance(a, AS.snapshot())
```

Modelling choices (see the paper folder's `differencies.md`):

* line 22–23 of `collect` reads `R_a[i]` twice ("if `R_a[i].read() ≠ ⊥` then add
  `R_a[i].read()`"); we read it once (the second read is a typo-level redundancy);
* `kC.propose` returning `⊥` is never the case (proved from `KShared μ k`); in the code the
  `⊥` decision is simply ignored (`hist ∪ ∅`);
* `balance` uses truncated subtraction on `ℕ` (the invariant shows no truncation happens).
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig3

open Cslib.SharedMemory

set_option allowUnsafeReducibility true in
attribute [local reducible] atSpec snapObj kConsObj

/-- A transfer tuple `(a, b, x, p, r)`: source `a`, destination `b`, amount `x`, originator `p`
and the originator's round number `r` for account `a` at invocation. -/
structure Tx (n : ℕ) (Acct : Type) where
  a : Acct
  b : Acct
  x : ℕ
  p : Fin n
  r : ℕ
  deriving DecidableEq

/-- `hist`: a set of (transfer tuple, success flag) pairs. -/
abbrev Hist (n : ℕ) (Acct : Type) [DecidableEq Acct] := Finset (Tx n Acct × Bool)

variable {n : ℕ} {Acct : Type} [DecidableEq Acct]

/-- The age of a transfer tuple: its round, ties broken by the originator's identifier
(lexicographic order). "The oldest transfer" has the smallest key. -/
def Tx.key (t : Tx n Acct) : ℕ ×ₗ Fin n := toLex (t.r, t.p)

/-- Index type of the base objects. -/
abbrev Idx (n : ℕ) (Acct : Type) := Unit ⊕ (Acct × Fin n) ⊕ (Acct × ℕ)

/-- The base objects: snapshot `AS`, registers `R_a[i]`, `k`-consensus objects `kC_a[r]`. -/
@[reducible] def B (n : ℕ) (Acct : Type) [DecidableEq Acct] (k : ℕ) : Idx n Acct → ObjSpec
  | .inl _ => snapObj (Fin n) (Hist n Acct) ∅
  | .inr (.inl _) => register (Option (Tx n Acct)) none
  | .inr (.inr _) => kConsObj (Tx n Acct × Bool) k

/-- Program counter. -/
inductive PC (n : ℕ) (Acct : Type) where
  /-- No pending operation. -/
  | idle
  /-- About to return `r`. -/
  | ret (r : Bool ⊕ ℕ)
  /-- `read(a)`: about to take the snapshot (line 19). -/
  | rscan (a : Acct)
  /-- About to announce `tx` in `R_a[p]` (line 4). -/
  | write (tx : Tx n Acct)
  /-- Collecting (line 5): about to read `R_a[i]`; `acc` collected so far. -/
  | coll (tx : Tx n Acct) (i : Fin n) (acc : Finset (Tx n Acct))
  /-- Loop body (lines 7–8): about to take the snapshot; `c` = `collected`. -/
  | snap (tx : Tx n Acct) (c : Finset (Tx n Acct))
  /-- About to propose `pr` to `kC_a[round_a]` (line 9). -/
  | prop (tx : Tx n Acct) (c : Finset (Tx n Acct)) (pr : Tx n Acct × Bool)
  /-- About to `AS.update(hist)` (line 11); `d` is the decision. -/
  | upd (tx : Tx n Acct) (c : Finset (Tx n Acct)) (d : Option (Tx n Acct × Bool))

/-- Local state of a process. -/
structure Loc (n : ℕ) (Acct : Type) [DecidableEq Acct] where
  pc : PC n Acct
  hist : Hist n Acct
  /-- `committed_a`. -/
  com : Acct → Finset (Tx n Acct)
  /-- `round_a`. -/
  rnd : Acct → ℕ

/-! ## Balances -/

/-- The successful transfers recorded in a snapshot (`(tx, success) ∈ AS`). -/
def succ (S : Fin n → Hist n Acct) : Finset (Tx n Acct) :=
  ((Finset.univ.biUnion S).filter (fun d => d.2 = true)).image Prod.fst

/-- Total amount of the transfers of `T` into `a`. -/
def inSum (a : Acct) (T : Finset (Tx n Acct)) : ℕ := ∑ t ∈ T.filter (fun t => t.b = a), t.x

/-- Total amount of the transfers of `T` out of `a`. -/
def outSum (a : Acct) (T : Finset (Tx n Acct)) : ℕ := ∑ t ∈ T.filter (fun t => t.a = a), t.x

/-- `balance(a, snapshot)` (lines 30–32). -/
def balance (q₀ : Acct → ℕ) (a : Acct) (S : Fin n → Hist n Acct) : ℕ :=
  q₀ a + inSum a (succ S) - outSum a (succ S)

/-- `proposal(t, snapshot)` (lines 25–29): success iff the source has enough balance. -/
def proposal (q₀ : Acct → ℕ) (t : Tx n Acct) (S : Fin n → Hist n Acct) : Tx n Acct × Bool :=
  (t, decide (t.x ≤ balance q₀ t.a S))

/-- The oldest transfer of `c` (smallest `key`); `dflt` if `c` is empty. -/
noncomputable def oldest (c : Finset (Tx n Acct)) (dflt : Tx n Acct) : Tx n Acct :=
  if h : c.Nonempty then Classical.choose (c.exists_min_image Tx.key h) else dflt

lemma oldest_spec {c : Finset (Tx n Acct)} (h : c.Nonempty) (dflt : Tx n Acct) :
    oldest c dflt ∈ c ∧ ∀ t ∈ c, (oldest c dflt).key ≤ t.key := by
  simp only [oldest, h, dite_true]
  exact Classical.choose_spec (c.exists_min_image Tx.key h)

/-- The loop test (line 6), and the return value (lines 15–18) when the loop is left. -/
def loopCheck (tx : Tx n Acct) (c : Finset (Tx n Acct)) (h : Hist n Acct) : PC n Acct :=
  if tx ∈ c then .snap tx c else .ret (.inl (decide ((tx, true) ∈ h)))

/-! ## The implementation -/

variable (μ : Acct → Finset (Fin n)) (q₀ : Acct → ℕ) (k : ℕ)

/-- Processes invoke transfers only under their own identity. -/
def allowedOp (p : Fin n) : ATOp (Fin n) Acct → Prop
  | .transfer p' _ _ _ => p' = p
  | .read _ => True

/-- The initial memory. -/
def memInit : (i : Idx n Acct) → (B n Acct k i).State
  | .inl _ => fun _ => (∅ : Hist n Acct)
  | .inr (.inl _) => (none : Option (Tx n Acct))
  | .inr (.inr _) => ((none, 0) : Option (Tx n Acct × Bool) × ℕ)

/-- **Figure 3.** -/
noncomputable def impl : Impl (atSpec (Fin n) Acct μ q₀) (B n Acct k) (Fin n) (Loc n Acct) where
  memInit := memInit k
  locInit _ := ⟨.idle, ∅, fun _ => ∅, fun _ => 0⟩
  invoke p l o := match o with
    | .read a => { l with pc := .rscan a }
    | .transfer _ a b x =>
      if p ∈ μ a then { l with pc := .write ⟨a, b, x, p, l.rnd a⟩ }
      else { l with pc := .ret (.inl false) }
  act p l := match l.pc with
    | .idle => .ret (.inl false) l
    | .ret r => .ret r { l with pc := .idle }
    | .rscan a => .access (.inl ()) SnapOp.scan (fun S =>
        { l with pc := .ret (.inr (balance q₀ a (Option.getD S fun _ => ∅))) })
    | .write tx => .access (.inr (.inl (tx.a, p))) (RWOp.write (some tx)) (fun _ =>
        { l with pc := .coll tx ⟨0, p.pos⟩ ∅ })
    | .coll tx i acc => .access (.inr (.inl (tx.a, i))) RWOp.read (fun v =>
        if h : i.val + 1 < n then { l with pc := .coll tx ⟨i.val + 1, h⟩ (acc ∪ Option.toFinset v) }
        else { l with pc := loopCheck tx ((acc ∪ Option.toFinset v) \ l.com tx.a) l.hist })
    | .snap tx c => .access (.inl ()) SnapOp.scan (fun S =>
        { l with pc := .prop tx c (proposal q₀ (oldest c tx) (Option.getD S fun _ => ∅)) })
    | .prop tx c pr => .access (.inr (.inr (tx.a, l.rnd tx.a))) pr (fun d =>
        { l with pc := .upd tx c d, hist := l.hist ∪ Option.toFinset d })
    | .upd tx c d => .access (.inl ()) (SnapOp.update p l.hist) (fun _ =>
        { l with
          pc := loopCheck tx (c \ (l.com tx.a ∪ Option.toFinset (Option.map Prod.fst d))) l.hist
          com := Function.update l.com tx.a (l.com tx.a ∪ Option.toFinset (Option.map Prod.fst d))
          rnd := Function.update l.rnd tx.a (l.rnd tx.a + 1) })
  allowed := allowedOp

/-! ## Memory accessors -/

/-- Memory states. -/
abbrev Mem (n : ℕ) (Acct : Type) [DecidableEq Acct] (k : ℕ) := (i : Idx n Acct) → (B n Acct k i).State

/-- Configurations. -/
abbrev Cfg := Config (atSpec (Fin n) Acct μ q₀) (B n Acct k) (Fin n) (Loc n Acct)

variable {μ q₀ k}

/-- The snapshot object. -/
def AS (m : Mem n Acct k) : Fin n → Hist n Acct := m (.inl ())

/-- The register `R_a[i]`. -/
def Reg (m : Mem n Acct k) (a : Acct) (i : Fin n) : Option (Tx n Acct) := m (.inr (.inl (a, i)))

/-- The `k`-consensus object `kC_a[r]` (first proposal, number of invocations). -/
def KC (m : Mem n Acct k) (a : Acct) (r : ℕ) : Option (Tx n Acct × Bool) × ℕ :=
  m (.inr (.inr (a, r)))

/-- The decision of `kC_a[r]` (if any). -/
def Dec (m : Mem n Acct k) (a : Acct) (r : ℕ) : Option (Tx n Acct × Bool) := (KC m a r).1

/-- The successful transfers recorded in `AS`. -/
def U (m : Mem n Acct k) : Finset (Tx n Acct) := succ (AS m)

/-! ## Step lemmas -/

section Steps

variable {C : Cfg μ q₀ k} {q : Fin n}

lemma step_inv_eq (o : ATOp (Fin n) Acct) (h0 : C.pend q = none) (ha : allowedOp q o) :
    (impl μ q₀ k).step C (.inv q o) = some { C with
      pend := Function.update C.pend q (some o),
      loc := Function.update C.loc q ((impl μ q₀ k).invoke q (C.loc q) o) } := by
  simp [Impl.step, h0, impl, ha]

lemma step_rscan (a : Acct) (h0 : C.pend q ≠ none) (hpc : (C.loc q).pc = .rscan a) :
    (impl μ q₀ k).step C (.tau q) = some { C with
      loc := Function.update C.loc q
        { C.loc q with pc := .ret (.inr (balance q₀ a (AS C.mem))) } } := by
  simp [Impl.step, h0, impl, hpc, AS]

lemma step_write (tx : Tx n Acct) (h0 : C.pend q ≠ none) (hpc : (C.loc q).pc = .write tx) :
    (impl μ q₀ k).step C (.tau q) = some { C with
      mem := Function.update C.mem (.inr (.inl (tx.a, q))) (some tx : Option (Tx n Acct)),
      loc := Function.update C.loc q { C.loc q with pc := .coll tx ⟨0, q.pos⟩ ∅ } } := by
  simp [Impl.step, h0, impl, hpc]

lemma step_coll (tx : Tx n Acct) (i : Fin n) (acc : Finset (Tx n Acct)) (h0 : C.pend q ≠ none)
    (hpc : (C.loc q).pc = .coll tx i acc) :
    (impl μ q₀ k).step C (.tau q) = some { C with
      loc := Function.update C.loc q
        (if h : i.val + 1 < n then
          { C.loc q with pc := .coll tx ⟨i.val + 1, h⟩ (acc ∪ Option.toFinset (Reg C.mem tx.a i)) }
        else { C.loc q with pc := loopCheck tx ((acc ∪ Option.toFinset (Reg C.mem tx.a i)) \
          (C.loc q).com tx.a) (C.loc q).hist }) } := by
  simp [Impl.step, h0, impl, hpc, Reg]

lemma step_snap (tx : Tx n Acct) (c : Finset (Tx n Acct)) (h0 : C.pend q ≠ none)
    (hpc : (C.loc q).pc = .snap tx c) :
    (impl μ q₀ k).step C (.tau q) = some { C with
      loc := Function.update C.loc q
        { C.loc q with pc := .prop tx c (proposal q₀ (oldest c tx) (AS C.mem)) } } := by
  simp [Impl.step, h0, impl, hpc, AS]

lemma step_prop (tx : Tx n Acct) (c : Finset (Tx n Acct)) (pr : Tx n Acct × Bool)
    (h0 : C.pend q ≠ none) (hpc : (C.loc q).pc = .prop tx c pr) :
    (impl μ q₀ k).step C (.tau q) = some { C with
      mem := Function.update C.mem (.inr (.inr (tx.a, (C.loc q).rnd tx.a)))
        (((some ((Dec C.mem tx.a ((C.loc q).rnd tx.a)).getD pr),
          (KC C.mem tx.a ((C.loc q).rnd tx.a)).2 + 1)) : Option (Tx n Acct × Bool) × ℕ),
      loc := Function.update C.loc q
        (let d := if (KC C.mem tx.a ((C.loc q).rnd tx.a)).2 < k then
            some ((Dec C.mem tx.a ((C.loc q).rnd tx.a)).getD pr) else none
         { C.loc q with pc := .upd tx c d, hist := (C.loc q).hist ∪ Option.toFinset d }) } := by
  by_cases hk : (KC C.mem tx.a ((C.loc q).rnd tx.a)).2 < k
  · simp only [KC] at hk
    simp [Impl.step, h0, impl, hpc, Dec, KC, hk]
  · simp only [KC] at hk
    simp [Impl.step, h0, impl, hpc, Dec, KC, hk]

lemma step_upd (tx : Tx n Acct) (c : Finset (Tx n Acct)) (d : Option (Tx n Acct × Bool))
    (h0 : C.pend q ≠ none) (hpc : (C.loc q).pc = .upd tx c d) :
    (impl μ q₀ k).step C (.tau q) = some { C with
      mem := Function.update C.mem (.inl ()) (Function.update (AS C.mem) q (C.loc q).hist),
      loc := Function.update C.loc q
        { C.loc q with
          pc := loopCheck tx (c \ ((C.loc q).com tx.a ∪ Option.toFinset (Option.map Prod.fst d)))
            (C.loc q).hist
          com := Function.update (C.loc q).com tx.a
            ((C.loc q).com tx.a ∪ Option.toFinset (Option.map Prod.fst d))
          rnd := Function.update (C.loc q).rnd tx.a ((C.loc q).rnd tx.a + 1) } } := by
  simp only [Impl.step, h0, impl, hpc, ite_false, AS]

lemma step_ret_eq {C' : Cfg μ q₀ k} {r : Bool ⊕ ℕ}
    (h : (impl μ q₀ k).step C (.ret q r) = some C')
    (hidle : (C.loc q).pc = .idle → C.pend q = none) :
    C.pend q ≠ none ∧ (C.loc q).pc = .ret r ∧
      C' = { C with pend := Function.update C.pend q none,
                    loc := Function.update C.loc q { C.loc q with pc := .idle } } := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  refine ⟨h0, ?_⟩
  cases hpc : (C.loc q).pc with
  | idle => exact absurd (hidle hpc) h0
  | ret r' =>
    simp only [impl, hpc] at hact
    obtain ⟨rfl, rfl⟩ := hact
    refine ⟨rfl, ?_⟩
    cases C'; simp_all
  | _ => simp [impl, hpc] at hact

/-- A `tau` step is not enabled when the process is about to return or idle. -/
lemma step_tau_ret_none (r : Bool ⊕ ℕ) (hpc : (C.loc q).pc = .ret r) :
    (impl μ q₀ k).step C (.tau q) = none := by
  simp [Impl.step, impl, hpc]

lemma step_tau_idle_none (hpc : (C.loc q).pc = .idle) :
    (impl μ q₀ k).step C (.tau q) = none := by
  simp [Impl.step, impl, hpc]

end Steps

/-! ## Accessor lemmas -/

section Access

variable {m : Mem n Acct k}

@[simp] lemma AS_update_AS (v : Fin n → Hist n Acct) :
    AS (Function.update m (.inl ()) v) = v := by
  simp [AS]

@[simp] lemma AS_update_inr (j : (Acct × Fin n) ⊕ (Acct × ℕ)) (v : (B n Acct k (.inr j)).State) :
    AS (Function.update m (.inr j) v) = AS m := by
  simp [AS]

@[simp] lemma Reg_update_AS (v : Fin n → Hist n Acct) (a : Acct) (i : Fin n) :
    Reg (Function.update m (.inl ()) v) a i = Reg m a i := by
  simp [Reg]

@[simp] lemma Reg_update_KC (j : Acct × ℕ) (v : (B n Acct k (.inr (.inr j))).State) (a : Acct)
    (i : Fin n) : Reg (Function.update m (.inr (.inr j)) v) a i = Reg m a i := by
  simp [Reg]

lemma Reg_update_Reg (j : Acct × Fin n) (v : Option (Tx n Acct)) (a : Acct) (i : Fin n) :
    Reg (Function.update m (.inr (.inl j)) v) a i = if (a, i) = j then v else Reg m a i := by
  by_cases h : (a, i) = j
  · subst h; simp [Reg]
  · simp only [Reg, h, ite_false]
    rw [Function.update_of_ne]
    intro h'; simp at h'; exact h h'

@[simp] lemma KC_update_AS (v : Fin n → Hist n Acct) (a : Acct) (r : ℕ) :
    KC (Function.update m (.inl ()) v) a r = KC m a r := by
  simp [KC]

@[simp] lemma KC_update_Reg (j : Acct × Fin n) (v : Option (Tx n Acct)) (a : Acct) (r : ℕ) :
    KC (Function.update m (.inr (.inl j)) v) a r = KC m a r := by
  simp [KC]

lemma KC_update_KC (j : Acct × ℕ) (v : Option (Tx n Acct × Bool) × ℕ) (a : Acct) (r : ℕ) :
    KC (Function.update m (.inr (.inr j)) v) a r = if (a, r) = j then v else KC m a r := by
  by_cases h : (a, r) = j
  · subst h; simp [KC]
  · simp only [KC, h, ite_false]
    rw [Function.update_of_ne]
    intro h'; simp at h'; exact h h'

@[simp] lemma Dec_update_AS (v : Fin n → Hist n Acct) (a : Acct) (r : ℕ) :
    Dec (Function.update m (.inl ()) v) a r = Dec m a r := by
  simp [Dec]

@[simp] lemma Dec_update_Reg (j : Acct × Fin n) (v : Option (Tx n Acct)) (a : Acct) (r : ℕ) :
    Dec (Function.update m (.inr (.inl j)) v) a r = Dec m a r := by
  simp [Dec]

@[simp] lemma U_update_Reg (j : Acct × Fin n) (v : Option (Tx n Acct)) :
    U (Function.update m (.inr (.inl j)) v) = U m := by
  simp [U]

@[simp] lemma U_update_KC (j : Acct × ℕ) (v : Option (Tx n Acct × Bool) × ℕ) :
    U (Function.update m (.inr (.inr j)) v) = U m := by
  simp [U]

end Access

end CryptoCons.Fig3
