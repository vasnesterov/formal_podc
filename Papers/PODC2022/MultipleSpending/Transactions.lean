import Mathlib

/-!
# Transactions, well-formed histories, balances, spending number (§4.1)

Transactions are an abstract type `Tx` with an issuer (`none` = the system originator `⊥`, used
by `tx_init` only), an output map `τ` and a finite set of input transactions. The paper's
transactions are tuples `(s, τ, I)`, so two transactions with equal fields are equal; we do not
need (nor assume) this.

* `TxSystem.WellFormed T`: T-Validity, Completeness, No-Conflict, Cycle-Freedom.
* `theorem_4_1`: balances in a well-formed history are nonnegative.
* `spendSet Γ r tx` (`I^r_tx`) and `spendingNumber Γ` (Definition 4.2, valued in `ℕ∞`).
-/

namespace Podc.MultipleSpending

open Finset

/-- A universe of transactions over processes `P`. -/
structure TxSystem (P Tx : Type*) where
  /-- The issuer `tx.s` (`none` is the system originator `⊥`). -/
  issuer : Tx → Option P
  /-- The output map `tx.τ`. -/
  out : Tx → P → ℕ
  /-- The input transactions `tx.I`. -/
  inputs : Tx → Finset Tx
  /-- The initial transaction `tx_init = (⊥, τ_init, ∅)`. -/
  init : Tx
  issuer_init : issuer init = none
  inputs_init : inputs init = ∅

namespace TxSystem

variable {P Tx : Type*} [Fintype P] [DecidableEq Tx] (X : TxSystem P Tx)

/-- `outValue tx = ∑_p tx.τ(p)`. -/
def outValue (tx : Tx) : ℕ := ∑ p, X.out tx p

/-- `inValue tx = ∑_{tx' ∈ tx.I} tx'.τ(tx.s)` (zero for the originator). -/
def inValue (tx : Tx) : ℕ :=
  match X.issuer tx with
  | some s => ∑ tx' ∈ X.inputs tx, X.out tx' s
  | none => 0

/-- A transaction is valid iff it spends a positive amount equal to the value of its inputs. -/
def Valid (tx : Tx) : Prop := 0 < X.outValue tx ∧ X.outValue tx = X.inValue tx

/-- Two distinct transactions conflict if they have the same issuer and share an input. -/
def Conflict (tx tx' : Tx) : Prop :=
  tx ≠ tx' ∧ X.issuer tx = X.issuer tx' ∧ ¬ Disjoint (X.inputs tx) (X.inputs tx')

/-- `tx` depends on `tx'`: there is a (nonempty) path from `tx'` to `tx` along input edges. -/
def DependsOn (tx tx' : Tx) : Prop := Relation.TransGen (fun a b => a ∈ X.inputs b) tx' tx

/-- A well-formed transaction history. -/
structure WellFormed (T : Finset Tx) : Prop where
  init_mem : X.init ∈ T
  valid : ∀ tx ∈ T, tx ≠ X.init → X.Valid tx
  complete : ∀ tx ∈ T, X.inputs tx ⊆ T
  noConflict : ∀ tx ∈ T, ∀ tx' ∈ T, ¬ X.Conflict tx tx'
  cycleFree : ∀ tx ∈ T, ∀ tx' ∈ T, X.DependsOn tx tx' → tx ∉ X.inputs tx'

/-- `balance_T(w)`: incoming minus outgoing stake of `w` in `T`. -/
def balance [DecidableEq P] (T : Finset Tx) (w : P) : ℤ :=
  (∑ tx ∈ T, (X.out tx w : ℤ)) - ∑ tx ∈ T.filter (fun tx => X.issuer tx = some w), (X.outValue tx : ℤ)

/-- **Theorem 4.1**: in a well-formed history every balance is nonnegative. (Cycle-Freedom is not
needed.) -/
theorem theorem_4_1 [DecidableEq P] {T : Finset Tx} (hT : X.WellFormed T) (w : P) :
    0 ≤ X.balance T w := by
  set Tw := T.filter (fun tx => X.issuer tx = some w) with hTw
  -- outgoing stake = value of the inputs of `w`'s transactions
  have h1 : ∑ tx ∈ Tw, X.outValue tx = ∑ tx ∈ Tw, ∑ tx' ∈ X.inputs tx, X.out tx' w := by
    apply Finset.sum_congr rfl
    intro tx htx
    rw [Finset.mem_filter] at htx
    have hne : tx ≠ X.init := fun h => by
      have := htx.2; rw [h, X.issuer_init] at this; simp at this
    rw [(hT.valid tx htx.1 hne).2, inValue, htx.2]
  -- the inputs of distinct transactions of `w` are disjoint (No-Conflict)
  have hdisj : (Tw : Set Tx).PairwiseDisjoint X.inputs := by
    intro a ha b hb hab
    simp only [hTw, Finset.coe_filter] at ha hb
    by_contra hc
    exact hT.noConflict a ha.1 b hb.1 ⟨hab, ha.2.trans hb.2.symm, hc⟩
  have h2 : ∑ tx ∈ Tw, ∑ tx' ∈ X.inputs tx, X.out tx' w =
      ∑ tx' ∈ Tw.biUnion X.inputs, X.out tx' w := (Finset.sum_biUnion hdisj).symm
  -- and they belong to `T` (Completeness)
  have hsub : Tw.biUnion X.inputs ⊆ T := by
    intro x hx
    obtain ⟨tx, htx, hx⟩ := Finset.mem_biUnion.mp hx
    exact hT.complete tx (Finset.mem_filter.mp htx).1 hx
  have h3 : ∑ tx' ∈ Tw.biUnion X.inputs, X.out tx' w ≤ ∑ tx ∈ T, X.out tx w :=
    Finset.sum_le_sum_of_subset hsub
  have h4 : ∑ tx ∈ Tw, X.outValue tx ≤ ∑ tx ∈ T, X.out tx w := by
    rw [h1, h2]; exact h3
  unfold balance
  rw [← hTw]
  have : ((∑ tx ∈ Tw, X.outValue tx : ℕ) : ℤ) ≤ ((∑ tx ∈ T, X.out tx w : ℕ) : ℤ) := by
    exact_mod_cast h4
  push_cast at this
  linarith

/-- `I^r_tx`: the transactions issued by `r` with input `tx` that appear in some history of
`Γ`. -/
def spendSet (Γ : Set (Finset Tx)) (r : P) (tx : Tx) : Set Tx :=
  {tx' | (∃ T ∈ Γ, tx' ∈ T) ∧ tx ∈ X.inputs tx' ∧ X.issuer tx' = some r}

/-- **Definition 4.2** (spending number): the largest `|I^r_tx|` over processes `r` and
transactions `tx` incoming to `r`. Valued in `ℕ∞`. -/
noncomputable def spendingNumber (Γ : Set (Finset Tx)) : ℕ∞ :=
  sSup {k | ∃ r tx, 0 < X.out tx r ∧ (X.spendSet Γ r tx).encard = k}

omit [Fintype P] [DecidableEq Tx] in
theorem spendingNumber_le_iff {Γ : Set (Finset Tx)} {k : ℕ∞} :
    X.spendingNumber Γ ≤ k ↔ ∀ r tx, 0 < X.out tx r → (X.spendSet Γ r tx).encard ≤ k := by
  unfold spendingNumber
  rw [sSup_le_iff]
  constructor
  · intro h r tx hin; exact h _ ⟨r, tx, hin, rfl⟩
  · rintro h _ ⟨r, tx, hin, rfl⟩; exact h r tx hin

end TxSystem

end Podc.MultipleSpending
