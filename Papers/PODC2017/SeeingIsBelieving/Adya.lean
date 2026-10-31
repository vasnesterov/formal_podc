import Papers.PODC2017.SeeingIsBelieving.Model

/-!
# Adya's dependency-graph definitions of isolation

Adya, *Weak consistency: a generalized theory and optimistic implementations for distributed
transactions*, PhD thesis, MIT, 1999 (reference [2] of the paper), restricted to the key-value
setting of the paper (item reads and writes, no predicates).

A history consists of the transactions (`TxnSet`, with committed and aborted transactions), a
*version order* (for every key, a total order on the versions installed by committed
transactions; the initial version comes first) and, for snapshot isolation, *start and commit
timestamps* of the committed transactions. The direct serialization graph `DSG(H)` has the
committed transactions as nodes and

* write-dependency edges `Ti →ww Tj`: `Tj` installs the version of some key right after `Ti`'s;
* read-dependency edges `Ti →wr Tj`: `Tj` reads a version installed by `Ti`;
* anti-dependency edges `Ti →rw Tj`: `Ti` reads a version of some key and `Tj` installs the next
  version of that key;

all between distinct transactions. The start-ordered serialization graph `SSG(H)` adds
start-dependency edges `Ti →sd Tj` when `Ti` commits before `Tj` starts.

-- CSLib candidate (together with `Model.lean`): a transactional key-value history model.
-/

namespace Podc.SeeingIsBelieving

open Relation

variable {K ι : Type*} [DecidableEq K] [DecidableEq ι]

/-- A version order of the history: for every key `k`, a strict total order `lt k` on the
committed transactions writing `k` (`lt k X Y`: `x_X ≪ x_Y`). -/
structure VersionOrder (H : TxnSet K ι) where
  /-- `lt k X Y`: the version of `k` installed by `X` precedes the one installed by `Y`. -/
  lt : K → ι → ι → Prop
  dom : ∀ {k X Y}, lt k X Y → X ∈ H.committed ∧ Y ∈ H.committed ∧ H.Writes X k ∧ H.Writes Y k
  irrefl : ∀ k X, ¬ lt k X X
  trans : ∀ {k X Y Z}, lt k X Y → lt k Y Z → lt k X Z
  total : ∀ {k X Y}, X ∈ H.committed → Y ∈ H.committed → H.Writes X k → H.Writes Y k → X ≠ Y →
    lt k X Y ∨ lt k Y X

/-- Start and commit timestamps of the committed transactions, with values in a linear order
`τ`: distinct, and every transaction starts before it commits. -/
structure Timestamps (H : TxnSet K ι) (τ : Type*) [LinearOrder τ] where
  /-- start timestamp -/
  start : ι → τ
  /-- commit timestamp -/
  commit : ι → τ
  start_lt_commit : ∀ T ∈ H.committed, start T < commit T
  start_inj : ∀ T ∈ H.committed, ∀ T' ∈ H.committed, start T = start T' → T = T'
  commit_inj : ∀ T ∈ H.committed, ∀ T' ∈ H.committed, commit T = commit T' → T = T'
  start_ne_commit : ∀ T ∈ H.committed, ∀ T' ∈ H.committed, start T ≠ commit T'

namespace TxnSet

variable (H : TxnSet K ι)

/-- Read-dependency edge `X →wr Y`: `Y` reads the version of some key installed by `X`. -/
def WR (X Y : ι) : Prop :=
  X ∈ H.committed ∧ Y ∈ H.committed ∧ X ≠ Y ∧ ∃ k, H.Writes X k ∧ Op.read k (some X) ∈ H.ops Y

/-- **G1a (aborted reads).** A committed transaction reads a version written by an aborted
transaction. -/
def G1a : Prop := ∃ T ∈ H.committed, ∃ k X, Op.read k (some X) ∈ H.ops T ∧ X ∉ H.committed

/-- Start-dependency edge `X →sd Y`: `X` commits before `Y` starts. -/
def SD {τ : Type*} [LinearOrder τ] (ts : Timestamps H τ) (X Y : ι) : Prop :=
  X ∈ H.committed ∧ Y ∈ H.committed ∧ ts.commit X < ts.start Y

end TxnSet

namespace VersionOrder

variable {H : TxnSet K ι} (vo : VersionOrder H)

/-- `Y` installs the version of `k` that immediately follows `X`'s. -/
def IsNext (k : K) (X Y : ι) : Prop := vo.lt k X Y ∧ ∀ Z, ¬ (vo.lt k X Z ∧ vo.lt k Z Y)

/-- `Y` installs the first committed version of `k` (the one following the initial version). -/
def IsFirst (k : K) (Y : ι) : Prop := Y ∈ H.committed ∧ H.Writes Y k ∧ ∀ Z, ¬ vo.lt k Z Y

/-- `Y` installs the version of `k` following version `v` (`none` = the initial version). -/
def IsNextAfter (k : K) : Option ι → ι → Prop
  | none, Y => vo.IsFirst k Y
  | some X, Y => vo.IsNext k X Y

/-- Write-dependency edge `X →ww Y`. -/
def WW (X Y : ι) : Prop := ∃ k, vo.IsNext k X Y

/-- Anti-dependency edge `X →rw Y`: `X` reads a version of `k`, `Y` installs the next one. -/
def RW (X Y : ι) : Prop :=
  X ∈ H.committed ∧ X ≠ Y ∧ ∃ k v, Op.read k v ∈ H.ops X ∧ vo.IsNextAfter k v Y

/-- Dependency edges `ww ∪ wr`. -/
def Dep (X Y : ι) : Prop := vo.WW X Y ∨ H.WR X Y

/-- All edges of `DSG(H)`: `ww ∪ wr ∪ rw`. -/
def DSG (X Y : ι) : Prop := vo.Dep X Y ∨ vo.RW X Y

/-- **G0 (write cycles).** `DSG(H)` has a cycle of write-dependency edges. -/
def G0 : Prop := ∃ X, TransGen vo.WW X X

/-- **G1c (circular information flow).** `DSG(H)` has a cycle of dependency edges. -/
def G1c : Prop := ∃ X, TransGen vo.Dep X X

/-- **G1** = G1a ∨ G1b ∨ G1c. Phenomenon G1b (intermediate reads) cannot occur: every
transaction writes a key at most once (an assumption of the paper), so every version is final. -/
def G1 : Prop := H.G1a ∨ vo.G1c

/-- **G2 (anti-dependency cycles).** `DSG(H)` has a cycle with at least one anti-dependency edge. -/
def G2 : Prop := ∃ X Y, vo.RW X Y ∧ ReflTransGen vo.DSG Y X

/-- **G-single.** `DSG(H)` has a cycle with exactly one anti-dependency edge. -/
def GSingle : Prop := ∃ X Y, vo.RW X Y ∧ ReflTransGen vo.Dep Y X

variable {τ : Type*} [LinearOrder τ] (ts : Timestamps H τ)

/-- **G-SIa (interference).** `SSG(H)` has a write- or read-dependency edge `X → Y` without a
start-dependency edge `X →sd Y`. -/
def GSIa : Prop := ∃ X Y, vo.Dep X Y ∧ ¬ H.SD ts X Y

/-- Edges of `SSG(H)` other than anti-dependencies: `ww ∪ wr ∪ sd`. -/
def SSGDep (X Y : ι) : Prop := vo.Dep X Y ∨ H.SD ts X Y

/-- **G-SIb (missed effects).** `SSG(H)` has a cycle with exactly one anti-dependency edge. -/
def GSIb : Prop := ∃ X Y, vo.RW X Y ∧ ReflTransGen (vo.SSGDep ts) Y X

end VersionOrder

end Podc.SeeingIsBelieving
