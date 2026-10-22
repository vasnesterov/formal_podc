import Cslib.Computability.Distributed.SharedMemory.History
import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Lattice.Basic

/-!
# State-based CRDTs (Section II-B) and their sequential specification

* `CRDT`: a state-based CRDT `(S, Q, U)` (Definition 3): a join semilattice of payload states
  `S` with an initial state `s₀`, update commands `U` acting by inflationary maps
  (`s ⊑ u(s)`), and side-effect free query commands `Q` with results in `R`.
* `CRDT.Equiv`: query equivalence `s₁ ≡ s₂` (all queries return the same result).
* `CRDT.CausalHistory`: a causal-history map `C : S → Set U` with the axioms of Section II-B
  (`C(s₀) = ∅`, `C(u(s)) = C(s) ∪ {u}`, `C(s₁ ⊔ s₂) = C(s₁) ∪ C(s₂)`) and Shapiro et al.'s
  property `C(s₁) = C(s₂) ⇒ s₁ ≡ s₂` (`faithful`).
* `CRDT.spec`: the sequential specification of the CRDT as a CSLib `ObjSpec` (updates apply the
  command, queries return `cmd_q(s)`), used for linearizability.
* `gset U`: the grow-only set over update identifiers `U` (states `Finset U`, `u(s) = s ∪ {u}`,
  the only query returns the whole set); `C = id` is a causal history for it.
-/

-- CSLib candidate: Cslib/Computability/Distributed/CRDT/Basic.lean (state-based CRDTs, G-set)
namespace Podc.CRDTReplication

/-- A state-based CRDT (Definition 3 of the paper): payload states form a join semilattice with
an initial state `s₀`; update commands are inflationary; queries are functions of the state. -/
structure CRDT where
  /-- Payload states. -/
  S : Type
  [lat : SemilatticeSup S]
  [decEq : DecidableEq S]
  [decLe : DecidableRel (α := S) (· ≤ ·)]
  /-- The initial state `s₀`. -/
  s₀ : S
  /-- Update commands. -/
  U : Type
  /-- Query commands. -/
  Q : Type
  /-- Query results. -/
  R : Type
  /-- The effect of an update command. -/
  app : U → S → S
  /-- Updates are monotonically non-decreasing: `s ⊑ u(s)`. -/
  le_app : ∀ u s, s ≤ app u s
  /-- The result of a query command. -/
  query : Q → S → R

attribute [instance] CRDT.lat CRDT.decEq CRDT.decLe

namespace CRDT

variable (D : CRDT)

/-- Query equivalence `s₁ ≡ s₂`: all queries return the same result. -/
def Equiv (s t : D.S) : Prop := ∀ q, D.query q s = D.query q t

/-- A causal-history map for a CRDT (Section II-B): `C(s₀) = ∅`, `u ∈ C(u(s))` (we require the
precise `C(u(s)) = C(s) ∪ {u}`, which is what "the set of updates applied on `s₀` to reach `s`"
means), `C(s₁ ⊔ s₂) = C(s₁) ∪ C(s₂)`, and the property `C(s₁) = C(s₂) ⇒ s₁ ≡ s₂` that the paper
quotes from Shapiro et al. -/
structure CausalHistory where
  /-- The causal history of a state. -/
  C : D.S → Set D.U
  C_init : C D.s₀ = ∅
  C_app : ∀ u s, C (D.app u s) = insert u (C s)
  C_sup : ∀ s t, C (s ⊔ t) = C s ∪ C t
  faithful : ∀ s t, C s = C t → D.Equiv s t

namespace CausalHistory

variable {D} (H : D.CausalHistory)

/-- Causal histories grow with the state. -/
lemma C_mono {s t : D.S} (h : s ≤ t) : H.C s ⊆ H.C t := by
  have := H.C_sup s t
  rw [sup_eq_right.2 h] at this
  rw [this]; exact Set.subset_union_left

end CausalHistory

/-- Commands (operations of the replicated object). -/
inductive Cmd (D : CRDT) where
  /-- An update command. -/
  | upd (u : D.U)
  /-- A query command. -/
  | qry (q : D.Q)

/-- Responses: updates are acknowledged, queries return a result. -/
inductive Res (D : CRDT) where
  /-- Acknowledgment of an update (`UPDATE_DONE`). -/
  | done
  /-- Result of a query (`QUERY_DONE`). -/
  | val (r : D.R)

/-- The sequential specification of the CRDT as a CSLib object: an update applies its command,
a query returns `cmd_q(s)` and leaves the state unchanged. -/
abbrev spec : Cslib.SharedMemory.ObjSpec where
  State := D.S
  Op := Cmd D
  Resp := Res D
  init := D.s₀
  δ s o := match o with
    | .upd u => (D.app u s, .done)
    | .qry q => (s, .val (D.query q s))

end CRDT

/-! ## The grow-only set -/

/-- The grow-only set (G-set) over update identifiers `U`: states `Finset U` ordered by inclusion,
`s₀ = ∅`, the update `u` adds `u`, and the single query returns the whole set. -/
abbrev gset (U : Type) [DecidableEq U] : CRDT where
  S := Finset U
  s₀ := ∅
  U := U
  Q := Unit
  R := Finset U
  app u s := insert u s
  le_app u s := Finset.subset_insert u s
  query _ s := s

/-- For the G-set, the identity is a causal history. -/
def gsetHistory (U : Type) [DecidableEq U] : (gset U).CausalHistory where
  C s := ((s : Finset U) : Set U)
  C_init := by simp
  C_app u s := by simp
  C_sup s t := by simp
  faithful s t h := fun _ => by exact_mod_cast h

end Podc.CRDTReplication
