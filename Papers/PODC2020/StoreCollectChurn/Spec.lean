import Mathlib

/-!
# The store-collect specification (Section 2 of the paper)

A *schedule* is a sequence of invocations and responses of `STORE_p(v)` / `COLLECT_p` operations.
An operation is identified by the position `i` of its invocation; its response is the next event of
the same client (`Next σ i j`).  A *view* is a partial function `P → Option V` (a set of
client-value pairs without repetition of client ids).

`Regular σ` is the paper's "regularity for the store-collect problem":

1. for each collect `cop` returning `V` and every client `p`: if `V p = ⊥` then no store by `p`
   precedes `cop`; if `V p = v` then some `STORE_p(v)` is invoked before `cop` completes and no other
   store operation by `p` occurs (invocation and response) between this invocation and the
   invocation of `cop`;
2. if a collect returning `V₁` precedes a collect returning `V₂` then `V₁ ⪯ V₂`, where `V₁ ⪯ V₂`
   means: for every `⟨p, v₁⟩ ∈ V₁` there is `⟨p, v₂⟩ ∈ V₂` with `v₁ = v₂` or the invocation of
   `STORE_p(v₁)` does not occur after the response of `STORE_p(v₂)`.
-/

namespace Podc.StoreCollectChurn

/-- Events of a store-collect schedule. -/
inductive SCEv (P V : Type) where
  /-- Invocation `STORE_p(v)`. -/
  | stInv (p : P) (v : V)
  /-- Response `ACK_p`. -/
  | ack (p : P)
  /-- Invocation `COLLECT_p`. -/
  | colInv (p : P)
  /-- Response `RETURN_p(V)`. -/
  | ret (p : P) (W : P → Option V)

namespace SCEv

variable {P V : Type}

/-- The client of an event. -/
def proc : SCEv P V → P
  | stInv p _ => p
  | ack p => p
  | colInv p => p
  | ret p _ => p

/-- Invocations. -/
def IsInv : SCEv P V → Prop
  | stInv _ _ => True
  | colInv _ => True
  | _ => False

end SCEv

variable {P V : Type}

/-- `j` is the position of the next event of the client of the event at position `i`
(the response matching an invocation at `i`, in a well-formed schedule). -/
def Next (σ : List (SCEv P V)) (i j : ℕ) : Prop :=
  i < j ∧ ∃ e e', σ[i]? = some e ∧ σ[j]? = some e' ∧ e'.proc = e.proc ∧
    ∀ k, i < k → k < j → ∀ e'', σ[k]? = some e'' → e''.proc ≠ e.proc

/-- Well-formed schedule: for each client, its events alternate between invocations and matching
responses, beginning with an invocation (`ACK` answers `STORE`, `RETURN` answers `COLLECT`). -/
def WellFormed (σ : List (SCEv P V)) : Prop :=
  ∀ i e, σ[i]? = some e →
    (¬ e.IsInv → ∃ i', Next σ i' i ∧
        ((∃ v, σ[i']? = some (.stInv e.proc v) ∧ e = .ack e.proc) ∨
         (σ[i']? = some (.colInv e.proc) ∧ ∃ W, e = .ret e.proc W))) ∧
    (e.IsInv → ∀ j, Next σ i j → ∀ e', σ[j]? = some e' → ¬ e'.IsInv)

/-- `STORE_p(v)` is invoked at position `a`. -/
def StoreAt (σ : List (SCEv P V)) (a : ℕ) (p : P) (v : V) : Prop :=
  σ[a]? = some (.stInv p v)

/-- A collect by some client, invoked at `i`, returning `W` at `j`. -/
def CollectOp (σ : List (SCEv P V)) (i j : ℕ) (W : P → Option V) : Prop :=
  ∃ p, σ[i]? = some (.colInv p) ∧ σ[j]? = some (.ret p W) ∧ Next σ i j

/-- A store by `p` invoked at `a` and completed at `b` (its matching response). -/
def StoreDone (σ : List (SCEv P V)) (a b : ℕ) (p : P) : Prop :=
  (∃ v, StoreAt σ a p v) ∧ Next σ a b

/-- The order `V₁ ⪯ V₂` on views of a schedule `σ` (Section 2). -/
def ViewLE (σ : List (SCEv P V)) (V₁ V₂ : P → Option V) : Prop :=
  ∀ p v₁, V₁ p = some v₁ → ∃ v₂, V₂ p = some v₂ ∧
    (v₁ = v₂ ∨ ¬ ∃ a b k, StoreAt σ a p v₂ ∧ Next σ a b ∧ b < k ∧ StoreAt σ k p v₁)

/-- Regularity for the store-collect problem (Section 2). -/
def Regular (σ : List (SCEv P V)) : Prop :=
  (∀ i j W, CollectOp σ i j W → ∀ p,
      (W p = none → ¬ ∃ a b, StoreDone σ a b p ∧ b < i) ∧
      (∀ v, W p = some v → ∃ a, a < j ∧ StoreAt σ a p v ∧
          ¬ ∃ a' b', a < a' ∧ StoreDone σ a' b' p ∧ b' < i)) ∧
  (∀ i₁ j₁ W₁ i₂ j₂ W₂, CollectOp σ i₁ j₁ W₁ → CollectOp σ i₂ j₂ W₂ → j₁ < i₂ →
      ViewLE σ W₁ W₂)

/-- Every value is stored at most once by a given client (the paper's uniqueness assumption). -/
def UniqueValues (σ : List (SCEv P V)) : Prop :=
  ∀ a a' p v, StoreAt σ a p v → StoreAt σ a' p v → a = a'

end Podc.StoreCollectChurn
