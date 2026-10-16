import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Spec

/-!
# The asset-transfer object type

Guerraoui, Kuznetsov, Monti, Pavlovič, Seredinschi, *The Consensus Number of a Cryptocurrency*,
PODC 2019 (DOI 10.1145/3293611.3331589; extended version arXiv 1906.05574), Section 2.2.

The asset-transfer type associated with a set of accounts `Acct` and an owner map
`μ : Acct → Finset Proc` (`Proc` = processes):

* states: balances `q : Acct → ℕ`, initial state `q₀`;
* `transfer(a, b, x)` invoked by `p` succeeds (response `true`) iff `p ∈ μ a` and `x ≤ q a`; then
  `x` is moved from `a` to `b`; otherwise the state is unchanged and the response is `false`;
* `read(a)` returns `q a`.

CSLib's sequential specifications (`ObjSpec`) do not see the caller, so the invoking process is
an argument of `transfer` (`ATOp.transfer p a b x`); every use of the type requires processes to
invoke transfers only under their own identity (`allowed` in the `Impl` model, `Honest` in the
consensus model).

**Self-transfers.** For `a = b` the paper's relation `Δ` requires `q'(a) = q(a) - x` and
`q'(a) = q(a) + x`, which is unsatisfiable for `x > 0`, so `Δ` is not total (contradicting the
paper's standing assumption). We use the sequential reading "debit `a`, then credit `b`": a
successful self-transfer leaves the balances unchanged (`moveFunds`).
-/

namespace CryptoCons

open Cslib.SharedMemory

/-- Operations of the asset-transfer type: `transfer p a b x` is `transfer(a, b, x)` invoked by
process `p`; `read a` is `read(a)`. -/
inductive ATOp (Proc Acct : Type) where
  | transfer (p : Proc) (a b : Acct) (x : ℕ)
  | read (a : Acct)
  deriving DecidableEq

/-- Balances after moving `x` from `a` to `b` (debit `a`, then credit `b`). -/
def moveFunds {Acct : Type} [DecidableEq Acct] (q : Acct → ℕ) (a b : Acct) (x : ℕ) : Acct → ℕ :=
  fun c => q c - (if c = a then x else 0) + (if c = b then x else 0)

/-- The asset-transfer object type with accounts `Acct`, owner map `μ` and initial balances `q₀`.
Responses: `.inl b` for transfers (success flag), `.inr n` for reads (balance). -/
def atSpec (Proc Acct : Type) [DecidableEq Proc] [DecidableEq Acct] (μ : Acct → Finset Proc)
    (q₀ : Acct → ℕ) : ObjSpec where
  State := Acct → ℕ
  Op := ATOp Proc Acct
  Resp := Bool ⊕ ℕ
  init := q₀
  δ q
    | .transfer p a b x =>
      if p ∈ μ a ∧ x ≤ q a then (moveFunds q a b x, .inl true) else (q, .inl false)
    | .read a => (q, .inr (q a))

section Lemmas

variable {Proc Acct : Type} [DecidableEq Proc] [DecidableEq Acct] {μ : Acct → Finset Proc} {q₀ : Acct → ℕ}

@[simp] lemma atSpec_read (q : Acct → ℕ) (a : Acct) :
    (atSpec Proc Acct μ q₀).δ q (.read a) = (q, .inr (q a)) := rfl

lemma atSpec_transfer (q : Acct → ℕ) (p : Proc) (a b : Acct) (x : ℕ) :
    (atSpec Proc Acct μ q₀).δ q (.transfer p a b x) =
      if p ∈ μ a ∧ x ≤ q a then (moveFunds q a b x, .inl true) else (q, .inl false) := rfl

lemma atSpec_transfer_pos {q : Acct → ℕ} {p : Proc} {a b : Acct} {x : ℕ} (h : p ∈ μ a ∧ x ≤ q a) :
    (atSpec Proc Acct μ q₀).δ q (.transfer p a b x) = (moveFunds q a b x, .inl true) := by
  simp [atSpec_transfer, h.1, h.2]; rfl

lemma atSpec_transfer_neg {q : Acct → ℕ} {p : Proc} {a b : Acct} {x : ℕ} (h : ¬ (p ∈ μ a ∧ x ≤ q a)) :
    (atSpec Proc Acct μ q₀).δ q (.transfer p a b x) = (q, .inl false) := by
  simp only [atSpec_transfer, h, ↓reduceIte]; rfl

lemma moveFunds_apply (q : Acct → ℕ) (a b c : Acct) (x : ℕ) :
    moveFunds q a b x c = q c - (if c = a then x else 0) + (if c = b then x else 0) := rfl

/-- Moving funds out of `a` does not decrease the balance of any other account. -/
lemma le_moveFunds_of_ne (q : Acct → ℕ) {a b c : Acct} (x : ℕ) (h : c ≠ a) :
    q c ≤ moveFunds q a b x c := by
  simp [moveFunds_apply, h]

/-- Two fund moves from different source accounts commute (when both are covered). -/
lemma moveFunds_comm (q : Acct → ℕ) {a a' : Acct} (b b' : Acct) {x x' : ℕ} (haa : a ≠ a')
    (hx : x ≤ q a) (hx' : x' ≤ q a') :
    moveFunds (moveFunds q a b x) a' b' x' = moveFunds (moveFunds q a' b' x') a b x := by
  funext c
  simp only [moveFunds_apply]
  by_cases hca : c = a
  · subst hca
    have : c ≠ a' := haa
    simp only [this, ↓reduceIte]
    split_ifs <;> omega
  · by_cases hca' : c = a'
    · subst hca'
      simp only [hca, ↓reduceIte]
      split_ifs <;> omega
    · simp only [hca, hca', ↓reduceIte]
      split_ifs <;> omega

/-- `k`-shared: every account has at most `k` owners. (The paper calls the object `k`-shared when
the maximum is exactly `k`; the impossibility only needs `≤ k`, the algorithm only needs one
account with `k` owners.) -/
def KShared (μ : Acct → Finset Proc) (k : ℕ) : Prop := ∀ a, (μ a).card ≤ k

end Lemmas

/-! ## Base objects used by the paper's implementations -/

/-- Operations of an atomic snapshot object with one component per process: `update i v`
writes `v` into component `i` (the implementation must only let process `i` do this), `scan`
returns all components atomically. -/
inductive SnapOp (Proc V : Type) where
  | update (i : Proc) (v : V)
  | scan

/-- An atomic snapshot object (Afek et al.) with components `Proc → V`, initially `v₀`.
Responses: `none` for `update`, `some S` for `scan`. -/
def snapObj (Proc V : Type) [DecidableEq Proc] (v₀ : V) : ObjSpec where
  State := Proc → V
  Op := SnapOp Proc V
  Resp := Option (Proc → V)
  init := fun _ => v₀
  δ S
    | .update i v => (Function.update S i v, none)
    | .scan => (S, some S)

/-- A `k`-consensus object (Jayanti–Toueg; Section 4 of the paper): the first `k` invocations of
`propose` return the argument of the first invocation, later ones return `⊥ = none`. State:
the first proposal (if any) and the number of invocations so far. -/
def kConsObj (V : Type) (k : ℕ) : ObjSpec where
  State := Option V × ℕ
  Op := V
  Resp := Option V
  init := (none, 0)
  δ s v :=
    let d := s.1.getD v
    if s.2 < k then ((some d, s.2 + 1), some d) else ((some d, s.2 + 1), none)

end CryptoCons
