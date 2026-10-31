import Papers.PODC2018.PartialReplicationCausal.Model

/-!
# Theorem 1 (necessity): the class of algorithms and the notion of obliviousness

Section 2 of the paper restricts attention to algorithms that "implement causal consistency by
storing and attaching metadata (timestamps) with update messages … When to apply a received update
at a replica is determined only using the replica's local metadata and the metadata attached with
the update." We model these as *deterministic metadata algorithms* (`Alg`):

* each replica `i` keeps metadata `m : M` (its "timestamp"), initially `init i`;
* on a client write of `x`, the metadata becomes `write i m x` and the update message carries the
  new metadata (the update tuple `update(i, T, x, v)` carries the timestamp `T`);
* a received update `(k, x, T)` may be applied at `i` iff `ready i m k x T`; applying it sets the
  metadata to `merge i m k x T`.

Allowing the decision to see the sender and the register (not only `T`) and attaching the full
metadata makes the class larger, hence the necessity result stronger.

Updates carry a label `lab` (the written value, which the paper assumes unique); it is not visible
to the algorithm and is only used to identify an update across two executions, as needed to
compare causal dependency graphs of different executions (Section 3.1).
-/

namespace Podc.PartialReplicationCausal.Necessity

open Classical

variable {ι Reg M : Type*}

/-- A deterministic metadata algorithm. -/
structure Alg (ι Reg M : Type*) where
  /-- Initial metadata of each replica. -/
  init : ι → M
  /-- Metadata of replica `i` after a client write on register `x`; it is attached to the update. -/
  write : ι → M → Reg → M
  /-- `ready i m k x T`: replica `i` with metadata `m` may apply the update from `k` on register `x`
  with attached metadata `T`. -/
  ready : ι → M → ι → Reg → M → Prop
  /-- Metadata of replica `i` after applying the update from `k` on `x` with attached `T`. -/
  merge : ι → M → ι → Reg → M → M

/-- An update message; `lab` is the (unique) written value and `pre` is ghost data, as in
`Podc.PartialReplicationCausal.Update`. -/
structure Upd (ι Reg M : Type*) where
  /-- The issuing replica. -/
  src : ι
  /-- The register written. -/
  reg : Reg
  /-- The value written (unique), invisible to the algorithm. -/
  lab : ℕ
  /-- The attached metadata. -/
  ts : M
  /-- Ghost: the updates applied at `src` before this update was issued. -/
  pre : Set ℕ

/-- Global state: issued updates `log 0, …, log (n-1)`, metadata and applied sets. -/
structure St (ι Reg M : Type*) where
  /-- Number of issued updates. -/
  n : ℕ
  /-- The issued updates. -/
  log : ℕ → Upd ι Reg M
  /-- Metadata of each replica. -/
  md : ι → M
  /-- Updates applied at each replica (including its own). -/
  app : ι → Set ℕ

variable (X : ι → Set Reg) (A : Alg ι Reg M)

/-- Initial states. -/
def IsInit (s : St ι Reg M) : Prop := s.n = 0 ∧ s.md = A.init ∧ s.app = fun _ => ∅

/-- Replica `i` performs a client write of the value `ℓ` on register `x`. -/
noncomputable def St.write (s : St ι Reg M) (i : ι) (x : Reg) (ℓ : ℕ) : St ι Reg M :=
  { n := s.n + 1
    log := Function.update s.log s.n ⟨i, x, ℓ, A.write i (s.md i) x, s.app i⟩
    md := Function.update s.md i (A.write i (s.md i) x)
    app := Function.update s.app i (insert s.n (s.app i)) }

/-- Replica `i` applies update `a`. -/
noncomputable def St.apply (s : St ι Reg M) (i : ι) (a : ℕ) : St ι Reg M :=
  { s with
    md := Function.update s.md i
      (A.merge i (s.md i) (s.log a).src (s.log a).reg (s.log a).ts)
    app := Function.update s.app i (insert a (s.app i)) }

/-- Update `a` has been sent to `i` (it writes a register of `X i`), is not applied there yet, and
the algorithm allows applying it. -/
def Enabled (s : St ι Reg M) (i : ι) (a : ℕ) : Prop :=
  a < s.n ∧ (s.log a).src ≠ i ∧ (s.log a).reg ∈ X i ∧ a ∉ s.app i ∧
    A.ready i (s.md i) (s.log a).src (s.log a).reg (s.log a).ts

/-- Steps: a client write (of a fresh value) or the application of an enabled update. -/
inductive Step : St ι Reg M → St ι Reg M → Prop
  | write (s : St ι Reg M) (i : ι) (x : Reg) (ℓ : ℕ) (hx : x ∈ X i)
      (hℓ : ∀ a < s.n, (s.log a).lab ≠ ℓ) : Step s (s.write A i x ℓ)
  | apply (s : St ι Reg M) (i : ι) (a : ℕ) (h : Enabled X A s i a) : Step s (s.apply A i a)

/-- Reachable states. -/
def Reachable (s : St ι Reg M) : Prop :=
  ∃ s₀, IsInit A s₀ ∧ Relation.ReflTransGen (Step X A) s₀ s

/-- Happened-before (Definition 4). -/
def HB (s : St ι Reg M) : ℕ → ℕ → Prop :=
  Relation.TransGen fun a b => b < s.n ∧ a ∈ (s.log b).pre

/-- Safety (Definition 5). -/
def Safe (s : St ι Reg M) : Prop :=
  ∀ i, ∀ b ∈ s.app i, ∀ a, (s.log a).reg ∈ X i → HB s a b → a ∈ s.app i

/-- An infinite execution (idle steps allowed). -/
structure Execution where
  /-- State at time `t`. -/
  σ : ℕ → St ι Reg M
  init : IsInit A (σ 0)
  step : ∀ t, Step X A (σ t) (σ (t + 1)) ∨ σ (t + 1) = σ t

/-- Weak fairness: an update that stays applicable at a replica is eventually applied. -/
def Execution.Fair (E : Execution X A) : Prop :=
  ∀ i a t₀, (∀ t ≥ t₀, Enabled X A (E.σ t) i a) → ∃ t, a ∈ (E.σ t).app i

/-- Liveness (Definition 5): in a fair execution, an update is applied at each replica storing its
register within finite time after all its dependencies have been applied there. -/
def Live : Prop :=
  ∀ E : Execution X A, E.Fair → ∀ (t u : ℕ) (i : ι), u < (E.σ t).n → ((E.σ t).log u).reg ∈ X i →
    (∀ a, ((E.σ t).log a).reg ∈ X i → HB (E.σ t) a u → a ∈ (E.σ t).app i) →
    ∃ t' ≥ t, u ∈ (E.σ t').app i

/-- The algorithm implements replica-centric causal consistency (Definition 5). -/
def Implements : Prop := (∀ s, Reachable X A s → Safe X s) ∧ Live X A

/-! ### Causal dependency graphs and obliviousness (Section 3.1) -/

/-- The causal past of replica `i` (the vertex set of its causal dependency graph,
Definition 8): the applied updates and all updates that happened before them. -/
def CP (s : St ι Reg M) (i : ι) : Set ℕ := {a | a ∈ s.app i ∨ ∃ b ∈ s.app i, HB s a b}

/-- An update, identified across executions by its value, issuer and register. -/
def key (s : St ι Reg M) (a : ℕ) : ℕ × ι × Reg := ((s.log a).lab, (s.log a).src, (s.log a).reg)

/-- The causal dependency graphs of replica `i` in `s₁` and `s₂` *differ only in updates on
`e_jk`* (Section 3.1): (i) every update in only one of the two causal pasts is issued by `j` on a
register of `X_jk`, and (ii) the edges (`↪`) between common vertices coincide. -/
def DiffOnly (s₁ s₂ : St ι Reg M) (i j k : ι) : Prop :=
  (∀ a ∈ CP s₁ i, (¬ ∃ b ∈ CP s₂ i, key s₂ b = key s₁ a) →
      (s₁.log a).src = j ∧ (s₁.log a).reg ∈ X j ∩ X k) ∧
  (∀ b ∈ CP s₂ i, (¬ ∃ a ∈ CP s₁ i, key s₁ a = key s₂ b) →
      (s₂.log b).src = j ∧ (s₂.log b).reg ∈ X j ∩ X k) ∧
  (∀ a ∈ CP s₁ i, ∀ a' ∈ CP s₁ i, ∀ b ∈ CP s₂ i, ∀ b' ∈ CP s₂ i,
      key s₁ a = key s₂ b → key s₁ a' = key s₂ b' → (HB s₁ a a' ↔ HB s₂ b b'))

/-- Replica `i`, in state `s₀`, is *oblivious to updates on `e_jk`* (Section 3.1): its timestamp
(metadata `md`) is the same in any two later states whose causal dependency graphs of `i` differ only
in updates on `e_jk`. (The paper quantifies over all later graphs `R₁, R₂` with `R₀ < R₁`,
`R₀ < R₂`; we only quantify over extensions of the given state `s₀`, which makes obliviousness a
weaker assumption and Theorem 1 a stronger statement.) -/
def Oblivious (s₀ : St ι Reg M) (i j k : ι) : Prop :=
  ∀ s₁ s₂, Relation.ReflTransGen (Step X A) s₀ s₁ → Relation.ReflTransGen (Step X A) s₀ s₂ →
    DiffOnly X s₁ s₂ i j k → s₁.md i = s₂.md i

/-- Quiescent state: every issued update has been applied at every replica storing its
register. -/
def Quiescent (s : St ι Reg M) : Prop := ∀ a < s.n, ∀ r, (s.log a).reg ∈ X r → a ∈ s.app r

end Podc.PartialReplicationCausal.Necessity
