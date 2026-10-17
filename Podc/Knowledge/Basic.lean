import Mathlib

/-!
# Interpreted systems: runs, points, local states and knowledge

The *runs and systems* semantics of knowledge (Fagin–Halpern–Moses–Vardi, *Reasoning about
Knowledge*), in the abstract form used by knowledge-based analyses of distributed protocols:

* a system is a type `R` of runs (all runs of a protocol in a model) together with, for every
  process `i : ι`, a local-state function `loc i : R → ℕ → L i`; a *point* is a pair `(r, t)`;
* every run determines a set `nf r` of nonfaulty processes (crash, omission, Byzantine, … — the
  operational meaning of "faulty" is left abstract, as in the specifications of agreement
  problems);
* a *fact* is a predicate on points (`Fact R = R → ℕ → Prop`); a *run fact* is a predicate on runs,
  viewed as a fact constant in time (`RunFact.lift`).

Knowledge (`System.K`) is defined by indistinguishability of local states, over all points of all
runs of the system. Besides the standard notions (`K`, local facts, everyone knows / common
knowledge `E`, `C`) this file defines

* `System.KN` — *nonfaulty knowledge* `K_i^N φ := i ∈ N ∧ K_i (i ∈ N → φ)` (Moses–Tuttle's belief
  restricted to nonfaulty processes; David–Moses PODC 2026, Definition 1.1);
* `System.Hope` — the *hope* modality `H_i φ := i ∈ N → K_i (i ∈ N → φ)` of Kuznets et al.;

and proves the **knowledge of preconditions** principle for nonfaulty processes
(`System.kop`, Moses TARK 2015): a precondition of a local action is nonfaulty-known whenever a
nonfaulty process performs it.

-- CSLib candidate (whole file)
-/

namespace Podc.Knowledge

/-- A fact: a predicate on points `(r, t)`. -/
abbrev Fact (R : Type*) := R → ℕ → Prop

/-- A run fact, seen as a fact whose truth does not depend on time. -/
def RunFact.lift {R : Type*} (p : R → Prop) : Fact R := fun r _ => p r

@[simp] lemma RunFact.lift_apply {R : Type*} (p : R → Prop) (r : R) (t : ℕ) :
    RunFact.lift p r t ↔ p r := Iff.rfl

/-- `⊨ φ`: the fact `φ` holds at every point of the system. -/
def Fact.Valid {R : Type*} (φ : Fact R) : Prop := ∀ r t, φ r t

/-- An interpreted system over processes `ι` and runs `R`: local states (of type `L i` for
process `i`) at every point, and the set of nonfaulty processes of every run. -/
structure System (ι R : Type*) (L : ι → Type*) where
  /-- The local state of process `i` at time `t` of run `r`. -/
  loc : (i : ι) → R → ℕ → L i
  /-- The nonfaulty (correct) processes of a run: the paper's `N(r)`. -/
  nf : R → Set ι

namespace System

variable {ι R : Type*} {L : ι → Type*} (S : System ι R L)

/-- `K_i φ`: process `i` knows `φ` at `(r, t)` iff `φ` holds at every point of the system at which
`i` has the same local state as at `(r, t)`. -/
def K (i : ι) (φ : Fact R) : Fact R :=
  fun r t => ∀ r' t', S.loc i r' t' = S.loc i r t → φ r' t'

/-- A fact is *local to `i`* if its truth at a point depends only on `i`'s local state there. -/
def IsLocal (i : ι) (φ : Fact R) : Prop :=
  ∀ r t r' t', S.loc i r' t' = S.loc i r t → (φ r' t' ↔ φ r t)

/-- The fact `i ∈ N`: process `i` is nonfaulty in the current run. -/
def InN (i : ι) : Fact R := fun r _ => i ∈ S.nf r

/-- **Nonfaulty knowledge** `K_i^N φ := i ∈ N ∧ K_i (i ∈ N → φ)`. -/
def KN (i : ι) (φ : Fact R) : Fact R :=
  fun r t => i ∈ S.nf r ∧ S.K i (fun r' t' => i ∈ S.nf r' → φ r' t') r t

/-- The **hope** modality of Kuznets et al.: `H_i φ := i ∈ N → K_i (i ∈ N → φ)`. -/
def Hope (i : ι) (φ : Fact R) : Fact R :=
  fun r t => i ∈ S.nf r → S.K i (fun r' t' => i ∈ S.nf r' → φ r' t') r t

/-! ### Basic properties of knowledge -/

variable {S}

/-- Knowledge axiom `K_i φ → φ`. -/
lemma K.holds {i : ι} {φ : Fact R} {r : R} {t : ℕ} (h : S.K i φ r t) : φ r t :=
  h r t rfl

lemma K.mono {i : ι} {φ ψ : Fact R} {r : R} {t : ℕ} (h : S.K i φ r t)
    (hφψ : ∀ r' t', S.loc i r' t' = S.loc i r t → φ r' t' → ψ r' t') : S.K i ψ r t :=
  fun r' t' h' => hφψ r' t' h' (h r' t' h')

/-- Knowledge formulas are local. -/
lemma isLocal_K (i : ι) (φ : Fact R) : S.IsLocal i (S.K i φ) := by
  intro r t r' t' h
  simp only [K, h]

/-- Knowledge is determined by the local state. -/
lemma K.of_loc_eq {i : ι} {φ : Fact R} {r r' : R} {t t' : ℕ} (h : S.K i φ r t)
    (he : S.loc i r' t' = S.loc i r t) : S.K i φ r' t' :=
  ((isLocal_K i φ) r t r' t' he).2 h

/-- Positive introspection `K_i φ → K_i K_i φ`. -/
lemma K.introspect {i : ι} {φ : Fact R} {r : R} {t : ℕ} (h : S.K i φ r t) : S.K i (S.K i φ) r t :=
  fun _ _ h' => h.of_loc_eq h'

/-- Local facts are known when they hold. -/
lemma IsLocal.K {i : ι} {φ : Fact R} (hφ : S.IsLocal i φ) {r : R} {t : ℕ} (h : φ r t) :
    S.K i φ r t :=
  fun r' t' h' => (hφ r t r' t' h').2 h

/-! ### Nonfaulty knowledge -/

/-- Footnote 4 of David–Moses: `⊨ K_i^N φ → φ`. -/
lemma KN.holds {i : ι} {φ : Fact R} {r : R} {t : ℕ} (h : S.KN i φ r t) : φ r t :=
  h.2 r t rfl h.1

/-- `⊨ i ∈ N ∧ K_i (i ∈ N → ψ) → ψ` (nonfaulty beliefs are never false). -/
lemma belief_true {i : ι} {φ : Fact R} {r : R} {t : ℕ} (hi : i ∈ S.nf r)
    (h : S.K i (fun r' t' => i ∈ S.nf r' → φ r' t') r t) : φ r t :=
  KN.holds ⟨hi, h⟩

lemma KN.mono {i : ι} {φ ψ : Fact R} {r : R} {t : ℕ} (h : S.KN i φ r t)
    (hφψ : ∀ r' t', i ∈ S.nf r' → φ r' t' → ψ r' t') : S.KN i ψ r t :=
  ⟨h.1, fun r' t' h' hi => hφψ r' t' hi (h.2 r' t' h' hi)⟩

lemma KN.and {i : ι} {φ ψ : Fact R} {r : R} {t : ℕ} (h₁ : S.KN i φ r t) (h₂ : S.KN i ψ r t) :
    S.KN i (fun r t => φ r t ∧ ψ r t) r t :=
  ⟨h₁.1, fun r' t' h' hi => ⟨h₁.2 r' t' h' hi, h₂.2 r' t' h' hi⟩⟩

lemma KN.forall {α : Sort*} {i : ι} {φ : α → Fact R} {r : R} {t : ℕ}
    (hi : i ∈ S.nf r) (h : ∀ a, S.KN i (φ a) r t) : S.KN i (fun r t => ∀ a, φ a r t) r t :=
  ⟨hi, fun r' t' h' hi' a => (h a).2 r' t' h' hi'⟩

/-- Faulty processes have no nonfaulty knowledge (footnote 4). -/
lemma not_KN_of_faulty {i : ι} {φ : Fact R} {r : R} {t : ℕ} (hi : i ∉ S.nf r) :
    ¬ S.KN i φ r t := fun h => hi h.1

/-- For nonfaulty processes, nonfaulty knowledge coincides with hope (footnote 4). -/
lemma KN_iff_hope {i : ι} {φ : Fact R} {r : R} {t : ℕ} (hi : i ∈ S.nf r) :
    S.KN i φ r t ↔ S.Hope i φ r t :=
  ⟨fun h _ => h.2, fun h => ⟨hi, h hi⟩⟩

/-- For faulty processes, hope holds for every fact, even `False` (footnote 4). -/
lemma hope_of_faulty {i : ι} {φ : Fact R} {r : R} {t : ℕ} (hi : i ∉ S.nf r) :
    S.Hope i φ r t := fun h => absurd h hi

/-- **Knowledge of preconditions for nonfaulty processes** (Theorem 1.2 of David–Moses, an
instance of Moses' KoP principle): if the action `α` of process `i` is triggered by `i`'s local
state (`α` is `i`-local) and `ψ` is a precondition for a nonfaulty `i` performing `α`, then a
nonfaulty `i` performing `α` has nonfaulty knowledge of `ψ`. -/
theorem kop {i : ι} {α ψ : Fact R} (hα : S.IsLocal i α)
    (hpre : ∀ r t, i ∈ S.nf r → α r t → ψ r t) :
    ∀ r t, i ∈ S.nf r → α r t → S.KN i ψ r t :=
  fun r t hi ha => ⟨hi, fun r' t' h' hi' => hpre r' t' hi' ((hα r t r' t' h').2 ha)⟩

/-! ### Classical (point-based) everyone knows and common knowledge -/

variable (S)

/-- Classical *everyone knows* among all processes: `E φ := ⋀_i K_i φ`. -/
def E (φ : Fact R) : Fact R := fun r t => ∀ i, S.K i φ r t

/-- Classical *common knowledge* among all processes: `E^m φ` for all `m ≥ 1`. -/
def C (φ : Fact R) : Fact R := fun r t => ∀ m, (S.E)^[m + 1] φ r t

end System

end Podc.Knowledge
