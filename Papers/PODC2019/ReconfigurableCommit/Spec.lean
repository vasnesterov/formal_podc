/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The Transaction Certification Service specification (Bravo–Gotsman, PODC 2019, §2 and App. A.2)

This file formalizes the specification side of
*M. Bravo, A. Gotsman. Reconfigurable Atomic Transaction Commit. PODC 2019* (arXiv 1906.01365v1):

* decisions `Dec` with the meet `⊓` and the order `⊑`;
* certification functions `f : 2^L × L → D` and distributivity (1);
* histories of `certify` / `decide` actions, real-time order, legal linearizations and
  TCS correctness (§2);
* shard-local certification functions `fₛ, gₛ` matching `f` (conditions (3)–(5), §2);
* the low-level specification TCS-LL (Figure 6, App. A.2).

Payload sets are `Finset`s (the paper's `2^L`; all sets that occur are finite).
-/

-- CSLib candidate: the TCS specification (this file) and Lemma A.3 (`LemmaA3.lean`).

namespace Podc.ReconfigurableCommit

/-- Decisions `D = {commit, abort}`. -/
inductive Dec
  | commit
  | abort
  deriving DecidableEq, Repr

namespace Dec

/-- The meet `⊓`: `commit ⊓ commit = commit`, `d ⊓ abort = abort ⊓ d = abort`. -/
def meet : Dec → Dec → Dec
  | commit, commit => commit
  | _, _ => abort

/-- The order `⊑` of Figure 6: `x ⊑ y ↔ x = y ∨ (x = abort ∧ y = commit)`. -/
def le (x y : Dec) : Prop := x = y ∨ (x = abort ∧ y = commit)

@[simp] theorem meet_eq_commit {x y : Dec} : meet x y = commit ↔ x = commit ∧ y = commit := by
  cases x <;> cases y <;> simp [meet]

@[simp] theorem le_commit_iff {y : Dec} : le commit y ↔ y = commit := by
  cases y <;> simp [le]

@[simp] theorem abort_le (y : Dec) : le abort y := by cases y <;> simp [le]

end Dec

section CertFun

variable {Pl : Type*} [DecidableEq Pl]

/-- Distributivity (1): `f(L₁ ∪ L₂, l) = f(L₁, l) ⊓ f(L₂, l)`. -/
def Distributive (f : Finset Pl → Pl → Dec) : Prop :=
  ∀ L₁ L₂ l, f (L₁ ∪ L₂) l = (f L₁ l).meet (f L₂ l)

/-- A distributive function commits against a set iff it commits against each element and
against `∅`. -/
theorem Distributive.eq_commit_iff {f : Finset Pl → Pl → Dec} (hf : Distributive f)
    (L : Finset Pl) (l : Pl) :
    f L l = .commit ↔ f ∅ l = .commit ∧ ∀ x ∈ L, f {x} l = .commit := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | insert a L ha ih =>
    rw [Finset.insert_eq, hf, Dec.meet_eq_commit, ih]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, ?_⟩
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact h1
      · exact h3 x hx
    · rintro ⟨h2, h3⟩
      exact ⟨h3 a (by simp), h2, fun x hx => h3 x (by simp [hx])⟩

/-- Monotonicity: committing against a set implies committing against any subset. -/
theorem Distributive.mono {f : Finset Pl → Pl → Dec} (hf : Distributive f) {L L' : Finset Pl}
    (hL : L' ⊆ L) {l : Pl} (h : f L l = .commit) : f L' l = .commit := by
  have := (hf.eq_commit_iff L l).1 h
  exact (hf.eq_commit_iff L' l).2 ⟨this.1, fun x hx => this.2 x (hL hx)⟩

end CertFun

/-! ### Histories -/

section History

variable {T Pl : Type*}

/-- Actions of a TCS history: requests `certify(t, l)` and responses `decide(t, d)`. -/
inductive Event (T Pl : Type*)
  | certify (t : T) (l : Pl)
  | decide (t : T) (d : Dec)
  deriving DecidableEq

/-- A history is a finite sequence of actions (oldest first). -/
abbrev History (T Pl : Type*) := List (Event T Pl)

/-- `t` commits in `h`: `h` contains `decide(t, commit)`. -/
def Committed (h : History T Pl) (t : T) : Prop := Event.decide t .commit ∈ h

/-- Real-time order `t ≺rt t'`: `decide(t, _) ≺h certify(t', _)`. -/
def RT (h : History T Pl) (t t' : T) : Prop :=
  ∃ i j : Fin h.length, i < j ∧ (∃ d, h[i] = Event.decide t d) ∧ (∃ l, h[j] = Event.certify t' l)

/-- Well-formedness of a history (§2): every transaction appears at most once in `certify`, and
every `decide` responds to exactly one preceding `certify` (at most one `decide` per
transaction). -/
structure WellFormed (h : History T Pl) : Prop where
  certify_unique : ∀ t l l', Event.certify t l ∈ h → Event.certify t l' ∈ h → l = l'
  decide_unique : ∀ t d d', Event.decide t d ∈ h → Event.decide t d' ∈ h → d = d'
  decide_after_certify : ∀ (j : Fin h.length) t d, h[j] = Event.decide t d →
    ∃ i : Fin h.length, i < j ∧ ∃ l, h[i] = Event.certify t l

variable [DecidableEq T] [DecidableEq Pl]

/-- The set of payloads `{l' | certify(t', l') ∈ act(h), t' ∈ ts}`. -/
def payloadsOf (h : History T Pl) (ts : List T) : Finset Pl :=
  (h.filterMap fun
    | Event.certify t' l' => if t' ∈ ts then some l' else none
    | Event.decide _ _ => none).toFinset

/-- A legal linearization of `h | committed(h)` w.r.t. `f` (§2), presented by the order `ord` in
which the committed transactions appear in the sequential history: it lists exactly the
committed transactions, once each; it preserves the real-time order of `h`; and each
transaction's decision `commit` equals `f` applied to the payloads of the transactions committed
before it. (The sequential history itself is `ord` with each `t` expanded to
`certify(t, l), decide(t, commit)`.) -/
def IsLegalLinearization (f : Finset Pl → Pl → Dec) (h : History T Pl) (ord : List T) : Prop :=
  ord.Nodup ∧ (∀ t, t ∈ ord ↔ Committed h t) ∧
  (∀ t t', t ∈ ord → t' ∈ ord → RT h t t' → ord.idxOf t < ord.idxOf t') ∧
  ∀ (i : Fin ord.length) l, Event.certify ord[i] l ∈ h →
    f (payloadsOf h (ord.take i)) l = .commit

/-- A history is correct w.r.t. `f` (§2) if `h | committed(h)` has a legal linearization. -/
def Correct (f : Finset Pl → Pl → Dec) (h : History T Pl) : Prop :=
  ∃ ord, IsLegalLinearization f h ord

end History

/-! ### Shard-local certification functions -/

section Shards

variable {T Pl S : Type*} [DecidableEq Pl]

/-- The sharding data of §2: the shards `shards(t)` of each transaction, the projection
`l | s` of payloads to shards and the empty payload `ε`. -/
structure Sharding (T Pl S : Type*) where
  /-- `shards : T → 2^S`. -/
  shards : T → Finset S
  /-- The projection `l | s`. -/
  proj : Pl → S → Pl
  /-- The empty payload `ε`. -/
  eps : Pl

/-- A payload `l` is valid for `t` (§2): `l | s = ε` for every shard `s ∉ shards(t)`. -/
def Sharding.ValidPayload (σ : Sharding T Pl S) (t : T) (l : Pl) : Prop :=
  ∀ s, s ∉ σ.shards t → σ.proj l s = σ.eps

/-- Conditions of §2 relating the global certification function `f` and the shard-local
functions `fₛ`, `gₛ`: distributivity of all of them ((1) and "similarly to (1)"), `fₛ(L, ε) =
commit`, and conditions (3), (4), (5). -/
structure Matching (σ : Sharding T Pl S) (f : Finset Pl → Pl → Dec)
    (fs gs : S → Finset Pl → Pl → Dec) : Prop where
  distrib_f : Distributive f
  distrib_fs : ∀ s, Distributive (fs s)
  distrib_gs : ∀ s, Distributive (gs s)
  fs_eps : ∀ s L, fs s L σ.eps = .commit
  /-- (3) -/
  match_f : ∀ l L, f L l = .commit ↔ ∀ s, fs s (L.image (σ.proj · s)) (σ.proj l s) = .commit
  /-- (4) -/
  g_imp_f : ∀ s L l, gs s L l = .commit → fs s L l = .commit
  /-- (5) -/
  comm : ∀ s l l', gs s {l} l' = .commit → fs s {l'} l = .commit

/-- The assumption missing from §2 (it is built into condition (6) of Chockler–Gotsman, DISC 2018,
which projects *transactions* rather than payloads): the empty payload `ε` never conflicts with
anything, `fₛ({ε}, l) = commit`. -/
def EpsNeutral (σ : Sharding T Pl S) (fs : S → Finset Pl → Pl → Dec) : Prop :=
  ∀ s l, fs s {σ.eps} l = .commit

end Shards

/-! ### TCS-LL (Figure 6) -/

section TCSLL

variable {T Pl S : Type*} [DecidableEq T] [DecidableEq Pl]

/-- The witnesses of TCS-LL: for some transactions `t` and shards `s`, a vote `dₛ[t]` (`ds s t =
some _` marks where they are defined), a position `posₛ[t]`, a payload `ploadₛ[t]` and sets
`Tₛ[t]`, `Pₛ[t]`. -/
structure LLWitness (T Pl S : Type*) where
  ds : S → T → Option Dec
  pos : S → T → ℕ
  pload : S → T → Pl
  Ts : S → T → Finset T
  Ps : S → T → Finset T

namespace LLWitness

variable (σ : Sharding T Pl S) (h : History T Pl) (w : LLWitness T Pl S)

/-- `t' ≺dec t` (Figure 6): `∃ s. t' ∈ Tₛ[t] ∨ (posₛ[t'] < posₛ[t] ∧ dₛ[t'] = commit ∧
d[t'] = abort ∧ t' ∉ Pₛ[t])` (positions taken where defined). -/
def DecRel (t' t : T) : Prop :=
  ∃ s, (w.ds s t).isSome ∧
    (t' ∈ w.Ts s t ∨
      (w.pos s t' < w.pos s t ∧ w.ds s t' = some .commit ∧ Event.decide t' .abort ∈ h ∧
        t' ∉ w.Ps s t))

/-- The constraints of Figure 6 except (12) (see `Constraint12`). Positions and votes are
defined only for certified transactions and their shards. -/
structure Valid (fs gs : S → Finset Pl → Pl → Dec) : Prop where
  dom : ∀ s t, (w.ds s t).isSome → s ∈ σ.shards t ∧ ∃ l, Event.certify t l ∈ h
  /-- (6) -/
  c6_def : ∀ t d, Event.decide t d ∈ h → ∀ s ∈ σ.shards t, (w.ds s t).isSome
  c6 : ∀ t d, Event.decide t d ∈ h → (d = .commit ↔ ∀ s ∈ σ.shards t, w.ds s t = some .commit)
  /-- (7) -/
  c7 : ∀ s t₁ t₂, t₁ ≠ t₂ → (w.ds s t₁).isSome → (w.ds s t₂).isSome → w.pos s t₁ ≠ w.pos s t₂
  /-- (8) -/
  c8 : ∀ t l s, Event.certify t l ∈ h →
    (w.ds s t = some .commit → w.pload s t = σ.proj l s) ∧
    (w.ds s t = some .abort → w.pload s t = σ.proj l s ∨ w.pload s t = σ.eps)
  /-- (9) -/
  c9 : ∀ s t d, w.ds s t = some d →
    Dec.le d ((fs s ((w.Ts s t).image (w.pload s)) (w.pload s t)).meet
      (gs s ((w.Ps s t).image (w.pload s)) (w.pload s t)))
  /-- (10) -/
  c10 : ∀ s t, (w.ds s t).isSome → ∀ t', t' ∈ w.Ts s t ↔
    ((w.ds s t').isSome ∧ w.pos s t' < w.pos s t ∧ Committed h t') ∧ t' ∉ w.Ps s t
  /-- (11) -/
  c11 : ∀ s t, (w.ds s t).isSome → ∀ t' ∈ w.Ps s t,
    w.ds s t' = some .commit ∧ w.pos s t' < w.pos s t
  /-- (13) -/
  c13 : ∀ t, ¬ Relation.TransGen (fun a b => RT h a b ∨ DecRel h w a b) t t

/-- Constraint (12) of Figure 6: `t' ≺rt t ∧ s ∈ shards(t') ∩ shards(t) ⇒ posₛ[t'] < posₛ[t]`
(where both positions are defined). It is not needed for Lemma A.3. -/
def Constraint12 : Prop :=
  ∀ t' t s, RT h t' t → s ∈ σ.shards t' → s ∈ σ.shards t → (w.ds s t').isSome →
    (w.ds s t).isSome → w.pos s t' < w.pos s t

end LLWitness

/-- A history satisfies TCS-LL (App. A.2, without constraint (12)). -/
def TCSLL (σ : Sharding T Pl S) (fs gs : S → Finset Pl → Pl → Dec) (h : History T Pl) : Prop :=
  ∃ w : LLWitness T Pl S, w.Valid σ h fs gs

end TCSLL

end Podc.ReconfigurableCommit
