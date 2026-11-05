import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Spec

/-!
# Theorem 4(b): a wait-free `(k, ℓ)`-SC object from a `(k, ℓ)`-universal construction

Raynal, Stainer, Taubenfeld, *Distributed Universality* (PODC 2014), Section 4.3, Theorem 4(b):
"a wait-free `(k, ℓ)`-SC object can be built in `ARW_{n,n-1}[(k, ℓ)-UC]`".

## The `(k, ℓ)`-UC as a black box

The paper deliberately does not give the `(k, ℓ)`-UC an object interface (footnote 4). We use the
weakest faithful black-box abstraction of *any* `(k, ℓ)`-universal construction instantiated with `k`
objects (sequential specifications `spec m`, CSLib's `ObjSpec`): an infinite execution
(`UCExec`) in which

* process `p` issues a sequence of operations on each object `m` (the `j`-th one with argument
  `input m p j`), each possibly invoked (`inv`), linearized and responded (`resp`, with result `out`);
* on every object the linearization points form a sequence over discrete time (`ev m t`: the
  operation linearized on `m` at time `t`, if any), each operation is linearized at most once, after
  its invocation, and before its response (if any); every responded operation is linearized;
* the result of an operation is given by the sequential specification applied to the state produced
  by the operations linearized before it (`linState`): this is linearizability, "the processes see
  the same sequence of operations on each object";
* a process issues its operations on an object one at a time (`inv_seq`).

`UCExec.IsWaitFree ℓ` is ℓ-wait-freedom of Appendix G.1: every correct process completes infinitely
many operations on each of at least `ℓ` objects.

## Result and the gap in the paper's proof

The paper instantiates the UC with `k` read/write registers: each process writes its value `v_{i,m}`
into register `m` and then reads; "as soon as `p_i` sees that `ℓ` objects have progressed, it returns
the `ℓ` values written in these objects". With a black-box UC a read returns the *last* written value,
so two processes may return different values for the same entry (`register_counterexample`: two
processes, one register, linearization `write(a) read→a write(b) read→b`, wait-free execution).
The argument "the processes see the same sequence of operations on each object" does not help: the
sequence is not observable through the registers' responses.

Repair (`scFromUC`): instantiate the `k` objects as *sticky registers* (`sticky V`, "first-value"
objects: `propose v` returns the first value ever proposed). Each process repeatedly invokes
`propose (v p m)` on every object `m` and decides, at a time `T` when its first `propose` returned on
at least `ℓ` objects, on `ℓ` of these objects with the returned values. All four properties of the
`(k, ℓ)`-SC specification hold (exactly `ℓ` pairs with distinct entries; validity with the "before
the decision" timing; agreement; termination for correct processes).
-/

namespace Podc.DistributedUniversality.Abstract

open Cslib.SharedMemory

/-! ## Linearized executions of a `(k, ℓ)`-universal construction -/

/-- The state of an object with sequential specification `S` after applying, in time order, the
operations linearized strictly before time `t` (`ev t' = some (p, j)`: the `j`-th operation of process
`p`, with argument `input p j`, is linearized at time `t'`). -/
def linState {P : Type*} (S : ObjSpec) (ev : ℕ → Option (P × ℕ)) (input : P → ℕ → S.Op) :
    ℕ → S.State
  | 0 => S.init
  | t + 1 =>
    match ev t with
    | none => linState S ev input t
    | some (p, j) => (S.δ (linState S ev input t) (input p j)).1

/-- An infinite linearizable execution of a `(k, ℓ)`-universal construction instantiated with the
`k` objects `spec m` (Sections 2–4 of the paper; black-box abstraction, see the module docstring).
Times are natural numbers; `none` means "never". -/
structure UCExec (P : Type*) (k : ℕ) (spec : Fin k → ObjSpec) where
  /-- The correct (non-crashing) processes. -/
  correct : P → Prop
  /-- Argument of the `j`-th operation of process `p` on object `m`. -/
  input : (m : Fin k) → P → ℕ → (spec m).Op
  /-- Invocation time of the `j`-th operation of `p` on `m`. -/
  inv : Fin k → P → ℕ → Option ℕ
  /-- Response time of the `j`-th operation of `p` on `m`. -/
  resp : Fin k → P → ℕ → Option ℕ
  /-- Result returned by the `j`-th operation of `p` on `m` (meaningful once it responded). -/
  out : (m : Fin k) → P → ℕ → (spec m).Resp
  /-- The operation linearized on object `m` at time `t`, if any. -/
  ev : Fin k → ℕ → Option (P × ℕ)
  /-- An operation is linearized after its invocation. -/
  ev_inv : ∀ m t p j, ev m t = some (p, j) → ∃ s, inv m p j = some s ∧ s ≤ t
  /-- An operation is linearized at most once. -/
  ev_unique : ∀ m t t' x, ev m t = some x → ev m t' = some x → t = t'
  /-- A responded operation was linearized before its response. -/
  resp_ev : ∀ m p j r, resp m p j = some r → ∃ t ≤ r, ev m t = some (p, j)
  /-- Linearizability: results follow the sequential specification along the linearization. -/
  out_spec : ∀ m t p j, ev m t = some (p, j) → (resp m p j).isSome →
    out m p j = ((spec m).δ (linState (spec m) (ev m) (input m) t) (input m p j)).2
  /-- Processes are sequential on each object: the next operation is invoked after the response
  of the previous one. -/
  inv_seq : ∀ m p j t, inv m p (j + 1) = some t → ∃ r ≤ t, resp m p j = some r

variable {P : Type*} {k : ℕ} {spec : Fin k → ObjSpec}

/-- **ℓ-wait-freedom** of a `(k, ℓ)`-universal construction (Appendix G.1): every correct process
`p` completes infinitely many operations on each object of some set `R` of at least `ℓ` objects. -/
def UCExec.IsWaitFree (E : UCExec P k spec) (ℓ : ℕ) : Prop :=
  ∀ p, E.correct p → ∃ R : Finset (Fin k), ℓ ≤ R.card ∧
    ∀ m ∈ R, {j | (E.resp m p j).isSome}.Infinite

lemma UCExec.resp_inv (E : UCExec P k spec) {m p j r} (h : E.resp m p j = some r) :
    ∃ s ≤ r, E.inv m p j = some s := by
  obtain ⟨t, htr, ht⟩ := E.resp_ev m p j r h
  obtain ⟨s, hs, hst⟩ := E.ev_inv m t p j ht
  exact ⟨s, hst.trans htr, hs⟩

/-- If the `j`-th operation of `p` on `m` responded, so did the first one (no later response). -/
lemma UCExec.resp_zero (E : UCExec P k spec) {m p} :
    ∀ j r, E.resp m p j = some r → ∃ r₀ ≤ r, E.resp m p 0 = some r₀
  | 0, r, h => ⟨r, le_rfl, h⟩
  | j + 1, r, h => by
    obtain ⟨s, hsr, hs⟩ := E.resp_inv h
    obtain ⟨r', hr's, hr'⟩ := E.inv_seq m p j s hs
    obtain ⟨r₀, hr₀, h₀⟩ := E.resp_zero j r' hr'
    exact ⟨r₀, by omega, h₀⟩

/-! ## Sticky registers -/

/-- A *sticky register* ("first-value" object) over `V`: `propose v` returns the first value ever
proposed (and stores it). The state is `none` until the first proposal. -/
abbrev sticky (V : Type) : ObjSpec where
  State := Option V
  Op := V
  Resp := V
  init := none
  δ s v := (some (s.getD v), s.getD v)

section Sticky

variable {V : Type}

@[simp] lemma sticky_δ (s : Option V) (v : V) :
    (sticky V).δ s v = (some (s.getD v), s.getD v) := rfl

lemma linState_sticky_none (ev : ℕ → Option (P × ℕ)) (input : P → ℕ → V) :
    ∀ t, (∀ t' < t, ev t' = none) → linState (sticky V) ev input t = none
  | 0, _ => rfl
  | t + 1, h => by
    rw [linState, h t (by omega)]
    exact linState_sticky_none ev input t (fun t' ht' => h t' (by omega))

lemma linState_sticky_some (ev : ℕ → Option (P × ℕ)) (input : P → ℕ → V) {t₀ : ℕ} {p₀ : P}
    {j₀ : ℕ} (h₀ : ev t₀ = some (p₀, j₀)) (hfirst : ∀ t' < t₀, ev t' = none) :
    ∀ t, t₀ < t → linState (sticky V) ev input t = some (input p₀ j₀)
  | 0, h => by omega
  | t + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · have ih := linState_sticky_some ev input h₀ hfirst t h
      rw [linState]
      rcases ev t with _ | ⟨p, j⟩
      · exact ih
      · simp only [ih, Option.getD_some]
    · rw [linState, h₀]
      simp only [linState_sticky_none ev input _ hfirst, Option.getD_none]

/-- On a sticky register, every operation returns the argument of the first linearized one. -/
lemma sticky_result (ev : ℕ → Option (P × ℕ)) (input : P → ℕ → V) {t₀ : ℕ} {p₀ : P} {j₀ : ℕ}
    (h₀ : ev t₀ = some (p₀, j₀)) (hfirst : ∀ t' < t₀, ev t' = none) {t : ℕ} {p : P} {j : ℕ}
    (h : ev t = some (p, j)) :
    ((sticky V).δ (linState (sticky V) ev input t) (input p j)).2 = input p₀ j₀ := by
  rcases lt_trichotomy t t₀ with ht | rfl | ht
  · simp [hfirst t ht] at h
  · rw [h₀] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [sticky_δ, linState_sticky_none ev input _ hfirst]
    rfl
  · rw [sticky_δ, linState_sticky_some ev input h₀ hfirst t ht]
    rfl

end Sticky

/-! ## The `(k, ℓ)`-SC specification -/

/-- **`(k, ℓ)`-simultaneous consensus**, timeless (combinatorial) form (Sections 2.1 and 4.3).
Process `i ∈ S` (the deciding processes) decides the `ℓ` pairs `(x, d i x)`, `x ∈ D i`; `prop j x` is
the value proposed by process `j` in entry `x` of its input vector.
* exactly `ℓ` pairs, with distinct first components (`D i` is a set of `ℓ` entries);
* validity: each decided value in entry `x` was proposed in entry `x` by some process;
* agreement: two decided pairs with the same entry carry the same value. -/
structure IsSCOutcome {P V : Type*} (k ℓ : ℕ) (S : Finset P) (prop : P → Fin k → V)
    (D : P → Finset (Fin k)) (d : P → Fin k → V) : Prop where
  card_eq : ∀ i ∈ S, (D i).card = ℓ
  valid : ∀ i ∈ S, ∀ x ∈ D i, ∃ j, d i x = prop j x
  agree : ∀ i ∈ S, ∀ j ∈ S, ∀ x ∈ D i, x ∈ D j → d i x = d j x

/-! ## The algorithm: sticky registers in the universal construction -/

section Algorithm

variable {V : Type} (E : UCExec P k (fun _ => sticky V))

/-- The objects on which the first `propose` of `p` returned by time `T` ("`p` has seen object `m`
progress"). -/
def UCExec.doneBy [Fintype P] (p : P) (T : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun m => ∃ r ≤ T, E.resp m p 0 = some r

/-- Process `p` decides at time `T` on the entries `D`: `ℓ` objects on which its first `propose`
returned by time `T`. The decided value for entry `m` is the result `E.out m p 0` of that
`propose`. (The algorithm decides at the first such `T`; the properties hold for every `T`.) -/
structure Decides [Fintype P] (ℓ : ℕ) (p : P) (T : ℕ) (D : Finset (Fin k)) : Prop where
  card_eq : D.card = ℓ
  subset : D ⊆ E.doneBy p T

/-- Every responded `propose` on a sticky object returns the argument of the first operation
linearized on that object. -/
lemma UCExec.sticky_out {m : Fin k} {p : P} {j r : ℕ} (h : E.resp m p j = some r) :
    ∃ t₀ q j₀, E.ev m t₀ = some (q, j₀) ∧ (∀ t' < t₀, E.ev m t' = none) ∧ t₀ ≤ r ∧
      E.out m p j = E.input m q j₀ := by
  classical
  obtain ⟨t, htr, ht⟩ := E.resp_ev m p j r h
  have hex : ∃ t, (E.ev m t).isSome := ⟨t, by simp [ht]⟩
  obtain ⟨⟨q, j₀⟩, hq⟩ := Option.isSome_iff_exists.1 (Nat.find_spec hex)
  have hfirst : ∀ t' < Nat.find hex, E.ev m t' = none := fun t' ht' => by
    simpa using Nat.find_min hex ht'
  refine ⟨Nat.find hex, q, j₀, hq, hfirst, (Nat.find_min' hex (by simp [ht])).trans htr, ?_⟩
  rw [E.out_spec m t p j ht (by simp [h])]
  exact sticky_result (E.ev m) (E.input m) hq hfirst ht

/-- Agreement: two responded `propose`s on the same sticky object return the same value. -/
theorem UCExec.sticky_agree {m : Fin k} {p q : P} {j j' r r' : ℕ} (h : E.resp m p j = some r)
    (h' : E.resp m q j' = some r') : E.out m p j = E.out m q j' := by
  obtain ⟨t₀, q₀, j₀, h₀, hf, -, ho⟩ := E.sticky_out h
  obtain ⟨t₁, q₁, j₁, h₁, hf', -, ho'⟩ := E.sticky_out h'
  have : t₀ = t₁ := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · simp [hf' _ hlt] at h₀
    · simp [hf _ hlt] at h₁
  subst this
  rw [h₀] at h₁
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
  rw [ho, ho']

/-- Termination (from ℓ-wait-freedom): a correct process eventually sees `ℓ` objects progress, and
thus decides. -/
theorem UCExec.exists_decides [Fintype P] {ℓ : ℕ} (hwf : E.IsWaitFree ℓ) {p : P}
    (hp : E.correct p) : ∃ T D, Decides E ℓ p T D := by
  classical
  obtain ⟨R, hR, hinf⟩ := hwf p hp
  have h0 : ∀ m ∈ R, ∃ r, E.resp m p 0 = some r := fun m hm => by
    obtain ⟨j, hj⟩ := (hinf m hm).nonempty
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hj
    obtain ⟨r₀, -, h₀⟩ := E.resp_zero j r hr
    exact ⟨r₀, h₀⟩
  choose! rt hrt using h0
  have hsub : R ⊆ E.doneBy p (R.sup rt) := fun m hm => by
    simp only [UCExec.doneBy, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨rt m, Finset.le_sup hm, hrt m hm⟩
  obtain ⟨D, hD, hcard⟩ := Finset.exists_subset_card_eq hR
  exact ⟨R.sup rt, D, hcard, hD.trans hsub⟩

/-- **Theorem 4(b)** of [Raynal–Stainer–Taubenfeld, PODC 2014], repaired with sticky registers:
the algorithm in which every process `p` invokes `propose (v p m)` (repeatedly) on each of the `k`
sticky objects of an ℓ-wait-free `(k, ℓ)`-universal construction, and decides on `ℓ` objects whose
first `propose` returned (with the returned values), implements a wait-free `(k, ℓ)`-SC object:
1. termination: every correct process decides;
2. the decisions of any set `S` of deciding processes form a `(k, ℓ)`-SC outcome
   (exactly `ℓ` pairs with distinct entries, validity, agreement);
3. timed validity: the value decided by `p` at time `T` in entry `m` was proposed in entry `m` by an
   operation of some process `q` invoked no later than `T`. -/
theorem scFromUC [Fintype P] {ℓ : ℕ} (v : P → Fin k → V)
    (hinput : ∀ m p j, E.input m p j = v p m) (hwf : E.IsWaitFree ℓ) :
    (∀ p, E.correct p → ∃ T D, Decides E ℓ p T D) ∧
    (∀ (S : Finset P) (T : P → ℕ) (D : P → Finset (Fin k)),
      (∀ p ∈ S, Decides E ℓ p (T p) (D p)) →
      IsSCOutcome k ℓ S v D (fun p m => E.out m p 0)) ∧
    (∀ p T D, Decides E ℓ p T D → ∀ m ∈ D,
      ∃ q j s, E.inv m q j = some s ∧ s ≤ T ∧ E.out m p 0 = v q m) := by
  have hdone : ∀ {p T m}, m ∈ E.doneBy p T → ∃ r ≤ T, E.resp m p 0 = some r := by
    intro p T m hm
    simpa [UCExec.doneBy] using hm
  refine ⟨fun p hp => E.exists_decides hwf hp, fun S T D hS => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun i hi => (hS i hi).card_eq
  · intro i hi x hx
    obtain ⟨r, -, hr⟩ := hdone ((hS i hi).subset hx)
    obtain ⟨-, q, j₀, -, -, -, ho⟩ := E.sticky_out hr
    exact ⟨q, by rw [ho, hinput]⟩
  · intro i hi j hj x hxi hxj
    obtain ⟨r, -, hr⟩ := hdone ((hS i hi).subset hxi)
    obtain ⟨r', -, hr'⟩ := hdone ((hS j hj).subset hxj)
    exact E.sticky_agree hr hr'
  · intro p T D hD m hm
    obtain ⟨r, hrT, hr⟩ := hdone (hD.subset hm)
    obtain ⟨t₀, q, j₀, h₀, -, ht₀, ho⟩ := E.sticky_out hr
    obtain ⟨s, hs, hst⟩ := E.ev_inv m t₀ q j₀ h₀
    exact ⟨q, j₀, s, hs, by omega, by rw [ho, hinput]⟩

end Algorithm

/-! ## Non-vacuity: executions from a schedule -/

section Schedule

/-- The execution of the universal construction in which the operations of all processes are
executed one at a time following a bijective schedule `sched : P × ℕ ≃ ℕ` (operation `(p, j)` is
invoked, linearized and responded at time `sched (p, j)` on every object), with the given arguments.
All processes are correct. -/
def UCExec.ofSchedule (spec : Fin k → ObjSpec) (sched : P × ℕ ≃ ℕ)
    (hmono : ∀ p j, sched (p, j) ≤ sched (p, j + 1)) (input : (m : Fin k) → P → ℕ → (spec m).Op) :
    UCExec P k spec where
  correct _ := True
  input := input
  inv _ p j := some (sched (p, j))
  resp _ p j := some (sched (p, j))
  out m p j := ((spec m).δ (linState (spec m) (fun t => some (sched.symm t)) (input m)
    (sched (p, j))) (input m p j)).2
  ev _ t := some (sched.symm t)
  ev_inv m t p j h := ⟨t, by simp [← Option.some.inj h], le_rfl⟩
  ev_unique m t t' x h h' := by
    simpa using (Option.some.inj h).trans (Option.some.inj h').symm
  resp_ev m p j r h := ⟨r, le_rfl, by simp [← Option.some.inj h]⟩
  out_spec m t p j h _ := by
    have : sched (p, j) = t := by simp [← Option.some.inj h]
    simp [this]
  inv_seq m p j t h := ⟨sched (p, j), (hmono p j).trans (Option.some.inj h).le, rfl⟩

lemma UCExec.ofSchedule_isWaitFree (spec : Fin k → ObjSpec) (sched : P × ℕ ≃ ℕ) (hmono)
    (input : (m : Fin k) → P → ℕ → (spec m).Op) {ℓ : ℕ} (hℓ : ℓ ≤ k) :
    (UCExec.ofSchedule spec sched hmono input).IsWaitFree ℓ :=
  fun _ _ => ⟨Finset.univ, by simpa using hℓ, fun _ _ => by
    simpa [UCExec.ofSchedule] using Set.infinite_univ⟩

/-- The round-robin schedule for `n` processes: operation `(p, j)` at time `j * n + p`. -/
def roundRobin (n : ℕ) [NeZero n] : Fin n × ℕ ≃ ℕ :=
  (Equiv.prodComm _ _).trans (Nat.divModEquiv n).symm

lemma roundRobin_mono (n : ℕ) [NeZero n] (p : Fin n) (j : ℕ) :
    roundRobin n (p, j) ≤ roundRobin n (p, j + 1) := by
  simp [roundRobin, Nat.divModEquiv]
  nlinarith [Nat.pos_of_neZero n]

/-- Non-vacuity of `scFromUC`: for every `n ≥ 1`, `ℓ ≤ k` and proposals `v`, the hypotheses are
satisfiable, and every process decides. -/
example (n : ℕ) [NeZero n] {V : Type} {ℓ : ℕ} (hℓ : ℓ ≤ k) (v : Fin n → Fin k → V) :
    ∃ E : UCExec (Fin n) k (fun _ => sticky V), (∀ m p j, E.input m p j = v p m) ∧
      E.IsWaitFree ℓ ∧ ∀ p, ∃ T D, Decides E ℓ p T D := by
  refine ⟨UCExec.ofSchedule _ (roundRobin n) (roundRobin_mono n) (fun m p _ => v p m), fun _ _ _ =>
    rfl, UCExec.ofSchedule_isWaitFree _ _ _ _ hℓ, fun p => ?_⟩
  exact UCExec.exists_decides _ (UCExec.ofSchedule_isWaitFree _ _ _ _ hℓ) trivial

end Schedule

/-! ## The paper's register-based construction violates agreement -/

/-- The schedule `(0,0), (0,1), (1,0), (1,1), (0,2), (1,2), (0,3), …` for two processes:
process `0` writes and reads, then process `1` writes and reads, then round robin. -/
def cexSchedule : Fin 2 × ℕ ≃ ℕ := (roundRobin 2).trans (Equiv.swap 1 2)

lemma cexSchedule_mono (p : Fin 2) (j : ℕ) : cexSchedule (p, j) ≤ cexSchedule (p, j + 1) := by
  have h := roundRobin_mono 2 p j
  simp only [cexSchedule, roundRobin, Nat.divModEquiv, Equiv.trans_apply, Equiv.prodComm_apply,
    Prod.swap_prod_mk] at h ⊢
  fin_cases p <;> simp at h ⊢ <;> rcases j with _ | _ | j <;>
    simp [Equiv.swap_apply_def]

/-- The register-based client of the paper's proof: process `p`'s first operation on register `m`
is `write (v p m)`, all later ones are `read`s. -/
def regClient {k : ℕ} (v : Fin 2 → Fin k → ℕ) (m : Fin k) (p : Fin 2) : ℕ → RWOp (Option ℕ)
  | 0 => .write (some (v p m))
  | _ + 1 => .read

/-- **The paper's proof of Theorem 4(b) is incomplete.** With a black-box `(1, 1)`-universal
construction instantiated with one atomic register (initially `⊥ = none`), the paper's algorithm
(write your value, then read) admits a wait-free execution in which process `0` writes `0` and reads
`0`, then process `1` writes `1` and reads `1`: both have seen the object progress, and the values
they read for entry `0` differ, violating `(1, 1)`-SC agreement. -/
theorem register_counterexample :
    ∃ E : UCExec (Fin 2) 1 (fun _ => register (Option ℕ) none),
      E.IsWaitFree 1 ∧ (∀ m p j, E.input m p j = regClient (fun p _ => p.val) m p j) ∧
      (∀ p, E.resp 0 p 0 ≠ none ∧ E.resp 0 p 1 ≠ none) ∧
      E.out 0 0 1 = some 0 ∧ E.out 0 1 1 = some 1 := by
  refine ⟨UCExec.ofSchedule _ cexSchedule cexSchedule_mono
    (regClient (fun p _ => p.val)), UCExec.ofSchedule_isWaitFree _ _ _ _ le_rfl,
    fun _ _ _ => rfl, fun p => by simp [UCExec.ofSchedule], ?_, ?_⟩ <;>
  decide

end Podc.DistributedUniversality.Abstract
