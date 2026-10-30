import Mathlib

set_option linter.unusedSectionVars false

/-!
# Blink (Algorithm 1): Representative Binary Consensus on top of a black-box Binary Consensus

Monti, Camaioni, Roman. *Fast Byzantine Total Order Broadcast.* PODC 2026 (arXiv:2412.14061v2).

## Model

* `P` is the finite set of servers, `F : Finset P` the (static) set of Byzantine servers.
* Asynchronous interleaving semantics: a run is a sequence of global states `st : ℕ → P → LState P`;
  at each step either nothing happens (stutter) or one correct server performs one *action* whose
  guard holds. Safety does not depend on timing, so no clocks are needed.
* Authenticated links: a correct server records `suggestions[σ] = v` only if `σ` is Byzantine (who may
  send anything, any number of times, also changing its mind) or `σ` is correct and proposed `v`
  (correct servers send `[Suggest, v]` to all upon proposing, so "`σ` sent `[Suggest, v]`" is exactly
  "`σ.input = some v`"; messages may be delivered several times — harmless, only more general).
* The underlying Binary Consensus `dep` is a black box: `dep.Decide` events reach correct servers as
  unconstrained environment actions (`Act.depDecide`). Its specification (`DepValidity`,
  `DepAgreement`, …) is a hypothesis about the whole run. Validity is stated over the whole run (a
  value may be decided before it is proposed): this is the weakest reading of a black-box spec.
* The algorithm's thresholds are parameters: `W` (suggestions needed before proposing to `dep`;
  `4f+1` in the paper), `M` (majority threshold, `2f+1`) and `Q` (fast-path threshold, `4f+1`). The
  choice "the value suggested at least `2f+1` times" (line 16) is modelled by a nondeterministic guard;
  for `W = 2M - 1` (as in the paper) there is exactly one such value.

The state records history variables: `input` (the `con.Propose` value), `depProp` (the
`dep.Propose` value), `depDecs` (all `dep.Decide` events), `decs` (all `con.Decide` events).
-/

namespace Podc.FastByzantineTOB.Blink

open Finset

variable {P : Type*}

/-- Local state of a server running Blink (Algorithm 1), with history variables. -/
structure LState (P : Type*) where
  /-- The value proposed via `con.Propose` (each correct server proposes at most once). -/
  input : Option Bool
  /-- The `suggestions` map (line 7). -/
  sugg : P → Option Bool
  /-- The `proposed` flag (line 8). -/
  proposed : Bool
  /-- The `decided` flag (line 9). -/
  decided : Bool
  /-- History: the value proposed to `dep` (line 17). -/
  depProp : Option Bool
  /-- History: all `dep.Decide` events received (line 23). -/
  depDecs : List Bool
  /-- History: all `con.Decide` events triggered (lines 21, 25). -/
  decs : List Bool

/-- Initial state (lines 6–9). -/
def LState.init : LState P := ⟨none, fun _ => none, false, false, none, [], []⟩

/-- Trigger `con.Decide v` unless already decided (lines 20–22 and 24–26). -/
def LState.decide (s : LState P) (v : Bool) : LState P :=
  if s.decided then s else { s with decided := true, decs := s.decs ++ [v] }

/-- Actions of a correct server. -/
inductive Act (P : Type*)
  /-- `con.Propose v` (line 10): send `[Suggest, v]` to all. -/
  | propose (v : Bool)
  /-- Delivery of `[Suggest, v]` from `σ` (line 13). -/
  | recv (σ : P) (v : Bool)
  /-- Proposal of the majority value `v` to `dep` (line 15). -/
  | depPropose (v : Bool)
  /-- Fast path: `4f+1` suggestions for `v` (line 19). -/
  | fast (v : Bool)
  /-- `dep.Decide v` (line 23); an environment event of the black box. -/
  | depDecide (v : Bool)
  deriving DecidableEq

variable [Fintype P] [DecidableEq P]

/-- Number of servers whose suggestion is `v`. -/
def count (s : P → Option Bool) (v : Bool) : ℕ := #{q | s q = some v}

/-- Number of keys of the suggestions map. -/
def keys (s : P → Option Bool) : ℕ := #{q | (s q).isSome}

/-- Thresholds of Blink. -/
structure Thresholds where
  /-- Suggestions needed before proposing to `dep` (paper: `4f+1`). -/
  W : ℕ
  /-- Majority threshold (paper: `2f+1`). -/
  M : ℕ
  /-- Fast-path threshold (paper: `4f+1`). -/
  Q : ℕ

/-- The paper's thresholds for a given `f`. -/
def paperThresholds (f : ℕ) : Thresholds := ⟨4 * f + 1, 2 * f + 1, 4 * f + 1⟩

/-- Guard of an action of server `p` in global state `g`. -/
def guard (F : Finset P) (θ : Thresholds) (g : P → LState P) (p : P) : Act P → Prop
  | .propose _ => (g p).input = none
  | .recv σ v => σ ∈ F ∨ (g σ).input = some v
  | .depPropose v => θ.W ≤ keys (g p).sugg ∧ (g p).proposed = false ∧ θ.M ≤ count (g p).sugg v
  | .fast v => θ.Q ≤ count (g p).sugg v
  | .depDecide _ => True

instance (F : Finset P) (θ : Thresholds) (g : P → LState P) (p : P) (a : Act P) :
    Decidable (guard F θ g p a) := by
  cases a <;> unfold guard <;> infer_instance

/-- Effect of an action. -/
def LState.apply (s : LState P) : Act P → LState P
  | .propose v => { s with input := some v }
  | .recv σ v => { s with sugg := Function.update s.sugg σ (some v) }
  | .depPropose v => { s with proposed := true, depProp := some v }
  | .fast v => s.decide v
  | .depDecide v => { s.decide v with depDecs := s.depDecs ++ [v] }

/-- One global step: a stutter, or one action of one correct server whose guard holds. -/
def Step (F : Finset P) (θ : Thresholds) (g g' : P → LState P) : Prop :=
  g' = g ∨ ∃ p ∉ F, ∃ a, guard F θ g p a ∧ g' = Function.update g p ((g p).apply a)

/-- A run of Blink with Byzantine set `F` and thresholds `θ`. -/
structure Run (F : Finset P) (θ : Thresholds) where
  /-- Global state at time `k`. -/
  st : ℕ → P → LState P
  init : st 0 = fun _ => LState.init
  step : ∀ k, Step F θ (st k) (st (k + 1))

/-! ### Specification of the black box `dep` (Binary Consensus, safety part) -/

section Spec

variable {F : Finset P} {θ : Thresholds} (R : Run F θ)

/-- Validity of `dep`: a value decided by `dep` at a correct server was proposed to `dep` by some
correct server (at some time of the run). -/
def DepValidity : Prop :=
  ∀ k p v, p ∉ F → v ∈ (R.st k p).depDecs → ∃ k' q, q ∉ F ∧ (R.st k' q).depProp = some v

/-- Agreement of `dep` (over all pairs of correct servers, including `p = q`). -/
def DepAgreement : Prop :=
  ∀ k k' p q v w, p ∉ F → q ∉ F → v ∈ (R.st k p).depDecs → w ∈ (R.st k' q).depDecs → v = w

/-- Integrity of `dep`: no correct server receives more than one decision. -/
def DepIntegrity : Prop := ∀ k p, p ∉ F → ((R.st k p).depDecs).length ≤ 1

/-- Number of correct servers that proposed `v` to `con`, at time `k`. -/
def nProp (k : ℕ) (v : Bool) : ℕ := #{q | q ∉ F ∧ (R.st k q).input = some v}

/-- Integrity of Representative Binary Consensus: no correct server decides more than once. -/
def Integrity : Prop := ∀ k p, p ∉ F → ((R.st k p).decs).length ≤ 1

/-- Agreement of Representative Binary Consensus. -/
def Agreement : Prop :=
  ∀ k k' p q v w, p ∉ F → q ∉ F → v ∈ (R.st k p).decs → w ∈ (R.st k' q).decs → v = w

/-- Representative Validity: a decided value was proposed by at least `f + 1` correct servers. -/
def RepValidity (f : ℕ) : Prop :=
  ∀ k p v, p ∉ F → v ∈ (R.st k p).decs → ∃ k', f + 1 ≤ nProp R k' v

end Spec

/-! ### Invariants -/

section Invariants

variable {F : Finset P} {θ : Thresholds}

/-- Number of correct servers with input `v` in global state `g`. -/
def cntIn (F : Finset P) (g : P → LState P) (v : Bool) : ℕ := #{q | q ∉ F ∧ (g q).input = some v}

/-- The inductive invariant of Blink. -/
structure Inv (F : Finset P) (θ : Thresholds) (g : P → LState P) : Prop where
  /-- Observation 1 + authenticated links: suggestions of correct servers are genuine. -/
  sugg : ∀ p q v, p ∉ F → q ∉ F → (g p).sugg q = some v → (g q).input = some v
  /-- A value proposed to `dep` was suggested by `M` servers. -/
  depProp : ∀ p v, p ∉ F → (g p).depProp = some v → θ.M ≤ F.card + cntIn F g v
  /-- A decided value was fast-path justified or decided by `dep`. -/
  decs : ∀ p v, p ∉ F → v ∈ (g p).decs → θ.Q ≤ F.card + cntIn F g v ∨ v ∈ (g p).depDecs
  /-- At most one decision, and only once the `decided` flag is set. -/
  decided : ∀ p, p ∉ F → ((g p).decs.length ≤ if (g p).decided then 1 else 0)

lemma count_le (F : Finset P) (s : P → Option Bool) (v : Bool) :
    count s v ≤ F.card + #{q | q ∉ F ∧ s q = some v} := by
  unfold count
  calc #{q | s q = some v} ≤ #(F ∪ ({q | q ∉ F ∧ s q = some v} : Finset P)) := by
        apply card_le_card
        intro q hq
        by_cases h : q ∈ F
        · exact mem_union_left _ h
        · exact mem_union_right _ (by simp_all)
    _ ≤ _ := card_union_le _ _

lemma count_le_cntIn {g : P → LState P} (hI : Inv F θ g) {p : P} (hp : p ∉ F) (v : Bool) :
    count (g p).sugg v ≤ F.card + cntIn F g v := by
  refine (count_le F _ v).trans (Nat.add_le_add_left (card_le_card ?_) _)
  intro q hq
  simp only [mem_filter, mem_univ, true_and] at hq ⊢
  exact ⟨hq.1, hI.sugg p q v hp hq.1 hq.2⟩

/-! Local effects of actions. -/

lemma LState.input_apply (s : LState P) (a : Act P) (v : Bool) (h : s.input = some v)
    (ha : ∀ w, a ≠ .propose w) : (s.apply a).input = some v := by
  cases a <;> simp only [apply, decide] <;> (try split_ifs) <;> simp_all

lemma LState.sugg_apply (s : LState P) (a : Act P) (q : P) (v : Bool)
    (h : (s.apply a).sugg q = some v) : s.sugg q = some v ∨ a = .recv q v := by
  cases a with
  | recv σ w =>
    simp only [apply] at h
    by_cases hq : q = σ
    · subst hq; simp at h; simp [h]
    · rw [Function.update_of_ne hq] at h; exact Or.inl h
  | _ => simp only [apply, decide] at h <;> (try split_ifs at h) <;> simp_all

lemma LState.depProp_apply (s : LState P) (a : Act P) (v : Bool)
    (h : (s.apply a).depProp = some v) : s.depProp = some v ∨ a = .depPropose v := by
  cases a <;> simp only [apply, decide] at h <;> (try split_ifs at h) <;> simp_all

lemma LState.decs_apply (s : LState P) (a : Act P) (v : Bool) (h : v ∈ (s.apply a).decs) :
    v ∈ s.decs ∨ a = .fast v ∨ a = .depDecide v := by
  cases a <;> simp only [apply, decide] at h <;> (try split_ifs at h) <;> simp_all <;> tauto

lemma LState.depDecs_prefix_apply (s : LState P) (a : Act P) :
    s.depDecs <+: (s.apply a).depDecs := by
  cases a <;> simp only [apply, decide] <;> (try split_ifs) <;> simp

lemma LState.depDecs_apply (s : LState P) (a : Act P) : s.depDecs ⊆ (s.apply a).depDecs :=
  (s.depDecs_prefix_apply a).subset

lemma LState.mem_depDecs_apply (s : LState P) (v : Bool) :
    v ∈ (s.apply (.depDecide v)).depDecs := by
  simp [apply]

lemma LState.decided_apply (s : LState P) (a : Act P)
    (h : s.decs.length ≤ if s.decided then 1 else 0) :
    (s.apply a).decs.length ≤ if (s.apply a).decided then 1 else 0 := by
  cases a <;> simp only [apply, decide] <;> (try split_ifs at h ⊢) <;> simp_all

/-- Inputs only change from `none` to `some`. -/
lemma input_step {g g' : P → LState P} (h : Step F θ g g') (q : P) (v : Bool)
    (hq : (g q).input = some v) : (g' q).input = some v := by
  rcases h with rfl | ⟨p, -, a, hg, rfl⟩
  · exact hq
  by_cases hpq : q = p
  · subst hpq
    rw [Function.update_self]
    refine LState.input_apply _ a v hq ?_
    rintro w rfl
    simp [guard, hq] at hg
  · simpa [Function.update_of_ne hpq] using hq

lemma cntIn_mono_step {g g' : P → LState P} (h : Step F θ g g') (v : Bool) :
    cntIn F g v ≤ cntIn F g' v := by
  apply card_le_card
  intro q hq
  simp only [mem_filter, mem_univ, true_and] at hq ⊢
  exact ⟨hq.1, input_step h q v hq.2⟩

lemma Inv.init : Inv F θ (fun _ => (LState.init : LState P)) where
  sugg := by simp [LState.init]
  depProp := by simp [LState.init]
  decs := by simp [LState.init]
  decided := by simp [LState.init]

lemma Inv.step {g g' : P → LState P} (hI : Inv F θ g) (h : Step F θ g g') : Inv F θ g' := by
  have hmono := cntIn_mono_step h
  have hin := input_step h
  rcases h with rfl | ⟨p, hp, a, hg, rfl⟩
  · exact hI
  constructor
  · intro r q v hr hq hs
    by_cases hrp : r = p
    · subst hrp
      rw [Function.update_self] at hs
      rcases LState.sugg_apply _ a q v hs with hs | rfl
      · exact hin q v (hI.sugg r q v hr hq hs)
      · simp only [guard, hq, false_or] at hg
        exact hin q v hg
    · rw [Function.update_of_ne hrp] at hs
      exact hin q v (hI.sugg r q v hr hq hs)
  · intro r v hr hd
    by_cases hrp : r = p
    · subst hrp
      rw [Function.update_self] at hd
      rcases LState.depProp_apply _ a v hd with hd | rfl
      · exact (hI.depProp r v hr hd).trans (Nat.add_le_add_left (hmono _) _)
      · exact ((hg.2.2).trans (count_le_cntIn hI hr _)).trans (Nat.add_le_add_left (hmono _) _)
    · rw [Function.update_of_ne hrp] at hd
      exact (hI.depProp r v hr hd).trans (Nat.add_le_add_left (hmono _) _)
  · intro r v hr hd
    by_cases hrp : r = p
    · subst hrp
      rw [Function.update_self] at hd ⊢
      rcases LState.decs_apply _ a v hd with hd | rfl | rfl
      · exact (hI.decs r v hr hd).imp (fun h' => h'.trans (Nat.add_le_add_left (hmono _) _))
          (fun h' => LState.depDecs_apply _ a h')
      · left
        exact ((hg : θ.Q ≤ _).trans (count_le_cntIn hI hr _)).trans
          (Nat.add_le_add_left (hmono _) _)
      · exact Or.inr (LState.mem_depDecs_apply _ v)
    · rw [Function.update_of_ne hrp] at hd ⊢
      exact (hI.decs r v hr hd).imp (fun h' => h'.trans (Nat.add_le_add_left (hmono _) _)) id
  · intro r hr
    by_cases hrp : r = p
    · subst hrp
      rw [Function.update_self]
      exact LState.decided_apply _ a (hI.decided r hr)
    · rw [Function.update_of_ne hrp]
      exact hI.decided r hr


variable (R : Run F θ)

lemma Run.inv (k : ℕ) : Inv F θ (R.st k) := by
  induction k with
  | zero => rw [R.init]; exact Inv.init
  | succ k ih => exact ih.step (R.step k)

lemma Run.cntIn_mono {k k' : ℕ} (h : k ≤ k') (v : Bool) :
    cntIn F (R.st k) v ≤ cntIn F (R.st k') v := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (cntIn_mono_step (R.step _) v)

lemma Run.depDecs_prefix {k k' : ℕ} (h : k ≤ k') (p : P) :
    (R.st k p).depDecs <+: (R.st k' p).depDecs := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    refine ih.trans ?_
    rcases R.step _ with h | ⟨q, -, a, -, h⟩
    · rw [h]
    · rw [h]
      by_cases hpq : p = q
      · subst hpq; rw [Function.update_self]; exact LState.depDecs_prefix_apply _ a
      · rw [Function.update_of_ne hpq]

lemma Run.depDecs_mono {k k' : ℕ} (h : k ≤ k') (p : P) :
    (R.st k p).depDecs ⊆ (R.st k' p).depDecs :=
  (R.depDecs_prefix h p).subset

/-! ### Runs given by a finite list of actions (followed by stuttering) -/

/-- The global state after performing the first `k` actions of `acts`. -/
def listState (acts : List (P × Act P)) (k : ℕ) : P → LState P :=
  (acts.take k).foldl (fun g pa => Function.update g pa.1 ((g pa.1).apply pa.2))
    (fun _ => LState.init)

/-- Every action of `acts` is performed by a correct server whose guard holds. -/
def ValidList (F : Finset P) (θ : Thresholds) (acts : List (P × Act P)) : Prop :=
  ∀ i (h : i < acts.length), acts[i].1 ∉ F ∧ guard F θ (listState acts i) acts[i].1 acts[i].2

instance (F : Finset P) (θ : Thresholds) (acts : List (P × Act P)) :
    Decidable (ValidList F θ acts) := by
  unfold ValidList; infer_instance

/-- The run performing the actions of a valid list, then stuttering. -/
def Run.ofList (F : Finset P) (θ : Thresholds) (acts : List (P × Act P))
    (h : ValidList F θ acts) : Run F θ where
  st := listState acts
  init := by simp [listState]
  step k := by
    by_cases hk : k < acts.length
    · right
      refine ⟨acts[k].1, (h k hk).1, acts[k].2, (h k hk).2, ?_⟩
      simp only [listState]
      rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
    · left
      simp [listState, List.take_of_length_le (by omega : acts.length ≤ k),
        List.take_of_length_le (by omega : acts.length ≤ k + 1)]

lemma cntIn_add_cntIn_le (F : Finset P) (g : P → LState P) :
    cntIn F g true + cntIn F g false ≤ Fintype.card P - F.card := by
  unfold cntIn
  rw [← card_union_of_disjoint]
  · calc _ ≤ #(univ \ F) := card_le_card (by intro q; simp; tauto)
      _ = _ := by rw [card_sdiff_of_subset (subset_univ _), card_univ]
  · rw [disjoint_filter]; intro q _ h1 h2; simp_all

/-- Two values cannot both be supported by thresholds `A` and `B` when `n + |F| < A + B`. -/
lemma eq_of_thresholds {g g' : P → LState P} {A B : ℕ} {v w : Bool}
    (hAB : Fintype.card P + F.card < A + B) (hF : F.card ≤ Fintype.card P)
    (hmono : ∀ u, cntIn F g u ≤ cntIn F g' u)
    (hv : A ≤ F.card + cntIn F g v) (hw : B ≤ F.card + cntIn F g' w) : v = w := by
  by_contra hne
  have h1 := hmono v
  have h2 := cntIn_add_cntIn_le F g'
  cases v <;> cases w <;> simp at hne <;> omega

end Invariants

/-! ### The paper's lemmas and theorems -/

section Main

variable {F : Finset P} {θ : Thresholds} (R : Run F θ)

/-- Observation 1: a correct server records `suggestions[σ] = v` for a correct `σ` only if `σ`
proposed `v`. -/
theorem observation1 (k : ℕ) (p q : P) (v : Bool) (hp : p ∉ F) (hq : q ∉ F)
    (h : (R.st k p).sugg q = some v) : (R.st k q).input = some v :=
  (R.inv k).sugg p q v hp hq h

/-- Lemma 2 of [Monti–Camaioni–Roman], for general thresholds: if a correct server ever has `Q`
suggestions for `v`, no correct server ever has `M` suggestions for `!v`, provided
`n + |F| < Q + M`. (Paper: `Q = 4f+1`, `M = 2f+1`, `n = 5f+1`, `|F| ≤ f`.) -/
theorem lemma2 (hθ : Fintype.card P + F.card < θ.Q + θ.M) (k k' : ℕ) (p q : P) (v : Bool)
    (hp : p ∉ F) (hq : q ∉ F) (h1 : θ.Q ≤ count (R.st k p).sugg v) :
    ¬ θ.M ≤ count (R.st k' q).sugg (!v) := by
  intro h2
  have hF : F.card ≤ Fintype.card P := card_le_univ F
  have a := h1.trans (count_le_cntIn (R.inv k) hp v)
  have b := h2.trans (count_le_cntIn (R.inv k') hq (!v))
  rcases le_total k k' with hk | hk
  · have := eq_of_thresholds hθ hF (fun u => R.cntIn_mono hk u) a b
    cases v <;> simp at this
  · have := eq_of_thresholds (by omega) hF (fun u => R.cntIn_mono hk u) b a
    cases v <;> simp at this

/-- Lemma 3, for general thresholds: if a correct server ever has `Q` suggestions for `v`, every
`dep` decision at a correct server is `v` (uses the Validity of `dep`). -/
theorem lemma3 (hθ : Fintype.card P + F.card < θ.Q + θ.M) (hval : DepValidity R)
    (k k' : ℕ) (p q : P) (v w : Bool) (hp : p ∉ F) (hq : q ∉ F)
    (h1 : θ.Q ≤ count (R.st k p).sugg v) (h2 : w ∈ (R.st k' q).depDecs) : w = v := by
  obtain ⟨k'', r, hr, hd⟩ := hval k' q w hq h2
  have hF : F.card ≤ Fintype.card P := card_le_univ F
  have a := h1.trans (count_le_cntIn (R.inv k) hp v)
  have b := (R.inv k'').depProp r w hr hd
  rcases le_total k k'' with hk | hk
  · exact (eq_of_thresholds hθ hF (fun u => R.cntIn_mono hk u) a b).symm
  · exact eq_of_thresholds (by omega) hF (fun u => R.cntIn_mono hk u) b a

/-- Lemma 4, for general thresholds: if a correct server triggers both `dep.Decide v` and
`con.Decide w`, then `v = w`. (The paper uses the Integrity of `dep`; we use its Agreement.) -/
theorem lemma4 (hθ : Fintype.card P + F.card < θ.Q + θ.M) (hval : DepValidity R)
    (hagr : DepAgreement R) (k k' : ℕ) (p : P) (v w : Bool) (hp : p ∉ F)
    (h1 : v ∈ (R.st k p).depDecs) (h2 : w ∈ (R.st k' p).decs) : v = w := by
  rcases (R.inv k').decs p w hp h2 with h | h
  · obtain ⟨k'', r, hr, hd⟩ := hval k p v hp h1
    have b := (R.inv k'').depProp r v hr hd
    rcases le_total k' k'' with hk | hk
    · exact (eq_of_thresholds hθ (card_le_univ F) (fun u => R.cntIn_mono hk u) h b).symm
    · exact eq_of_thresholds (by omega) (card_le_univ F) (fun u => R.cntIn_mono hk u) b h
  · exact hagr k k' p p v w hp hp h1 h

/-- Theorem 3 of [Monti–Camaioni–Roman]: Blink satisfies Integrity. -/
theorem theorem3 : Integrity R := fun k p hp => by
  have := (R.inv k).decided p hp
  split_ifs at this <;> omega

/-- Theorem 2 of [Monti–Camaioni–Roman] (Representative Validity), for general thresholds
`M, Q ≥ 2f + 1`. Unlike the paper's proof, it does not use the Termination of `dep`. -/
theorem theorem2 {f : ℕ} (hF : F.card ≤ f) (hM : 2 * f + 1 ≤ θ.M) (hQ : 2 * f + 1 ≤ θ.Q)
    (hval : DepValidity R) : RepValidity R f := by
  intro k p v hp hd
  rcases (R.inv k).decs p v hp hd with h | h
  · exact ⟨k, by unfold nProp; unfold cntIn at h; omega⟩
  · obtain ⟨k', r, hr, hd'⟩ := hval k p v hp h
    have := (R.inv k').depProp r v hr hd'
    exact ⟨k', by unfold nProp; unfold cntIn at this; omega⟩

/-- Theorem 4 of [Monti–Camaioni–Roman] (Agreement), for general thresholds with
`n + |F| < Q + M` and `M ≤ Q`. Unlike the paper's proof, it does not use the Termination of `dep`. -/
theorem theorem4 (hθ : Fintype.card P + F.card < θ.Q + θ.M) (hMQ : θ.M ≤ θ.Q)
    (hval : DepValidity R) (hagr : DepAgreement R) : Agreement R := by
  intro k k' p q v w hp hq hv hw
  have hF : F.card ≤ Fintype.card P := card_le_univ F
  -- a dep decision `u` at time `k` is supported by `M` at some time
  have dep : ∀ k p u, p ∉ F → u ∈ (R.st k p).depDecs →
      ∃ k'', θ.M ≤ F.card + cntIn F (R.st k'') u := fun k p u hp h => by
    obtain ⟨k'', r, hr, hd⟩ := hval k p u hp h
    exact ⟨k'', (R.inv k'').depProp r u hr hd⟩
  have key : ∀ {k k' : ℕ} {A B : ℕ} {v w : Bool}, Fintype.card P + F.card < A + B →
      A ≤ F.card + cntIn F (R.st k) v → B ≤ F.card + cntIn F (R.st k') w → v = w :=
    fun {k k'} {A B} {v w} hAB ha hb => by
      rcases le_total k k' with hk | hk
      · exact eq_of_thresholds hAB hF (fun u => R.cntIn_mono hk u) ha hb
      · exact (eq_of_thresholds (by omega) hF (fun u => R.cntIn_mono hk u) hb ha).symm
  rcases (R.inv k).decs p v hp hv with h1 | h1 <;>
    rcases (R.inv k').decs q w hq hw with h2 | h2
  · exact key (by omega) h1 h2
  · obtain ⟨k'', h⟩ := dep _ _ _ hq h2
    exact key hθ h1 h
  · obtain ⟨k'', h⟩ := dep _ _ _ hp h1
    exact key (by omega) h h2
  · exact hagr k k' p q v w hp hq h1 h2

/-- Blink with the paper's thresholds (`W = Q = 4f+1`, `M = 2f+1`) satisfies Integrity,
Agreement and Representative Validity whenever `n ≤ 5f + 1` and at most `f` servers are Byzantine,
given a `dep` satisfying Validity and Agreement (Theorems 2–4 of [Monti–Camaioni–Roman]; the paper
assumes `n = 5f + 1`). -/
theorem blink_safe {f : ℕ} {F : Finset P} (hF : F.card ≤ f) (hn : Fintype.card P ≤ 5 * f + 1)
    (R : Run F (paperThresholds f)) (hval : DepValidity R) (hagr : DepAgreement R) :
    Integrity R ∧ Agreement R ∧ RepValidity R f :=
  ⟨theorem3 R,
    theorem4 R (by simp only [paperThresholds]; omega) (by simp [paperThresholds]; omega) hval hagr,
    theorem2 R hF (by simp [paperThresholds]) (by simp [paperThresholds]; omega) hval⟩

/-- Thresholds that work for every `n ≥ 5f + 1`: wait for and fast-decide on `n - f` suggestions,
majority threshold `2f + 1`. -/
def generalThresholds (n f : ℕ) : Thresholds := ⟨n - f, 2 * f + 1, n - f⟩

/-- Blink with thresholds `n - f`, `2f + 1`, `n - f` is safe for every `n ≥ 5f + 1`. -/
theorem blink_safe_general {f : ℕ} {F : Finset P} (hF : F.card ≤ f)
    (hn : 5 * f + 1 ≤ Fintype.card P) (R : Run F (generalThresholds (Fintype.card P) f))
    (hval : DepValidity R) (hagr : DepAgreement R) :
    Integrity R ∧ Agreement R ∧ RepValidity R f :=
  ⟨theorem3 R,
    theorem4 R (by simp only [generalThresholds]; omega) (by simp [generalThresholds]; omega)
      hval hagr,
    theorem2 R hF (by simp [generalThresholds]) (by simp [generalThresholds]; omega) hval⟩

end Main

end Podc.FastByzantineTOB.Blink
