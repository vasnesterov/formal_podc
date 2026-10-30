import Papers.PODC2025.GraphAlgorithmsPredictions.Basic
import Cslib.Computability.Distributed.Local.Locality

/-!
# The pruning algorithm, the Distributed Greedy MIS Algorithm, and their composition

Sections 3–5 of Boyar–Ellen–Larsen (PODC 2025 BA). Model: synchronous LOCAL, CSLib's
locally-iterative model `Cslib.LocallyIterative.Algorithm` (in every round a node updates its state
from its own state and the *set* of its neighbours' states). Node names are identifiers (a linear
order on `V`); a node's state `St V` holds its identifier, its prediction bit and its status
(`active`, or terminated with output `1` = `inMIS` / output `0` = `outMIS`).

All algorithms here are built from three rules (`Rule`), one per round:

* `prune`: an active node with prediction `1` all of whose neighbours have prediction `0` outputs 1;
* `max`: an active node whose active neighbours all have smaller identifiers outputs 1;
* `out`: an active node with a neighbour that output 1 outputs 0.

* `pruneAlg` (Section 3, the "simple 3 round initialization algorithm"): `prune`, then `out`.
* `greedyAlg` (Section 4, the Distributed Greedy MIS Algorithm): `max` in odd rounds, `out` in even
  rounds (rounds counted from 1).
* `predAlg = pruneAlg.seq 3 greedyAlg` (Section 5): 3 rounds of pruning, then greedy.
-/

namespace Podc.GraphAlgorithmsPredictions

open SimpleGraph Cslib.LocallyIterative

/-- Status of a node. -/
inductive Status
  | active
  | inMIS
  | outMIS
  deriving DecidableEq

/-- State of a node: identifier, prediction, status. -/
structure St (V : Type*) where
  id : V
  pred : Bool
  status : Status

/-- The rules executed in one round. -/
inductive Rule
  | prune
  | max
  | out

variable {V : Type*} [LinearOrder V]

open Classical in
/-- One round of a rule, for a node with state `s` that sees the set `N` of its neighbours' states.
Terminated nodes never change. -/
noncomputable def Rule.apply : Rule → St V → Set (St V) → St V
  | .prune, s, N =>
    if s.status = .active ∧ s.pred = true ∧ ∀ s' ∈ N, s'.pred = false then
      { s with status := .inMIS } else s
  | .max, s, N =>
    if s.status = .active ∧ ∀ s' ∈ N, s'.status = .active → s'.id < s.id then
      { s with status := .inMIS } else s
  | .out, s, N =>
    if s.status = .active ∧ ∃ s' ∈ N, s'.status = .inMIS then
      { s with status := .outMIS } else s

/-- The algorithm executing rule `r t` in round `t + 1`. -/
noncomputable def ofRules (r : ℕ → Rule) : Algorithm (St V) := ⟨fun t => (r t).apply⟩

@[simp] lemma ofRules_step (r : ℕ → Rule) (t : ℕ) :
    (ofRules (V := V) r).step t = (r t).apply := rfl

/-- Rounds of the pruning algorithm: `prune` in round 1, `out` afterwards. -/
def pruneRule (t : ℕ) : Rule := if t = 0 then .prune else .out

/-- Rounds of the Distributed Greedy MIS Algorithm: `max` in rounds `1, 3, 5, …` (`t` even), `out`
in rounds `2, 4, …`. -/
def greedyRule (t : ℕ) : Rule := if Even t then .max else .out

/-- The pruning (initialization) algorithm of Section 3. -/
noncomputable def pruneAlg : Algorithm (St V) := ofRules pruneRule

/-- The Distributed Greedy MIS Algorithm of Section 4. -/
noncomputable def greedyAlg : Algorithm (St V) := ofRules greedyRule

/-- The MIS algorithm with predictions of Section 5: the 3-round pruning algorithm followed by the
Distributed Greedy MIS Algorithm on the remaining graph (i.e. on every error component). -/
noncomputable def predAlg : Algorithm (St V) := pruneAlg.seq 3 greedyAlg

/-- Initial states: every node knows its identifier and prediction and is active. -/
def initSt (x : V → Bool) (v : V) : St V := ⟨v, x v, .active⟩

/-- All nodes active, predictions irrelevant (the input of an algorithm without predictions). -/
def allActive (v : V) : St V := ⟨v, false, .active⟩

/-! ### Basic properties of the rules -/

@[simp] lemma Rule.apply_id (r : Rule) (s : St V) (N : Set (St V)) : (r.apply s N).id = s.id := by
  cases r <;> simp only [Rule.apply] <;> split_ifs <;> rfl

@[simp] lemma Rule.apply_pred (r : Rule) (s : St V) (N : Set (St V)) :
    (r.apply s N).pred = s.pred := by
  cases r <;> simp only [Rule.apply] <;> split_ifs <;> rfl

lemma Rule.apply_of_ne (r : Rule) {s : St V} (h : s.status ≠ .active) (N : Set (St V)) :
    r.apply s N = s := by
  cases r <;> simp [Rule.apply, h]

variable (G : SimpleGraph V) (r : ℕ → Rule)

lemma run_id {c : V → St V} (hc : ∀ v, (c v).id = v) (t : ℕ) (v : V) :
    ((ofRules r).run G c t v).id = v := by
  induction t generalizing v with
  | zero => exact hc v
  | succ t ih => rw [Algorithm.run_succ_apply, ofRules_step, Rule.apply_id, ih]

lemma run_pred (c : V → St V) (t : ℕ) (v : V) :
    ((ofRules r).run G c t v).pred = (c v).pred := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih => rw [Algorithm.run_succ_apply, ofRules_step, Rule.apply_pred, ih]

/-- The status of node `v` after `t` rounds. -/
noncomputable def status (c : V → St V) (t : ℕ) (v : V) : Status :=
  ((ofRules r).run G c t v).status

variable {G r} {c : V → St V}

lemma status_succ_of_ne {t : ℕ} {v : V} (h : status G r c t v ≠ .active) :
    status G r c (t + 1) v = status G r c t v := by
  simp only [status, Algorithm.run_succ_apply, ofRules_step]
  rw [Rule.apply_of_ne _ h]

lemma status_le_of_ne {t t' : ℕ} (htt : t ≤ t') {v : V} (h : status G r c t v ≠ .active) :
    status G r c t' v = status G r c t v := by
  induction t', htt using Nat.le_induction with
  | base => rfl
  | succ t' _ ih => rw [status_succ_of_ne (by rw [ih]; exact h), ih]

lemma active_of_active_le {t t' : ℕ} (htt : t ≤ t') {v : V}
    (h : status G r c t' v = .active) : status G r c t v = .active := by
  by_contra h'
  exact h' (status_le_of_ne htt h' ▸ h)

variable (hc : ∀ v, (c v).id = v)
include hc

open Classical in
lemma status_succ_max {t : ℕ} (ht : r t = .max) (v : V) :
    status G r c (t + 1) v =
      if status G r c t v = .active ∧ ∀ u, G.Adj v u → status G r c t u = .active → u < v
      then .inMIS else status G r c t v := by
  classical
  simp only [status, Algorithm.run_succ_apply, ofRules_step, ht, Rule.apply]
  have e : (∀ s' ∈ nbrColors G ((ofRules r).run G c t) v, s'.status = .active →
      s'.id < ((ofRules r).run G c t v).id) ↔
      ∀ u, G.Adj v u → ((ofRules r).run G c t u).status = .active → u < v := by
    simp only [mem_nbrColors, forall_exists_index, and_imp, run_id G r hc]
    constructor
    · intro h u hu hs; simpa [run_id G r hc] using h _ u hu rfl hs
    · rintro h _ u hu rfl hs; simpa [run_id G r hc] using h u hu hs
  simp only [e]
  split_ifs with h
  · exact (ite_eq_left h).symm
  · exact (ite_eq_right h).symm

omit hc in
open Classical in
lemma status_succ_out {t : ℕ} (ht : r t = .out) (v : V) :
    status G r c (t + 1) v =
      if status G r c t v = .active ∧ ∃ u, G.Adj v u ∧ status G r c t u = .inMIS
      then .outMIS else status G r c t v := by
  classical
  simp only [status, Algorithm.run_succ_apply, ofRules_step, ht, Rule.apply]
  have e : (∃ s' ∈ nbrColors G ((ofRules r).run G c t) v, s'.status = .inMIS) ↔
      ∃ u, G.Adj v u ∧ ((ofRules r).run G c t u).status = .inMIS := by
    simp only [mem_nbrColors]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, hs⟩; exact ⟨u, hu, hs⟩
    · rintro ⟨u, hu, hs⟩; exact ⟨_, ⟨u, hu, rfl⟩, hs⟩
  simp only [e]
  split_ifs with h
  · exact (ite_eq_left h).symm
  · exact (ite_eq_right h).symm

omit hc in
open Classical in
lemma status_succ_prune {t : ℕ} (ht : r t = .prune) (v : V) :
    status G r c (t + 1) v =
      if status G r c t v = .active ∧ (c v).pred = true ∧ ∀ u, G.Adj v u → (c u).pred = false
      then .inMIS else status G r c t v := by
  classical
  simp only [status, Algorithm.run_succ_apply, ofRules_step, ht, Rule.apply]
  have e : (∀ s' ∈ nbrColors G ((ofRules r).run G c t) v, s'.pred = false) ↔
      ∀ u, G.Adj v u → (c u).pred = false := by
    simp only [mem_nbrColors, forall_exists_index, and_imp]
    constructor
    · intro h u hu; simpa [run_pred] using h _ u hu rfl
    · rintro h _ u hu rfl; simpa [run_pred] using h u hu
  simp only [e, run_pred]
  split_ifs with h
  · exact (ite_eq_left h).symm
  · exact (ite_eq_right h).symm

end Podc.GraphAlgorithmsPredictions
