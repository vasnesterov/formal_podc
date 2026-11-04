import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Basic
import Mathlib.Tactic.FinCases

/-!
# Consistency layers: Eventual Consistency and Eventual Consensus (Section 4.2, Appendix B)

A run of a consistency layer is described, as in the paper, by the sequences `S(i, t)`: the last
sequence delivered to process `p_i` at (or before) time `t` (`S(i, 0) = []`; a crashed process
keeps its last sequence), by the submission of the operations (which process submitted an
operation, and when), and by the set of correct processes.

* `LayerRun`, `Nontriviality`, `SetStability`, `PrefixConsistency` (C1)–(C3),
  `EventualConsistency`.
* `StableFrom R t` (the property in Eventual Stability, from time `t` on), `EventualStability`
  (there is such a time *in this run*: all layer properties are properties of runs),
  `EventualConsensus`.
* `TConsistent R t` (`t`-consistency, Appendix B).

**Lemma 5 is false** (`lemma5_false`): `t`-stability does not imply `t`-consistency. The proof
of Lemma 5 applies (C3) to the operations at a position where two correct processes disagree,
but (C3) only concerns operations submitted by *correct* processes. In the counterexample a
faulty process submits `a` and `b`; after a common prefix `[c]` (submitted by a correct
process) one correct process delivers `[c, a]` and the other `[c, b]`, forever.
-/

namespace Podc.EventualLinearizability

/-- A run of a consistency layer. -/
structure LayerRun (Proc Item : Type) where
  /-- `S i t`: the last sequence delivered to `p_i` at time `t` (or before). -/
  S : Proc → ℕ → List Item
  /-- `sub o = some (j, t)`: `o` was submitted by `p_j` at time `t`; `none`: never submitted. -/
  sub : Item → Option (Proc × ℕ)
  /-- The correct processes. -/
  correct : Set Proc

namespace LayerRun

variable {Proc Item : Type} (R : LayerRun Proc Item)

/-- `S(i, 0)` is the empty sequence. -/
def Initial : Prop := ∀ i, R.S i 0 = []

/-- **Nontriviality**: every operation in `S(i, t)` has been submitted at a time `t' ≤ t`, and
appears only once in `S(i, t)`. -/
def Nontriviality : Prop :=
  ∀ i t, (∀ o ∈ R.S i t, ∃ j t', R.sub o = some (j, t') ∧ t' ≤ t) ∧ (R.S i t).Nodup

/-- **Set stability**: if `t ≤ t'` then each operation of `S(i, t)` is in `S(i, t')`. -/
def SetStability : Prop := ∀ i t t', t ≤ t' → ∀ o ∈ R.S i t, o ∈ R.S i t'

/-- **Prefix consistency** (C1)–(C3) with the common prefixes `P`. -/
def PrefixConsistencyWith (P : ℕ → List Item) : Prop :=
  (∀ i ∈ R.correct, ∀ t t', t ≤ t' → P t <+: R.S i t') ∧
  (∀ t t', t ≤ t' → P t <+: P t') ∧
  (∀ o j t', R.sub o = some (j, t') → j ∈ R.correct → ∃ t'', t' ≤ t'' ∧ o ∈ P t'')

/-- **Prefix consistency**. -/
def PrefixConsistency : Prop := ∃ P, R.PrefixConsistencyWith P

/-- **Eventual Consistency** (Section 4.2). -/
def EventualConsistency : Prop :=
  R.Initial ∧ R.Nontriviality ∧ R.SetStability ∧ R.PrefixConsistency

/-- The property required by Eventual Stability, from time `t` on: for `t ≤ t' ≤ t''`,
`S(i, t')` is a prefix of `S(i, t'')`, for every process. -/
def StableFrom (t : ℕ) : Prop := ∀ i t' t'', t ≤ t' → t' ≤ t'' → R.S i t' <+: R.S i t''

/-- **Eventual Stability**: there is a time from which the run is stable. -/
def EventualStability : Prop := ∃ t, R.StableFrom t

/-- **Eventual Consensus** (Section 4.2) = Eventual Consistency + Eventual Stability. -/
def EventualConsensus : Prop := R.EventualConsistency ∧ R.EventualStability

/-- **`t`-consistency** (Appendix B): the sequences of any two correct processes at times
after `t` are prefixes of each other. -/
def TConsistent (t : ℕ) : Prop :=
  ∀ i ∈ R.correct, ∀ j ∈ R.correct, ∀ ti tj, t < ti → t < tj →
    R.S i ti <+: R.S j tj ∨ R.S j tj <+: R.S i ti

end LayerRun

/-! ### Lemma 5 is false -/

/-- The counterexample: processes `0, 1` correct, `2` faulty; operations `0 = a`, `1 = b`
(submitted by `p2` at times `1`, `2`) and `2 = c` (submitted by `p0` at time `3`). From time
`4` on, `p0` holds `[c, a]` and `p1` holds `[c, b]`; the common prefix is `[c]`. -/
def lemma5Run : LayerRun (Fin 3) (Fin 3) where
  S i t := if 4 ≤ t then (if i = 0 then [2, 0] else if i = 1 then [2, 1] else []) else []
  sub o := if o = 0 then some (2, 1) else if o = 1 then some (2, 2) else some (0, 3)
  correct := {0, 1}

/-- The common prefixes of `lemma5Run`. -/
def lemma5P (t : ℕ) : List (Fin 3) := if 4 ≤ t then [2] else []

lemma lemma5Run_eventualConsensus : lemma5Run.EventualConsensus ∧ lemma5Run.StableFrom 0 := by
  have hstab : lemma5Run.StableFrom 0 := by
    intro i t' t'' _ h
    simp only [lemma5Run]
    by_cases h1 : 4 ≤ t'
    · simp [h1, le_trans h1 h]
    · simp [h1]
  refine ⟨⟨⟨fun i => by simp [lemma5Run], ?_, ?_, lemma5P, ?_, ?_, ?_⟩, 0, hstab⟩, hstab⟩
  · intro i t
    simp only [lemma5Run]
    split_ifs <;> fin_cases i <;> simp_all <;> omega
  · intro i t t' h o ho
    simp only [lemma5Run] at ho ⊢
    split_ifs at ho ⊢ <;> simp_all <;> omega
  · intro i hi t t' h
    simp only [lemma5Run, lemma5P, Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
    split_ifs <;> simp_all; omega
  · intro t t' h
    simp only [lemma5P]
    split_ifs <;> simp_all; omega
  · intro o j t' ho hj
    refine ⟨4, ?_, ?_⟩ <;>
      simp only [lemma5Run, lemma5P, Set.mem_insert_iff, Set.mem_singleton_iff] at ho hj ⊢ <;>
      split_ifs at ho <;> simp_all <;> omega

/-- **Lemma 5 of the paper is false**: a run satisfying Eventual Consensus with stability from
time `0` (`t`-stability for `t = 0`) is not `t`-consistent for any `t`. -/
theorem lemma5_false :
    lemma5Run.EventualConsensus ∧ lemma5Run.StableFrom 0 ∧ ∀ t, ¬ lemma5Run.TConsistent t := by
  refine ⟨lemma5Run_eventualConsensus.1, lemma5Run_eventualConsensus.2, fun t ht => ?_⟩
  have := ht 0 (by simp [lemma5Run]) 1 (by simp [lemma5Run]) (t + 4) (t + 4) (by omega)
    (by omega)
  simp [lemma5Run] at this

/-- Lemma 5 as stated ("if a consistency layer satisfies `t`-stability then it satisfies
`t`-consistency") does not hold. -/
theorem not_lemma5 :
    ¬ ∀ (R : LayerRun (Fin 3) (Fin 3)) (t : ℕ), R.EventualConsistency → R.StableFrom t →
      R.TConsistent t := fun h =>
  lemma5_false.2.2 0 (h lemma5Run 0 lemma5_false.1.1 lemma5_false.2.1)

end Podc.EventualLinearizability
