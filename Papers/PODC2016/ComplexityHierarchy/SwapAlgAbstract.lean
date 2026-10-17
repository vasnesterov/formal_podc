import Cslib.Computability.Distributed.SharedMemory.Consensus
import Cslib.Computability.Distributed.SharedMemory.Progress
import Mathlib.Data.Finset.Max

/-!
# Swap and read (Section 8 of [EGSZ16]): the algorithm with atomic scans

[EGSZ16] F. Ellen, R. Gelashvili, N. Shavit, L. Zhu, *A Complexity-Based Hierarchy for
Multiprocessor Synchronization*, PODC 2016 (arXiv 1607.06139), Section 8, Algorithm 1.

This file contains the combinatorial core of the correctness proof of Algorithm 1: the
algorithm with *atomic* scans of the `m` swap locations, as a transition system on abstract
configurations `ACfg` (memory = `m` lap vectors, local states `ALoc`). The real algorithm (scans
by double collect, `SwapAlg.lean`) is reduced to this one by a simulation argument.

Values are `Fin k`, a *lap vector* is `Fin k → ℕ`. After a scan returning `a : Fin m → Laps k`,
a process with local laps `l` and last swap result `s` computes `L = merge l s a` (Algorithm 1,
line 5); if every location contains `L` it decides `v* = vstar L` (largest lap, ties to the
smaller value) when `v*` is at least two laps ahead of every other value, otherwise it
increments `L v*` and swaps into `X_1` (index `0`); if some location differs from `L` it swaps
`L` into the first such location (`after`).

## Main result

* `AInv`: an invariant of abstract configurations (existentially quantified ghost state) which
  holds initially (`aInv_init`) and is preserved by every step (`AInv.invoke`, `AInv.swap`,
  `AInv.scan`, the latter needs `|P| ≤ m + 1`); it implies agreement (`AInv.agree`) and validity
  (`AInv.valid`).

## The invariant (relation to the paper)

The ghost state records the *floor* `F` = lap vector of the last scan that returned the same
vector from every location ("all-equal scan", the scans `S` of Lemma 8.3), the set `wloc` of
locations and the set `wproc` of processes involved in *stale* swaps since then (a swap by a
process `p` with `¬ F ≤ l p`; these are the swaps of the set `W` in the proof of Lemma 8.3), and
the first deciding all-equal scan `win` (Lemma 8.5). Lemma 8.3 ("every scan after an all-equal
scan `S` sees laps `≥ ℓ(S)`") becomes `floor_le_merge`: locations outside `wloc` contain vectors
`≥ F`; the counting part of the paper's proof becomes the inequality
`|wloc| + |{q ∈ wproc stale with stale s}| ≤ |wproc|` together with a non-stale witness outside
`wproc`, which gives `|wproc| ≤ |P| - 1 ≤ m`. Lemma 8.2/8.4 become the bound
`laps ≤ F + 1` on every lap value in the system (`Bnd`), and its strengthening for the losing
values after the first decision.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy.SwapRead

open Finset

/-- Lap vectors: `l v` is the lap of value `v`. -/
abbrev Laps (k : ℕ) := Fin k → ℕ

variable {k m : ℕ}

/-- Line 5 of Algorithm 1: the componentwise maximum of the local laps `l`, the result `s` of the
last swap and the vectors `a j` returned by the scan. -/
def merge (l s : Laps k) (a : Fin m → Laps k) : Laps k :=
  fun v => max (max (l v) (s v)) (univ.sup fun j => a j v)

lemma le_merge_l (l s : Laps k) (a : Fin m → Laps k) : l ≤ merge l s a :=
  fun _ => le_trans (le_max_left _ _) (le_max_left _ _)

lemma le_merge_s (l s : Laps k) (a : Fin m → Laps k) : s ≤ merge l s a :=
  fun _ => le_trans (le_max_right _ _) (le_max_left _ _)

lemma le_merge_a (l s : Laps k) (a : Fin m → Laps k) (j : Fin m) : a j ≤ merge l s a :=
  fun v => le_trans (le_sup (f := fun j => a j v) (mem_univ j)) (le_max_right _ _)

lemma merge_le {l s : Laps k} {a : Fin m → Laps k} {v : Fin k} {B : ℕ} (hl : l v ≤ B)
    (hs : s v ≤ B) (ha : ∀ j, a j v ≤ B) : merge l s a v ≤ B :=
  max_le (max_le hl hs) (Finset.sup_le fun j _ => ha j)

instance (F l : Laps k) : Decidable (F ≤ l) := decidable_of_iff (∀ v, F v ≤ l v) Pi.le_def.symm

/-- `w` is at least two laps ahead of every other value (line 9). -/
def Lead2 (L : Laps k) (w : Fin k) : Prop := ∀ u, u ≠ w → L u + 2 ≤ L w

instance (L : Laps k) (w : Fin k) : Decidable (Lead2 L w) := by unfold Lead2; infer_instance

/-- Lines 6–7: the smallest value with the largest lap. -/
def vstar [NeZero k] (L : Laps k) : Fin k :=
  (univ.filter fun v => ∀ u, L u ≤ L v).min' (by
    obtain ⟨v, -, hv⟩ := exists_max_image univ L univ_nonempty
    exact ⟨v, by simpa using fun u => hv u (mem_univ u)⟩)

lemma le_vstar [NeZero k] (L : Laps k) (u : Fin k) : L u ≤ L (vstar L) := by
  have := min'_mem (univ.filter fun v => ∀ u, L u ≤ L v) (by
    obtain ⟨v, -, hv⟩ := exists_max_image univ L univ_nonempty
    exact ⟨v, by simpa using fun u => hv u (mem_univ u)⟩)
  simp only [mem_filter, mem_univ, true_and] at this
  exact this u

/-- Line 12: the first location whose content differs from `L` (`0` if there is none). -/
def firstNe [NeZero m] (a : Fin m → Laps k) (L : Laps k) : Fin m :=
  if h : ∃ j, a j ≠ L then
    (univ.filter fun j => a j ≠ L).min' (by obtain ⟨j, hj⟩ := h; exact ⟨j, by simp [hj]⟩)
  else 0

lemma firstNe_ne [NeZero m] {a : Fin m → Laps k} {L : Laps k} (h : ∃ j, a j ≠ L) :
    a (firstNe a L) ≠ L := by
  unfold firstNe
  simp only [h, ↓reduceDIte]
  have := min'_mem (univ.filter fun j => a j ≠ L) (by obtain ⟨j, hj⟩ := h; exact ⟨j, by simp [hj]⟩)
  simpa using this

/-- Program counter of a process. -/
inductive Ph (k m : ℕ) where
  /-- Not invoked yet. -/
  | idle
  /-- About to scan (the loop of Algorithm 1 starts with a scan). -/
  | scan
  /-- About to swap its laps into location `j`. -/
  | swap (j : Fin m)
  /-- Decided `w`. -/
  | done (w : Fin k)
  deriving DecidableEq

/-- Lines 5–12 of Algorithm 1: the next program counter and the new local laps after a scan
returning `a`, for local laps `l` and last swap result `s`. -/
def after [NeZero k] [NeZero m] (l s : Laps k) (a : Fin m → Laps k) : Ph k m × Laps k :=
  if ∀ j, a j = merge l s a then
    if Lead2 (merge l s a) (vstar (merge l s a)) then (.done (vstar (merge l s a)), merge l s a)
    else (.swap 0, Function.update (merge l s a) (vstar (merge l s a))
      (merge l s a (vstar (merge l s a)) + 1))
  else (.swap (firstNe a (merge l s a)), merge l s a)

/-- The three outcomes of a scan. -/
lemma after_cases [NeZero k] [NeZero m] (l s : Laps k) (a : Fin m → Laps k) :
    ((∀ j, a j = merge l s a) ∧ Lead2 (merge l s a) (vstar (merge l s a)) ∧
        after l s a = (.done (vstar (merge l s a)), merge l s a)) ∨
      ((∀ j, a j = merge l s a) ∧ ¬ Lead2 (merge l s a) (vstar (merge l s a)) ∧
        after l s a = (.swap 0, Function.update (merge l s a) (vstar (merge l s a))
          (merge l s a (vstar (merge l s a)) + 1))) ∨
      ((¬ ∀ j, a j = merge l s a) ∧
        after l s a = (.swap (firstNe a (merge l s a)), merge l s a)) := by
  unfold after
  by_cases h1 : ∀ j, a j = merge l s a
  · by_cases h2 : Lead2 (merge l s a) (vstar (merge l s a))
    · left; simp [h1, h2]
    · right; left; simp [h1, h2]
  · right; right; simp [h1]

lemma after_cases' [NeZero k] [NeZero m] (l s : Laps k) (a : Fin m → Laps k) (L : Laps k)
    (hL : L = merge l s a) :
    ((∀ j, a j = L) ∧ Lead2 L (vstar L) ∧ after l s a = (.done (vstar L), L)) ∨
      ((∀ j, a j = L) ∧ ¬ Lead2 L (vstar L) ∧
        after l s a = (.swap 0, Function.update L (vstar L) (L (vstar L) + 1))) ∨
      ((¬ ∀ j, a j = L) ∧ after l s a = (.swap (firstNe a L), L)) := by
  subst hL; exact after_cases l s a

lemma merge_le_after [NeZero k] [NeZero m] (l s : Laps k) (a : Fin m → Laps k) :
    merge l s a ≤ (after l s a).2 := by
  rcases after_cases l s a with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩
  · rw [h]
  · rw [h]; intro v
    by_cases hv : v = vstar (merge l s a)
    · subst hv; simp
    · simp [Function.update_of_ne hv]
  · rw [h]

lemma after_ph_ne_idle [NeZero k] [NeZero m] (l s : Laps k) (a : Fin m → Laps k) :
    (after l s a).1 ≠ .idle := by
  rcases after_cases l s a with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp

lemma after_ph_ne_scan [NeZero k] [NeZero m] (l s : Laps k) (a : Fin m → Laps k) :
    (after l s a).1 ≠ .scan := by
  rcases after_cases l s a with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp

/-! ### Abstract configurations -/

/-- Local state of a process in the atomic-scan algorithm. -/
structure ALoc (k m : ℕ) where
  /-- Program counter. -/
  ph : Ph k m
  /-- The local laps `ℓ_0, …, ℓ_{k-1}`. -/
  l : Laps k
  /-- The result of the last swap. -/
  s : Laps k
  /-- The input (meaningful once invoked). -/
  inp : Fin k

/-- Abstract configuration: contents of the `m` locations and local states. -/
structure ACfg (k m : ℕ) (P : Type) where
  /-- Contents of the swap locations. -/
  mem : Fin m → Laps k
  /-- Local states. -/
  loc : P → ALoc k m

variable {P : Type} [DecidableEq P]

namespace ACfg

/-- Invocation with input `x` (line 1: `ℓ_x ← 1`). -/
def invoke (a : ACfg k m P) (p : P) (x : Fin k) : ACfg k m P :=
  ⟨a.mem, Function.update a.loc p ⟨.scan, Function.update 0 x 1, 0, x⟩⟩

/-- The swap of line 13 by `p` into location `j`. -/
def swapStep (a : ACfg k m P) (p : P) (j : Fin m) : ACfg k m P :=
  ⟨Function.update a.mem j (a.loc p).l,
    Function.update a.loc p { a.loc p with ph := .scan, s := a.mem j }⟩

/-- An atomic scan by `p` followed by the local computation of lines 4–12. -/
def scanStep [NeZero k] [NeZero m] (a : ACfg k m P) (p : P) : ACfg k m P :=
  ⟨a.mem, Function.update a.loc p { a.loc p with
    ph := (after (a.loc p).l (a.loc p).s a.mem).1, l := (after (a.loc p).l (a.loc p).s a.mem).2 }⟩

end ACfg

/-- All lap values of `u` in the system (memory, local laps, swap results) are at most `b`. -/
def Bnd (a : ACfg k m P) (u : Fin k) (b : ℕ) : Prop :=
  (∀ j, a.mem j u ≤ b) ∧ ∀ p, (a.loc p).l u ≤ b ∧ (a.loc p).s u ≤ b

/-- Ghost state of the invariant. -/
structure Ghost (k m : ℕ) (P : Type) where
  /-- The floor: laps of the last all-equal scan. -/
  F : Laps k
  /-- Locations written by stale swaps since that scan. -/
  wloc : Finset (Fin m)
  /-- Processes that performed stale swaps since that scan. -/
  wproc : Finset P
  /-- The value decided by the first deciding scan and that scan's laps. -/
  win : Option (Fin k × Laps k)

/-- The invariant of the atomic-scan algorithm. -/
structure Inv (a : ACfg k m P) (g : Ghost k m P) : Prop where
  good : ∀ j, j ∉ g.wloc → g.F ≤ a.mem j
  count : g.wloc.card +
      (g.wproc.filter fun q => ¬ g.F ≤ (a.loc q).l ∧ ¬ g.F ≤ (a.loc q).s).card ≤ g.wproc.card
  wit : ∀ _ : P, ∃ r, g.F ≤ (a.loc r).l ∧ r ∉ g.wproc
  wscan : ∀ q ∈ g.wproc, ¬ g.F ≤ (a.loc q).l → (a.loc q).ph = .scan
  wact : ∀ q ∈ g.wproc, (a.loc q).ph ≠ .idle
  bnd : ∀ u, Bnd a u (g.F u + 1)
  winNone : g.win = none → ∀ p w, (a.loc p).ph ≠ .done w
  winSome : ∀ v F0, g.win = some (v, F0) → (∀ u, u ≠ v → F0 u + 2 ≤ F0 v) ∧ F0 ≤ g.F ∧
    (∀ u, u ≠ v → Bnd a u (F0 u + 1)) ∧ ∀ p w, (a.loc p).ph = .done w → w = v
  valid : ∀ u, (∀ q, (a.loc q).ph ≠ .idle → (a.loc q).inp ≠ u) →
    Bnd a u 0 ∧ ∀ p, (a.loc p).ph ≠ .done u
  idle0 : ∀ p, (a.loc p).ph = .idle → (a.loc p).l = 0 ∧ (a.loc p).s = 0
  inpPos : ∀ p, (a.loc p).ph ≠ .idle → 1 ≤ (a.loc p).l (a.loc p).inp

/-- The invariant (ghost state existentially quantified). -/
def AInv (a : ACfg k m P) : Prop := ∃ g : Ghost k m P, Inv a g

/-- The initial abstract configuration. -/
def aInit [NeZero k] : ACfg k m P := ⟨fun _ => 0, fun _ => ⟨.idle, 0, 0, 0⟩⟩

lemma aInv_init [NeZero k] : AInv (aInit : ACfg k m P) := by
  refine ⟨⟨0, ∅, ∅, none⟩, ?_⟩
  constructor
  · intro j _; exact le_rfl
  · simp
  · intro q; exact ⟨q, le_rfl, by simp⟩
  · simp
  · simp
  · intro u; simp [Bnd, aInit]
  · intro _ p w; simp [aInit]
  · intro v F0 h; simp at h
  · intro u _; simp [Bnd, aInit]
  · intro p _; simp [aInit]
  · intro p h; simp [aInit] at h

/-! ### Effect of the steps on single fields -/

namespace ACfg

variable (a : ACfg k m P) (p r : P)

@[simp] lemma invoke_mem (x : Fin k) : (a.invoke p x).mem = a.mem := rfl

lemma invoke_loc (x : Fin k) : (a.invoke p x).loc r =
    if r = p then ⟨.scan, Function.update 0 x 1, 0, x⟩ else a.loc r := by
  by_cases h : r = p
  · subst h; simp [invoke]
  · simp [invoke, h]

lemma swapStep_mem (j i : Fin m) : (a.swapStep p j).mem i = if i = j then (a.loc p).l else a.mem i := by
  by_cases h : i = j
  · subst h; simp [swapStep]
  · simp [swapStep, h]

lemma swapStep_ph (j : Fin m) : ((a.swapStep p j).loc r).ph = if r = p then .scan else (a.loc r).ph := by
  by_cases h : r = p
  · subst h; simp [swapStep]
  · simp [swapStep, h]

@[simp] lemma swapStep_l (j : Fin m) : ((a.swapStep p j).loc r).l = (a.loc r).l := by
  by_cases h : r = p
  · subst h; simp [swapStep]
  · simp [swapStep, h]

@[simp] lemma swapStep_inp (j : Fin m) : ((a.swapStep p j).loc r).inp = (a.loc r).inp := by
  by_cases h : r = p
  · subst h; simp [swapStep]
  · simp [swapStep, h]

lemma swapStep_s (j : Fin m) : ((a.swapStep p j).loc r).s = if r = p then a.mem j else (a.loc r).s := by
  by_cases h : r = p
  · subst h; simp [swapStep]
  · simp [swapStep, h]

variable [NeZero k] [NeZero m]

@[simp] lemma scanStep_mem : (a.scanStep p).mem = a.mem := rfl

lemma scanStep_ph : ((a.scanStep p).loc r).ph =
    if r = p then (after (a.loc p).l (a.loc p).s a.mem).1 else (a.loc r).ph := by
  by_cases h : r = p
  · subst h; simp [scanStep]
  · simp [scanStep, h]

lemma scanStep_l : ((a.scanStep p).loc r).l =
    if r = p then (after (a.loc p).l (a.loc p).s a.mem).2 else (a.loc r).l := by
  by_cases h : r = p
  · subst h; simp [scanStep]
  · simp [scanStep, h]

@[simp] lemma scanStep_s : ((a.scanStep p).loc r).s = (a.loc r).s := by
  by_cases h : r = p
  · subst h; simp [scanStep]
  · simp [scanStep, h]

@[simp] lemma scanStep_inp : ((a.scanStep p).loc r).inp = (a.loc r).inp := by
  by_cases h : r = p
  · subst h; simp [scanStep]
  · simp [scanStep, h]

end ACfg

/-! ### Preservation of the invariant -/

variable {a : ACfg k m P} {g : Ghost k m P}

lemma Bnd.mono {u : Fin k} {b b' : ℕ} (h : Bnd a u b) (hb : b ≤ b') : Bnd a u b' :=
  ⟨fun j => (h.1 j).trans hb, fun p => ⟨(h.2 p).1.trans hb, (h.2 p).2.trans hb⟩⟩

lemma Bnd.swapStep {u : Fin k} {b : ℕ} (h : Bnd a u b) (p : P) (j : Fin m) :
    Bnd (a.swapStep p j) u b := by
  refine ⟨fun i => ?_, fun r => ⟨?_, ?_⟩⟩
  · rw [ACfg.swapStep_mem]; split_ifs
    · exact (h.2 p).1
    · exact h.1 i
  · rw [ACfg.swapStep_l]; exact (h.2 r).1
  · rw [ACfg.swapStep_s]; split_ifs
    · exact h.1 j
    · exact (h.2 r).2

lemma Bnd.scanStep [NeZero k] [NeZero m] {u : Fin k} {b : ℕ} (h : Bnd a u b) (p : P)
    (hp : (after (a.loc p).l (a.loc p).s a.mem).2 u ≤ b) : Bnd (a.scanStep p) u b := by
  refine ⟨fun i => h.1 i, fun r => ⟨?_, ?_⟩⟩
  · rw [ACfg.scanStep_l]; split_ifs
    · exact hp
    · exact (h.2 r).1
  · rw [ACfg.scanStep_s]; exact (h.2 r).2

lemma Bnd.merge_le {u : Fin k} {b : ℕ} (h : Bnd a u b) (p : P) :
    merge (a.loc p).l (a.loc p).s a.mem u ≤ b :=
  SwapRead.merge_le (h.2 p).1 (h.2 p).2 h.1

lemma Inv.invoke [NeZero k] (h : Inv a g) {p : P} {x : Fin k} (hp : (a.loc p).ph = .idle) :
    Inv (a.invoke p x) g := by
  obtain ⟨hl0, hs0⟩ := h.idle0 p hp
  have hpw : p ∉ g.wproc := fun hm => h.wact p hm hp
  have hl : ∀ r, ((a.invoke p x).loc r).l = if r = p then Function.update (0 : Laps k) x 1 else (a.loc r).l := by
    intro r; rw [ACfg.invoke_loc]; split_ifs <;> rfl
  have hs : ∀ r, ((a.invoke p x).loc r).s = if r = p then 0 else (a.loc r).s := by
    intro r; rw [ACfg.invoke_loc]; split_ifs <;> rfl
  have hph : ∀ r, ((a.invoke p x).loc r).ph = if r = p then .scan else (a.loc r).ph := by
    intro r; rw [ACfg.invoke_loc]; split_ifs <;> rfl
  have hinp : ∀ r, ((a.invoke p x).loc r).inp = if r = p then x else (a.loc r).inp := by
    intro r; rw [ACfg.invoke_loc]; split_ifs <;> rfl
  have hex : (1 : ℕ) ≤ Function.update (0 : Laps k) x 1 x := by simp
  have hle1 : ∀ u, Function.update (0 : Laps k) x 1 u ≤ 1 := by
    intro u; by_cases hu : u = x
    · subst hu; simp
    · simp [Function.update_of_ne hu]
  have hbnd : ∀ u b, 1 ≤ b → Bnd a u b → Bnd (a.invoke p x) u b := by
    intro u b hb hB
    refine ⟨fun j => hB.1 j, fun r => ⟨?_, ?_⟩⟩
    · rw [hl]; split_ifs
      · exact (hle1 u).trans hb
      · exact (hB.2 r).1
    · rw [hs]; split_ifs
      · simp
      · exact (hB.2 r).2
  have hdone : ∀ r w, ((a.invoke p x).loc r).ph = .done w → (a.loc r).ph = .done w := by
    intro r w hr; rw [hph] at hr; split_ifs at hr; exact hr
  constructor
  · exact h.good
  · have : (g.wproc.filter fun q => ¬ g.F ≤ ((a.invoke p x).loc q).l ∧
        ¬ g.F ≤ ((a.invoke p x).loc q).s) =
        (g.wproc.filter fun q => ¬ g.F ≤ (a.loc q).l ∧ ¬ g.F ≤ (a.loc q).s) := by
      apply Finset.filter_congr; intro q hq
      have hqp : q ≠ p := by rintro rfl; exact hpw hq
      rw [hl, hs, ite_eq_right hqp, ite_eq_right hqp]
    rw [this]; exact h.count
  · intro q
    obtain ⟨r, hr, hrw⟩ := h.wit q
    refine ⟨r, ?_, hrw⟩
    rw [hl]; split_ifs with hrp
    · subst hrp; rw [hl0] at hr
      intro v; exact (hr v).trans (Nat.zero_le _)
    · exact hr
  · intro q hq
    have hqp : q ≠ p := by rintro rfl; exact hpw hq
    rw [hl, hph, ite_eq_right hqp, ite_eq_right hqp]; exact h.wscan q hq
  · intro q hq
    have hqp : q ≠ p := by rintro rfl; exact hpw hq
    rw [hph, ite_eq_right hqp]; exact h.wact q hq
  · intro u; exact hbnd u _ (by omega) (h.bnd u)
  · intro hw r w hr; exact h.winNone hw r w (hdone r w hr)
  · intro v F0 hw
    obtain ⟨h1, h2, h3, h4⟩ := h.winSome v F0 hw
    exact ⟨h1, h2, fun u hu => hbnd u _ (by omega) (h3 u hu), fun r w hr => h4 r w (hdone r w hr)⟩
  · intro u hu
    have hux : x ≠ u := by
      have := hu p (by rw [hph]; simp); rwa [hinp, ite_eq_left rfl] at this
    have hu' : ∀ q, (a.loc q).ph ≠ .idle → (a.loc q).inp ≠ u := by
      intro q hq
      have hqp : q ≠ p := by rintro rfl; exact hq hp
      have := hu q (by rw [hph, ite_eq_right hqp]; exact hq)
      rwa [hinp, ite_eq_right hqp] at this
    obtain ⟨hB, hD⟩ := h.valid u hu'
    refine ⟨⟨fun j => hB.1 j, fun r => ⟨?_, ?_⟩⟩, fun r hr => hD r (hdone r u hr)⟩
    · rw [hl]; split_ifs
      · simp [Function.update_of_ne hux.symm]
      · exact (hB.2 r).1
    · rw [hs]; split_ifs
      · simp
      · exact (hB.2 r).2
  · intro r hr
    rw [hph] at hr; split_ifs at hr with hrp
    rw [hl, hs, ite_eq_right hrp, ite_eq_right hrp]; exact h.idle0 r hr
  · intro r hr
    rw [hl, hinp]; split_ifs with hrp
    · exact hex
    · rw [hph, ite_eq_right hrp] at hr; exact h.inpPos r hr

lemma swapStep_ph_ne_idle {p r : P} {j : Fin m} (hp : (a.loc p).ph = .swap j) :
    ((a.swapStep p j).loc r).ph ≠ .idle ↔ (a.loc r).ph ≠ .idle := by
  rw [ACfg.swapStep_ph]; split_ifs with hrp
  · subst hrp; simp [hp]
  · rfl

lemma swapStep_done {p r : P} {j : Fin m} {w : Fin k}
    (hr : ((a.swapStep p j).loc r).ph = .done w) : (a.loc r).ph = .done w := by
  rw [ACfg.swapStep_ph] at hr; split_ifs at hr; exact hr

/-- Common part of the two swap cases. -/
lemma Inv.swap_common (h : Inv a g) {p : P} {j : Fin m} (hp : (a.loc p).ph = .swap j) :
    (∀ u, Bnd (a.swapStep p j) u (g.F u + 1)) ∧
    (g.win = none → ∀ r w, ((a.swapStep p j).loc r).ph ≠ .done w) ∧
    (∀ v F0, g.win = some (v, F0) → (∀ u, u ≠ v → F0 u + 2 ≤ F0 v) ∧ F0 ≤ g.F ∧
      (∀ u, u ≠ v → Bnd (a.swapStep p j) u (F0 u + 1)) ∧
      ∀ r w, ((a.swapStep p j).loc r).ph = .done w → w = v) ∧
    (∀ u, (∀ q, ((a.swapStep p j).loc q).ph ≠ .idle → ((a.swapStep p j).loc q).inp ≠ u) →
      Bnd (a.swapStep p j) u 0 ∧ ∀ r, ((a.swapStep p j).loc r).ph ≠ .done u) ∧
    (∀ r, ((a.swapStep p j).loc r).ph = .idle →
      ((a.swapStep p j).loc r).l = 0 ∧ ((a.swapStep p j).loc r).s = 0) ∧
    (∀ r, ((a.swapStep p j).loc r).ph ≠ .idle →
      1 ≤ ((a.swapStep p j).loc r).l ((a.swapStep p j).loc r).inp) := by
  refine ⟨fun u => (h.bnd u).swapStep p j, fun hw r w hr => h.winNone hw r w (swapStep_done hr),
    fun v F0 hw => ?_, fun u hu => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.winSome v F0 hw
    exact ⟨h1, h2, fun u hu => (h3 u hu).swapStep p j, fun r w hr => h4 r w (swapStep_done hr)⟩
  · have hu' : ∀ q, (a.loc q).ph ≠ .idle → (a.loc q).inp ≠ u := by
      intro q hq
      have := hu q ((swapStep_ph_ne_idle hp).2 hq)
      rwa [ACfg.swapStep_inp] at this
    obtain ⟨hB, hD⟩ := h.valid u hu'
    exact ⟨hB.swapStep p j, fun r hr => hD r (swapStep_done hr)⟩
  · have hrp : r ≠ p := by
      rintro rfl; rw [ACfg.swapStep_ph, ite_eq_left rfl] at hr; cases hr
    rw [ACfg.swapStep_ph, ite_eq_right hrp] at hr
    rw [ACfg.swapStep_l, ACfg.swapStep_s, ite_eq_right hrp]; exact h.idle0 r hr
  · rw [ACfg.swapStep_l, ACfg.swapStep_inp]; exact h.inpPos r ((swapStep_ph_ne_idle hp).1 hr)

lemma Inv.swap_post (h : Inv a g) {p : P} {j : Fin m} (hp : (a.loc p).ph = .swap j)
    (hF : g.F ≤ (a.loc p).l) : Inv (a.swapStep p j) g := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h.swap_common hp
  constructor
  · intro i hi; rw [ACfg.swapStep_mem]; split_ifs
    · exact hF
    · exact h.good i hi
  · have : (g.wproc.filter fun q => ¬ g.F ≤ ((a.swapStep p j).loc q).l ∧
        ¬ g.F ≤ ((a.swapStep p j).loc q).s) =
        (g.wproc.filter fun q => ¬ g.F ≤ (a.loc q).l ∧ ¬ g.F ≤ (a.loc q).s) := by
      apply Finset.filter_congr; intro q _
      rw [ACfg.swapStep_l, ACfg.swapStep_s]; split_ifs with hqp
      · subst hqp; simp [hF]
      · rfl
    rw [this]; exact h.count
  · intro q
    obtain ⟨r, hr, hrw⟩ := h.wit q
    exact ⟨r, by rw [ACfg.swapStep_l]; exact hr, hrw⟩
  · intro q hq hql
    rw [ACfg.swapStep_l] at hql
    have hqp : q ≠ p := by rintro rfl; exact hql hF
    rw [ACfg.swapStep_ph, ite_eq_right hqp]; exact h.wscan q hq hql
  · intro q hq; exact (swapStep_ph_ne_idle hp).2 (h.wact q hq)
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · exact c6

lemma Inv.swap_stale (h : Inv a g) {p : P} {j : Fin m} (hp : (a.loc p).ph = .swap j)
    (hF : ¬ g.F ≤ (a.loc p).l) :
    Inv (a.swapStep p j) { g with wloc := insert j g.wloc, wproc := insert p g.wproc } := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h.swap_common hp
  have hpw : p ∉ g.wproc := fun hm => by rw [h.wscan p hm hF] at hp; cases hp
  constructor
  · intro i hi
    simp only [mem_insert, not_or] at hi
    rw [ACfg.swapStep_mem, ite_eq_right hi.1]; exact h.good i hi.2
  · simp only
    have hfilt : ((insert p g.wproc).filter fun q => ¬ g.F ≤ ((a.swapStep p j).loc q).l ∧
        ¬ g.F ≤ ((a.swapStep p j).loc q).s) ⊆
        insert p (g.wproc.filter fun q => ¬ g.F ≤ (a.loc q).l ∧ ¬ g.F ≤ (a.loc q).s) := by
      intro q hq
      simp only [mem_filter, mem_insert, ACfg.swapStep_l, ACfg.swapStep_s] at hq ⊢
      rcases hq with ⟨rfl | hq1, hq2⟩
      · left; rfl
      · by_cases hqp : q = p
        · left; exact hqp
        · right; rw [ite_eq_right hqp] at hq2; exact ⟨hq1, hq2⟩
    rw [card_insert_of_notMem hpw]
    by_cases hj : j ∈ g.wloc
    · rw [insert_eq_of_mem hj]
      have := (card_le_card hfilt).trans (card_insert_le _ _)
      have := h.count
      omega
    · rw [card_insert_of_notMem hj]
      have hfilt' : ((insert p g.wproc).filter fun q => ¬ g.F ≤ ((a.swapStep p j).loc q).l ∧
          ¬ g.F ≤ ((a.swapStep p j).loc q).s) ⊆
          (g.wproc.filter fun q => ¬ g.F ≤ (a.loc q).l ∧ ¬ g.F ≤ (a.loc q).s) := by
        intro q hq
        have h1 := hfilt hq
        rcases mem_insert.1 h1 with rfl | h1
        · exfalso
          simp only [mem_filter, ACfg.swapStep_s] at hq
          exact hq.2.2 (h.good j hj)
        · exact h1
      have := card_le_card hfilt'
      have := h.count
      omega
  · intro q
    obtain ⟨r, hr, hrw⟩ := h.wit q
    have hrp : r ≠ p := by rintro rfl; exact hF hr
    exact ⟨r, by rw [ACfg.swapStep_l]; exact hr, by simp [hrp, hrw]⟩
  · intro q hq hql
    rw [ACfg.swapStep_ph]; split_ifs with hqp
    · rfl
    · rw [ACfg.swapStep_l] at hql
      exact h.wscan q ((mem_insert.1 hq).resolve_left hqp) hql
  · intro q hq
    rw [ACfg.swapStep_ph]; split_ifs with hqp
    · simp
    · exact h.wact q ((mem_insert.1 hq).resolve_left hqp)
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · exact c6

lemma AInv.invoke [NeZero k] (h : AInv a) {p : P} {x : Fin k} (hp : (a.loc p).ph = .idle) :
    AInv (a.invoke p x) := by
  obtain ⟨g, hg⟩ := h; exact ⟨g, hg.invoke hp⟩

lemma AInv.swap (h : AInv a) {p : P} {j : Fin m} (hp : (a.loc p).ph = .swap j) :
    AInv (a.swapStep p j) := by
  obtain ⟨g, hg⟩ := h
  by_cases hF : g.F ≤ (a.loc p).l
  · exact ⟨g, hg.swap_post hp hF⟩
  · exact ⟨_, hg.swap_stale hp hF⟩

/-! ### The scan step -/

section Scan

variable [NeZero k] [NeZero m]

lemma after_done {l s : Laps k} {a : Fin m → Laps k} {w : Fin k}
    (h : (after l s a).1 = .done w) : w = vstar (merge l s a) ∧ (∀ j, a j = merge l s a) ∧
      Lead2 (merge l s a) w ∧ (after l s a).2 = merge l s a := by
  rcases after_cases l s a with ⟨h1, h2, h3⟩ | ⟨-, -, h3⟩ | ⟨-, h3⟩ <;> rw [h3] at h ⊢ <;>
    simp only [Ph.done.injEq, reduceCtorEq] at h
  subst h; exact ⟨rfl, h1, h2, rfl⟩

/-- Only the value `vstar` can get a new lap. -/
lemma after_snd_eq {l s : Laps k} {a : Fin m → Laps k} {u : Fin k}
    (hu : u ≠ vstar (merge l s a)) : (after l s a).2 u = merge l s a u := by
  rcases after_cases l s a with ⟨-, -, h3⟩ | ⟨-, -, h3⟩ | ⟨-, h3⟩ <;> rw [h3]
  simp [Function.update_of_ne hu]

lemma after_snd_le {l s : Laps k} {a : Fin m → Laps k} (u : Fin k) :
    (after l s a).2 u ≤ merge l s a u + 1 := by
  by_cases hu : u = vstar (merge l s a)
  · rcases after_cases l s a with ⟨-, -, h3⟩ | ⟨-, -, h3⟩ | ⟨-, h3⟩ <;> rw [h3] <;> subst hu <;> simp
  · rw [after_snd_eq hu]; omega

/-- A value with lap `0` in the merged vector cannot be decided or promoted, provided some
value has a positive lap. -/
lemma after_zero {l s : Laps k} {a : Fin m → Laps k} {u v : Fin k} (hu : merge l s a u = 0)
    (hv : 0 < merge l s a v) : (after l s a).2 u = 0 ∧ (after l s a).1 ≠ .done u := by
  have hne : u ≠ vstar (merge l s a) := by
    rintro rfl; have := le_vstar (merge l s a) v; omega
  refine ⟨by rw [after_snd_eq hne, hu], fun hd => hne (after_done hd).1⟩

variable [Fintype P]

/-- Lemma 8.3 of [EGSZ16] in invariant form: every scan returns laps at least the floor `F`. -/
lemma Inv.floor (hP : Fintype.card P ≤ m + 1) (h : Inv a g) (q : P) :
    g.F ≤ merge (a.loc q).l (a.loc q).s a.mem := by
  by_cases hl : g.F ≤ (a.loc q).l
  · exact le_trans hl (le_merge_l _ _ _)
  by_cases hs : g.F ≤ (a.loc q).s
  · exact le_trans hs (le_merge_s _ _ _)
  by_cases hw : ∃ j, j ∉ g.wloc
  · obtain ⟨j, hj⟩ := hw; exact le_trans (h.good j hj) (le_merge_a _ _ _ j)
  exfalso
  have hwl : g.wloc = univ := eq_univ_of_forall fun j => by
    by_contra hj; exact hw ⟨j, hj⟩
  have hcard : g.wloc.card = m := by rw [hwl, card_univ, Fintype.card_fin]
  obtain ⟨r, hr, hrw⟩ := h.wit q
  have hrq : r ≠ q := by rintro rfl; exact hl hr
  have hc := h.count
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  by_cases hqw : q ∈ g.wproc
  · have h1 : g.wproc ⊆ univ.erase r := fun x hx =>
      mem_erase.2 ⟨by rintro rfl; exact hrw hx, mem_univ _⟩
    have h2 := card_le_card h1
    rw [card_erase_of_mem (mem_univ _), card_univ] at h2
    have h3 : 0 < (g.wproc.filter fun q => ¬ g.F ≤ (a.loc q).l ∧ ¬ g.F ≤ (a.loc q).s).card :=
      card_pos.2 ⟨q, mem_filter.2 ⟨hqw, hl, hs⟩⟩
    omega
  · have h1 : g.wproc ⊆ (univ.erase r).erase q := fun x hx =>
      mem_erase.2 ⟨by rintro rfl; exact hqw hx,
        mem_erase.2 ⟨by rintro rfl; exact hrw hx, mem_univ _⟩⟩
    have h2 := card_le_card h1
    rw [card_erase_of_mem (mem_erase.2 ⟨hrq.symm, mem_univ _⟩), card_erase_of_mem (mem_univ _),
      card_univ] at h2
    omega

lemma Inv.scan (hP : Fintype.card P ≤ m + 1) (h : Inv a g) {q : P}
    (hq : (a.loc q).ph = .scan) : AInv (a.scanStep q) := by
  set L := merge (a.loc q).l (a.loc q).s a.mem with hL
  set LL := (after (a.loc q).l (a.loc q).s a.mem).2 with hLL
  set PH := (after (a.loc q).l (a.loc q).s a.mem).1 with hPH
  have hF : g.F ≤ L := h.floor hP q
  have hLl : (a.loc q).l ≤ L := le_merge_l _ _ _
  have hLLL : L ≤ LL := merge_le_after _ _ _
  have hqi : (a.loc q).ph ≠ .idle := by rw [hq]; simp
  have hpos : 1 ≤ L (a.loc q).inp := (h.inpPos q hqi).trans (hLl _)
  have hph : ∀ r, ((a.scanStep q).loc r).ph = if r = q then PH else (a.loc r).ph :=
    fun r => ACfg.scanStep_ph a q r
  have hl : ∀ r, ((a.scanStep q).loc r).l = if r = q then LL else (a.loc r).l :=
    fun r => ACfg.scanStep_l a q r
  have hPHi : PH ≠ .idle := after_ph_ne_idle _ _ _
  -- common parts
  have c_valid : ∀ u, (∀ r, ((a.scanStep q).loc r).ph ≠ .idle → ((a.scanStep q).loc r).inp ≠ u) →
      Bnd (a.scanStep q) u 0 ∧ ∀ r, ((a.scanStep q).loc r).ph ≠ .done u := by
    intro u hu
    have hu' : ∀ r, (a.loc r).ph ≠ .idle → (a.loc r).inp ≠ u := by
      intro r hr
      have := hu r (by rw [hph]; split_ifs <;> first | exact hPHi | exact hr)
      rwa [ACfg.scanStep_inp] at this
    obtain ⟨hB, hD⟩ := h.valid u hu'
    have hLu : L u = 0 := Nat.le_zero.1 (hB.merge_le q)
    obtain ⟨h1, h2⟩ := after_zero hLu (by omega : 0 < L (a.loc q).inp)
    refine ⟨hB.scanStep q (by rw [h1]), fun r hr => ?_⟩
    rw [hph] at hr; split_ifs at hr
    · exact h2 hr
    · exact hD r hr
  have c_idle0 : ∀ r, ((a.scanStep q).loc r).ph = .idle →
      ((a.scanStep q).loc r).l = 0 ∧ ((a.scanStep q).loc r).s = 0 := by
    intro r hr
    rw [hph] at hr; split_ifs at hr with hrq
    · exact absurd hr hPHi
    · rw [hl, ite_eq_right hrq, ACfg.scanStep_s]; exact h.idle0 r hr
  have c_inpPos : ∀ r, ((a.scanStep q).loc r).ph ≠ .idle →
      1 ≤ ((a.scanStep q).loc r).l ((a.scanStep q).loc r).inp := by
    intro r hr
    rw [hl, ACfg.scanStep_inp]; split_ifs with hrq
    · subst hrq; exact hpos.trans (hLLL _)
    · rw [hph, ite_eq_right hrq] at hr; exact h.inpPos r hr
  rcases after_cases' (a.loc q).l (a.loc q).s a.mem L hL with ⟨hall, hlead, hafter⟩ |
    ⟨hall, hlead, hafter⟩ | ⟨hne, hafter⟩
  · -- all-equal scan with a 2-lap leader: decide `vstar L`
    have hPH' : PH = .done (vstar L) := by rw [hPH, hafter]
    have hLL' : LL = L := by rw [hLL, hafter]
    have hbndL : ∀ u, Bnd (a.scanStep q) u (L u + 1) := fun u =>
      ((h.bnd u).mono (b' := L u + 1) (by have : g.F u ≤ L u := hF u; omega)).scanStep q (by rw [← hLL, hLL']; omega)
    have hreset : ∀ win : Option (Fin k × Laps k), (win = none → ∀ r w,
        ((a.scanStep q).loc r).ph ≠ .done w) → (∀ v F0, win = some (v, F0) →
        (∀ u, u ≠ v → F0 u + 2 ≤ F0 v) ∧ F0 ≤ L ∧ (∀ u, u ≠ v → Bnd (a.scanStep q) u (F0 u + 1)) ∧
        ∀ r w, ((a.scanStep q).loc r).ph = .done w → w = v) →
        AInv (a.scanStep q) := by
      intro win h1 h2
      refine ⟨⟨L, ∅, ∅, win⟩, ?_⟩
      constructor
      · intro j _; rw [ACfg.scanStep_mem, hall j]
      · simp
      · intro _; exact ⟨q, by rw [hl, ite_eq_left rfl, hLL'], by simp⟩
      · simp
      · simp
      · exact hbndL
      · exact h1
      · exact h2
      · exact c_valid
      · exact c_idle0
      · exact c_inpPos
    cases hw : g.win with
    | none =>
      refine hreset (some (vstar L, L)) (by simp) fun v F0 hv => ?_
      simp only [Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      refine ⟨hlead, le_rfl, fun u _ => hbndL u, fun r w hr => ?_⟩
      rw [hph] at hr; split_ifs at hr with hrq
      · rw [hPH'] at hr; cases hr; rfl
      · exact absurd hr (h.winNone hw r w)
    | some vF =>
      obtain ⟨v, F0⟩ := vF
      obtain ⟨w1, w2, w3, w4⟩ := h.winSome v F0 hw
      have hvw : vstar L = v := by
        by_contra hne
        have h5 := hlead v (Ne.symm hne)
        have h6 := (w3 _ hne).merge_le q
        have h7 := w1 _ hne
        have h8 : F0 v ≤ g.F v := w2 v
        have h9 : g.F v ≤ L v := hF v
        rw [← hL] at h6
        omega
      refine hreset (some (v, F0)) (by simp) fun v' F0' hv => ?_
      simp only [Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      refine ⟨w1, le_trans w2 hF, fun u hu => (w3 u hu).scanStep q ?_, fun r w hr => ?_⟩
      · rw [← hLL, hLL']; exact (w3 u hu).merge_le q
      · rw [hph] at hr; split_ifs at hr with hrq
        · rw [hPH'] at hr; cases hr; exact hvw
        · exact w4 r w hr
  · -- all-equal scan without a leader: promote `vstar L`
    have hPH' : PH = .swap 0 := by rw [hPH, hafter]
    refine ⟨⟨L, ∅, ∅, g.win⟩, ?_⟩
    constructor
    · intro j _; rw [ACfg.scanStep_mem, hall j]
    · simp
    · intro _; exact ⟨q, by rw [hl, ite_eq_left rfl]; exact hLLL, by simp⟩
    · simp
    · simp
    · intro u
      exact ((h.bnd u).mono (b' := L u + 1) (by have : g.F u ≤ L u := hF u; omega)).scanStep q (by rw [← hLL]; exact after_snd_le u)
    · intro hw r w hr
      rw [hph] at hr; split_ifs at hr with hrq
      · rw [hPH'] at hr; cases hr
      · exact h.winNone hw r w hr
    · intro v F0 hw
      obtain ⟨w1, w2, w3, w4⟩ := h.winSome v F0 hw
      have hvw : vstar L = v := by
        by_contra hne
        have h5 := le_vstar L v
        have h6 := (w3 _ hne).merge_le q
        have h7 := w1 _ hne
        have h8 : F0 v ≤ g.F v := w2 v
        have h9 : g.F v ≤ L v := hF v
        rw [← hL] at h6
        omega
      refine ⟨w1, le_trans w2 hF, fun u hu => (w3 u hu).scanStep q ?_, fun r w hr => ?_⟩
      · rw [after_snd_eq (by rw [← hL, hvw]; exact hu)]; exact (w3 u hu).merge_le q
      · rw [hph] at hr; split_ifs at hr with hrq
        · rw [hPH'] at hr; cases hr
        · exact w4 r w hr
    · exact c_valid
    · exact c_idle0
    · exact c_inpPos
  · -- not all-equal: swap `L` into the first differing location
    have hPH' : PH = .swap (firstNe a.mem L) := by rw [hPH, hafter]
    have hLL' : LL = L := by rw [hLL, hafter]
    refine ⟨g, ?_⟩
    constructor
    · intro j hj; rw [ACfg.scanStep_mem]; exact h.good j hj
    · have hsub : (g.wproc.filter fun r => ¬ g.F ≤ ((a.scanStep q).loc r).l ∧
          ¬ g.F ≤ ((a.scanStep q).loc r).s) ⊆
          (g.wproc.filter fun r => ¬ g.F ≤ (a.loc r).l ∧ ¬ g.F ≤ (a.loc r).s) := by
        intro r hr
        simp only [mem_filter, hl, ACfg.scanStep_s] at hr ⊢
        split_ifs at hr with hrq
        · exact absurd (hLL' ▸ hF) hr.2.1
        · exact hr
      exact (Nat.add_le_add_left (card_le_card hsub) _).trans h.count
    · intro r
      obtain ⟨r', hr', hrw⟩ := h.wit r
      refine ⟨r', ?_, hrw⟩
      rw [hl]; split_ifs with hrq
      · subst hrq; exact hr'.trans (hLl.trans hLLL)
      · exact hr'
    · intro r hr hrl
      rw [hl] at hrl; rw [hph]; split_ifs at hrl ⊢ with hrq
      · exact absurd (hLL' ▸ hF) hrl
      · exact h.wscan r hr hrl
    · intro r hr
      rw [hph]; split_ifs
      · exact hPHi
      · exact h.wact r hr
    · intro u
      exact (h.bnd u).scanStep q (by rw [← hLL, hLL']; exact (h.bnd u).merge_le q)
    · intro hw r w hr
      rw [hph] at hr; split_ifs at hr with hrq
      · rw [hPH'] at hr; cases hr
      · exact h.winNone hw r w hr
    · intro v F0 hw
      obtain ⟨w1, w2, w3, w4⟩ := h.winSome v F0 hw
      refine ⟨w1, w2, fun u hu => (w3 u hu).scanStep q ?_, fun r w hr => ?_⟩
      · rw [← hLL, hLL']; exact (w3 u hu).merge_le q
      · rw [hph] at hr; split_ifs at hr with hrq
        · rw [hPH'] at hr; cases hr
        · exact w4 r w hr
    · exact c_valid
    · exact c_idle0
    · exact c_inpPos

lemma AInv.scan (hP : Fintype.card P ≤ m + 1) (h : AInv a) {q : P}
    (hq : (a.loc q).ph = .scan) : AInv (a.scanStep q) := by
  obtain ⟨g, hg⟩ := h; exact hg.scan hP hq

end Scan

/-! ### Consequences: agreement and validity -/

/-- Agreement (Lemma 8.5 of [EGSZ16]): all decided values are equal. -/
lemma AInv.agree (h : AInv a) {p q : P} {v w : Fin k} (hp : (a.loc p).ph = .done v)
    (hq : (a.loc q).ph = .done w) : v = w := by
  obtain ⟨g, hg⟩ := h
  cases hw : g.win with
  | none => exact absurd hp (hg.winNone hw p v)
  | some x =>
    obtain ⟨x1, x2⟩ := x
    obtain ⟨-, -, -, h4⟩ := hg.winSome x1 x2 hw
    rw [h4 p v hp, h4 q w hq]

/-- Validity: a decided value is the input of some invoked process. -/
lemma AInv.valid (h : AInv a) {p : P} {v : Fin k} (hp : (a.loc p).ph = .done v) :
    ∃ q, (a.loc q).ph ≠ .idle ∧ (a.loc q).inp = v := by
  obtain ⟨g, hg⟩ := h
  by_contra hc
  push Not at hc
  exact (hg.valid v hc).2 p hp

end Cslib.SharedMemory.ComplexityHierarchy.SwapRead
