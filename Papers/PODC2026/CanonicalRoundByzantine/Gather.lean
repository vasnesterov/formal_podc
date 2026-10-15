import Mathlib

/-!
# Algorithm 4 of [AFW26]: connected consensus from gather (and approximate agreement)

Formalization of Sections 4.2 and 5 of

> H. Attiya, I. Flam, J. L. Welch. *Why Canonical-Round Algorithms Fail for Optimal Byzantine
> Resilience.* PODC 2026.

This is the *positive* side of the paper: Algorithm 4 solves `R`-connected consensus for `n > 3f`
using a gather subroutine `G` and (for `R ≥ 2`) an approximate agreement subroutine `AA` with
`ε = 1`, and it preserves the binding property of gather.

## Modelling

* The subroutines are **black boxes given by their specifications**: an execution of Algorithm 4
  is abstracted to the family of all local variables of all processes (`Run`): the inputs `x`, the
  outputs `S` of the first gather (line 1), the branch `v₁` of line 2, the outputs `T` of the second
  gather (line 4), the branch `v₂` of line 5, the AA input `r` (line 6) and the AA output `y` (line 7).
  A run is *admissible* (`Phase1`, `Phase2`) when the gather outputs satisfy `GatherSpec`, the AA
  outputs satisfy `AASpec`, and the local variables are computed according to lines 2, 5, 6. The
  decisions are then a function of the run (`decision`, lines 3 and 8).
* "if some `v ∈ V` appears `θ` times in `S` then `vᵢ ← v` else `vᵢ ← ⊥`" is modelled as a
  **relation** (`Line2`, `Line5`) admitting *every* choice of `v` the code allows (no choice
  function). "appears `θ` times" is read as "at least `θ` times". `⊥` is `none : Option V`.
* Processes `P` form a finite type, `n = Fintype.card P`; the Byzantine processes form a set `F`
  with `F.card ≤ f`. Nothing is assumed about the local variables of faulty processes.
* Grades are integers (`ℤ`), `gᵢ = ⌈yᵢ⌉` (`Int.ceil`); we prove `0 ≤ gᵢ ≤ R`.
* **Termination** is not modelled: Algorithm 4 consists of (at most) three subroutine calls and
  local computation, so it terminates whenever the subroutines do (as the paper says in Theorems
  14 and 18). Only the safety properties (agreement, validity, decisions in `D`) are proved.
* **Binding** (Theorem 19): the execution prefix `α` ending when the first correct process returns
  from the first gather is abstracted by the common core `SC` of the first gather that the binding
  property of gather fixes at the end of `α`; an "extension" of `α` is any admissible run whose
  first-gather outputs (of correct processes) all contain `SC`. We prove that the non-`⊥` branch
  of every correct decision in every extension is one value `v*` determined by `SC` alone.

## Notes on the paper (see `differencies.md`)

* Gather agreement must also hold for `i = j` (equivalently, a correct process's output contains at
  most one pair per process id). This is used (only) in validity (ii) ("all elements of `Sᵢ` for
  correct processes, of which there are at least `|Sᵢ| - f`"). Without it, validity fails:
  `validity_fails_without_self_agreement`.
* Gather agreement (across processes) is otherwise never used.
* Lemma 17 needs neither Lemma 16 nor `|F| ≤ f` (only that some value appears `f + 1` times in
  `Tᵢ`); the identification `vᵢ = u` via Lemma 16 in its proof is not needed for the statement.
* Theorem 19 holds for every `R` and does not depend on the inputs: the branch is determined by
  the core `SC` alone (`branch_heavy_in_core`).
* `|Sᵢ| ≥ n - f` (Prop. 13) follows from the common core.
* Lemma 11 holds for every `SC ⊆ Sᵢ` (no size assumption); Prop. 12 only needs `2f < |SC|`.
* `|⌈a⌉ - ⌈b⌉| ≤ 1` from `|a - b| ≤ 1` (used tacitly in Theorem 18) is `abs_ceil_sub_ceil_le`.
* The paper does not argue that decisions lie in `D` (`1 ≤ g ≤ R` for non-`⊥` decisions); this
  follows from AA validity since the AA inputs are in `{0, R}` (`ceil_y_mem`).
-/

namespace Podc2026.CanonicalRound.Gather

open Finset

/-! ### Counting occurrences of values in sets of (process id, value) pairs -/

section Counting

variable {P W : Type*} [DecidableEq P] [DecidableEq W]

/-- `#(S, w)`: the number of pairs of `S` carrying the value `w` (proof of Lemma 11). -/
def cnt (S : Finset (P × W)) (w : W) : ℕ := (S.filter (fun p => p.2 = w)).card

omit [DecidableEq P] in
-- CSLib candidate
theorem cnt_mono {S S' : Finset (P × W)} (h : S ⊆ S') (w : W) : cnt S w ≤ cnt S' w :=
  card_le_card (filter_subset_filter _ h)

/-- Lemma 11 of [AFW26]. If `w` appears at least `|S| - f` times in `S` and `SC ⊆ S`, then `w`
appears at least `|SC| - f` times in `SC`. (The paper states it for a gather output `Sᵢ` and its
common core `SC`; only `SC ⊆ Sᵢ` is used.) -/
theorem lemma11 {S SC : Finset (P × W)} {f : ℕ} {w : W} (hsub : SC ⊆ S)
    (h : S.card - f ≤ cnt S w) : SC.card - f ≤ cnt SC w := by
  have h1 : S.filter (fun p => p.2 = w) ⊆ SC.filter (fun p => p.2 = w) ∪ (S \ SC) := by
    intro p hp
    simp only [mem_filter, mem_union, mem_sdiff] at hp ⊢
    by_cases hpc : p ∈ SC
    · exact Or.inl ⟨hpc, hp.2⟩
    · exact Or.inr ⟨hp.1, hpc⟩
  have h2 := (card_le_card h1).trans (card_union_le _ _)
  rw [card_sdiff_of_subset hsub] at h2
  have h3 := card_le_card hsub
  unfold cnt at h ⊢
  omega

/-- Prop. 12 of [AFW26], general form: if `2f < |SC|`, at most one value appears at least
`|SC| - f` times in `SC`. -- CSLib candidate -/
theorem heavy_unique {SC : Finset (P × W)} {f : ℕ} (hf : 2 * f < SC.card) {u w : W}
    (hu : SC.card - f ≤ cnt SC u) (hw : SC.card - f ≤ cnt SC w) : u = w := by
  by_contra huw
  have hdisj : Disjoint (SC.filter (fun p => p.2 = u)) (SC.filter (fun p => p.2 = w)) := by
    rw [disjoint_filter]
    intro p _ hpu hpw
    exact huw (hpu.symm.trans hpw)
  have := card_le_card (union_subset (filter_subset (fun p : P × W => p.2 = u) SC)
    (filter_subset (fun p : P × W => p.2 = w) SC))
  rw [card_union_of_disjoint hdisj] at this
  unfold cnt at hu hw
  omega

/-- Proposition 12 of [AFW26]. If `|SC| = n - f` and `n > 3f`, at most one value appears
`|SC| - f` times in `SC`. -/
theorem prop12 {n f : ℕ} (hn : 3 * f < n) {SC : Finset (P × W)} (hSC : SC.card = n - f)
    {u w : W} (hu : SC.card - f ≤ cnt SC u) (hw : SC.card - f ≤ cnt SC w) : u = w :=
  heavy_unique (by omega) hu hw

/-- If a value appears more than `|F|` times in a set of pairs, it appears in a pair whose process
is not in `F` (pairs with the same value have distinct process ids). -- CSLib candidate -/
theorem exists_not_mem_of_cnt {S : Finset (P × W)} {F : Finset P} {w : W}
    (h : F.card < cnt S w) : ∃ j, j ∉ F ∧ (j, w) ∈ S := by
  by_contra hcon
  push Not at hcon
  have hsub : (S.filter (fun p => p.2 = w)).image Prod.fst ⊆ F := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hj
    rw [mem_filter] at hp
    by_contra hjF
    exact hcon p.1 hjF (by rw [← hp.2]; exact hp.1)
  have hinj : Set.InjOn Prod.fst (S.filter (fun p => p.2 = w) : Set (P × W)) := by
    intro p hp q hq hpq
    simp only [coe_filter, Set.mem_ofPred_eq] at hp hq
    exact Prod.ext hpq (hp.2.trans hq.2.symm)
  have := card_le_card hsub
  rw [card_image_of_injOn hinj] at this
  unfold cnt at h
  omega

/-- If no process id occurs in two pairs of `S` with different values, and every pair of `S` whose
process is outside `F` carries the value `w`, then `w` appears at least `|S| - |F|` times.
-- CSLib candidate -/
theorem cnt_ge_of_functional {S : Finset (P × W)} {F : Finset P} {w : W}
    (hfun : ∀ k a b, (k, a) ∈ S → (k, b) ∈ S → a = b)
    (hcorr : ∀ j a, j ∉ F → (j, a) ∈ S → a = w) : S.card - F.card ≤ cnt S w := by
  have hsub : (S.filter (fun p => ¬ p.2 = w)).image Prod.fst ⊆ F := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hj
    rw [mem_filter] at hp
    by_contra hjF
    exact hp.2 (hcorr p.1 p.2 hjF hp.1)
  have hinj : Set.InjOn Prod.fst (S.filter (fun p => ¬ p.2 = w) : Set (P × W)) := by
    intro p hp q hq hpq
    simp only [coe_filter, Set.mem_ofPred_eq] at hp hq
    exact Prod.ext hpq (hfun p.1 p.2 q.2 hp.1 (by rw [hpq]; exact hq.1))
  have h1 := card_le_card hsub
  rw [card_image_of_injOn hinj] at h1
  have h2 := card_filter_add_card_filter_not (s := S) (fun p => p.2 = w)
  unfold cnt
  omega

end Counting

/-- `|⌈a⌉ - ⌈b⌉| ≤ 1` whenever `|a - b| ≤ 1`. -- CSLib candidate -/
theorem abs_ceil_sub_ceil_le {a b : ℝ} (h : |a - b| ≤ 1) : |⌈a⌉ - ⌈b⌉| ≤ 1 := by
  rw [abs_le] at h ⊢
  have h1 : ⌈a⌉ ≤ ⌈b⌉ + 1 := by
    rw [← Int.ceil_add_one]; exact Int.ceil_le_ceil (by linarith)
  have h2 : ⌈b⌉ ≤ ⌈a⌉ + 1 := by
    rw [← Int.ceil_add_one]; exact Int.ceil_le_ceil (by linarith)
  constructor <;> linarith

/-! ### Specifications of the subroutines and of connected consensus -/

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Specification of gather (Section 4.2 of [AFW26]); `x` are the inputs, `S i` the output of
process `i`, `F` the faulty processes. Termination is not modelled. Agreement is required also for
`i = j` (the paper: "for any `k`, if `pᵢ` and `pⱼ` are correct …"). -/
structure GatherSpec {W : Type*} (f : ℕ) (F : Finset P) (x : P → W)
    (S : P → Finset (P × W)) : Prop where
  /-- Agreement. -/
  agreement : ∀ i j k a b, i ∉ F → j ∉ F → (k, a) ∈ S i → (k, b) ∈ S j → a = b
  /-- Validity. -/
  validity : ∀ i j a, i ∉ F → j ∉ F → (j, a) ∈ S i → a = x j
  /-- Common core. -/
  commonCore : ∃ SC : Finset (P × W), SC.card = Fintype.card P - f ∧ ∀ i, i ∉ F → SC ⊆ S i

/-- Specification of approximate agreement on `ℝ` with `ε = 1`: inputs `r`, outputs `y`.
Validity: every correct output lies between two correct inputs. -/
structure AASpec (F : Finset P) (r y : P → ℝ) : Prop where
  /-- Validity. -/
  validity : ∀ i, i ∉ F → (∃ j, j ∉ F ∧ r j ≤ y i) ∧ (∃ j, j ∉ F ∧ y i ≤ r j)
  /-- `1`-Agreement. -/
  agreement : ∀ i j, i ∉ F → j ∉ F → |y i - y j| ≤ 1

/-- `R`-connected consensus (Section 2 of [AFW26]) for inputs `x` and decisions `d`
(`(none, 0)` is `(⊥, 0)`). -/
structure ConnectedConsensus {V : Type*} (R : ℕ) (F : Finset P) (x : P → V)
    (d : P → Option V × ℤ) : Prop where
  /-- Decisions lie in `D = {(v, g) | v ∈ V, 1 ≤ g ≤ R} ∪ {(⊥, 0)}`. -/
  mem_D : ∀ i, i ∉ F → d i = (none, 0) ∨ ∃ v, (d i).1 = some v ∧ 1 ≤ (d i).2 ∧ (d i).2 ≤ R
  /-- Agreement on grades. -/
  agreement_grade : ∀ i j, i ∉ F → j ∉ F → |(d i).2 - (d j).2| ≤ 1
  /-- Agreement on branches: equal unless one is `⊥`. -/
  agreement_branch : ∀ i j, i ∉ F → j ∉ F → (d i).1 = none ∨ (d j).1 = none ∨ (d i).1 = (d j).1
  /-- Validity: a non-`⊥` branch is the input of a correct process. -/
  validity_branch : ∀ i v, i ∉ F → (d i).1 = some v → ∃ j, j ∉ F ∧ x j = v
  /-- Validity: if all correct inputs are equal, the grade is `R`. -/
  validity_grade : (∀ i j, i ∉ F → j ∉ F → x i = x j) → ∀ i, i ∉ F → (d i).2 = R

/-! ### Algorithm 4 -/

variable {V : Type*} [DecidableEq V]

/-- Line 2 of Algorithm 4 (branch part): `vᵢ` is a value appearing `|Sᵢ| - f` times in `Sᵢ`, or
`⊥` if there is none. -/
def Line2 (f : ℕ) (S : Finset (P × V)) : Option V → Prop
  | some v => S.card - f ≤ cnt S v
  | none => ∀ v, ¬ S.card - f ≤ cnt S v

/-- Line 5 of Algorithm 4: `vᵢ` is a value `v ∈ V` appearing `f + 1` times in `Tᵢ`, or `⊥`. -/
def Line5 (f : ℕ) (T : Finset (P × Option V)) : Option V → Prop
  | some v => f + 1 ≤ cnt T (some v)
  | none => ∀ v, ¬ f + 1 ≤ cnt T (some v)

/-- Line 6 of Algorithm 4: `rᵢ = R` if some `v ∈ V` appears `|Tᵢ| - f` times in `Tᵢ`, else `0`. -/
def Line6 (R f : ℕ) (T : Finset (P × Option V)) (r : ℝ) : Prop :=
  ((∃ v, T.card - f ≤ cnt T (some v)) ∧ r = R) ∨ ((¬ ∃ v, T.card - f ≤ cnt T (some v)) ∧ r = 0)

variable (P V) in
/-- The local variables of all processes in an execution of Algorithm 4. -/
structure Run where
  /-- Inputs `xᵢ`. -/
  x : P → V
  /-- Line 1: output `Sᵢ` of the first gather. -/
  S : P → Finset (P × V)
  /-- Line 2: branch `vᵢ` (the grade of line 2 is `1` iff `vᵢ ≠ ⊥`). -/
  v₁ : P → Option V
  /-- Line 4: output `Tᵢ` of the second gather (on inputs `v₁`). -/
  T : P → Finset (P × Option V)
  /-- Line 5: branch `vᵢ`. -/
  v₂ : P → Option V
  /-- Line 6: input `rᵢ` of AA. -/
  r : P → ℝ
  /-- Line 7: output of AA. -/
  y : P → ℝ

/-- Lines 1–2 are executed correctly (first gather satisfies its spec). -/
structure Phase1 (f : ℕ) (F : Finset P) (ρ : Run P V) : Prop where
  gather : GatherSpec f F ρ.x ρ.S
  line2 : ∀ i, i ∉ F → Line2 f (ρ.S i) (ρ.v₁ i)

/-- Lines 4–7 are executed correctly (for `R ≥ 2`): the second gather (with inputs `v₁`) and AA
(with inputs `r`) satisfy their specs. -/
structure Phase2 (R f : ℕ) (F : Finset P) (ρ : Run P V) : Prop where
  gather : GatherSpec f F ρ.v₁ ρ.T
  line5 : ∀ i, i ∉ F → Line5 f (ρ.T i) (ρ.v₂ i)
  line6 : ∀ i, i ∉ F → Line6 R f (ρ.T i) (ρ.r i)
  aa : AASpec F ρ.r ρ.y

/-- Lines 3 and 8 of Algorithm 4: the decision of process `i`. For `R = 1` it is `(vᵢ, gᵢ)` of
line 2; otherwise `gᵢ = ⌈yᵢ⌉` and the decision is `(⊥, 0)` if `gᵢ = 0`, else `(vᵢ, gᵢ)` with
`vᵢ` of line 5. -/
noncomputable def decision (R : ℕ) (ρ : Run P V) (i : P) : Option V × ℤ :=
  if R = 1 then (ρ.v₁ i, if ρ.v₁ i = none then 0 else 1)
  else if ⌈ρ.y i⌉ = 0 then (none, 0) else (ρ.v₂ i, ⌈ρ.y i⌉)

/-! ### Facts about gather outputs -/

section Facts

variable {W : Type*} [DecidableEq W] {f : ℕ} {F : Finset P} {x : P → W} {S : P → Finset (P × W)}

/-- Proposition 13 of [AFW26]. If `w` appears `|Sᵢ| - f` times in the gather output `Sᵢ` of a
correct process, then `w` is the input of a correct process. (`|Sᵢ| ≥ n - f` comes from the common
core.) -/
theorem prop13 (hn : 3 * f < Fintype.card P) (hF : F.card ≤ f) (hG : GatherSpec f F x S)
    {i : P} (hi : i ∉ F) {w : W} (h : (S i).card - f ≤ cnt (S i) w) : ∃ j, j ∉ F ∧ x j = w := by
  obtain ⟨SC, hSC, hsub⟩ := hG.commonCore
  have := card_le_card (hsub i hi)
  obtain ⟨j, hj, hjS⟩ := exists_not_mem_of_cnt (F := F) (S := S i) (w := w) (by omega)
  exact ⟨j, hj, (hG.validity i j w hi hj hjS).symm⟩

/-- In a gather output of a correct process, if all correct inputs equal `w`, then `w` appears
`|Sᵢ| - f` times (uses agreement for `i = j`). -/
theorem heavy_of_inputs_eq (hF : F.card ≤ f) (hG : GatherSpec f F x S) {i : P} (hi : i ∉ F)
    {w : W} (hx : ∀ j, j ∉ F → x j = w) : (S i).card - f ≤ cnt (S i) w := by
  have := cnt_ge_of_functional (F := F) (w := w)
    (fun k a b ha hb => hG.agreement i i k a b hi hi ha hb)
    (fun j a hj hja => (hG.validity i j a hi hj hja).trans (hx j hj))
  omega

end Facts

/-! ### Theorem 14: the case `R = 1` (crusader agreement) -/

variable {f : ℕ} {F : Finset P} {ρ : Run P V}

/-- A value heavy in a correct first-gather output is heavy in any common core. -/
theorem heavy_core_of_v₁ {SC : Finset (P × V)} (hsub : ∀ i, i ∉ F → SC ⊆ ρ.S i)
    (h1 : Phase1 f F ρ) {i : P} (hi : i ∉ F) {v : V} (hv : ρ.v₁ i = some v) :
    SC.card - f ≤ cnt SC v := by
  have := h1.line2 i hi
  rw [hv] at this
  exact lemma11 (hsub i hi) this

/-- Two correct processes with non-`⊥` branches in line 2 have the same branch
(Lemma 11 + Proposition 12). -/
theorem v₁_agree (hn : 3 * f < Fintype.card P) (h1 : Phase1 f F ρ) {i j : P} (hi : i ∉ F)
    (hj : j ∉ F) {u v : V} (hu : ρ.v₁ i = some u) (hv : ρ.v₁ j = some v) : u = v := by
  obtain ⟨SC, hSC, hsub⟩ := h1.gather.commonCore
  exact prop12 hn hSC (heavy_core_of_v₁ hsub h1 hi hu) (heavy_core_of_v₁ hsub h1 hj hv)

/-- If all correct inputs are equal to `v`, every correct process sets `vᵢ = v` in line 2. -/
theorem v₁_eq_of_inputs_eq (hn : 3 * f < Fintype.card P) (hF : F.card ≤ f) (h1 : Phase1 f F ρ)
    {v : V} (hx : ∀ j, j ∉ F → ρ.x j = v) {i : P} (hi : i ∉ F) : ρ.v₁ i = some v := by
  have hheavy := heavy_of_inputs_eq hF h1.gather hi hx
  have hl := h1.line2 i hi
  cases hvi : ρ.v₁ i with
  | none => rw [hvi] at hl; exact absurd hheavy (hl v)
  | some u =>
    rw [hvi] at hl
    obtain ⟨SC, hSC, hsub⟩ := h1.gather.commonCore
    rw [prop12 hn hSC (lemma11 (hsub i hi) hl) (lemma11 (hsub i hi) hheavy)]

/-- Theorem 14 of [AFW26]. For `n > 3f`, Algorithm 4 with `R = 1` solves connected consensus
(i.e. crusader agreement). Termination is immediate from that of gather and not modelled. -/
theorem theorem14 (hn : 3 * f < Fintype.card P) (hF : F.card ≤ f) (h1 : Phase1 f F ρ) :
    ConnectedConsensus 1 F ρ.x (decision 1 ρ) where
  mem_D i _ := by
    simp only [decision, ite_true]
    cases ρ.v₁ i <;> simp
  agreement_grade i j _ _ := by
    simp only [decision, ite_true]
    split_ifs <;> simp
  agreement_branch i j hi hj := by
    simp only [decision, ite_true]
    cases hu : ρ.v₁ i with
    | none => exact Or.inl rfl
    | some u =>
      cases hv : ρ.v₁ j with
      | none => exact Or.inr (Or.inl rfl)
      | some v => exact Or.inr (Or.inr (by rw [v₁_agree hn h1 hi hj hu hv]))
  validity_branch i v hi hd := by
    simp only [decision, ite_true] at hd
    have := h1.line2 i hi
    rw [hd] at this
    exact prop13 hn hF h1.gather hi this
  validity_grade hx i hi := by
    have := v₁_eq_of_inputs_eq hn hF h1 (fun j hj => hx j i hj hi) hi
    simp [decision, this]

/-! ### Agreement of gather is needed also for `i = j`

The proof of validity (ii) in Theorem 14 counts "the elements of `Sᵢ` for correct processes, of
which there are at least `|Sᵢ| - f`", i.e. it assumes that a faulty process contributes at most one
pair to `Sᵢ`. This holds if gather agreement is applied with `i = j` (or if "a set of distinct
(process id, value) pairs" is read as "with distinct process ids"), but not if agreement is only
required between two *different* correct processes: then `n = 4`, `f = 1`, faulty `p₃` and
`S₀ = {(0,0), (1,0), (2,0), (3,1), (3,2)}`, `S₁ = S₂ = {(0,0), (1,0), (2,0)}` satisfy the weakened
spec, all correct inputs are `0`, yet `p₀` finds no value appearing `|S₀| - f = 4` times and
decides `(⊥, 0)`, violating validity. -/

/-- Gather specification with agreement only between two *distinct* correct processes. -/
structure GatherSpecWeak {W : Type*} (f : ℕ) (F : Finset P) (x : P → W)
    (S : P → Finset (P × W)) : Prop where
  agreement : ∀ i j k a b, i ∉ F → j ∉ F → i ≠ j → (k, a) ∈ S i → (k, b) ∈ S j → a = b
  validity : ∀ i j a, i ∉ F → j ∉ F → (j, a) ∈ S i → a = x j
  commonCore : ∃ SC : Finset (P × W), SC.card = Fintype.card P - f ∧ ∀ i, i ∉ F → SC ⊆ S i

/-- Counterexample: with `GatherSpecWeak` (agreement only for `i ≠ j`), Algorithm 4 with `R = 1`
violates validity, although `n = 4 > 3 = 3f`. -/
theorem validity_fails_without_self_agreement :
    ∃ ρ : Run (Fin 4) (Fin 3), 3 * 1 < Fintype.card (Fin 4) ∧ ({3} : Finset (Fin 4)).card ≤ 1 ∧
      GatherSpecWeak 1 {3} ρ.x ρ.S ∧ (∀ i, i ∉ ({3} : Finset (Fin 4)) → Line2 1 (ρ.S i) (ρ.v₁ i)) ∧
      ¬ ConnectedConsensus 1 {3} ρ.x (decision 1 ρ) := by
  let SC : Finset (Fin 4 × Fin 3) := {(0, 0), (1, 0), (2, 0)}
  let S : Fin 4 → Finset (Fin 4 × Fin 3) := fun i => if i = 0 then SC ∪ {(3, 1), (3, 2)} else SC
  refine ⟨⟨fun _ => 0, S, fun i => if i = 0 then none else some 0, fun _ => ∅, fun _ => none, fun _ => 0, fun _ => 0⟩,
    by decide, by decide, ⟨?_, ?_, ⟨SC, by decide, ?_⟩⟩, ?_, ?_⟩
  · simp only [S, SC]; decide
  · simp only [S, SC]; decide
  · simp only [S, SC]; decide
  · intro i hi
    fin_cases i
    · change Line2 1 (SC ∪ {(3, 1), (3, 2)}) none; simp only [Line2, SC]; decide
    · change Line2 1 SC (some 0); simp only [Line2, SC]; decide
    · change Line2 1 SC (some 0); simp only [Line2, SC]; decide
    · exact absurd (mem_singleton_self _) hi
  · intro h
    have := h.validity_grade (fun _ _ _ _ => rfl) 0 (by decide)
    simp [decision] at this

/-! ### Lemmas 16, 17 and Theorem 18: the case `R ≥ 2` -/

/-- A value `v ∈ V` appearing `f + 1` times in the second-gather output of a correct process is
the line-2 branch of some correct process (validity of gather). -/
theorem exists_v₁_of_T (hF : F.card ≤ f) (h2 : Phase2 R f F ρ) {i : P} (hi : i ∉ F) {v : V}
    (h : f + 1 ≤ cnt (ρ.T i) (some v)) : ∃ k, k ∉ F ∧ ρ.v₁ k = some v := by
  obtain ⟨k, hk, hkT⟩ := exists_not_mem_of_cnt (F := F) (S := ρ.T i) (w := some v) (by omega)
  exact ⟨k, hk, (h2.gather.validity i k _ hi hk hkT).symm⟩

/-- Lemma 16 of [AFW26]. If `v ∈ V` occurs `f + 1` times in `Tᵢ` and `u ∈ V` occurs `f + 1`
times in `Tⱼ` (correct `pᵢ`, `pⱼ`, not necessarily distinct), then `u = v`. -/
theorem lemma16 (hn : 3 * f < Fintype.card P) (hF : F.card ≤ f) (h1 : Phase1 f F ρ)
    (h2 : Phase2 R f F ρ) {i j : P} (hi : i ∉ F) (hj : j ∉ F) {u v : V}
    (hv : f + 1 ≤ cnt (ρ.T i) (some v)) (hu : f + 1 ≤ cnt (ρ.T j) (some u)) : u = v := by
  obtain ⟨k, hk, hkv⟩ := exists_v₁_of_T hF h2 hi hv
  obtain ⟨l, hl, hlu⟩ := exists_v₁_of_T hF h2 hj hu
  exact v₁_agree hn h1 hl hk hlu hkv

omit [DecidableEq P] in
/-- For `R ≥ 1`, the AA inputs of correct processes are in `{0, R}`, hence the AA outputs lie in
`[0, R]` and the grades `⌈yᵢ⌉` lie in `{0, …, R}`. -/
theorem ceil_y_mem (h2 : Phase2 R f F ρ) {i : P} (hi : i ∉ F) :
    0 ≤ ⌈ρ.y i⌉ ∧ ⌈ρ.y i⌉ ≤ R := by
  have hr : ∀ j, j ∉ F → 0 ≤ ρ.r j ∧ ρ.r j ≤ R := by
    intro j hj
    rcases h2.line6 j hj with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
  obtain ⟨⟨j, hj, hjy⟩, ⟨k, hk, hky⟩⟩ := h2.aa.validity i hi
  have h0 := (hr j hj).1
  have hR := (hr k hk).2
  constructor
  · exact Int.ceil_nonneg (by linarith)
  · exact Int.ceil_le.2 (by push_cast; linarith)

/-- Lemma 17 of [AFW26] (key step): if `⌈yᵢ⌉ ≠ 0` then `pᵢ` picks a non-`⊥` branch in line 5. -/
theorem v₂_ne_none (hn : 3 * f < Fintype.card P) (h2 : Phase2 R f F ρ)
    {i : P} (hi : i ∉ F) (hg : ⌈ρ.y i⌉ ≠ 0) : ρ.v₂ i ≠ none := by
  have hpos : 0 < ρ.y i := by
    have := (ceil_y_mem h2 hi).1
    have h : (0 : ℤ) < ⌈ρ.y i⌉ := lt_of_le_of_ne this (Ne.symm hg)
    exact Int.ceil_pos.1 h
  obtain ⟨j, hj, hjy⟩ := (h2.aa.validity i hi).2
  -- some correct `pⱼ` has `rⱼ = R`, hence a value `u` appearing `|Tⱼ| - f` times in `Tⱼ`
  obtain ⟨u, hu⟩ : ∃ u, (ρ.T j).card - f ≤ cnt (ρ.T j) (some u) := by
    rcases h2.line6 j hj with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · rw [h] at hjy; linarith
  obtain ⟨TC, hTC, hsub⟩ := h2.gather.commonCore
  have h11 := lemma11 (hsub j hj) hu
  have hmono := cnt_mono (hsub i hi) (some u)
  have hl := h2.line5 i hi
  intro hnone
  rw [hnone] at hl
  exact hl u (by omega)

/-- Lemma 17 of [AFW26]. If `R ≥ 2` and correct `pᵢ` decides `(v, g)`, then `g = 0 ↔ v = ⊥`. -/
theorem lemma17 (hR : 2 ≤ R) (hn : 3 * f < Fintype.card P) (h2 : Phase2 R f F ρ) {i : P} (hi : i ∉ F) :
    (decision R ρ i).2 = 0 ↔ (decision R ρ i).1 = none := by
  have hR1 : R ≠ 1 := by omega
  simp only [decision, hR1, ite_false]
  split_ifs with hg
  · simp
  · simp [hg, v₂_ne_none hn h2 hi hg]

omit [Fintype P] [DecidableEq P] [DecidableEq V] in
/-- The grade of a correct process for `R ≥ 2` is `⌈yᵢ⌉`. -/
theorem decision_snd (hR : 2 ≤ R) (i : P) : (decision R ρ i).2 = ⌈ρ.y i⌉ := by
  have hR1 : R ≠ 1 := by omega
  simp only [decision, hR1, ite_false]
  split_ifs with hg <;> simp [hg]

/-- Theorem 18 of [AFW26]. For `n > 3f` and `R ≥ 2`, Algorithm 4 solves `R`-connected consensus.
Termination is immediate from that of gather and AA and not modelled. -/
theorem theorem18 (hR : 2 ≤ R) (hn : 3 * f < Fintype.card P) (hF : F.card ≤ f)
    (h1 : Phase1 f F ρ) (h2 : Phase2 R f F ρ) : ConnectedConsensus R F ρ.x (decision R ρ) := by
  have hR1 : R ≠ 1 := by omega
  -- non-`⊥` branches decided by correct processes are line-5 branches
  have hbr : ∀ i v, i ∉ F → (decision R ρ i).1 = some v → f + 1 ≤ cnt (ρ.T i) (some v) := by
    intro i v hi hd
    simp only [decision, hR1, ite_false] at hd
    split_ifs at hd with hg
    simp only at hd
    have := h2.line5 i hi
    rw [hd] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- decisions lie in `D`
    intro i hi
    have hm := ceil_y_mem h2 hi
    simp only [decision, hR1, ite_false]
    split_ifs with hg
    · exact Or.inl rfl
    · right
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (v₂_ne_none hn h2 hi hg)
      exact ⟨v, hv, by omega, hm.2⟩
  · -- agreement on grades: `|⌈yᵢ⌉ - ⌈yⱼ⌉| ≤ 1`
    intro i j hi hj
    rw [decision_snd hR, decision_snd hR]
    exact abs_ceil_sub_ceil_le (h2.aa.agreement i j hi hj)
  · -- agreement on branches: Lemma 16
    intro i j hi hj
    cases hu : (decision R ρ i).1 with
    | none => exact Or.inl rfl
    | some u =>
      cases hv : (decision R ρ j).1 with
      | none => exact Or.inr (Or.inl rfl)
      | some v =>
        refine Or.inr (Or.inr ?_)
        rw [lemma16 hn hF h1 h2 hj hi (hbr j v hj hv) (hbr i u hi hu)]
  · -- validity (i)
    intro i v hi hd
    obtain ⟨k, hk, hkv⟩ := exists_v₁_of_T hF h2 hi (hbr i v hi hd)
    have := h1.line2 k hk
    rw [hkv] at this
    exact prop13 hn hF h1.gather hk this
  · -- validity (ii)
    intro hx i hi
    obtain ⟨v, hv⟩ : ∃ v, ∀ j, j ∉ F → ρ.x j = v := ⟨ρ.x i, fun j hj => hx j i hj hi⟩
    have hv₁ : ∀ j, j ∉ F → ρ.v₁ j = some v := fun j hj => v₁_eq_of_inputs_eq hn hF h1 hv hj
    have hT : ∀ j, j ∉ F → (ρ.T j).card - f ≤ cnt (ρ.T j) (some v) :=
      fun j hj => heavy_of_inputs_eq hF h2.gather hj hv₁
    have hr : ∀ j, j ∉ F → ρ.r j = R := by
      intro j hj
      rcases h2.line6 j hj with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd ⟨v, hT j hj⟩ h
    obtain ⟨⟨j, hj, hjy⟩, ⟨k, hk, hky⟩⟩ := h2.aa.validity i hi
    rw [hr j hj] at hjy
    rw [hr k hk] at hky
    have hy : ρ.y i = R := le_antisymm hky hjy
    rw [decision_snd hR, hy]
    simp

/-! ### Theorem 19: binding -/

/-- Proof of Theorem 19 of [AFW26] (the "even stronger property"): once the common core `SC` of
the first gather is fixed, every non-`⊥` branch decided by a correct process (for any `R`, in any
admissible run whose correct first-gather outputs contain `SC`) appears `|SC| - f` times in `SC`.
For `R ≠ 1` it uses only the validity of the second gather. -/
theorem branch_heavy_in_core (hF : F.card ≤ f) {R : ℕ} {SC : Finset (P × V)}
    (hsub : ∀ i, i ∉ F → SC ⊆ ρ.S i) (h1 : Phase1 f F ρ) (h2 : R ≠ 1 → Phase2 R f F ρ)
    {i : P} (hi : i ∉ F) {u : V} (hd : (decision R ρ i).1 = some u) :
    SC.card - f ≤ cnt SC u := by
  by_cases hR : R = 1
  · simp only [decision, hR, ite_true] at hd
    exact heavy_core_of_v₁ hsub h1 hi hd
  · have h2 := h2 hR
    simp only [decision, hR, ite_false] at hd
    split_ifs at hd with hg
    simp only at hd
    have hl := h2.line5 i hi
    rw [hd] at hl
    obtain ⟨k, hk, hkv⟩ := exists_v₁_of_T hF h2 hi hl
    exact heavy_core_of_v₁ hsub h1 hk hkv

/-- Theorem 19 of [AFW26] (binding). Let `SC` with `|SC| = n - f` be the common core of the first
gather fixed (by the binding property of gather) at the end of the prefix `α` in which the first
correct process returns from the first gather. Then there is a value `v*` (determined by `SC`) such
that in every extension of `α` — every admissible run whose correct first-gather outputs contain
`SC` — no correct process decides `(u, g)` with `u ≠ v*`. -/
theorem theorem19 [Nonempty V] (R : ℕ) (hn : 3 * f < Fintype.card P) (hF : F.card ≤ f)
    (SC : Finset (P × V)) (hSC : SC.card = Fintype.card P - f) :
    ∃ vstar : V, ∀ ρ : Run P V, Phase1 f F ρ → (R ≠ 1 → Phase2 R f F ρ) →
      (∀ i, i ∉ F → SC ⊆ ρ.S i) → ∀ i u g, i ∉ F → decision R ρ i = (some u, g) → u = vstar := by
  by_cases h : ∃ v, SC.card - f ≤ cnt SC v
  · obtain ⟨v, hv⟩ := h
    refine ⟨v, fun ρ h1 h2 hsub i u g hi hd => ?_⟩
    have := branch_heavy_in_core hF hsub h1 h2 hi (u := u) (by rw [hd])
    exact prop12 hn hSC this hv
  · refine ⟨Classical.arbitrary V, fun ρ h1 h2 hsub i u g hi hd => ?_⟩
    exact absurd ⟨u, branch_heavy_in_core hF hsub h1 h2 hi (u := u) (by rw [hd])⟩ h

end Podc2026.CanonicalRound.Gather
