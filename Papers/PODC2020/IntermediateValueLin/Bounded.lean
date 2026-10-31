import Papers.PODC2020.IntermediateValueLin.Canonical
import Mathlib.Data.Fintype.List
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# `(ε, δ)`-bounded objects and Theorem 1 (Section 4 of Rinberg–Keidar)

Randomized algorithms. A randomized object is a family of deterministic objects indexed by the
coin flip vector `c : Ω`; `Ω` carries a probability measure `μ`.

* The sequential specification `{A(c)}` of a randomized object is a family
  `S : Ω → QSpec A.Op A.Resp` of deterministic sequential specifications (Section 2.2/3.3); the
  *ideal* specification `I : QSpec A.Op A.Resp` gives the exact quantity estimated.
* A concurrent randomized algorithm is given by its executions under every coin flip vector,
  `E : Ω → List (Label P A) → Prop` (e.g. `E c = (impl c).Valid`). The paper's schedule `σ`
  fixes the order of all steps and invocations; under its uniform-step-complexity assumption the
  executions of a schedule under different coin flips differ only in the response values, so we
  identify the schedule with the common skeleton history `σ = α?`: the execution "`H(A, c, σ)`"
  is any `α` with `E c α` and `skel α = σ`.

Definitions:
* `SeqBounded` — **Definition 3**: every query of a sequential execution over- (under-)
  estimates the ideal value by more than `ε` with probability at most `δ/2`.
* `RandIVL` — **Definition 2** (IVL for randomized algorithms): for every skeleton history `σ`
  there are two linearizations `L₁`, `L₂` of `σ`, common to all coin flip vectors, sandwiching
  every return value.
* `vmin`, `vmax` — the paper's `v^I_min(H, Q)`, `v^I_max(H, Q)`: extreme ideal values of `Q` over
  all linearizations of the skeleton (`finite_isLinearization` shows they are attained).
* `ConcBounded` — **Definition 4**.

Main result: `theorem1` (**Theorem 1**): an IVL implementation of a sequential `(ε, δ)`-bounded
object is a concurrent `(ε, δ)`-bounded object.

Probabilities are measured with the outer measure `μ` (Lean's `μ s` is defined for every set), so
no measurability of the events is needed; for measurable events this is the usual probability.
The paper compares only queries; we compare all completed operations (the updates of the paper's
objects return a fixed dummy value).
-/

open Cslib.SharedMemory MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace Podc.IntermediateValueLin

/-! ### Finitely many linearizations -/

section Finite

variable {P : Type} [DecidableEq P] {B : ObjSpec}

lemma invoked_proc_mem {σ : List (Label P B)} {x : OpId P} (hx : Invoked σ x) :
    x.1 ∈ σ.map Label.proc := by
  by_contra h
  have : opsOf σ x.1 = [] :=
    opsOf_eq_nil_of_proc_ne fun ℓ hℓ he => h (List.mem_map.2 ⟨ℓ, hℓ, he⟩)
  simp [Invoked, this] at hx

lemma length_opsOf_le (σ : List (Label P B)) (p : P) : (opsOf σ p).length ≤ σ.length :=
  List.length_filterMap_le _ _

/-- Two lists of entries with the same identities, each entry carrying the operation of its
instance in `σ`, are equal. -/
lemma eq_of_map_fst_eq {σ : List (Label P B)} :
    ∀ {L L' : List (OpId P × B.Op)}, L.map Prod.fst = L'.map Prod.fst →
      (∀ y ∈ L, opOf σ y.1 = some y.2) → (∀ y ∈ L', opOf σ y.1 = some y.2) → L = L'
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | y :: L, y' :: L', h, hL, hL' => by
    simp only [List.map_cons, List.cons.injEq] at h
    have h1 := hL y (by simp)
    have h2 := hL' y' (by simp)
    rw [h.1, h2] at h1
    obtain ⟨a, o⟩ := y; obtain ⟨a', o'⟩ := y'
    obtain ⟨rfl, h2'⟩ := h
    simp only at h1
    cases h1
    rw [eq_of_map_fst_eq h2' (fun z hz => hL z (by simp [hz])) (fun z hz => hL' z (by simp [hz]))]

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/History.lean
/-- A finite history has finitely many linearizations. -/
theorem finite_isLinearization (σ : List (Label P B)) : {L | IsLinearization σ L}.Finite := by
  classical
  let F : Finset (OpId P) := (σ.map Label.proc).toFinset ×ˢ Finset.range (σ.length + 1)
  have hF : ∀ L, IsLinearization σ L → ∀ x ∈ L.map Prod.fst, x ∈ F := by
    intro L hL x hx
    have hinv := hL.mem_invoked hx
    simp only [F, Finset.mem_product, List.mem_toFinset, Finset.mem_range]
    exact ⟨invoked_proc_mem hinv, by have := length_opsOf_le σ x.1; simp [Invoked] at hinv; omega⟩
  have hfin : {l : List (OpId P) | l.Nodup ∧ ∀ x ∈ l, x ∈ F}.Finite := by
    refine Set.Finite.subset (s := ⋃ T ∈ F.powerset, {l | l ∈ Multiset.lists T.val})
      (Set.Finite.biUnion F.powerset.finite_toSet fun T _ => ?_) ?_
    · exact (Multiset.lists T.val).toFinset.finite_toSet.subset fun l hl => by simpa using hl
    · rintro l ⟨hnd, hl⟩
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_powerset]
      refine ⟨l.toFinset, fun x hx => hl x (List.mem_toFinset.1 hx), ?_⟩
      rw [Multiset.mem_lists_iff]
      simp [List.toFinset_val, List.dedup_eq_self.2 hnd]
  refine Set.Finite.of_finite_image (f := fun L : List (OpId P × B.Op) => L.map Prod.fst)
    (hfin.subset ?_) ?_
  · rintro _ ⟨L, hL, rfl⟩
    exact ⟨hL.nodup, hF L hL⟩
  · intro L hL L' hL' h
    exact eq_of_map_fst_eq h hL.op_eq hL'.op_eq

end Finite

/-! ### Definitions 2–4 and Theorem 1 -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Type} [DecidableEq P] {A : ObjSpec}
  [ConditionallyCompleteLinearOrder A.Resp] [AddCommMonoid A.Resp] [Sub A.Resp]
  [OrderedSub A.Resp] [AddLeftMono A.Resp]

variable (P) in
/-- **Definition 3** (sequential `(ε, δ)`-bounded object). The randomized sequential specification
`{S c}` implements an `(ε, δ)`-bounded `I` object: for every sequential history (a duplicate-free
sequential skeleton `L`) and every instance `a` in it, with probability at least `1 - δ/2` the
return value is at least the ideal one minus `ε`, and with probability at least `1 - δ/2` at most
the ideal one plus `ε`. -/
def SeqBounded (S : Ω → QSpec A.Op A.Resp) (I : QSpec A.Op A.Resp) (μ : Measure Ω)
    (ε : A.Resp) (δ : ℝ≥0∞) : Prop :=
  ∀ (L : List (OpId P × A.Op)) (a : OpId P), (L.map Prod.fst).Nodup → a ∈ L.map Prod.fst →
    1 - δ / 2 ≤ μ {c | ∀ v w, tau (S c) L a = some v → tau I L a = some w → w - ε ≤ v} ∧
    1 - δ / 2 ≤ μ {c | ∀ v w, tau (S c) L a = some v → tau I L a = some w → v ≤ w + ε}

/-- **Definition 2** (IVL for randomized algorithms). The randomized algorithm with executions
`E c` (under coin flip vector `c`) is an IVL implementation of `{S c}`: for every skeleton history
`σ` there are linearizations `L₁`, `L₂` of `σ` such that, for every coin flip vector `c` and
every execution `α` under `c` with skeleton `σ`, every instance `a` returning `r` in `α` satisfies
`ret(a, τ_{S c}(L₁)) ≤ r ≤ ret(a, τ_{S c}(L₂))`. -/
def RandIVL (S : Ω → QSpec A.Op A.Resp) (E : Ω → List (Label P A) → Prop) : Prop :=
  ∀ σ : List (Label P (skelSpec A)), ∃ L₁ L₂ : List (OpId P × A.Op),
    ∀ c α, E c α → skel α = σ → IsLinearization σ L₁ ∧ IsLinearization σ L₂ ∧
      ∀ a r, respOf α a = some r → ∃ r₁ r₂, tau (S c) L₁ a = some r₁ ∧
        tau (S c) L₂ a = some r₂ ∧ r₁ ≤ r ∧ r ≤ r₂

/-- The values of `a` in the ideal object over all linearizations of the skeleton `σ`. -/
def idealVals (I : QSpec A.Op A.Resp) (σ : List (Label P (skelSpec A))) (a : OpId P) :
    Set A.Resp :=
  {v | ∃ L, IsLinearization σ L ∧ tau I L a = some v}

/-- `v^I_min(H, a)`: the minimum ideal value of `a` over the linearizations of `σ = H?`. -/
noncomputable def vmin (I : QSpec A.Op A.Resp) (σ : List (Label P (skelSpec A))) (a : OpId P) :
    A.Resp := sInf (idealVals I σ a)

/-- `v^I_max(H, a)`: the maximum ideal value of `a` over the linearizations of `σ = H?`. -/
noncomputable def vmax (I : QSpec A.Op A.Resp) (σ : List (Label P (skelSpec A))) (a : OpId P) :
    A.Resp := sSup (idealVals I σ a)

/-- **Definition 4** (concurrent `(ε, δ)`-bounded object). For every schedule (skeleton `σ`) and
instance `a`, with probability at least `1 - δ/2` (over `c`) the value returned by `a` is at least
`v^I_min - ε`, and with probability at least `1 - δ/2` at most `v^I_max + ε`. -/
def ConcBounded (E : Ω → List (Label P A) → Prop) (I : QSpec A.Op A.Resp) (μ : Measure Ω)
    (ε : A.Resp) (δ : ℝ≥0∞) : Prop :=
  ∀ (σ : List (Label P (skelSpec A))) (a : OpId P),
    1 - δ / 2 ≤ μ {c | ∀ α, E c α → skel α = σ → ∀ r, respOf α a = some r → vmin I σ a - ε ≤ r} ∧
    1 - δ / 2 ≤ μ {c | ∀ α, E c α → skel α = σ → ∀ r, respOf α a = some r → r ≤ vmax I σ a + ε}

lemma idealVals_finite (I : QSpec A.Op A.Resp) (σ : List (Label P (skelSpec A))) (a : OpId P) :
    (idealVals I σ a).Finite := by
  refine ((finite_isLinearization σ).image fun L => (tau I L a).getD 0).subset ?_
  rintro v ⟨L, hL, hv⟩
  exact ⟨L, hL, by simp [hv]⟩

lemma vmin_le {I : QSpec A.Op A.Resp} {σ : List (Label P (skelSpec A))} {a : OpId P}
    {L : List (OpId P × A.Op)} (hL : IsLinearization σ L) {v : A.Resp} (hv : tau I L a = some v) :
    vmin I σ a ≤ v :=
  csInf_le (idealVals_finite I σ a).bddBelow ⟨L, hL, hv⟩

lemma le_vmax {I : QSpec A.Op A.Resp} {σ : List (Label P (skelSpec A))} {a : OpId P}
    {L : List (OpId P × A.Op)} (hL : IsLinearization σ L) {v : A.Resp} (hv : tau I L a = some v) :
    v ≤ vmax I σ a :=
  le_csSup (idealVals_finite I σ a).bddAbove ⟨L, hL, hv⟩

/-- **Theorem 1.** An IVL implementation (Definition 2) of a sequential `(ε, δ)`-bounded `I`
object (Definition 3) implements a concurrent `(ε, δ)`-bounded `I` object (Definition 4). -/
theorem theorem1 (μ : Measure Ω) [IsProbabilityMeasure μ] {S : Ω → QSpec A.Op A.Resp}
    {I : QSpec A.Op A.Resp} {E : Ω → List (Label P A) → Prop} {ε : A.Resp} {δ : ℝ≥0∞}
    (hseq : SeqBounded P S I μ ε δ) (hivl : RandIVL S E) : ConcBounded E I μ ε δ := by
  intro σ a
  obtain ⟨L₁, L₂, h⟩ := hivl σ
  -- if `σ` is not the skeleton of an execution, or `a` does not return, the events are certain
  have hcert : ∀ (Q : Ω → Prop), (∀ c, Q c) → 1 - δ / 2 ≤ μ {c | Q c} := fun Q hQ => by
    simp only [hQ, Set.ofPred_true, measure_univ]
    exact tsub_le_self
  by_cases hreal : ∃ c α, E c α ∧ skel α = σ
  · obtain ⟨c₀, α₀, hE₀, hσ₀⟩ := hreal
    obtain ⟨hL₁, hL₂, -⟩ := h c₀ α₀ hE₀ hσ₀
    -- an instance not in a linearization does not return in any execution with skeleton `σ`
    have hnot : ∀ (L : List (OpId P × A.Op)), IsLinearization σ L → a ∉ L.map Prod.fst →
        ∀ c α, E c α → skel α = σ → ∀ r, respOf α a ≠ some r := by
      intro L hL ha c α _ hσ r hr
      subst hσ
      exact ha (hL.complete a (completed_skel.2 (Completed.of_respOf_eq_some hr)))
    constructor
    · by_cases ha : a ∈ L₁.map Prod.fst
      · refine le_trans (hseq L₁ a hL₁.nodup ha).1 (measure_mono ?_)
        intro c hc α hE hσ r hr
        obtain ⟨-, -, hs⟩ := h c α hE hσ
        obtain ⟨r₁, -, h₁, -, hr₁, -⟩ := hs a r hr
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1
          ((ObjSpec.respIn_isSome_iff (A := I.obj) (q := I.init)).2 ha)
        have := hc r₁ w h₁ hw
        have hmin : vmin I σ a ≤ w := vmin_le hL₁ hw
        calc vmin I σ a - ε ≤ w - ε := tsub_le_tsub_right hmin ε
          _ ≤ r₁ := this
          _ ≤ r := hr₁
      · exact hcert _ fun c α hE hσ r hr => absurd hr (hnot L₁ hL₁ ha c α hE hσ r)
    · by_cases ha : a ∈ L₂.map Prod.fst
      · refine le_trans (hseq L₂ a hL₂.nodup ha).2 (measure_mono ?_)
        intro c hc α hE hσ r hr
        obtain ⟨-, -, hs⟩ := h c α hE hσ
        obtain ⟨-, r₂, -, h₂, -, hr₂⟩ := hs a r hr
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1
          ((ObjSpec.respIn_isSome_iff (A := I.obj) (q := I.init)).2 ha)
        have := hc r₂ w h₂ hw
        have hmax : w ≤ vmax I σ a := le_vmax hL₂ hw
        calc r ≤ r₂ := hr₂
          _ ≤ w + ε := this
          _ ≤ vmax I σ a + ε := by simpa [add_comm] using add_le_add_right hmax ε
      · exact hcert _ fun c α hE hσ r hr => absurd hr (hnot L₂ hL₂ ha c α hE hσ r)
  · push Not at hreal
    exact ⟨hcert _ fun c α hE hσ => absurd hσ (hreal c α hE),
      hcert _ fun c α hE hσ => absurd hσ (hreal c α hE)⟩

/-- Definition 2 from canonical linearizations: if, for every coin flip vector, the canonical
linearizations `canon f₁ α`, `canon f₂ α` sandwich the return values of every execution `α`, the
algorithm is a randomized IVL implementation — these lists depend only on the skeleton `α?`
(`canon_skel`), so they are common to all coin flip vectors. -/
theorem randIVL_of_canon {S : Ω → QSpec A.Op A.Resp} {E : Ω → List (Label P A) → Prop}
    (f₁ f₂ : A.Op → Bool) (hwf : ∀ c α, E c α → WellFormed α)
    (h : ∀ c α, E c α → ∀ a r, respOf α a = some r → ∃ r₁ r₂,
      tau (S c) (canon f₁ α) a = some r₁ ∧ tau (S c) (canon f₂ α) a = some r₂ ∧ r₁ ≤ r ∧ r ≤ r₂) :
    RandIVL S E := by
  intro σ
  refine ⟨canon (A := skelSpec A) f₁ σ, canon (A := skelSpec A) f₂ σ, fun c α hE hσ => ?_⟩
  subst hσ
  rw [canon_skel, canon_skel]
  exact ⟨isSkelLin_canon f₁ (hwf c α hE), isSkelLin_canon f₂ (hwf c α hE), h c α hE⟩

end Podc.IntermediateValueLin
