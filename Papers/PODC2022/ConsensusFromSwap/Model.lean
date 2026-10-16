import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Spec

/-!
# The Space Complexity of Consensus from Swap — the model

Sean Ovens, *The Space Complexity of Consensus from Swap*, PODC 2022 (arXiv 2305.06507).

A self-contained model of the standard asynchronous shared-memory model of the paper (Section 2)
for one-shot tasks in which **processes start with their inputs** (k-set agreement, consensus):

* processes `P` (any type), deterministic; process `p` with input `x` starts in local state
  `A.init p x`;
* shared objects indexed by `ι`; object `i` has a deterministic sequential specification
  `T i : ObjSpec` (CSLib); the algorithm fixes their initial values `A.mem₀`
  (`ObjSpec.init` is ignored);
* a local state either *outputs* (decides) a value (`Act.out v`, an output state; output states
  are final, a step taken in an output state is a no-op) or is *poised* to apply operation `o`
  to object `i` and continue with `k r` on response `r` (`Act.access i o k`). Every step that is
  not a no-op is exactly one operation on one object (local computation is folded into the
  continuation);
* the scheduler picks the next process (`Cfg.step C p`); since everything is deterministic, a
  finite execution from a configuration is its list of processes (`run C α`).

Correctness of a k-set agreement algorithm for the inputs in a set `S` (`SolvesSetAgreement`):
* **k-agreement**: in every finite execution from an initial configuration (all inputs in `S`) at
  most `k` distinct values are decided (`decSet`);
* **validity**: every decided value is the input of some process.

**Obstruction-freedom** (`ObstructionFree`): from every reachable configuration, every process
running solo decides after finitely many steps. (Nondeterministic solo-termination coincides with
this for deterministic algorithms; randomization is not modelled.)

-- CSLib candidate: a generalization of `Cslib.SharedMemory.Recoverable` (no crashes, arbitrary
-- processes and input values).
-/

namespace ConsensusFromSwap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

section Defs

variable {ι : Type} (T : ι → ObjSpec)

/-- What a process does in a local state: apply operation `o` to object `i` and continue with
`k r` (where `r` is the response), or output (decide) `v`. -/
inductive Act (V L : Type) where
  /-- Apply `o` to object `i` and continue with `k r` on response `r`. -/
  | access (i : ι) (o : (T i).Op) (k : (T i).Resp → L)
  /-- Output (decide) `v`. -/
  | out (v : V)

/-- A deterministic algorithm for processes `P` with input/output values `V`, using the objects
`T i`, `i : ι`. -/
structure Alg (P V : Type) where
  /-- Local states. -/
  L : Type
  /-- Initial state of process `p` with input `x`. -/
  init : P → V → L
  /-- The next action in a local state. -/
  act : L → Act T V L
  /-- Initial values of the objects. -/
  mem₀ : (i : ι) → (T i).State

variable {T} {P V : Type}

/-- Configurations: local states and object values. -/
structure Cfg (A : Alg T P V) where
  /-- Local states. -/
  loc : P → A.L
  /-- Values of the objects. -/
  mem : (i : ι) → (T i).State

end Defs

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {P V : Type} [DecidableEq P]
  {A : Alg T P V}

namespace Cfg

/-- `p` is in an output state with value `v` (`p` has decided `v`). -/
def Out (C : Cfg A) (p : P) (v : V) : Prop := A.act (C.loc p) = .out v

/-- `p` has decided. -/
def Dec (C : Cfg A) (p : P) : Prop := ∃ v, C.Out p v

/-- `p` is poised to apply some operation to object `i`. -/
def Poised (C : Cfg A) (p : P) (i : ι) : Prop := ∃ o k, A.act (C.loc p) = .access i o k

/-- The next step of `p` (a no-op if `p` has decided). -/
def step (C : Cfg A) (p : P) : Cfg A :=
  match A.act (C.loc p) with
  | .access i o k =>
    ⟨Function.update C.loc p (k ((T i).δ (C.mem i) o).2),
     Function.update C.mem i ((T i).δ (C.mem i) o).1⟩
  | .out _ => C

/-- The set of values decided in `C`. -/
def decSet (C : Cfg A) : Set V := {v | ∃ p, C.Out p v}

end Cfg

/-- The configuration reached from `C` by the schedule `α`. -/
def run (C : Cfg A) (α : List P) : Cfg A := α.foldl Cfg.step C

/-- A solo run of `t` steps of `p`. -/
abbrev solo (p : P) (t : ℕ) : List P := List.replicate t p

variable (A) in
/-- The initial configuration with inputs `x`. -/
def initCfg (x : P → V) : Cfg A := ⟨fun p => A.init p (x p), A.mem₀⟩

/-- All inputs are in `S`. -/
def InputsIn (S : Set V) (x : P → V) : Prop := ∀ p, x p ∈ S

variable (A) in
/-- `A` solves `k`-set agreement for inputs in `S` (safety: `k`-agreement and validity). -/
structure SolvesSetAgreement (k : ℕ) (S : Set V) : Prop where
  /-- At most `k` distinct values are decided. -/
  agreement : ∀ x, InputsIn S x → ∀ α, (run (initCfg A x) α).decSet.encard ≤ k
  /-- Every decided value is the input of some process. -/
  validity : ∀ x, InputsIn S x → ∀ α p v, (run (initCfg A x) α).Out p v → ∃ q, x q = v

variable (A) in
/-- Obstruction-freedom: from every reachable configuration (inputs in `S`), every process
running solo decides within finitely many steps. -/
def ObstructionFree (S : Set V) : Prop :=
  ∀ x, InputsIn S x → ∀ α p, ∃ t, (run (run (initCfg A x) α) (solo p t)).Dec p

/-! ## Basic lemmas -/

@[simp] lemma run_nil (C : Cfg A) : run C [] = C := rfl

@[simp] lemma run_cons (C : Cfg A) (p : P) (α : List P) : run C (p :: α) = run (C.step p) α :=
  rfl

lemma run_append (C : Cfg A) (α β : List P) : run C (α ++ β) = run (run C α) β := by
  simp [run, List.foldl_append]

lemma run_concat (C : Cfg A) (α : List P) (p : P) : run C (α ++ [p]) = (run C α).step p := by
  simp [run_append]

lemma run_singleton (C : Cfg A) (p : P) : run C [p] = C.step p := rfl

lemma solo_succ (p : P) (t : ℕ) : solo p (t + 1) = solo p t ++ [p] :=
  List.replicate_succ' ..

lemma solo_add (p : P) (a b : ℕ) : solo p (a + b) = solo p a ++ solo p b :=
  List.replicate_add ..

namespace Cfg

lemma step_of_access (C : Cfg A) {p : P} {i : ι} {o : (T i).Op} {k : (T i).Resp → A.L}
    (h : A.act (C.loc p) = .access i o k) :
    C.step p = ⟨Function.update C.loc p (k ((T i).δ (C.mem i) o).2),
      Function.update C.mem i ((T i).δ (C.mem i) o).1⟩ := by
  simp only [step]
  split
  · rename_i i' o' k' h'
    rw [h] at h'
    cases h'
    rfl
  · rename_i h'
    rw [h] at h'
    cases h'

lemma step_of_out (C : Cfg A) {p : P} {v : V} (h : C.Out p v) : C.step p = C := by
  simp only [step]
  rw [Out] at h
  split <;> simp_all

lemma step_of_dec (C : Cfg A) {p : P} (h : C.Dec p) : C.step p = C := by
  obtain ⟨v, hv⟩ := h
  exact C.step_of_out hv

lemma step_loc_other (C : Cfg A) {p q : P} (h : q ≠ p) : (C.step p).loc q = C.loc q := by
  simp only [step]
  split
  · simp [Function.update_of_ne h]
  · rfl

/-- A step of `p` poised on object `i` does not change the other objects. -/
lemma step_mem_other (C : Cfg A) {p : P} {i j : ι} (hp : C.Poised p i) (hj : j ≠ i) :
    (C.step p).mem j = C.mem j := by
  obtain ⟨o, k, h⟩ := hp
  rw [C.step_of_access h]
  simp [Function.update_of_ne hj]

/-- A step of `p` changes at most the object `p` is poised on. -/
lemma step_mem_eq_of_not_poised (C : Cfg A) {p : P} {j : ι} (hj : ¬ C.Poised p j) :
    (C.step p).mem j = C.mem j := by
  simp only [step]
  split
  · rename_i i o k h
    have : j ≠ i := by
      rintro rfl
      exact hj ⟨o, k, h⟩
    simp [Function.update_of_ne this]
  · rfl

lemma dec_or_poised (C : Cfg A) (p : P) : C.Dec p ∨ ∃ i, C.Poised p i := by
  cases h : A.act (C.loc p) with
  | access i o k => exact Or.inr ⟨i, o, k, h⟩
  | out v => exact Or.inl ⟨v, h⟩

lemma not_dec_of_poised {C : Cfg A} {p : P} {i : ι} (h : C.Poised p i) : ¬ C.Dec p := by
  rintro ⟨v, hv⟩
  obtain ⟨o, k, h⟩ := h
  rw [Out, h] at hv
  cases hv

lemma Out.unique {C : Cfg A} {p : P} {v w : V} (hv : C.Out p v) (hw : C.Out p w) : v = w := by
  rw [Out, hv] at hw
  cases hw
  rfl

lemma Out.step {C : Cfg A} {p : P} {v : V} (h : C.Out p v) (q : P) : (C.step q).Out p v := by
  by_cases hq : p = q
  · subst hq
    rwa [C.step_of_out h]
  · rw [Out, C.step_loc_other hq]
    exact h

lemma Dec.step {C : Cfg A} {p : P} (h : C.Dec p) (q : P) : (C.step q).Dec p := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v, hv.step q⟩

lemma Out.dec {C : Cfg A} {p : P} {v : V} (h : C.Out p v) : C.Dec p := ⟨v, h⟩

end Cfg

lemma run_loc_other (C : Cfg A) (α : List P) {q : P} (h : ∀ r ∈ α, r ≠ q) :
    (run C α).loc q = C.loc q := by
  induction α generalizing C with
  | nil => rfl
  | cons r α ih =>
    simp only [run_cons]
    rw [ih _ (fun r' hr' => h r' (by simp [hr'])),
      C.step_loc_other (Ne.symm (h r (by simp)))]

/-- Output states are permanent. -/
lemma Cfg.Out.run {C : Cfg A} {p : P} {v : V} (h : C.Out p v) (α : List P) :
    (ConsensusFromSwap.run C α).Out p v := by
  induction α generalizing C with
  | nil => exact h
  | cons r α ih => exact ih (h.step r)

lemma Cfg.Dec.run {C : Cfg A} {p : P} (h : C.Dec p) (α : List P) :
    (ConsensusFromSwap.run C α).Dec p := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v, hv.run α⟩

lemma decSet_mono (C : Cfg A) (α : List P) : C.decSet ⊆ (run C α).decSet := by
  rintro v ⟨p, hp⟩
  exact ⟨p, hp.run α⟩

lemma run_solo_of_dec {C : Cfg A} {p : P} (h : C.Dec p) (t : ℕ) : run C (solo p t) = C := by
  induction t with
  | zero => rfl
  | succ t ih => rw [solo_succ, run_concat, ih, C.step_of_dec h]

/-- Steps of processes that do not access object `j` leave it unchanged. -/
lemma run_mem_of_not_poised (C : Cfg A) (α : List P) (j : ι)
    (h : ∀ β p γ, α = β ++ p :: γ → ¬ (run C β).Poised p j) :
    (run C α).mem j = C.mem j := by
  induction α using List.reverseRecOn with
  | nil => rfl
  | append_singleton α p ih =>
    rw [run_concat, Cfg.step_mem_eq_of_not_poised _ (h α p [] rfl), ih]
    intro β q γ hβ
    exact h β q (γ ++ [p]) (by simp [hβ])

/-! ## Indistinguishability -/

/-- `C` and `D` have the same object values and agree on the local states of the processes in
`R`. -/
def AgreeOn (R : Set P) (C D : Cfg A) : Prop := C.mem = D.mem ∧ ∀ p ∈ R, C.loc p = D.loc p

lemma AgreeOn.refl (R : Set P) (C : Cfg A) : AgreeOn R C C := ⟨rfl, fun _ _ => rfl⟩

lemma AgreeOn.symm {R : Set P} {C D : Cfg A} (h : AgreeOn R C D) : AgreeOn R D C :=
  ⟨h.1.symm, fun p hp => (h.2 p hp).symm⟩

lemma AgreeOn.trans {R : Set P} {C D E : Cfg A} (h : AgreeOn R C D) (h' : AgreeOn R D E) :
    AgreeOn R C E :=
  ⟨h.1.trans h'.1, fun p hp => (h.2 p hp).trans (h'.2 p hp)⟩

lemma AgreeOn.mono {R R' : Set P} {C D : Cfg A} (h : AgreeOn R C D) (hR : R' ⊆ R) :
    AgreeOn R' C D :=
  ⟨h.1, fun p hp => h.2 p (hR hp)⟩

lemma AgreeOn.step {R : Set P} {C D : Cfg A} (h : AgreeOn R C D) {p : P} (hp : p ∈ R) :
    AgreeOn R (C.step p) (D.step p) := by
  obtain ⟨hm, hl⟩ := h
  have hlp := hl p hp
  simp only [Cfg.step]
  rw [hlp]
  split
  · rename_i i o k _
    refine ⟨?_, fun q hq => ?_⟩
    · simp [hm]
    · by_cases hqp : q = p
      · subst hqp; simp [hm]
      · simp [Function.update_of_ne hqp, hl q hq]
  · exact ⟨hm, hl⟩

lemma AgreeOn.run {R : Set P} {C D : Cfg A} (h : AgreeOn R C D) {α : List P}
    (hα : ∀ p ∈ α, p ∈ R) : AgreeOn R (ConsensusFromSwap.run C α) (ConsensusFromSwap.run D α) := by
  induction α generalizing C D with
  | nil => exact h
  | cons p α ih =>
    exact ih (h.step (hα p (by simp))) (fun q hq => hα q (by simp [hq]))

lemma AgreeOn.out_iff {R : Set P} {C D : Cfg A} (h : AgreeOn R C D) {p : P} (hp : p ∈ R)
    {v : V} : C.Out p v ↔ D.Out p v := by
  simp only [Cfg.Out, h.2 p hp]

lemma AgreeOn.dec_iff {R : Set P} {C D : Cfg A} (h : AgreeOn R C D) {p : P} (hp : p ∈ R) :
    C.Dec p ↔ D.Dec p := by
  simp only [Cfg.Dec, h.out_iff hp]

lemma AgreeOn.poised_iff {R : Set P} {C D : Cfg A} (h : AgreeOn R C D) {p : P} (hp : p ∈ R)
    {i : ι} : C.Poised p i ↔ D.Poised p i := by
  simp only [Cfg.Poised, h.2 p hp]

/-- Steps of processes outside `R` that do not change the memory preserve agreement on `R`. -/
lemma agreeOn_step_of_mem_eq {R : Set P} (C : Cfg A) {p : P} (hp : p ∉ R)
    (hm : (C.step p).mem = C.mem) : AgreeOn R C (C.step p) :=
  ⟨hm.symm, fun q hq => (C.step_loc_other (by rintro rfl; exact hp hq)).symm⟩

/-! ## Commuting steps -/

/-- Steps of two different processes that are poised on different objects commute. -/
lemma Cfg.step_comm (C : Cfg A) {p q : P} (hpq : p ≠ q)
    (h : ∀ i, C.Poised p i → ¬ C.Poised q i) : (C.step p).step q = (C.step q).step p := by
  rcases C.dec_or_poised p with hp | ⟨i, hp⟩
  · obtain ⟨v, hv⟩ := hp
    rw [C.step_of_dec ⟨v, hv⟩, (C.step q).step_of_dec ⟨v, ?_⟩]
    show A.act ((C.step q).loc p) = _
    rw [C.step_loc_other hpq]; exact hv
  rcases C.dec_or_poised q with hq | ⟨j, hq⟩
  · obtain ⟨v, hv⟩ := hq
    rw [C.step_of_dec ⟨v, hv⟩, (C.step p).step_of_dec ⟨v, ?_⟩]
    show A.act ((C.step p).loc q) = _
    rw [C.step_loc_other (Ne.symm hpq)]; exact hv
  have hij : i ≠ j := by rintro rfl; exact h i hp hq
  obtain ⟨o, k, hpa⟩ := hp
  obtain ⟨o', k', hqa⟩ := hq
  rw [C.step_of_access hpa, C.step_of_access hqa]
  rw [Cfg.step_of_access _ (p := q) (i := j) (o := o') (k := k')
      (by simp [Function.update_of_ne (Ne.symm hpq), hqa]),
    Cfg.step_of_access _ (p := p) (i := i) (o := o) (k := k)
      (by simp [Function.update_of_ne hpq, hpa])]
  simp only [Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
  congr 1
  · exact Function.update_comm hpq _ _ _
  · exact Function.update_comm hij _ _ _

/-! ## Swap objects -/

/-- A swap object with values `D`: `Swap(v)` sets the value to `v` and returns the old value. -/
abbrev swapObj (D : Type) (d₀ : D) : ObjSpec where
  State := D
  Op := D
  Resp := D
  init := d₀
  δ s v := (v, s)

/-- Operations of a readable swap object. -/
inductive RSOp (D : Type) where
  /-- `Read`. -/
  | read
  /-- `Swap(v)`. -/
  | swap (v : D)
  deriving DecidableEq

/-- A readable swap object with values `D`. -/
abbrev rswapObj (D : Type) (d₀ : D) : ObjSpec where
  State := D
  Op := RSOp D
  Resp := D
  init := d₀
  δ s
    | .read => (s, s)
    | .swap v => (v, s)

/-- Every operation of `S` sets the state to a value independent of the old state: `S` is a
historyless object all of whose operations are nontrivial (e.g. a swap object). -/
def OnlyOverwrites (S : ObjSpec) : Prop := ∀ o s s', (S.δ s o).1 = (S.δ s' o).1

lemma onlyOverwrites_swapObj (D : Type) (d₀ : D) : OnlyOverwrites (swapObj D d₀) :=
  fun _ _ _ => rfl

end ConsensusFromSwap
