/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/PopulationProtocols/Phases.lean
import Cslib.Computability.Distributed.PopulationProtocols.Schedules
import Mathlib.Data.List.GetD

/-!
# Building fair executions from phases; stabilization versus reachability

Tools to turn reachability arguments into statements about (weakly or globally) fair executions
of CSLib's deterministic population protocols, and back.

* `Protocol.runList`: following a finite list of interactions; `reachable_runList`,
  `exists_list_of_reachable`.
* `Protocol.exists_execution_of_segments`: an infinite sequence of finite schedule segments
  (`D k` ⟶ `D (k+1)`) glued into one execution.
* **`Protocol.exists_weaklyFair_of_phases`**: if from every configuration of a set `G` and for
  every pair of distinct agents there is a path back into `G` that uses this pair (a *phase*),
  then there is a weakly fair execution visiting `G` infinitely often, along which consecutive
  phase boundaries are related by any relation `R` the phases guarantee. This is the standard way
  to build adversarial weakly fair executions (impossibility proofs under weak fairness).
* `Execution.Stabilizes out good`: the output `out` of the configuration is eventually constant
  and `good`; `StablyGood out good C`: `out C` is good and never changes again.
* `exists_stablyGood_of_weaklyFair`, `exists_stablyGood_of_globallyFair`: if every weakly
  (globally) fair execution from `I` stabilizes, then from every configuration reachable from `I`
  a stably good configuration is reachable. `stabilizes_of_globallyFair` is the converse under
  global fairness.
-/

namespace Cslib.PopulationProtocol.Protocol

open Cslib.TransitionSystem

variable {Q A : Type*} [DecidableEq A] (P : Protocol Q)

/-! ### Finite lists of interactions -/

/-- The configuration reached from `C` by the interactions of the list `l`, in order. -/
def runList : List (A × A) → Config A Q → Config A Q
  | [], C => C
  | p :: l, C => runList l (P.interact C p.1 p.2)

@[simp] lemma runList_nil (C : Config A Q) : P.runList [] C = C := rfl

@[simp] lemma runList_cons (p : A × A) (l : List (A × A)) (C : Config A Q) :
    P.runList (p :: l) C = P.runList l (P.interact C p.1 p.2) := rfl

lemma runList_append (l₁ l₂ : List (A × A)) (C : Config A Q) :
    P.runList (l₁ ++ l₂) C = P.runList l₂ (P.runList l₁ C) := by
  induction l₁ generalizing C with
  | nil => rfl
  | cons p l ih => exact ih _

lemma reachable_runList {l : List (A × A)} (hl : ∀ p ∈ l, p.1 ≠ p.2) (C : Config A Q) :
    P.Reachable C (P.runList l C) := by
  induction l generalizing C with
  | nil => exact .refl
  | cons p l ih =>
    rw [List.forall_mem_cons] at hl
    exact Relation.ReflTransGen.head ⟨p.1, p.2, hl.1, rfl⟩ (ih hl.2 _)

lemma exists_list_of_reachable {C D : Config A Q} (h : P.Reachable C D) :
    ∃ l : List (A × A), (∀ p ∈ l, p.1 ≠ p.2) ∧ P.runList l C = D := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], by simp, rfl⟩
  | head hst _ ih =>
    obtain ⟨a, b, hab, rfl⟩ := hst
    obtain ⟨l, hl, hrun⟩ := ih
    exact ⟨(a, b) :: l, List.forall_mem_cons.2 ⟨hab, hl⟩, hrun⟩

lemma runSched_add_length (C : Config A Q) (σ : ℕ → A × A) (l : List (A × A)) (s : ℕ)
    (h : ∀ i (hi : i < l.length), σ (s + i) = l[i]) :
    P.runSched C σ (s + l.length) = P.runList l (P.runSched C σ s) := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    have h0 : σ s = p := by
      have := h 0 (by simp)
      simpa only [Nat.add_zero, List.getElem_cons_zero] using this
    have h' : ∀ i (hi : i < l.length), σ (s + 1 + i) = l[i] := by
      intro i hi
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    rw [List.length_cons, show s + (l.length + 1) = s + 1 + l.length by omega, ih (s + 1) h',
      runList_cons]
    simp only [runSched, h0]

/-! ### Gluing segments -/

section Flatten

variable {α : Type*} (seg : ℕ → List α)

/-- Start positions of the segments in the concatenation. -/
def segStart : ℕ → ℕ
  | 0 => 0
  | k + 1 => segStart k + (seg k).length

variable {seg}

lemma segStart_succ (k : ℕ) : segStart seg (k + 1) = segStart seg k + (seg k).length := rfl

lemma segStart_strictMono (hne : ∀ k, seg k ≠ []) : StrictMono (segStart seg) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  rw [segStart_succ]
  have := List.length_pos_iff.2 (hne k)
  omega

/-- Index of the segment containing position `t`. -/
def segIdx (seg : ℕ → List α) (t : ℕ) : ℕ := Nat.findGreatest (fun k => segStart seg k ≤ t) t

lemma segIdx_eq (hne : ∀ k, seg k ≠ []) {k t : ℕ} (h₁ : segStart seg k ≤ t)
    (h₂ : t < segStart seg (k + 1)) : segIdx seg t = k := by
  have hmono := segStart_strictMono hne
  rw [segIdx, Nat.findGreatest_eq_iff]
  refine ⟨le_trans hmono.le_apply h₁, fun _ => h₁, fun j hj _ hle => ?_⟩
  have : segStart seg (k + 1) ≤ segStart seg j := hmono.monotone hj
  omega

/-- The concatenation of all segments (`d` is a junk default, never used). -/
def segFlat (seg : ℕ → List α) (d : α) (t : ℕ) : α :=
  (seg (segIdx seg t)).getD (t - segStart seg (segIdx seg t)) d

lemma segFlat_start (hne : ∀ k, seg k ≠ []) (d : α) (k i : ℕ) (hi : i < (seg k).length) :
    segFlat seg d (segStart seg k + i) = (seg k)[i] := by
  have hidx : segIdx seg (segStart seg k + i) = k :=
    segIdx_eq hne (by omega) (by rw [segStart_succ]; omega)
  rw [segFlat, hidx, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hi]

lemma segFlat_mem (d : α) (t : ℕ) : segFlat seg d t = d ∨ ∃ k, segFlat seg d t ∈ seg k := by
  unfold segFlat
  by_cases h : t - segStart seg (segIdx seg t) < (seg (segIdx seg t)).length
  · right
    exact ⟨_, by rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h⟩
  · left
    exact List.getD_eq_default _ _ (by omega)

end Flatten

/-- **Gluing segments.** Finite nonempty schedule segments leading from `D k` to `D (k+1)` form
an execution starting at `D 0`; segment `k` occupies the times `[st k, st (k+1))`. -/
theorem exists_execution_of_segments (D : ℕ → Config A Q) (seg : ℕ → List (A × A))
    (hne : ∀ k, seg k ≠ []) (hd : ∀ k, ∀ p ∈ seg k, p.1 ≠ p.2)
    (hrun : ∀ k, P.runList (seg k) (D k) = D (k + 1)) :
    ∃ (E : P.Execution A) (st : ℕ → ℕ), StrictMono st ∧ st 0 = 0 ∧
      (∀ k, E.config (st k) = D k) ∧
      ∀ k, ∀ p ∈ seg k, ∃ t, st k ≤ t ∧ t < st (k + 1) ∧ E.sched t = p := by
  have h0 : 0 < (seg 0).length := List.length_pos_iff.2 (hne 0)
  set d := (seg 0)[0] with hd0
  have hdd : d.1 ≠ d.2 := hd 0 d (List.getElem_mem h0)
  have hσ : ∀ t, (segFlat seg d t).1 ≠ (segFlat seg d t).2 := by
    intro t
    rcases segFlat_mem (seg := seg) d t with h | ⟨k, hk⟩
    · rw [h]; exact hdd
    · exact hd k _ hk
  let E := Execution.ofSched P (D 0) (segFlat seg d) hσ
  have hconf : ∀ k, E.config (segStart seg k) = D k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      show P.runSched (D 0) (segFlat seg d) (segStart seg (k + 1)) = D (k + 1)
      rw [segStart_succ, runSched_add_length P _ _ (seg k) _ (fun i hi => segFlat_start hne d k i hi)]
      have : P.runSched (D 0) (segFlat seg d) (segStart seg k) = D k := ih
      rw [this, hrun]
  refine ⟨E, segStart seg, segStart_strictMono hne, rfl, hconf, fun k p hp => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  exact ⟨segStart seg k + i, by omega, by rw [segStart_succ]; omega,
    segFlat_start hne d k i hi⟩

/-! ### Weakly fair executions from phases -/

/-- **Weakly fair executions from phases.** Let `G` be a set of configurations such that from
every `C ∈ G`, for every pair `a ≠ b`, some path back into `G` uses the interaction `(a, b)` and
ends in a configuration `C₂` with `R C C₂`. Then from any `C₀` from which `G` is reachable there is
a weakly fair execution that visits `G` infinitely often, at times `t ≤ t'` with
`R (config t) (config t')`. -/
theorem exists_weaklyFair_of_phases [Fintype A] (G : Config A Q → Prop)
    (R : Config A Q → Config A Q → Prop)
    (h : ∀ C, G C → ∀ a b, a ≠ b → ∃ C₁ C₂, P.Reachable C C₁ ∧
      P.Reachable (P.interact C₁ a b) C₂ ∧ G C₂ ∧ R C C₂)
    {C₀ C₁ : Config A Q} (h₀₁ : P.Reachable C₀ C₁) (hG : G C₁) {a₀ b₀ : A} (hab₀ : a₀ ≠ b₀) :
    ∃ E : P.Execution A, E.config 0 = C₀ ∧ E.WeaklyFair ∧
      ∀ T, ∃ t ≥ T, ∃ t' ≥ t, G (E.config t) ∧ R (E.config t) (E.config t') := by
  classical
  -- the list of all pairs of distinct agents
  set L := (Finset.univ.filter (fun p : A × A => p.1 ≠ p.2)).toList with hL
  have hmemL : ∀ p : A × A, p ∈ L ↔ p.1 ≠ p.2 := by simp [hL]
  have hLne : L ≠ [] := List.ne_nil_of_mem ((hmemL (a₀, b₀)).2 hab₀)
  have hLpos : 0 < L.length := List.length_pos_iff.2 hLne
  let pr : ℕ → A × A := fun k => L[k % L.length]'(Nat.mod_lt _ hLpos)
  have hpr : ∀ k, (pr k).1 ≠ (pr k).2 := fun k => (hmemL _).1 (List.getElem_mem _)
  -- one phase
  have phase : ∀ (X : {C // G C}) (k : ℕ), ∃ (Y : {C // G C}) (l : List (A × A)),
      (∀ p ∈ l, p.1 ≠ p.2) ∧ pr k ∈ l ∧ P.runList l X.1 = Y.1 ∧ R X.1 Y.1 := by
    intro X k
    obtain ⟨D₁, D₂, h₁, h₂, hG₂, hR⟩ := h X.1 X.2 (pr k).1 (pr k).2 (hpr k)
    obtain ⟨l₁, hl₁, hr₁⟩ := P.exists_list_of_reachable h₁
    obtain ⟨l₂, hl₂, hr₂⟩ := P.exists_list_of_reachable h₂
    refine ⟨⟨D₂, hG₂⟩, l₁ ++ pr k :: l₂, ?_, by simp, ?_, hR⟩
    · intro p hp
      simp only [List.mem_append, List.mem_cons] at hp
      rcases hp with hp | rfl | hp
      · exact hl₁ p hp
      · exact hpr k
      · exact hl₂ p hp
    · rw [runList_append, hr₁, runList_cons, hr₂]
  choose nxt lst hlst hmem hrunl hRl using phase
  let Y : ℕ → {C // G C} := fun k => Nat.rec ⟨C₁, hG⟩ (fun k X => nxt X k) k
  have hY : ∀ k, Y (k + 1) = nxt (Y k) k := fun _ => rfl
  obtain ⟨l₀, hl₀, hr₀⟩ := P.exists_list_of_reachable h₀₁
  let D : ℕ → Config A Q := fun k => Nat.casesOn k C₀ (fun k => (Y (k + 1)).1)
  let seg : ℕ → List (A × A) := fun k => Nat.casesOn k (l₀ ++ lst (Y 0) 0)
    (fun k => lst (Y (k + 1)) (k + 1))
  have hsegpr : ∀ k, pr k ∈ seg k := by
    intro k; cases k with
    | zero => exact List.mem_append_right _ (hmem _ _)
    | succ k => exact hmem _ _
  have hne : ∀ k, seg k ≠ [] := fun k => List.ne_nil_of_mem (hsegpr k)
  have hd : ∀ k, ∀ p ∈ seg k, p.1 ≠ p.2 := by
    intro k; cases k with
    | zero =>
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hl₀ p hp
      · exact hlst _ _ p hp
    | succ k => exact hlst _ _
  have hrun : ∀ k, P.runList (seg k) (D k) = D (k + 1) := by
    intro k; cases k with
    | zero =>
      show P.runList (l₀ ++ lst (Y 0) 0) C₀ = (Y 1).1
      rw [runList_append, hr₀]
      exact hrunl (Y 0) 0
    | succ k =>
      show P.runList (lst (Y (k + 1)) (k + 1)) (Y (k + 1)).1 = (Y (k + 2)).1
      rw [hY (k + 1)]
      exact hrunl _ _
  obtain ⟨E, st, hst, hst0, hconf, hsched⟩ :=
    P.exists_execution_of_segments D seg hne hd hrun
  refine ⟨E, by rw [← hst0, hconf]; rfl, ?_, ?_⟩
  · intro a b hab T
    obtain ⟨i, hi, hiL⟩ := List.getElem_of_mem ((hmemL (a, b)).2 hab)
    set k := L.length * (T + 1) + i
    have hk : k % L.length = i := by
      simp only [k]; rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hi
    have hprk : pr k = (a, b) := by simp only [pr, hk, hiL]
    obtain ⟨t, ht, -, hts⟩ := hsched k _ (hsegpr k)
    refine ⟨t, ?_, Or.inl (hts.trans hprk)⟩
    have h1 : k ≤ st k := hst.le_apply
    have h2 : T ≤ k := by
      simp only [k]; nlinarith
    omega
  · intro T
    refine ⟨st (T + 1), le_trans (Nat.le_succ T) hst.le_apply, st (T + 2),
      (hst (Nat.lt_succ_self _)).le, ?_, ?_⟩
    · rw [hconf]; exact (Y (T + 1)).2
    · rw [hconf, hconf]
      show R (Y (T + 1)).1 (Y (T + 1 + 1)).1
      rw [hY (T + 1)]
      exact hRl _ _

/-! ### Stabilization of outputs -/

variable {P}

/-- The output `out` of the configuration is eventually constant, with a value satisfying
`good`. -/
def Execution.Stabilizes {O : Type*} (out : Config A Q → O) (good : O → Prop)
    (E : P.Execution A) : Prop :=
  ∃ T, good (out (E.config T)) ∧ ∀ t ≥ T, out (E.config t) = out (E.config T)

variable (P) in
/-- `out C` is good and no reachable configuration has another output. -/
def StablyGood {O : Type*} (out : Config A Q → O) (good : O → Prop) (C : Config A Q) : Prop :=
  good (out C) ∧ ∀ D, P.Reachable C D → out D = out C

lemma StablyGood.reachable {O : Type*} {out : Config A Q → O} {good : O → Prop}
    {C D : Config A Q} (hC : P.StablyGood out good C) (h : P.Reachable C D) :
    P.StablyGood out good D := by
  refine ⟨(hC.2 D h).symm ▸ hC.1, fun D' hD' => ?_⟩
  rw [hC.2 D' (h.trans hD'), hC.2 D h]

/-- **Weak fairness ⇒ reachability.** If every weakly fair execution from `I` stabilizes, then a
stably good configuration is reachable from every configuration reachable from `I`. -/
theorem exists_stablyGood_of_weaklyFair [Fintype A] {O : Type*} {out : Config A Q → O}
    {good : O → Prop} {I : Set (Config A Q)} {a₀ b₀ : A} (hab₀ : a₀ ≠ b₀)
    (h : ∀ E : P.Execution A, E.config 0 ∈ I → E.WeaklyFair → E.Stabilizes out good)
    {C₀ C : Config A Q} (hC₀ : C₀ ∈ I) (hC : P.Reachable C₀ C) :
    ∃ D, P.Reachable C D ∧ P.StablyGood out good D := by
  by_contra hno
  push Not at hno
  let G : Config A Q → Prop := fun X => P.Reachable C X
  let R : Config A Q → Config A Q → Prop := fun X X' => out X' ≠ out X ∨ ¬ good (out X)
  have hph : ∀ X, G X → ∀ a b, a ≠ b → ∃ X₁ X₂, P.Reachable X X₁ ∧
      P.Reachable (P.interact X₁ a b) X₂ ∧ G X₂ ∧ R X X₂ := by
    intro X hX a b hab
    have hstep : P.Reachable X (P.interact X a b) := .single ⟨a, b, hab, rfl⟩
    by_cases hout : out (P.interact X a b) = out X
    · have hns := hno _ (hX.trans hstep)
      simp only [StablyGood, not_and, not_forall] at hns
      by_cases hg : good (out X)
      · obtain ⟨D', hD', hne⟩ := hns (hout ▸ hg)
        exact ⟨X, D', .refl, hD', (hX.trans hstep).trans hD', Or.inl (hout ▸ hne)⟩
      · exact ⟨X, _, .refl, .refl, hX.trans hstep, Or.inr hg⟩
    · exact ⟨X, _, .refl, .refl, hX.trans hstep, Or.inl hout⟩
  obtain ⟨E, hE0, hEf, hinf⟩ := P.exists_weaklyFair_of_phases G R hph hC .refl hab₀
  obtain ⟨T, hgT, hT⟩ := h E (hE0 ▸ hC₀) hEf
  obtain ⟨t, ht, t', ht', -, hR⟩ := hinf T
  rcases hR with hR | hR
  · exact hR (by rw [hT t' (le_trans ht ht'), hT t ht])
  · exact hR (by rw [hT t ht]; exact hgT)

/-- An execution with the given configurations (the interacting pairs are chosen). -/
noncomputable def Execution.ofRun (E : Run (P.Step (A := A))) : P.Execution A where
  config := E.st
  sched t := ((E.step t).choose, (E.step t).choose_spec.choose)
  sched_ne t := (E.step t).choose_spec.choose_spec.1
  step t := (E.step t).choose_spec.choose_spec.2

@[simp] lemma Execution.ofRun_config (E : Run (P.Step (A := A))) :
    (Execution.ofRun (A := A) E).config = E.st := rfl

lemma Execution.ofRun_globallyFair {E : Run (P.Step (A := A))} (hE : E.GloballyFair) :
    (Execution.ofRun (A := A) E).GloballyFair := by
  rw [Execution.globallyFair_iff]
  have : (Execution.ofRun (A := A) E).toRun = E := by cases E; rfl
  rw [this]; exact hE

/-- Prepending a finite path to a run. -/
theorem exists_run_prefix {X : Type*} {R : X → X → Prop} {x y : X}
    (hxy : Relation.ReflTransGen R x y) (E : Run R) (hE : E.st 0 = y) :
    ∃ (E' : Run R) (k : ℕ), E'.st 0 = x ∧ ∀ t, E'.st (t + k) = E.st t := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨E, 0, hE, fun _ => rfl⟩
  | @head a b hab _ ih =>
    obtain ⟨E', k, h0, hk⟩ := ih
    refine ⟨⟨fun t => Nat.casesOn t a E'.st, fun t => ?_⟩, k + 1, rfl, fun t => ?_⟩
    · cases t with
      | zero => show R a (E'.st 0); exact h0 ▸ hab
      | succ t => exact E'.step t
    · show E'.st (t + k) = _
      exact hk t

/-- **Global fairness ⇒ reachability.** If every globally fair execution from `I` stabilizes,
then a stably good configuration is reachable from every configuration reachable from `I`. -/
theorem exists_stablyGood_of_globallyFair [Finite A] [Finite Q] {O : Type*}
    {out : Config A Q → O} {good : O → Prop} {I : Set (Config A Q)} {a₀ b₀ : A}
    (hab₀ : a₀ ≠ b₀)
    (h : ∀ E : P.Execution A, E.config 0 ∈ I → E.GloballyFair → E.Stabilizes out good)
    {C₀ C : Config A Q} (hC₀ : C₀ ∈ I) (hC : P.Reachable C₀ C) :
    ∃ D, P.Reachable C D ∧ P.StablyGood out good D := by
  obtain ⟨F, hF0, hF⟩ := exists_globallyFair (R := P.Step (A := A))
    (fun X => ⟨_, a₀, b₀, hab₀, rfl⟩) C
  obtain ⟨F', k, hF'0, hF'k⟩ := exists_run_prefix hC F hF0
  have hF'fair : F'.GloballyFair := by
    intro x y hxy hx
    have hx' : ∃ᶠ t in Filter.atTop, F.st t = x := by
      rw [Filter.frequently_atTop] at hx ⊢
      intro T
      obtain ⟨t, ht, hxt⟩ := hx (T + k)
      exact ⟨t - k, by omega, by rw [← hF'k, Nat.sub_add_cancel (by omega)]; exact hxt⟩
    have := hF x y hxy hx'
    rw [Filter.frequently_atTop] at this ⊢
    intro T
    obtain ⟨t, ht, hyt⟩ := this T
    exact ⟨t + k, by omega, by rw [hF'k]; exact hyt⟩
  set E := Execution.ofRun (A := A) F' with hEdef
  have hEf : E.GloballyFair := Execution.ofRun_globallyFair hF'fair
  obtain ⟨T, hgT, hT⟩ := h E (by simp [hEdef, hF'0, hC₀]) hEf
  obtain ⟨D, hD⟩ := E.exists_infinitely_often
  obtain ⟨t₁, ht₁, hDt₁⟩ := hD (T + k)
  refine ⟨D, ?_, ?_, ?_⟩
  · rw [← hDt₁]
    have : E.config t₁ = F.st (t₁ - k) := by
      simp only [hEdef, Execution.ofRun_config]; rw [← hF'k, Nat.sub_add_cancel (by omega)]
    rw [this, ← hF0]; exact F.reach _
  · rw [← hDt₁, hT t₁ (by omega)]; exact hgT
  · intro D' hD'
    obtain ⟨t₂, ht₂, hDt₂⟩ := hEf.infinitely_often_of_reachable hD hD' T
    rw [← hDt₂, ← hDt₁, hT t₂ ht₂, hT t₁ (by omega)]

/-- **Reachability ⇒ global fairness.** If a stably good configuration is reachable from every
configuration reachable from `I`, every globally fair execution from `I` stabilizes. -/
theorem stabilizes_of_globallyFair [Finite A] [Finite Q] {O : Type*}
    {out : Config A Q → O} {good : O → Prop} {I : Set (Config A Q)}
    (h : ∀ C₀ ∈ I, ∀ C, P.Reachable C₀ C → ∃ D, P.Reachable C D ∧ P.StablyGood out good D)
    (E : P.Execution A) (hE0 : E.config 0 ∈ I) (hE : E.GloballyFair) :
    E.Stabilizes out good := by
  have hcl : P.Closed (P.StablyGood out good) :=
    fun C C' hC hst => hC.reachable (.single hst)
  obtain ⟨T, hT⟩ := hE.eventually_mem hcl (fun C hC => by
    obtain ⟨D, hD, hDs⟩ := h _ hE0 C hC
    exact ⟨D, hDs, hD⟩)
  exact ⟨T, (hT T le_rfl).1, fun t ht =>
    (hT T le_rfl).2 _ (E.reachable_of_le ht)⟩

end Cslib.PopulationProtocol.Protocol
