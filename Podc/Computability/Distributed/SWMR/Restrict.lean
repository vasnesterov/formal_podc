/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/SWMR/Restrict.lean
import Podc.Computability.Distributed.SWMR.Basic

/-!
# Restricting an algorithm to a subset of the processes

Given an algorithm `A` for processes `P` and a set `G : Finset P`, the processes of `G` can run
`A` on their own, as if the processes outside `G` had crashed before taking any step: a read of a
register of a process outside `G` returns its initial value (it is simulated by a read of the
reader's own register, whose value is ignored). Decisions may be post-processed by a map
`f : Out → Out'`. This is the standard way of turning an algorithm for `n` processes into an
algorithm for a subsystem (e.g. to reduce a `t`-resilient problem to `1`-resilient consensus).

## Main definitions

* `Alg.restrictMap A G f : Alg G K V In Out'`
* `liftIn xG w`: the input vector of `P` that agrees with `xG` on `G` and with `w` outside `G`

## Main statements

* `Alg.run_restrictMap`: an execution of the restricted algorithm is an execution of `A` (from
  the lifted inputs, with the same schedule) in which no process outside `G` takes a step; the
  local states, registers and (mapped) outputs of `G` coincide.
* `Alg.Solves.restrictMap_termination`: if `A` is `t`-resilient and `|Gᶜ| + s ≤ t`, then the
  restricted algorithm satisfies the termination condition of the `s`-resilient model.
-/

namespace Cslib.SWMR

variable {P K : Type} {V : K → Type} {In Out Out' : Type}

namespace Alg

/-- The processes of `G` run `A` alone; reads of registers outside `G` return the initial value;
decisions are mapped by `f`. -/
@[reducible] def restrictMap [DecidableEq P] (A : Alg P K V In Out) (G : Finset P) (f : Out → Out') : Alg G K V In Out' where
  S := A.S
  v₀ := A.v₀
  init p x := A.init p x
  next p s :=
    match A.next p s with
    | .write i v s' => .write i v s'
    | .read q i k => if h : q ∈ G then .read ⟨q, h⟩ i k else .read p i (fun _ => k (A.v₀ i))
    | .decide y s' => .decide (f y) s'

end Alg

/-- The input vector that is `xG` on `G` and `w` outside `G`. -/
def liftIn [DecidableEq P] {G : Finset P} (xG : G → In) (w : P → In) (p : P) : In :=
  if h : p ∈ G then xG ⟨p, h⟩ else w p

section Rel

variable [DecidableEq P] [DecidableEq K] {A : Alg P K V In Out} {G : Finset P} {f : Out → Out'}

/-- The simulation relation between configurations of the restricted algorithm and of `A`. -/
def RestrictRel (A : Alg P K V In Out) (G : Finset P) (f : Out → Out')
    (D : Config (A.restrictMap G f)) (C : Config A) : Prop :=
  (∀ p : G, D.loc p = C.loc p ∧ D.mem p = C.mem p ∧ D.out p = (C.out p).map f) ∧
  ∀ p, p ∉ G → C.mem p = A.v₀

omit [DecidableEq K] in
lemma restrictRel_init (xG : G → In) (w : P → In) :
    RestrictRel A G f ((A.restrictMap G f).initCfg xG) (A.initCfg (liftIn xG w)) := by
  refine ⟨fun p => ?_, fun p _ => rfl⟩
  refine ⟨?_, rfl, rfl⟩
  simp [Alg.initCfg, Alg.restrictMap, liftIn]

omit [DecidableEq K] in
lemma restrictMap_next (p : G) (s : A.S) : (A.restrictMap G f).next p s =
    match A.next p.1 s with
    | .write i v s' => .write i v s'
    | .read q i k => if h : q ∈ G then .read ⟨q, h⟩ i k else .read p i (fun _ => k (A.v₀ i))
    | .decide y s' => .decide (f y) s' := rfl

lemma RestrictRel.step {D : Config (A.restrictMap G f)} {C : Config A}
    (h : RestrictRel A G f D C) (p : G) :
    RestrictRel A G f ((A.restrictMap G f).step p D) (A.step p.1 C) := by
  obtain ⟨hG, hout⟩ := h
  obtain ⟨hl, hm, ho⟩ := hG p
  have hne : ∀ r : G, r ≠ p → r.1 ≠ p.1 := fun r h e => h (Subtype.ext e)
  rcases hA : A.next p.1 (C.loc p.1) with ⟨i, v, s'⟩ | ⟨q, i, k⟩ | ⟨y, s'⟩
  · have hB : (A.restrictMap G f).next p (D.loc p) = .write i v s' := by
      rw [restrictMap_next, hl, hA]
    rw [Alg.step_of_write hA, Alg.step_of_write hB]
    refine ⟨fun r => ?_, fun r hr => ?_⟩
    · by_cases hrp : r = p
      · subst hrp; exact ⟨by simp, by simp [hm], by simp [ho]⟩
      · simp only [Function.update_of_ne hrp, Function.update_of_ne (hne r hrp)]
        exact hG r
    · have hrp' : r ≠ p.1 := fun e => hr (e ▸ p.2)
      simp [Function.update_of_ne hrp', hout r hr]
  · by_cases hq : q ∈ G
    · have hB : (A.restrictMap G f).next p (D.loc p) = .read ⟨q, hq⟩ i k := by
        rw [restrictMap_next, hl, hA]; simp [hq]
      rw [Alg.step_of_read hA, Alg.step_of_read hB]
      refine ⟨fun r => ?_, hout⟩
      by_cases hrp : r = p
      · subst hrp; exact ⟨by simp [(hG ⟨q, hq⟩).2.1], hm, ho⟩
      · simp only [Function.update_of_ne hrp, Function.update_of_ne (hne r hrp)]
        exact hG r
    · have hB : (A.restrictMap G f).next p (D.loc p) = .read p i (fun _ => k (A.v₀ i)) := by
        rw [restrictMap_next, hl, hA]; simp [hq]
      rw [Alg.step_of_read hA, Alg.step_of_read hB]
      refine ⟨fun r => ?_, hout⟩
      by_cases hrp : r = p
      · subst hrp; exact ⟨by simp [hout q hq], hm, ho⟩
      · simp only [Function.update_of_ne hrp, Function.update_of_ne (hne r hrp)]
        exact hG r
  · have hB : (A.restrictMap G f).next p (D.loc p) = .decide (f y) s' := by
      rw [restrictMap_next, hl, hA]
    rw [Alg.step_of_decide hA, Alg.step_of_decide hB]
    refine ⟨fun r => ?_, hout⟩
    by_cases hrp : r = p
    · subst hrp
      refine ⟨by simp, hm, ?_⟩
      cases hc : C.out r.1 <;> simp [ho, hc]
    · simp only [Function.update_of_ne hrp, Function.update_of_ne (hne r hrp)]
      exact hG r

lemma RestrictRel.run {D : Config (A.restrictMap G f)} {C : Config A}
    (h : RestrictRel A G f D C) (τ : List G) :
    RestrictRel A G f ((A.restrictMap G f).run D τ) (A.run C (τ.map Subtype.val)) := by
  induction τ generalizing D C with
  | nil => exact h
  | cons p τ ih => exact ih (h.step p)

/-- An execution of the restricted algorithm is an execution of `A` in which only `G` steps. -/
theorem Alg.run_restrictMap (xG : G → In) (w : P → In) (τ : List G) :
    RestrictRel A G f ((A.restrictMap G f).run ((A.restrictMap G f).initCfg xG) τ)
      (A.run (A.initCfg (liftIn xG w)) (τ.map Subtype.val)) :=
  (restrictRel_init xG w).run τ

omit [DecidableEq P] [DecidableEq K] in
lemma pre_comp_val (σ : ℕ → G) (T : ℕ) :
    pre (fun m => (σ m).1) T = (pre σ T).map Subtype.val := by
  simp [pre, List.map_map, Function.comp_def]

/-- Termination transfers to the restriction: with `|Gᶜ| + s ≤ t`, an infinite execution of the
restricted algorithm with at most `s` faulty processes is an infinite execution of `A` with at
most `t` faulty processes (all processes outside `G` are faulty). -/
theorem Alg.Solves.restrictMap_termination [Fintype P] {t s : ℕ} {T : Task P In Out}
    (hA : A.Solves t T) (hG : Gᶜ.card + s ≤ t) (xG : G → In) (w : P → In) (σ : ℕ → G)
    (hσ : (Faulty σ).ncard ≤ s) (p : G) (hp : InfOften σ p) :
    ∃ T, (((A.restrictMap G f).run ((A.restrictMap G f).initCfg xG) (pre σ T)).out p).isSome := by
  set σA : ℕ → P := fun m => (σ m).1
  have hsub : Faulty σA ⊆ (↑Gᶜ : Set P) ∪ Subtype.val '' Faulty σ := by
    intro q hq
    by_cases hqG : q ∈ G
    · right
      refine ⟨⟨q, hqG⟩, fun hinf => hq ?_, rfl⟩
      intro N
      obtain ⟨m, hm, hmq⟩ := hinf N
      exact ⟨m, hm, by simp [σA, hmq]⟩
    · left; simpa using hqG
  have hF : (Faulty σA).ncard ≤ t := by
    refine le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) ?_
    refine le_trans (Set.ncard_union_le _ _) ?_
    rw [Set.ncard_coe_finset, Set.ncard_image_of_injective _ Subtype.val_injective]
    omega
  have hpA : InfOften σA p.1 := by
    intro N
    obtain ⟨m, hm, hmp⟩ := hp N
    exact ⟨m, hm, by simp [σA, hmp]⟩
  obtain ⟨T, hT⟩ := hA.2 (liftIn xG w) σA hF p.1 hpA
  refine ⟨T, ?_⟩
  have := ((Alg.run_restrictMap (A := A) (f := f) xG w (pre σ T)).1 p).2.2
  rw [this, ← pre_comp_val]
  simpa using hT

end Rel

end Cslib.SWMR
