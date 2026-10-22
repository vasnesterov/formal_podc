import Papers.PODC2015.ABADetection.Common

/-!
# Observations 1 and 2: clean and dirty configurations are distinguishable

Paper, Section 2 (Observation 1, proof in Appendix B.1) and Appendix B.3 (Observation 2).

Let `p ≠ w0` be idle in the final configurations `C₁` of a `p`-clean execution `α₁` and `C₂` of
a `p`-dirty execution `α₂` (both standard). If `p` could not distinguish `C₁` and `C₂`
(`Impl.Agree p C₁ C₂`), then a solo run of a further operation of `p` would return the same
response from both (`soloOp_eq_of_agree`); it completes by obstruction-freedom (`soloOp_spec`).
In every linearization of the extended executions, the response is determined by the abstract
state just before the new operation, and real-time order (plus the standard-execution
discipline `Std`) pins down this state enough to force different responses:

* **ABA-detecting register** (`separates_aba`): a new `DRead()` of `p` returns flag `false`
  after the clean execution (the last write is linearized before `p`'s last clean read) and
  `true` after the dirty one (the write of the dirty round is linearized after all of `p`'s
  earlier reads).
* **LL/SC** (`separates_llsc`): a new `SC(y)` of `p` succeeds after the clean execution (`p`'s
  link from its clean `LL()` is still valid: only the writer executes `SC`, and all its operations
  are linearized before that `LL()`) and fails after the dirty one (the writer's `LL(); SC(x)`
  round succeeds and invalidates all links, and `p` executes no `LL()` afterwards).

The common part is `exists_solo_lin`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ABADetection

open Cslib.SharedMemory List

/-! ## Positions in duplicate-free lists -/

section Positions

variable {X Y : Type}

lemma exists_split_of_mem_map_fst {l : List (X × Y)} {a : X} (h : a ∈ l.map Prod.fst) :
    ∃ N₁ N₂ o, l = N₁ ++ (a, o) :: N₂ := by
  obtain ⟨⟨a', o⟩, hm, rfl⟩ := mem_map.1 h
  obtain ⟨N₁, N₂, rfl⟩ := append_of_mem hm
  exact ⟨N₁, N₂, o, rfl⟩

/-- If `[a, b]` is a sublist of the keys and `l` is split at `b`, then `a` is on the left. -/
lemma mem_left_of_sublist_split {l N₁ N₂ : List (X × Y)} {a b : X} {ob : Y}
    (hnd : (l.map Prod.fst).Nodup) (hl : l = N₁ ++ (b, ob) :: N₂)
    (h : [a, b].Sublist (l.map Prod.fst)) : a ∈ N₁.map Prod.fst := by
  subst hl; simp only [map_append, map_cons] at hnd h; exact mem_left_of_sublist_pair hnd h

/-- An entry to the right of `a` does not come before `a`. -/
lemma not_sublist_of_mem_right {l N₁ N₂ : List (X × Y)} {a y : X} {oa : Y}
    (hnd : (l.map Prod.fst).Nodup) (hl : l = N₁ ++ (a, oa) :: N₂) (hy : y ∈ N₂.map Prod.fst) :
    ¬ [y, a].Sublist (l.map Prod.fst) := by
  intro h
  have h1 := mem_left_of_sublist_split hnd hl h
  subst hl
  simp only [map_append, map_cons] at hnd
  exact (nodup_append.1 hnd).2.2 _ h1 _ (mem_cons_of_mem _ hy) rfl

/-- An entry to the left of `a` does not come after `a`. -/
lemma not_sublist_of_mem_left {l N₁ N₂ : List (X × Y)} {a y : X} {oa : Y}
    (hnd : (l.map Prod.fst).Nodup) (hl : l = N₁ ++ (a, oa) :: N₂) (hy : y ∈ N₁.map Prod.fst) :
    ¬ [a, y].Sublist (l.map Prod.fst) := by
  intro h
  exact not_sublist_pair_both hnd h (by
    subst hl
    simp only [map_append, map_cons]
    exact sublist_pair_iff.2 ⟨_, _, rfl, hy, mem_cons_self⟩)

lemma ne_of_mem_left {l N₁ N₂ : List (X × Y)} {a y : X} {oa : Y}
    (hnd : (l.map Prod.fst).Nodup) (hl : l = N₁ ++ (a, oa) :: N₂) (hy : y ∈ N₁.map Prod.fst) :
    y ≠ a := by
  subst hl
  simp only [map_append, map_cons] at hnd
  exact (nodup_append.1 hnd).2.2 _ hy _ mem_cons_self

end Positions

/-- The state reached by a sequential history split at an entry. -/
lemma runOps_split {A : ObjSpec} {K : Type} (q : A.State) (N₁ N₂ : List (K × A.Op)) (a : K)
    (o : A.Op) : A.runOps q ((N₁ ++ (a, o) :: N₂).map Prod.snd) =
      A.runOps (A.δ (A.runOps q (N₁.map Prod.snd)) o).1 (N₂.map Prod.snd) := by
  simp [ObjSpec.runOps_append]

/-! ## A solo operation after a reachable configuration, linearized -/

section Solo

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The operation of an invoked instance was invoked by its process. -/
lemma inv_mem_of_opOf {α : List (Label P A)} {y : OpId P} {o : A.Op}
    (h : opOf α y = some o) : Label.inv y.1 o ∈ α := by
  have hm : o ∈ opsOf α y.1 := mem_of_getElem? h
  simp only [opsOf, mem_filterMap] at hm
  obtain ⟨ℓ, hℓ, he⟩ := hm
  rwa [Label.eq_inv_of_invOf_eq_some he] at hℓ

/-- **Setup of Observations 1 and 2.** Let `p` be idle at the end of the execution `α`, and let
`p` run an operation `o` solo to completion (`I.soloOp p o C`, which terminates by
obstruction-freedom), receiving the response `r`. In some linearization `Lin` of the extended
execution, the new instance `(p, |opsOf α p|)` is preceded by a prefix `M₁` that contains every
operation completed in `α`, and whose entries are operations of `α`; the response `r` is the
response of `o` in the state reached by `M₁`. -/
lemma exists_solo_lin {I : Impl A B P L} (hlin : I.Linearizable) (hof : I.ObstructionFree)
    {p : P} {o : A.Op} (ho : I.allowed p o) {α : List (Label P A)} {C : Config A B P L}
    (hα : I.run α = some C) (hC : C.pend p = none) :
    ∃ r Lin M₁ M₂, respsOf (I.soloOp p o C) p = [r] ∧
      Lin = M₁ ++ ((p, (opsOf α p).length), o) :: M₂ ∧
      (Lin.map Prod.fst).Nodup ∧
      (A.δ (A.runOps A.init (M₁.map Prod.snd)) o).2 = r ∧
      (∀ a, Completed α a → a ∈ M₁.map Prod.fst) ∧
      (∀ y o', (y, o') ∈ M₁ → opOf α y = some o') ∧
      (∀ a b, Precedes α a b → b ∈ Lin.map Prod.fst → [a, b].Sublist (Lin.map Prod.fst)) := by
  obtain ⟨C', h1, -, h3, h4, h5⟩ := I.soloOp_spec hof p o ho hα hC
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.1 h5
  set σ := I.soloOp p o C with hσ
  obtain ⟨h, hh⟩ := hlin
  have hv : I.Valid (α ++ σ) := ⟨C', by rw [Impl.run_append_of_eq I hα, h1]⟩
  have hL := hh _ hv
  have hidle := I.run_idle_counts hα hC
  set K : OpId P := (p, (opsOf α p).length) with hK
  have hresp : respOf (α ++ σ) K = some r := by
    simp [respOf, hr, hidle, hK]
  obtain ⟨M₁, M₂, o', hs, hr'⟩ := ObjSpec.exists_split_of_respIn_eq_some (hL.respIn_eq hresp)
  have hoK : opOf (α ++ σ) K = some o := by
    simp [opOf, h4, hK]
  have ho' : o' = o := by
    have := hL.op_eq (K, o') (by rw [hs]; simp)
    rw [hoK] at this; exact (Option.some.inj this).symm
  subst ho'
  have hnd := hL.nodup
  have hσo : ∀ q, q ≠ p → opsOf σ q = [] := fun q hq =>
    opsOf_eq_nil_of_proc_ne fun ℓ hℓ => by rw [h3 ℓ hℓ]; exact Ne.symm hq
  refine ⟨r, h (α ++ σ), M₁, M₂, hr, hs, hnd, hr', fun a ha => ?_, fun y o' hy => ?_,
    fun a b hab hb => hL.realtime a b hab.mono hb⟩
  · have hpre : Precedes (α ++ σ) a K := ⟨α, σ, rfl, ha, by simp [Invoked, hK]⟩
    exact mem_left_of_sublist_split hnd hs (hL.realtime a K hpre (by rw [hs]; simp))
  · have hyL : (y, o') ∈ h (α ++ σ) := by rw [hs]; simp [hy]
    have hop := hL.op_eq _ hyL
    have hyK : y ≠ K := ne_of_mem_left hnd hs (mem_map_of_mem (f := Prod.fst) hy)
    simp only [opOf, opsOf_append] at hop ⊢
    by_cases hlt : y.2 < (opsOf α y.1).length
    · rwa [getElem?_append_left hlt] at hop
    · exfalso
      rw [getElem?_append_right (by omega)] at hop
      by_cases hyp : y.1 = p
      · rw [hyp, h4] at hop
        have : y.2 - (opsOf α y.1).length = 0 := by
          rw [hyp]
          rcases hk : y.2 - (opsOf α p).length with _ | n
          · rfl
          · rw [hk] at hop; simp at hop
        apply hyK
        obtain ⟨y1, y2⟩ := y
        simp only at hyp this hlt
        subst hyp
        simp only [hK, Prod.mk.injEq, true_and]
        omega
      · rw [hσo _ hyp] at hop; simp at hop

end Solo

/-! ## Observation 1: ABA-detecting registers -/

section ABA

variable {P V : Type} [DecidableEq P] {v₀ : V}

/-- Without writes, a cleared flag stays cleared. -/
lemma aba_flag_false {p : P} (q : (abaObj P V v₀).State) (os : List (abaObj P V v₀).Op)
    (hq : q.2 p = false) (hos : ∀ x, ABAOp.dwrite x ∉ os) :
    ((abaObj P V v₀).runOps q os).2 p = false := by
  induction os generalizing q with
  | nil => exact hq
  | cons o os ih =>
    apply ih _ _ (fun x hx => hos x (mem_cons_of_mem _ hx))
    cases o with
    | dread p' => simp [Function.update_apply, hq]
    | dwrite x => exact absurd mem_cons_self (hos x)

/-- Without reads by `p`, a set flag of `p` stays set. -/
lemma aba_flag_true {p : P} (q : (abaObj P V v₀).State) (os : List (abaObj P V v₀).Op)
    (hq : q.2 p = true) (hos : ABAOp.dread p ∉ os) :
    ((abaObj P V v₀).runOps q os).2 p = true := by
  induction os generalizing q with
  | nil => exact hq
  | cons o os ih =>
    apply ih _ _ (fun hx => hos (mem_cons_of_mem _ hx))
    cases o with
    | dread p' =>
      have : p' ≠ p := fun h => hos (h ▸ mem_cons_self)
      simp [hq, Ne.symm this]
    | dwrite x => simp

end ABA

/-- **Observation 1** (paper, Section 2; proof in Appendix B.1), for linearizable,
obstruction-free implementations of a single-writer ABA-detecting register: for every reader
`p`, a `p`-clean and a `p`-dirty configuration in which `p` is idle are distinguishable by `p`.
(The paper assumes only nondeterministic solo-termination, which obstruction-freedom implies for
deterministic processes.) -/
theorem separates_aba {P V ι L : Type} [DecidableEq P] [DecidableEq ι] {B : ι → ObjSpec} {v₀ : V}
    (I : Impl (abaObj P V v₀) B P L) (w0 : P) (x : V)
    (hlin : I.Linearizable) (hof : I.ObstructionFree)
    (hrd : ∀ p, p ≠ w0 → I.allowed p (.dread p)) :
    Separates I w0 (fun p => .dread p) [.dwrite x] := by
  intro p hp α₁ α₂ C₁ C₂ hr₁ hr₂ hs₁ hs₂ hcl hdi hp₁ hp₂ hag
  obtain ⟨r, Lin₁, M₁, M₂, hσ₁, hsp₁, hnd₁, hres₁, hcomp₁, hold₁, hrt₁⟩ :=
    exists_solo_lin hlin hof (hrd p hp) hr₁ hp₁
  obtain ⟨r', Lin₂, M₁', M₂', hσ₂, hsp₂, hnd₂, hres₂, hcomp₂, hold₂, hrt₂⟩ :=
    exists_solo_lin hlin hof (hrd p hp) hr₂ hp₂
  have hrr : r = r' := by
    rw [I.soloOp_eq_of_agree hag, hσ₂] at hσ₁
    exact (List.cons.inj hσ₁).1.symm
  -- the clean execution: the new read returns `false`
  obtain ⟨k, hk, hkc, hkw⟩ := hcl
  obtain ⟨N₁, N₂, o₁, hM₁⟩ := exists_split_of_mem_map_fst (hcomp₁ _ hkc)
  have ho₁ : o₁ = .dread p := by
    have := hold₁ (p, k) o₁ (by rw [hM₁]; simp); rw [hk] at this; exact (Option.some.inj this).symm
  subst ho₁
  have hLin₁ : Lin₁ = N₁ ++ ((p, k), .dread p) ::
      (N₂ ++ ((p, (opsOf α₁ p).length), .dread p) :: M₂) := by
    rw [hsp₁, hM₁]; simp
  have hclean : r.2 = false := by
    rw [← hres₁, hM₁, runOps_split]
    refine aba_flag_false (p := p) _ _ (by simp) ?_
    · intro x' hx'
      obtain ⟨⟨y, o⟩, hy, hyo⟩ := mem_map.1 hx'
      simp only at hyo; subst hyo
      have hop := hold₁ y (.dwrite x') (by rw [hM₁]; simp [hy])
      have hw := hs₁ _ _ (inv_mem_of_opOf hop)
      obtain ⟨y1, y2⟩ := y
      have hyw : y1 = w0 := by simp at hw; exact hw.1
      subst hyw
      have hpre := hkw y2 (Invoked.of_opOf_eq_some hop)
      exact not_sublist_of_mem_right hnd₁ hLin₁ (by simp; exact Or.inl ⟨_, hy⟩)
        (hrt₁ _ _ hpre (by rw [hLin₁]; simp))
  -- the dirty execution: the new read returns `true`
  obtain ⟨j, hj, hjp⟩ := hdi
  obtain ⟨hjo, hjc⟩ := hj 0 (by simp)
  simp only [Nat.add_zero, getElem_cons_zero] at hjo hjc
  obtain ⟨N₁', N₂', o₂, hM₁'⟩ := exists_split_of_mem_map_fst (hcomp₂ _ hjc)
  have ho₂ : o₂ = .dwrite x := by
    have := hold₂ (w0, j) o₂ (by rw [hM₁']; simp); rw [hjo] at this; exact (Option.some.inj this).symm
  subst ho₂
  have hLin₂ : Lin₂ = N₁' ++ ((w0, j), .dwrite x) ::
      (N₂' ++ ((p, (opsOf α₂ p).length), .dread p) :: M₂') := by
    rw [hsp₂, hM₁']; simp
  have hdirty : r'.2 = true := by
    rw [← hres₂, hM₁', runOps_split]
    refine aba_flag_true (p := p) _ _ rfl ?_
    · intro hx'
      obtain ⟨⟨y, o⟩, hy, hyo⟩ := mem_map.1 hx'
      simp only at hyo; subst hyo
      have hop := hold₂ y (.dread p) (by rw [hM₁']; simp [hy])
      have hw := hs₂ _ _ (inv_mem_of_opOf hop)
      obtain ⟨y1, y2⟩ := y
      have hyp : y1 = p := by simp at hw; exact hw.2.symm
      subst hyp
      have hpre := hjp y2 (Invoked.of_opOf_eq_some hop)
      exact not_sublist_of_mem_right hnd₂ hLin₂ (by simp; exact Or.inl ⟨_, hy⟩)
        (hrt₂ _ _ hpre (by rw [hLin₂]; simp))
  rw [hrr, hdirty] at hclean
  exact absurd hclean (by simp)

/-! ## Observation 2: LL/SC -/

section LLSC

variable {V K : Type} [DecidableEq K] {v₀ : V}

/-- `LL()` creates a link. -/
lemma llsc_mem_δ_ll (q : (llscObj V K v₀).State) (k : K) :
    k ∈ ((llscObj V K v₀).δ q (.ll k)).1.2 := by
  by_cases h : k ∈ q.2 <;> simp [h]

/-- Without `SC`s, a valid link stays valid. -/
lemma llsc_link_mem {k : K} (q : (llscObj V K v₀).State) (os : List (llscObj V K v₀).Op)
    (hq : k ∈ q.2) (hos : ∀ k' v, LLOp.sc k' v ∉ os) :
    k ∈ ((llscObj V K v₀).runOps q os).2 := by
  induction os generalizing q with
  | nil => exact hq
  | cons o os ih =>
    apply ih _ _ (fun k' v hx => hos k' v (mem_cons_of_mem _ hx))
    cases o with
    | ll k' => by_cases h : k' ∈ q.2 <;> simp [h, hq]
    | sc k' v => exact absurd mem_cons_self (hos k' v)
    | vl k' => exact hq

/-- Without `LL`s by `k`, an invalid link of `k` stays invalid. -/
lemma llsc_link_not_mem {k : K} (q : (llscObj V K v₀).State) (os : List (llscObj V K v₀).Op)
    (hq : k ∉ q.2) (hos : LLOp.ll k ∉ os) :
    k ∉ ((llscObj V K v₀).runOps q os).2 := by
  induction os generalizing q with
  | nil => exact hq
  | cons o os ih =>
    apply ih _ _ (fun hx => hos (mem_cons_of_mem _ hx))
    cases o with
    | ll k' =>
      have : k' ≠ k := fun h => hos (h ▸ mem_cons_self)
      by_cases h : k' ∈ q.2 <;> simp [h, hq, Ne.symm this]
    | sc k' v => by_cases h : k' ∈ q.2 <;> simp [h, hq]
    | vl k' => exact hq

end LLSC

/-- **Observation 2** (paper, Appendix B.3), for linearizable, obstruction-free implementations
of LL/SC objects (no `VL` is needed: only `LL` and `SC` are invoked): for every process `p ≠ w0`,
a `p`-clean configuration (a complete `LL()` of `p` after all operations of `w0`) and a `p`-dirty
configuration (a complete round `LL(); SC(x)` of `w0` after all operations of `p`) in which `p` is
idle are distinguishable by `p`. The distinguishing operation is a solo `SC(y)` of `p`. -/
theorem separates_llsc {P V ι L : Type} [DecidableEq P] [DecidableEq ι] {B : ι → ObjSpec} {v₀ : V}
    (I : Impl (llscObj V P v₀) B P L) (w0 : P) (x y : V)
    (hlin : I.Linearizable) (hof : I.ObstructionFree)
    (hsc : ∀ p, p ≠ w0 → I.allowed p (.sc p y)) :
    Separates I w0 (fun p => .ll p) [.ll w0, .sc w0 x] := by
  intro p hp α₁ α₂ C₁ C₂ hr₁ hr₂ hs₁ hs₂ hcl hdi hp₁ hp₂ hag
  obtain ⟨r, Lin₁, M₁, M₂, hσ₁, hsp₁, hnd₁, hres₁, hcomp₁, hold₁, hrt₁⟩ :=
    exists_solo_lin hlin hof (hsc p hp) hr₁ hp₁
  obtain ⟨r', Lin₂, M₁', M₂', hσ₂, hsp₂, hnd₂, hres₂, hcomp₂, hold₂, hrt₂⟩ :=
    exists_solo_lin hlin hof (hsc p hp) hr₂ hp₂
  have hrr : r = r' := by
    rw [I.soloOp_eq_of_agree hag, hσ₂] at hσ₁
    exact (List.cons.inj hσ₁).1.symm
  -- the clean execution: the new `SC` succeeds
  obtain ⟨k, hk, hkc, hkw⟩ := hcl
  obtain ⟨N₁, N₂, o₁, hM₁⟩ := exists_split_of_mem_map_fst (hcomp₁ _ hkc)
  have ho₁ : o₁ = .ll p := by
    have := hold₁ (p, k) o₁ (by rw [hM₁]; simp); rw [hk] at this
    exact (Option.some.inj this).symm
  subst ho₁
  have hLin₁ : Lin₁ = N₁ ++ ((p, k), .ll p) ::
      (N₂ ++ ((p, (opsOf α₁ p).length), .sc p y) :: M₂) := by
    rw [hsp₁, hM₁]; simp
  have hclean : r.2 = true := by
    rw [← hres₁, hM₁, runOps_split]
    have hmem := llsc_link_mem (k := p) ((llscObj V P v₀).δ
      ((llscObj V P v₀).runOps (llscObj V P v₀).init (N₁.map Prod.snd)) (.ll p)).1
      (N₂.map Prod.snd) (llsc_mem_δ_ll _ _) (by
        intro k' v hx'
        obtain ⟨⟨z, o⟩, hz, hzo⟩ := mem_map.1 hx'
        simp only at hzo; subst hzo
        have hop := hold₁ z (.sc k' v) (by rw [hM₁]; simp [hz])
        have hw := hs₁ _ _ (inv_mem_of_opOf hop)
        obtain ⟨z1, z2⟩ := z
        have hzw : z1 = w0 := by simp at hw; exact hw.1
        subst hzw
        have hpre := hkw z2 (Invoked.of_opOf_eq_some hop)
        exact not_sublist_of_mem_right hnd₁ hLin₁ (by simp; exact Or.inl ⟨_, hz⟩)
          (hrt₁ _ _ hpre (by rw [hLin₁]; simp)))
    simp [hmem]
  -- the dirty execution: the writer's `SC` succeeds, and the new `SC` of `p` fails
  have hwf₂ : WellFormed α₂ := Impl.Valid.wellFormed (I := I) ⟨C₂, hr₂⟩
  obtain ⟨j, hj, hjp⟩ := hdi
  obtain ⟨hjo0, -⟩ := hj 0 (by simp)
  obtain ⟨hjo1, hjc1⟩ := hj 1 (by simp)
  simp only [Nat.add_zero, getElem_cons_zero, getElem_cons_succ] at hjo0 hjo1 hjc1
  have hpre01 : Precedes α₂ (w0, j) (w0, j + 1) :=
    hwf₂.precedes_of_lt (by omega) (Invoked.of_opOf_eq_some hjo1)
  obtain ⟨N₁, N₂, o₂, hM₁'⟩ := exists_split_of_mem_map_fst (hcomp₂ _ hjc1)
  have ho₂ : o₂ = .sc w0 x := by
    have := hold₂ (w0, j + 1) o₂ (by rw [hM₁']; simp); rw [hjo1] at this
    exact (Option.some.inj this).symm
  subst ho₂
  have hLin₂ : Lin₂ = N₁ ++ ((w0, j + 1), .sc w0 x) ::
      (N₂ ++ ((p, (opsOf α₂ p).length), .sc p y) :: M₂') := by
    rw [hsp₂, hM₁']; simp
  have hjN : (w0, j) ∈ N₁.map Prod.fst :=
    mem_left_of_sublist_split hnd₂ hLin₂ (hrt₂ _ _ hpre01 (by rw [hLin₂]; simp))
  obtain ⟨N₀, N₀', o₃, hN₁⟩ := exists_split_of_mem_map_fst hjN
  have ho₃ : o₃ = .ll w0 := by
    have := hold₂ (w0, j) o₃ (by rw [hM₁', hN₁]; simp); rw [hjo0] at this
    exact (Option.some.inj this).symm
  subst ho₃
  have hLin₂' : Lin₂ = N₀ ++ ((w0, j), .ll w0) ::
      (N₀' ++ ((w0, j + 1), .sc w0 x) :: (N₂ ++ ((p, (opsOf α₂ p).length), .sc p y) :: M₂')) := by
    rw [hLin₂, hN₁]; simp
  -- the writer's link is valid at its `SC`
  have hw0 : w0 ∈ ((llscObj V P v₀).runOps (llscObj V P v₀).init (N₁.map Prod.snd)).2 := by
    rw [hN₁, runOps_split]
    refine llsc_link_mem _ _ (llsc_mem_δ_ll _ _) ?_
    intro k' v hx'
    obtain ⟨⟨z, o⟩, hz, hzo⟩ := mem_map.1 hx'
    simp only at hzo; subst hzo
    have hop := hold₂ z (.sc k' v) (by rw [hM₁', hN₁]; simp [hz])
    have hw := hs₂ _ _ (inv_mem_of_opOf hop)
    obtain ⟨z1, i⟩ := z
    have hzw : z1 = w0 := by simp at hw; exact hw.1
    subst hzw
    have hzr : (z1, i) ∈ (N₀' ++ ((z1, j + 1), LLOp.sc z1 x) ::
        (N₂ ++ ((p, (opsOf α₂ p).length), LLOp.sc p y) :: M₂')).map Prod.fst := by
      simp; exact Or.inl ⟨_, hz⟩
    have hzl : (z1, i) ∈ N₁.map Prod.fst := by rw [hN₁]; simp; exact Or.inr (Or.inr ⟨_, hz⟩)
    rcases lt_trichotomy i j with h | rfl | h
    · exact not_sublist_of_mem_right hnd₂ hLin₂' hzr (hrt₂ _ _
        (hwf₂.precedes_of_lt h (Invoked.of_opOf_eq_some hjo0)) (by rw [hLin₂']; simp))
    · rw [hjo0] at hop; cases hop
    · rcases Nat.lt_or_ge (j + 1) i with h' | h'
      · exact not_sublist_of_mem_left hnd₂ hLin₂ hzl (hrt₂ _ _
          (hwf₂.precedes_of_lt h' (Invoked.of_opOf_eq_some hop)) (by rw [hLin₂]; simp [hzl]))
      · exact ne_of_mem_left hnd₂ hLin₂ hzl (by rw [show i = j + 1 by omega])
  have hdirty : r'.2 = false := by
    rw [← hres₂, hM₁', runOps_split]
    have hnm := llsc_link_not_mem (k := p) ((llscObj V P v₀).δ
      ((llscObj V P v₀).runOps (llscObj V P v₀).init (N₁.map Prod.snd)) (.sc w0 x)).1
      (N₂.map Prod.snd) (by simp [hw0]) (by
        intro hx'
        obtain ⟨⟨z, o⟩, hz, hzo⟩ := mem_map.1 hx'
        simp only at hzo; subst hzo
        have hop := hold₂ z (.ll p) (by rw [hM₁']; simp [hz])
        have hw := hs₂ _ _ (inv_mem_of_opOf hop)
        obtain ⟨z1, z2⟩ := z
        have hzp : z1 = p := by
          simp at hw
          rcases hw with ⟨-, h⟩ | ⟨-, h⟩
          · exact absurd h hp
          · exact h.symm
        subst hzp
        have hpre := (hjp z2 (Invoked.of_opOf_eq_some hop)).trans hwf₂ hpre01
        exact not_sublist_of_mem_right hnd₂ hLin₂ (by simp; exact Or.inl ⟨_, hz⟩)
          (hrt₂ _ _ hpre (by rw [hLin₂]; simp)))
    simp [hnm]
  rw [hrr, hdirty] at hclean
  exact absurd hclean (by simp)

end Cslib.SharedMemory.ABADetection
