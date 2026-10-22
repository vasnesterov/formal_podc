import Papers.PODC2025.GeneralizedQuorums.Defs
import Podc.Computability.Distributed.MessagePassing.ChannelFailures.Glue

/-!
# The lower bound (§6 and Appendix C), for any object with conflicting operations

We prove Lemma 2 and Theorem 2 for every safety specification `Spec` that has *conflicting
operations* for any two distinct processes (`Conflict Spec p₁ p₂`: two solo histories that are
incompatible when run one after the other). Lattice agreement, consensus, MWMR registers and SWMR
snapshots all have this property (`Objects.lean`).

The liveness assumption is only used through *solo termination* (`SoloTerm`), which follows both
from asynchronous obstruction-freedom and from obstruction-freedom under partial synchrony.
Hence one proof covers Theorem 2 and the lower bound of Theorem 6.
-/

namespace Podc.GeneralizedQuorums

open Cslib.ChannelFailures Cslib.SharedMemory

variable {P : Type} [DecidableEq P] [Fintype P] {A : ObjSpec} {M L : Type}

omit [DecidableEq P] [Fintype P] in
/-- The set `{x | x reaches t}` is closed under predecessors in `G \ f`. -/
lemma closed_reachTo (f : FailurePattern P) (t : P) : f.Closed {x | f.Reach x t} :=
  fun _ _ he hp => Reach.head he hp

omit [DecidableEq P] [Fintype P] in
/-- The set `{x | x reaches t, t does not reach x}` is closed under predecessors in `G \ f`. -/
lemma closed_reachTo_not (f : FailurePattern P) (t : P) :
    f.Closed {x | f.Reach x t ∧ ¬ f.Reach t x} :=
  fun _ _ he hp => ⟨Reach.head he hp.1, fun h => hp.2 (Reach.tail h he)⟩

/-- **Lemma 2** (generalized to any object with conflicting operations). If every finite
execution of `Alg` satisfies `Spec`, any two distinct processes have conflicting operations, and
`Alg` terminates solo at the correct processes of `T` under `f`, then `T` is strongly connected in
`G \ f`. -/
theorem lemma_2_of_soloTerm (Alg : Algorithm P A M L) {Spec : List (Label P A) → Prop}
    (hsafe : Alg.Satisfies Spec) (hconf : ∀ p₁ p₂ : P, p₁ ≠ p₂ → Conflict Spec p₁ p₂)
    {f : FailurePattern P} {T : Set P} (hT : T ⊆ (f.procs)ᶜ)
    (hsolo : ∀ p ∈ T, ∀ o, SoloTerm Alg f p o) : ∀ u ∈ T, ∀ v ∈ T, f.Reach u v := by
  intro u hu v hv
  by_contra huv
  have hu' : u ∉ f.procs := hT hu
  have hv' : v ∉ f.procs := hT hv
  -- `X₁ = R_u ∪ S_u`, `A₁ = R_u`, `X₂ = R_u ∪ R_v ∪ S_v`
  refine false_of_conflict Alg hsafe (f := f) (g := f) (X₁ := {x | f.Reach x u})
    (A₁ := {x | f.Reach x u ∧ ¬ f.Reach u x})
    (X₂ := {x | f.Reach x u ∧ ¬ f.Reach u x} ∪ {x | f.Reach x v}) (p₁ := u) (p₂ := v)
    (hconf u v fun h => huv (h ▸ reach_refl hu')) (closed_reachTo f u) (closed_reachTo_not f u)
    (fun x hx => hx.1) (reach_refl hu') (fun h => h.2 (reach_refl hu')) hu'
    (fun q p he hp => hp.elim (fun h => Or.inl (closed_reachTo_not f u q p he h))
      (fun h => Or.inr (closed_reachTo f v q p he h)))
    (Or.inr (reach_refl hv')) hv' ?_ (hsolo u hu) (hsolo v hv)
  rintro x ⟨hx | hx, hxu⟩
  · exact hx
  · exact ⟨hxu, fun h => huv (reach_trans h hx)⟩

/-- **Theorem 2 / Theorem 6 (lower bounds)**, generic form. If every finite execution of `Alg`
satisfies `Spec`, any two distinct processes have conflicting operations, `τ(f)` is a non-empty set
of correct processes for every `f ∈ F`, and `Alg` terminates solo at the processes of `τ(f)` under
`f`, then there are `R` and `W` such that `(F, R, W)` is a generalized quorum system, and moreover
`τ(f) ⊆ U_f` for every `f ∈ F`. -/
theorem theorem_2_of_soloTerm (Alg : Algorithm P A M L) {Spec : List (Label P A) → Prop}
    (hsafe : Alg.Satisfies Spec) (hconf : ∀ p₁ p₂ : P, p₁ ≠ p₂ → Conflict Spec p₁ p₂)
    {F : Set (FailurePattern P)} {τ : FailurePattern P → Set P}
    (hne : ∀ f ∈ F, (τ f).Nonempty) (hτ : ∀ f ∈ F, τ f ⊆ (f.procs)ᶜ)
    (hsolo : ∀ f ∈ F, ∀ p ∈ τ f, ∀ o, SoloTerm Alg f p o) :
    ∃ R W : Set (Set P), IsGQS F R W ∧ ∀ f ∈ F, τ f ⊆ Uf R W f := by
  classical
  -- a representative `t f ∈ τ f`
  choose t ht using hne
  -- `W_f`: the SCC of `t f`; `R_f`: the processes reaching it
  let Wf : ∀ f ∈ F, Set P := fun f hf => {x | f.Reach (t f hf) x ∧ f.Reach x (t f hf)}
  let Rf : ∀ f ∈ F, Set P := fun f hf => {x | f.Reach x (t f hf)}
  have htc : ∀ f (hf : f ∈ F), t f hf ∉ f.procs := fun f hf => hτ f hf (ht f hf)
  have hav : ∀ f (hf : f ∈ F), Available f (Wf f hf) ∧ ReachableFrom f (Wf f hf) (Rf f hf) := by
    intro f hf
    refine ⟨fun u hu v hv => reach_trans hu.2 hv.1, fun w hw => Reach.right_notMem hw.1,
      fun r hr => Reach.left_notMem hr, fun r hr w hw => reach_trans hr hw.1⟩
  set RR : Set (Set P) := {r | ∃ g, ∃ hg : g ∈ F, r = Rf g hg}
  set WW : Set (Set P) := {w | ∃ g, ∃ hg : g ∈ F, w = Wf g hg}
  have hWU : ∀ f (hf : f ∈ F), Wf f hf ⊆ U RR WW f :=
    fun f hf x hx => ⟨Wf f hf, ⟨⟨f, hf, rfl⟩, (hav f hf).1, Rf f hf, ⟨f, hf, rfl⟩, (hav f hf).2⟩, hx⟩
  refine ⟨RR, WW, ⟨?_, ?_⟩, ?_⟩
  · -- Consistency, by the partitioning argument
    rintro r ⟨g, hg, rfl⟩ w ⟨f, hf, rfl⟩
    by_contra hdisj
    rw [Set.not_nonempty_iff_eq_empty] at hdisj
    have hdis : ∀ x, x ∈ Rf g hg → x ∈ Wf f hf → False := fun x h₁ h₂ => by
      have : x ∈ Rf g hg ∩ Wf f hf := ⟨h₁, h₂⟩
      rw [hdisj] at this; exact this
    have hfg : t f hf ≠ t g hg := fun h =>
      hdis (t f hf) (by rw [h]; exact reach_refl (htc g hg))
        ⟨reach_refl (htc f hf), reach_refl (htc f hf)⟩
    refine false_of_conflict Alg hsafe (f := f) (g := g) (X₁ := Rf f hf)
      (A₁ := {x | f.Reach x (t f hf) ∧ ¬ f.Reach (t f hf) x}) (X₂ := Rf g hg)
      (hconf _ _ hfg) (closed_reachTo f _) (closed_reachTo_not f _) (fun x hx => hx.1)
      (reach_refl (htc f hf)) (fun h => h.2 (reach_refl (htc f hf))) (htc f hf)
      (closed_reachTo g _) (reach_refl (htc g hg)) (htc g hg) ?_
      (hsolo f hf _ (ht f hf)) (hsolo g hg _ (ht g hg))
    rintro x ⟨hxg, hxf⟩
    exact ⟨hxf, fun h => hdis x hxg ⟨h, hxf⟩⟩
  · -- Availability
    intro f hf
    exact ⟨Wf f hf, ⟨f, hf, rfl⟩, Rf f hf, ⟨f, hf, rfl⟩, hav f hf⟩
  · -- `τ(f) ⊆ W_f ⊆ U_f`, by Lemma 2
    intro f hf p hp
    have hsc := lemma_2_of_soloTerm Alg hsafe hconf (hτ f hf) (hsolo f hf)
    have hpW : p ∈ Wf f hf := ⟨hsc _ (ht f hf) _ hp, hsc _ hp _ (ht f hf)⟩
    exact subset_Uf _ _ f (hWU f hf hpW)

/-- **Lemma 2.** An `(f, T)`-obstruction-free implementation of an object with conflicting
operations (e.g. lattice agreement) has `T` strongly connected in `G \ f`. -/
theorem lemma_2 (Alg : Algorithm P A M L) {Spec : List (Label P A) → Prop}
    (hsafe : Alg.Satisfies Spec) (hconf : ∀ p₁ p₂ : P, p₁ ≠ p₂ → Conflict Spec p₁ p₂)
    {f : FailurePattern P} {T : Set P} (hT : T ⊆ (f.procs)ᶜ) (hOF : Alg.ObstructionFree f T) :
    ∀ u ∈ T, ∀ v ∈ T, f.Reach u v :=
  lemma_2_of_soloTerm Alg hsafe hconf hT fun _p hp o =>
    soloTerm_of_obstructionFree Alg hOF hp (hT hp) o

/-- **Theorem 2** (generic form). An `(F, τ)`-obstruction-free implementation of an object with
conflicting operations, with `τ(f)` non-empty, yields a generalized quorum system `(F, R, W)` with
`τ(f) ⊆ U_f`. -/
theorem theorem_2_generic (Alg : Algorithm P A M L) {Spec : List (Label P A) → Prop}
    (hsafe : Alg.Satisfies Spec) (hconf : ∀ p₁ p₂ : P, p₁ ≠ p₂ → Conflict Spec p₁ p₂)
    {F : Set (FailurePattern P)} {τ : FailurePattern P → Set P}
    (hne : ∀ f ∈ F, (τ f).Nonempty) (hτ : ∀ f ∈ F, τ f ⊆ (f.procs)ᶜ)
    (hOF : Alg.ObstructionFreeOn F τ) :
    ∃ R W : Set (Set P), IsGQS F R W ∧ ∀ f ∈ F, τ f ⊆ Uf R W f :=
  theorem_2_of_soloTerm Alg hsafe hconf hne hτ fun f hf _p hp o =>
    soloTerm_of_obstructionFree Alg (hOF f hf) hp (hτ f hf hp) o

end Podc.GeneralizedQuorums
