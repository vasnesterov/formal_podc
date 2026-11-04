import Mathlib

/-!
# Safety–liveness exclusion: the set-theoretic layer (Sections 3–4)

V. Bushkov, R. Guerraoui. *Safety-Liveness Exclusion in Distributed Computing.* PODC 2015.

Sections 3–4 of the paper are pure set theory over histories once two facts about the
implementation model are known:

* `fair I`, the set of fair histories of an implementation `I`;
* `ensS I`, "`I` is an admissible implementation and `I` ensures the safety property `S`".

This file fixes such data abstractly (`Setting`) and proves:

* the characterization "`L` excludes `S` iff there is an adversary set w.r.t. `L` and `S`"
  (`Setting.excludes_iff_exists_adversarySet`, stated after Definition 4.3);
* **Theorem 4.4** (`Setting.theorem_4_4`): a weakest liveness property excluding `S` exists iff
  `Gmax`, the intersection of all adversary sets w.r.t. `Lmax`, is itself an adversary set;
* the corollary scheme of **Corollaries 4.5–4.6** (`Setting.no_weakest_of_disjoint`);
* **Lemma 4.8** (`Setting.lemma_4_8`);
* the exact characterization of strongest non-excluding liveness properties
  (`Setting.isStrongestNonExcl_iff`): it exists iff some implementation ensuring `S` has all its
  fair histories outside `Lmax` in the *core* (histories fair for *every* implementation ensuring
  `S`); it is then `Lmax ∪ core`. Theorem 4.9 ("it must be `Lmax`") is thus equivalent to
  `core ⊆ Lmax` whenever a strongest one exists (`Setting.eq_Lmax_of_core_subset`); whether this
  holds depends on the concrete model, see `Theorem49.lean` and `Counterexample.lean`;
* the corollary scheme of **Corollaries 4.10–4.11** (`Setting.no_strongest_of_excludes_Lmax`).

The order on liveness properties is set inclusion (`L₁` is stronger than `L₂` iff `L₁ ⊆ L₂`),
as in all proofs of the paper.
-/

namespace Podc.SafetyLivenessExclusion

universe u v

/-- The data of Section 4 for a fixed safety property `S` and strongest liveness requirement
`Lmax`. `ι` indexes implementations (of the fixed object type, in the fixed class of admissible
implementations); `ensS I` says that `I` ensures `S`; `fair I` is its set of fair histories. -/
structure Setting (H : Type u) (ι : Type v) where
  /-- Fair histories of an implementation. -/
  fair : ι → Set H
  /-- `I` ensures the safety property `S`. -/
  ensS : ι → Prop
  /-- The safety property. -/
  S : Set H
  /-- The strongest liveness requirement. -/
  Lmax : Set H

namespace Setting

variable {H : Type u} {ι : Type v} (Θ : Setting H ι)

/-- Definition 3.2: a liveness property is a weakening of `Lmax`. -/
def IsLiveness (L : Set H) : Prop := Θ.Lmax ⊆ L

/-- Definition 4.1: `L` excludes `S` if no implementation ensures both `S` and `L`. -/
def Excludes (L : Set H) : Prop := ¬ ∃ I, Θ.ensS I ∧ Θ.fair I ⊆ L

/-- Definition 4.2 (with "`L'` stronger than `L`" read as `L' ⊆ L`). -/
def IsWeakestExcl (L : Set H) : Prop :=
  Θ.IsLiveness L ∧ Θ.Excludes L ∧ ∀ L', Θ.IsLiveness L' → Θ.Excludes L' → L' ⊆ L

/-- Definition 4.7 (with "`L'` weaker than `L`" read as `L ⊆ L'`). -/
def IsStrongestNonExcl (L : Set H) : Prop :=
  Θ.IsLiveness L ∧ ¬ Θ.Excludes L ∧ ∀ L', Θ.IsLiveness L' → ¬ Θ.Excludes L' → L ⊆ L'

/-- Definition 4.3: an adversary set w.r.t. `L` and `S`. Condition (2), "`F` is contained in the
complement of `L`", is `Disjoint F L`. -/
def IsAdversarySet (L F : Set H) : Prop :=
  F.Nonempty ∧ F ⊆ Θ.S ∧ Disjoint F L ∧ ∀ I, Θ.ensS I → (Θ.fair I ∩ F).Nonempty

/-- `𝓕(Lmax)`: all adversary sets w.r.t. `Lmax` and `S`. -/
def advSets : Set (Set H) := {F | Θ.IsAdversarySet Θ.Lmax F}

/-- `Gmax`, the intersection of all adversary sets w.r.t. `Lmax` and `S` (the whole type if there
is none). -/
def Gmax : Set H := ⋂₀ Θ.advSets

/-- An adversary set witnesses exclusion (this direction needs no hypothesis). -/
theorem excludes_of_adversarySet {L F : Set H} (hF : Θ.IsAdversarySet L F) : Θ.Excludes L := by
  rintro ⟨I, hI, hIL⟩
  obtain ⟨h, hfair, hF'⟩ := hF.2.2.2 I hI
  exact Set.disjoint_left.1 hF.2.2.1 hF' (hIL hfair)

/-- The remark after Definition 4.3: `L` excludes `S` iff there is an adversary set w.r.t. `L`
and `S`. The direction "⇒" needs that fair histories of implementations ensuring `S` lie in `S`
(limit closure) and that some implementation ensures `S` (a consequence of the paper's standing
assumptions on `S`). -/
theorem excludes_iff_exists_adversarySet (hfair : ∀ I, Θ.ensS I → Θ.fair I ⊆ Θ.S)
    (hex : ∃ I, Θ.ensS I) (L : Set H) :
    Θ.Excludes L ↔ ∃ F, Θ.IsAdversarySet L F := by
  refine ⟨fun hL => ?_, fun ⟨F, hF⟩ => Θ.excludes_of_adversarySet hF⟩
  have key : ∀ I, Θ.ensS I → ∃ h ∈ Θ.fair I, h ∉ L := by
    intro I hI
    by_contra hcon
    push Not at hcon
    exact hL ⟨I, hI, hcon⟩
  refine ⟨{h | ∃ I, Θ.ensS I ∧ h ∈ Θ.fair I ∧ h ∉ L}, ?_, ?_, ?_, ?_⟩
  · obtain ⟨I, hI⟩ := hex
    obtain ⟨h, hh, hhL⟩ := key I hI
    exact ⟨h, I, hI, hh, hhL⟩
  · rintro h ⟨I, hI, hh, -⟩
    exact hfair I hI hh
  · exact Set.disjoint_left.2 fun h ⟨_, _, _, hhL⟩ => hhL
  · intro I hI
    obtain ⟨h, hh, hhL⟩ := key I hI
    exact ⟨h, hh, I, hI, hh, hhL⟩

/-- An adversary set w.r.t. a liveness property is an adversary set w.r.t. `Lmax`. -/
theorem IsAdversarySet.mono {Θ : Setting H ι} {L L' F : Set H} (hF : Θ.IsAdversarySet L F) (hLL' : L' ⊆ L) :
    Θ.IsAdversarySet L' F :=
  ⟨hF.1, hF.2.1, hF.2.2.1.mono_right hLL', hF.2.2.2⟩

/-- **Theorem 4.4.** A weakest liveness property that excludes `S` exists iff `Gmax` is an
adversary set w.r.t. `Lmax` and `S`. (When there is no adversary set w.r.t. `Lmax`, `Gmax` is the
whole type and both sides are false.) -/
theorem theorem_4_4 (hfair : ∀ I, Θ.ensS I → Θ.fair I ⊆ Θ.S) (hex : ∃ I, Θ.ensS I) :
    (∃ L, Θ.IsWeakestExcl L) ↔ Θ.Gmax ∈ Θ.advSets := by
  have hchar := Θ.excludes_iff_exists_adversarySet hfair hex
  constructor
  · rintro ⟨Lw, hLive, hExcl, hWeak⟩
    obtain ⟨Fw, hFw⟩ := (hchar Lw).1 hExcl
    -- `Lw` is the complement of `Fw`.
    have hLw : Lw = Fwᶜ := by
      apply Set.Subset.antisymm
      · intro h hh hhF
        exact Set.disjoint_left.1 hFw.2.2.1 hhF hh
      · intro h hh
        by_contra hhL
        have hLive' : Θ.IsLiveness (Lw ∪ {h}) := hLive.trans Set.subset_union_left
        have hAdv : Θ.IsAdversarySet (Lw ∪ {h}) Fw := by
          refine ⟨hFw.1, hFw.2.1, ?_, hFw.2.2.2⟩
          refine Set.disjoint_union_right.2 ⟨hFw.2.2.1, ?_⟩
          exact Set.disjoint_singleton_right.2 hh
        have := hWeak _ hLive' (Θ.excludes_of_adversarySet hAdv)
        exact hhL (this (Set.mem_union_right _ rfl))
    -- `Fw` is below every adversary set w.r.t. `Lmax`.
    have hFwLmax : Fw ∈ Θ.advSets := hFw.mono hLive
    have hbelow : ∀ F ∈ Θ.advSets, Fw ⊆ F := by
      intro F hF
      have hLiveF : Θ.IsLiveness Fᶜ := fun h hh hhF => Set.disjoint_left.1 hF.2.2.1 hhF hh
      have hAdvF : Θ.IsAdversarySet Fᶜ F :=
        ⟨hF.1, hF.2.1, disjoint_compl_right, hF.2.2.2⟩
      have hsub := hWeak _ hLiveF (Θ.excludes_of_adversarySet hAdvF)
      rw [hLw] at hsub
      exact Set.compl_subset_compl.1 hsub
    have hFwG : Fw ⊆ Θ.Gmax := Set.subset_sInter hbelow
    refine ⟨hFw.1.mono hFwG, (Set.sInter_subset_of_mem hFwLmax).trans hFwLmax.2.1,
      (Set.sInter_subset_of_mem hFwLmax |> Disjoint.mono_left) hFwLmax.2.2.1, ?_⟩
    intro I hI
    obtain ⟨h, hh, hhF⟩ := hFw.2.2.2 I hI
    exact ⟨h, hh, hFwG hhF⟩
  · intro hG
    refine ⟨Θ.Gmaxᶜ, fun h hh hhG => Set.disjoint_left.1 hG.2.2.1 hhG hh,
      Θ.excludes_of_adversarySet ⟨hG.1, hG.2.1, disjoint_compl_right, hG.2.2.2⟩, ?_⟩
    intro L hL hLex
    obtain ⟨F, hF⟩ := (hchar L).1 hLex
    have hFmax : F ∈ Θ.advSets := hF.mono hL
    intro h hh hhG
    exact Set.disjoint_left.1 hF.2.2.1 (Set.sInter_subset_of_mem hFmax hhG) hh

/-- In the situation of Theorem 4.4, the weakest liveness property excluding `S` is the
complement of `Gmax`. -/
theorem isWeakestExcl_compl_Gmax (hfair : ∀ I, Θ.ensS I → Θ.fair I ⊆ Θ.S)
    (hex : ∃ I, Θ.ensS I) (hG : Θ.Gmax ∈ Θ.advSets) : Θ.IsWeakestExcl Θ.Gmaxᶜ := by
  refine ⟨fun h hh hhG => Set.disjoint_left.1 hG.2.2.1 hhG hh,
    Θ.excludes_of_adversarySet ⟨hG.1, hG.2.1, disjoint_compl_right, hG.2.2.2⟩, ?_⟩
  intro L hL hLex
  obtain ⟨F, hF⟩ := (Θ.excludes_iff_exists_adversarySet hfair hex L).1 hLex
  intro h hh hhG
  exact Set.disjoint_left.1 hF.2.2.1 (Set.sInter_subset_of_mem (hF.mono hL) hhG) hh

/-- **Corollaries 4.5 and 4.6** (scheme). If there are two disjoint adversary sets w.r.t. `Lmax`
and `S`, no weakest liveness property excludes `S`. The paper instantiates `F₁, F₂` with the
consensus adversary of [5] and the TM adversary of [4] run with the roles of `p₁, p₂` swapped. -/
theorem no_weakest_of_disjoint (hfair : ∀ I, Θ.ensS I → Θ.fair I ⊆ Θ.S)
    (hex : ∃ I, Θ.ensS I) {F₁ F₂ : Set H} (h₁ : F₁ ∈ Θ.advSets) (h₂ : F₂ ∈ Θ.advSets)
    (hdisj : Disjoint F₁ F₂) : ¬ ∃ L, Θ.IsWeakestExcl L := by
  rw [Θ.theorem_4_4 hfair hex]
  intro hG
  obtain ⟨h, hh⟩ := hG.1
  exact Set.disjoint_left.1 hdisj (Set.sInter_subset_of_mem h₁ hh)
    (Set.sInter_subset_of_mem h₂ hh)

/-- An implementation `I` ensures `L` if all its fair histories are in `L`. -/
def Ensures (I : ι) (L : Set H) : Prop := Θ.fair I ⊆ L

/-- **Lemma 4.8.** The strongest liveness property ensured by `I` is `Lmax ∪ fair(I)`: it is a
liveness property, `I` ensures it, and it is stronger than every liveness property that `I`
ensures. -/
theorem lemma_4_8 (I : ι) :
    Θ.IsLiveness (Θ.Lmax ∪ Θ.fair I) ∧ Θ.Ensures I (Θ.Lmax ∪ Θ.fair I) ∧
      ∀ L, Θ.IsLiveness L → Θ.Ensures I L → Θ.Lmax ∪ Θ.fair I ⊆ L :=
  ⟨Set.subset_union_left, Set.subset_union_right, fun _ hL hI => Set.union_subset hL hI⟩

/-- The *core*: histories that are fair for every implementation ensuring `S`. -/
def core : Set H := {h | ∀ I, Θ.ensS I → h ∈ Θ.fair I}

/-- Characterization of strongest non-excluding liveness properties: `L` is one iff
`L = Lmax ∪ core` and some implementation ensuring `S` has all fair histories in `Lmax ∪ core`. -/
theorem isStrongestNonExcl_iff (L : Set H) :
    Θ.IsStrongestNonExcl L ↔
      L = Θ.Lmax ∪ Θ.core ∧ ∃ I, Θ.ensS I ∧ Θ.fair I ⊆ Θ.Lmax ∪ Θ.core := by
  constructor
  · rintro ⟨hLive, hNE, hStr⟩
    obtain ⟨Is, hIs, hIsL⟩ := not_not.1 hNE
    have hLsub : ∀ I, Θ.ensS I → L ⊆ Θ.Lmax ∪ Θ.fair I := fun I hI =>
      hStr _ Set.subset_union_left (fun hex => hex ⟨I, hI, Set.subset_union_right⟩)
    have hcore : L ⊆ Θ.Lmax ∪ Θ.core := by
      intro h hh
      by_cases hm : h ∈ Θ.Lmax
      · exact Or.inl hm
      · refine Or.inr fun I hI => ?_
        rcases hLsub I hI hh with h' | h'
        · exact absurd h' hm
        · exact h'
    have hL : L = Θ.Lmax ∪ Θ.core := by
      apply Set.Subset.antisymm hcore
      refine Set.union_subset hLive fun h hh => hIsL (hh Is hIs)
    exact ⟨hL, Is, hIs, hIsL.trans hcore⟩
  · rintro ⟨rfl, Is, hIs, hIsL⟩
    refine ⟨Set.subset_union_left, fun hex => hex ⟨Is, hIs, hIsL⟩, ?_⟩
    intro L' hL' hNE
    obtain ⟨I, hI, hIL'⟩ := not_not.1 hNE
    exact Set.union_subset hL' fun h hh => hIL' (hh I hI)

/-- A strongest liveness property not excluding `S` exists iff some implementation ensuring `S`
has all its fair histories in `Lmax ∪ core`. -/
theorem exists_isStrongestNonExcl_iff :
    (∃ L, Θ.IsStrongestNonExcl L) ↔ ∃ I, Θ.ensS I ∧ Θ.fair I ⊆ Θ.Lmax ∪ Θ.core := by
  constructor
  · rintro ⟨L, hL⟩
    exact ((Θ.isStrongestNonExcl_iff L).1 hL).2
  · intro h
    exact ⟨_, (Θ.isStrongestNonExcl_iff _).2 ⟨rfl, h⟩⟩

/-- Theorem 4.9 reduced to the model: if every history that is fair for all implementations
ensuring `S` lies in `Lmax`, any strongest liveness property not excluding `S` is `Lmax`. -/
theorem eq_Lmax_of_core_subset (hcore : Θ.core ⊆ Θ.Lmax) {L : Set H}
    (hL : Θ.IsStrongestNonExcl L) : L = Θ.Lmax := by
  rw [((Θ.isStrongestNonExcl_iff L).1 hL).1, Set.union_eq_left.2 hcore]

/-- Conversely, if a strongest non-excluding liveness property exists, Theorem 4.9's conclusion
holds iff `core ⊆ Lmax`. -/
theorem core_subset_of_eq_Lmax {L : Set H} (hL : Θ.IsStrongestNonExcl L) (hLL : L = Θ.Lmax) :
    Θ.core ⊆ Θ.Lmax := by
  have := ((Θ.isStrongestNonExcl_iff L).1 hL).1
  rw [hLL] at this
  intro h hh
  rw [this]
  exact Or.inr hh

/-- **Corollaries 4.10 and 4.11** (scheme). If Theorem 4.9's conclusion holds and `Lmax`
excludes `S`, there is no strongest liveness property that does not exclude `S`. -/
theorem no_strongest_of_excludes_Lmax
    (h49 : ∀ L, Θ.IsStrongestNonExcl L → L = Θ.Lmax) (hmax : Θ.Excludes Θ.Lmax) :
    ¬ ∃ L, Θ.IsStrongestNonExcl L := by
  rintro ⟨L, hL⟩
  have := hL.2.1
  rw [h49 L hL] at this
  exact this hmax

end Setting

end Podc.SafetyLivenessExclusion
