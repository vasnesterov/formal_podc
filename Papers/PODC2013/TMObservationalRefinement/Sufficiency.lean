import Papers.PODC2013.TMObservationalRefinement.Program

/-!
# Sufficiency of the opacity relation (Section 6)

* `lemma_20`: `∼` preserves membership in `[[P]](s)`.
* `theorem_21`: `H_C ⊑ H_A ⟹ H_C ⊑_trace H_A` (for a concrete system with repaired-well-formed
  histories; nothing is needed of `H_A`).
* `corollary_19`: `⊑_trace ⟹ ⊑_state`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.TMObservationalRefinement

open IKind Act Lang CmdClass

variable {T LV GV O M BE IE C : Type} [Lang T LV GV BE IE C] [DecidableEq T] [Fintype T]

/-- **Lemma 20.** If `τH ∈ [[P]](s)` and `τH ∼ τS` (both well-formed), then `τS ∈ [[P]](s)`. -/
theorem lemma_20 {P : Prog T LV O M C BE IE} {s : State T LV GV} {τH τS : List (Act T O M C)}
    (hH : τH ∈ den P s) (hwH : WFTrace τH) (hwS : WFTrace τS) (h : ObsEq τH τS) :
    τS ∈ den P s := by
  obtain ⟨⟨τ', ⟨r, rfl⟩, htr⟩, hne⟩ := hH
  refine ⟨⟨τS ++ r, ⟨r, rfl⟩, fun t => ?_⟩, ?_⟩
  · rw [tproj_append, ← h.1 t, ← tproj_append]; exact htr t
  · rwa [← lemma_18 hwH hwS h]

/-- **Theorem 21.** The opacity relation implies observational refinement with respect to traces.
-/
theorem theorem_21 {HC HA : Set (List (IAct T O M))} (hC : ∀ h ∈ HC, WellFormed h)
    (hop : OpacRel HC HA) : TraceRef (LV := LV) (GV := GV) (C := C) (BE := BE) (IE := IE) O M HC HA := by
  intro P hP s τH hτ
  obtain ⟨hden, hHC⟩ := hτ
  have hw : WFTrace τH := wfTrace_of_inA hP hden.1 (hC _ hHC)
  obtain ⟨S, hS, hHS⟩ := hop _ hHC
  obtain ⟨τS, hwS, hhS, hobs⟩ := rearrangement hHS hw rfl
  exact ⟨τS, ⟨lemma_20 hden hw hwS hobs, by rw [hhS]; exact hS⟩, hobs⟩

/-- **Corollary 19.** Observational refinement with respect to traces implies observational
refinement with respect to states. -/
theorem corollary_19 {HC HA : Set (List (IAct T O M))} (hC : ∀ h ∈ HC, WellFormed h)
    (hA : ∀ h ∈ HA, WellFormed h)
    (h : TraceRef (LV := LV) (GV := GV) (C := C) (BE := BE) (IE := IE) O M HC HA) :
    StateRef (LV := LV) (GV := GV) (C := C) (BE := BE) (IE := IE) O M HC HA := by
  intro P hP s τ hτ
  obtain ⟨τ', hτ', hobs⟩ := h P hP s τ hτ
  refine ⟨τ', hτ', lemma_18 ?_ ?_ hobs s⟩
  · exact wfTrace_of_inA hP hτ.1.1 (hC _ hτ.2)
  · exact wfTrace_of_inA hP hτ'.1.1 (hA _ hτ'.2)

/-- **Theorem 16**, first two implications. -/
theorem theorem_16_sufficiency {HC HA : Set (List (IAct T O M))} (hC : IsTS HC) (hA : IsTS HA)
    (hop : OpacRel HC HA) :
    TraceRef (LV := LV) (GV := GV) (C := C) (BE := BE) (IE := IE) O M HC HA ∧
      StateRef (LV := LV) (GV := GV) (C := C) (BE := BE) (IE := IE) O M HC HA :=
  ⟨theorem_21 hC.1 hop, corollary_19 hC.1 hA.1 (theorem_21 hC.1 hop)⟩

end Podc.TMObservationalRefinement
