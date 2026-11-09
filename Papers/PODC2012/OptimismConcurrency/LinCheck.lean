import Papers.PODC2012.OptimismConcurrency.ListSet
import Podc.Computability.Distributed.SharedMemory.LinPointCheck

/-!
# Herlihy–Wing linearizability from annotated linearization points

`linearizable_of_lpRun`: if the linearization-point checker `lpRun` of
`Podc/.../LinPointCheck.lean` accepts an annotated history whose erasure is the single-object
Herlihy–Wing history `H`, then `H` is linearizable (Herlihy–Wing, amended definition) w.r.t. the
deterministic object. Also `wellFormed_of_lpRun`: the checker only accepts well-formed histories.

-- CSLib candidate: `wellFormed_of_lpRun`, `hwLinearizable_of_lpRun` (generic in the object).
-/

namespace Podc.OptimismConcurrency

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] {A : ObjSpec} [DecidableEq A.Resp]

/-- Along an accepted run of the checker, the history stays well formed. -/
lemma LPInv.wellFormed_of_lpRun {l : List (LPLabel P A)} :
    ∀ {α : List (Label P A)} {s : A.State} {st : P → LPStatus A} {L : List (OpId P × A.Op)}
      {c' : A.State × (P → LPStatus A)}, LPInv α s st L → WellFormed α →
      lpRun (s, st) l = some c' → WellFormed (α ++ l.filterMap LPLabel.erase) := by
  induction l with
  | nil => intro α s st L c' _ hwf _; simpa using hwf
  | cons ℓ l ih =>
    intro α s st L c' h hwf hrun
    rw [lpRun_cons] at hrun
    cases hstep : lpStep (s, st) ℓ with
    | none => rw [hstep] at hrun; simp at hrun
    | some c₁ =>
      rw [hstep, Option.bind_some] at hrun
      obtain ⟨L₁, h₁⟩ := h.step hstep
      have hwf₁ : WellFormed (α ++ (ℓ.erase).toList) := by
        cases ℓ with
        | inv p o =>
          simp only [lpStep] at hstep
          split at hstep <;> try simp at hstep
          rename_i hp
          have hsp := h.status p; rw [hp] at hsp
          exact hwf.append_inv hsp
        | ret p r =>
          simp only [lpStep] at hstep
          split at hstep <;> try simp at hstep
          rename_i r' hp
          have hsp := h.status p; rw [hp] at hsp
          exact hwf.append_ret hsp.1
        | lin p => simpa [LPLabel.erase] using hwf
      have := ih h₁ hwf₁ hrun
      cases he : ℓ.erase <;> simp_all [List.filterMap_cons]

/-- The checker only accepts well-formed histories. -/
theorem wellFormed_of_lpRun {l : List (LPLabel P A)} {c' : A.State × (P → LPStatus A)}
    (h : lpRun (A.init, fun _ => .idle) l = some c') :
    WellFormed (l.filterMap LPLabel.erase) := by
  simpa using LPInv.wellFormed_of_lpRun lpInv_nil (fun β ℓ γ he => by simp at he) h

omit [DecidableEq A.Resp] in
/-- Erasures of annotated histories contain no internal steps, so `ofHist ∘ toHist` is the
identity on them. -/
lemma ofHist_toHist_erase (l : List (LPLabel P A)) :
    HerlihyWing.ofHist (HerlihyWing.toHist (l.filterMap LPLabel.erase)) = l.filterMap LPLabel.erase := by
  induction l with
  | nil => rfl
  | cons ℓ l ih =>
    cases ℓ with
    | inv p o => simpa [LPLabel.erase, HerlihyWing.toHist, HerlihyWing.ofHist,
        HerlihyWing.labelEvents, HerlihyWing.eventLabel] using ih
    | ret p r => simpa [LPLabel.erase, HerlihyWing.toHist, HerlihyWing.ofHist,
        HerlihyWing.labelEvents, HerlihyWing.eventLabel] using ih
    | lin p => simp only [List.filterMap_cons, LPLabel.erase]; exact ih

/-- **Linearization points ⇒ Herlihy–Wing linearizability.** -/
theorem hwLinearizable_of_lpRun {l : List (LPLabel P A)} {c' : A.State × (P → LPStatus A)}
    (h : lpRun (A.init, fun _ => .idle) l = some c')
    {H : HerlihyWing.History P Unit A.Op A.Resp}
    (hH : l.filterMap LPLabel.erase = HerlihyWing.ofHist H) :
    HerlihyWing.Linearizable (HerlihyWing.specOf A) H := by
  have hwf := wellFormed_of_lpRun h
  rw [hH] at hwf
  have hwf' : HerlihyWing.WellFormed H := by
    have := (HerlihyWing.wellFormed_toHist_iff (HerlihyWing.ofHist H)).2 hwf
    simpa using this
  rw [HerlihyWing.linearizable_iff_cslib H hwf']
  rw [← hH]
  exact isLinearization_of_lpRun h (List.prefix_refl _)

end Podc.OptimismConcurrency

namespace Podc.OptimismConcurrency

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] {A : ObjSpec} [DecidableEq A.Resp]

/-- Variant of `hwLinearizable_of_lpRun` with a decidable hypothesis (`toHist` of the erasure). -/
theorem hwLinearizable_of_lpRun' {l : List (LPLabel P A)} {c' : A.State × (P → LPStatus A)}
    (h : lpRun (A.init, fun _ => .idle) l = some c')
    {H : HerlihyWing.History P Unit A.Op A.Resp}
    (hH : HerlihyWing.toHist (l.filterMap LPLabel.erase) = H) :
    HerlihyWing.Linearizable (HerlihyWing.specOf A) H :=
  hwLinearizable_of_lpRun h (by rw [← hH, ofHist_toHist_erase])

end Podc.OptimismConcurrency
