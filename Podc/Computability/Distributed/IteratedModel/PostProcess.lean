import Cslib.Computability.Distributed.IteratedModel.Basic

-- CSLib candidate: Cslib/Computability/Distributed/IteratedModel/PostProcess.lean

/-!
# Reductions by local post-processing of the outputs

The simplest reduction between tasks: run an algorithm for a task `T` and let every process apply
a fixed function `g` to its decision. If `g` maps every legal output vector of `T` to a legal output
vector of `T'` (on inputs of `T'`, which must be inputs of `T`), the result solves `T'`, in every
model and for every number of rounds. The map `g` is the same for all processes, so the
post-processing preserves index-independence (`Alg.IndexIndependent`).

## Main definitions and statements
* `Alg.mapDec alg g` — decide `g (dec)` instead of `dec`;
* `Alg.IndexIndependent` — all processes use the same box-input and decision functions;
* `Solves.mapDec`, `Solvable.mapDec` — solvability is transported along post-processing maps;
* `Solvable.mapDec_contra` — the contrapositive, for transferring impossibility.
-/

namespace Cslib.Iterated

variable {P X A B Y Z : Type} {t : ℕ}

/-- Post-process the decisions of an algorithm with a function `g`. -/
def Alg.mapDec (alg : Alg P X A B Y t) (g : Y → Z) : Alg P X A B Z t where
  inp := alg.inp
  dec i v := g (alg.dec i v)

/-- An algorithm is index-independent if all processes run the same code (the box-input and
decision functions do not depend on the process index).

For `0` rounds (the view is the input) this is exactly index-independence in the sense of
Imbs–Rajsbaum–Raynal (runs are invariant under permuting the indices). For `t ≥ 1` it is weaker:
full-information views are indexed by `P`, so uniform code may still use the indices of the
processes it has seen. -/
def Alg.IndexIndependent (alg : Alg P X A B Y t) : Prop :=
  (∀ r i j, alg.inp r i = alg.inp r j) ∧ ∀ i j, alg.dec i = alg.dec j

lemma Alg.IndexIndependent.mapDec {alg : Alg P X A B Y t} (h : alg.IndexIndependent)
    (g : Y → Z) : (alg.mapDec g).IndexIndependent :=
  ⟨h.1, fun i j => by simp only [Alg.mapDec, h.2 i j]⟩

variable [DecidableEq P] {M : Model P A B}

/-- Post-processing reduction: if `alg` solves `T` and `g` maps legal outputs of `T` to legal
outputs of `T'`, then `alg.mapDec g` solves `T'`. -/
theorem Solves.mapDec {T : Task P X Y} {T' : Task P X Z} {alg : Alg P X A B Y t}
    (h : Solves M T alg) (g : Y → Z) (hInp : T'.Inp ⊆ T.Inp)
    (hΔ : ∀ I x, (I, x) ∈ T'.Inp → ∀ y ∈ T.Δ I x, g ∘ y ∈ T'.Δ I x) :
    Solves M T' (alg.mapDec g) := by
  intro I x hI V hV
  obtain ⟨y, hy, hdec⟩ := h I x (hInp hI) V hV
  exact ⟨g ∘ y, hΔ I x hI y hy, fun i hi => by simp [Alg.mapDec, hdec i hi]⟩

/-- Post-processing reduction for solvability. -/
theorem Solvable.mapDec {T : Task P X Y} {T' : Task P X Z} (h : Solvable M T t) (g : Y → Z)
    (hInp : T'.Inp ⊆ T.Inp) (hΔ : ∀ I x, (I, x) ∈ T'.Inp → ∀ y ∈ T.Δ I x, g ∘ y ∈ T'.Δ I x) :
    Solvable M T' t :=
  let ⟨alg, halg⟩ := h; ⟨alg.mapDec g, halg.mapDec g hInp hΔ⟩

/-- Impossibility transfers backwards along post-processing reductions. -/
theorem Solvable.mapDec_contra {T : Task P X Y} {T' : Task P X Z} (h : ¬ Solvable M T' t)
    (g : Y → Z) (hInp : T'.Inp ⊆ T.Inp)
    (hΔ : ∀ I x, (I, x) ∈ T'.Inp → ∀ y ∈ T.Δ I x, g ∘ y ∈ T'.Δ I x) : ¬ Solvable M T t :=
  fun hT => h (hT.mapDec g hInp hΔ)

end Cslib.Iterated
