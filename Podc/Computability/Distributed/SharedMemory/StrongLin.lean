import Cslib.Computability.Distributed.SharedMemory.StrongLin

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/StrongLin.lean (append; the
-- `linOfPts` section could also go to `LinPoints.lean`)

/-!
# Linearization functions from linearization points

Many linearizability proofs assign to every step of an execution the (possibly empty) list of
operations whose linearization point is that step; the linearization of an execution is the
concatenation of these lists (`linOfPts`). Such a linearization function only grows along an
execution, so real-time order is automatic and the function is even a *strong* linearization
function (`Impl.isStrongLinFun_of_prefix`).

* `linOfPts pt`: the linearization function with per-step contributions `pt α ℓ` (the operations
  linearized by the step `ℓ` taken after `α`); `linOfPts_concat`, `linOfPts_prefix`.
* `Impl.isStrongLinFun_of_prefix`: a prefix-monotone function that, on every valid execution,
  lists distinct invoked operations with their operations, contains all completed operations and
  gives the actual responses (`SeqOK`) is a strong linearization function (in particular a
  linearization function).
-/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {P : Type}

/-! ### Linearizations from per-step contributions -/

section LinOfPts

variable (pt : List (Label P A) → Label P A → List (OpId P × A.Op))

/-- Auxiliary for `linOfPts`: the linearization of the reversed execution. -/
def linOfPtsRev : List (Label P A) → List (OpId P × A.Op)
  | [] => []
  | ℓ :: β => linOfPtsRev β ++ pt β.reverse ℓ

/-- The linearization obtained from linearization points: `pt α ℓ` is the list of operations
linearized by the step `ℓ` taken after `α`; the linearization of `α` is the concatenation of
the contributions of its steps, in order. -/
def linOfPts (α : List (Label P A)) : List (OpId P × A.Op) := linOfPtsRev pt α.reverse

@[simp] lemma linOfPts_nil : linOfPts pt [] = [] := rfl

@[simp] lemma linOfPts_concat (α : List (Label P A)) (ℓ : Label P A) :
    linOfPts pt (α ++ [ℓ]) = linOfPts pt α ++ pt α ℓ := by
  simp [linOfPts, linOfPtsRev]

/-- A linearization built from linearization points only grows along an execution. -/
lemma linOfPts_prefix {α β : List (Label P A)} (h : α <+: β) :
    linOfPts pt α <+: linOfPts pt β := by
  obtain ⟨γ, rfl⟩ := h
  induction γ using List.reverseRecOn with
  | nil => simp
  | append_singleton γ ℓ ih =>
    rw [← List.append_assoc, linOfPts_concat]
    exact ih.trans (List.prefix_append _ _)

end LinOfPts

/-! ### Growing linearization functions are strong linearization functions -/

namespace Impl

variable {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq P] [DecidableEq ι]
  {I : Impl A B P L}

/-- **Linearization functions that only grow.** If `h` is prefix-monotone on valid executions
and, on every valid execution `α`, `h α` lists distinct operation instances of `α` with their
operations, contains every completed instance, and assigns the actual responses (`SeqOK`), then
real-time order holds automatically and `h` is a strong linearization function. -/
theorem isStrongLinFun_of_prefix {h : List (Label P A) → List (OpId P × A.Op)}
    (hmono : ∀ α β, I.Valid β → α <+: β → h α <+: h β)
    (hnodup : ∀ α, I.Valid α → ((h α).map Prod.fst).Nodup)
    (hop : ∀ α, I.Valid α → ∀ y ∈ h α, opOf α y.1 = some y.2)
    (hcomp : ∀ α, I.Valid α → ∀ a, Completed α a → a ∈ (h α).map Prod.fst)
    (hseq : ∀ α, I.Valid α → SeqOK α A.init (h α)) : I.IsStrongLinFun h := by
  refine ⟨fun α hα => ⟨hnodup α hα, hop α hα, hcomp α hα, ?_, hseq α hα⟩, hmono⟩
  rintro a b ⟨β, γ, rfl, ha, hb⟩ hbL
  have hβ : I.Valid β := hα.of_append
  obtain ⟨M, hM⟩ := hmono β (β ++ γ) hα (List.prefix_append β γ)
  rw [← hM] at hbL ⊢
  have haβ := hcomp β hβ a ha
  have hbβ : b ∉ (h β).map Prod.fst := fun hm => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hm
    exact hb (Invoked.of_opOf_eq_some (hop β hβ y hy))
  simp only [List.map_append, List.mem_append] at hbL ⊢
  rcases hbL with hbL | hbL
  · exact absurd hbL hbβ
  · exact (List.Sublist.append (List.singleton_sublist.2 haβ) (List.singleton_sublist.2 hbL) :
      List.Sublist ([a] ++ [b]) _)

end Impl

end Cslib.SharedMemory
