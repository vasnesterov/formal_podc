import Papers.PODC2012.OptimismConcurrency.Basic

/-!
# LS-linearizability is compositional (Theorem 5, Appendix B)

A history `H` on several objects `x : X` (for the paper: `X = {O₁, O₂}`) is LS-linearizable
w.r.t. the composed sequential implementation as soon as every `H|x` is LS-linearizable w.r.t.
the sequential implementation of `x`.

The composed implementation is represented by any set `SigIS` of sequential histories containing
the histories of every component (`∀ x, SigX x ⊆ SigIS`: running only operations of `O_x` is an
execution of `IS₁ × IS₂`). The composed type `τ₁ × τ₂` is represented, as usual for
linearizability, by the multi-object Herlihy–Wing specification (one sequential specification per
object). Well-formedness of the high-level history of `H` is assumed (all histories of the paper
are well-formed).

The local-serializability half is immediate, because every operation acts on one object, so
`H|π = (H|x)|π`; the linearizability half is the locality of linearizability (Herlihy–Wing,
`Cslib.SharedMemory.HerlihyWing.linearizable_of_restrictX`). The paper's proof reasons about
interleaving witnesses `S¹_π`, `S²_π` of both components and "any completion"; neither is needed.
-/

namespace Podc.OptimismConcurrency

open Cslib.SharedMemory

variable {P X Op Res Obj Val : Type} [DecidableEq P] [DecidableEq X]

/-- `H|x`: the events on object `x`. -/
def restrictObj (H : Hist P X Op Res Obj Val) (x : X) : Hist P X Op Res Obj Val :=
  H.filter (fun e => decide (e.obj = x))

lemma restrictPX_restrictObj (H : Hist P X Op Res Obj Val) (p : P) (x : X) :
    restrictPX (restrictObj H x) p x = restrictPX H p x := by
  unfold restrictPX restrictObj
  rw [List.filter_filter]
  congr 1; funext e
  by_cases h : e.obj = x <;> simp [h]

lemma termOf_restrictObj (p : P) (x : X) (l : Hist P X Op Res Obj Val) :
    termOf p x (restrictObj l x) = termOf p x l := by
  unfold termOf restrictObj
  induction l with
  | nil => rfl
  | cons e l ih =>
    by_cases he : e.obj = x
    · simp only [List.filter_cons, he, decide_true, if_true, List.find?_cons]
      split <;> simp_all
    · simp only [List.filter_cons, he, decide_false, Bool.false_eq_true, if_false,
        List.find?_cons]
      rw [ih]
      simp [he]

lemma lookFilter_keepHL_restrictObj (H : Hist P X Op Res Obj Val) (x : X) :
    lookFilter keepHL (restrictObj H x) = (lookFilter keepHL H).filter (fun e => decide (e.obj = x)) := by
  induction H with
  | nil => rfl
  | cons e l ih =>
    have hr : restrictObj (e :: l) x =
        if e.obj = x then e :: restrictObj l x else restrictObj l x := by
      unfold restrictObj; simp only [List.filter_cons, decide_eq_true_eq]
    by_cases he : e.obj = x
    · rw [hr, if_pos he]
      have hk : keepHL e (restrictObj l x) = keepHL e l := by
        cases e with
        | inv p y o =>
          simp only [Ev.obj_inv] at he; subst he
          simp only [keepHL, termOf_restrictObj]
        | _ => rfl
      simp only [lookFilter, hk, ih]
      split <;> simp [he]
    · rw [hr, if_neg he, ih]
      simp only [lookFilter]
      split <;> simp [he]

lemma filterMap_toHW_filter (L : Hist P X Op Res Obj Val) (x : X) :
    (L.filter (fun e => decide (e.obj = x))).filterMap toHW =
      HerlihyWing.restrictX (L.filterMap toHW) x := by
  unfold HerlihyWing.restrictX
  induction L with
  | nil => rfl
  | cons e l ih =>
    cases e with
    | inv p y o => by_cases h : y = x <;> simp_all [toHW, List.filter_cons, List.filterMap_cons]
    | res p y r => by_cases h : y = x <;> simp_all [toHW, List.filter_cons, List.filterMap_cons]
    | rinv p y z => by_cases h : y = x <;> simp_all [toHW, List.filter_cons, List.filterMap_cons]
    | rres p y v => by_cases h : y = x <;> simp_all [toHW, List.filter_cons, List.filterMap_cons]
    | winv p y z v => by_cases h : y = x <;> simp_all [toHW, List.filter_cons, List.filterMap_cons]
    | wres p y b => by_cases h : y = x <;> simp_all [toHW, List.filter_cons, List.filterMap_cons]

lemma hl_restrictObj (H : Hist P X Op Res Obj Val) (x : X) :
    hl (restrictObj H x) = HerlihyWing.restrictX (hl H) x := by
  unfold hl
  rw [lookFilter_keepHL_restrictObj, filterMap_toHW_filter]

/-- **Theorem 5** (LS-linearizability is compositional). If every `H|x` is LS-linearizable w.r.t.
the sequential implementation `SigX x` of `x` and the specification, then `H` is LS-linearizable
w.r.t. the composed sequential implementation `SigIS` (any set containing the histories of the
components) and the composed specification. -/
theorem theorem_5 {SigX : X → Set (Hist P X Op Res Obj Val)} {SigIS : Set (Hist P X Op Res Obj Val)}
    (hSig : ∀ x, SigX x ⊆ SigIS) {spec : HerlihyWing.SeqSpec P X Op Res}
    {H : Hist P X Op Res Obj Val} (hwf : HerlihyWing.WellFormed (hl H))
    (h : ∀ x, LSL (SigX x) spec (restrictObj H x)) : LSL SigIS spec H := by
  refine ⟨fun p x k hk => ?_, ?_⟩
  · have hk' : k < numOps (restrictObj H x) p x := by
      rwa [numOps, restrictPX_restrictObj]
    obtain ⟨S₀, hS⟩ := (h x).1 p x k hk'
    refine ⟨S₀, hSig x ?_⟩
    rwa [localView, restrictPX_restrictObj] at hS
  · refine HerlihyWing.linearizable_of_restrictX hwf fun x => ?_
    rw [← hl_restrictObj]
    exact (h x).2

end Podc.OptimismConcurrency
