import Papers.PODC2016.AnalysingSI.Relations

/-!
# Walks and cycles in edge-labelled graphs: definitions

An edge-labelled multigraph on `α` is a family of relations `E : L → α → α → Prop`.
See `Cycles.lean` for the theory.
-/

-- CSLib candidate: generic relation/walk lemmas (Cslib/Foundations/Data/Relation or Combinatorics)
namespace Podc.AnalysingSI

variable {α L : Type*}

/-- `Walk E a w b`: `w = [(l₁, v₁), …, (lₖ, vₖ)]` is a walk `a —l₁→ v₁ —l₂→ ⋯ —lₖ→ vₖ = b`. -/
inductive Walk (E : L → α → α → Prop) : α → List (L × α) → α → Prop
  | nil (a : α) : Walk E a [] a
  | cons {a b c : α} {l : L} {w : List (L × α)} :
      E l a b → Walk E b w c → Walk E a ((l, b) :: w) c

/-- A cycle: a nonempty closed walk. -/
def IsCycle (E : L → α → α → Prop) (w : List (L × α)) : Prop :=
  w ≠ [] ∧ ∃ a, Walk E a w a

/-- A cycle is simple if it does not contain two occurrences of the same vertex. -/
def IsSimple (w : List (L × α)) : Prop := (w.map Prod.snd).Nodup

/-- The labels of a walk, in order. -/
def labels (w : List (L × α)) : List L := w.map Prod.fst

/-- Some two cyclically consecutive elements `a, b` of the cyclic sequence `ls` (including the
pair formed by the last and the first element, when `ls` has at least two elements) satisfy
`P a b`. -/
def CycAdj (P : L → L → Prop) (ls : List L) : Prop :=
  (∃ pre a b suf, ls = pre ++ a :: b :: suf ∧ P a b) ∨
    (∃ a mid b, ls = a :: (mid ++ [b]) ∧ P b a)


end Podc.AnalysingSI
