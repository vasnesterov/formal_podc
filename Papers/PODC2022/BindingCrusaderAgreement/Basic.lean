import Mathlib

/-!
# Graded outputs

Abraham, Ben-David, Yandamuri, PODC 2022, Definition 3.2: a Graded Binding Crusader Agreement
decides one of five ordered buckets `0 grade 2, 0 grade 1, ⊥ grade 0, 1 grade 1, 1 grade 2`.
-/

namespace Podc.BindingCrusaderAgreement

/-- The five buckets of Definition 3.2. -/
inductive Grade
  | two (v : Bool)
  | one (v : Bool)
  | zero
  deriving DecidableEq, Fintype

/-- `g` is `v` with grade `1` or `2`. -/
def Grade.HasVal (g : Grade) (v : Bool) : Prop := g = .two v ∨ g = .one v

end Podc.BindingCrusaderAgreement
