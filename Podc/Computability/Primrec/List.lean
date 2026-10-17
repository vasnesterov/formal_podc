import Mathlib.Computability.Primrec.List

-- CSLib candidate: Cslib/Computability/Primrec/List.lean (Mathlib candidate)

/-!
# More primitive recursive functions

* `Primrec.list_all`, `Primrec.list_any`: `List.all` / `List.any` with a primitive recursive
  predicate;
* `Primrec.nat_pow`: exponentiation of natural numbers (from `Nat.Primrec.pow`).
-/

namespace Primrec

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- `List.all` with a primitive recursive predicate is primitive recursive. -/
theorem list_all {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).all (p a) :=
  (Primrec.list_foldr hf (Primrec.const true)
    (Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun a => by
    induction f a <;> simp [*]

/-- `List.any` with a primitive recursive predicate is primitive recursive. -/
theorem list_any {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).any (p a) :=
  (Primrec.list_foldr hf (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun a => by
    induction f a <;> simp [*]

/-- Exponentiation of natural numbers is primitive recursive. -/
theorem nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

end Primrec
