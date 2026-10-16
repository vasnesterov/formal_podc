import Mathlib

/-! Parameters of the boosting construction (Theorem 1). -/

namespace SynchronousCounting

/-- `m = ⌈k/2⌉`. -/
abbrev half (k : ℕ) : ℕ := (k + 1) / 2

/-- `τ = 3(F + 2)`, the length of one phase-king run. -/
abbrev tau (F : ℕ) : ℕ := 3 * (F + 2)

/-- The extra stabilisation time of one boosting step: `3(F+2)(2m)^k`. -/
abbrev boostTime (k F : ℕ) : ℕ := 3 * (F + 2) * (2 * half k) ^ k

end SynchronousCounting
