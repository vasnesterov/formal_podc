import Mathlib

/-!
# The arithmetic of the proof of Lemma 38

The proof of Lemma 38 bounds the range after `r = 2⌈log t⌉ + 5` approximation rounds by
`(1/2)^(2⌈log t⌉+5) · 2t (1 + 1/(n+t))` and claims this is `< 1/(6(n+t))`. The left side does not
depend on `n` (it uses only the contraction factor `≥ 2`), the right side tends to `0`; the claimed
inequality fails e.g. for `t = 1`, `n = 100`.
-/

namespace Podc.OrderPreservingByzRenaming

/-- The inequality in the proof of Lemma 38 is false for `t = 1` (`⌈log t⌉ = 0`), `n = 100`. -/
theorem lemma_38_step_false :
    ¬ ((1 / 2 : ℚ) ^ (2 * 0 + 5) * (2 * 1 * (1 + 1 / (100 + 1))) < 1 / (6 * (100 + 1))) := by
  norm_num

end Podc.OrderPreservingByzRenaming

namespace Podc.OrderPreservingByzRenaming

/-- The last inequality of the proof of Lemma 41 (`1/(3t³) < (δ - 1)/2 = 1/(6(n+t))`) is false,
e.g. for `t = 2`, `n = 9 > t² + 2t`. -/
theorem lemma_41_step_false : ¬ ((1 : ℚ) / (3 * 2 ^ 3) < 1 / (6 * (9 + 2))) := by
  norm_num

end Podc.OrderPreservingByzRenaming
