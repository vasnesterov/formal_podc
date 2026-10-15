import Papers.PODC2019.AnonymousMutex.Alg2Holder
import Papers.PODC2019.AnonymousMutex.Alg2Endgame

/-!
# Theorem 4: Algorithm 2 is deadlock-free

Suppose that in a fair client-well-formed execution some process is pending at `t₀`, nobody is in
the critical section at `t₀`, and no operation completes afterwards (`Hyp e t₀`). Let `c*` be the
eventual maximum of the number of registers owned by a process (`exists_cstar`). If `c* = 0`,
eventually nobody owns anything and a pending process performs a successful compare&swap
(`zero_case`). Otherwise some process keeps its registers forever (`exists_holder`) and the
`endgame` contradicts `m ∈ M(n)`.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P] [Fintype P]

/-- **Theorem 4** (Aghazadeh et al., PODC 2019): Algorithm 2 is deadlock-free whenever
`1 ≤ m` and `m ∈ M(n)`, for all identifiers and all anonymity permutations. -/
theorem theorem_4 (ids : P → Id) (hid : Function.Injective ids) (π : P → Equiv.Perm (Fin m))
    (hm : 0 < m) (hM : m ∈ M (Fintype.card P)) : ((alg2 Id m).impl ids π).DeadlockFree := by
  intro e hwf hfair t₀ ⟨p₀, hp₀⟩ hnocs
  by_contra hno
  push Not at hno
  have H : Hyp e t₀ := ⟨hwf, hfair, hno, hnocs⟩
  obtain ⟨c, T, hT, hc, hcase⟩ := exists_cstar e t₀
  have hzero : c = 0 → False := fun h0 =>
    zero_case hid hm H hp₀ hT (fun t ht r => Finset.card_eq_zero.1 (by have := hc t ht r; omega))
  rcases hcase with h0 | hinf
  · exact hzero h0
  · obtain ⟨q, t, ht, hq, hown, y₀, hy₀⟩ :=
      exists_holder hid hm H hT (by by_contra h; exact hzero (by omega)) hc hinf
    exact endgame hid hm hM H ht hq hown hy₀

end AnonymousMutex.Alg2
