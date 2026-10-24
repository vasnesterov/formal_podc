import Papers.PODC2017.RegisterEmulationSpace.Theorems
import Papers.PODC2017.RegisterEmulationSpace.Algorithm2Layout

/-!
# Theorem 8 as stated is false; non-vacuity of the lower-bound hypotheses

Theorem 8 of the paper: "for any `f > 0`, there is no `f`-tolerant algorithm that emulates a WS-Safe
obstruction-free `k`-register with resource complexity adaptive to point contention", where adaptive
means: there is a function `M` with resource consumption `≤ M(PntCont(r))` in every finite run `r`.
For a fixed `k`, Algorithm 2 (Theorem 3) is such an algorithm with finitely many registers, so its
resource consumption is bounded by the constant function `M = N` (the number of its registers).
The repaired statement (`M` independent of `k`) is `Alg.theorem8`.

`theorem3` also shows that the hypotheses of the lower bounds (`ObstructionFree`, `SeqSafe`) are
satisfiable for every `f ≥ 1` and `n > 2f`.
-/

namespace Podc.RegisterEmulationSpace

open Finset

/-- **Theorem 8 fails as stated** (for a fixed number `k = |Wr|` of writers): Algorithm 2 is an
`f`-tolerant obstruction-free `k`-register emulation, safe in sequential runs (indeed WS-Regular and
wait-free, see `Alg2.theorem3_wsRegular`), whose number of registers in use (covered by pending
writes) is bounded in every run by the constant `N = kf + ⌈k/z⌉(f+1)`, whatever the point
contention. -/
theorem theorem8_false_as_stated {C S V : Type*} [DecidableEq C] [Fintype S] [DecidableEq S]
    (Wr : Finset C) {f : ℕ} (hf : 0 < f) (hn : 2 * f < Fintype.card S) (v₀ : V) :
    ∃ (N : ℕ) (δ : Fin N → S) (R : C → Finset (Fin N)),
      (Alg2.alg δ f R v₀).ObstructionFree δ f ↑Wr ∧ (Alg2.alg δ f R v₀).SeqSafe v₀ ↑Wr ∧
      ∀ E, #(Cov ((Alg2.alg δ f R v₀).run E)) ≤ N := by
  obtain ⟨N, δ, R, -, -, -, -, hOF, hS⟩ := Alg2.theorem3 Wr hf hn v₀
  exact ⟨N, δ, R, hOF, hS, fun E => (card_le_univ _).trans (by simp)⟩

end Podc.RegisterEmulationSpace
