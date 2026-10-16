import Papers.PODC2021.StabilizingLEDynamic.Model

/-!
# The identifier domain must be larger than the system

All impossibility proofs of Section 3 replace a process by a *fresh* one (`v ∉ V`), i.e. they use
that `IDSET` has more than `n` elements, so that fake identifiers exist. The paper only says
"`IDSET` is an arbitrary totally ordered domain". If `|IDSET| = n`, every system of `n` processes
is the whole of `IDSET`, and the constant algorithm "`lid := min IDSET`" is self-stabilizing for
*every* class of dynamic graphs, so all impossibility results (Theorems 2–5, Corollaries 1–3)
fail. Here: `IDSET = Fin 2`, `n = 2`.
-/

namespace StabilizingLEDynamic

/-- Every process always elects `0`. -/
def constAlg : Algorithm (Fin 2) Unit := ⟨fun _ _ => (), fun _ _ => 0⟩

/-- With only two identifiers and two processes, leader election is trivially self-stabilizing
(and pseudo-stabilizing within `0` rounds) in every class, e.g. in `J^B_{*,1}(Δ)` or `J_{1,*}`. -/
theorem constAlg_selfStab (C : DGClass (Fin 2)) : SelfStab constAlg C 2 ∧
    PseudoStabWithin constAlg C 2 0 := by
  have hspec : ∀ V : Finset (Fin 2), V.card = 2 → ∀ e, SPLE constAlg V e := by
    intro V hV e
    have : V = Finset.univ := Finset.eq_univ_of_card V (by simpa using hV)
    exact ⟨0, this ▸ Finset.mem_univ _, fun _ _ _ => rfl⟩
  exact ⟨fun V hV => ⟨Set.univ, fun _ _ _ => ⟨0, trivial⟩, fun _ _ _ _ => hspec V hV _⟩,
    fun V hV _ _ _ => hspec V hV _⟩

end StabilizingLEDynamic
