import Papers.PODC2024.SSLeaderElectionDirected.Unison

/-!
# Concrete instances

* `twoCycle`: the 2-node network `0 ⇄ 1` (strongly connected, no self-loop), `α = 1 = MAD`.
* `twoCycle_paper_unison_fails`: the paper's `U(2)` is not self-stabilizing on it (Theorem 5 is
  false as stated).
* `twoCycle_fixed_unison`, `twoCycle_PEL`: non-vacuity of the positive results.
* `idset_card_needed`: Corollary 2 needs `|IDSET| > |V|`: with exactly `|V|` identifiers, leader
  election is trivially solvable on two isolated nodes (two source components).
-/

set_option linter.unusedSectionVars false

open Podc.AtomicState

namespace Papers.PODC2024.SSLeaderElectionDirected

/-- The 2-cycle `0 ⇄ 1`. -/
def twoCycle : Digraph (Fin 2) where
  Adj a b := a ≠ b

theorem twoCycle_anc (a b : Fin 2) : Anc twoCycle a b := by
  by_cases h : a = b
  · rw [h]
  · exact Anc.of_adj h

theorem twoCycle_madLe : MADLe twoCycle 1 := by
  intro q p _
  by_cases h : q = p
  · subst h; exact ReachIn.refl 1 q
  · exact Or.inr ⟨q, rfl, h⟩

theorem twoCycle_source : IsSourceComponent twoCycle Set.univ :=
  isSourceComponent_iff.mpr ⟨0, by ext x; simp [twoCycle_anc], fun x _ => twoCycle_anc 0 x⟩

theorem twoCycle_unique : ∀ S, IsSourceComponent twoCycle S → S = Set.univ := fun _ hS =>
  hS.eq_of_mem twoCycle_source (hS.nonempty.some_mem) (Set.mem_univ _)

/-- **Counterexample to Theorem 5** (as stated in the paper): on the 2-cycle with identifiers `0, 1`
(`α = 1`, period `K = 2`), the paper's algorithm `U(K)` is not self-stabilizing for the
synchronous unison. -/
theorem twoCycle_paper_unison_fails :
    ¬ SelfStab (IsSyncExec (U.next twoCycle 1 1 false (fun i : Fin 2 => (i : ℕ))))
      (SPSU U.clk) :=
  U.paper_unison_not_selfStab twoCycle_source twoCycle_unique twoCycle_madLe le_rfl
    (p₁ := 0) (p₂ := 1) (Set.mem_univ _) (Set.mem_univ _) (by decide)

/-- The dipath `0 → 1` (its source component is the single process `0`). -/
def dipath : Digraph (Fin 2) where
  Adj a b := a = 0 ∧ b = 1

theorem dipath_anc_iff (a b : Fin 2) : Anc dipath a b ↔ a = b ∨ (a = 0 ∧ b = 1) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hbc ih =>
      obtain ⟨hb, hc⟩ := hbc
      rcases ih with rfl | ⟨rfl, hb'⟩
      · exact Or.inr ⟨hb, hc⟩
      · exact absurd (hb'.symm.trans hb) (by decide)
  · rintro (rfl | ⟨rfl, rfl⟩)
    · rfl
    · exact Anc.of_adj ⟨rfl, rfl⟩

theorem dipath_madLe : MADLe dipath 1 := by
  intro q p h
  rcases (dipath_anc_iff q p).mp h with rfl | ⟨rfl, rfl⟩
  · exact ReachIn.refl 1 q
  · exact Or.inr ⟨0, rfl, rfl, rfl⟩

theorem dipath_source : IsSourceComponent dipath {0} :=
  isSourceComponent_iff.mpr ⟨0, by ext x; simp [dipath_anc_iff], fun x hx => by
    rcases (dipath_anc_iff x 0).mp hx with rfl | ⟨-, h⟩
    · rfl
    · exact absurd h (by decide)⟩

theorem dipath_unique : ∀ S, IsSourceComponent dipath S → S = {0} := fun S hS =>
  hS.eq_of_mem dipath_source
    (by
      obtain ⟨r, hr⟩ := hS.nonempty
      exact mem_of_anc_of_closed hS.closed ((dipath_anc_iff 0 r).mpr (by
        fin_cases r <;> simp)) hr)
    rfl

/-- **Counterexample to Theorem 5 on a network that is not strongly connected and whose source
component is a single process**: the dipath `0 → 1` with identifiers `0, 1` (`α = 1`, `K = 2`). -/
theorem dipath_paper_unison_fails :
    ¬ SelfStab (IsSyncExec (U.next dipath 1 1 false (fun i : Fin 2 => (i : ℕ))))
      (SPSU U.clk) :=
  U.paper_unison_not_selfStab_of_min dipath_source dipath_unique dipath_madLe le_rfl
    (ℓ := 0) rfl (fun q => Nat.zero_le _) (p₁ := 0) (p₂ := 1) (by decide)

/-- Non-vacuity: the corrected `U(K)` on the 2-cycle is self-stabilizing. -/
theorem twoCycle_fixed_unison :
    SelfStab (IsSyncExec (U.next twoCycle 1 1 true (fun i : Fin 2 => (i : ℕ)))) (SPSU U.clk) :=
  U.theorem5 twoCycle_source twoCycle_unique twoCycle_madLe
    (fun a b h => Fin.ext (by simpa using h))

/-- Non-vacuity: PEL on the same instance. -/
theorem twoCycle_PEL :
    SilentSelfStab (PEL.next twoCycle 1 false (fun i : Fin 2 => (i : ℕ)))
      (IsExec (PEL.next twoCycle 1 false (fun i : Fin 2 => (i : ℕ))))
      (PEL.LEPred (fun i : Fin 2 => (i : ℕ))) :=
  PEL.theorem3 twoCycle_madLe twoCycle_source twoCycle_unique

/-- Two isolated nodes: two source components. -/
def twoIsolated : Digraph (Fin 2) where
  Adj _ _ := False

/-- With exactly `|V|` identifiers (`IDSET = Fin 2`), a trivial algorithm ("everybody appoints
identifier `0`") is silent self-stabilizing for leader election on two isolated nodes, although
there are two source components. Hence the hypothesis `|IDSET| > |V|` of Corollary 2 cannot be
dropped. -/
theorem idset_card_needed :
    (∃ S₁ S₂, IsSourceComponent twoIsolated S₁ ∧ IsSourceComponent twoIsolated S₂ ∧ S₁ ≠ S₂) ∧
    ∃ A : LEAlg twoIsolated (Fin 2) Unit, ∀ ι, Function.Injective ι →
      SilentSelfStab (A.next ι) (IsExec (A.next ι)) (LEPredicate (A.out ι) ι) := by
  have hanc : ∀ a b : Fin 2, Anc twoIsolated a b ↔ a = b := by
    intro a b
    constructor
    · intro h
      induction h with
      | refl => rfl
      | tail _ h => exact absurd h id
    · rintro rfl; rfl
  refine ⟨⟨{0}, {1}, ?_, ?_, by simp⟩, ⟨⟨fun _ γ => γ, fun _ _ _ => 0, fun _ _ _ _ _ h =>
    (h _ (Or.inl rfl)).2, fun _ _ _ _ _ _ _ => rfl⟩, fun ι hι => ⟨fun e _ => ⟨0, fun _ => rfl⟩,
    fun γ _ => ?_⟩⟩⟩
  · exact isSourceComponent_iff.mpr ⟨0, by ext x; simp [hanc], fun x hx => by
      rw [(hanc x 0).mp hx]⟩
  · exact isSourceComponent_iff.mpr ⟨1, by ext x; simp [hanc], fun x hx => by
      rw [(hanc x 1).mp hx]⟩
  · obtain ⟨ℓ, hℓ⟩ := (Finite.injective_iff_surjective.mp hι) 0
    exact ⟨ℓ, fun _ => hℓ.symm⟩

end Papers.PODC2024.SSLeaderElectionDirected
