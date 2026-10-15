import Papers.PODC2025.ByzantineStableMatching.Lemma5
import Papers.PODC2025.ByzantineStableMatching.Lemma7
import Papers.PODC2025.ByzantineStableMatching.Lemma13
import Papers.PODC2025.ByzantineStableMatching.Symmetry

/-!
# Necessary conditions for bSM, and the `k = 1` counterexample

Lifts the sSM lower bounds (Lemmas 5, 7, 13, generalized to all `k ≥ 2`) to bSM via Lemma 2, and
derives the side-swapped variants. Also shows that for `k = 1` bSM is *always* solvable, which
contradicts the "only if" directions of Theorems 2, 3, 4, 6, 7 as literally stated (the paper never
assumes `k ≥ 2`).
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum

variable {k : ℕ}

lemma neZero_of_two_le (hk : 2 ≤ k) : NeZero k := ⟨by omega⟩

/-- Lemma 5 for bSM: `tL ≥ k/3 ∧ tR ≥ k/3` makes bSM unsolvable on any network (unauthenticated). -/
theorem bSM_not_solvable_third (G : SimpleGraph (Party k)) {tL tR : ℕ} (hk : 2 ≤ k)
    (hL : k ≤ 3 * tL) (hR : k ≤ 3 * tR) : ¬ Solvable G (thresholds k tL tR) (bSM k) := by
  have := neZero_of_two_le hk
  exact fun h => lemma5 G hk hL hR (lemma2 h)

/-- Lemma 7 for bSM: without edges inside `L`, `tR ≥ k/2` makes bSM unsolvable (unauthenticated). -/
theorem bSM_not_solvable_halfR (G : SimpleGraph (Party k)) (hG : ∀ i i', ¬ G.Adj (inl i) (inl i'))
    {tL tR : ℕ} (hk : 2 ≤ k) (hR : k ≤ 2 * tR) : ¬ Solvable G (thresholds k tL tR) (bSM k) := by
  have := neZero_of_two_le hk
  exact fun h => lemma7 G hG hk hR (lemma2 h)

/-- Mirror of Lemma 7: without edges inside `R`, `tL ≥ k/2` makes bSM unsolvable. -/
theorem bSM_not_solvable_halfL (G : SimpleGraph (Party k)) (hG : ∀ j j', ¬ G.Adj (inr j) (inr j'))
    {tL tR : ℕ} (hk : 2 ≤ k) (hL : k ≤ 2 * tL) : ¬ Solvable G (thresholds k tL tR) (bSM k) := by
  have := neZero_of_two_le hk
  intro h
  exact lemma7 (G.comap swapE) (fun i i' => hG i i') hk hL (sSM_solvable_swap (lemma2 h))

/-- Lemma 13 for bSM: without edges inside `L`, `tR = k` and `tL ≥ k/3` make bSM unsolvable even
with signatures. -/
theorem bSM_not_solvableAuth_R (G : SimpleGraph (Party k)) (hG : ∀ i i', ¬ G.Adj (inl i) (inl i'))
    {tL tR : ℕ} (hk : 2 ≤ k) (hL : k ≤ 3 * tL) (hR : k ≤ tR) :
    ¬ SolvableAuth G (thresholds k tL tR) (bSM k) := by
  have := neZero_of_two_le hk
  exact fun h => lemma13_sSM G hG hk hL hR (lemma2_auth h)

/-- Mirror of Lemma 13 (Corollary 5, the case `tL = k`): without edges inside `R`, `tL = k` and
`tR ≥ k/3` make bSM unsolvable even with signatures. -/
theorem bSM_not_solvableAuth_L (G : SimpleGraph (Party k)) (hG : ∀ j j', ¬ G.Adj (inr j) (inr j'))
    {tL tR : ℕ} (hk : 2 ≤ k) (hR : k ≤ 3 * tR) (hL : k ≤ tL) :
    ¬ SolvableAuth G (thresholds k tL tR) (bSM k) := by
  have := neZero_of_two_le hk
  intro h
  exact lemma13_sSM (G.comap swapE) (fun i i' => hG i i') hk hR hL
    (sSM_solvableAuth_swap (lemma2_auth h))

/-! ## `k = 1` -/

/-- The trivial protocol for `k = 1`: never send anything, immediately match with the only party
on the other side. -/
def trivialProtocol : Protocol (Party 1) (Equiv.Perm (Fin 1)) Unit (Option (Fin 1)) where
  send _ _ _ _ := none
  decide _ _ _ := some (some 0)

lemma trivial_decides {G : SimpleGraph (Party 1)} (s : Scenario (Party 1) (Equiv.Perm (Fin 1)) Unit)
    (p : Party 1) (o : Option (Fin 1)) : Decides G trivialProtocol s p o ↔ o = some 0 := by
  constructor
  · rintro ⟨r, hr, -⟩
    simp only [status, trivialProtocol, Option.some.injEq] at hr
    exact hr.symm
  · rintro rfl; exact ⟨0, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- **Counterexample (`k = 1`)**: with one party per side, bSM is solvable on every network and
against every adversary structure (in particular for `tL = tR = 1`), without any communication. -/
theorem bSM_solvable_k1 (G : SimpleGraph (Party 1)) (Z : AdvStructure (Party 1)) :
    Solvable G Z (bSM 1) := by
  refine ⟨Unit, trivialProtocol, fun s _ _ => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · intro p _; exact ⟨_, (trivial_decides s p _).mpr rfl⟩
  · intro i j _ _
    simp only [trivial_decides, Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
  · intro p q _ _ hpq z z' _ _ h
    rcases p with i | i <;> rcases q with j | j <;>
      simp_all [partner, Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
  · intro i j oi oj _ _ hoi _ hb
    rw [trivial_decides] at hoi
    subst hoi
    simp [Prefers, Fin.fin_one_eq_zero j] at hb

theorem bSM_solvableAuth_k1 (G : SimpleGraph (Party 1)) (Z : AdvStructure (Party 1)) :
    SolvableAuth G Z (bSM 1) := (bSM_solvable_k1 G Z).solvableAuth G

/-- The "only if" part of Theorem 2 fails for `k = 1`: `tL = tR = 1 ≥ k/3`, yet bSM is solvable
(even on the bipartite network, the weakest one). -/
theorem theorem2_only_if_false_k1 :
    ¬ (∀ k tL tR : ℕ, Solvable (fully k) (thresholds k tL tR) (bSM k) →
      3 * tL < k ∨ 3 * tR < k) := by
  intro h
  have := h 1 1 1 (bSM_solvable_k1 _ _)
  omega

end Papers.PODC2025.ByzantineStableMatching
