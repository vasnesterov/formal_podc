import Papers.PODC2014.DistributedUniversality.Safety
import Papers.PODC2014.DistributedUniversality.WaitFree3
import Papers.PODC2014.DistributedUniversality.ContentionCex

/-!
# Main results

Summary theorems for the constructions of Raynal–Stainer–Taubenfeld (PODC 2014):

* `theorem_1`: Figure 1 is a non-blocking linearizable `(k, 1)`-universal construction;
* `theorem_2_safety_progress`: Figure 2 is a non-blocking linearizable `(k, 1)`-universal
  construction (its contention-awareness claim is refuted in `ContentionCex.lean`);
* `theorem_4a`: with `(k, ℓ)`-SC objects and helping (Section 4.3, Figure 2 + L1–L5), the
  construction is linearizable and `ℓ`-wait-free: at least `ℓ` objects on each of which every
  correct process completes infinitely many operations.
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ}

/-- **Theorem 1.** Figure 1 (`k`-SC objects, `ca = false`, no helping): linearizable (Lemma 4) and
non-blocking (Corollary 1): in every infinite execution some object has a process completing
infinitely many operations on it. -/
theorem theorem_1 (hk : 0 < k) (M : Mode) (hM1 : M.ℓ = 1) (hca : M.ca = false) :
    (∀ s : St n k, Reachable M s → ∀ m, ∃ H : List (Op n), H.Nodup ∧
      (∀ i c t, s.retAt i m c = some t → (i, c) ∈ H ∧ ∃ tl ti, s.lin m (i, c) = some tl ∧
        s.invAt i m c = some ti ∧ ti ≤ tl ∧ tl ≤ t) ∧
      (∀ (x y : ℕ) (o1 o2 : Op n) (t2 : ℕ), H[x]? = some o1 → H[y]? = some o2 → x < y →
        s.lin m o2 = some t2 → ∃ t1, s.lin m o1 = some t1 ∧ t1 ≤ t2) ∧
      (∀ i c h, s.retH i m c = some h → h <+: H ∧ (i, c) ∈ h)) ∧
    (∀ e : Exec M n k, ∃ x j, e.CompletesInf j x) := by
  have hM : M.Good := fun h => by simp [hca] at h
  refine ⟨fun s hs m => lemma_4 hM hs m, fun e => ?_⟩
  obtain ⟨T, hT, hx⟩ := corollary_1 (by omega) (by omega) hM e
  have hne : T.Nonempty := by rw [← Finset.card_pos]; rw [hM1] at hT; omega
  obtain ⟨x, hxT⟩ := hne
  obtain ⟨j, hj⟩ := hx x hxT
  exact ⟨x, j, hj⟩

/-- **Theorem 4(a)** (with Theorem 3): the construction of Section 4.3 (Figure 2, lines L1–L5,
`(k, ℓ)`-SC objects) is linearizable and `ℓ`-wait-free: in every infinite execution there are at
least `ℓ` objects on each of which every correct process completes infinitely many operations. -/
theorem theorem_4a (M : Mode) (hℓ : 1 ≤ M.ℓ) (hℓk : M.ℓ ≤ k) (hhelp : M.help = true)
    (hM : M.Good) (e : Exec M n k) :
    ∃ T : Finset (Fin k), M.ℓ ≤ T.card ∧ ∀ x ∈ T, ∀ j, e.Correct j → e.CompletesInf j x := by
  obtain ⟨T, hT, hx⟩ := lemma_6 hℓ hℓk hM e
  exact ⟨T, hT, fun x hxT j hj => theorem_3 hℓ hℓk hM hhelp e hj (hx x hxT)⟩

end Podc.DistributedUniversality
