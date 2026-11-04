import Papers.PODC2011.AtMostOnceEffectiveness.WaitFree
import Papers.PODC2011.AtMostOnceEffectiveness.Adversary
import Papers.PODC2011.AtMostOnceEffectiveness.UpperBound

/-!
# Theorem 4.4: the effectiveness of `KK_β`

* `theorem_4_4_do_ge`: every fair run with at most `m − 1` crashes performs at least
  `n − (β + m − 2)` jobs (Lemmas 4.2 and 4.3);
* `theorem_4_4_ge`: hence `E_{KK_β}(n, m, f) ≥ n − (β + m − 2)` for every `f ≤ m − 1`;
* `theorem_4_4`: for `f = m − 1` and `n ≥ β + m − 1`, `E_{KK_β}(n, m, m − 1) = n − (β + m − 2)`
  (the matching adversary is `exists_fair_run_do_le`);
* `kk_effectiveness_le`: Theorem 2.1 applied to `KK_β`, `E ≤ n − f`.
-/

namespace Podc.AtMostOnceEffectiveness

variable {m n β : ℕ}

/-- **Theorem 4.4, lower bound, per run**: for `β ≥ m`, every run of `KK_β` that is fair with
respect to a crash set of at most `m − 1` processes performs at least `n − (β + m − 2)` jobs. -/
theorem theorem_4_4_do_ge (hβm : m ≤ β) (r : (kk m n β).Run) (F : Finset (Fin m))
    (hF : F.card ≤ m - 1) (hfair : r.Fair F) (hm : 1 ≤ m) : n - (β + m - 2) ≤ r.Do n := by
  obtain ⟨K, hK⟩ := lemma_4_3 hβm r
  obtain ⟨p, hp⟩ : ∃ p, p ∉ F := by
    by_contra h; push Not at h
    have : F = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [this, Finset.card_univ, Fintype.card_fin] at hF; omega
  obtain ⟨k', hk', h⟩ := hfair p hp K
  have hh : (kk m n β).Halted (r.cfg K) p := by
    rcases h with h | h
    · rw [hK k' hk'] at h; exact absurd h (by simp)
    · rwa [r.cfg_eq_of_stutter hK k' hk'] at h
  obtain ⟨hI, hI2⟩ := inv_of_reachable (by omega) (r.reachable K)
  have := do_ge_of_halted hI hI2 hh
  rw [r.do_eq_of_stutter n hK]
  omega

/-- **Theorem 4.4, lower bound**: `E_{KK_β}(n, m, f) ≥ n − (β + m − 2)` for `β ≥ m` and
`f ≤ m − 1`. -/
theorem theorem_4_4_ge (hm : 1 ≤ m) (hβm : m ≤ β) {f : ℕ} (hf : f ≤ m - 1) :
    n - (β + m - 2) ≤ (kk m n β).effectiveness n f := by
  apply le_csInf
  · exact ⟨_, Alg.advFinal (kk m n β) n f (by omega), Alg.advRun (kk m n β) n f (by omega),
      Alg.advFinal_card_le _ _ _ _, Alg.advRun_fair _ _ _ _, rfl⟩
  · rintro d ⟨F, r, hF, hfair, rfl⟩
    exact theorem_4_4_do_ge hβm r F (hF.trans hf) hfair hm

/-- **Theorem 4.4** of [Kentros–Kiayias]: for `β ≥ m`, `f = m − 1` crashes and
`n ≥ β + m − 1`, algorithm `KK_β` has effectiveness exactly `n − (β + m − 2)`. For `β = m`
this is the abstract's `n − 2m + 2`. -/
theorem theorem_4_4 (hm : 1 ≤ m) (hβm : m ≤ β) (hn : β + m - 1 ≤ n) :
    (kk m n β).effectiveness n (m - 1) = n - (β + m - 2) := by
  apply le_antisymm _ (theorem_4_4_ge hm hβm le_rfl)
  obtain ⟨F, r, hF, hfair, hdo⟩ := exists_fair_run_do_le hm hβm hn
  have hmem : r.Do n ∈
      {d | ∃ (F : Finset (Fin m)) (r : (kk m n β).Run), F.card ≤ m - 1 ∧ r.Fair F ∧ r.Do n = d} :=
    ⟨F, r, hF.le, hfair, rfl⟩
  exact (Nat.sInf_le hmem).trans hdo

/-- The abstract's headline: `KK_m` has effectiveness `n − 2m + 2` (for `n ≥ 2m − 1`). -/
theorem kk_m_effectiveness (hm : 1 ≤ m) (hn : 2 * m - 1 ≤ n) :
    (kk m n m).effectiveness n (m - 1) = n - (2 * m - 2) := by
  rw [theorem_4_4 hm le_rfl (by omega)]; congr 1; omega

/-- Theorem 2.1 applied to `KK_β`: `E_{KK_β}(n, m, f) ≤ n − f`. -/
theorem kk_effectiveness_le (hβ : 1 ≤ β) (f : ℕ) : (kk m n β).effectiveness n f ≤ n - f :=
  effectiveness_le_sub _ n f (lemma_4_1 hβ)

end Podc.AtMostOnceEffectiveness
