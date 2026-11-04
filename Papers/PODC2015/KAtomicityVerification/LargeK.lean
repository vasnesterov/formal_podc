import Papers.PODC2015.KAtomicityVerification.Normalization
import Papers.PODC2015.KAtomicityVerification.Characterization

/-!
# k-AV for `k ≥ n_w` (Section 2) and line 3 of CGS

Section 2 of the paper: when `k` is at least the number of writes, the writes can be ordered
arbitrarily subject to `<_H`, and "it suffices to verify that each read returns the value assigned
by some write whose start time is less than the finish time of the read", i.e. Assumption 3.3.
We prove this for arbitrary histories (Assumption 3.2 built in, no Assumption 3.4), using the
normalization of Theorem 3.5 and Lemma 3.8.
-/

namespace Podc.KAtomicityVerification

variable {V R : Type*} [Fintype V] [DecidableEq V] [Fintype R]

namespace History

variable {H : History V R}

omit [Fintype V] [DecidableEq V] [Fintype R] in
/-- Every `k`-atomic history satisfies Assumption 3.3 (for any `k`). -/
lemma assumption33_of_kAtomic {k : ℕ} (h : H.KAtomic k) : H.Assumption33 := by
  obtain ⟨lt, hto, hext, hread⟩ := h
  intro r hr
  exact asymm (hread r).1 (hext _ _ hr)

omit [Fintype R] in
/-- The length of a topological ordering is the number of values. -/
lemma IsTopoOrder.length_eq {T : List V} (hT : H.IsTopoOrder T) : T.length = Fintype.card V := by
  rw [← List.toFinset_card_of_nodup hT.nodup]
  congr 1
  ext v; simp [hT.complete v]

/-- **Section 2 claim** of [Golab–Li–López-Ortiz–Nishimura]. If `k ≥ 1` is at least the number
`n_w = |V|` of writes, then `H` is `k`-atomic iff no read happens before its dictating write
(Assumption 3.3). -/
theorem kAtomic_iff_assumption33_of_card_le {k : ℕ} (hk0 : 0 < k) (hk : Fintype.card V ≤ k) :
    H.KAtomic k ↔ H.Assumption33 := by
  refine ⟨assumption33_of_kAtomic, fun h33 => ?_⟩
  rw [← normalize_kAtomic_iff, kAtomic_iff_exists_valueOrder (normalize_assumption34 h33) hk0]
  obtain ⟨T, hT⟩ := exists_topoOrder (H := H.normalize)
  refine ⟨T, hT.nodup, hT.complete, hT.topo, fun i j hi hj _ => ?_⟩
  have := hT.length_eq
  omega

/-- Line 3–4 of Algorithm 3 (CGS): under Assumption 3.4, a history with at most `k ≥ 1` written
values is `k`-atomic. -/
theorem kAtomic_of_card_le (hA : H.Assumption34) {k : ℕ} (hk0 : 0 < k)
    (hk : Fintype.card V ≤ k) : H.KAtomic k :=
  (kAtomic_iff_assumption33_of_card_le hk0 hk).2 (assumption33_of_assumption34 hA)

end History

end Podc.KAtomicityVerification
