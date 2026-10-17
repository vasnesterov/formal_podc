import Papers.PODC2022.AsyncCycleColoring.Alg1Term

/-!
# Algorithm 1: termination bounds (Lemma 3.9, local extrema, Theorem 3.1)
-/

namespace AsyncCycle

variable {ι : Type*} [LinearOrder ι] {n : ℕ} [NeZero n]

omit [LinearOrder ι] [NeZero n] in
lemma sub_one_ne_of_proper {X : ZMod n → ι} (hX : ∀ p, X p ≠ X (p + 1)) (p : ZMod n) :
    X p ≠ X (p - 1) := by
  have := hX (p - 1); rw [sub_add_cancel] at this; exact this.symm

/-- For a process that is not a local minimum, `a_p` changes at most `ℓ = upDist X p` times. -/
theorem chg_a_le_upDist {X : ZMod n → ι} (hX : ∀ p, X p ≠ X (p + 1))
    (σ : ℕ → Finset (ZMod n)) (T : ℕ) :
    ∀ p, ¬ (X p < X (p - 1) ∧ X p < X (p + 1)) →
      chg (fun t => ((run (alg1 ι) (init1 X) σ t).loc p).a) T ≤ upDist X p := by
  intro p
  induction h : (Finset.univ.filter (fun u => X p < X u)).card using Nat.strong_induction_on
    generalizing p with
  | _ m ih =>
    intro hmin
    rw [upDist]
    split_ifs with h1 h2
    · -- the larger neighbour is `p + 1`
      have hlt := card_up_lt X h1.1
      have hq := ih _ (h ▸ hlt) (p + 1) rfl (by
        rw [add_sub_cancel_right]; exact fun h' => lt_asymm h1.1 h'.1)
      have := chg_a_step X σ (q := p + 1) (q' := p - 1) (Or.inr ⟨rfl, rfl⟩) h1.1 h1.2 T
      omega
    · have hlt := card_up_lt X h2.1
      have hq := ih _ (h ▸ hlt) (p - 1) rfl (by
        rw [sub_add_cancel]; exact fun h' => lt_asymm h2.1 h'.2)
      have := chg_a_step X σ (q := p - 1) (q' := p + 1) (Or.inl ⟨rfl, rfl⟩) h2.1 h2.2 T
      omega
    · -- local maximum
      have hp1 := hX p
      have hm1 := sub_one_ne_of_proper hX p
      have hmax1 : X (p - 1) < X p := by
        rcases lt_or_gt_of_ne hm1 with h' | h'
        · rcases lt_or_gt_of_ne hp1 with h'' | h''
          · exact absurd ⟨h', h''⟩ hmin
          · exact absurd ⟨h', h''⟩ h2
        · exact h'
      have hmax2 : X (p + 1) < X p := by
        rcases lt_or_gt_of_ne hp1 with h'' | h''
        · exact absurd ⟨h'', hmax1⟩ h1
        · exact h''
      rw [chg_eq_zero_of_const (fun t => a_of_max X σ hmax1 hmax2 t)]

omit [NeZero n] in
/-- The `b`-component in the run for `X` is the `a`-component in the run for the reversed
order. -/
lemma b_eq_dual_a (X : ZMod n → ι) (σ : ℕ → Finset (ZMod n)) (t : ℕ) (p : ZMod n) :
    ((run (alg1 ι) (init1 X) σ t).loc p).b =
      ((run (alg1 ιᵒᵈ) (init1 (fun q => OrderDual.toDual (X q))) σ t).loc p).a := by
  rw [run_alg1_dual]; rfl

/-- For a process that is not a local maximum, `b_p` changes at most `ℓ' = downDist X p`
times. -/
theorem chg_b_le_downDist {X : ZMod n → ι} (hX : ∀ p, X p ≠ X (p + 1))
    (σ : ℕ → Finset (ZMod n)) (T : ℕ) (p : ZMod n) (hmax : ¬ (X (p - 1) < X p ∧ X (p + 1) < X p)) :
    chg (fun t => ((run (alg1 ι) (init1 X) σ t).loc p).b) T ≤ downDist X p := by
  simp only [b_eq_dual_a]
  apply chg_a_le_upDist (X := fun q => OrderDual.toDual (X q))
  · intro q h; exact hX q (OrderDual.toDual.injective h)
  · simpa using hmax

/-- **Lemma 3.9**, our version: a non-extremal process `p` returns after at most `ℓ + ℓ' + 1`
activations, where `ℓ`, `ℓ'` are the monotone distances from `p` to the closest local maximum and
minimum. (The paper states `min {3ℓ, 3ℓ', ℓ + ℓ'} + 4`; the proof there obtains `ℓ + ℓ' + 1`
for the third term, which is what we prove; the terms `3ℓ + 4`, `3ℓ' + 4` are not formalized.) -/
theorem lemma_3_9 {X : ZMod n → ι} (hX : ∀ p, X p ≠ X (p + 1)) (σ : ℕ → Finset (ZMod n))
    (p : ZMod n) (hp : ¬ (X p < X (p - 1) ∧ X p < X (p + 1)))
    (hp' : ¬ (X (p - 1) < X p ∧ X (p + 1) < X p)) (T : ℕ) :
    workActs (alg1 ι) (init1 X) σ p T ≤ upDist X p + downDist X p + 1 := by
  have h1 := workActs_le_fails (alg1 ι) (init1 X) σ p T
  have h2 := fails_le_chg X σ hX p T
  have h3 := chg_a_le_upDist hX σ T p hp
  have h4 := chg_b_le_downDist hX σ T p hp'
  omega

lemma upDist_add_downDist_le (X : ZMod n → ι) (p : ZMod n) :
    upDist X p + downDist X p ≤ n - 1 := by
  classical
  have h1 := upDist_le_card X p
  have h2 := upDist_le_card (fun q => OrderDual.toDual (X q)) p
  unfold downDist
  have hdisj : Disjoint (Finset.univ.filter (fun u => X p < X u))
      (Finset.univ.filter (fun u => X u < X p)) := by
    rw [Finset.disjoint_filter]; intro u _ h h'; exact lt_asymm h h'
  have hsub : Finset.univ.filter (fun u => X p < X u) ∪ Finset.univ.filter (fun u => X u < X p) ⊆
      Finset.univ.erase p := by
    intro u hu
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    rintro rfl; rcases hu with h | h <;> exact lt_irrefl _ h
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card] at hc
  have e : (Finset.univ.filter (fun u => OrderDual.toDual (X p) < OrderDual.toDual (X u))) =
      Finset.univ.filter (fun u => X u < X p) := by
    ext u; simp
  rw [e] at h2
  omega

end AsyncCycle
