import Papers.PODC2022.AsyncCycleColoring.Alg1Bound

/-!
# Algorithm 1: local extrema return within 4 activations; Theorem 3.1

The paper derives this from Lemma 3.4. Our proof for a local maximum `p`, for which `a_p ≡ 0`:
after `p`'s first round at time `t₁`, its register shows `a = 0`, so every smaller neighbour `u`
that fails a round at a time `≥ t₁` computes `a_u ≠ 0` forever after; hence once `u` has taken
two rounds from `t₁` on, its register shows `a_u ≠ 0` and `u` can no longer conflict with `p`.
A failed round of `p` after `t₁` needs a conflict with a neighbour whose register changed since
`p`'s previous round (Lemma 3.2). So each of the two neighbours causes at most one failure after
`t₁`: at most `1 + 2` failures and one return.
-/

namespace AsyncCycle

variable {ι : Type*} [LinearOrder ι] {n : ℕ}

section Max

variable {X : ZMod n → ι} (σ : ℕ → Finset (ZMod n)) {p : ZMod n}
  (hm1 : X (p - 1) < X p) (hm2 : X (p + 1) < X p)

local notation "R" => run (alg1 ι) (init1 X) σ

include hm1 hm2

/-- The register of a local maximum always shows `a = 0`. -/
lemma reg_a_of_max (t : ℕ) (x : St1 ι) (h : (R t).reg p = some x) : x.a = 0 := by
  induction t with
  | zero => simp at h
  | succ t ih =>
    rw [reg_succ] at h
    split_ifs at h
    · cases h; exact a_of_max X σ hm1 hm2 t
    · exact ih h

omit hm1 hm2 in
lemma nbr_cases {u : ZMod n} (hu : u = p - 1 ∨ u = p + 1) : p = u + 1 ∨ p = u - 1 := by
  rcases hu with rfl | rfl
  · left; simp
  · right; simp

/-- A smaller neighbour that fails a round after `p`'s register was written computes `a ≠ 0`. -/
lemma a_ne_zero_of_fail {u : ZMod n} (hu : u = p - 1 ∨ u = p + 1) {s : ℕ} {s' : St1 ι}
    (hs : resAt (alg1 ι) (init1 X) σ s u = Sum.inl s') (hp : (R (s + 1)).reg p ≠ none) :
    s'.a ≠ 0 := by
  obtain ⟨-, rfl⟩ := alg1_fail_eq X σ hs
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hp
  have hxX := alg1_reg_X X σ _ _ _ hx
  have hxa := reg_a_of_max σ hm1 hm2 _ _ hx
  have hmem : x ∈ awake ((R (s + 1)).reg (u - 1)) ((R (s + 1)).reg (u + 1)) := by
    rcases nbr_cases hu with h | h
    · rw [h] at hx; exact mem_awake_right hx
    · rw [h] at hx; exact mem_awake_left hx
  have hlt : X u < x.X := by
    rw [hxX]; rcases hu with rfl | rfl
    · exact hm1
    · exact hm2
  have := upA_ne hmem hlt
  rw [hxa] at this
  exact this

omit hm1 hm2 in
lemma reg_ne_none_after {t₁ t : ℕ} (h1 : ActsAt (alg1 ι) (init1 X) σ t₁ p) (ht : t₁ + 1 ≤ t) :
    (R t).reg p ≠ none := by
  refine reg_ne_none_mono _ _ _ ht ?_
  rw [reg_succ_of_acts _ _ _ h1]; simp

/-- Once a smaller neighbour has failed a round at a time `≥ t₁`, its `a` stays nonzero. -/
lemma a_ne_zero_after {u : ZMod n} (hu : u = p - 1 ∨ u = p + 1) {t₁ s : ℕ}
    (h1 : ActsAt (alg1 ι) (init1 X) σ t₁ p) (hs1 : t₁ ≤ s)
    (hs : FailsAt (alg1 ι) (init1 X) σ s u) : ∀ t, s + 1 ≤ t → ((R t).loc u).a ≠ 0 := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    obtain ⟨ha, s', hs'⟩ := hs
    rw [loc_succ_of_inl _ _ _ ha hs']
    exact a_ne_zero_of_fail σ hm1 hm2 hu hs' (reg_ne_none_after σ h1 (by omega))
  | succ t ht ih =>
    by_cases ha : ActsAt (alg1 ι) (init1 X) σ t u
    · rcases hr : resAt (alg1 ι) (init1 X) σ t u with s' | o
      · rw [loc_succ_of_inl _ _ _ ha hr]
        exact a_ne_zero_of_fail σ hm1 hm2 hu hr (reg_ne_none_after σ h1 (by omega))
      · rw [loc_succ_of_inr _ _ _ ha hr]; exact ih
    · rw [loc_succ_of_not_acts _ _ _ ha]; exact ih

/-- After two rounds from time `t₁` on, a smaller neighbour's register shows `a ≠ 0`. -/
lemma reg_a_ne_zero_after_two {u : ZMod n} (hu : u = p - 1 ∨ u = p + 1) {t₁ s₁ s₂ : ℕ}
    (h1 : ActsAt (alg1 ι) (init1 X) σ t₁ p) (hs1 : t₁ ≤ s₁) (h12 : s₁ < s₂)
    (ha1 : ActsAt (alg1 ι) (init1 X) σ s₁ u) (ha2 : ActsAt (alg1 ι) (init1 X) σ s₂ u) :
    ∀ t, s₂ + 1 ≤ t → ∀ x, (R t).reg u = some x → x.a ≠ 0 := by
  have hf := failsAt_of_actsAt_later _ _ _ ha1 h12 ha2
  have hloc := a_ne_zero_after σ hm1 hm2 hu h1 hs1 hf
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    intro x hx
    rw [reg_succ_of_acts _ _ _ ha2] at hx
    cases hx; exact hloc s₂ (by omega)
  | succ t ht ih =>
    intro x hx
    rw [reg_succ] at hx
    split_ifs at hx
    · cases hx; exact hloc t (by omega)
    · exact ih x hx

omit hm1 hm2 in
/-- A failed round of `p` comes from a neighbour whose register shows `p`'s colour. -/
lemma conflict_of_fails {t : ℕ} (h : FailsAt (alg1 ι) (init1 X) σ t p) :
    ∃ u, (u = p - 1 ∨ u = p + 1) ∧ ∃ x, (R (t + 1)).reg u = some x ∧
      x.col = ((R t).loc p).col := by
  obtain ⟨-, s, hs⟩ := h
  obtain ⟨hmem, -⟩ := alg1_fail_eq X σ hs
  obtain ⟨x, hx, hcol⟩ := List.mem_map.1 hmem
  rcases mem_awake.1 hx with h | h
  · exact ⟨p - 1, Or.inl rfl, x, h, hcol⟩
  · exact ⟨p + 1, Or.inr rfl, x, h, hcol⟩

omit hm1 hm2 in
/-- A conflict at `t` with `u` needs a round of `u` since `p`'s previous round `t₀`. -/
lemma fresh_of_conflict (hX : ∀ p, X p ≠ X (p + 1)) {u : ZMod n} (hu : u = p - 1 ∨ u = p + 1) {t₀ t : ℕ}
    (h0 : FailsAt (alg1 ι) (init1 X) σ t₀ p) (ht : t₀ < t)
    (hgap : ∀ s, t₀ < s → s < t → ¬ ActsAt (alg1 ι) (init1 X) σ s p) {x : St1 ι}
    (hx : (R (t + 1)).reg u = some x) (hcol : x.col = ((R t).loc p).col) :
    ∃ s, t₀ < s ∧ s ≤ t ∧ ActsAt (alg1 ι) (init1 X) σ s u := by
  by_contra hno
  push Not at hno
  obtain ⟨ha0, s', hs'⟩ := h0
  have hregu := (reg_loc_const (alg1 ι) (init1 X) σ (p := u) (a := t₀ + 1) (t + 1) (by omega)
    (fun s h1 h2 => hno s (by omega) (by omega))).1
  have hlocp := (reg_loc_const (alg1 ι) (init1 X) σ (p := p) (a := t₀ + 1) t (by omega)
    (fun s h1 h2 => hgap s (by omega) h2)).2
  rw [loc_succ_of_inl _ _ _ ha0 hs'] at hlocp
  rw [hregu] at hx
  have hmem : x ∈ awake ((R (t₀ + 1)).reg (p - 1)) ((R (t₀ + 1)).reg (p + 1)) := by
    rcases hu with rfl | rfl
    · exact mem_awake_left hx
    · exact mem_awake_right hx
  exact lemma_3_2 X σ hX hs' hmem (by rw [hcol, hlocp])

/-- The key step: a neighbour cannot cause two failures of `p` after `p`'s first round. -/
lemma no_two_conflicts (hX : ∀ p, X p ≠ X (p + 1)) {u : ZMod n} (hu : u = p - 1 ∨ u = p + 1) {t₁ t t' : ℕ}
    (h1 : ActsAt (alg1 ι) (init1 X) σ t₁ p) (h1t : t₁ < t) (htt' : t < t')
    (ht : FailsAt (alg1 ι) (init1 X) σ t p) (ht' : FailsAt (alg1 ι) (init1 X) σ t' p)
    {x : St1 ι} (hx : (R (t + 1)).reg u = some x) (hcol : x.col = ((R t).loc p).col)
    {x' : St1 ι} (hx' : (R (t' + 1)).reg u = some x') (hcol' : x'.col = ((R t').loc p).col) :
    False := by
  obtain ⟨t₀, h01, h02, h03, h04⟩ := exists_last_act (alg1 ι) (init1 X) σ h1 h1t
  have hf0 := failsAt_of_actsAt_later _ _ _ h03 h02 ht.1
  obtain ⟨s₀, hs01, hs02, hs03⟩ := fresh_of_conflict σ hX hu hf0 h02 h04 hx hcol
  obtain ⟨t₀', h01', h02', h03', h04'⟩ := exists_last_act (alg1 ι) (init1 X) σ ht.1 htt'
  have hf0' := failsAt_of_actsAt_later _ _ _ h03' h02' ht'.1
  obtain ⟨s', hs1', hs2', hs3'⟩ := fresh_of_conflict σ hX hu hf0' h02' h04' hx' hcol'
  have := reg_a_ne_zero_after_two σ hm1 hm2 hu h1 (by omega : t₁ ≤ s₀) (by omega : s₀ < s')
    hs03 hs3' (t' + 1) (by omega) x' hx'
  apply this
  have : x'.a = ((R t').loc p).a := congrArg Prod.fst hcol'
  rw [this, a_of_max X σ hm1 hm2]

omit hm1 hm2 in
lemma card_le_one_conflicts_aux {S : Finset ℕ} (h : ∀ t ∈ S, ∀ t' ∈ S, t < t' → False) :
    S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · exact h a ha b hb h'
  · exact h b hb a ha h'

/-- A local maximum returns after at most 4 activations. -/
theorem workActs_le_four_of_max (hX : ∀ p, X p ≠ X (p + 1)) (T : ℕ) : workActs (alg1 ι) (init1 X) σ p T ≤ 4 := by
  classical
  by_cases hA : ∃ t₁, ActsAt (alg1 ι) (init1 X) σ t₁ p
  swap
  · push Not at hA
    unfold workActs
    rw [Finset.filter_false_of_mem (fun t _ => hA t)]; simp
  -- the first activation
  let t₁ := Nat.find hA
  have h1 : ActsAt (alg1 ι) (init1 X) σ t₁ p := Nat.find_spec hA
  have hmin : ∀ t, ActsAt (alg1 ι) (init1 X) σ t p → t₁ ≤ t := fun t ht => Nat.find_min' hA ht
  let Conf : ZMod n → ℕ → Prop := fun u t => ∃ x, (R (t + 1)).reg u = some x ∧
      x.col = ((R t).loc p).col
  let F : ZMod n → Finset ℕ := fun u => (Finset.range T).filter
    (fun t => FailsAt (alg1 ι) (init1 X) σ t p ∧ t₁ < t ∧ Conf u t)
  have hF : ∀ u, (u = p - 1 ∨ u = p + 1) → (F u).card ≤ 1 := by
    intro u hu
    apply card_le_one_conflicts_aux
    intro t ht t' ht' htt'
    simp only [F, Finset.mem_filter] at ht ht'
    obtain ⟨x, hx, hc⟩ := ht.2.2.2
    obtain ⟨x', hx', hc'⟩ := ht'.2.2.2
    exact no_two_conflicts σ hm1 hm2 hX hu h1 ht.2.2.1 htt' ht.2.1 ht'.2.1 hx hc hx' hc'
  have hsub : (Finset.range T).filter (fun t => FailsAt (alg1 ι) (init1 X) σ t p) ⊆
      {t₁} ∪ (F (p - 1) ∪ F (p + 1)) := by
    intro t ht
    simp only [Finset.mem_filter] at ht
    simp only [Finset.mem_union, Finset.mem_singleton]
    rcases Nat.eq_or_lt_of_le (hmin t ht.2.1) with h | h
    · exact Or.inl h.symm
    · right
      obtain ⟨u, hu, hc⟩ := conflict_of_fails σ ht.2
      rcases hu with rfl | rfl
      · exact Or.inl (Finset.mem_filter.2 ⟨ht.1, ht.2, h, hc⟩)
      · exact Or.inr (Finset.mem_filter.2 ⟨ht.1, ht.2, h, hc⟩)
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le {t₁} (F (p - 1) ∪ F (p + 1))
  have hu2 := Finset.card_union_le (F (p - 1)) (F (p + 1))
  have := hF (p - 1) (Or.inl rfl)
  have := hF (p + 1) (Or.inr rfl)
  have := workActs_le_fails (alg1 ι) (init1 X) σ p T
  simp only [Finset.card_singleton] at hu1
  omega

end Max

/-- A local minimum returns after at most 4 activations (by the `a ↔ b` symmetry). -/
theorem workActs_le_four_of_min {X : ZMod n → ι} (hX : ∀ p, X p ≠ X (p + 1))
    (σ : ℕ → Finset (ZMod n)) {p : ZMod n} (hm1 : X p < X (p - 1)) (hm2 : X p < X (p + 1))
    (T : ℕ) : workActs (alg1 ι) (init1 X) σ p T ≤ 4 := by
  rw [← workActs_alg1_dual]
  exact workActs_le_four_of_max (X := fun q => OrderDual.toDual (X q)) σ (by simpa using hm1)
    (by simpa using hm2) (fun q h => hX q (OrderDual.toDual.injective h)) T

/-- Per-process bound: local extrema return within 4 activations, the other processes within
`ℓ + ℓ' + 1 ≤ n` activations. -/
theorem alg1_workActs_le [NeZero n] {X : ZMod n → ι} (hX : ∀ p, X p ≠ X (p + 1))
    (σ : ℕ → Finset (ZMod n)) (p : ZMod n) (T : ℕ) :
    workActs (alg1 ι) (init1 X) σ p T ≤ max 4 n := by
  by_cases hmin : X p < X (p - 1) ∧ X p < X (p + 1)
  · exact (workActs_le_four_of_min hX σ hmin.1 hmin.2 T).trans (le_max_left _ _)
  by_cases hmax : X (p - 1) < X p ∧ X (p + 1) < X p
  · exact (workActs_le_four_of_max σ hmax.1 hmax.2 hX T).trans (le_max_left _ _)
  have h1 := lemma_3_9 hX σ p hmin hmax T
  have h2 := upDist_add_downDist_le X p
  have : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  omega

/-- **Theorem 3.1** of [Fraigniaud, Lambein-Monette, Rabie, PODC 2022]: for every proper initial
colouring `X` of `C_n` (`n ≥ 3`), in every execution of Algorithm 1,
* (termination) every process returns after at most `⌊3n/2⌋ + 4` activations
  (we prove the sharper `max 4 n`, `alg1_workActs_le`);
* (6-colour palette) every output `(a, b)` satisfies `a + b ≤ 2`;
* (correctness) neighbouring terminated processes output different colours. -/
theorem theorem_3_1 (hn : 3 ≤ n) (X : ZMod n → ℕ) (hX : ∀ p, X p ≠ X (p + 1)) :
    WaitFreeWithin (alg1 ℕ) (init1 X) (3 * n / 2 + 4) ∧
      OutputsIn (alg1 ℕ) (init1 X) {c | c.1 + c.2 ≤ 2} ∧
      ProperOutputs (alg1 ℕ) (init1 X) := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨fun σ p T => (alg1_workActs_le hX σ p T).trans ?_, alg1_outputs_six X,
    alg1_properOutputs X⟩
  omega

end AsyncCycle
