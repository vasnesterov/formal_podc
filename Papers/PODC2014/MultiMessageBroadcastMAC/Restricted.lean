import Papers.PODC2014.MultiMessageBroadcastMAC.Arbitrary

/-!
# Theorem 3.2: BMMB in `O(D F_prog + r k F_ack)` time for `r`-restricted `G'`

§3.2.3–3.2.5: Lemma 3.11 (slow progress), the complexity bounds of Lemma 3.12 for the times
`t_{d,ℓ}`, Lemmas 3.13–3.15 (the double induction on `ℓ` and `d`), Theorem 3.16 and Theorem 3.2.

The paper uses `t_{d,ℓ}` without defining it. We take `t_{d,ℓ} = d F_prog + (ℓ - 1)((r + 1) F_prog
+ r F_ack)` (`tdl`): it satisfies parts 1–4 of Lemma 3.12, `t_{0,1} = 0` (used in the proof of
Lemma 3.13), and `t_{D,k}` is at most the bound `t₁` of Theorem 3.16 (with equality for `r = 1`).
Part 5 of Lemma 3.12 is false (`lemma_3_12_5_false`); the proof only needs the weaker
`(ℓ - 1) F_ack ≤ t_{0,ℓ}` (`lemma_3_12_5'`).
-/

namespace Podc.MultiMessageBroadcastMAC

variable {V M : Type*}

/-- `G'` is `r`-restricted: every `G'` edge joins nodes within `r` hops in `G`. -/
def RRestricted (G G' : SimpleGraph V) (r : ℕ) : Prop := ∀ u v, G'.Adj u v → G.edist u v ≤ r

/-- The time `t_{d,ℓ}` of §3.2.4: `d F_prog + (ℓ - 1)((r + 1) F_prog + r F_ack)`. -/
def tdl (r : ℕ) (Fprog Fack : ℝ) (d ℓ : ℕ) : ℝ :=
  d * Fprog + ((ℓ - 1 : ℕ) : ℝ) * ((r + 1) * Fprog + r * Fack)

section Bounds

variable {r : ℕ} {Fprog Fack : ℝ}

/-- **Lemma 3.12**, part 1: `t_{d,ℓ}` is monotone in `d`. -/
theorem lemma_3_12_1 (hFp : 0 ≤ Fprog) {d' d'' : ℕ} (h : d' ≤ d'') (ℓ : ℕ) :
    tdl r Fprog Fack d' ℓ ≤ tdl r Fprog Fack d'' ℓ := by
  unfold tdl
  have : (d' : ℝ) ≤ d'' := by exact_mod_cast h
  nlinarith

/-- **Lemma 3.12**, part 2: `t_{d+r,ℓ-1} + r F_ack ≤ t_{d,ℓ}` for `ℓ ≥ 2`. -/
theorem lemma_3_12_2 (hFp : 0 ≤ Fprog) (d ℓ : ℕ) :
    tdl r Fprog Fack (d + r) (ℓ + 1) + r * Fack ≤ tdl r Fprog Fack d (ℓ + 2) := by
  unfold tdl
  simp only [Nat.add_sub_cancel, show ℓ + 2 - 1 = ℓ + 1 by omega]
  push_cast
  nlinarith

/-- **Lemma 3.12**, part 3: `t_{d+r,ℓ-1} + F_ack ≤ t_{d-1,ℓ}` for `ℓ ≥ 2`, `d ≥ 1` (needs
`r ≥ 1`). -/
theorem lemma_3_12_3 (hr : 1 ≤ r) (hFa : 0 ≤ Fack) (d ℓ : ℕ) :
    tdl r Fprog Fack (d + 1 + r) (ℓ + 1) + Fack ≤ tdl r Fprog Fack d (ℓ + 2) := by
  unfold tdl
  simp only [Nat.add_sub_cancel, show ℓ + 2 - 1 = ℓ + 1 by omega]
  have : (1 : ℝ) ≤ r := by exact_mod_cast hr
  push_cast
  nlinarith

/-- **Lemma 3.12**, part 4: `t_{d-1,ℓ} + F_prog = t_{d,ℓ}`. -/
theorem lemma_3_12_4 (d ℓ : ℕ) :
    tdl r Fprog Fack d ℓ + Fprog = tdl r Fprog Fack (d + 1) ℓ := by
  unfold tdl; push_cast; ring

/-- **Lemma 3.12**, part 5, as needed in the proof of Lemma 3.14: `(ℓ - 1) F_ack ≤ t_{0,ℓ}`. -/
theorem lemma_3_12_5' (hr : 1 ≤ r) (hFp : 0 ≤ Fprog) (hFa : 0 ≤ Fack) (ℓ : ℕ) :
    ((ℓ - 1 : ℕ) : ℝ) * Fack ≤ tdl r Fprog Fack 0 ℓ := by
  unfold tdl
  have h0 : (0 : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith [mul_nonneg h0 (mul_nonneg (sub_nonneg.2 h1) hFa), mul_nonneg h0 hFp]

/-- **Lemma 3.12**, part 5 (`ℓ F_ack ≤ t_{0,ℓ}` for `ℓ > 1`) is false, both for our `t_{d,ℓ}` and
for `t_{d,ℓ} = (d + (r + 1) ℓ - 2) F_prog + r (ℓ - 1) F_ack` (the formula matching the bound `t₁` of
Theorem 3.16): take `r = 1`, `ℓ = 2`, `F_prog = 1`, `F_ack = 3`; then `ℓ F_ack = 6 > 5 = t_{0,2}`.
It fails whenever `F_ack > 2 F_prog`, the regime of interest. -/
theorem lemma_3_12_5_false :
    ¬ ((2 : ℕ) * (3 : ℝ) ≤ tdl 1 1 3 0 2) ∧
      ¬ ((2 : ℕ) * (3 : ℝ) ≤ ((0 : ℝ) + (1 + 1) * 2 - 2) * 1 + 1 * (2 - 1) * 3) := by
  unfold tdl; norm_num

/-- **Lemma 3.12**, part 5 is false for *every* choice of `t_{d,ℓ}` compatible with part 4 and with
the bound `t₁` of Theorem 3.16 (which the paper derives "directly from Lemma 3.15", i.e. from
`t_{D,k} ≤ t₁`): for `r = 1`, `k = ℓ = 2`, `F_prog = 1`, `F_ack = 3`, part 4 gives
`t_{D,2} = t_{0,2} + D`, so `t_{D,2} ≤ t₁ = D + 5` forces `t_{0,2} ≤ 5 < 6 = ℓ F_ack`. -/
theorem lemma_3_12_5_false_any (t : ℕ → ℕ → ℝ) (h4 : ∀ d, t d 2 + 1 = t (d + 1) 2) (D : ℕ)
    (ht₁ : t D 2 ≤ ((D : ℝ) + (1 + 1) * 2 - 2) * 1 + 1 * (2 - 1) * 3) :
    ¬ ((2 : ℕ) * (3 : ℝ) ≤ t 0 2) := by
  have h : ∀ d : ℕ, t d 2 = t 0 2 + d := by
    intro d
    induction d with
    | zero => simp
    | succ d ih => rw [← h4, ih]; push_cast; ring
  rw [h D] at ht₁
  norm_num at ht₁ ⊢
  linarith

end Bounds

namespace Exec

variable [DecidableEq V] [DecidableEq M] {G G' : SimpleGraph V} {α : Exec G G' M}

/-- **Lemma 3.11**: if `|C_j(t)| ≥ ℓ - 1`, every node within `z` hops of `j` has acknowledged
everything `j` has, and some node within `z` hops of `j` got `ℓ` messages, then `j` gets `ℓ`
messages by time `t + z F_ack`. -/
theorem lemma_3_11 {Fack : ℝ} (hA : α.AckBound Fack) (hF : 0 ≤ Fack) {j : V} {ℓ : ℕ}
    (hℓ : 0 < ℓ) (z : ℕ) {t : ℝ} (ht : 0 ≤ t) (h1 : ℓ - 1 ≤ (α.C j t).card)
    (h2 : ∀ j', G.edist j j' ≤ z → α.C j t ⊆ α.C j' t)
    (h3 : ∃ j'', G.edist j j'' ≤ z ∧ ℓ ≤ (α.R j'' t).card) :
    ℓ ≤ (α.R j (t + z * Fack)).card := by
  induction z generalizing t with
  | zero =>
    obtain ⟨j'', hj'', hR⟩ := h3
    obtain rfl : j = j'' := (SimpleGraph.edist_eq_zero_iff (G := G)).1 (by simpa using hj'')
    simpa using hR
  | succ z ih =>
    have htF : t ≤ t + Fack := by linarith
    have hT : t + Fack + z * Fack = t + ((z + 1 : ℕ) : ℝ) * Fack := by push_cast; ring
    have hmono : ∀ s, t ≤ s → s ≤ t + ((z + 1 : ℕ) : ℝ) * Fack →
        ℓ ≤ (α.R j s).card → ℓ ≤ (α.R j (t + ((z + 1 : ℕ) : ℝ) * Fack)).card :=
      fun s _ hs h => h.trans (Finset.card_le_card (α.lemma_3_5_1 j hs).1)
    by_cases hRj : ℓ ≤ (α.R j t).card
    · exact hmono t le_rfl (le_add_of_nonneg_right (by positivity)) hRj
    by_cases hCj : α.C j (t + Fack) = α.C j t
    · obtain ⟨j'', hj'', hR''⟩ := h3
      -- `j''` is not `j`, so it is at distance `e + 1 ≤ z + 1`
      have hfin := SimpleGraph.edist_eq_natCast_dist_of_le hj''
      obtain ⟨e, he⟩ : ∃ e, G.dist j j'' = e + 1 := by
        refine Nat.exists_eq_add_one.2 (Nat.pos_of_ne_zero fun h0 => hRj ?_)
        rw [h0, Nat.cast_zero, SimpleGraph.edist_eq_zero_iff] at hfin
        rwa [hfin]
      rw [he] at hfin
      have hez : e ≤ z := by
        have := hj''; rw [hfin] at this; exact_mod_cast Nat.succ_le_succ_iff.1 (by exact_mod_cast this)
      obtain ⟨y, hy, hyj''⟩ := SimpleGraph.exists_adj_of_edist_eq_succ hfin
      have hC'' : ℓ ≤ (α.C j'' (t + Fack)).card :=
        corollary_3_8 hA hF ht hℓ (h1.trans (Finset.card_le_card (h2 j'' hj''))) hR''
      have := ih (t := t + Fack) (by linarith)
        (h1.trans (Finset.card_le_card (α.lemma_3_5_1 j htF).2))
        (fun j' hj' => by
          rw [hCj]
          exact (h2 j' (hj'.trans (by exact_mod_cast Nat.le_succ z))).trans
            (α.lemma_3_5_1 j' htF).2)
        ⟨y, by rw [hy]; exact_mod_cast hez,
          hC''.trans (Finset.card_le_card (α.lemma_3_5_3 hyj'' le_rfl))⟩
      rwa [hT] at this
    · have hlt : (α.C j t).card < (α.C j (t + Fack)).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨(α.lemma_3_5_1 j htF).2, Ne.symm hCj⟩)
      refine hmono (t + Fack) htF (by push_cast; nlinarith) ?_
      exact (show ℓ ≤ (α.C j (t + Fack)).card by omega).trans
        (Finset.card_le_card (α.C_subset_R j _))

variable {r : ℕ} {Fprog Fack : ℝ}

/-- **Lemma 3.13**: a node `j` at distance `d` from the source `i₀` of `m` has
`R_j(t_{d,1}) ≠ ∅` and `C_j(t_{d,1} + F_ack) ≠ ∅`. -/
theorem lemma_3_13 (hG : G ≤ G') (hA : α.AckBound Fack) (hP : α.ProgBound Fprog)
    (hFp : 0 ≤ Fprog) (hFa : 0 ≤ Fack) (h0 : α.ArrivalsAtZero) {i₀ : V} {m : M}
    (hm : α.Arrives i₀ m) (d : ℕ) {j : V} (hj : G.edist i₀ j = d) :
    (α.R j (tdl r Fprog Fack d 1)).Nonempty ∧ (α.C j (tdl r Fprog Fack d 1 + Fack)).Nonempty := by
  have h1 : (α.R j (tdl r Fprog Fack d 1)).Nonempty := by
    induction d generalizing j with
    | zero =>
      obtain rfl : i₀ = j := (SimpleGraph.edist_eq_zero_iff (G := G)).1 (by simpa using hj)
      exact ⟨m, by simpa [tdl] using α.mem_R_zero h0 hm⟩
    | succ d ih =>
      obtain ⟨y, hy, hyj⟩ := SimpleGraph.exists_adj_of_edist_eq_succ hj
      have := lemma_3_9 hG hP hFp hyj.symm (by unfold tdl; positivity) (ih hy)
      rwa [lemma_3_12_4] at this
  refine ⟨h1, ?_⟩
  have := lemma_3_7_3 hA hFa (by unfold tdl; positivity) (k := 1) (Finset.card_pos.2 h1)
  simpa using this

/-- **Lemma 3.14**: for `ℓ ≥ 1`, `m ∈ R_{i₀}(t_{0,ℓ})`, and `m ∈ C_{i₀}(t_{0,ℓ} + F_ack)` or
`|C_{i₀}(t_{0,ℓ} + F_ack)| ≥ ℓ`. -/
theorem lemma_3_14 (hr : 1 ≤ r) (hA : α.AckBound Fack) (hFp : 0 ≤ Fprog) (hFa : 0 ≤ Fack)
    (h0 : α.ArrivalsAtZero) {i₀ : V} {m : M} (hm : α.Arrives i₀ m) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    m ∈ α.R i₀ (tdl r Fprog Fack 0 ℓ) ∧
      (m ∈ α.C i₀ (tdl r Fprog Fack 0 ℓ + Fack) ∨
        ℓ ≤ (α.C i₀ (tdl r Fprog Fack 0 ℓ + Fack)).card) := by
  have ht0 : 0 ≤ tdl r Fprog Fack 0 ℓ := by unfold tdl; positivity
  refine ⟨(α.lemma_3_5_1 i₀ ht0).1 (α.mem_R_zero h0 hm), ?_⟩
  have hle : (0 : ℝ) + ℓ * Fack ≤ tdl r Fprog Fack 0 ℓ + Fack := by
    have := lemma_3_12_5' hr hFp hFa ℓ
    have hc : ((ℓ - 1 : ℕ) : ℝ) = ℓ - 1 := by rw [Nat.cast_sub hℓ, Nat.cast_one]
    rw [hc] at this; linarith
  rcases mem_C_or_le_card hA hFa le_rfl (α.mem_R_zero h0 hm) ℓ with h | h
  · exact Or.inl ((α.lemma_3_5_1 i₀ hle).2 h)
  · exact Or.inr (h.trans (Finset.card_le_card (α.lemma_3_5_1 i₀ hle).2))

/-- **Lemma 3.15** (the key lemma), for an `r`-restricted `G'` with `r ≥ 1`: for a node `j` at
distance `d` from the source `i₀` of `m` and `ℓ ≥ 1`,
1. `m ∈ R_j(t_{d,ℓ})` or `|R_j(t_{d,ℓ})| ≥ ℓ`;
2. `m ∈ C_j(t_{d,ℓ} + F_ack)` or `|C_j(t_{d,ℓ} + F_ack)| ≥ ℓ`. -/
theorem lemma_3_15 (hG : G ≤ G') (hr : 1 ≤ r) (hres : RRestricted G G' r)
    (hA : α.AckBound Fack) (hP : α.ProgBound Fprog) (hFp : 0 ≤ Fprog) (hFa : 0 ≤ Fack)
    (h0 : α.ArrivalsAtZero) {i₀ : V} {m : M} (hm : α.Arrives i₀ m) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (d : ℕ) (j : V) (hj : G.edist i₀ j = d) :
    (m ∈ α.R j (tdl r Fprog Fack d ℓ) ∨ ℓ ≤ (α.R j (tdl r Fprog Fack d ℓ)).card) ∧
      (m ∈ α.C j (tdl r Fprog Fack d ℓ + Fack) ∨
        ℓ ≤ (α.C j (tdl r Fprog Fack d ℓ + Fack)).card) := by
  set t := tdl r Fprog Fack with ht_def
  have tnn : ∀ d ℓ, 0 ≤ t d ℓ := fun d ℓ => by simp only [ht_def, tdl]; positivity
  induction ℓ, hℓ using Nat.le_induction generalizing d j with
  | base =>
    obtain ⟨h1, h2⟩ := lemma_3_13 (r := r) hG hA hP hFp hFa h0 hm d hj
    exact ⟨Or.inr (Finset.card_pos.2 h1), Or.inr (Finset.card_pos.2 h2)⟩
  | succ ℓ hℓ ihℓ =>
    induction d generalizing j with
    | zero =>
      obtain rfl : i₀ = j := (SimpleGraph.edist_eq_zero_iff (G := G)).1 (by simpa using hj)
      obtain ⟨h1, h2⟩ := lemma_3_14 hr hA hFp hFa h0 hm (ℓ := ℓ + 1) (by omega)
      exact ⟨Or.inl h1, h2⟩
    | succ d ihd =>
      -- paper's `ℓ ≥ 2` is our `ℓ + 1`, paper's `d ≥ 1` is our `d + 1`
      set τ := t (d + 1) (ℓ + 1)
      set ts := t (d + 1 + r) ℓ + Fack with hts_def
      have hℓ' : ℓ + 1 = (ℓ - 1) + 2 := by omega
      have hts_le : ts + (r - 1 : ℕ) * Fack ≤ τ := by
        have := lemma_3_12_2 (r := r) (Fack := Fack) hFp (d + 1) (ℓ - 1)
        rw [show ℓ - 1 + 1 = ℓ by omega, ← hℓ'] at this
        have hc : ((r - 1 : ℕ) : ℝ) = r - 1 := by rw [Nat.cast_sub hr, Nat.cast_one]
        simp only [hts_def, hc, τ, ht_def]; linarith
      have hts_τ : ts ≤ τ := by
        have : (0 : ℝ) ≤ (r - 1 : ℕ) * Fack := by positivity
        linarith
      have hts0 : 0 ≤ ts := by simp only [hts_def]; linarith [tnn (d + 1 + r) ℓ]
      have hτ0 : 0 ≤ τ := tnn _ _
      -- (S1): every node within `r` hops of `j` acknowledged `m` or `ℓ` messages by `ts`
      have S1 : ∀ j', G.edist j j' ≤ r → m ∈ α.C j' ts ∨ ℓ ≤ (α.C j' ts).card := by
        intro j' hj'
        have hle : G.edist i₀ j' ≤ ((d + 1 + r : ℕ) : ℕ∞) :=
          SimpleGraph.edist_le_natCast_add (by rw [hj]) hj'
        have he := SimpleGraph.edist_eq_natCast_dist_of_le hle
        have hdist : G.dist i₀ j' ≤ d + 1 + r := SimpleGraph.dist_le_of_edist_le_natCast hle
        have hmono : t (G.dist i₀ j') ℓ + Fack ≤ ts := by
          simp only [hts_def]; linarith [lemma_3_12_1 (r := r) (Fack := Fack) hFp hdist ℓ]
        rcases (ihℓ (G.dist i₀ j') j' he).2 with h | h
        · exact Or.inl ((α.lemma_3_5_1 j' hmono).2 h)
        · exact Or.inr (h.trans (Finset.card_le_card (α.lemma_3_5_1 j' hmono).2))
      -- Part 1
      have part1 : m ∈ α.R j τ ∨ ℓ + 1 ≤ (α.R j τ).card := by
        by_cases hdone : m ∈ α.C j ts ∨ ℓ + 1 ≤ (α.C j ts).card
        · rcases hdone with h | h
          · exact Or.inl (α.lemma_3_5_2 j hts_τ h)
          · exact Or.inr (h.trans (Finset.card_le_card (α.lemma_3_5_2 j hts_τ)))
        push Not at hdone
        obtain ⟨hmC, hcard⟩ := hdone
        have hCj : (α.C j ts).card = ℓ := by
          rcases S1 j (by simp) with h | h
          · exact absurd h hmC
          · omega
        right
        by_cases hcase : ∃ j', G.edist j j' ≤ r ∧ α.C j' ts ≠ α.C j ts
        · -- Case 1: a closest node `j''` within `r` hops whose `C` differs from `C_j`
          classical
          have hex : ∃ e : ℕ, ∃ j', G.edist j j' = e ∧ e ≤ r ∧ α.C j' ts ≠ α.C j ts := by
            obtain ⟨j', hj', hne⟩ := hcase
            have he := SimpleGraph.edist_eq_natCast_dist_of_le hj'
            exact ⟨G.dist j j', j', he, by rw [he] at hj'; exact_mod_cast hj', hne⟩
          obtain ⟨j'', hj''e, he0r, hne''⟩ := Nat.find_spec hex
          have hmin : ∀ j', G.edist j j' < Nat.find hex → α.C j' ts = α.C j ts := by
            intro j' hj'
            have he := SimpleGraph.edist_eq_natCast_dist_of_le hj'.le
            rw [he] at hj'
            have hlt : G.dist j j' < Nat.find hex := by exact_mod_cast hj'
            by_contra hne
            exact Nat.find_min hex hlt ⟨j', he, by omega, hne⟩
          obtain ⟨z, hz⟩ : ∃ z, Nat.find hex = z + 1 := by
            refine Nat.exists_eq_add_one.2 (Nat.pos_of_ne_zero fun h0 => hne'' ?_)
            rw [h0, Nat.cast_zero, SimpleGraph.edist_eq_zero_iff] at hj''e
            rw [hj''e]
          rw [hz] at hj''e hmin he0r
          obtain ⟨y, hy, hyj''⟩ := SimpleGraph.exists_adj_of_edist_eq_succ hj''e
          have hCeq : ∀ j', G.edist j j' ≤ z → α.C j' ts = α.C j ts := fun j' hj' =>
            hmin j' (lt_of_le_of_lt hj' (by exact_mod_cast Nat.lt_succ_self z))
          have hCy := hCeq y hy.le
          -- `y` got a message that it has not acknowledged
          obtain ⟨m', hm'C'', hm'Cy⟩ : ∃ m' ∈ α.C j'' ts, m' ∉ α.C y ts := by
            rcases S1 j'' (hj''e.le.trans (by exact_mod_cast he0r)) with h | h
            · exact ⟨m, h, by rw [hCy]; exact hmC⟩
            · by_contra hall
              push Not at hall
              exact hne'' ((Finset.eq_of_subset_of_card_le hall (by rw [hCy]; omega)).trans hCy)
          have hRy : ℓ + 1 ≤ (α.R y ts).card := by
            have hsub : insert m' (α.C y ts) ⊆ α.R y ts :=
              Finset.insert_subset (α.lemma_3_5_3 hyj'' le_rfl hm'C'') (α.C_subset_R y ts)
            have := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem hm'Cy, hCy, hCj] at this
            exact this
          have h311 := lemma_3_11 hA hFa (ℓ := ℓ + 1) (by omega) z hts0 (by rw [hCj]; omega)
            (fun j' hj' => (hCeq j' hj').symm.subset) ⟨y, hy.le, hRy⟩
          have hzr : (z : ℝ) * Fack ≤ (r - 1 : ℕ) * Fack := by
            gcongr; omega
          exact h311.trans (Finset.card_le_card (α.lemma_3_5_1 j (by linarith)).1)
        · -- Case 2: all nodes within `r` hops have the same `C` as `j`
          push Not at hcase
          set s := t d (ℓ + 1)
          have hs_eq : s + Fprog = τ := lemma_3_12_4 d (ℓ + 1)
          have hts_s : ts ≤ s := by
            have := lemma_3_12_3 (r := r) (Fprog := Fprog) hr hFa d (ℓ - 1)
            rw [show ℓ - 1 + 1 = ℓ by omega, ← hℓ'] at this
            simpa only [hts_def, s, ht_def] using this
          have hs0 : 0 ≤ s := tnn _ _
          by_cases hRs : ℓ + 1 ≤ (α.R j s).card
          · exact hRs.trans (Finset.card_le_card (α.lemma_3_5_1 j (by linarith)).1)
          have hsub : α.C j ts ⊆ α.R j s := α.lemma_3_5_2 j hts_s
          have hReq : α.R j s = α.C j ts :=
            (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
          obtain ⟨y, hy, hyj⟩ := SimpleGraph.exists_adj_of_edist_eq_succ hj
          have h310 := lemma_3_10 hG hP hFp hyj.symm hs0
            (fun i' hi' => by
              rw [hReq, ← hcase i' (by rw [SimpleGraph.edist_comm]; exact hres i' j hi')]
              exact (α.lemma_3_5_1 i' hts_s).2)
            (by
              rcases (ihd y hy).1 with h | h
              · exact ⟨m, Finset.mem_sdiff.2 ⟨h, by rw [hReq]; exact hmC⟩⟩
              · by_contra hemp
                rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
                have := Finset.card_le_card hemp
                rw [hReq, hCj] at this
                omega)
          rw [hs_eq, hReq, hCj] at h310
          exact h310
      refine ⟨part1, ?_⟩
      -- Part 2
      by_cases hmC : m ∈ α.C j ts
      · exact Or.inl ((α.lemma_3_5_1 j (by linarith)).2 hmC)
      right
      have hCj : ℓ ≤ (α.C j ts).card := by
        rcases S1 j (by simp) with h | h
        · exact absurd h hmC
        · exact h
      have hRτ : ℓ + 1 ≤ (α.R j τ).card := by
        rcases part1 with h | h
        · have hsub : insert m (α.C j ts) ⊆ α.R j τ :=
            Finset.insert_subset h (α.lemma_3_5_2 j hts_τ)
          have := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hmC] at this
          omega
        · exact h
      have hCτ : ℓ + 1 - 1 ≤ (α.C j τ).card := by
        rw [Nat.add_sub_cancel]
        exact hCj.trans (Finset.card_le_card (α.lemma_3_5_1 j hts_τ).2)
      exact corollary_3_8 hA hFa hτ0 (by omega) hCτ hRτ

/-- **Theorem 3.16**: with an `r`-restricted `G'` (`r ≥ 1`) and at most `k` messages, all arriving
at time `0`, every message `m` arriving at `i₀` is received by every node `j` of `i₀`'s component
within distance `D` of `i₀` by time `t₁ = (D + (r + 1) k - 2) F_prog + r (k - 1) F_ack`. -/
theorem theorem_3_16 (hG : G ≤ G') (hr : 1 ≤ r) (hres : RRestricted G G' r)
    (hA : α.AckBound Fack) (hP : α.ProgBound Fprog) (hFp : 0 ≤ Fprog) (hFa : 0 ≤ Fack)
    (h0 : α.ArrivalsAtZero) {K : Finset M} (hK : ∀ i m, α.Arrives i m → m ∈ K) {k : ℕ}
    (hk : K.card ≤ k) {D : ℕ} {i₀ j : V} {m : M} (hm : α.Arrives i₀ m) (hj : G.Reachable i₀ j)
    (hD : G.dist i₀ j ≤ D) :
    m ∈ α.R j (((D : ℝ) + (r + 1) * k - 2) * Fprog + r * (k - 1) * Fack) := by
  have hk1 : 1 ≤ k := (Finset.card_pos.2 ⟨m, hK i₀ m hm⟩).trans_le hk
  have hmem : m ∈ α.R j (tdl r Fprog Fack (G.dist i₀ j) k) := by
    rcases (lemma_3_15 hG hr hres hA hP hFp hFa h0 hm k hk1 (G.dist i₀ j) j
      hj.coe_dist_eq_edist.symm).1 with h | h
    · exact h
    · have heq := Finset.eq_of_subset_of_card_le (α.R_subset hK j _) (hk.trans h)
      rw [heq]; exact hK i₀ m hm
  refine (α.lemma_3_5_1 j ?_).1 hmem
  unfold tdl
  have hc : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub hk1, Nat.cast_one]
  have hD' : ((G.dist i₀ j : ℕ) : ℝ) ≤ D := by exact_mod_cast hD
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  rw [hc]
  nlinarith

/-- **Theorem 3.16**, as stated in the paper for a connected `G` of diameter at most `D`: if `K` is
the set of messages that arrive (all at time `0`) and `|K| ≤ k`, then `R_j(t₁) = K` for every
node `j`. -/
theorem theorem_3_16_connected (hG : G ≤ G') (hconn : G.Connected) (hr : 1 ≤ r)
    (hres : RRestricted G G' r) (hA : α.AckBound Fack) (hP : α.ProgBound Fprog)
    (hFp : 0 ≤ Fprog) (hFa : 0 ≤ Fack) (h0 : α.ArrivalsAtZero) {K : Finset M}
    (hK : ∀ m, m ∈ K ↔ ∃ i, α.Arrives i m) {k : ℕ} (hk : K.card ≤ k) {D : ℕ}
    (hD : ∀ u v, G.dist u v ≤ D) (j : V) :
    α.R j (((D : ℝ) + (r + 1) * k - 2) * Fprog + r * (k - 1) * Fack) = K := by
  refine subset_antisymm (α.R_subset (fun i m h => (hK m).2 ⟨i, h⟩) j _) fun m hm => ?_
  obtain ⟨i₀, hi₀⟩ := (hK m).1 hm
  exact theorem_3_16 hG hr hres hA hP hFp hFa h0 (fun i m h => (hK m).2 ⟨i, h⟩) hk hi₀
    (hconn.preconnected i₀ j) (hD i₀ j)

/-- **Theorem 3.2**: for an `r`-restricted `G'` (`r ≥ 1`), BMMB solves MMB in
`O(D F_prog + r k F_ack)` time: every message arriving (at time `0`) at `i₀` is received by every
node of `i₀`'s component within distance `D` by time `D F_prog + 3 r k F_ack`. No relation between
`F_prog` and `F_ack` is assumed: for `F_prog ≤ F_ack` this follows from Theorem 3.16, otherwise from
Theorem 3.1. -/
theorem theorem_3_2 (hG : G ≤ G') (hr : 1 ≤ r) (hres : RRestricted G G' r)
    (hA : α.AckBound Fack) (hP : α.ProgBound Fprog) (hFp : 0 ≤ Fprog) (hFa : 0 ≤ Fack)
    (h0 : α.ArrivalsAtZero) {K : Finset M} (hK : ∀ i m, α.Arrives i m → m ∈ K) {k : ℕ}
    (hk : K.card ≤ k) {D : ℕ} {i₀ j : V} {m : M} (hm : α.Arrives i₀ m) (hj : G.Reachable i₀ j)
    (hD : G.dist i₀ j ≤ D) :
    m ∈ α.R j (D * Fprog + 3 * r * k * Fack) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.card_pos.2 ⟨m, hK i₀ m hm⟩).trans_le hk
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  rcases le_total Fprog Fack with hle | hle
  · refine (α.lemma_3_5_1 j ?_).1 (theorem_3_16 hG hr hres hA hP hFp hFa h0 hK hk hm hj hD)
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hr') (sub_nonneg.2 hk1)) hFa,
      mul_nonneg (sub_nonneg.2 hle) (mul_nonneg (by linarith : (0 : ℝ) ≤ r + 1) (by linarith : (0 : ℝ) ≤ k)),
      mul_nonneg hD0 hFp]
  · refine (α.lemma_3_5_1 j ?_).1 (theorem_3_1_diam hA hFa h0 hK hk hm hj hD)
    nlinarith [mul_nonneg hD0 (sub_nonneg.2 hle),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hr') (by linarith : (0 : ℝ) ≤ k)) hFa,
      mul_nonneg (by linarith : (0 : ℝ) ≤ k) hFa, mul_nonneg (by linarith : (0 : ℝ) ≤ r) hFa]

end Exec

end Podc.MultiMessageBroadcastMAC
