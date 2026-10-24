import Papers.PODC2025.RendezvousLabeledLine.PathRulingSet

/-!
# Algorithm 3 (ES-ColPathRulingSet), membership part: the early-stopping ruling set

Nodes are partitioned into levels `V_i = {v | log* ℓ(v) = i}` (`i ≥ 1`); labels in `V_i` are
`< tower i`. Level `i` computes a `V_i`-limited `(R, R-1)`-ruling set `P_i` with Algorithm 2
(`O(R i)` rounds, Lemma 3.4), then the ruling set `S_{≤ i}` of levels `≤ i` is obtained from
`S_{< i}` by adding the nodes of `P_i` at distance `≥ R` from `S_{< i}` and four greedy steps
(Algorithm 3, lines 5–9). A node of level `i` decides its membership after `816 R i` rounds.
-/

namespace Podc.RendezvousLabeledLine

open Function Classical

namespace ES

variable (R : ℕ)

/-- Level `i` of the partition: `V_i = {v | log* ℓ(v) = i}`. -/
def Lv (i : ℕ) : (ℤ → ℕ) → ℤ → Prop := fun ℓ v => lstar (ℓ v) = i

/-- The `V_i`-limited ruling set computed by level `i` (Algorithm 3, line 3). -/
noncomputable def P (i : ℕ) : (ℤ → ℕ) → ℤ → Prop := prsRule (Lv i) R (Nat.tower i)

/-- No node of `S` within distance `R - 1`. -/
def Far (S : (ℤ → ℕ) → ℤ → Prop) : (ℤ → ℕ) → ℤ → Prop :=
  fun ℓ v => ∀ s, |s - v| ≤ (R : ℤ) - 1 → ¬ S ℓ s

/-- `S_{< i} ∪ S'_i` (Algorithm 3, lines 5–6). -/
def Q0 (S Pi : (ℤ → ℕ) → ℤ → Prop) : (ℤ → ℕ) → ℤ → Prop :=
  fun ℓ v => S ℓ v ∨ (Pi ℓ v ∧ Far R S ℓ v)

/-- `S_{≤ i}`, the ruling set after levels `1..i` (Algorithm 3, lines 3–9). -/
noncomputable def Sle : ℕ → (ℤ → ℕ) → ℤ → Prop
  | 0 => fun _ _ => False
  | i + 1 => gIterRule (Lv (i + 1)) (Q0 R (Sle i) (P R (i + 1))) R (2 * R) 4

lemma lt_tower_of_lstar {x i : ℕ} (h : lstar x = i) : x < Nat.tower i := by
  have := Nat.lt_tower_logStar_succ x
  simp only [lstar] at h; rwa [h] at this

lemma logStar_tower_le (i : ℕ) : Nat.logStar (Nat.tower i) ≤ i := by
  have := Nat.tower_logStar_le (Nat.tower_pos i).ne'
  exact Nat.tower_strictMono.le_iff_le.1 this

/-- Membership invariants of `S_{≤ i}`. -/
theorem Sle_spec (hR : 1 ≤ R) {ℓ : ℤ → ℕ} (hℓ : Injective ℓ) (i : ℕ) :
    Packed (Sle R i ℓ) R ∧ (∀ v, Sle R i ℓ v → lstar (ℓ v) ≤ i) ∧
    (∀ v, lstar (ℓ v) ≤ i → ∃ s, Sle R i ℓ s ∧ |v - s| ≤ (R : ℤ) - 1) ∧
    (∀ v, Sle R i ℓ v → Sle R (i + 1) ℓ v) ∧
    (∀ v, Sle R (i + 1) ℓ v → lstar (ℓ v) ≤ i → Sle R i ℓ v) := by
  induction i with
  | zero =>
    refine ⟨fun _ _ h => h.elim, fun _ h => h.elim, fun v hv => ?_, fun _ h => h.elim, ?_⟩
    · exact absurd hv (by have := one_le_lstar (ℓ v); omega)
    · intro v _ hv; exact absurd hv (by have := one_le_lstar (ℓ v); omega)
  | succ i ih =>
    obtain ⟨i1, i2, i3, -, -⟩ := ih
    -- level `i + 1` (and the step to `i + 2`)
    have key : ∀ j, (Packed (Sle R j ℓ) R ∧ (∀ v, Sle R j ℓ v → lstar (ℓ v) ≤ j) ∧
        (∀ v, lstar (ℓ v) ≤ j → ∃ s, Sle R j ℓ s ∧ |v - s| ≤ (R : ℤ) - 1)) →
        Packed (Sle R (j + 1) ℓ) R ∧ (∀ v, Sle R (j + 1) ℓ v → lstar (ℓ v) ≤ j + 1) ∧
        (∀ v, lstar (ℓ v) ≤ j + 1 → ∃ s, Sle R (j + 1) ℓ s ∧ |v - s| ≤ (R : ℤ) - 1) ∧
        (∀ v, Sle R j ℓ v → Sle R (j + 1) ℓ v) ∧
        (∀ v, Sle R (j + 1) ℓ v → lstar (ℓ v) ≤ j → Sle R j ℓ v) := by
      rintro j ⟨j1, j2, j3⟩
      obtain ⟨p1, p2, p3⟩ := lemma_3_4 (Lv (j + 1)) R (Nat.tower (j + 1)) hR hℓ
        (fun v hv => lt_tower_of_lstar hv)
      -- `Q0` is packed and covers level `j + 1` within `2R - 2`
      have q1 : Packed (Q0 R (Sle R j) (P R (j + 1)) ℓ) R := by
        rintro u w (hu | ⟨hu, hfu⟩) (hw | ⟨hw, hfw⟩) huw
        · exact j1 u w hu hw huw
        · by_contra h; exact hfw u (by omega) hu
        · by_contra h; exact hfu w (by rw [abs_sub_comm]; omega) hw
        · exact p2 u w hu hw huw
      have q2 : ∀ v, Lv (j + 1) ℓ v → ∃ q, Q0 R (Sle R j) (P R (j + 1)) ℓ q ∧
          |v - q| ≤ ((2 * R - 2 : ℕ) : ℤ) := by
        intro v hv
        obtain ⟨p, hp, hvp⟩ := p3 v hv
        by_cases hf : Far R (Sle R j) ℓ p
        · exact ⟨p, Or.inr ⟨hp, hf⟩, by push_cast [show 2 ≤ 2 * R by omega]; omega⟩
        · simp only [Far, not_forall, not_not] at hf
          obtain ⟨s, hs, hS⟩ := hf
          refine ⟨s, Or.inl hS, ?_⟩
          calc |v - s| = |(v - p) - (s - p)| := by ring_nf
            _ ≤ |v - p| + |s - p| := abs_sub _ _
            _ ≤ ((2 * R - 2 : ℕ) : ℤ) := by push_cast [show 2 ≤ 2 * R by omega]; omega
      obtain ⟨g1, g2, g3, g4⟩ := gIter_spec (Lv (j + 1) ℓ) (Q0 R (Sle R j) (P R (j + 1)) ℓ) ℓ hℓ
        R (2 * R) (2 * R - 2) 4 hR (by omega) (by omega) q1 q2 (Or.inr ⟨by omega, by omega⟩)
      have hsub : ∀ v, Sle R (j + 1) ℓ v → Sle R j ℓ v ∨ lstar (ℓ v) = j + 1 := by
        intro v hv
        rcases g2 v hv with (h | ⟨h, -⟩) | h
        · exact Or.inl h
        · exact Or.inr (p1 v h)
        · exact Or.inr h
      refine ⟨g1, fun v hv => ?_, fun v hv => ?_, fun v hv => g3 v (Or.inl hv), fun v hv hl => ?_⟩
      · rcases hsub v hv with h | h
        · have := j2 v h; omega
        · omega
      · rcases Nat.lt_or_ge (lstar (ℓ v)) (j + 1) with h | h
        · obtain ⟨s, hs, hvs⟩ := j3 v (by omega)
          exact ⟨s, g3 s (Or.inl hs), hvs⟩
        · exact g4 v (show lstar (ℓ v) = j + 1 by omega)
      · rcases hsub v hv with h | h
        · exact h
        · omega
    obtain ⟨k1, k2, k3, -, -⟩ := key i ⟨i1, i2, i3⟩
    obtain ⟨-, -, -, k4, k5⟩ := key (i + 1) ⟨k1, k2, k3⟩
    exact ⟨k1, k2, k3, k4, k5⟩

/-- `S_{≤ i}` and `S_{≤ j}` agree on levels `≤ i` for `j ≥ i`. -/
lemma Sle_stable (hR : 1 ≤ R) {ℓ : ℤ → ℕ} (hℓ : Injective ℓ) {i j : ℕ} (hij : i ≤ j) (v : ℤ)
    (hv : lstar (ℓ v) ≤ i) : Sle R j ℓ v ↔ Sle R i ℓ v := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← ih (by omega)]
    obtain ⟨-, -, -, h4, h5⟩ := Sle_spec R hR hℓ (i + d)
    exact ⟨fun h => h5 v h (by omega), fun h => h4 v h⟩

/-! ### Locality -/

lemma isLocal_Lv (i : ℕ) : IsLocal (Lv i) 0 := by
  intro ℓ ℓ' _ _ v hv
  simp only [Lv, hv v (by simp)]

lemma isLocal_or_and {A B C : (ℤ → ℕ) → ℤ → Prop} {ρ : ℕ} (hA : IsLocal A ρ) (hB : IsLocal B ρ)
    (hC : IsLocal C ρ) : IsLocal (fun ℓ v => A ℓ v ∨ (B ℓ v ∧ C ℓ v)) ρ := by
  intro ℓ ℓ' h h' v hv
  simp only [hA ℓ ℓ' h h' v hv, hB ℓ ℓ' h h' v hv, hC ℓ ℓ' h h' v hv]

lemma isLocal_Far {S : (ℤ → ℕ) → ℤ → Prop} {ρ : ℕ} (hS : IsLocal S ρ) :
    IsLocal (Far R S) (ρ + R) := by
  intro ℓ ℓ' h h' v hv
  simp only [Far]
  apply propext
  refine forall_congr' fun s => imp_congr_right fun hs => ?_
  rw [hS ℓ ℓ' h h' s fun x hx => hv x (by
    calc |x - v| = |(x - s) + (s - v)| := by ring_nf
      _ ≤ |x - s| + |s - v| := abs_add_le _ _
      _ ≤ _ := by push_cast; omega)]

/-- Membership in `S_{≤ i}` is decided after `816 R i` rounds. -/
theorem Sle_isLocal (hR : 1 ≤ R) (i : ℕ) : IsLocal (Sle R i) (816 * R * i) := by
  induction i with
  | zero => intro _ _ _ _ _ _; rfl
  | succ i ih =>
    have hP : IsLocal (P R (i + 1)) (3 * R * (i + 1 + 267)) := by
      have := lemma_3_4_isLocal (Lv (i + 1)) (isLocal_Lv (i + 1)) R (Nat.tower (i + 1)) hR
      refine this.mono ?_
      have := Nat.mul_le_mul_left (3 * R) (Nat.add_le_add_right (logStar_tower_le (i + 1)) 267)
      omega
    set ρ := max (3 * R * (i + 1 + 267)) (816 * R * i + R)
    have hQ : IsLocal (Q0 R (Sle R i) (P R (i + 1))) ρ :=
      isLocal_or_and (ih.mono (by omega)) (hP.mono (le_max_left _ _))
        ((isLocal_Far R ih).mono (le_max_right _ _))
    refine (gIterRule_isLocal ((isLocal_Lv (i + 1)).mono (Nat.zero_le ρ)) hQ R (2 * R) 4).mono ?_
    have h1 : 3 * R * (i + 1 + 267) + 4 * (2 * R + R) ≤ 816 * R * (i + 1) := by nlinarith
    have h2 : 816 * R * i + R + 4 * (2 * R + R) ≤ 816 * R * (i + 1) := by nlinarith
    rcases max_cases (3 * R * (i + 1 + 267)) (816 * R * i + R) with ⟨h, -⟩ | ⟨h, -⟩ <;>
      simp only [ρ, h] <;> omega

/-! ### Equivariance -/

lemma frame_surj (v : ℤ) (ε : ℤˣ) (x : ℤ) : frame v ε ((ε : ℤ) * (x - v)) = x := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [frame]

lemma isEquivar_Lv (i : ℕ) : IsEquivar (Lv i) := by
  intro ℓ v ε j; rfl

lemma isEquivar_Far {S : (ℤ → ℕ) → ℤ → Prop} (hS : IsEquivar S) : IsEquivar (Far R S) := by
  intro ℓ v ε j
  simp only [Far, eq_iff_iff]
  constructor
  · intro h s hs hS'
    have := h ((ε : ℤ) * (s - v)) (by rw [← abs_frame_sub_frame v ε, frame_surj]; exact hs)
    rw [hS, frame_surj] at this; exact this hS'
  · intro h s hs hS'
    rw [hS] at hS'
    exact h _ (by rw [← abs_frame_sub_frame v ε] at hs; exact hs) hS'

theorem Sle_isEquivar (i : ℕ) : IsEquivar (Sle R i) := by
  induction i with
  | zero => intro _ _ _ _; rfl
  | succ i ih =>
    refine gIterRule_isEquivar (isEquivar_Lv _) ?_ R (2 * R) 4
    intro ℓ v ε j
    simp only [Q0, P, ih ℓ v ε j, prsRule_isEquivar (Lv (i + 1)) (isEquivar_Lv _) R _ ℓ v ε j,
      isEquivar_Far R ih ℓ v ε j]

end ES

end Podc.RendezvousLabeledLine
