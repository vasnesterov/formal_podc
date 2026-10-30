import Papers.PODC2022.PPLeadersStateComplexity.MainBound

/-!
# Theorem 4.3 (Leroux, PODC 2022)

A protocol of interaction-width at most `m` with `|ρ_L|` leaders that stably computes the
counting predicate `(i ≥ n)` satisfies `n ≤ (4 + 4m + 2|ρ_L|)^(|P|^((|P|+2)^2))`.

The case `|P| ≥ 2` is Section 8 (`Sec8.main_bound`, with the Petri net
`{t ∈ →* | |t| ≤ m}` of Section 3); the case `|P| = 1` (the paper: "if `d = 1` then `n = 1`")
is `n_le_one_of_card_le_one`.
-/

namespace Podc.PPLeadersStateComplexity

set_option linter.unusedSectionVars false

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- With a single state, only the predicate `(i ≥ 1)` (or `n = 0`) can be stably computed
(any protocol, no width assumption). -/
theorem n_le_one_of_card_le_one (Pr : Protocol P) {i : P} {n : ℕ} (hP : Fintype.card P ≤ 1)
    (h : Pr.StablyComputesGe i n) : n ≤ 1 := by
  have hall : ∀ p, p = i := fun p => Fintype.card_le_one_iff.1 hP p i
  have hsingle : ∀ x : Config P, x = Pi.single i (x i) := fun x => by
    funext p; rw [hall p]; simp
  obtain ⟨hI, hc⟩ := h
  have hin : ∀ c, Pr.IsInput (Pi.single i c) := fun c p hp => by
    rw [hI, Finset.mem_singleton] at hp; exact absurd (hall p) hp
  by_contra hn
  push_neg at hn
  -- `S₀`-configurations are `0` (otherwise the output of `i` would be `0`)
  -- and the output of `i` is `1` (input `n`)
  obtain ⟨β, -, hβ⟩ := hc _ (hin n) _ (Pr.refl _)
  have hβS1 : β ∈ Pr.S1 := by simpa [Protocol.stable, countingPred] using hβ
  have hγ : Pr.γ i = Out.one := by
    have := hβS1 β (Pr.refl β)
    have h1 : Out.one ∈ Pr.outputs β := by rw [this]; rfl
    obtain ⟨p, -, hp⟩ := h1
    rwa [hall p] at hp
  have hS0 : ∀ x, x ∈ Pr.S0 → ∀ y, Pr.R x y → y = 0 := by
    intro x hx y hy
    have := hx y hy
    funext p
    by_contra hne
    have : Out.one ∈ Pr.outputs y := ⟨p, Nat.pos_of_ne_zero hne, by rw [hall p, hγ]⟩
    have := hx y hy this
    simp at this
  -- `ρ_L →* 0` (input `0`) and `i →* 0` (input `1 < n`)
  obtain ⟨β0, hβ0, hβ0S⟩ := hc _ (hin 0) _ (Pr.refl _)
  have hβ0S' : β0 ∈ Pr.S0 := by
    simpa [Protocol.stable, countingPred, show ¬ n ≤ 0 by omega] using hβ0S
  have hL0 : Pr.R (Pr.leaders + Pi.single i 0) 0 := by
    have := hS0 β0 hβ0S' β0 (Pr.refl _); rw [this] at hβ0; exact hβ0
  have hL : Pr.R Pr.leaders 0 := by simpa using hL0
  have hi1 : Pr.R (Pr.leaders + Pi.single i 1) (Pi.single i 1) := by
    simpa using Pr.add _ _ (Pi.single i 1) hL
  obtain ⟨β1, hβ1, hβ1S⟩ := hc _ (hin 1) _ hi1
  have hβ1S' : β1 ∈ Pr.S0 := by
    simpa [Protocol.stable, countingPred, show ¬ n ≤ 1 by omega] using hβ1S
  have hone : Pr.R (Pi.single i 1) 0 := by
    have := hS0 β1 hβ1S' β1 (Pr.refl _); rwa [this] at hβ1
  have hall0 : ∀ c, Pr.R (Pi.single i c) 0 := by
    intro c
    induction c with
    | zero => simpa using Pr.refl (0 : Config P)
    | succ c ih =>
      have h1 := Pr.add _ _ (Pi.single i c) hone
      have e : (Pi.single i 1 : Config P) + Pi.single i c = Pi.single i (c + 1) := by
        rw [← Pi.single_add, add_comm]
      rw [e, zero_add] at h1
      exact Pr.trans _ _ _ h1 ih
  -- the `1`-output stable `β` reaches `0`, whose output is `∅ ≠ {1}`
  have h0 := hβS1 0 (by rw [hsingle β]; exact hall0 _)
  have : Out.one ∈ Pr.outputs 0 := by rw [h0]; rfl
  obtain ⟨p, hp, -⟩ := this
  simp at hp

/-- **Theorem 4.3.** A protocol of interaction-width at most `m` that stably computes the
`(i ≥ n)` predicate satisfies `n ≤ (4 + 4m + 2|ρ_L|)^(|P|^((|P|+2)^2))`. -/
theorem theorem_4_3 (Pr : Protocol P) {i : P} {n m : ℕ} (hw : HasWidthLE Pr.R m)
    (h : Pr.StablyComputesGe i n) :
    n ≤ (4 + 4 * m + 2 * Pr.numLeaders) ^ (Fintype.card P ^ (Fintype.card P + 2) ^ 2) := by
  rcases Nat.lt_or_ge (Fintype.card P) 2 with hd | hd
  · have := n_le_one_of_card_le_one Pr (by omega) h
    exact this.trans (Nat.one_le_pow _ _ (by omega))
  set T := widthNet Pr.R m
  have hR : ∀ α β, Pr.R α β ↔ Reach T α β := fun α β => Pr.reach_iff hw
  have h1 := Sec8.main_bound Pr T hR h hd
  rw [← pow_add] at h1
  have h2 := Arith.final (Fintype.card P) (netNorm T) (supNorm Pr.leaders) hd
  rw [show 2 * Fintype.card P + 5 + (2 ^ Fintype.card P + 2 * Fintype.card P + 4) =
    2 ^ Fintype.card P + 4 * Fintype.card P + 9 by ring] at h1
  refine (h1.trans h2).trans (Nat.pow_le_pow_left ?_ _)
  have : netNorm T ≤ m := netNorm_widthNet_le Pr.R m
  have := supNorm_le_size Pr.leaders
  simp only [Protocol.numLeaders]
  omega

/-- **Theorem 4.3**, with the interaction-width `width(→*)` of the paper. -/
theorem theorem_4_3' (Pr : Protocol P) {i : P} {n : ℕ} (hw : width Pr.R ≠ ⊤)
    (h : Pr.StablyComputesGe i n) :
    n ≤ (4 + 4 * (width Pr.R).toNat + 2 * Pr.numLeaders) ^
      (Fintype.card P ^ (Fintype.card P + 2) ^ 2) := by
  obtain ⟨m', hm', hw'⟩ := hasWidthLE_of_width_le (R := Pr.R) (m := (width Pr.R).toNat)
    (by rw [ENat.natCast_toNat hw])
  refine (theorem_4_3 Pr hw' h).trans (Nat.pow_le_pow_left ?_ _)
  omega

end Podc.PPLeadersStateComplexity
