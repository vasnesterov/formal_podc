import Papers.PODC2025.RendezvousLabeledLine.LineLocal
import Papers.PODC2025.RendezvousLabeledLine.Greedy
import Cslib.Foundations.Data.Nat.Log

/-!
# Algorithm 2 (PathRulingSet) and Lemma 3.4

`U ℓ` is a set of nodes with labels `< n`. With `d = ⌈log₂ R⌉`, `S₀ = U` and
`S_j = MIS(G^{R_j}[S_{j-1}])` for `j = 1..d`, where `R_j = 2^j - 1` for `j < d` and `R_d = R - 1`;
then six greedy steps extend `S_d`. The result is a `U`-limited `(R, R-1)`-ruling set, computed
in `3R (log* n + 267) = O(R log* n)` rounds (Lemma 3.4).
-/

namespace Podc.RendezvousLabeledLine

open Function

/-- `R_j` of Algorithm 2 (line 2). -/
def prsRad (R j : ℕ) : ℕ := if j < Nat.clog 2 R then 2 ^ j - 1 else R - 1

/-- The sets `S_j` of Algorithm 2 (lines 1–4). -/
noncomputable def prsStage (U : (ℤ → ℕ) → ℤ → Prop) (R n : ℕ) : ℕ → (ℤ → ℕ) → ℤ → Prop
  | 0 => U
  | j + 1 => misRule (prsStage U R n j) (prsRad R (j + 1)) n

/-- **Algorithm 2** (PathRulingSet): `S_d` followed by six greedy steps (lines 5–8). -/
noncomputable def prsRule (U : (ℤ → ℕ) → ℤ → Prop) (R n : ℕ) : (ℤ → ℕ) → ℤ → Prop :=
  gIterRule U (prsStage U R n (Nat.clog 2 R)) R (3 * R) 6

/-- Packing distance of `S_j`. -/
def prsPack (R j : ℕ) : ℕ := if j < Nat.clog 2 R then 2 ^ j else R

/-- Covering distance of `S_j`. -/
def prsCov (R j : ℕ) : ℕ := if j < Nat.clog 2 R then 2 ^ (j + 1) - 2 else 3 * R - 3

lemma two_pow_clog_lt (R : ℕ) (hR : 1 ≤ R) : 2 ^ Nat.clog 2 R < 2 * R :=
  Nat.pow_clog_lt_mul (by norm_num) (by omega)

lemma le_two_pow_clog (R : ℕ) : R ≤ 2 ^ Nat.clog 2 R := Nat.le_pow_clog (by norm_num) R

/-- One MIS stage: radius, packing and covering bookkeeping. -/
lemma prs_step_arith (R j : ℕ) (hR : 1 ≤ R) (hj : j < Nat.clog 2 R) :
    prsRad R (j + 1) + 1 ≤ 2 * prsPack R j ∧ prsRad R (j + 1) + 1 = prsPack R (j + 1) ∧
      prsCov R j + prsRad R (j + 1) ≤ prsCov R (j + 1) := by
  have h1 := two_pow_clog_lt R hR
  have h2 := le_two_pow_clog R
  have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have hpos := Nat.one_le_two_pow (n := j)
  simp only [prsRad, prsPack, prsCov, ite_eq_left hj]
  by_cases hj1 : j + 1 < Nat.clog 2 R
  · simp only [ite_eq_left hj1]
    have : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
    omega
  · simp only [ite_eq_right hj1]
    have hd : Nat.clog 2 R = j + 1 := by omega
    rw [hd] at h1 h2
    omega

/-- Properties of the stages `S_j`, `j ≤ d`. -/
lemma prsStage_spec (U : (ℤ → ℕ) → ℤ → Prop) (R n : ℕ) (hR : 1 ≤ R) {ℓ : ℤ → ℕ}
    (hℓ : Injective ℓ) (hn : ∀ v, U ℓ v → ℓ v < n) (j : ℕ) (hj : j ≤ Nat.clog 2 R) :
    (∀ v, prsStage U R n j ℓ v → U ℓ v) ∧ Packed (prsStage U R n j ℓ) (prsPack R j) ∧
      ∀ v, U ℓ v → ∃ s, prsStage U R n j ℓ s ∧ |v - s| ≤ (prsCov R j : ℤ) := by
  induction j with
  | zero =>
    refine ⟨fun v h => h, ?_, fun v hv => ⟨v, hv, by simp⟩⟩
    intro u w _ _ huw
    have : (prsPack R 0 : ℤ) ≤ 1 := by
      simp only [prsPack]; split_ifs with h
      · simp
      · have : R ≤ 1 := by
          have := le_two_pow_clog R; simp_all
        exact_mod_cast this
    have : (1 : ℤ) ≤ |u - w| := Int.one_le_abs (sub_ne_zero.2 huw)
    omega
  | succ j ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
    obtain ⟨a1, a2, a3⟩ := prs_step_arith R j hR (by omega)
    obtain ⟨m1, m2, m3⟩ := misRule_spec (prsStage U R n j) (prsRad R (j + 1)) n (prsPack R j) hℓ
      ih2 a1 (fun v hv => hn v (ih1 v hv))
    refine ⟨fun v hv => ih1 v (m1 v hv), fun u w hu hw huw => ?_, fun v hv => ?_⟩
    · have := m2 u w hu hw huw
      rw [← a2]; push_cast; omega
    · obtain ⟨s, hs, hvs⟩ := ih3 v hv
      obtain ⟨w, hw, hws⟩ := m3 s hs
      refine ⟨w, hw, ?_⟩
      calc |v - w| = |(v - s) + (s - w)| := by ring_nf
        _ ≤ |v - s| + |s - w| := abs_add_le _ _
        _ ≤ (prsCov R j : ℤ) + prsRad R (j + 1) := by rw [abs_sub_comm s w]; omega
        _ ≤ prsCov R (j + 1) := by exact_mod_cast a3

/-- **Lemma 3.4** (correctness). For labels `< n` on `U`, Algorithm 2 computes a `U`-limited
`(R, R - 1)`-ruling set. -/
theorem lemma_3_4 (U : (ℤ → ℕ) → ℤ → Prop) (R n : ℕ) (hR : 1 ≤ R) {ℓ : ℤ → ℕ}
    (hℓ : Injective ℓ) (hn : ∀ v, U ℓ v → ℓ v < n) :
    (∀ v, prsRule U R n ℓ v → U ℓ v) ∧ Packed (prsRule U R n ℓ) R ∧
      ∀ v, U ℓ v → ∃ s, prsRule U R n ℓ s ∧ |v - s| ≤ (R : ℤ) - 1 := by
  obtain ⟨s1, s2, s3⟩ := prsStage_spec U R n hR hℓ hn _ le_rfl
  have hpk : prsPack R (Nat.clog 2 R) = R := by simp [prsPack]
  have hcv : prsCov R (Nat.clog 2 R) = 3 * R - 3 := by simp [prsCov]
  rw [hpk] at s2
  rw [hcv] at s3
  obtain ⟨g1, g2, -, g4⟩ := gIter_spec (U ℓ) (prsStage U R n (Nat.clog 2 R) ℓ) ℓ hℓ R (3 * R)
    (3 * R - 3) 6 hR (by omega) (by omega) s2 (fun v hv => by
      obtain ⟨s, hs, h⟩ := s3 v hv; exact ⟨s, hs, h⟩)
    (Or.inl ⟨by omega, by omega⟩)
  refine ⟨fun v hv => ?_, g1, g4⟩
  rcases g2 v hv with h | h
  · exact s1 v h
  · exact h

/-- Locality of the stages. -/
lemma prsStage_isLocal (U : (ℤ → ℕ) → ℤ → Prop) {ρ : ℕ} (hU : IsLocal U ρ) (R n : ℕ)
    (hR : 1 ≤ R) (j : ℕ) (hj : j ≤ Nat.clog 2 R) :
    IsLocal (prsStage U R n j) (ρ + prsCov R j * (Nat.logStar n + 259)) := by
  induction j with
  | zero => exact hU.mono (by omega)
  | succ j ih =>
    obtain ⟨-, -, a3⟩ := prs_step_arith R j hR (by omega)
    refine (misRule_isLocal (ih (by omega)) _ n).mono ?_
    have := Nat.mul_le_mul_right (Nat.logStar n + 259) a3
    rw [add_mul] at this
    omega

/-- **Lemma 3.4** (complexity). Algorithm 2 runs in `3R (log* n + 267) = O(R log* n)` rounds (on
top of the `ρ` rounds needed to know `U`). -/
theorem lemma_3_4_isLocal (U : (ℤ → ℕ) → ℤ → Prop) {ρ : ℕ} (hU : IsLocal U ρ) (R n : ℕ)
    (hR : 1 ≤ R) : IsLocal (prsRule U R n) (ρ + 3 * R * (Nat.logStar n + 267)) := by
  have h := prsStage_isLocal U hU R n hR _ le_rfl
  have hcv : prsCov R (Nat.clog 2 R) = 3 * R - 3 := by simp [prsCov]
  rw [hcv] at h
  have hle : (3 * R - 3) * (Nat.logStar n + 259) ≤ 3 * R * (Nat.logStar n + 259) :=
    Nat.mul_le_mul_right _ (by omega)
  have h' : IsLocal (prsStage U R n (Nat.clog 2 R)) (ρ + 3 * R * (Nat.logStar n + 259)) :=
    h.mono (by omega)
  refine (gIterRule_isLocal (hU.mono (show ρ ≤ ρ + 3 * R * (Nat.logStar n + 259) by omega)) h'
    R (3 * R) 6).mono ?_
  ring_nf; omega

/-- Algorithm 2 runs on the unoriented line. -/
theorem prsRule_isEquivar (U : (ℤ → ℕ) → ℤ → Prop) (hU : IsEquivar U) (R n : ℕ) :
    IsEquivar (prsRule U R n) := by
  have : ∀ j, IsEquivar (prsStage U R n j) := by
    intro j; induction j with
    | zero => exact hU
    | succ j ih => exact misRule_isEquivar ih _ n
  exact gIterRule_isEquivar hU (this _) R (3 * R) 6

end Podc.RendezvousLabeledLine
