import Papers.PODC2021.WakeUpMatching.Lemma52

/-!
# The first bad round (deterministic part of the proof of Lemma 5.4)

Dani, Gupta, Hayes, Pettie, PODC 2021 (arXiv:2104.09096v2), Definition 5.3, Definition 5.5 and
the first half of the proof of Lemma 5.4.

For a sequence of partner states `s 0, s 1, …` produced by rounds of the protocol, `Δ(t)` is the
maximum residual degree (`maxRes`), round `t` is *good* if `Δ(t−1) r(t) < 1/2` (`Good`), and
`Z(v, t)` holds if `t` is good, `v` is unmatched after round `t` and `3 r(t) d(v, t) ≥ 1`
(`LostOpp`). If some round is bad, let `t` be the first bad round and `v` a vertex witnessing it;
then `Z(v, t')` holds for every `t' < t` with `3 r(t') > 2 r(t)` (`exists_first_bad`).
-/

set_option linter.unusedSectionVars false

namespace Podc.WakeUpMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `Δ(t)`: the maximum residual degree of the state `s` (`0` if every vertex is matched). -/
def maxRes (s : V → Option V) : ℕ := (univ.filter fun u => s u = none).sup fun u => #(resN G s u)

/-- Definition 5.3: round `t` is good if `Δ(t − 1) r(t) < 1/2`. -/
def Good (r : ℕ → ℝ) (s : ℕ → V → Option V) (t : ℕ) : Prop := (maxRes G (s (t - 1)) : ℝ) * r t < 1 / 2

/-- Definition 5.5: `Z(v, t) = 1` — round `t` is good, `v` is unmatched after it, and
`d(v, t) ≥ 1/(3 r(t))`. -/
def LostOpp (r : ℕ → ℝ) (s : ℕ → V → Option V) (v : V) (t : ℕ) : Prop :=
  Good G r s t ∧ s t v = none ∧ 1 ≤ 3 * r t * (#(resN G (s t) v) : ℝ)

/-- The rounds `t' ∈ [1, t − 1]` with `3 r(t') > 2 r(t)` (the interval `I` of the paper). -/
noncomputable def lostSet (r : ℕ → ℝ) (t : ℕ) : Finset ℕ := (Icc 1 (t - 1)).filter fun t' => 2 * r t < 3 * r t'

variable {G}

/-- States produced by rounds of the protocol. -/
def IsRoundSeq (s : ℕ → V → Option V) : Prop := ∀ t, ∃ ρ, s (t + 1) = round G (s t) ρ

theorem IsRoundSeq.mono {s : ℕ → V → Option V} (hs : IsRoundSeq (G := G) s) {t t' : ℕ}
    (h : t ≤ t') {v w : V} (hv : s t v = some w) : s t' v = some w := by
  induction h with
  | refl => exact hv
  | step _ ih =>
    obtain ⟨ρ, hρ⟩ := hs _
    rw [hρ]; exact round_mono ih

theorem IsRoundSeq.none_of_le {s : ℕ → V → Option V} (hs : IsRoundSeq (G := G) s) {t t' : ℕ}
    (h : t ≤ t') {v : V} (hv : s t' v = none) : s t v = none := by
  by_contra hne
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hne
  rw [hs.mono h hw] at hv; cases hv

theorem IsRoundSeq.resN_subset {s : ℕ → V → Option V} (hs : IsRoundSeq (G := G) s) {t t' : ℕ}
    (h : t ≤ t') (v : V) : resN G (s t') v ⊆ resN G (s t) v := by
  intro u hu
  simp only [resN, mem_filter, mem_univ, true_and] at hu ⊢
  exact ⟨hu.1, hs.none_of_le h hu.2⟩

/-- The maximum residual degree is attained. -/
theorem exists_maxRes (s : V → Option V) (h : 0 < maxRes G s) :
    ∃ v, s v = none ∧ #(resN G s v) = maxRes G s := by
  have hne : (univ.filter fun u => s u = none).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    simp [maxRes, hemp] at h
  obtain ⟨v, hv, hmax⟩ := exists_mem_eq_sup _ hne (fun u => #(resN G s u))
  exact ⟨v, (mem_filter.1 hv).2, hmax.symm⟩

/-- **The first bad round.** If some round `t ≥ 1` is bad, there is a first bad round `t₁ ≤ t`
(`t₁ ≥ 1`) and a vertex `v` with `Δ(t₁ − 1) = d(v, t₁ − 1)`, `d(v, t₁ − 1) r(t₁) ≥ 1/2`, and
`Z(v, t')` for every `t' ∈ I(t₁)`. -/
theorem exists_first_bad (r : ℕ → ℝ) {s : ℕ → V → Option V}
    (hs : IsRoundSeq (G := G) s) {t : ℕ} (hr : ∀ t' ≤ t, 0 < r t') (ht : 1 ≤ t)
    (hbad : ¬ Good G r s t) :
    ∃ t₁, 1 ≤ t₁ ∧ t₁ ≤ t ∧ ¬ Good G r s t₁ ∧ (∀ t' ∈ Icc 1 (t₁ - 1), Good G r s t') ∧
      ∃ v, 1 / 2 ≤ (#(resN G (s (t₁ - 1)) v) : ℝ) * r t₁ ∧
        ∀ t' ∈ lostSet r t₁, LostOpp G r s v t' := by
  classical
  have hex : ∃ t', 1 ≤ t' ∧ ¬ Good G r s t' := ⟨t, ht, hbad⟩
  set t₁ := Nat.find hex
  obtain ⟨h1, hb⟩ := Nat.find_spec hex
  have hmin : ∀ t' ∈ Icc 1 (t₁ - 1), Good G r s t' := by
    intro t' ht'
    rw [mem_Icc] at ht'
    by_contra hng
    have := Nat.find_min hex (show t' < t₁ by omega)
    exact this ⟨ht'.1, hng⟩
  -- the witness
  have hbad' : 1 / 2 ≤ (maxRes G (s (t₁ - 1)) : ℝ) * r t₁ := by
    unfold Good at hb; exact not_lt.1 hb
  have hpos : 0 < maxRes G (s (t₁ - 1)) := by
    by_contra h0
    have : maxRes G (s (t₁ - 1)) = 0 := by omega
    rw [this] at hbad'; simp at hbad'; linarith
  obtain ⟨v, hv, hdv⟩ := exists_maxRes (s (t₁ - 1)) hpos
  have ht₁ : t₁ ≤ t := Nat.find_min' hex ⟨ht, hbad⟩
  refine ⟨t₁, h1, ht₁, hb, hmin, v, by rw [hdv]; exact hbad', ?_⟩
  intro t' ht'
  simp only [lostSet, mem_filter, mem_Icc] at ht'
  obtain ⟨⟨ht'1, ht'2⟩, hlt⟩ := ht'
  refine ⟨hmin t' (mem_Icc.2 ⟨ht'1, ht'2⟩), hs.none_of_le ht'2 hv, ?_⟩
  -- `3 r(t') d(v, t') ≥ 3 r(t') d(v, t₁ − 1) ≥ 3 r(t') / (2 r(t₁)) > 1`
  have hd : (#(resN G (s (t₁ - 1)) v) : ℝ) ≤ #(resN G (s t') v) := by
    exact_mod_cast card_le_card (hs.resN_subset ht'2 v)
  have hrt := hr t₁ ht₁
  have hrt' := hr t' (by omega)
  have h2 : 1 / 2 ≤ (#(resN G (s (t₁ - 1)) v) : ℝ) * r t₁ := by rw [hdv]; exact hbad'
  nlinarith

end Podc.WakeUpMatching
