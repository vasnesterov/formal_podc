import Papers.PODC2011.TimestampSpace.Alg4Inv3

/-!
# Space complexity of Algorithm 4 (Lemma 6.5)

In every execution with at most `M` `getTS` invocations, every base-object access touches only
registers `R[1..⌈2√M⌉]` (the sentinel `R[myrnd + 1]` included), and registers beyond
`⌈2√M⌉ - 1` are never written.

Proof: if `R[K] ≠ ⊥` (`K ≥ 1`) then the phase is `Φ ≥ K`; phases `1..Φ-1` are complete and
contain `≥ ϕ` invalidation writes each, the current one contains the write to `R[Φ]` if
`Φ = K`; and `#invalidation writes + Φ ≤ 2M` (charging, with the phase starters' unused
credits). Hence `K² + K + 2 ≤ 4M`, so `K < 2√M`. Every access has index `1` or index `j` with
`R[j-1] ≠ ⊥`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp.Alg4

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-- The ghost counter of `getTS` invocations. -/
lemma ghostOf_nget {α : List (Label P TS)} {C : ACfg P} (h : (alg4 (P := P)).run α = some C) :
    (ghostOf α).nget = totalGetTS α := by
  induction α using List.reverseRecOn generalizing C with
  | nil => rfl
  | append_singleton α ℓ ih =>
    obtain ⟨C₀, h₀, hs⟩ := run_append_singleton h
    rw [ghostOf_append h₀ hs]
    have ih' := ih h₀
    unfold totalGetTS at ih' ⊢
    rw [List.countP_append, ← ih', List.countP_singleton]
    cases ℓ with
    | inv q o => cases o <;> simp [gstep]
    | ret q r => simp [gstep]
    | tau q =>
      simp only [gstep]
      split
      · split <;> simp
      · simp
      · simp
      · split_ifs <;> simp_all
      · simp
      · simp

/-- **Counting** (Claims 6.8–6.13 combined): if `R[K] ≠ ⊥` then `K² + K + 2 ≤ 4 · #getTS`. -/
theorem sq_le_of_written {α : List (Label P TS)} {C : ACfg P}
    (h : (alg4 (P := P)).run α = some C) {K : ℕ} (hK : 1 ≤ K) (hR : Rg C K ≠ none) :
    K * K + K + 2 ≤ 4 * totalGetTS α := by
  have h2 := inv2_of_run h
  have h3 := inv3_of_run h
  rw [← ghostOf_nget h]
  set G := ghostOf α
  have hph := h2.ph_ge K hR
  have hc := h3.count
  have hcr := h3.credit
  rcases eq_or_lt_of_le hph with he | hlt
  · -- the current phase is `K`: `R[K]` was written in it
    have hw : K ∈ G.wc := (h3.wc_iff K).2 (by have := h2.wph (by rw [← he]; exact hR); rwa [← he] at this)
    have hcard : 1 ≤ G.wc.card := Finset.card_pos.2 ⟨K, hw⟩
    rw [← he] at hc hcr
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hc
    nlinarith
  · obtain ⟨d, hd⟩ : ∃ d, G.ph = K + 1 + d := ⟨G.ph - (K + 1), by omega⟩
    rw [hd] at hc hcr
    simp only [show K + 1 + d - 1 = K + d by omega] at hc
    nlinarith

lemma lt_two_sqrt {K M : ℕ} (h : K * K + K + 2 ≤ 4 * M) : (K : ℝ) < 2 * Real.sqrt M := by
  have h0 : (0 : ℝ) ≤ K / 2 := by positivity
  have : (K : ℝ) / 2 < Real.sqrt M := by
    rw [Real.lt_sqrt h0]
    have : (K : ℝ) * K < 4 * M := by exact_mod_cast (show K * K < 4 * M by omega)
    nlinarith
  linarith

/-- Registers with index `≥ ⌈2√M⌉` are never written. -/
theorem alg4_written_lt {M : ℕ} {α : List (Label P TS)} {C : ACfg P}
    (h : (alg4 (P := P)).run α = some C) (hM : totalGetTS α ≤ M) {j : ℕ}
    (hj : Rg C j ≠ none) : j < ⌈2 * Real.sqrt M⌉₊ := by
  have h1 := inv1_of_run h
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with rfl | h0
    · exact absurd h1.mem.r0 hj
    · exact h0
  have := sq_le_of_written h hj1 hj
  exact Nat.lt_ceil.2 (lt_two_sqrt (by omega))

/-- Every access is to index `1` or to an index `j` with `R[j-1] ≠ ⊥`. -/
lemma acc_idx {α : List (Label P TS)} {C : ACfg P} (h1 : Inv1 α C) {p : P} {i : Unit}
    {o : MOp P} {k : (memObj P).Resp → Loc P}
    (hact : (alg4 (P := P)).act p (C.loc p) = .access i o k) :
    1 ≤ o.idx ∧ (o.idx = 1 ∨ Rg C (o.idx - 1) ≠ none) := by
  have hpi := h1.pi p
  change act p (C.loc p) = _ at hact
  unfold act at hact
  generalize C.loc p = l at hpi hact
  obtain ⟨c, pc⟩ := l
  simp only [PI1] at hpi
  cases pc with
  | idle => simp at hact
  | done r => simp at hact
  | wh j v =>
    simp only [Action.access.injEq] at hact
    obtain ⟨-, ho, -⟩ := hact
    cases eq_of_heq ho
    simp only [MOp.idx]
    refine ⟨hpi.1, ?_⟩
    rcases Nat.lt_or_ge j 2 with h3 | h3
    · left; omega
    · right; exact hpi.2 h3
  | loop k' i' v s =>
    obtain ⟨hi1, hik, hk⟩ := hpi
    have hprev : ∀ j, 1 ≤ j → j ≤ k' → j = 1 ∨ Rg C (j - 1) ≠ none := by
      intro j h3 h4
      rcases Nat.lt_or_ge j 2 with h5 | h5
      · left; omega
      · right; exact h1.mem.contig k' (j - 1) hk (by omega) (by omega)
    cases s <;> simp only [Action.access.injEq] at hact <;> obtain ⟨-, ho, -⟩ := hact <;>
      cases eq_of_heq ho <;> simp only [MOp.idx]
    · exact ⟨by omega, Or.inr (by simpa using hk)⟩
    all_goals exact ⟨hi1, hprev i' hi1 (by omega)⟩
  | scan k' =>
    simp only [Action.access.injEq] at hact
    obtain ⟨-, ho, -⟩ := hact
    cases eq_of_heq ho
    simp only [MOp.idx]
    refine ⟨by omega, ?_⟩
    rcases Nat.eq_zero_or_pos k' with h3 | h3
    · left; omega
    · right; simpa using hpi h3
  | fin k' w =>
    simp only [Action.access.injEq] at hact
    obtain ⟨-, ho, -⟩ := hact
    cases eq_of_heq ho
    simp only [MOp.idx]
    refine ⟨by omega, ?_⟩
    rcases Nat.eq_zero_or_pos k' with h3 | h3
    · left; omega
    · right; simpa using hpi.1 h3

/-- A process about to access memory has a pending `getTS`, so `#getTS ≥ 1`. -/
lemma totalGetTS_pos {α : List (Label P TS)} {C : ACfg P} (h : (alg4 (P := P)).run α = some C)
    {p : P} (hp : C.pend p ≠ none) {i : Unit} {o : MOp P} {k : (memObj P).Resp → Loc P}
    (hact : (alg4 (P := P)).act p (C.loc p) = .access i o k) : 1 ≤ totalGetTS α := by
  have h1 := inv1_of_run h
  obtain ⟨op, hop⟩ := Option.ne_none_iff_exists'.1 hp
  have hg : op = .getTS := by
    cases op with
    | getTS => rfl
    | compare a b =>
      have := h1.cmp p a b hop
      change act p (C.loc p) = _ at hact
      unfold act at hact
      rw [this] at hact
      simp at hact
  subst hg
  have hl := Impl.run_pend _ h hop
  have hmem : TSOp.getTS ∈ opsOf α p := List.mem_of_getLast? hl
  simp only [opsOf, List.mem_filterMap] at hmem
  obtain ⟨ℓ, hℓ, hinv⟩ := hmem
  apply List.countP_pos_iff.2
  refine ⟨ℓ, hℓ, ?_⟩
  cases ℓ with
  | inv q o' =>
    simp only [Label.invOf_inv] at hinv
    split_ifs at hinv
    simp only [Option.some.injEq] at hinv
    subst hinv; rfl
  | ret q r => simp at hinv
  | tau q => simp at hinv

/-- **Lemma 6.5** (space): in every execution with at most `M` `getTS` invocations, every
base-object access of every process touches only registers `R[1..⌈2√M⌉]` (for a scan:
`R[1..o.idx]`). -/
theorem alg4_space {M : ℕ} {α : List (Label P TS)} {C : ACfg P}
    (h : (alg4 (P := P)).run α = some C) (hM : totalGetTS α ≤ M) {p : P}
    (hp : C.pend p ≠ none) {i : Unit} {o : MOp P} {k : (memObj P).Resp → Loc P}
    (hact : (alg4 (P := P)).act p (C.loc p) = .access i o k) :
    1 ≤ o.idx ∧ o.idx ≤ ⌈2 * Real.sqrt M⌉₊ := by
  have h1 := inv1_of_run h
  obtain ⟨hi1, hi2⟩ := acc_idx h1 hact
  refine ⟨hi1, ?_⟩
  rcases hi2 with hi2 | hi2
  · rw [hi2]
    have hpos := totalGetTS_pos h hp hact
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    rw [Nat.ceil_eq_zero] at h0
    have : (1 : ℝ) ≤ M := by exact_mod_cast (hpos.trans hM)
    have : (1 : ℝ) ≤ Real.sqrt M := by rw [Real.one_le_sqrt]; exact this
    linarith
  · have := alg4_written_lt h hM hi2
    omega

end Cslib.SharedMemory.Timestamp.Alg4
