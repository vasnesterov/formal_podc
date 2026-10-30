import Papers.PODC2021.ContentionPredictions.LowerBounds

/-!
# Deterministic upper bounds with perfect advice (tightness of Theorems 3.4 and 3.5)

* Without collision detection, `b` bits of advice give a `⌈n / 2^b⌉`-round algorithm
  (`upper_noCD`): the advice names the residue of the smallest participant modulo `2^b`, and the
  `⌈n/2^b⌉` players with that residue transmit one per round. By `theorem_3_4_card` (`n ≤ 2^b t`)
  this is *exactly* optimal.
* With collision detection, `b ≤ ⌈log₂ n⌉` bits give a `⌈log₂ n⌉ - b + 1`-round algorithm
  (`upper_CD`): the advice names the block of size `2^{⌈log₂ n⌉ - b}` containing the smallest
  participant, then a binary search in that block (collision = descend left, silence = descend
  right), as described after Theorem 3.5 in the paper.
-/

namespace Podc.ContentionPredictions

open Finset

variable {n : ℕ}

/-- The smallest participant (`0` for the empty set, which never matters). -/
def minPart (P : Finset (Fin n)) : ℕ := if h : P.Nonempty then (P.min' h).val else 0

theorem minPart_mem {P : Finset (Fin n)} (hP : P.Nonempty) :
    ∃ m ∈ P, (m : ℕ) = minPart P := ⟨P.min' hP, P.min'_mem hP, by simp [minPart, hP]⟩

theorem minPart_lt {P : Finset (Fin n)} (hP : P.Nonempty) : minPart P < n := by
  obtain ⟨m, -, hm⟩ := minPart_mem hP; rw [← hm]; exact m.isLt

/-- A fixed encoding of `Fin (2^b)` by `b`-bit strings. -/
noncomputable def bitsEquiv (b : ℕ) : Fin (2 ^ b) ≃ Bits b :=
  (Fintype.equivFinOfCardEq (card_bits b)).symm

/-! ### No collision detection -/

/-- The algorithm of `upper_noCD`: player `v` transmits in round `r` iff `v ≡ a (mod 2^b)` and
`⌊v / 2^b⌋ = r`. -/
noncomputable def algNoCD (b : ℕ) : DetAlg n (Bits b) := fun a h v =>
  decide (((bitsEquiv b).symm a : ℕ) = (v : ℕ) % 2 ^ b ∧ (v : ℕ) / 2 ^ b = h.length)

/-- The advice of `upper_noCD`: the residue of the smallest participant modulo `2^b`. -/
noncomputable def adviceNoCD (b : ℕ) (P : Finset (Fin n)) : Bits b :=
  bitsEquiv b ⟨minPart P % 2 ^ b, Nat.mod_lt _ (by positivity)⟩

/-- **Upper bound matching Theorem 3.4** (paper, after Theorem 3.4): with `b` bits of advice and
no collision detection, contention resolution is solved deterministically within `⌈n / 2^b⌉`
rounds. Together with `theorem_3_4_card` this is exactly optimal. -/
theorem upper_noCD (b : ℕ) :
    SolvesIn false (algNoCD (n := n) b) (adviceNoCD b) ((n + 2 ^ b - 1) / 2 ^ b) := by
  intro P hP
  obtain ⟨m, hmP, hm⟩ := minPart_mem hP
  have hpos : 0 < 2 ^ b := by positivity
  refine ⟨(m : ℕ) / 2 ^ b, ?_, ?_⟩
  · have := m.isLt
    apply (Nat.le_div_iff_mul_le hpos).2
    have h1 := Nat.div_mul_le_self (m : ℕ) (2 ^ b)
    calc ((m : ℕ) / 2 ^ b + 1) * 2 ^ b = (m : ℕ) / 2 ^ b * 2 ^ b + 2 ^ b := by ring
      _ ≤ n + 2 ^ b - 1 := by omega
  · simp only [SolvedAt, transmitters, history_false, List.length_replicate, algNoCD,
      adviceNoCD, Equiv.symm_apply_apply, ← hm]
    rw [Finset.card_eq_one]
    refine ⟨m, ?_⟩
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton, decide_eq_true_eq]
    constructor
    · rintro ⟨-, h1, h2⟩
      apply Fin.ext
      rw [← Nat.div_add_mod (v : ℕ) (2 ^ b), ← Nat.div_add_mod (m : ℕ) (2 ^ b), h1, h2]
    · rintro rfl; exact ⟨hmP, rfl, rfl⟩

/-! ### Collision detection: binary search -/

/-- One binary-search step on the state `(lo, e)` (candidate interval `[lo, lo + 2^e)`, the left
half `[lo, lo + 2^{e-1})` transmitted): a collision keeps the left half, silence the right half. -/
def bsStep (s : ℕ × ℕ) (collision : Bool) : ℕ × ℕ :=
  if collision then (s.1, s.2 - 1) else (s.1 + 2 ^ (s.2 - 1), s.2 - 1)

/-- The algorithm of `upper_CD`: start with the block `[a 2^d, (a+1) 2^d)` named by the advice
`a`; in each round the participants in the left half of the current interval transmit (when the
interval is a single point, that point transmits). -/
noncomputable def algCD (b d : ℕ) : DetAlg n (Bits b) := fun a h v =>
  let s := h.foldl bsStep (((bitsEquiv b).symm a : ℕ) * 2 ^ d, d)
  decide (s.1 ≤ (v : ℕ) ∧ (v : ℕ) < s.1 + 2 ^ (s.2 - 1))

/-- The advice of `upper_CD`: the block of size `2^d` containing the smallest participant. -/
noncomputable def adviceCD (b d : ℕ) (P : Finset (Fin n)) : Bits b :=
  bitsEquiv b ⟨(minPart P / 2 ^ d) % 2 ^ b, Nat.mod_lt _ (by positivity)⟩

theorem algCD_invariant (b d : ℕ) (hn : n ≤ 2 ^ (b + d)) {P : Finset (Fin n)} (hP : P.Nonempty)
    (r : ℕ) (hr : r ≤ d) :
    (∃ r' < r, SolvedAt true (algCD b d) (adviceCD b d P) P r') ∨
      ((history true (algCD b d) (adviceCD b d P) P r).foldl bsStep
          (((bitsEquiv b).symm (adviceCD b d P) : ℕ) * 2 ^ d, d)).2 = d - r ∧
      ∃ p ∈ P, ((history true (algCD b d) (adviceCD b d P) P r).foldl bsStep
          (((bitsEquiv b).symm (adviceCD b d P) : ℕ) * 2 ^ d, d)).1 ≤ (p : ℕ) ∧
        (p : ℕ) < ((history true (algCD b d) (adviceCD b d P) P r).foldl bsStep
          (((bitsEquiv b).symm (adviceCD b d P) : ℕ) * 2 ^ d, d)).1 + 2 ^ (d - r) := by
  induction r with
  | zero =>
    right
    obtain ⟨m, hmP, hm⟩ := minPart_mem hP
    have hmn : (m : ℕ) < 2 ^ b * 2 ^ d := by rw [← pow_add]; exact lt_of_lt_of_le m.isLt hn
    have hblk : (m : ℕ) / 2 ^ d < 2 ^ b := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; exact hmn
    simp only [history, List.foldl_nil, adviceCD, Equiv.symm_apply_apply, ← hm,
      Nat.mod_eq_of_lt hblk, Nat.sub_zero, true_and]
    refine ⟨m, hmP, Nat.div_mul_le_self _ _, ?_⟩
    have := Nat.lt_div_mul_add (a := (m : ℕ)) (b := 2 ^ d) (by positivity)
    linarith
  | succ r ih =>
    rcases ih (by omega) with ⟨r', hr', hs⟩ | ⟨he, p, hpP, hp1, hp2⟩
    · exact Or.inl ⟨r', by omega, hs⟩
    by_cases hsolved : SolvedAt true (algCD b d) (adviceCD b d P) P r
    · exact Or.inl ⟨r, by omega, hsolved⟩
    right
    set a := adviceCD b d P
    set H := history true (algCD b d) a P r
    set s := H.foldl bsStep (((bitsEquiv b).symm a : ℕ) * 2 ^ d, d) with hsdef
    set T : Finset (Fin n) :=
      P.filter (fun v : Fin n => s.1 ≤ (v : ℕ) ∧ (v : ℕ) < s.1 + 2 ^ (s.2 - 1)) with hTdef
    have hT : transmitters (algCD b d) a H P = T := by
      ext v; simp [transmitters, algCD, hsdef, hTdef]
    have hhist : history true (algCD b d) a P (r + 1) = H ++ [feedback true T] := by
      simp only [history, ← hT]; rfl
    rw [hhist, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hsdef]
    have hsolved' : T.card ≠ 1 := by rw [← hT]; exact hsolved
    have he1 : 1 ≤ s.2 := by rw [he]; omega
    have hpow : 2 ^ (d - r) = 2 ^ (s.2 - 1) + 2 ^ (s.2 - 1) := by
      rw [show d - r = (s.2 - 1) + 1 by omega, pow_succ]; ring
    rcases Nat.lt_or_ge T.card 2 with hlt | hge
    · -- silence: no participant in the left half
      have h0 : T.card = 0 := by omega
      have hfb : feedback true T = false := by simp [feedback]; omega
      rw [hfb]
      simp only [bsStep, Bool.false_eq_true, ↓reduceIte]
      refine ⟨by omega, p, hpP, ?_, ?_⟩
      · by_contra hlt'
        rw [Finset.card_eq_zero, hTdef, Finset.filter_eq_empty_iff] at h0
        exact h0 hpP ⟨hp1, by omega⟩
      · rw [show d - (r + 1) = s.2 - 1 by omega]; omega
    · -- collision: at least two participants in the left half
      have hfb : feedback true T = true := by simp [feedback]; omega
      rw [hfb]
      simp only [bsStep, ↓reduceIte]
      obtain ⟨q, hq⟩ : T.Nonempty := by rw [← Finset.card_pos]; omega
      simp only [hTdef, Finset.mem_filter] at hq
      refine ⟨by omega, q, hq.1, hq.2.1, ?_⟩
      rw [show d - (r + 1) = s.2 - 1 by omega]; exact hq.2.2

/-- **Upper bound matching Theorem 3.5** (paper, after Theorem 3.5): if `n ≤ 2^{b+d}`, then with
`b` bits of advice and collision detection, contention resolution is solved deterministically
within `d + 1` rounds. -/
theorem upper_CD (b d : ℕ) (hn : n ≤ 2 ^ (b + d)) :
    SolvesIn true (algCD (n := n) b d) (adviceCD b d) (d + 1) := by
  intro P hP
  rcases algCD_invariant b d hn hP d le_rfl with ⟨r', hr', hs⟩ | ⟨he, p, hpP, hp1, hp2⟩
  · exact ⟨r', by omega, hs⟩
  refine ⟨d, by omega, ?_⟩
  simp only [Nat.sub_self, pow_zero] at he hp2
  simp only [SolvedAt, transmitters, algCD, he, Nat.zero_sub, pow_zero]
  rw [Finset.card_eq_one]
  refine ⟨p, ?_⟩
  ext v
  simp only [Finset.mem_filter, Finset.mem_singleton, decide_eq_true_eq]
  constructor
  · rintro ⟨-, h1, h2⟩; apply Fin.ext; omega
  · rintro rfl; exact ⟨hpP, hp1, hp2⟩

/-- Upper bound matching Theorem 3.5 in the paper's form: for `b ≤ ⌈log₂ n⌉`, contention
resolution with collision detection and `b` bits of advice is solved deterministically within
`⌈log₂ n⌉ - b + 1` rounds. -/
theorem upper_CD_clog (b : ℕ) (hb : b ≤ Nat.clog 2 n) :
    ∃ (alg : DetAlg n (Bits b)) (f : Finset (Fin n) → Bits b),
      SolvesIn true alg f (Nat.clog 2 n - b + 1) :=
  ⟨_, _, upper_CD b (Nat.clog 2 n - b) (by
    rw [Nat.add_sub_cancel' hb]; exact Nat.le_pow_clog (by norm_num) n)⟩

end Podc.ContentionPredictions
