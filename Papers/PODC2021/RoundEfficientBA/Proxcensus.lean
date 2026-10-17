import Mathlib
import Podc.Agreement.Specs

/-!
# Proxcensus and the extraction step (Definition 2.2, Section 3.4, Theorem 3.7)

Fitzi, Liu-Zhang, Loss, *A New Way to Achieve Round-Efficient Byzantine Agreement*, PODC 2021.

* `maxGrade s = ⌊(s-1)/2⌋` and `ProxCons s a b`: the consistency clauses of Definition 2.2 for an
  ordered pair of outputs `a = (yᵢ, gᵢ)`, `b = (yⱼ, gⱼ)`; `IsProx s x H out`: the honest outputs
  `out` (honest set `H`, inputs `x`) satisfy `s`-slot Proxcensus (grades in `[0, G]`, validity,
  consistency).
* `slotPos s (b, g)`: the slot (`0, …, s-1`) of a binary output, as in Figure 1 / Figure 3.
* `extract s (b, g) c`: the extraction function `f` of Section 3.4.
* `extract_iff`: `f(b, g, c) = 1 ↔ c ≤ slotPos s (b, g)` (the "cut" picture of Figure 3).
* `ProxCons.slotPos_le`: consistent binary outputs lie in adjacent slots.
* `badCoin_subsingleton`: at most one coin value separates the honest parties.
* `iter_validity`, `iter_error_le` (**Theorem 3.7**): one Proxcensus followed by a uniform coin in
  `[1, s-1]` and extraction is a binary BA with error probability at most `1/(s-1)`, also when the
  adversary corrupts further parties after seeing the coin.
-/

namespace RoundEfficientBA

/-! ### Definition 2.2 -/

-- The maximal grade `G = ⌊(s-1)/2⌋` of `s`-slot Proxcensus.
export Cslib.Byzantine.Problem.Proxcensus (maxGrade)

/-- The consistency conditions of Definition 2.2 for the ordered pair of outputs
`a = (yᵢ, gᵢ)`, `b = (yⱼ, gⱼ)`: `|gᵢ - gⱼ| ≤ 1`, `min(gᵢ, gⱼ) ≥ 1 → yᵢ = yⱼ`, and, for even `s`,
`gᵢ > 0 → yᵢ = yⱼ`. (Definition 2.2 quantifies over *any two* honest parties, so the last clause is
required for both orders.) -/
abbrev ProxCons {D : Type*} (s : ℕ) (a b : D × ℕ) : Prop := Cslib.Byzantine.Problem.Proxcensus.Consistent s a b

/-- **Definition 2.2** (`s`-slot Proxcensus) as a property of one run: the honest parties `H`
with inputs `x` output `out p = (yₚ, gₚ)` with `gₚ ∈ [0, G]`, validity and consistency hold
(fields `grade_le`, `validity`, `consistency`). (Termination is a property of the protocol, not of
the output relation.) -/
abbrev IsProx {P D : Type*} (s : ℕ) (x : P → D) (H : Set P) (out : P → D × ℕ) : Prop :=
  Cslib.Byzantine.Problem.Proxcensus s x H out

/-! ### Slots of binary outputs and the extraction function -/

/-- The slot `0, …, s-1` of a binary output `(b, g)` (Figure 1): for odd `s` the slots are
`(0,G), …, (0,1), (⊥,0), (1,1), …, (1,G)` (a grade-0 output sits in the middle slot whatever its
value), for even `s` they are `(0,G), …, (0,0), (1,0), …, (1,G)`. -/
def slotPos (s : ℕ) (o : Bool × ℕ) : ℕ :=
  if s % 2 = 1 then
    (if o.2 = 0 then maxGrade s else if o.1 then maxGrade s + o.2 else maxGrade s - o.2)
  else (if o.1 then maxGrade s + 1 + o.2 else maxGrade s - o.2)

/-- The extraction function of Section 3.4:
`f(b, g, c) = 1` iff `(b = 1 ∧ c ≤ g + G + 1 - r) ∨ (b = 0 ∧ c ≤ G - g)`, `r = s mod 2`. -/
def extract (s : ℕ) (o : Bool × ℕ) (c : ℕ) : Bool :=
  decide ((o.1 = true ∧ c ≤ o.2 + maxGrade s + 1 - s % 2) ∨ (o.1 = false ∧ c ≤ maxGrade s - o.2))

/-- The extraction function is the cut of Figure 3: a party outputs `1` iff its slot is at or to the
right of the coin. -/
lemma extract_iff (s : ℕ) (o : Bool × ℕ) (c : ℕ) (hg : o.2 ≤ maxGrade s) :
    extract s o c = true ↔ c ≤ slotPos s o := by
  obtain ⟨b, g⟩ := o
  simp only at hg
  unfold extract slotPos
  have := Nat.mod_two_eq_zero_or_one s
  cases b <;> rcases this with h | h <;> simp [h] <;> (try split_ifs) <;> omega

lemma slotPos_le (s : ℕ) (hs : 1 ≤ s) (o : Bool × ℕ) (hg : o.2 ≤ maxGrade s) :
    slotPos s o ≤ s - 1 := by
  obtain ⟨b, g⟩ := o
  simp only at hg
  unfold slotPos maxGrade at *
  have := Nat.mod_two_eq_zero_or_one s
  have h2 := Nat.div_add_mod s 2
  cases b <;> rcases this with h | h <;> simp [h] <;> (try split_ifs) <;> omega

/-- Consistent binary outputs lie in the same or in adjacent slots (the brace (a) of Figure 1). -/
lemma ProxCons.slotPos_le {s : ℕ} {a b : Bool × ℕ} (hab : ProxCons s a b) (hba : ProxCons s b a)
    (ha : a.2 ≤ maxGrade s) (hb : b.2 ≤ maxGrade s) : slotPos s a ≤ slotPos s b + 1 := by
  obtain ⟨y, g⟩ := a
  obtain ⟨y', g'⟩ := b
  obtain ⟨h1, h2, h3, h4⟩ := hab
  obtain ⟨-, -, -, h4'⟩ := hba
  simp only at *
  unfold slotPos
  have := Nat.mod_two_eq_zero_or_one s
  rcases this with h | h
  · simp only [h, zero_ne_one, ite_false]
    have h4 := h4 h; have h4' := h4' h
    cases y <;> cases y' <;> simp at h3 h4 h4' ⊢ <;> omega
  · simp only [h, ite_true]
    cases y <;> cases y' <;> simp at h3 ⊢ <;> split_ifs <;> omega

/-! ### Theorem 3.7 -/

section Iter

variable {P : Type*}

/-- The coin `c` *separates* honest parties of `H` with Proxcensus outputs `out`. -/
def BadCoin (s : ℕ) (H : Set P) (out : P → Bool × ℕ) (c : ℕ) : Prop :=
  ∃ p ∈ H, ∃ q ∈ H, extract s (out p) c ≠ extract s (out q) c

/-- Core of the consistency part of Theorem 3.7: if the honest outputs are pairwise consistent,
at most one coin value separates them. -/
theorem badCoin_subsingleton {s : ℕ} {H : Set P} {out : P → Bool × ℕ}
    (hg : ∀ p ∈ H, (out p).2 ≤ maxGrade s)
    (hc : ∀ p ∈ H, ∀ q ∈ H, ProxCons s (out p) (out q)) :
    {c | BadCoin s H out c}.Subsingleton := by
  -- a bad coin `c` is `slotPos p = slotPos q + 1 = c` for some honest `p`, `q`
  have key : ∀ c, BadCoin s H out c →
      ∃ p ∈ H, ∃ q ∈ H, slotPos s (out p) = c ∧ slotPos s (out q) + 1 = c := by
    rintro c ⟨p, hp, q, hq, hne⟩
    have ep := extract_iff s (out p) c (hg p hp)
    have eq := extract_iff s (out q) c (hg q hq)
    have l1 := ProxCons.slotPos_le (hc p hp q hq) (hc q hq p hp) (hg p hp) (hg q hq)
    have l2 := ProxCons.slotPos_le (hc q hq p hp) (hc p hp q hq) (hg q hq) (hg p hp)
    cases hx : extract s (out p) c <;> cases hy : extract s (out q) c <;> simp_all
    · exact ⟨q, hq, p, hp, by omega, by omega⟩
    · exact ⟨p, hp, q, hq, by omega, by omega⟩
  intro c hc' c' hc''
  obtain ⟨p, hp, q, hq, h1, h2⟩ := key c hc'
  obtain ⟨p', hp', q', hq', h1', h2'⟩ := key c' hc''
  have a := ProxCons.slotPos_le (hc p hp q' hq') (hc q' hq' p hp) (hg p hp) (hg q' hq')
  have b := ProxCons.slotPos_le (hc p' hp' q hq) (hc q hq p' hp') (hg p' hp') (hg q hq)
  omega

/-- **Theorem 3.7, validity.** If all honest parties input `b` and the outputs of `Prox_s` satisfy
validity, every honest party outputs `b` for every coin `c ∈ [1, s-1]`. -/
theorem iter_validity {s : ℕ} {x : P → Bool} {H : Set P} {out : P → Bool × ℕ}
    (hP : IsProx s x H out) (b : Bool) (hb : ∀ p ∈ H, x p = b) (c : ℕ) (hc1 : 1 ≤ c)
    (hc2 : c ≤ s - 1) : ∀ p ∈ H, extract s (out p) c = b := by
  intro p hp
  rw [hP.validity b hb p hp]
  unfold extract maxGrade at *
  have := Nat.mod_two_eq_zero_or_one s
  have h2 := Nat.div_add_mod s 2
  cases b <;> rcases this with h | h <;> simp [h] <;> omega

/-- Bad-coin bound for coin-dependent outputs: the honest set `H c` and the outputs `out c` may
depend on the coin `c + 1` (e.g. when the adversary sees the coin before the last round), but if
all outputs for all coins are pairwise consistent, the separating probability is `≤ 1/N`. -/
theorem iter_error_le_family {s N : ℕ} [NeZero N] {ι : Type*} (H : Fin N → Set ι)
    (out : Fin N → ι → Bool × ℕ) (hg : ∀ c, ∀ p ∈ H c, (out c p).2 ≤ maxGrade s)
    (hc : ∀ c c', ∀ p ∈ H c, ∀ q ∈ H c', ProxCons s (out c p) (out c' q)) :
    (PMF.uniformOfFintype (Fin N)).toOuterMeasure
        {c | ∃ p ∈ H c, ∃ q ∈ H c, extract s (out c p) (c + 1) ≠ extract s (out c q) (c + 1)}
      ≤ 1 / N := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, Fintype.card_fin, one_div]
  rw [ENNReal.div_eq_inv_mul]
  -- the whole family of (coin, party) outputs is pairwise consistent
  have hsub := badCoin_subsingleton (P := Fin N × ι) (s := s) (H := {cp | cp.2 ∈ H cp.1})
    (out := fun cp => out cp.1 cp.2) (fun cp hcp => hg cp.1 cp.2 hcp)
    (fun cp hcp cq hcq => hc cp.1 cq.1 cp.2 hcp cq.2 hcq)
  have h1 : (Finset.univ.filter fun c : Fin N =>
      ∃ p ∈ H c, ∃ q ∈ H c, extract s (out c p) (c + 1) ≠ extract s (out c q) (c + 1)).card
        ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    obtain ⟨p, hp, q, hq, h⟩ := hi
    obtain ⟨p', hp', q', hq', h'⟩ := hj
    have := hsub (show ((i : ℕ) + 1) ∈ {c | BadCoin s {cp : Fin N × ι | cp.2 ∈ H cp.1}
        (fun cp => out cp.1 cp.2) c} from ⟨(i, p), hp, (i, q), hq, h⟩)
      (show ((j : ℕ) + 1) ∈ {c | BadCoin s {cp : Fin N × ι | cp.2 ∈ H cp.1}
        (fun cp => out cp.1 cp.2) c} from ⟨(j, p'), hp', (j, q'), hq', h'⟩)
    exact Fin.ext (by omega)
  have h' : (Fintype.card {c : Fin N | ∃ p ∈ H c, ∃ q ∈ H c,
        extract s (out c p) (c + 1) ≠ extract s (out c q) (c + 1)} : ENNReal) ≤ 1 := by
    rw [Fintype.card_ofFinset]
    exact_mod_cast h1
  calc _ ≤ ((N : ℕ) : ENNReal)⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

/-- **Theorem 3.7, error probability.** Let the honest Proxcensus outputs (honest set `H`) be
consistent, and let the coin be uniform in `[1, s-1]` (here `c = i + 1` for `i` uniform in
`Fin N`, `N = s - 1`). Even if the adversary, after seeing the coin, corrupts further parties
(the honest set becomes `Hc i ⊆ H`), the probability that two honest parties output different
bits is at most `1/(s-1)`. -/
theorem iter_error_le {s N : ℕ} [NeZero N] (_hN : N = s - 1) {H : Set P} {out : P → Bool × ℕ}
    (hg : ∀ p ∈ H, (out p).2 ≤ maxGrade s)
    (hc : ∀ p ∈ H, ∀ q ∈ H, ProxCons s (out p) (out q))
    (Hc : Fin N → Set P) (hHc : ∀ i, Hc i ⊆ H) :
    (PMF.uniformOfFintype (Fin N)).toOuterMeasure
        {i | ∃ p ∈ Hc i, ∃ q ∈ Hc i, extract s (out p) (i + 1) ≠ extract s (out q) (i + 1)}
      ≤ 1 / N :=
  iter_error_le_family Hc (fun _ => out) (fun c p hp => hg p (hHc c hp))
    (fun c c' p hp q hq => hc p (hHc c hp) q (hHc c' hq))

end Iter

end RoundEfficientBA
