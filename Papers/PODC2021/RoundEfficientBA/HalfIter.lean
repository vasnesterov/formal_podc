import Papers.PODC2021.RoundEfficientBA.Half

/-!
# One iteration for `t < n/2` with the coin in parallel to the last round (Corollary 3.8)

In the proof of Corollary 3.8 (`t < n/2`) one iteration `Π^5_iter` takes 3 rounds: the coin flip is
run *in parallel to the third round* of `Prox_5`, justified by "after round 2 of `Prox_5`, the
slot-pair where the honest parties lie is already fixed"; the iteration is claimed to fail with
probability `1/4`.

The coin of round `r` is revealed during round `r` (its threshold-signature shares are sent in that
round), so a rushing adversary may choose its round-`r` messages — and, being adaptive and strongly
rushing, its round-`r` corruptions — depending on the coin. We model an adversary strategy as a
family `σ c` of adversaries indexed by the coin, which agree before round `r` (`PrefixAgree`).

* `coin_parallel_static`: if the corruption times do not depend on the coin (in particular for a
  static adversary), the failure probability is at most `1/(2r-2)` (`1/4` for `Prox_5`), and
  validity holds for every coin. This is the paper's claim, for non-adaptive corruption.
* `coin_parallel_adaptive_attack`: for `n = 5`, `t = 2`, `Prox_5` and the uniform coin in `[1,4]`,
  an adversary that corrupts one more party in round 3 *after seeing the coin* makes the honest
  parties disagree with probability `1/2`. So the paper's claim (and Corollary 3.8 for `t < n/2`
  with `κ = 2`, which promises failure probability `2^{-2}`) fails against the adaptive strongly
  rushing adversary of the paper's model.
-/

namespace RoundEfficientBA.Half

variable {P D : Type*} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
variable {n t : ℕ} {x : P → D}

/-- Two adversaries that behave identically before round `r`: the same corruptions before round
`r` and the same messages in the rounds `< r`. -/
structure PrefixAgree (r : ℕ) (A B : Adv P D) : Prop where
  cr_lt : ∀ q, A.cr q < r ↔ B.cr q < r
  cr_eq : ∀ q, A.cr q < r → A.cr q = B.cr q
  sh1 : A.sh1 = B.sh1
  wsh : A.wsh = B.wsh
  sig : ∀ k < r, A.sig k = B.sig k
  om : ∀ k < r, A.om k = B.om k

section Agree

variable {r : ℕ} {A B : Adv P D}

/-- Before round `r` only the comparisons `k < A.cr q` with `k < r` matter. -/
lemma PrefixAgree.lt_cr (h : PrefixAgree r A B) {k : ℕ} (hk : k < r) (q : P) :
    k < A.cr q ↔ k < B.cr q := by
  by_cases hq : A.cr q < r
  · rw [h.cr_eq q hq]
  · have hq' : ¬ B.cr q < r := fun h' => hq ((h.cr_lt q).2 h')
    omega

lemma PrefixAgree.S1_eq (h : PrefixAgree r A B) (hr : 1 < r) (i : P) :
    S1 n t x A i = S1 n t x B i := by
  have e : ∀ v, (Finset.univ.filter fun q => (1 < A.cr q ∧ x q = v) ∨ (A.cr q ≤ 1 ∧ v ∈ A.sh1 q i))
      = Finset.univ.filter fun q => (1 < B.cr q ∧ x q = v) ∨ (B.cr q ≤ 1 ∧ v ∈ B.sh1 q i) := by
    intro v; ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h.lt_cr hr q, h.sh1, show A.cr q ≤ 1 ↔ B.cr q ≤ 1 by
      have := h.lt_cr hr q; omega]
  unfold S1
  simp only [e]

lemma PrefixAgree.signsOm_eq (h : PrefixAgree r A B) (hr : 1 < r) (q : P) :
    SignsOm n t x A q ↔ SignsOm n t x B q := by
  unfold SignsOm; rw [h.S1_eq hr]

/-- Agreeing adversaries produce the same sets before round `r`. -/
lemma PrefixAgree.S_eq (h : PrefixAgree r A B) : ∀ k < r, ∀ q, S n t x A k q = S n t x B k q := by
  intro k hk
  induction k with
  | zero => intro q; rfl
  | succ k ih =>
    intro q
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact h.S1_eq hk q
    · rw [S_succ k hk0, S_succ k hk0]
      have e1 : (Finset.univ.filter fun q => k + 1 < A.cr q) =
          Finset.univ.filter fun q => k + 1 < B.cr q := by
        ext q; simp [h.lt_cr hk q]
      have e2 : (Finset.univ.filter fun q => A.cr q ≤ k + 1) =
          Finset.univ.filter fun q => B.cr q ≤ k + 1 := by
        ext q; have := h.lt_cr hk q; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [e1, e2, h.sig (k + 1) hk]
      congr 1
      exact Finset.biUnion_congr rfl (fun q _ => ih (by omega) q)

lemma PrefixAgree.Om_eq (h : PrefixAgree r A B) :
    ∀ k < r, ∀ q, Om n t x A k q = Om n t x B k q := by
  intro k hk
  induction k with
  | zero => intro q; rfl
  | succ k ih =>
    intro q
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · rfl
      · change Om2 n t x A q = Om2 n t x B q
        unfold Om2
        congr 1
        congr 2
        ext q'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [h.lt_cr hk q', h.signsOm_eq (by omega) q', h.wsh, show A.cr q' ≤ 2 ↔ B.cr q' ≤ 2 by
          have := h.lt_cr hk q'; omega]
    · rw [Om_succ k hk2, Om_succ k hk2]
      have e1 : (Finset.univ.filter fun q => k + 1 < A.cr q) =
          Finset.univ.filter fun q => k + 1 < B.cr q := by
        ext q; simp [h.lt_cr hk q]
      have e2 : (Finset.univ.filter fun q => A.cr q ≤ k + 1) =
          Finset.univ.filter fun q => B.cr q ≤ k + 1 := by
        ext q; have := h.lt_cr hk q; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [e1, e2, h.om (k + 1) hk]
      congr 1
      exact Finset.biUnion_congr rfl (fun q _ => ih (by omega) q)

end Agree

variable [LinearOrder D]

/-- **Coin in parallel to the last round, non-adaptive corruptions.** Let `2t < n`, `r ≥ 3`, and
let the adversary strategy `σ c` (for the coin value `c + 1 ∈ [1, 2r-2]`) behave identically
before round `r` and have coin-independent corruption times. Then the iteration
`(b', g) ← Prox_{2r-1}(b)`, coin `c` (revealed in round `r`), output `f(b', g, c)` fails with
probability at most `1/(2r-2)`. -/
theorem coin_parallel_static {r N : ℕ} [NeZero N] (hr : 3 ≤ r) (_hN : N = 2 * r - 2)
    (hn : Fintype.card P = n) (hnt : 2 * t < n) (d₀ : Bool) {x : P → Bool}
    (σ : Fin N → Adv P Bool) (hv : ∀ c, Valid n t x (σ c) r)
    (hpre : ∀ c c', PrefixAgree r (σ c) (σ c')) (hcr : ∀ c c', (σ c).cr = (σ c').cr) :
    (PMF.uniformOfFintype (Fin N)).toOuterMeasure
        {c | ∃ p ∈ {q | r < (σ c).cr q}, ∃ q ∈ {q | r < (σ c).cr q},
          extract (2 * r - 1) (out n t x (σ c) r d₀ p) (c + 1) ≠
            extract (2 * r - 1) (out n t x (σ c) r d₀ q) (c + 1)}
      ≤ 1 / N := by
  refine iter_error_le_family (fun c => {q | r < (σ c).cr q}) (fun c => out n t x (σ c) r d₀)
    (fun c p hp => (half_isProx hr hn (hv c) hnt d₀).grade_le p hp) (fun c c' p hp q hq => ?_)
  exact two_run_cons (by omega) (hv c) hnt d₀ (hcr c c') (hpre c c').S_eq (hpre c c').Om_eq hp
    (by rw [hcr c c']; exact hq)

/-- Validity of the iteration for every coin value (from Lemma 3.5 and Theorem 3.7). -/
theorem coin_parallel_validity {r : ℕ} (hr : 3 ≤ r) (hn : Fintype.card P = n) (hnt : 2 * t < n)
    (d₀ : Bool) {x : P → Bool} (A : Adv P Bool) (hv : Valid n t x A r) (b : Bool)
    (hb : ∀ q, r < A.cr q → x q = b) (c : ℕ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2 * r - 2) :
    ∀ p, r < A.cr p → extract (2 * r - 1) (out n t x A r d₀ p) c = b :=
  fun p hp => iter_validity (half_isProx hr hn hv hnt d₀) b (fun q hq => hb q hq) c hc1
    (by omega) p hp

/-! ### The adaptive attack (`n = 5`, `t = 2`, `Prox_5`) -/

/-- Inputs: parties `0, 1` have input `1`, parties `2, 3, 4` input `0`. -/
def atkIn : Fin 5 → Bool := ![true, true, false, false, false]

/-- The adversary for coin value `c`. Party `4` is corrupted from the start: in round 1 it gives
a share on `1` to everybody (so every party gets `S¹ = {1}`), in round 2 it gives its share `ω` on
`1` to party `0` only (so only party `0` forms `Ω` on `1`). In round 3, after seeing the coin:
if `c = 3` it corrupts party `0` and lets it forward `Ω` to party `1` only; otherwise it does
nothing. -/
def atkAdv (c : ℕ) : Adv (Fin 5) Bool where
  cr q := if q = 4 then 1 else if q = 0 ∧ c = 3 then 3 else 4
  sh1 q _ := if q = 4 then {true} else ∅
  sig _ _ _ := ∅
  wsh q i := if q = 4 ∧ i = 0 then {true} else ∅
  om k q i := if k = 3 ∧ q = 0 ∧ c = 3 ∧ i = 1 then {true} else ∅

lemma atk_valid (c : ℕ) : Valid 5 2 atkIn (atkAdv c) 3 := by
  refine ⟨fun k q i _ _ => by simp [atkAdv], fun k q i hk hq => ?_, ?_⟩
  · by_cases h : k = 3 ∧ q = 0 ∧ c = 3 ∧ i = 1
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      decide
    · simp only [atkAdv, if_neg h]; exact Finset.empty_subset _
  · by_cases hc : c = 3
    · subst hc; decide
    · simp only [atkAdv, hc, and_false, if_false]; decide

lemma atk_prefix (c c' : ℕ) : PrefixAgree 3 (atkAdv c) (atkAdv c') := by
  refine ⟨fun q => ?_, fun q hq => ?_, rfl, rfl, fun k hk => rfl, fun k hk => ?_⟩
  · by_cases hc : c = 3 <;> by_cases hc' : c' = 3 <;> fin_cases q <;> simp [atkAdv, hc, hc']
  · by_cases hc : c = 3 <;> by_cases hc' : c' = 3 <;> fin_cases q <;> simp_all [atkAdv]
  · funext q i
    simp only [atkAdv]
    rw [if_neg (by omega), if_neg (by omega)]

/-- The outputs of the honest parties for the coin values `3` and `4`. -/
lemma atk_out3 : (out 5 2 atkIn (atkAdv 3) 3 false 1, out 5 2 atkIn (atkAdv 3) 3 false 2) =
    ((true, 1), (false, 0)) := by decide

lemma atk_out4 : (out 5 2 atkIn (atkAdv 4) 3 false 0, out 5 2 atkIn (atkAdv 4) 3 false 1) =
    ((true, 2), (true, 1)) := by decide

/-- The coins `c + 1 ∈ {3, 4}` lead to disagreement. -/
lemma atk_bad : {c : Fin 4 | ∃ p ∈ {q | 3 < (atkAdv (c + 1)).cr q},
      ∃ q ∈ {q | 3 < (atkAdv (c + 1)).cr q},
        extract (2 * 3 - 1) (out 5 2 atkIn (atkAdv (c + 1)) 3 false p) (c + 1) ≠
          extract (2 * 3 - 1) (out 5 2 atkIn (atkAdv (c + 1)) 3 false q) (c + 1)} ⊇
      {c | c = 2 ∨ c = 3} := by
  rintro c (rfl | rfl)
  · exact ⟨1, by decide, 2, by decide, by decide⟩
  · exact ⟨0, by decide, 1, by decide, by decide⟩

/-- **The adaptive attack.** For `n = 5`, `t = 2` (`2t < n`), protocol `Prox_5` (3 rounds) and the
coin uniform in `[1, 4]` revealed in round 3, the adversary `atkAdv` — identical before round 3
for all coin values, valid, corrupting at most `t` parties — makes two honest parties output
different bits with probability at least `1/2` (the paper claims `1/4`). -/
theorem coin_parallel_adaptive_attack :
    2 * 2 < 5 ∧ (∀ c, Valid 5 2 atkIn (atkAdv c) 3) ∧
      (∀ c c', PrefixAgree 3 (atkAdv c) (atkAdv c')) ∧
      1 / 2 ≤ (PMF.uniformOfFintype (Fin 4)).toOuterMeasure
        {c : Fin 4 | ∃ p ∈ {q | 3 < (atkAdv (c + 1)).cr q},
          ∃ q ∈ {q | 3 < (atkAdv (c + 1)).cr q},
            extract (2 * 3 - 1) (out 5 2 atkIn (atkAdv (c + 1)) 3 false p) (c + 1) ≠
              extract (2 * 3 - 1) (out 5 2 atkIn (atkAdv (c + 1)) 3 false q) (c + 1)} := by
  refine ⟨by norm_num, atk_valid, atk_prefix, ?_⟩
  have hm : (PMF.uniformOfFintype (Fin 4)).toOuterMeasure {c : Fin 4 | c = 2 ∨ c = 3} = 1 / 2 := by
    rw [PMF.toOuterMeasure_uniformOfFintype_apply]
    have : Fintype.card {c : Fin 4 | c = 2 ∨ c = 3} = 2 := by decide
    rw [this, Fintype.card_fin]
    rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  rw [← hm]
  exact (PMF.uniformOfFintype (Fin 4)).toOuterMeasure.mono atk_bad

end RoundEfficientBA.Half

namespace RoundEfficientBA.Half

/-- Non-vacuity of `coin_parallel_static`: the coin-independent strategy that always plays
`atkAdv 4` satisfies all hypotheses (`n = 5`, `t = 2`, `r = 3`), and for it the bound `1/4` is
attained: exactly the coin `4` separates party `0` (output `(1,2)`) from party `1` (output
`(1,1)`). -/
theorem coin_parallel_static_tight :
    (∀ c : Fin 4, Valid 5 2 atkIn ((fun _ => atkAdv 4) c) 3) ∧
    (∀ c c' : Fin 4, PrefixAgree 3 ((fun _ => atkAdv 4) c) ((fun _ => atkAdv 4) c')) ∧
    (∀ c c' : Fin 4, ((fun _ => atkAdv 4) c).cr = ((fun _ => atkAdv 4) c').cr) ∧
    (PMF.uniformOfFintype (Fin 4)).toOuterMeasure
        {c : Fin 4 | ∃ p ∈ {q | 3 < (atkAdv 4).cr q}, ∃ q ∈ {q | 3 < (atkAdv 4).cr q},
          extract (2 * 3 - 1) (out 5 2 atkIn (atkAdv 4) 3 false p) (c + 1) ≠
            extract (2 * 3 - 1) (out 5 2 atkIn (atkAdv 4) 3 false q) (c + 1)} = 1 / 4 := by
  refine ⟨fun _ => atk_valid 4, fun _ _ => atk_prefix 4 4, fun _ _ => rfl, ?_⟩
  have hset : {c : Fin 4 | ∃ p ∈ {q | 3 < (atkAdv 4).cr q}, ∃ q ∈ {q | 3 < (atkAdv 4).cr q},
      extract (2 * 3 - 1) (out 5 2 atkIn (atkAdv 4) 3 false p) (c + 1) ≠
        extract (2 * 3 - 1) (out 5 2 atkIn (atkAdv 4) 3 false q) (c + 1)} = {3} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    revert c
    decide
  rw [hset, PMF.toOuterMeasure_uniformOfFintype_apply]
  simp

end RoundEfficientBA.Half
