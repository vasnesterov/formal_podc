import Podc.Computability.Distributed.SleepingCrash.Model
import Papers.PODC2025.EnergyEfficientAgreement.Committees
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Binary consensus (Theorem 2): the algorithm violates agreement

Theorem 2 of the brief announcement (Theorem 6 of the full version arXiv:2506.12282v1) claims
binary consensus in `f + 1` rounds with `O(⌈f/√n⌉)` energy. The brief announcement only sketches
the algorithm; its full version (cited by the brief announcement for the proof) gives it as
Algorithm 3, formalized here as `binary` / `algorithm3`:

* `f` committees `C_1, …, C_f` of size `⌈√n⌉` from `JoinCommittees(f, ⌈√n⌉)`;
  `T₀ = ⌈(f + 1)/√n⌉`;
* round `1`: everybody is awake; a player with input `X = 1` sets `T ← T₀` and sends `1` to `C_1`;
  a player that receives `1` while `Y = 0` sets `Y ← 1`, `T ← T₀`;
* round `h ∈ [2, f]`: a player with `T > 0` wakes up, sets `T ← T - 1` and sends `1` to `C_h`;
  the members of `C_h` wake up, and one that receives `1` while `Y = 0` sets `Y ← 1`, `T ← T₀`;
* round `f + 1`: everybody is awake; players with `Y = 1` or `X = 1` broadcast `1`; a player that
  receives `1` or has `X = 1` sets `Y ← 1`; everybody decides `Y`.

`algorithm3_violates_agreement`: for `n = 5`, `f = 3` an adversary crashing 3 players makes the
two non-faulty players decide differently. The value `1` is relayed along a chain of players that
crash one per round; in round `3` the only relay `p₄` sends to `C_3 = {p₂, p₃, p₄}`, whose other
members have already crashed, so the adversary needs no crash in that round; `p₄` then crashes in
round `4 = f + 1` while broadcasting, reaching only `p₀`. Similar executions exist for
`n = 7, f = 4` (three non-faulty players) and `n = 9, f = 7` (a perfect square, where committees
are pairwise disjoint within a period): `algorithm3_violates_agreement_7_4`,
`algorithm3_violates_agreement_9_7`. The same executions are executions of the algorithm sketched
in the brief announcement (they never use the two points where the sketch differs from
Algorithm 3: the window of players with input `1`, who crash in round `1`, and their reactivation).
-/

namespace Podc.EnergyEfficientAgreement

open Cslib.SleepingCrash Finset

/-- Local state of Algorithm 3: input `X`, estimate `Y`, remaining relay rounds `T`. -/
structure BState where
  /-- The input bit. -/
  X : Bool
  /-- The decision estimate. -/
  Y : Bool
  /-- Number of rounds the player still relays `1`. -/
  T : ℕ
  deriving DecidableEq, Repr

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Algorithm 3 of the full version with committees `C` and relay length `T₀`
(messages carry the bit `1` only, so they have type `Unit`). -/
def binary (f T₀ : ℕ) (C : ℕ → Finset P) : Algorithm P Bool BState Unit where
  init _ x := ⟨x, false, 0⟩
  awake p r s := decide (r = 1 ∨ r = f + 1 ∨ (2 ≤ r ∧ r ≤ f ∧ (0 < s.T ∨ p ∈ C r)))
  send _ r s q :=
    if (r = 1 ∧ s.X = true ∧ q ∈ C 1) ∨ (2 ≤ r ∧ r ≤ f ∧ 0 < s.T ∧ q ∈ C r) ∨
        (r = f + 1 ∧ (s.Y = true ∨ s.X = true)) then some () else none
  recv p r s inbox :=
    let got := decide (∃ q, inbox q = some ())
    if r = 1 then
      -- lines 3-8: `T ← T₀` if `X = 1`; activation on the first received `1`
      if got ∧ s.Y = false then ⟨s.X, true, T₀⟩ else ⟨s.X, s.Y, if s.X then T₀ else s.T⟩
    else if r ≤ f then
      -- lines 10-17: relaying decrements `T`; activation on the first received `1`
      if p ∈ C r ∧ got ∧ s.Y = false then ⟨s.X, true, T₀⟩ else ⟨s.X, s.Y, s.T - 1⟩
    else if r = f + 1 then
      -- lines 21-22
      if got ∨ s.X = true then ⟨s.X, true, s.T⟩ else s
    else s

/-- Algorithm 3 for `n` players and parameter `f`: committees `JoinCommittees(f, ⌈√n⌉)` and
`T₀ = ⌈(f + 1)/√n⌉`. The decision of a player is `Y` at the end of round `f + 1`. -/
noncomputable def algorithm3 (n f : ℕ) [NeZero n] : Algorithm (Fin n) Bool BState Unit :=
  binary f ⌈((f + 1 : ℕ) : ℝ) / Real.sqrt n⌉₊ (joinCommittees n f ⌈Real.sqrt n⌉₊)

/-! ### Evaluating the ceilings -/

lemma ceil_sqrt_eq {n s : ℕ} (h1 : (s - 1) ^ 2 < n) (h2 : n ≤ s ^ 2) (hs : 0 < s) :
    ⌈Real.sqrt n⌉₊ = s := by
  rw [Nat.ceil_eq_iff hs.ne']
  constructor
  · rw [Real.lt_sqrt (by positivity)]
    exact_mod_cast h1
  · rw [Real.sqrt_le_left (by positivity)]
    exact_mod_cast h2

lemma ceil_div_sqrt_eq {a n T : ℕ} (hn : 0 < n) (hT : 0 < T) (h1 : (T - 1) ^ 2 * n < a ^ 2)
    (h2 : a ^ 2 ≤ T ^ 2 * n) : ⌈(a : ℝ) / Real.sqrt n⌉₊ = T := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by positivity)
  rw [Nat.ceil_eq_iff hT.ne', lt_div_iff₀ hs, div_le_iff₀ hs]
  constructor
  · have : (((T - 1 : ℕ) : ℝ) * Real.sqrt n) ^ 2 < (a : ℝ) ^ 2 := by
      rw [mul_pow, hsq]; exact_mod_cast h1
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
  · have : (a : ℝ) ^ 2 ≤ ((T : ℝ) * Real.sqrt n) ^ 2 := by
      rw [mul_pow, hsq]; exact_mod_cast h2
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) this

/-! ### Counterexamples -/

/-- The adversary for `n = 5`, `f = 3`: only `p₂` has input `1`; `p₂` crashes in round 1 reaching
only `p₃`, `p₃` crashes in round 2 reaching only `p₄`, `p₄` crashes in round 4 reaching only
`p₀`. -/
def adv5 : Adversary (Fin 5) Bool where
  input p := p = 2
  crash p := if p = 2 then some 1 else if p = 3 then some 2 else if p = 4 then some 4 else none
  reach p := if p = 2 then {3} else if p = 3 then {4} else {0}

/-- **Algorithm 3 violates agreement** (`n = 5`, `f = 3`, committees `C_1 = {p₁, p₂, p₃}`,
`C_2 = {p₄, p₀, p₁}`, `C_3 = {p₂, p₃, p₄}`, `T₀ = 2`): with 3 crashes, the non-faulty players
`p₀` and `p₁` decide `1` and `0`. -/
theorem algorithm3_violates_agreement :
    adv5.Admissible 3 ∧ ¬ adv5.Faulty 0 ∧ ¬ adv5.Faulty 1 ∧
      (config (algorithm3 5 3) adv5 4 0).Y = true ∧ (config (algorithm3 5 3) adv5 4 1).Y = false := by
  have hs : ⌈Real.sqrt ((5 : ℕ) : ℝ)⌉₊ = 3 := ceil_sqrt_eq (by norm_num) (by norm_num) (by norm_num)
  have hT : ⌈((3 + 1 : ℕ) : ℝ) / Real.sqrt ((5 : ℕ) : ℝ)⌉₊ = 2 :=
    ceil_div_sqrt_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold algorithm3
  rw [hs, hT]
  refine ⟨⟨by decide, fun p c hc => ?_⟩, by decide, by decide, by decide, by decide⟩
  fin_cases p <;> simp [adv5] at hc <;> omega

/-- The adversary for `n = 7`, `f = 4`: the chain `p₄ → p₃ → p₅ → p₂` crashes in rounds `1, 2, 3`;
round `4` needs no crash (`C_4 = {p₃, p₄, p₅}` has crashed); `p₂` crashes in round `5`. -/
def adv7 : Adversary (Fin 7) Bool where
  input p := p = 4
  crash p := if p = 4 then some 1 else if p = 3 then some 2 else if p = 5 then some 3
    else if p = 2 then some 5 else none
  reach p := if p = 4 then {3} else if p = 3 then {5} else if p = 5 then {2} else {0}

/-- Algorithm 3 violates agreement for `n = 7`, `f = 4` (three non-faulty players). -/
theorem algorithm3_violates_agreement_7_4 :
    adv7.Admissible 4 ∧ ¬ adv7.Faulty 0 ∧ ¬ adv7.Faulty 1 ∧
      (config (algorithm3 7 4) adv7 5 0).Y = true ∧ (config (algorithm3 7 4) adv7 5 1).Y = false := by
  have hs : ⌈Real.sqrt ((7 : ℕ) : ℝ)⌉₊ = 3 := ceil_sqrt_eq (by norm_num) (by norm_num) (by norm_num)
  have hT : ⌈((4 + 1 : ℕ) : ℝ) / Real.sqrt ((7 : ℕ) : ℝ)⌉₊ = 2 :=
    ceil_div_sqrt_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold algorithm3
  rw [hs, hT]
  refine ⟨⟨by decide, fun p c hc => ?_⟩, by decide, by decide, by decide, by decide⟩
  fin_cases p <;> simp [adv7] at hc <;> omega

/-- The adversary for `n = 9`, `f = 7`: the chain `p₁ → p₂ → p₄ → p₈ → p₃ → p₅ → p₀` crashes in
rounds `1, …, 6`; round `7` needs no crash (`C_7 = C_1 = {p₁, p₂, p₃}` has crashed); `p₀` crashes
in round `8` reaching only `p₆`. -/
def adv9 : Adversary (Fin 9) Bool where
  input p := p = 1
  crash p := if p = 1 then some 1 else if p = 2 then some 2 else if p = 4 then some 3
    else if p = 8 then some 4 else if p = 3 then some 5 else if p = 5 then some 6
    else if p = 0 then some 8 else none
  reach p := if p = 1 then {2} else if p = 2 then {4} else if p = 4 then {8} else if p = 8 then {3}
    else if p = 3 then {5} else if p = 5 then {0} else {6}

/-- Algorithm 3 violates agreement for `n = 9`, `f = 7` (`⌈√n⌉ = 3`, `T₀ = 3`). -/
theorem algorithm3_violates_agreement_9_7 :
    adv9.Admissible 7 ∧ ¬ adv9.Faulty 6 ∧ ¬ adv9.Faulty 7 ∧
      (config (algorithm3 9 7) adv9 8 6).Y = true ∧ (config (algorithm3 9 7) adv9 8 7).Y = false := by
  have hs : ⌈Real.sqrt ((9 : ℕ) : ℝ)⌉₊ = 3 := ceil_sqrt_eq (by norm_num) (by norm_num) (by norm_num)
  have hT : ⌈((7 + 1 : ℕ) : ℝ) / Real.sqrt ((9 : ℕ) : ℝ)⌉₊ = 3 :=
    ceil_div_sqrt_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold algorithm3
  rw [hs, hT]
  refine ⟨⟨by decide, fun p c hc => ?_⟩, by decide, by decide, by decide, by decide⟩
  fin_cases p <;> simp [adv9] at hc <;> omega

/-- Sanity check of the model: without crashes (`n = 5`, `f = 3`, only `p₂` has input `1`) every
player decides `1`. -/
example : ∀ p, (config (algorithm3 5 3)
    ({ input := fun p => decide (p = 2), crash := fun _ => none, reach := fun _ => ∅ } :
      Adversary (Fin 5) Bool) 4 p).Y = true := by
  have hs : ⌈Real.sqrt ((5 : ℕ) : ℝ)⌉₊ = 3 := ceil_sqrt_eq (by norm_num) (by norm_num) (by norm_num)
  have hT : ⌈((3 + 1 : ℕ) : ℝ) / Real.sqrt ((5 : ℕ) : ℝ)⌉₊ = 2 :=
    ceil_div_sqrt_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold algorithm3
  rw [hs, hT]
  decide

end Podc.EnergyEfficientAgreement
