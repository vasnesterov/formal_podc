import Papers.PODC2022.AsyncSpeedup.ApproxAgreement
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Podc.Foundations.Data.Real.Logb

/-!
# Round lower bounds for approximate agreement (Corollary 3, Theorems 3 and 4)

In scaled form (`ε = e/m`):

* `corollary3_two` — **Corollary 3**, `n = 2`, IIS: a `t`-round algorithm forces `m ≤ 3^t e`,
  i.e. `t ≥ ⌈log₃ (1/ε)⌉` (`corollary3_two_log`).
* `corollary3_many` — **Corollary 3**, `n ≥ 3`, IIS: `m ≤ 2^t e`, `t ≥ ⌈log₂ (1/ε)⌉`.
* `theorem3` — **Theorem 3**, `n ≥ 3`, IIS + test&set: `m ≤ 2^t e`, `t ≥ ⌈log₂ (1/ε)⌉`.
* `claim6_subset` — **Claim 6** (inclusion), `theorem4` — **Theorem 4**, IIS + binary consensus
  with box inputs depending only on ids and rounds: `n ≤ 2^(t+1)` or `m ≤ 2^t e`, i.e.
  `t ≥ min(⌈log₂ n⌉ - 1, ⌈log₂ (1/ε)⌉)` (`theorem4_log`).
-/

set_option linter.unusedSectionVars false

namespace AsyncSpeedup

open Cslib.Iterated

variable {P : Type} [DecidableEq P]

/-! ### Two processes -/

/-- **Corollary 3** (`n = 2`, scaled form): if `ε`-approximate agreement (`ε = e/m`) among two
processes is solvable in `t` rounds of IIS, then `1 ≤ 3^t ε`. -/
theorem corollary3_two [Fintype P] (hP : Fintype.card P = 2) {m : ℤ} (hm : 0 ≤ m) :
    ∀ (t : ℕ) (e : ℤ), Solvable iis (aa (Finset.univ : Finset P) m e) t → m ≤ 3 ^ t * e := by
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card P)
  intro t
  induction t with
  | zero =>
    intro e h
    by_contra hlt
    exact claim1_aa iis (Finset.mem_univ p) (Finset.mem_univ q) hpq hm (by simp at hlt; omega) h
  | succ t ih =>
    intro e h
    have h' : Solvable iis (aa (Finset.univ : Finset P) m (3 * e)) t :=
      (speedup_noBox iis_wellFormed iis_allowsSolo iis_extendable h).mono
        (Task.Easier.of_subset le_rfl fun I x _ => closure_aa_subset I x)
    have := ih _ h'
    rw [pow_succ]; linarith

/-! ### At least three processes: a generic iteration -/

/-- The iteration of Corollary 3 / Theorem 3 for any model satisfying the hypotheses of the speedup
theorem in which the closure of the liberal `ε`-agreement is contained in the liberal
`2ε`-agreement. -/
theorem libAA_bound {A B : Type} {M : Model P A B} (hwf : M.WellFormed) (hsolo : M.AllowsSolo)
    {b₀ : P → A → B} (hdet : M.SoloDet b₀) (hext : M.Extendable) {S : Finset P} {m : ℤ}
    (hcl : ∀ e I x, (closure M (libAA S m e)).Δ I x ⊆ (libAA S m (2 * e)).Δ I x)
    (hS : 3 ≤ S.card) (hm : 0 ≤ m) :
    ∀ (t : ℕ) (e : ℤ), Solvable M (libAA S m e) t → m ≤ 2 ^ t * e := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  obtain ⟨r, hr, hrp, hrq⟩ := exists_third hS p q
  intro t
  induction t with
  | zero =>
    intro e h
    by_contra hlt
    exact claim1_lib M hp hq hr hpq (Ne.symm hrp) (Ne.symm hrq) hm (by simp at hlt; omega) h
  | succ t ih =>
    intro e h
    have h' : Solvable M (libAA S m (2 * e)) t :=
      (speedup hwf hsolo hdet hext h).mono
        (Task.Easier.of_subset le_rfl fun I x _ => hcl e I x)
    have := ih _ h'
    rw [pow_succ]; linarith

lemma three_le_univ [Fintype P] (hP : 3 ≤ Fintype.card P) : 3 ≤ (Finset.univ : Finset P).card := by
  rwa [Finset.card_univ]

/-- **Corollary 3** (`n ≥ 3`, scaled form): if `ε`-approximate agreement among `n ≥ 3` processes
is solvable in `t` rounds of IIS, then `1 ≤ 2^t ε`. -/
theorem corollary3_many [Fintype P] (hP : 3 ≤ Fintype.card P) {m : ℤ} (hm : 0 ≤ m) (t : ℕ)
    (e : ℤ) (h : Solvable iis (aa (Finset.univ : Finset P) m e) t) : m ≤ 2 ^ t * e :=
  libAA_bound iis_wellFormed iis_allowsSolo iis_soloDet iis_extendable
    (fun _ I x => claim3_subset I x) (three_le_univ hP) hm t e (h.mono (libAA_easier _ _ _))

/-- **Theorem 3** (scaled form): if `ε`-approximate agreement among `n ≥ 3` processes is solvable
in `t` rounds of IIS augmented with test&set, then `1 ≤ 2^t ε`. -/
theorem theorem3 [Fintype P] (hP : 3 ≤ Fintype.card P) {m : ℤ} (hm : 0 ≤ m) (t : ℕ)
    (e : ℤ) (h : Solvable iisTS (aa (Finset.univ : Finset P) m e) t) : m ≤ 2 ^ t * e :=
  libAA_bound iisTS_wellFormed iisTS_allowsSolo iisTS_soloDet iisTS_extendable
    (fun _ I x => claim4_subset I x) (three_le_univ hP) hm t e (h.mono (libAA_easier _ _ _))

/-! ### Binary consensus objects (Section 5.3) -/

/-- **Claim 6** (inclusion `Δ'_ε ⊆ Δ_{2ε}`): when only processes calling the binary consensus
object with the same input participate, the closure w.r.t. `β` of the liberal `ε`-agreement is
contained in the liberal `2ε`-agreement. (No size assumption on `S` is needed.) -/
theorem claim6_subset {S : Finset P} {m e : ℤ} (β : P → Bool) (b : Bool) {I : Finset P}
    (hI : I ⊆ S.filter (fun l => β l = b)) (x : P → ℤ) :
    (closureβ iisBC (libAA S m e) β).Δ I x ⊆ (libAA S m (2 * e)).Δ I x := by
  rintro τ ⟨hV, g, hgβ, hg⟩
  have hβ : ∀ l ∈ I, β l = b := fun l hl => (Finset.mem_filter.1 (hI hl)).2
  refine libAA_subset_of_local iisBC_allowsSolo iisBC_soloDet hV hg
    fun i hi j hj k hk hij hki hkj => ?_
  refine ⟨bcPat I (rank3 i j k) i _, bcPat_mem hi rank3_zero _, bcPat I (rank3 j i k) j _,
    bcPat_mem hj rank3_zero _, rank3_solo hi, rank3_solo hj,
    rank3_third (Ne.symm hki) (Ne.symm hkj), ?_⟩
  simp only [bcPat, hgβ, hβ i hi, hβ j hj]

lemma solvableIdOnly_mono {A B X Y : Type} {M : Model P A B} {T T' : Task P X Y} {t : ℕ}
    (h : SolvableIdOnly M T t) (hT : T'.Easier T) : SolvableIdOnly M T' t :=
  let ⟨alg, hid, halg⟩ := h; ⟨alg, hid, halg.mono hT⟩

/-- The iteration of the proof of Theorem 4 (with the cleaner invariant `|S| ≤ 2^(t+1)` or
`1 ≤ 2^t ε`). -/
theorem theorem4_aux {m : ℤ} (hm : 0 ≤ m) :
    ∀ (t : ℕ) (S : Finset P) (e : ℤ), SolvableIdOnly iisBC (libAA S m e) t →
      S.card ≤ 2 ^ (t + 1) ∨ m ≤ 2 ^ t * e := by
  intro t
  induction t with
  | zero =>
    rintro S e ⟨alg, -, halg⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 (by simp at hcon; omega : 1 < S.card)
    obtain ⟨r, hr, hrp, hrq⟩ := exists_third (by simp at hcon; omega : 3 ≤ S.card) p q
    exact claim1_lib iisBC hp hq hr hpq (Ne.symm hrp) (Ne.symm hrq) hm (by simp at hcon; omega)
      ⟨alg, halg⟩
  | succ t ih =>
    intro S e h
    obtain ⟨β, hβ⟩ := speedup_idOnly iisBC_wellFormed iisBC_allowsSolo iisBC_soloDet
      iisBC_extendable h
    -- the larger of `β⁻¹(true)` and `β⁻¹(false)` inside `S`
    have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun l => β l = true)
    obtain ⟨b, hb⟩ : ∃ b : Bool, S.card ≤ 2 * (S.filter (fun l => β l = b)).card := by
      by_cases h' : (S.filter (fun l => ¬ β l = true)).card ≤ (S.filter (fun l => β l = true)).card
      · exact ⟨true, by omega⟩
      · refine ⟨false, ?_⟩
        have : S.filter (fun l => β l = false) = S.filter (fun l => ¬ β l = true) := by
          ext l; simp
        rw [this]; omega
    set S' := S.filter (fun l => β l = b) with hS'
    have h' : SolvableIdOnly iisBC (libAA S' m (2 * e)) t :=
      solvableIdOnly_mono hβ
        (Task.Easier.of_subset (fun σ ⟨h1, h2, h3⟩ => ⟨h1, h2.trans (Finset.filter_subset _ _), h3⟩)
          fun I x hI => claim6_subset β b hI.2.1 x)
    rcases ih S' (2 * e) h' with h1 | h1
    · left; rw [pow_succ]; omega
    · right; rw [pow_succ]; linarith

/-- **Theorem 4** (scaled form): if `ε`-approximate agreement among `n` processes is solvable in
`t` rounds of IIS augmented with binary consensus, by an algorithm whose inputs to the consensus
objects depend only on process ids and round numbers, then `n ≤ 2^(t+1)` or `1 ≤ 2^t ε`. -/
theorem theorem4 [Fintype P] {m : ℤ} (hm : 0 ≤ m) (t : ℕ) (e : ℤ)
    (h : SolvableIdOnly iisBC (aa (Finset.univ : Finset P) m e) t) :
    Fintype.card P ≤ 2 ^ (t + 1) ∨ m ≤ 2 ^ t * e := by
  have := theorem4_aux hm t Finset.univ e (solvableIdOnly_mono h (libAA_easier _ _ _))
  rwa [Finset.card_univ] at this

/-! ### Logarithmic forms -/

lemma ceil_logb_le_of_le_pow {b : ℕ} (hb : 1 < b) {u : ℝ} (hu : 0 < u) {t : ℕ}
    (h : u ≤ (b : ℝ) ^ t) : ⌈Real.logb b u⌉ ≤ t :=
  (Real.ceil_logb_le_iff_le_pow (by exact_mod_cast hb) hu).2 h

lemma one_div_eps_le {m e : ℤ} (he : 0 < e) {c : ℕ} {t : ℕ} (h : m ≤ (c : ℤ) ^ t * e) :
    1 / ((e : ℝ) / m) ≤ (c : ℝ) ^ t := by
  rw [one_div_div, div_le_iff₀ (by exact_mod_cast he)]
  exact_mod_cast h

/-- **Corollary 3** (`n = 2`): any IIS algorithm for `ε`-approximate agreement between two
processes (`ε = e/m ∈ (0, 1]`) needs at least `⌈log₃ (1/ε)⌉` rounds. -/
theorem corollary3_two_log [Fintype P] (hP : Fintype.card P = 2) {m e : ℤ} (hm : 0 < m)
    (he : 0 < e) {t : ℕ} (h : Solvable iis (aa (Finset.univ : Finset P) m e) t) :
    ⌈Real.logb 3 (1 / ((e : ℝ) / m))⌉ ≤ t := by
  have h3 := corollary3_two hP hm.le t e h
  exact_mod_cast ceil_logb_le_of_le_pow (b := 3) (by norm_num)
    (by have : (0 : ℝ) < e := by exact_mod_cast he
        have : (0 : ℝ) < m := by exact_mod_cast hm
        positivity) (one_div_eps_le (c := 3) he (by exact_mod_cast h3))

/-- **Corollary 3** (`n ≥ 3`): any IIS algorithm for `ε`-approximate agreement among `n ≥ 3`
processes needs at least `⌈log₂ (1/ε)⌉` rounds. -/
theorem corollary3_many_log [Fintype P] (hP : 3 ≤ Fintype.card P) {m e : ℤ} (hm : 0 < m)
    (he : 0 < e) {t : ℕ} (h : Solvable iis (aa (Finset.univ : Finset P) m e) t) :
    ⌈Real.logb 2 (1 / ((e : ℝ) / m))⌉ ≤ t := by
  have h3 := corollary3_many hP hm.le t e h
  exact_mod_cast ceil_logb_le_of_le_pow (b := 2) (by norm_num)
    (by have : (0 : ℝ) < e := by exact_mod_cast he
        have : (0 : ℝ) < m := by exact_mod_cast hm
        positivity) (one_div_eps_le (c := 2) he (by exact_mod_cast h3))

/-- **Theorem 3**: any algorithm for `ε`-approximate agreement among `n ≥ 3` processes in IIS
augmented with test&set needs at least `⌈log₂ (1/ε)⌉` rounds. -/
theorem theorem3_log [Fintype P] (hP : 3 ≤ Fintype.card P) {m e : ℤ} (hm : 0 < m)
    (he : 0 < e) {t : ℕ} (h : Solvable iisTS (aa (Finset.univ : Finset P) m e) t) :
    ⌈Real.logb 2 (1 / ((e : ℝ) / m))⌉ ≤ t := by
  have h3 := theorem3 hP hm.le t e h
  exact_mod_cast ceil_logb_le_of_le_pow (b := 2) (by norm_num)
    (by have : (0 : ℝ) < e := by exact_mod_cast he
        have : (0 : ℝ) < m := by exact_mod_cast hm
        positivity) (one_div_eps_le (c := 2) he (by exact_mod_cast h3))

/-- **Theorem 4**: any algorithm for `ε`-approximate agreement among `n` processes in IIS
augmented with binary consensus, whose consensus inputs depend only on ids and rounds, needs at
least `min(⌈log₂ n⌉ - 1, ⌈log₂ (1/ε)⌉)` rounds. -/
theorem theorem4_log [Fintype P] {m e : ℤ} (hm : 0 < m) (he : 0 < e) {t : ℕ}
    (h : SolvableIdOnly iisBC (aa (Finset.univ : Finset P) m e) t) :
    min (⌈Real.logb 2 (Fintype.card P)⌉ - 1) ⌈Real.logb 2 (1 / ((e : ℝ) / m))⌉ ≤ t := by
  rcases theorem4 hm.le t e h with h1 | h1
  · refine min_le_of_left_le ?_
    rcases Nat.eq_zero_or_pos (Fintype.card P) with h0 | h0
    · rw [h0]; simp
    have hpos : (0 : ℝ) < Fintype.card P := by exact_mod_cast h0
    have := ceil_logb_le_of_le_pow (b := 2) (t := t + 1) (by norm_num) hpos
      (by exact_mod_cast h1)
    push_cast at this
    omega
  · refine min_le_of_right_le ?_
    exact_mod_cast ceil_logb_le_of_le_pow (b := 2) (by norm_num)
      (by have : (0 : ℝ) < e := by exact_mod_cast he
          have : (0 : ℝ) < m := by exact_mod_cast hm
          positivity) (one_div_eps_le (c := 2) he (by exact_mod_cast h1))

end AsyncSpeedup
