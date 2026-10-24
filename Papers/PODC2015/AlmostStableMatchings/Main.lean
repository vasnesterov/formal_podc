import Papers.PODC2015.AlmostStableMatchings.BadMen

/-!
# Main results: Theorem 4.1 (approximation guarantee) and Theorem 4.7 (running time)

Ostrovsky, Rosenbaum, *Fast Distributed Almost Stable Matchings*, PODC 2015 (arXiv 1408.2782v2).

* `lemma_4_2_4_6`: in every reachable state, a `(2/k)`-blocking pair `(m, w)` has `m` bad and
  `w ∈ Q^m`. This is Lemma 4.2 (good men are in no `(2/k)`-blocking pair) and the key step of
  Lemma 4.6 (a bad man is in at most `|Q^m|` of them).
* `lemma_4_4`: the `(2/k)`-blocking pairs number at most `4δ|E|` if `ℓ ≥ 2k/δ`.
* `blocking_le`: the general bound `k ℓ · #blocking ≤ 4 ℓ |E| + 8 k² |E|`.
* `theorem_4_1`: `ASM(P, ε, n)` outputs a matching that is `(1 - ε)`-stable, for every `ε > 0`,
  every `n` bounding the degrees and every maximal-matching subroutine.
* `theorem_4_7`: `ASM(P, ε, n)` uses `O(ε⁻³ log⁵ n)` rounds when the subroutine uses
  `O(log⁴ n)` rounds (the arithmetic on `asmRounds`); `stageC_asm` shows that the run of `ASM`
  with a round counter ends at `asmRounds`, and `theorem_4_7_run` combines the two.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2015.AlmostStableMatchings

open Finset

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

namespace Prefs

variable {P : Prefs M W} {k : ℕ}

lemma nat_of_eps {k d R r : ℕ} (hk : 0 < k) (h : (2 / k : ℝ) * d ≤ (R : ℝ) - r) :
    k * r + 2 * d ≤ k * R := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 : (2 : ℝ) * d ≤ k * ((R : ℝ) - r) := by
    have := mul_le_mul_of_nonneg_left h hk'.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hk'.ne'] at this
  have : ((k * r + 2 * d : ℕ) : ℝ) ≤ ((k * R : ℕ) : ℝ) := by push_cast; nlinarith
  exact_mod_cast this

/-- **Lemmas 4.2 and 4.6.** In every reachable state, if `(m, w)` is `(2/k)`-blocking then `m` is
unmatched and `w` has not rejected him (`w ∈ Q^m`); in particular `m` is bad. -/
theorem lemma_4_2_4_6 (hk : 1 ≤ k) {s : St M W} (hI : P.Inv k s) {m : M} {w : W}
    (hE : w ∈ P.man m) (hb : P.IsEpsBlocking (2 / k) s.pm s.pw m w) :
    s.pm m = none ∧ w ∈ s.Q m := by
  have hk0 : 0 < k := hk
  have hwQ : w ∈ s.Q m := by
    by_contra hQ
    obtain ⟨m', hm', hle⟩ := hI.witness m w (P.mem_NM.2 hE) hQ
    have h := hb.2
    rw [hm'] at h
    have h1 := nat_of_eps hk0 h
    have h2 := lt_of_quant_le (P.degW_pos ((P.mem_iff m w).1 hE)) hle
    simp only [rankOptW] at h1
    omega
  refine ⟨?_, hwQ⟩
  cases hp : s.pm m with
  | none => rfl
  | some w0 =>
    exfalso
    have h := hb.1
    rw [hp] at h
    have h1 := nat_of_eps hk0 h
    simp only [rankOptM] at h1
    have hlt := quant_lt (P.degM_pos hE) (by omega : k * P.rankM m w + P.degM m ≤ k * P.rankM m w0)
    have := hI.p_best m w0 hp w hwQ
    unfold qM at this; omega

/-- **Lemma 4.2.** A good man (matched, or rejected by all acceptable partners) is in no
`(2/k)`-blocking pair. -/
theorem lemma_4_2 (hk : 1 ≤ k) {s : St M W} (hI : P.Inv k s) {m : M}
    (hgood : s.pm m ≠ none ∨ s.Q m = ∅) (w : W) (hE : w ∈ P.man m) :
    ¬ P.IsEpsBlocking (2 / k) s.pm s.pw m w := fun hb => by
  obtain ⟨h1, h2⟩ := lemma_4_2_4_6 hk hI hE hb
  rcases hgood with h | h
  · exact h h1
  · rw [h] at h2; simp at h2

/-- The `(2/k)`-blocking pairs (they are blocking pairs whenever they are edges). -/
noncomputable def strongBlocking (P : Prefs M W) (k : ℕ) (s : St M W) : Finset (M × W) :=
  (P.blockingPairs s.pm s.pw).filter fun e => P.IsEpsBlocking (2 / k) s.pm s.pw e.1 e.2

/-- **Lemma 4.6**, summed: the `(2/k)`-blocking pairs are at most `∑_{m bad} |Q^m|`. -/
lemma card_strongBlocking_le (hk : 1 ≤ k) {s : St M W} (hI : P.Inv k s) :
    #(P.strongBlocking k s) ≤ ∑ m ∈ badSet s, #(s.Q m) := by
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn (fun e => ⟨e.1, e.2⟩) (fun e he => ?_) ?_
  · simp only [strongBlocking, Finset.mem_coe, Finset.mem_filter, mem_blockingPairs] at he
    obtain ⟨h1, h2⟩ := lemma_4_2_4_6 hk hI he.1.1 he.2
    simp only [Finset.mem_coe, Finset.mem_sigma, mem_badSet]
    exact ⟨⟨h1, ⟨e.2, h2⟩⟩, h2⟩
  · intro e _ e' _ h
    simp only [Sigma.mk.injEq] at h
    exact Prod.ext h.1 (eq_of_heq h.2)

/-- The output of `asm` is a matching in the communication graph. -/
theorem asm_isMatching (mm : MMOracle M W) (ℓ L : ℕ) :
    P.IsMatching (P.asm k mm ℓ L).pm (P.asm k mm ℓ L).pw where
  consistent := (inv_stage mm ℓ (L + 1)).cons
  mem_E m w h := (inv_stage mm ℓ (L + 1)).mem_NM ((inv_stage mm ℓ (L + 1)).p_mem m w h)

/-- **Lemma 4.4.** If `ℓ ≥ 2k/δ` and all degrees are `< 2^{L+1}`, the bad men contribute at most
`4δ|E|` `(2/k)`-blocking pairs (and every `(2/k)`-blocking pair has a bad man, Lemma 4.2). -/
theorem lemma_4_4 (hk : 1 ≤ k) (mm : MMOracle M W) {ℓ L : ℕ}
    (hL : ∀ m, P.degM m < 2 ^ (L + 1)) {δ : ℝ} (hδ : 0 < δ) (hℓ : 2 * k / δ ≤ ℓ) :
    (#(P.strongBlocking k (P.asm k mm ℓ L)) : ℝ) ≤ 4 * δ * P.E.card := by
  have h1 := card_strongBlocking_le hk (inv_stage (k := k) (P := P) mm ℓ (L + 1))
  have h2 := sum_bad_card_le (P := P) (mm := mm) hk ℓ L hL
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hℓpos : (0 : ℝ) < ℓ := lt_of_lt_of_le (by positivity) hℓ
  have hℓ' : 2 * (k : ℝ) ≤ ℓ * δ := by rwa [div_le_iff₀ hδ] at hℓ
  set X := (#(P.strongBlocking k (P.asm k mm ℓ L)) : ℝ)
  have hX : (ℓ : ℝ) * X ≤ 8 * k * P.E.card := by
    have : ℓ * #(P.strongBlocking k (P.asm k mm ℓ L)) ≤ 8 * k * P.E.card :=
      (Nat.mul_le_mul_left ℓ h1).trans h2
    simp only [X]; exact_mod_cast this
  have hE : (0 : ℝ) ≤ P.E.card := by positivity
  -- `ℓ X ≤ 8 k |E| ≤ 4 δ ℓ |E|`
  have : (ℓ : ℝ) * X ≤ ℓ * (4 * δ * P.E.card) := by nlinarith
  exact le_of_mul_le_mul_left this hℓpos

/-- **The general bound.** For `k ≥ 1` quantiles, `ℓ` calls of `QuantileMatch` per outer
iteration and outer iterations `0, …, L` with all degrees `< 2^{L+1}`, the output has
`k ℓ · #blocking ≤ 4 ℓ |E| + 8 k² |E|`, i.e. at most `(4/k + 8k/ℓ)|E|` blocking pairs. -/
theorem blocking_le (hk : 1 ≤ k) (mm : MMOracle M W) (ℓ L : ℕ)
    (hL : ∀ m, P.degM m < 2 ^ (L + 1)) :
    (k : ℝ) * ℓ * #(P.blockingPairs (P.asm k mm ℓ L).pm (P.asm k mm ℓ L).pw) ≤
      4 * ℓ * P.E.card + 8 * k ^ 2 * P.E.card := by
  set s := P.asm k mm ℓ L
  have hsplit := Finset.card_filter_add_card_filter_not (s := P.blockingPairs s.pm s.pw)
    (fun e => P.IsEpsBlocking (2 / k) s.pm s.pw e.1 e.2)
  have hN := P.lemma_4_3 k hk s.pm s.pw
  have h1 := card_strongBlocking_le hk (inv_stage (k := k) (P := P) mm ℓ (L + 1))
  have h2 := sum_bad_card_le (P := P) (mm := mm) hk ℓ L hL
  have hS : (ℓ : ℝ) * #(P.strongBlocking k s) ≤ 8 * k * P.E.card := by
    have : ℓ * #(P.strongBlocking k s) ≤ 8 * k * P.E.card := (Nat.mul_le_mul_left ℓ h1).trans h2
    exact_mod_cast this
  rw [← hsplit]
  push_cast
  have hℓ : (0 : ℝ) ≤ ℓ := by positivity
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have : (k : ℝ) * ℓ * #((P.blockingPairs s.pm s.pw).filter
      fun e => ¬ P.IsEpsBlocking (2 / k) s.pm s.pw e.1 e.2) ≤ 4 * ℓ * P.E.card := by
    have := mul_le_mul_of_nonneg_left hN hℓ; nlinarith
  have : (k : ℝ) * ℓ * #(P.strongBlocking k s) ≤ 8 * k ^ 2 * P.E.card := by
    have := mul_le_mul_of_nonneg_left hS hk0; nlinarith
  unfold strongBlocking at *
  nlinarith

lemma one_le_kOf {ε : ℝ} (hε : 0 < ε) : 1 ≤ kOf ε :=
  Nat.one_le_iff_ne_zero.2 (by
    unfold kOf; exact (Nat.ceil_pos.2 (by positivity)).ne')

/-- **Theorem 4.1 (approximation guarantee).** For every `ε > 0`, every bound `n` on the degrees
(e.g. `n = |W|`) and every maximal-matching subroutine, `ASM(P, ε, n)` (with `k = ⌈8/ε⌉`,
`δ = ε/8`, `ℓ = ⌈2k/δ⌉` and outer iterations `0, …, ⌊log₂ n⌋`) outputs a matching with at most
`ε |E|` blocking pairs, i.e. a `(1 - ε)`-stable matching. -/
theorem theorem_4_1 (mm : MMOracle M W) {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (hn : ∀ m, P.degM m ≤ n) :
    P.IsMatching (P.ASM mm ε n).pm (P.ASM mm ε n).pw ∧
      P.IsAlmostStable ε (P.ASM mm ε n).pm (P.ASM mm ε n).pw := by
  refine ⟨asm_isMatching mm _ _, ?_⟩
  have hk := one_le_kOf hε
  have hL : ∀ m, P.degM m < 2 ^ (Nat.log 2 n + 1) := fun m =>
    (hn m).trans_lt (Nat.lt_pow_succ_log_self (by norm_num) n)
  have hb := blocking_le (P := P) hk mm (ellOf ε) (Nat.log 2 n) hL
  unfold IsAlmostStable ASM
  set X := (#(P.blockingPairs (P.asm (kOf ε) mm (ellOf ε) (Nat.log 2 n)).pm
    (P.asm (kOf ε) mm (ellOf ε) (Nat.log 2 n)).pw) : ℝ)
  set K := (kOf ε : ℝ)
  set Lr := (ellOf ε : ℝ)
  set E := (P.E.card : ℝ)
  have hK : 8 / ε ≤ K := Nat.le_ceil _
  have hK1 : (1 : ℝ) ≤ K := by simp only [K]; exact_mod_cast hk
  have hLr : 16 * K / ε ≤ Lr := Nat.le_ceil _
  have hKε : 8 ≤ K * ε := by rwa [div_le_iff₀ hε] at hK
  have hLε : 16 * K ≤ Lr * ε := by rwa [div_le_iff₀ hε] at hLr
  have hLpos : 0 < Lr := lt_of_lt_of_le (by positivity) hLr
  have hE : 0 ≤ E := by positivity
  have hX : 0 ≤ X := by positivity
  -- `K Lr X ≤ 4 Lr E + 8 K² E ≤ (K ε / 2) Lr E + (Lr ε / 2) K E = ε K Lr E`
  have h1 : 4 * Lr * E ≤ K * ε / 2 * Lr * E := by
    have : 4 ≤ K * ε / 2 := by linarith
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hLpos.le hE); nlinarith
  have h2 : 8 * K ^ 2 * E ≤ Lr * ε / 2 * K * E := by
    have : 8 * K ≤ Lr * ε / 2 := by linarith
    have := mul_le_mul_of_nonneg_right this (mul_nonneg (by linarith : (0 : ℝ) ≤ K) hE)
    nlinarith
  have hKL : 0 < K * Lr := by positivity
  have : K * Lr * X ≤ K * Lr * (ε * E) := by nlinarith
  exact le_of_mul_le_mul_left this hKL

/-! ## Theorem 4.7: running time -/

/-- Communication rounds of one `ProposalRound` with a `T`-round maximal-matching subroutine:
one round each for `PROPOSE`, `ACCEPT` and `REJECT`, plus `T` (steps 3 and 5 and the
initializations are local). -/
def prRounds (T : ℕ) : ℕ := 3 + T

/-- Communication rounds of `ASM` with `k` quantiles, `ℓ` calls of `QuantileMatch` per outer
iteration and outer iterations `0, …, L`: `(L + 1) ℓ k` calls of `ProposalRound`. -/
def asmRounds (k ℓ L T : ℕ) : ℕ := (L + 1) * (ℓ * (k * prRounds T))

variable (P k) in
/-- `ProposalRound` with a round counter: one call costs `prRounds mm.rounds` rounds. -/
def prStepC (mm : MMOracle M W) (x : St M W × ℕ) : St M W × ℕ :=
  (P.prStep k mm x.1, x.2 + prRounds mm.rounds)

variable (P k) in
/-- `QuantileMatch` with a round counter (its initialization is local). -/
def quantileMatchC (mm : MMOracle M W) (act : Finset M) (x : St M W × ℕ) : St M W × ℕ :=
  (P.prStepC k mm)^[k] (P.initQM k act x.1, x.2)

variable (P k) in
/-- One outer iteration of `ASM` with a round counter. -/
def outerC (mm : MMOracle M W) (ℓ i : ℕ) (x : St M W × ℕ) : St M W × ℕ :=
  (P.quantileMatchC k mm (P.active i x.1))^[ℓ] x

variable (P k) in
/-- The outer iterations `0, …, i - 1` of `ASM` with a round counter. -/
def stageC (mm : MMOracle M W) (ℓ : ℕ) : ℕ → St M W × ℕ
  | 0 => (P.init, 0)
  | i + 1 => P.outerC k mm ℓ i (stageC mm ℓ i)

lemma prStepC_iterate (mm : MMOracle M W) (t : ℕ) (s : St M W) (r : ℕ) :
    (P.prStepC k mm)^[t] (s, r) = ((P.prStep k mm)^[t] s, r + t * prRounds mm.rounds) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp only [prStepC, Prod.mk.injEq, true_and]; ring

lemma quantileMatchC_iterate (mm : MMOracle M W) (act : Finset M) (t : ℕ) (s : St M W) (r : ℕ) :
    (P.quantileMatchC k mm act)^[t] (s, r) =
      ((P.quantileMatch k mm act)^[t] s, r + t * (k * prRounds mm.rounds)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp only [quantileMatchC, prStepC_iterate, quantileMatch, Prod.mk.injEq, true_and]; ring

lemma stageC_eq (mm : MMOracle M W) (ℓ : ℕ) :
    ∀ i, P.stageC k mm ℓ i = (P.stage k mm ℓ i, i * (ℓ * (k * prRounds mm.rounds)))
  | 0 => by simp [stageC, stage]
  | i + 1 => by
    rw [stageC, stageC_eq mm ℓ i, outerC, quantileMatchC_iterate]
    simp only [stage, outer, Prod.mk.injEq, true_and]; ring

/-- The run of `ASM` instrumented with a round counter computes the output of `ASM`, and the
counter ends at `asmRounds k ℓ L mm.rounds`: `ASM` makes exactly `(L + 1) ℓ k` calls of
`ProposalRound`. -/
theorem stageC_asm (mm : MMOracle M W) (ℓ L : ℕ) :
    P.stageC k mm ℓ (L + 1) = (P.asm k mm ℓ L, asmRounds k ℓ L mm.rounds) := by
  rw [stageC_eq]; rfl

/-- **Theorem 4.7.** If the maximal-matching subroutine needs `T ≤ c log⁴ n` rounds, then
`ASM(P, ε, n)` needs at most `2610 (3 + c) ε⁻³ log⁵ n` rounds, for `0 < ε ≤ 1` and `n ≥ 2`
(`log = ⌊log₂⌋`): `O(ε⁻³ log⁵ n)`. -/
theorem theorem_4_7 {ε c : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {n T : ℕ} (hn : 2 ≤ n)
    (hT : (T : ℝ) ≤ c * (Nat.log 2 n : ℝ) ^ 4) :
    (asmRounds (kOf ε) (ellOf ε) (Nat.log 2 n) T : ℝ) ≤
      2610 * (3 + c) * ε⁻¹ ^ 3 * (Nat.log 2 n : ℝ) ^ 5 := by
  set lg := (Nat.log 2 n : ℝ)
  have hlg : (1 : ℝ) ≤ lg := by
    have : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
    simp only [lg]; exact_mod_cast this
  have hεi : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.2 hε1
  set e := ε⁻¹
  have hK : (kOf ε : ℝ) ≤ 9 * e := by
    have := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 8 / ε)).le
    unfold kOf; rw [div_eq_mul_inv] at this ⊢; linarith
  have hk0 : (0 : ℝ) ≤ kOf ε := by positivity
  have hL : (ellOf ε : ℝ) ≤ 145 * e ^ 2 := by
    have := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 16 * kOf ε / ε)).le
    unfold ellOf
    have h1 : 16 * (kOf ε : ℝ) / ε ≤ 144 * e ^ 2 := by
      rw [div_eq_mul_inv]; nlinarith
    nlinarith
  have hP : (prRounds T : ℝ) ≤ (3 + c) * lg ^ 4 := by
    unfold prRounds; push_cast
    have : (1 : ℝ) ≤ lg ^ 4 := one_le_pow₀ hlg
    nlinarith
  have hO : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 2 * lg := by push_cast; linarith
  unfold asmRounds
  push_cast
  have hl0 : (0 : ℝ) ≤ ellOf ε := by positivity
  have hp0 : (0 : ℝ) ≤ prRounds T := by positivity
  calc ((Nat.log 2 n : ℝ) + 1) * ((ellOf ε : ℝ) * ((kOf ε : ℝ) * (prRounds T : ℝ)))
      ≤ (2 * lg) * ((145 * e ^ 2) * ((9 * e) * ((3 + c) * lg ^ 4))) := by
        have h1 : (kOf ε : ℝ) * (prRounds T : ℝ) ≤ (9 * e) * ((3 + c) * lg ^ 4) :=
          mul_le_mul hK hP hp0 (by positivity)
        have h2 : (ellOf ε : ℝ) * ((kOf ε : ℝ) * (prRounds T : ℝ)) ≤
            (145 * e ^ 2) * ((9 * e) * ((3 + c) * lg ^ 4)) :=
          mul_le_mul hL h1 (by positivity) (by positivity)
        exact mul_le_mul (by push_cast at hO; linarith) h2 (by positivity) (by positivity)
    _ = 2610 * (3 + c) * e ^ 3 * lg ^ 5 := by ring

/-- **Theorem 4.7**, for the instrumented run of `ASM(P, ε, n)`: it computes the output of
`ASM`, and if the subroutine `mm` uses `mm.rounds ≤ c log⁴ n` rounds per call, its round counter
(`3` rounds per `ProposalRound` plus the subroutine) is at most `2610 (3 + c) ε⁻³ log⁵ n`. -/
theorem theorem_4_7_run (mm : MMOracle M W) {ε c : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {n : ℕ}
    (hn : 2 ≤ n) (hT : (mm.rounds : ℝ) ≤ c * (Nat.log 2 n : ℝ) ^ 4) :
    (P.stageC (kOf ε) mm (ellOf ε) (Nat.log 2 n + 1)).1 = P.ASM mm ε n ∧
      ((P.stageC (kOf ε) mm (ellOf ε) (Nat.log 2 n + 1)).2 : ℝ) ≤
        2610 * (3 + c) * ε⁻¹ ^ 3 * (Nat.log 2 n : ℝ) ^ 5 := by
  rw [stageC_asm]
  exact ⟨rfl, theorem_4_7 hε hε1 hn hT⟩

/-- Non-vacuity: a maximal-matching subroutine exists (for any round bound). -/
theorem exists_mmOracle (T : ℕ) : ∃ mm : MMOracle M W, mm.rounds = T :=
  ⟨⟨fun G => (exists_maximal G).choose, fun G => (exists_maximal G).choose_spec, T⟩, rfl⟩

end Prefs

end Papers.PODC2015.AlmostStableMatchings
