import Podc.Computability.Distributed.UniRing.Basic

/-!
# Fair leader election on an asynchronous unidirectional ring as a game (Section 2 of [YM18])

[YM18] A. Yifrach, Y. Mansour. *Fair Leader Election for Rational Agents in Asynchronous Rings and
Networks.* PODC 2018 (arXiv:1805.04778v2).

Processors `Fin n` sit on the asynchronous unidirectional ring of `Cslib.UniRing`. Each processor
terminates with an output in `Option (Fin n)` (`none` is `⊥`, abort). A *protocol* is a family of
strategy profiles `P ω` indexed by the joint randomness `ω : Ω` of the processors (a finite type with
the uniform distribution). An *adversarial deviation* (Def. 2.2) of a coalition `C` replaces the
strategies of the processors in `C` by arbitrary strategies `A`; we consider deterministic deviations
(the adversaries' strategies do not depend on `ω`), which is all that is needed for the negative
results of the paper and does not affect Lemma 2.4.

* `outcomeUnder P σ`: the outcome of the execution of profile `P` under the oblivious schedule `σ`
  (`some v` if all processors terminate with output `some v`, else `FAIL = none`); by
  `outcomeUnder_eq` it does not depend on the fair schedule and equals `outcome P`.
* `prob`, `expU`: probability of an outcome and expected utility over `ω`.
* `IsRational`, `IsFLE`, `IsResilient` (Def. 2.3), `IsUnbiased`; Lemma 2.4 is `lemma_2_4`.
-/

namespace Podc.FairLeaderElection

open Cslib.UniRing

variable {n : ℕ} [NeZero n] {M : Type*}

/-- Profiles of strategies with outputs `Option (Fin n)` (`none` = `⊥`). -/
abbrev Profile (n : ℕ) (M : Type*) := Fin n → Proc M (Option (Fin n))

/-- The outcome of a profile: `some v` if every processor terminates with output `v`, otherwise
`FAIL` (`none`). Schedule-free version, see `outcomeUnder_eq`. -/
noncomputable def outcome (P : Profile n M) : Option (Fin n) :=
  open Classical in
  if h : ∃ v, ∀ i, Terminates P i (some v) then some h.choose else none

/-- The outcome of the execution of profile `P` under the oblivious schedule `σ`. -/
noncomputable def outcomeUnder (P : Profile n M) (σ : ℕ → Fin n) : Option (Fin n) :=
  open Classical in
  if h : ∃ v, ∀ i, ∃ t, (P i).out (run P σ t i) = some (some v) then some h.choose else none

theorem outcome_eq_some {P : Profile n M} {v : Fin n} :
    outcome P = some v ↔ ∀ i, Terminates P i (some v) := by
  unfold outcome
  split_ifs with h
  · constructor
    · rintro hv; cases hv; exact h.choose_spec
    · intro hv
      have := (h.choose_spec 0).unique (hv 0)
      simp only [Option.some.injEq] at this
      rw [this]
  · simp only [reduceCtorEq, false_iff]
    intro hv; exact h ⟨v, hv⟩

/-- On a unidirectional ring the outcome does not depend on the (fair) schedule. -/
theorem outcomeUnder_eq (P : Profile n M) {σ : ℕ → Fin n} (hσ : Fair σ) :
    outcomeUnder P σ = outcome P := by
  have key : ∀ v, (∀ i, ∃ t, (P i).out (run P σ t i) = some (some v)) ↔
      ∀ i, Terminates P i (some v) := fun v => forall_congr' fun i => terminates_iff hσ
  unfold outcomeUnder outcome
  by_cases h : ∃ v, ∀ i, Terminates P i (some v)
  · have h' := (exists_congr key).mpr h
    rw [dif_pos h, dif_pos h']
    have e := ((key _).mp h'.choose_spec 0).unique (h.choose_spec 0)
    simp only [Option.some.injEq] at e
    rw [e]
  · rw [dif_neg h, dif_neg (fun h' => h ((exists_congr key).mp h'))]

variable {Ω : Type*} [Fintype Ω]

/-- Probability (over the uniform randomness `ω`) that the outcome is `o`. -/
noncomputable def prob (Q : Ω → Profile n M) (σ : ℕ → Fin n) (o : Option (Fin n)) : ℝ :=
  open Classical in
  ((Finset.univ.filter fun ω => outcomeUnder (Q ω) σ = o).card : ℝ) / Fintype.card Ω

/-- Expected utility. -/
noncomputable def expU (Q : Ω → Profile n M) (σ : ℕ → Fin n) (u : Option (Fin n) → ℝ) : ℝ :=
  (∑ ω, u (outcomeUnder (Q ω) σ)) / Fintype.card Ω

/-- Definition 2.1: a rational utility, `u : [n] ∪ {FAIL} → [0,1]` with `u FAIL = 0`. -/
def IsRational (u : Option (Fin n) → ℝ) : Prop := u none = 0 ∧ ∀ o, 0 ≤ u o ∧ u o ≤ 1

/-- Definition 2.2: the adversarial deviation of the coalition `C` playing the strategies `A`. -/
def deviate (P : Ω → Profile n M) (C : Finset (Fin n)) (A : Profile n M) (ω : Ω) : Profile n M :=
  fun i => if i ∈ C then A i else P ω i

/-- A fair leader election protocol: for every fair schedule, every processor is elected with
probability exactly `1/n`. -/
def IsFLE (P : Ω → Profile n M) : Prop :=
  ∀ σ, Fair σ → ∀ j : Fin n, prob P σ (some j) = 1 / n

/-- Definition 2.3: `P` is `ε`-`k`-resilient if for every schedule, every rational utilities, every
coalition of size `k` and every adversarial deviation, some member of the coalition does not gain
more than `ε` in expected utility. -/
def IsResilient (P : Ω → Profile n M) (ε : ℝ) (k : ℕ) : Prop :=
  ∀ σ, Fair σ → ∀ u : Fin n → Option (Fin n) → ℝ, (∀ p, IsRational (u p)) →
    ∀ C : Finset (Fin n), C.card = k → ∀ A : Profile n M,
      ∃ p ∈ C, expU (deviate P C A) σ (u p) ≤ expU P σ (u p) + ε

/-- `P` is `ε`-`k`-unbiased: no coalition of size `k` raises the probability of any outcome above
`1/n + ε`. -/
def IsUnbiased (P : Ω → Profile n M) (ε : ℝ) (k : ℕ) : Prop :=
  ∀ σ, Fair σ → ∀ C : Finset (Fin n), C.card = k → ∀ (A : Profile n M) (j : Fin n),
    prob (deviate P C A) σ (some j) ≤ 1 / n + ε

theorem expU_eq_sum (Q : Ω → Profile n M) (σ : ℕ → Fin n) {u : Option (Fin n) → ℝ}
    (hu : u none = 0) : expU Q σ u = ∑ j : Fin n, prob Q σ (some j) * u (some j) := by
  classical
  unfold expU prob
  rw [← Finset.sum_fiberwise Finset.univ (fun ω => outcomeUnder (Q ω) σ)
    (fun ω => u (outcomeUnder (Q ω) σ)), Fintype.sum_option]
  have h0 : ∑ ω ∈ Finset.univ with outcomeUnder (Q ω) σ = none, u (outcomeUnder (Q ω) σ) = 0 :=
    Finset.sum_eq_zero fun ω hω => by rw [(Finset.mem_filter.mp hω).2, hu]
  rw [h0, zero_add, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => u (some j)) fun ω hω => by
    rw [(Finset.mem_filter.mp hω).2]]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

theorem prob_nonneg (Q : Ω → Profile n M) (σ : ℕ → Fin n) (o : Option (Fin n)) :
    0 ≤ prob Q σ o := by unfold prob; positivity

/-- **Lemma 2.4.** An `ε`-`k`-resilient FLE protocol is `ε`-`k`-unbiased, and (for `k ≥ 1`,
`ε ≥ 0`) an `ε`-`k`-unbiased FLE protocol is `nε`-`k`-resilient. -/
theorem lemma_2_4 (P : Ω → Profile n M) (hP : IsFLE P) (ε : ℝ) (k : ℕ) :
    (IsResilient P ε k → IsUnbiased P ε k) ∧
      (1 ≤ k → 0 ≤ ε → IsUnbiased P ε k → IsResilient P (n * ε) k) := by
  classical
  constructor
  · intro hR σ hσ C hC A j
    let u : Option (Fin n) → ℝ := fun o => if o = some j then 1 else 0
    have hu : IsRational u := ⟨by simp [u], fun o => by by_cases h : o = some j <;> simp [u, h]⟩
    obtain ⟨p, -, hp⟩ := hR σ hσ (fun _ => u) (fun _ => hu) C hC A
    have e1 : ∀ Q : Ω → Profile n M, expU Q σ u = prob Q σ (some j) := by
      intro Q
      rw [expU_eq_sum Q σ (by simp [u])]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [u, hb]) (by simp)]
      simp [u]
    rw [e1, e1, hP σ hσ j] at hp
    exact hp
  · intro hk hε hU σ hσ u hu C hC A
    obtain ⟨p, hp⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨p, hp, ?_⟩
    rw [expU_eq_sum _ σ (hu p).1, expU_eq_sum _ σ (hu p).1]
    have h1 : ∀ j : Fin n, prob (deviate P C A) σ (some j) * u p (some j) ≤
        prob P σ (some j) * u p (some j) + ε := by
      intro j
      rw [hP σ hσ j]
      have := hU σ hσ C hC A j
      have h0 := ((hu p).2 (some j)).1
      have h1 := ((hu p).2 (some j)).2
      nlinarith
    calc ∑ j, prob (deviate P C A) σ (some j) * u p (some j)
        ≤ ∑ j : Fin n, (prob P σ (some j) * u p (some j) + ε) := Finset.sum_le_sum fun j _ => h1 j
      _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem sum_prob_le_one (Q : Ω → Profile n M) (σ : ℕ → Fin n) :
    ∑ j : Fin n, prob Q σ (some j) ≤ 1 := by
  classical
  unfold prob
  rw [← Finset.sum_div]
  apply div_le_one_of_le₀ _ (by positivity)
  norm_cast
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro x _ h1 h2; exact hab (Option.some_injective _ (h1.symm.trans h2))

/-- Upper bound on any gain: for an FLE protocol, a rational utility and any profile family `Q`, the
gain `E_Q[u] - E_P[u]` is at most `1 - 1/n`. -/
theorem expU_le_add_one_sub (P : Ω → Profile n M) (hP : IsFLE P) {σ : ℕ → Fin n} (hσ : Fair σ)
    (Q : Ω → Profile n M) {u : Option (Fin n) → ℝ} (hu : IsRational u) :
    expU Q σ u ≤ expU P σ u + (1 - 1 / n) := by
  classical
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ (fun j : Fin n => u (some j))
    Finset.univ_nonempty
  have hQ : expU Q σ u ≤ u (some j0) := by
    rw [expU_eq_sum Q σ hu.1]
    calc ∑ j, prob Q σ (some j) * u (some j) ≤ ∑ j : Fin n, prob Q σ (some j) * u (some j0) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hj0 j (Finset.mem_univ _)) (prob_nonneg _ _ _)
      _ = (∑ j : Fin n, prob Q σ (some j)) * u (some j0) := by rw [Finset.sum_mul]
      _ ≤ 1 * u (some j0) :=
          mul_le_mul_of_nonneg_right (sum_prob_le_one Q σ) ((hu.2 _).1)
      _ = u (some j0) := one_mul _
  have hP' : u (some j0) / n ≤ expU P σ u := by
    rw [expU_eq_sum P σ hu.1]
    simp only [hP σ hσ]
    calc u (some j0) / n = 1 / n * u (some j0) := by ring
      _ ≤ ∑ j : Fin n, 1 / n * u (some j) :=
          Finset.single_le_sum (f := fun j : Fin n => 1 / (n : ℝ) * u (some j))
            (fun j _ => mul_nonneg (by positivity) (hu.2 _).1) (Finset.mem_univ j0)
  have h1 := (hu.2 (some j0)).2
  have : u (some j0) - u (some j0) / n ≤ 1 - 1 / n := by
    have : u (some j0) - u (some j0) / n = u (some j0) * (1 - 1 / n) := by ring
    rw [this]
    have : 0 ≤ 1 - 1 / (n : ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hn
    nlinarith
  linarith

/-- Every FLE protocol is `(1 - 1/n)`-`k`-resilient, for every `k ≥ 1`: no gain can exceed
`1 - 1/n`. (So the boundary case `ε = 1 - 1/n` of Corollary 4.6 is false.) -/
theorem isResilient_one_sub_inv (P : Ω → Profile n M) (hP : IsFLE P) {k : ℕ} (hk : 1 ≤ k) :
    IsResilient P (1 - 1 / n) k := by
  intro σ hσ u hu C hC A
  obtain ⟨p, hp⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨p, hp, expU_le_add_one_sub P hP hσ _ (hu p)⟩

end Podc.FairLeaderElection
