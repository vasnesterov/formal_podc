import Papers.PODC2012.IterativeApproxBC.Algorithm
import Cslib.Computability.Distributed.ApproxConsensus.Contraction

/-!
# Convergence of Algorithm 1 (Claims 1–3, Lemma 5, Theorem 3 of [VTL12])

Throughout, `x` is a run of Algorithm 1 with any tie-breaking (`IsRun G (alg1Step G f) S x`) with
at most `f` faulty nodes, and every node has `≥ 2f + 1` in-neighbours if `f > 0` (Corollary 3).
`α` is any number with `0 ≤ α ≤ 1` and `α ≤ a_i` for all `i` (the paper's `α = min_i a_i`,
`alpha G f` below, is the best choice).

Instead of the exact extremes `U[s] = max`, `μ[s] = min` of the fault-free states we work with
arbitrary bounds `lo ≤ x s j ≤ hi` (`j ∉ F`); the paper's statements are the special case
`lo = μ[s]`, `hi = U[s]`.

* `claim1`, `claim3` (= Claim 4 of the appendix) — the inductive bounds along a propagating
  sequence; `lemma5` — contraction by `1 - α^l / 2` after `l` steps.
* `contraction` — one phase of Theorem 3: after `n = |V|` iterations the spread shrinks by
  `γ = 1 - α^n / 2` (uses Lemma 2).
* `alg1_spread_le` — explicit rate `|x t i - x t j| ≤ γ^⌊t/n⌋ (hi - lo)`.
* `alg1_converges` — **Theorem 3** (convergence); `alg1_tendsto` — all fault-free states converge
  to one common limit.
-/

open Finset Cslib.ApproxConsensus Filter Topology

namespace IterativeApproxBC

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} {f : ℕ}
  {S : Scenario V} {x : ℕ → V → ℝ}

/-- The paper's `α = min_i a_i` (equation (3)). -/
noncomputable def alpha (G : Digraph V) (f : ℕ) : ℝ := ⨅ i, weight G f i

theorem alpha_le_weight (i : V) : alpha G f ≤ weight G f i :=
  ciInf_le (Set.finite_range _).bddBelow i

theorem alpha_pos [Nonempty V] : 0 < alpha G f := by
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := weight G f)
  rw [alpha, ← hi]; exact weight_pos i

theorem weight_le_one (i : V) : weight G f i ≤ 1 := by
  unfold weight; apply inv_le_one_of_one_le₀
  have : (0 : ℝ) ≤ ((#(inNbrs G i) - 2 * f : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

theorem alpha_le_one [Nonempty V] : alpha G f ≤ 1 :=
  (alpha_le_weight (Classical.arbitrary V)).trans (weight_le_one _)

section Run

variable (hx : IsRun G (alg1Step G f) S x) (hF : #S.F ≤ f)
  (hdeg : 0 < f → ∀ i, 2 * f + 1 ≤ #(inNbrs G i))
include hx hF

/-- Bounds on the fault-free states persist (validity). -/
theorem bounds_persist {s : ℕ} {lo hi : ℝ} (hb : ∀ j ∉ S.F, lo ≤ x s j ∧ x s j ≤ hi) :
    ∀ τ, ∀ j ∉ S.F, lo ≤ x (s + τ) j ∧ x (s + τ) j ≤ hi := fun τ j hj => by
  obtain ⟨⟨k, hk, h₁⟩, ⟨k', hk', h₂⟩⟩ := (alg1_validStep hx hF).hull_from s τ j hj
  exact ⟨(hb k hk).1.trans h₁, h₂.trans (hb k' hk').2⟩

include hdeg in
/-- **Claim 1** of [VTL12]: along the propagating sequence `R_τ` of `R` (inside the fault-free set
`X`), `x (s + τ) i - lo ≥ α^τ (m - lo)` for `i ∈ R_τ`, where `lo ≤ m ≤ x s j` for `j ∈ R`. -/
theorem claim1 {α : ℝ} (hα0 : 0 ≤ α) (hα : ∀ i, α ≤ weight G f i) {s : ℕ} {lo m : ℝ}
    (hlo : ∀ j ∉ S.F, lo ≤ x s j) {R : Finset V} (hR : R ⊆ univ \ S.F) (hlom : lo ≤ m)
    (hm : ∀ j ∈ R, m ≤ x s j) :
    ∀ τ, ∀ i ∈ (propStep G f (univ \ S.F))^[τ] R, α ^ τ * (m - lo) ≤ x (s + τ) i - lo := by
  have hpers : ∀ τ, ∀ j ∉ S.F, lo ≤ x (s + τ) j := by
    intro τ j hj
    exact (bounds_persist hx hF (lo := lo) (hi := max (x s j) (univ.sup' ⟨j, mem_univ _⟩ (x s)))
      (fun k hk => ⟨hlo k hk, le_max_of_le_right (le_sup' _ (mem_univ k))⟩) τ j hj).1
  intro τ
  induction τ with
  | zero => intro i hi; simp only [Function.iterate_zero, id_eq] at hi; simp [hm i hi]
  | succ τ ih =>
    intro i hi
    rw [Function.iterate_succ_apply'] at hi
    set Rτ := (propStep G f (univ \ S.F))^[τ] R
    have hRτ : Rτ ⊆ univ \ S.F := propStep_iter_subset hR τ
    have hnn : 0 ≤ α ^ τ * (m - lo) := mul_nonneg (pow_nonneg hα0 τ) (by linarith)
    have hiX : i ∈ univ \ S.F := propStep_subset hRτ hi
    have hiF : i ∉ S.F := (mem_sdiff.mp hiX).2
    obtain ⟨-, hown, hP⟩ := alg1_lower_step hx hF (s + τ) hiF lo (hpers τ)
    have key : ∀ w, α ^ τ * (m - lo) ≤ w - lo →
        weight G f i * (w - lo) ≤ x (s + τ + 1) i - lo →
        α ^ (τ + 1) * (m - lo) ≤ x (s + (τ + 1)) i - lo := by
      intro w hw h
      rw [← Nat.add_assoc, pow_succ]
      calc α ^ τ * α * (m - lo) = α * (α ^ τ * (m - lo)) := by ring
        _ ≤ weight G f i * (α ^ τ * (m - lo)) :=
          mul_le_mul_of_nonneg_right (hα i) hnn
        _ ≤ weight G f i * (w - lo) := mul_le_mul_of_nonneg_left hw (weight_pos i).le
        _ ≤ _ := h
    rcases mem_union.mp hi with hi | hi
    · exact key _ (ih i hi) hown
    · obtain ⟨-, hc⟩ := mem_inArrow.mp hi
      obtain ⟨p, hp, hpw⟩ := hP (inNbrs G i ∩ Rτ)
        (fun y hy => mem_sdiff.mpr ⟨(mem_inter.mp hy).1, (mem_sdiff.mp (hRτ (mem_inter.mp hy).2)).2⟩)
        hc (fun h => hdeg h i)
      exact key _ (ih p (mem_inter.mp hp).2) hpw

include hdeg in
/-- **Claim 4** (appendix) / **Claim 3** of [VTL12]: the mirror image of `claim1`. -/
theorem claim3 {α : ℝ} (hα0 : 0 ≤ α) (hα : ∀ i, α ≤ weight G f i) {s : ℕ} {hi M : ℝ}
    (hhi : ∀ j ∉ S.F, x s j ≤ hi) {R : Finset V} (hR : R ⊆ univ \ S.F) (hMhi : M ≤ hi)
    (hM : ∀ j ∈ R, x s j ≤ M) :
    ∀ τ, ∀ i ∈ (propStep G f (univ \ S.F))^[τ] R, α ^ τ * (hi - M) ≤ hi - x (s + τ) i := by
  have hpers : ∀ τ, ∀ j ∉ S.F, x (s + τ) j ≤ hi := by
    intro τ j hj
    exact (bounds_persist hx hF (hi := hi) (lo := min (x s j) (univ.inf' ⟨j, mem_univ _⟩ (x s)))
      (fun k hk => ⟨min_le_of_right_le (inf'_le _ (mem_univ k)), hhi k hk⟩) τ j hj).2
  intro τ
  induction τ with
  | zero =>
    intro i hi; simp only [Function.iterate_zero, id_eq] at hi
    simp only [pow_zero, one_mul, Nat.add_zero]; linarith [hM i hi]
  | succ τ ih =>
    intro i hi'
    rw [Function.iterate_succ_apply'] at hi'
    set Rτ := (propStep G f (univ \ S.F))^[τ] R
    have hRτ : Rτ ⊆ univ \ S.F := propStep_iter_subset hR τ
    have hnn : 0 ≤ α ^ τ * (hi - M) := mul_nonneg (pow_nonneg hα0 τ) (by linarith)
    have hiX : i ∈ univ \ S.F := propStep_subset hRτ hi'
    have hiF : i ∉ S.F := (mem_sdiff.mp hiX).2
    obtain ⟨-, hown, hP⟩ := alg1_upper_step hx hF (s + τ) hiF hi (hpers τ)
    have key : ∀ w, α ^ τ * (hi - M) ≤ hi - w →
        weight G f i * (hi - w) ≤ hi - x (s + τ + 1) i →
        α ^ (τ + 1) * (hi - M) ≤ hi - x (s + (τ + 1)) i := by
      intro w hw h
      rw [← Nat.add_assoc, pow_succ]
      calc α ^ τ * α * (hi - M) = α * (α ^ τ * (hi - M)) := by ring
        _ ≤ weight G f i * (α ^ τ * (hi - M)) :=
          mul_le_mul_of_nonneg_right (hα i) hnn
        _ ≤ weight G f i * (hi - w) := mul_le_mul_of_nonneg_left hw (weight_pos i).le
        _ ≤ _ := h
    rcases mem_union.mp hi' with hi' | hi'
    · exact key _ (ih i hi') hown
    · obtain ⟨-, hc⟩ := mem_inArrow.mp hi'
      obtain ⟨p, hp, hpw⟩ := hP (inNbrs G i ∩ Rτ)
        (fun y hy => mem_sdiff.mpr ⟨(mem_inter.mp hy).1, (mem_sdiff.mp (hRτ (mem_inter.mp hy).2)).2⟩)
        hc (fun h => hdeg h i)
      exact key _ (ih p (mem_inter.mp hp).2) hpw

include hdeg in
/-- **Lemma 5** of [VTL12] (with arbitrary bounds `lo ≤ x s j ≤ hi` in place of `μ[s]`, `U[s]`):
if `R ⊆ X` propagates to the rest of the fault-free set `X` in `l` steps and the states of `R` lie
in an interval `[m, M] ⊆ [lo, hi]` of length `≤ (hi - lo)/2`, then after `l` iterations the
fault-free states lie in an interval `[lo', hi']` with `hi' - lo' ≤ (1 - α^l/2)(hi - lo)`. -/
theorem lemma5 {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hα : ∀ i, α ≤ weight G f i) {s l : ℕ}
    {lo hi m M : ℝ} (hb : ∀ j ∉ S.F, lo ≤ x s j ∧ x s j ≤ hi) {R : Finset V}
    (hR : R ⊆ univ \ S.F) (hl : (propStep G f (univ \ S.F))^[l] R = univ \ S.F)
    (hRb : ∀ j ∈ R, m ≤ x s j ∧ x s j ≤ M) (hlom : lo ≤ m) (hmM : m ≤ M) (hMhi : M ≤ hi)
    (hlen : M - m ≤ (hi - lo) / 2) :
    ∃ lo' hi', lo' ≤ hi' ∧ (∀ j ∉ S.F, lo' ≤ x (s + l) j ∧ x (s + l) j ≤ hi') ∧
      hi' - lo' ≤ (1 - α ^ l / 2) * (hi - lo) := by
  have c1 := claim1 hx hF hdeg hα0 hα (fun j hj => (hb j hj).1) hR hlom (fun j hj => (hRb j hj).1) l
  have c3 := claim3 hx hF hdeg hα0 hα (fun j hj => (hb j hj).2) hR hMhi (fun j hj => (hRb j hj).2) l
  rw [hl] at c1 c3
  have hal0 : 0 ≤ α ^ l := pow_nonneg hα0 l
  have hal1 : α ^ l ≤ 1 := pow_le_one₀ hα0 hα1
  refine ⟨lo + α ^ l * (m - lo), hi - α ^ l * (hi - M), ?_, fun j hj => ?_, ?_⟩
  · nlinarith
  · have := c1 j (by simpa using hj); have := c3 j (by simpa using hj)
    constructor <;> linarith
  · nlinarith

include hdeg in
/-- One phase of the proof of **Theorem 3** of [VTL12]: if `G` satisfies the condition, then after
`n = |V|` iterations the interval containing the fault-free states shrinks by `1 - α^n/2`. (The
paper uses the actual propagation length `l(s) ≤ n - f - 1`; we use the uniform bound `n`.) -/
theorem contraction (hG : Condition G f) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hα : ∀ i, α ≤ weight G f i) {s : ℕ} {lo hi : ℝ} (hlohi : lo ≤ hi)
    (hb : ∀ j ∉ S.F, lo ≤ x s j ∧ x s j ≤ hi) :
    ∃ lo' hi', lo' ≤ hi' ∧ (∀ j ∉ S.F, lo' ≤ x (s + Fintype.card V) j ∧
      x (s + Fintype.card V) j ≤ hi') ∧
      hi' - lo' ≤ (1 - α ^ Fintype.card V / 2) * (hi - lo) := by
  classical
  set X := univ \ S.F
  set A := X.filter (fun i => x s i < (lo + hi) / 2)
  set B := X.filter (fun i => ¬ x s i < (lo + hi) / 2)
  have hAX : A ⊆ X := filter_subset _ _
  have hBX : B ⊆ X := filter_subset _ _
  have hAB : A ∪ B = X := filter_union_filter_not_eq _ _
  have hFA : Disjoint S.F A := disjoint_sdiff.mono_right hAX
  have hFB : Disjoint S.F B := disjoint_sdiff.mono_right hBX
  have hU : S.F ∪ A ∪ B = univ := by rw [union_assoc, hAB, union_sdiff_of_subset (subset_univ _)]
  -- a set propagating to the rest of `X` does so in `n` steps
  have hfull : ∀ T ⊆ X, (propStep G f X)^[#X] T = X →
      (propStep G f X)^[Fintype.card V] T = X := fun T hT h =>
    subset_antisymm (propStep_iter_subset hT _)
      (h.symm.subset.trans (propStep_iter_mono_right _ _ (card_le_univ X)))
  rcases hG.propagates_or hF hFA hFB hU with h | h
  · rw [propagates_iff_iter_card, hAB] at h
    exact lemma5 hx hF hdeg hα0 hα1 hα hb hAX (hfull A hAX h)
      (fun j hj => ⟨(hb j (mem_sdiff.mp (hAX hj)).2).1, (mem_filter.mp hj).2.le⟩)
      le_rfl (by linarith) (by linarith) (by linarith)
  · rw [propagates_iff_iter_card, union_comm, hAB] at h
    exact lemma5 hx hF hdeg hα0 hα1 hα hb hBX (hfull B hBX h)
      (fun j hj => ⟨not_lt.mp (mem_filter.mp hj).2, (hb j (mem_sdiff.mp (hBX hj)).2).2⟩)
      (by linarith) (by linarith) le_rfl (by linarith)

include hdeg in
/-- Explicit convergence rate (Theorem 3 of [VTL12], quantitative form): if the fault-free inputs
lie in `[lo, hi]`, then at time `t` all fault-free states are within
`(1 - α^n/2)^⌊t/n⌋ (hi - lo)` of each other (`n = |V|`). -/
theorem alg1_spread_le (hG : Condition G f) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hα : ∀ i, α ≤ weight G f i) {lo hi : ℝ} (hlohi : lo ≤ hi)
    (hb : ∀ j ∉ S.F, lo ≤ S.input j ∧ S.input j ≤ hi) (t : ℕ) :
    ∀ i ∉ S.F, ∀ j ∉ S.F,
      |x t i - x t j| ≤ (1 - α ^ Fintype.card V / 2) ^ (t / Fintype.card V) * (hi - lo) := by
  set n := Fintype.card V
  set γ := 1 - α ^ n / 2
  have hγ : 0 ≤ γ := by have := pow_le_one₀ hα0 hα1 (n := n); simp only [γ]; linarith
  have phase := exists_sub_le_pow_mul_of_step
    (P := fun k lo' hi' => lo' ≤ hi' ∧ ∀ j ∉ S.F, lo' ≤ x (n * k) j ∧ x (n * k) j ≤ hi') hγ
    ⟨hlohi, by simpa [hx.1] using hb⟩ fun k lo' hi' ⟨hle, hb'⟩ => by
      obtain ⟨lo'', hi'', hle', hb'', hd'⟩ := contraction hx hF hdeg hG hα0 hα1 hα hle hb'
      exact ⟨lo'', hi'', ⟨hle', by rwa [Nat.mul_succ]⟩, hd'⟩
  obtain ⟨lo', hi', ⟨-, hb'⟩, hd⟩ := phase (t / n)
  have hb'' := bounds_persist hx hF hb' (t % n)
  rw [Nat.div_add_mod] at hb''
  intro i hi j hj
  have := hb'' i hi; have := hb'' j hj
  rw [abs_le]; constructor <;> linarith

include hdeg in
/-- **Theorem 3** of [VTL12]: if `G` satisfies the condition, Algorithm 1 (with any tie-breaking)
converges: `U[t] - μ[t] → 0`. -/
theorem alg1_converges (hG : Condition G f) [Nonempty V] : Converges S.F x := by
  set n := Fintype.card V
  have hn : 0 < n := Fintype.card_pos
  set α := alpha G f
  have hα0 : 0 < α := alpha_pos
  have hα1 : α ≤ 1 := alpha_le_one
  set c := ∑ j, |S.input j|
  have hb : ∀ j ∉ S.F, -c ≤ S.input j ∧ S.input j ≤ c := fun j _ => by
    have := single_le_sum (f := fun j => |S.input j|) (fun _ _ => abs_nonneg _) (mem_univ j)
    exact abs_le.mp this
  have hc : -c ≤ c := by have := sum_nonneg (fun j (_ : j ∈ univ) => abs_nonneg (S.input j)); linarith
  set γ := 1 - α ^ n / 2
  have hγ0 : 0 ≤ γ := by have := pow_le_one₀ hα0.le hα1 (n := n); simp only [γ]; linarith
  have hγ1 : γ < 1 := by have := pow_pos hα0 n; simp only [γ]; linarith
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (c - -c + 1) by
    apply div_pos hε; linarith) hγ1
  refine ⟨n * k, fun t ht i hi j hj => ?_⟩
  have h := alg1_spread_le hx hF hdeg hG hα0.le hα1 alpha_le_weight hc hb t i hi j hj
  have hkt : k ≤ t / n := (Nat.le_div_iff_mul_le hn).mpr (by linarith [Nat.mul_comm n k])
  have h2 : γ ^ (t / n) ≤ γ ^ k := pow_le_pow_of_le_one hγ0 hγ1.le hkt
  have hpos : 0 < c - -c + 1 := by linarith
  have h3 : γ ^ k * (c - -c) ≤ ε := by
    rw [lt_div_iff₀ hpos] at hk
    nlinarith [pow_nonneg hγ0 k]
  calc |x t i - x t j| ≤ γ ^ (t / n) * (c - -c) := h
    _ ≤ γ ^ k * (c - -c) := mul_le_mul_of_nonneg_right h2 (by linarith)
    _ ≤ ε := h3

end Run

end IterativeApproxBC
