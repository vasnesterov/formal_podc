import Mathlib

/-!
# Lemma 3.1, corrected

Klasing, Kosowski, Pająk, Sauerwald, PODC 2013, Lemma 3.1, with identity (4) corrected to
`a_i / a₁ = 2/a_i - 1/a_{i-1} - 1/a_{i+1}` (the printed `a_i · a₁ = …` is contradictory, see
`Podc.RotorRouterRing.lemma_3_1_false`).

## Proof

Following the paper, for `c > 0` let `b₀ = 0`, `b₁ = c`, `b_{i+1} = 2 b_i - b_{i-1} - 1/b_i`
(`L31C.b`), and `D_i = b_{i+1} - b_i = c - Σ_{j=1}^i 1/b_j` (`L31C.D`). Let `P c` say that
`D_0, …, D_k > 0`.

* If `4 H_k ≤ c²` then `b_j ≥ j c / 2` and `D_j ≥ c/2` for `j ≤ k`, so `P c` (`L31C.lower`).
* If `D_0, …, D_{k-1} > 0` and `D_k ≥ 0` then `H_k ≤ c²` (since `b_j ≤ j c`); in particular
  `¬ P 1` (`L31C.harm_le_sq`).
* Let `c* = sup {c ∈ [1, C] | ¬ P c}` for `C` large. For `c ∈ (c*, C]`, `P c` holds, which gives
  `b_j(c) ≥ 1/C` for `1 ≤ j ≤ k`; since each `b_j` is continuous at `c*` as long as the earlier `b`'s
  do not vanish, `b_j(c*) ≥ 1/C` and `D_j(c*) ≥ 0`; `D_j(c*) > 0` for `j < k` since `D` strictly
  decreases. If `D_k(c*) > 0` then `P` holds on a neighbourhood of `c*`, contradicting the choice
  of `c*`. Hence `D_k(c*) = 0`, i.e. `b_{k+1} = b_k` and `c* = Σ_{j=1}^k 1/b_j`.
* `a_i = 1/(c* b_i)` satisfies (1)–(6), with `a₁ = 1/c*²`.

The paper's continuity argument ("the `b_i` are continuous in `c`") is made precise by the
right-limit argument above.
-/

open Finset Filter Topology

namespace Podc.RotorRouterRing

/-- The harmonic number `H_k = Σ_{j=1}^k 1/j`. -/
noncomputable def harm (k : ℕ) : ℝ := ∑ j ∈ Icc 1 k, (1 : ℝ) / j

namespace L31C

/-- Pairs `(b_i, b_{i+1})` of the recursion `b₀ = 0`, `b₁ = c`, `b_{i+2} = 2 b_{i+1} - b_i - 1/b_{i+1}`. -/
noncomputable def bseq (c : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, c)
  | i + 1 => ((bseq c i).2, 2 * (bseq c i).2 - (bseq c i).1 - 1 / (bseq c i).2)

/-- The sequence `b_i` of the paper's proof (as a function of `c = b₁`). -/
noncomputable def b (c : ℝ) (i : ℕ) : ℝ := (bseq c i).1

/-- The differences `D_i = b_{i+1} - b_i` (`d_{i+1}` in the paper). -/
noncomputable def D (c : ℝ) (i : ℕ) : ℝ := b c (i + 1) - b c i

lemma bseq_snd (c : ℝ) (i : ℕ) : (bseq c i).2 = b c (i + 1) := rfl

@[simp] lemma b_zero (c : ℝ) : b c 0 = 0 := rfl

@[simp] lemma b_one (c : ℝ) : b c 1 = c := rfl

lemma b_succ_succ (c : ℝ) (i : ℕ) :
    b c (i + 2) = 2 * b c (i + 1) - b c i - 1 / b c (i + 1) := rfl

@[simp] lemma D_zero (c : ℝ) : D c 0 = c := by simp [D]

lemma D_succ (c : ℝ) (i : ℕ) : D c (i + 1) = D c i - 1 / b c (i + 1) := by
  simp only [D, b_succ_succ]; ring

lemma b_succ (c : ℝ) (i : ℕ) : b c (i + 1) = b c i + D c i := by simp [D]

lemma D_eq (c : ℝ) (i : ℕ) : D c i = c - ∑ j ∈ Icc 1 i, 1 / b c j := by
  induction i with
  | zero => simp
  | succ i ih => rw [D_succ, ih, sum_Icc_succ_top (by omega)]; ring

lemma harm_mono {i j : ℕ} (h : i ≤ j) : harm i ≤ harm j := by
  unfold harm
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h)
  intro x _ _; positivity

lemma harm_two_le {k : ℕ} (hk : 2 ≤ k) : 3 / 2 ≤ harm k := by
  have : harm 2 = 3 / 2 := by
    simp [harm, sum_Icc_succ_top]; norm_num
  linarith [harm_mono hk]

lemma harm_nonneg (k : ℕ) : 0 ≤ harm k := by
  unfold harm; apply sum_nonneg; intro x _; positivity

/-- If `D_j > 0` for `j < n`, then `b_j ≥ 0` for `j ≤ n`. -/
lemma b_nonneg {c : ℝ} {n : ℕ} (hD : ∀ j < n, 0 < D c j) : ∀ j ≤ n, 0 ≤ b c j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih => intro hj; rw [b_succ]; linarith [ih (by omega), hD j (by omega)]

lemma b_pos {c : ℝ} {n : ℕ} (hD : ∀ j < n, 0 < D c j) {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ n) :
    0 < b c j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [b_succ]; linarith [b_nonneg hD m (by omega), hD m (by omega)]

lemma D_le {c : ℝ} {n : ℕ} (hD : ∀ j < n, 0 < D c j) : ∀ j ≤ n, D c j ≤ c := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj; rw [D_succ]
    have := b_pos hD (j := j + 1) (by omega) hj
    have : 0 < 1 / b c (j + 1) := by positivity
    linarith [ih (by omega)]

lemma b_le {c : ℝ} {n : ℕ} (hD : ∀ j < n, 0 < D c j) : ∀ j ≤ n, b c j ≤ j * c := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj; rw [b_succ]; push_cast; linarith [ih (by omega), D_le hD j (by omega)]

/-- Upper bound on `H_k`: if `D_0, …, D_{k-1} > 0` and `D_k ≥ 0` then `H_k ≤ c²`. -/
lemma harm_le_sq {c : ℝ} {k : ℕ} (hc : 0 < c) (hD : ∀ j < k, 0 < D c j) (hDk : 0 ≤ D c k) :
    harm k ≤ c ^ 2 := by
  have hsum : harm k / c ≤ ∑ j ∈ Icc 1 k, 1 / b c j := by
    rw [harm, sum_div]
    apply sum_le_sum
    intro j hj
    simp only [mem_Icc] at hj
    have hb := b_pos hD hj.1 hj.2
    have := b_le hD j hj.2
    rw [div_div]
    exact one_div_le_one_div_of_le hb this
  rw [D_eq] at hDk
  have : harm k / c ≤ c := by linarith
  rw [div_le_iff₀ hc] at this; nlinarith

lemma D_ge_half {c : ℝ} (hc : 0 < c) {i j : ℕ} (h : 4 * harm i ≤ c ^ 2) (hj : j ≤ i)
    (hb : ∀ l ≤ j, l * c / 2 ≤ b c l) : c / 2 ≤ D c j := by
  have h1 : ∑ l ∈ Icc 1 j, 1 / b c l ≤ 2 / c * harm j := by
    rw [harm, mul_sum]; apply sum_le_sum; intro l hl
    simp only [mem_Icc] at hl
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.1
    have := hb l hl.2
    calc 1 / b c l ≤ 1 / (l * c / 2) := one_div_le_one_div_of_le (by positivity) this
      _ = 2 / c * (1 / l) := by field_simp
  have h2 : 2 / c * harm j ≤ 2 / c * harm i :=
    mul_le_mul_of_nonneg_left (harm_mono hj) (by positivity)
  have h3 : 2 / c * harm i ≤ c / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hc two_pos]; nlinarith
  rw [D_eq]; linarith

/-- Lower bound: if `4 H_i ≤ c²` then `b_l ≥ l c / 2` for `l ≤ i + 1`. -/
lemma lower {c : ℝ} (hc : 0 < c) {i : ℕ} (h : 4 * harm i ≤ c ^ 2) :
    ∀ j ≤ i + 1, ∀ l ≤ j, l * c / 2 ≤ b c l := by
  intro j
  induction j with
  | zero => intro _ l hl; obtain rfl : l = 0 := by omega
            simp
  | succ j ih =>
    intro hj l hl
    rcases Nat.lt_or_ge l (j + 1) with hl' | hl'
    · exact ih (by omega) l (by omega)
    obtain rfl : l = j + 1 := by omega
    have hD := D_ge_half hc h (by omega) (ih (by omega))
    rw [b_succ]; push_cast
    linarith [ih (by omega) j le_rfl]

/-- If `4 H_k ≤ c²` (and `c > 0`) then `D_j ≥ c / 2` for all `j ≤ k`. -/
lemma D_ge_half_of {c : ℝ} (hc : 0 < c) {k : ℕ} (h : 4 * harm k ≤ c ^ 2) {j : ℕ} (hj : j ≤ k) :
    c / 2 ≤ D c j :=
  D_ge_half hc h hj (lower hc h j (by omega))

/-- `c ↦ (b_i, b_{i+1})` is continuous at `c₀` provided `b_1, …, b_i` do not vanish at `c₀`. -/
lemma bseq_continuousAt (c₀ : ℝ) : ∀ i, (∀ j, 1 ≤ j → j ≤ i → b c₀ j ≠ 0) →
    ContinuousAt (fun c => bseq c i) c₀ := by
  intro i
  induction i with
  | zero => intro _; exact (continuous_const.prodMk continuous_id).continuousAt
  | succ i ih =>
    intro h
    have hi := ih (fun j h1 h2 => h j h1 (by omega))
    have h2 : ContinuousAt (fun c => (bseq c i).2) c₀ := hi.snd
    have h1 : ContinuousAt (fun c => (bseq c i).1) c₀ := hi.fst
    have hne : (bseq c₀ i).2 ≠ 0 := h (i + 1) (by omega) le_rfl
    show ContinuousAt
      (fun c => ((bseq c i).2, 2 * (bseq c i).2 - (bseq c i).1 - 1 / (bseq c i).2)) c₀
    exact h2.prodMk (((continuousAt_const.mul h2).sub h1).sub (continuousAt_const.div h2 hne))

lemma b_continuousAt {c₀ : ℝ} {i : ℕ} (h : ∀ j, 1 ≤ j → j < i → b c₀ j ≠ 0) :
    ContinuousAt (fun c => b c i) c₀ := by
  cases i with
  | zero => exact continuousAt_const
  | succ m => exact (bseq_continuousAt c₀ m (fun j h1 h2 => h j h1 (by omega))).snd

lemma D_continuousAt {c₀ : ℝ} {i : ℕ} (h : ∀ j, 1 ≤ j → j ≤ i → b c₀ j ≠ 0) :
    ContinuousAt (fun c => D c i) c₀ :=
  (b_continuousAt (fun j h1 h2 => h j h1 (by omega))).sub
    (b_continuousAt (fun j h1 h2 => h j h1 (by omega)))

/-- A lower bound valid on `(x, C]` passes to `x` by continuity at `x`. -/
lemma le_of_right {f : ℝ → ℝ} {x C m : ℝ} (hf : ContinuousAt f x) (hxC : x < C)
    (h : ∀ c, x < c → c ≤ C → m ≤ f c) : m ≤ f x := by
  have : Tendsto f (𝓝[>] x) (𝓝 (f x)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto this
  filter_upwards [Ioo_mem_nhdsGT hxC] with c hc using h c hc.1 hc.2.le

/-- The key step: there is `c ≥ 1` with `D_0, …, D_{k-1} > 0` and `D_k = 0`. -/
lemma exists_root {k : ℕ} (hk : 2 ≤ k) :
    ∃ c, 1 ≤ c ∧ (∀ j < k, 0 < D c j) ∧ D c k = 0 := by
  set P : ℝ → Prop := fun c => ∀ j ∈ range (k + 1), 0 < D c j with hP
  set C0 : ℝ := 2 * harm k + 1 with hC0
  have hH := harm_two_le hk
  have hPbig : ∀ c, C0 ≤ c → P c := by
    intro c hc j hj
    have hc0 : 0 < c := by linarith
    have h4 : 4 * harm k ≤ c ^ 2 := by nlinarith
    have := D_ge_half_of hc0 h4 (j := j) (by simp at hj; omega)
    linarith
  have hP1 : ¬ P 1 := by
    intro h
    have := harm_le_sq one_pos (fun j hj => h j (by simp; omega)) (h k (by simp)).le
    linarith
  set A : Set ℝ := {c | 1 ≤ c ∧ ¬ P c} with hA
  have hA1 : (1 : ℝ) ∈ A := ⟨le_rfl, hP1⟩
  have hAbdd : ∀ a ∈ A, a < C0 := fun a ha => by
    by_contra h; exact ha.2 (hPbig a (not_lt.1 h))
  have hBdd : BddAbove A := ⟨C0, fun a ha => (hAbdd a ha).le⟩
  set cs := sSup A with hcs
  have hcs1 : 1 ≤ cs := le_csSup hBdd hA1
  have hcsC : cs ≤ C0 := csSup_le ⟨1, hA1⟩ (fun a ha => (hAbdd a ha).le)
  set C : ℝ := C0 + 1 with hC
  have hCpos : 0 < C := by linarith
  have hPright : ∀ c, cs < c → P c := by
    intro c hc; by_contra h
    exact absurd (le_csSup hBdd ⟨by linarith, h⟩) (not_le.2 hc)
  have hbC : ∀ c, cs < c → c ≤ C → ∀ j, 1 ≤ j → j ≤ k → 1 / C ≤ b c j := by
    intro c hc hcC j h1 hj
    have hPc := hPright c hc
    have hD : ∀ j < k + 1, 0 < D c j := fun j hj => hPc j (by simpa using hj)
    have hD' : ∀ j < k, 0 < D c j := fun j hj => hD j (by omega)
    have hb := b_pos hD' h1 hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have h2 := hD (m + 1) (by omega)
    rw [D_succ] at h2
    have h3 := D_le hD' m (by omega)
    have h4 : 1 / b c (m + 1) < C := by linarith
    rw [div_lt_iff₀ hb] at h4
    rw [div_le_iff₀ hCpos]; linarith [mul_comm C (b c (m + 1))]
  have hbcs : ∀ j ≤ k, ∀ l, 1 ≤ l → l ≤ j → 1 / C ≤ b cs l := by
    intro j
    induction j with
    | zero => intro _ l h1 h2; omega
    | succ j ih =>
      intro hj l h1 hl
      rcases Nat.lt_or_ge l (j + 1) with hl' | hl'
      · exact ih (by omega) l h1 (by omega)
      obtain rfl : l = j + 1 := by omega
      have hcont : ContinuousAt (fun c => b c (j + 1)) cs := b_continuousAt (fun l h1 h2 =>
        ne_of_gt (lt_of_lt_of_le (by positivity) (ih (by omega) l h1 (by omega))))
      exact le_of_right hcont (show cs < C by linarith)
        (fun c hc hcC => hbC c hc hcC (j + 1) (by omega) hj)
  have hbpos : ∀ l, 1 ≤ l → l ≤ k → 0 < b cs l := fun l h1 h2 =>
    lt_of_lt_of_le (by positivity) (hbcs k le_rfl l h1 h2)
  have hDcont : ∀ j ≤ k, ContinuousAt (fun c => D c j) cs := fun j hj =>
    D_continuousAt (fun l h1 h2 => (hbpos l h1 (by omega)).ne')
  have hDnn : ∀ j ≤ k, 0 ≤ D cs j := fun j hj => le_of_right (f := fun c => D c j) (hDcont j hj)
    (show cs < C by linarith) (fun c hc _ => (hPright c hc j (by simp; omega)).le)
  have hDpos : ∀ j < k, 0 < D cs j := by
    intro j hj
    have h1 := hDnn (j + 1) (by omega)
    rw [D_succ] at h1
    have h2 := hbpos (j + 1) (by omega) (by omega)
    have : 0 < 1 / b cs (j + 1) := by positivity
    linarith
  refine ⟨cs, hcs1, hDpos, ?_⟩
  by_contra hne
  have hk0 : 0 < D cs k := lt_of_le_of_ne (hDnn k le_rfl) (Ne.symm hne)
  have hev : ∀ᶠ c in 𝓝 cs, P c := by
    simp only [hP]
    rw [eventually_all_finset]
    intro j hj
    have hj' : j ≤ k := by simp at hj; omega
    have hpos : 0 < D cs j := by
      rcases Nat.lt_or_ge j k with h | h
      · exact hDpos j h
      · obtain rfl : j = k := by omega
        exact hk0
    exact (hDcont j hj').tendsto.eventually (lt_mem_nhds hpos)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have : cs ≤ cs - ε := csSup_le ⟨1, hA1⟩ (fun a ha => by
    by_contra h; rw [not_le] at h
    have hale : a ≤ cs := le_csSup hBdd ha
    exact ha.2 (hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)))
  linarith

end L31C

open L31C in
/-- **Lemma 3.1 of [Klasing, Kosowski, Pająk, Sauerwald, PODC 2013], with identity (4) corrected**
to `a_i / a₁ = 2/a_i - 1/a_{i-1} - 1/a_{i+1}` (the printed `a_i · a₁ = …` is contradictory, see
`lemma_3_1_false`). For every `k ≥ 2` there are positive `a₁, …, a_{k+1}` with
(2) `a_{k+1} = a_k < a_{k-1} < … < a₁`, (3) `Σ_{i=1}^k a_i = 1`, (4) the identity above for
`1 ≤ i ≤ k` (with (1) `a₀ = +∞` encoded as `1/a₀ = 0`), (5) `1/(4(H_k+1)) ≤ a₁ ≤ 1/H_k` and
(6) `a_i ≥ 1/(4 i (H_k+1))`. The paper states it for `k > 3`. -/
theorem lemma_3_1_corrected (k : ℕ) (hk : 2 ≤ k) :
    ∃ a : ℕ → ℝ, (∀ i ∈ Icc 1 (k + 1), 0 < a i) ∧ a (k + 1) = a k ∧
      (∀ i ∈ Ico 1 k, a (i + 1) < a i) ∧ (∑ i ∈ Icc 1 k, a i = 1) ∧
      (∀ i ∈ Icc 1 k,
        a i / a 1 = 2 / a i - (if i = 1 then 0 else 1 / a (i - 1)) - 1 / a (i + 1)) ∧
      1 / (4 * (harm k + 1)) ≤ a 1 ∧ a 1 ≤ 1 / harm k ∧
      ∀ i ∈ Icc 1 k, 1 / (4 * i * (harm k + 1)) ≤ a i := by
  obtain ⟨c, hc1, hD, hDk⟩ := exists_root hk
  have hc : 0 < c := by linarith
  have hbk : b c (k + 1) = b c k := by have := b_succ c k; rw [hDk] at this; linarith
  have hbpos : ∀ i, 1 ≤ i → i ≤ k + 1 → 0 < b c i := by
    intro i h1 h2
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact b_pos hD h1 (by omega)
    · obtain rfl : i = k + 1 := by omega
      rw [hbk]; exact b_pos hD (by omega) le_rfl
  have hble : ∀ i ≤ k, b c i ≤ i * c := b_le hD
  have hsum : ∑ j ∈ Icc 1 k, 1 / b c j = c := by rw [D_eq] at hDk; linarith
  have hH := harm_le_sq hc hD hDk.ge
  have hH4 : c ^ 2 < 4 * harm k := by
    by_contra h; rw [not_lt] at h
    have := D_ge_half_of hc h (le_refl k); rw [hDk] at this; linarith
  have hH0 := harm_two_le hk
  refine ⟨fun i => 1 / (c * b c i), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; simp only [mem_Icc] at hi; have := hbpos i hi.1 hi.2; positivity
  · simp only [hbk]
  · intro i hi; simp only [mem_Ico] at hi
    have h1 := hbpos i hi.1 (by omega)
    have h2 : b c i < b c (i + 1) := by rw [b_succ]; linarith [hD i hi.2]
    exact one_div_lt_one_div_of_lt (by positivity) (mul_lt_mul_of_pos_left h2 hc)
  · have : ∀ i, 1 / (c * b c i) = 1 / c * (1 / b c i) := fun i => by rw [one_div_mul_one_div]
    simp only [this, ← mul_sum, hsum]; field_simp
  · intro i hi; simp only [mem_Icc] at hi
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hif : (if m + 1 = 1 then (0 : ℝ) else 1 / (1 / (c * b c (m + 1 - 1)))) = c * b c m := by
      split_ifs with h
      · obtain rfl : m = 0 := by omega
        simp
      · simp
    have hrec : b c (m + 1 + 1) = 2 * b c (m + 1) - b c m - 1 / b c (m + 1) := b_succ_succ c m
    have hb1 := hbpos (m + 1) hi.1 (by omega)
    beta_reduce
    rw [hif]
    simp only [one_div_one_div, b_one, hrec]
    field_simp
    ring
  · simp only [b_one]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  · simp only [b_one]
    exact one_div_le_one_div_of_le (by linarith) (by nlinarith)
  · intro i hi; simp only [mem_Icc] at hi
    have hb := hbpos i hi.1 (by omega)
    have hi0 : (1 : ℝ) ≤ i := by exact_mod_cast hi.1
    have h1 : c * b c i ≤ c * (i * c) := mul_le_mul_of_nonneg_left (hble i hi.2) hc.le
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

end Podc.RotorRouterRing
