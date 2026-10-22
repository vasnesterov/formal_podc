import Podc.Foundations.Combinatorics.HypergraphCover

/-!
# Covering ILPs (Section 5: Lemma 5.2, Definition 5.4, Proposition 5.5, Claim 5.6)

A covering ILP `min wᵀx, Ax ≥ b, x ∈ ℕⁿ` with nonnegative `A, b, w`. Rows are indexed by a finite
type `R`, columns (variables) by a finite type `J`.

* Lemma 5.2 (zero-one programs → MWHVC): for every row `i` and every `S ⊆ [n]` whose indicator
  vector violates row `i`, add the hyperedge `σᵢ \ S` (`σᵢ` = support of row `i`). We prove that a
  set `T` meets every hyperedge iff `I_T` is feasible (`lemma_5_2_cover_iff`), that hyperedges are
  nonempty (`lemma_5_2_nonempty`), the rank bound `≤ f(A)` (`lemma_5_2_rank`) and the degree bound
  `≤ 2^{f(A)-1} Δ(A) < 2^{f(A)} Δ(A)` (`lemma_5_2_degree`). The stated rank bound `f' < f(A)` is
  false: `lemma_5_2_rank_false` (no reduction at all can achieve it on `x₁ ≥ 1`).
* Proposition 5.5 is false for non-integral `M` (`prop_5_5_false`: `2x ≥ 3`, `M = 3/2`); it holds
  with the box `[0, ⌈M⌉]ⁿ` (`prop_5_5_ceil`).
* Claim 5.6 (binary expansion): false as stated when `M < 1` (`claim_5_6_false`: `2x ≥ 1`,
  `⌈log₂ M + 1⌉ = 0`); its proof uses `B = ⌈log₂ M⌉` bits, which loses solutions when `M` is a power
  of two (`claim_5_6_proof_false`: `x ≥ 2`). With `B` bits where `⌈M⌉ < 2^B` (e.g.
  `B = ⌈log₂ M + 1⌉` for `M ≥ 1`) the reduction is correct (`claim_5_6`, `claim_5_6_bits`).
-/

set_option linter.unusedSectionVars false

namespace Podc.CoveringPrimalDual.ILP

open Finset

variable {R J : Type*} [Fintype R] [Fintype J] [DecidableEq J]

/-- Definition 5.1: the program is a covering program (all of `A`, `b`, `w` nonnegative). -/
def IsCovering (A : R → J → ℝ) (b : R → ℝ) (w : J → ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ (∀ i, 0 ≤ b i) ∧ ∀ j, 0 ≤ w j

/-- `x ∈ ℕⁿ` satisfies `A x ≥ b`. -/
def Feasible (A : R → J → ℝ) (b : R → ℝ) (x : J → ℕ) : Prop := ∀ i, b i ≤ ∑ j, A i j * x j

/-- The objective `wᵀ x`. -/
def cost (w : J → ℝ) (x : J → ℕ) : ℝ := ∑ j, w j * x j

/-- The zero-one vector `I_T` satisfies `A x ≥ b`. -/
def ZOFeasible (A : R → J → ℝ) (b : R → ℝ) (T : Finset J) : Prop := ∀ i, b i ≤ ∑ j ∈ T, A i j

/-- `σᵢ = {j | A i j ≠ 0}`. -/
noncomputable def supp (A : R → J → ℝ) (i : R) : Finset J := by
  classical exact univ.filter fun j => A i j ≠ 0

/-- `f(A)`: the maximum number of nonzero entries in a row. -/
noncomputable def fA (A : R → J → ℝ) : ℕ := univ.sup fun i => (supp A i).card

/-- `Δ(A)`: the maximum number of nonzero entries in a column. -/
noncomputable def ΔA (A : R → J → ℝ) : ℕ := by
  classical exact univ.sup fun j => (univ.filter fun i => A i j ≠ 0).card

theorem mem_supp {A : R → J → ℝ} {i : R} {j : J} : j ∈ supp A i ↔ A i j ≠ 0 := by
  classical simp [supp]

theorem sum_supp_eq {A : R → J → ℝ} (i : R) (T : Finset J) :
    ∑ j ∈ T ∩ supp A i, A i j = ∑ j ∈ T, A i j := by
  classical
  rw [← sum_filter_add_sum_filter_not T (· ∈ supp A i)]
  have h0 : ∑ j ∈ T.filter (· ∉ supp A i), A i j = 0 :=
    sum_eq_zero fun j hj => by
      have := (mem_filter.1 hj).2; rw [mem_supp] at this; push Not at this; exact this
  rw [h0, add_zero, filter_mem_eq_inter]

/-! ### Lemma 5.2 -/

/-- The hyperedges of the reduction of Lemma 5.2: `σᵢ \ S` for every row `i` and every `S ⊆ [n]`
with `Aᵢ · I_S < bᵢ`. -/
noncomputable def redEdges (A : R → J → ℝ) (b : R → ℝ) : Finset (Finset J) := by
  classical exact univ.biUnion fun i =>
    ((univ : Finset (Finset J)).filter fun S => ∑ j ∈ S, A i j < b i).image fun S => supp A i \ S

theorem mem_redEdges {A : R → J → ℝ} {b : R → ℝ} {e : Finset J} :
    e ∈ redEdges A b ↔ ∃ i S, ∑ j ∈ S, A i j < b i ∧ supp A i \ S = e := by
  classical simp [redEdges]

/-- Lemma 5.2, correctness: `T` is a vertex cover of the hypergraph iff `I_T` is a feasible
solution of the zero-one covering program. -/
theorem lemma_5_2_cover_iff {A : R → J → ℝ} (hA : ∀ i j, 0 ≤ A i j) (b : R → ℝ) (T : Finset J) :
    (∀ e ∈ redEdges A b, ∃ j ∈ e, j ∈ T) ↔ ZOFeasible A b T := by
  classical
  constructor
  · intro h i
    by_contra hlt
    push Not at hlt
    obtain ⟨j, hj, hjT⟩ := h _ (mem_redEdges.2 ⟨i, T, hlt, rfl⟩)
    exact (mem_sdiff.1 hj).2 hjT
  · intro h e he
    obtain ⟨i, S, hS, rfl⟩ := mem_redEdges.1 he
    by_contra hne
    push Not at hne
    -- `T ∩ σᵢ ⊆ S`, so `Aᵢ·I_T = Aᵢ·I_{T ∩ σᵢ} ≤ Aᵢ·I_S < bᵢ`
    have hsub : T ∩ supp A i ⊆ S := fun j hj => by
      obtain ⟨hjT, hjs⟩ := mem_inter.1 hj
      by_contra hjS; exact hne j (mem_sdiff.2 ⟨hjs, hjS⟩) hjT
    have := h i
    rw [← sum_supp_eq] at this
    have h2 := sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hA i j
    linarith

/-- Lemma 5.2: if the zero-one program is feasible, every hyperedge is nonempty. -/
theorem lemma_5_2_nonempty {A : R → J → ℝ} (hA : ∀ i j, 0 ≤ A i j) {b : R → ℝ}
    (hfeas : ∃ T, ZOFeasible A b T) {e : Finset J} (he : e ∈ redEdges A b) : e.Nonempty := by
  obtain ⟨T, hT⟩ := hfeas
  obtain ⟨j, hj, -⟩ := (lemma_5_2_cover_iff hA b T).2 hT e he
  exact ⟨j, hj⟩

/-- Lemma 5.2, rank: every hyperedge has at most `f(A)` vertices. -/
theorem lemma_5_2_rank {A : R → J → ℝ} {b : R → ℝ} {e : Finset J} (he : e ∈ redEdges A b) :
    e.card ≤ fA A := by
  obtain ⟨i, S, -, rfl⟩ := mem_redEdges.1 he
  exact (card_le_card sdiff_subset).trans (le_sup (f := fun i => (supp A i).card) (mem_univ i))

/-- Lemma 5.2, degree: every vertex lies in at most `2^{f(A)-1} · Δ(A)` hyperedges. -/
theorem lemma_5_2_degree_le (A : R → J → ℝ) (b : R → ℝ) (j : J) :
    ((redEdges A b).filter (j ∈ ·)).card ≤ ΔA A * 2 ^ (fA A - 1) := by
  classical
  have hsub : (redEdges A b).filter (j ∈ ·) ⊆
      (univ.filter fun i => A i j ≠ 0).biUnion fun i =>
        ((supp A i).erase j).powerset.image (insert j) := by
    intro e he
    obtain ⟨he, hje⟩ := mem_filter.1 he
    obtain ⟨i, S, -, rfl⟩ := mem_redEdges.1 he
    have hji : A i j ≠ 0 := mem_supp.1 (mem_sdiff.1 hje).1
    refine mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ _, hji⟩, mem_image.2 ⟨(supp A i \ S).erase j,
      mem_powerset.2 (erase_subset_erase _ sdiff_subset), insert_erase hje⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ i ∈ univ.filter (fun i => A i j ≠ 0), (((supp A i).erase j).powerset.image (insert j)).card
      ≤ ∑ _i ∈ univ.filter (fun i => A i j ≠ 0), 2 ^ (fA A - 1) := by
        refine sum_le_sum fun i hi => card_image_le.trans ?_
        rw [card_powerset]
        apply Nat.pow_le_pow_right (by norm_num)
        have h1 : j ∈ supp A i := mem_supp.2 (mem_filter.1 hi).2
        have h2 : (supp A i).card ≤ fA A := le_sup (f := fun i => (supp A i).card) (mem_univ i)
        rw [card_erase_of_mem h1]; omega
    _ = (univ.filter fun i => A i j ≠ 0).card * 2 ^ (fA A - 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ ΔA A * 2 ^ (fA A - 1) := by
        apply Nat.mul_le_mul_right
        unfold ΔA
        convert le_sup (f := fun j => (univ.filter fun i => A i j ≠ 0).card) (mem_univ j)

/-- Lemma 5.2, degree bound as stated: `Δ' < 2^{f(A)} · Δ(A)` (when `f(A), Δ(A) ≥ 1`). -/
theorem lemma_5_2_degree (A : R → J → ℝ) (b : R → ℝ) (hf : 1 ≤ fA A) (hΔ : 1 ≤ ΔA A) (j : J) :
    ((redEdges A b).filter (j ∈ ·)).card < 2 ^ fA A * ΔA A := by
  refine (lemma_5_2_degree_le A b j).trans_lt ?_
  rw [mul_comm]
  exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by norm_num) (by omega)) (by omega)

/-- Lemma 5.2 claims rank `f' < f(A)`; this is impossible already for the single constraint
`x₁ ≥ 1` (`f(A) = 1`): no hypergraph on the variables whose edges all have fewer than `f(A)`
vertices has exactly the feasible solutions as vertex covers. -/
theorem lemma_5_2_rank_false :
    let A : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    let b : Fin 1 → ℝ := fun _ => 1
    fA A = 1 ∧ ¬ ∃ H : Finset (Finset (Fin 1)), (∀ e ∈ H, e.card < fA A) ∧
      ∀ T, (∀ e ∈ H, ∃ j ∈ e, j ∈ T) ↔ ZOFeasible A b T := by
  intro A b
  have hf : fA A = 1 := by
    unfold fA
    have : ∀ i, (supp A i).card = 1 := fun i => by
      rw [card_eq_one]; exact ⟨0, by ext j; simp [mem_supp, A, Fin.fin_one_eq_zero j]⟩
    simp [this]
  refine ⟨hf, ?_⟩
  rintro ⟨H, hH, hcov⟩
  rw [hf] at hH
  by_cases hne : H.Nonempty
  · obtain ⟨e, he⟩ := hne
    have he0 : e = ∅ := card_eq_zero.1 (by have := hH e he; omega)
    have := (hcov {0}).2 (fun i => by simp [A, b])
    obtain ⟨j, hj, -⟩ := this e he
    simp [he0] at hj
  · rw [not_nonempty_iff_eq_empty] at hne
    have := (hcov ∅).1 (by simp [hne]) 0
    norm_num [b] at this

/-! ### Definition 5.4 and Proposition 5.5 -/

/-- Definition 5.4: `M` is `max_{i,j : A i j ≠ 0} bᵢ / A i j`. -/
def IsM (A : R → J → ℝ) (b : R → ℝ) (M : ℝ) : Prop :=
  (∀ i j, A i j ≠ 0 → b i / A i j ≤ M) ∧ ∃ i j, A i j ≠ 0 ∧ b i / A i j = M

/-- Proposition 5.5 ("limiting `x` to the box `[0, M]ⁿ` does not increase the optimal value of the
ILP") is false for non-integral `M`: for `2x ≥ 3`, `M = 3/2`, the ILP is feasible (`x = 2`) but no
integral point of `[0, 3/2]` is feasible. -/
theorem prop_5_5_false :
    let A : Fin 1 → Fin 1 → ℝ := fun _ _ => 2
    let b : Fin 1 → ℝ := fun _ => 3
    IsM A b (3 / 2) ∧ Feasible A b (fun _ => 2) ∧
      ¬ ∃ x : Fin 1 → ℕ, Feasible A b x ∧ ∀ j, (x j : ℝ) ≤ 3 / 2 := by
  intro A b
  refine ⟨⟨fun i j _ => by norm_num [A, b], 0, 0, by norm_num [A], by norm_num [A, b]⟩,
    fun i => by norm_num [A, b], ?_⟩
  rintro ⟨x, hx, hbox⟩
  have h1 := hx 0
  have h2 := hbox 0
  simp only [A, b, Finset.univ_unique, Fin.default_eq_zero, sum_singleton] at h1
  have : x 0 ≤ 1 := by
    have : (x 0 : ℝ) < 2 := by linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have : (x 0 : ℝ) ≤ 1 := by exact_mod_cast this
  linarith

/-- Proposition 5.5, corrected: with the box `[0, ⌈M⌉]ⁿ`, every feasible `x` can be capped to a
feasible `x' ≤ x` (hence of no larger cost) inside the box. Only `bᵢ ≤ A i j · M` for nonzero
entries is used, which holds for the `M` of Definition 5.4. -/
theorem prop_5_5_ceil {A : R → J → ℝ} {b : R → ℝ} (hA : ∀ i j, 0 ≤ A i j) {M : ℝ}
    (hM : ∀ i j, A i j ≠ 0 → b i ≤ A i j * M) {x : J → ℕ} (hx : Feasible A b x) :
    Feasible A b (fun j => min (x j) ⌈M⌉₊) ∧ (∀ j, min (x j) ⌈M⌉₊ ≤ x j) ∧
      ∀ j, min (x j) ⌈M⌉₊ ≤ ⌈M⌉₊ := by
  refine ⟨fun i => ?_, fun j => min_le_left _ _, fun j => min_le_right _ _⟩
  by_cases h : ∃ j, A i j ≠ 0 ∧ ⌈M⌉₊ < x j
  · obtain ⟨j, hj, hlt⟩ := h
    have hmin : min (x j) ⌈M⌉₊ = ⌈M⌉₊ := min_eq_right hlt.le
    have h1 : b i ≤ A i j * (min (x j) ⌈M⌉₊ : ℕ) := by
      rw [hmin]
      exact (hM i j hj).trans (mul_le_mul_of_nonneg_left (Nat.le_ceil M) (hA i j))
    exact h1.trans (single_le_sum (f := fun j => A i j * (min (x j) ⌈M⌉₊ : ℕ))
      (fun j _ => mul_nonneg (hA i j) (Nat.cast_nonneg _)) (mem_univ j))
  · push Not at h
    refine (hx i).trans (le_of_eq (sum_congr rfl fun j _ => ?_))
    by_cases hj : A i j = 0
    · simp [hj]
    · show A i j * (x j : ℝ) = A i j * ((min (x j) ⌈M⌉₊ : ℕ) : ℝ)
      rw [min_eq_left (h j hj)]

/-! ### Claim 5.6 -/

/-- Claim 5.6 is false as stated when `M < 1`: for `2x ≥ 1` (`M = 1/2`) the bound
`f(A') ≤ f(A) · ⌈log₂ M + 1⌉ = 0` forces `A' = 0`, so no such zero-one program is feasible, while
the ILP is (`x = 1`). -/
theorem claim_5_6_false :
    let A : Fin 1 → Fin 1 → ℝ := fun _ _ => 2
    let b : Fin 1 → ℝ := fun _ => 1
    IsM A b (1 / 2) ∧ ⌈Real.logb 2 (1 / 2) + 1⌉₊ = 0 ∧ Feasible A b (fun _ => 1) ∧
      ∀ (J' : Type) [Fintype J'] [DecidableEq J'] (A' : Fin 1 → J' → ℝ),
        fA A' ≤ fA A * ⌈Real.logb 2 (1 / 2) + 1⌉₊ → ∀ T, ¬ ZOFeasible A' b T := by
  intro A b
  have hlog : ⌈Real.logb 2 (1 / 2) + 1⌉₊ = 0 := by
    rw [Nat.ceil_eq_zero, one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    norm_num
  refine ⟨⟨fun i j _ => by norm_num [A, b], 0, 0, by norm_num [A], by norm_num [A, b]⟩, hlog,
    fun i => by norm_num [A, b], ?_⟩
  intro J' _ _ A' hf T hT
  rw [hlog, mul_zero, Nat.le_zero] at hf
  have hzero : ∀ j, A' 0 j = 0 := fun j => by
    by_contra hj
    have : (supp A' 0).card ≤ fA A' := le_sup (f := fun i => (supp A' i).card) (mem_univ 0)
    rw [hf, Nat.le_zero, card_eq_zero] at this
    have hm : j ∈ supp A' 0 := mem_supp.2 hj
    rw [this] at hm; simp at hm
  have := hT 0
  simp only [hzero, sum_const_zero, b] at this
  norm_num at this

/-- The binary expansion of Claim 5.6 with `B` bits: column `j` of `A` is replaced by the columns
`2^ℓ · A^{(j)}`, `ℓ < B`. -/
def binExp (A : R → J → ℝ) (B : ℕ) : R → J × Fin B → ℝ := fun i p => 2 ^ (p.2 : ℕ) * A i p.1

/-- The weights of the binary expansion. -/
def binW (w : J → ℝ) (B : ℕ) : J × Fin B → ℝ := fun p => 2 ^ (p.2 : ℕ) * w p.1

/-- Decoding a zero-one solution: `xⱼ = ∑_ℓ 2^ℓ x_{j,ℓ}`. -/
def decode {B : ℕ} (T : Finset (J × Fin B)) (j : J) : ℕ :=
  ∑ ℓ : Fin B, if (j, ℓ) ∈ T then 2 ^ (ℓ : ℕ) else 0

/-- Encoding `y < 2^B` in binary. -/
def encode (B : ℕ) (x : J → ℕ) : Finset (J × Fin B) :=
  univ.filter fun p => (x p.1).testBit p.2

theorem sum_testBit : ∀ (B y : ℕ), y < 2 ^ B →
    (∑ ℓ : Fin B, if y.testBit ℓ then 2 ^ (ℓ : ℕ) else 0) = y
  | 0, y, hy => by simp at hy; simp [hy]
  | B + 1, y, hy => by
    rw [Fin.sum_univ_succ]
    have ih := sum_testBit B (y / 2) (Nat.div_lt_of_lt_mul (by rw [← pow_succ']; exact hy))
    simp only [Fin.val_zero, pow_zero, Fin.val_succ, Nat.testBit_succ, pow_succ]
    have h2 : (∑ ℓ : Fin B, if (y / 2).testBit ℓ then 2 ^ (ℓ : ℕ) * 2 else 0) =
        2 * (y / 2) := by
      have : (∑ ℓ : Fin B, if (y / 2).testBit ℓ then 2 ^ (ℓ : ℕ) * 2 else 0) =
          2 * ∑ ℓ : Fin B, if (y / 2).testBit ℓ then 2 ^ (ℓ : ℕ) else 0 := by
        rw [mul_sum]; exact sum_congr rfl fun ℓ _ => by split_ifs <;> ring
      rw [this, ih]
    rw [h2, Nat.testBit_zero]
    split_ifs with h <;> simp only [decide_eq_true_eq] at h <;> omega

theorem decode_encode {B : ℕ} {x : J → ℕ} (hx : ∀ j, x j < 2 ^ B) (j : J) :
    decode (encode B x) j = x j := by
  unfold decode encode
  simpa using sum_testBit B (x j) (hx j)

theorem sum_binExp (A : R → J → ℝ) {B : ℕ} (T : Finset (J × Fin B)) (i : R) :
    ∑ p ∈ T, binExp A B i p = ∑ j, A i j * decode T j := by
  have h1 : ∑ p ∈ T, binExp A B i p = ∑ p, if p ∈ T then binExp A B i p else 0 := by
    rw [sum_ite_mem, univ_inter]
  rw [h1, Fintype.sum_prod_type]
  refine sum_congr rfl fun j _ => ?_
  simp only [decode, Nat.cast_sum, Nat.cast_ite, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero,
    mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [binExp]; split_ifs <;> ring

theorem sum_binW (w : J → ℝ) {B : ℕ} (T : Finset (J × Fin B)) :
    ∑ p ∈ T, binW w B p = cost w (decode T) := by
  have := sum_binExp (R := Unit) (fun _ j => w j) T ()
  simpa [binExp, binW, cost] using this

/-- Claim 5.6 (corrected): with `B` bits such that `⌈M⌉ < 2^B`, the zero-one program
`ZO(A', b, w')` of the binary expansion solves the covering ILP: every zero-one solution decodes
to an ILP solution of the same cost, and every ILP solution yields a zero-one solution of no
larger cost. -/
theorem claim_5_6 {A : R → J → ℝ} {b : R → ℝ} {w : J → ℝ} (hcov : IsCovering A b w) {M : ℝ}
    (hM : ∀ i j, A i j ≠ 0 → b i ≤ A i j * M) {B : ℕ} (hB : ⌈M⌉₊ < 2 ^ B) :
    (∀ T, ZOFeasible (binExp A B) b T ↔ Feasible A b (decode T)) ∧
      (∀ T, ∑ p ∈ T, binW w B p = cost w (decode T)) ∧
      ∀ x, Feasible A b x → ∃ T, ZOFeasible (binExp A B) b T ∧
        ∑ p ∈ T, binW w B p ≤ cost w x := by
  have hiff : ∀ T, ZOFeasible (binExp A B) b T ↔ Feasible A b (decode T) := fun T => by
    simp only [ZOFeasible, Feasible, sum_binExp]
  refine ⟨hiff, sum_binW w, fun x hx => ?_⟩
  obtain ⟨hx', hle, hbox⟩ := prop_5_5_ceil hcov.1 hM hx
  set x' := fun j => min (x j) ⌈M⌉₊
  have hdec : decode (encode B x') = x' := funext fun j =>
    decode_encode (fun j => (hbox j).trans_lt hB) j
  refine ⟨encode B x', (hiff _).2 (by rw [hdec]; exact hx'), ?_⟩
  rw [sum_binW, hdec]
  exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (by exact_mod_cast hle j) (hcov.2.2 j)

/-- `B = ⌈log₂ M + 1⌉` bits (the bound in the statement of Claim 5.6) suffice when `M ≥ 1`. -/
theorem claim_5_6_bits {M : ℝ} (hM : 1 ≤ M) : ⌈M⌉₊ < 2 ^ ⌈Real.logb 2 M + 1⌉₊ := by
  have h1 : Real.logb 2 M + 1 ≤ ⌈Real.logb 2 M + 1⌉₊ := Nat.le_ceil _
  have h2 : (2 : ℝ) * M ≤ 2 ^ ⌈Real.logb 2 M + 1⌉₊ := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h1
    rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by linarith),
      Real.rpow_one, Real.rpow_natCast] at this
    linarith
  have h3 : (⌈M⌉₊ : ℝ) < M + 1 := Nat.ceil_lt_add_one (by linarith)
  have : (⌈M⌉₊ : ℝ) < 2 ^ ⌈Real.logb 2 M + 1⌉₊ := by linarith
  exact_mod_cast this

/-- The proof of Claim 5.6 uses `B = ⌈log₂ M⌉` bits, which is too few when `M` is a power of two:
for `x ≥ 2` (`M = 2`, `B = 1`) the binary expansion is infeasible while the ILP is feasible. -/
theorem claim_5_6_proof_false :
    let A : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    let b : Fin 1 → ℝ := fun _ => 2
    IsM A b 2 ∧ ⌈Real.logb 2 2⌉₊ = 1 ∧ Feasible A b (fun _ => 2) ∧
      ∀ T, ¬ ZOFeasible (binExp A 1) b T := by
  intro A b
  refine ⟨⟨fun i j _ => by norm_num [A, b], 0, 0, by norm_num [A], by norm_num [A, b]⟩,
    by rw [Real.logb_self_eq_one (by norm_num)]; simp, fun i => by norm_num [A, b], ?_⟩
  intro T hT
  have h := hT 0
  have hle : ∑ p ∈ T, binExp A 1 0 p ≤ ∑ p : Fin 1 × Fin 1, binExp A 1 0 p :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ => by
      simp [binExp, A]
  have : ∑ p : Fin 1 × Fin 1, binExp A 1 0 p = 1 := by simp [binExp, A]
  simp only [b] at h
  linarith

/-- Claim 5.6, degree: `Δ(A') = Δ(A)` (columns of `A'` are scaled copies of columns of `A`). -/
theorem ΔA_binExp (A : R → J → ℝ) {B : ℕ} (hB : 0 < B) : ΔA (binExp A B) = ΔA A := by
  classical
  unfold ΔA
  have h : ∀ p : J × Fin B, (univ.filter fun i => binExp A B i p ≠ 0) =
      univ.filter fun i => A i p.1 ≠ 0 := fun p => by
    ext i; simp [binExp]
  simp only [h]
  apply le_antisymm
  · exact Finset.sup_le fun p _ =>
      le_sup (f := fun j => (univ.filter fun i => A i j ≠ 0).card) (mem_univ p.1)
  · exact Finset.sup_le fun j _ =>
      le_sup (f := fun p : J × Fin B => (univ.filter fun i => A i p.1 ≠ 0).card)
        (mem_univ (j, ⟨0, hB⟩))

/-- Claim 5.6, rank: `f(A') = f(A) · B`. -/
theorem fA_binExp (A : R → J → ℝ) (B : ℕ) : fA (binExp A B) = fA A * B := by
  classical
  unfold fA
  have h : ∀ i, (supp (binExp A B) i).card = (supp A i).card * B := fun i => by
    have : supp (binExp A B) i = supp A i ×ˢ (univ : Finset (Fin B)) := by
      ext p; simp [mem_supp, binExp]
    rw [this, card_product, card_univ, Fintype.card_fin]
  simp only [h]
  rcases Nat.eq_zero_or_pos B with hB | hB
  · simp [hB]
  · apply le_antisymm
    · exact Finset.sup_le fun i _ => Nat.mul_le_mul_right _
        (le_sup (f := fun i => (supp A i).card) (mem_univ i))
    · rcases isEmpty_or_nonempty R with hR | hR
      · simp [univ_eq_empty]
      · obtain ⟨i, -, hi⟩ := exists_mem_eq_sup (univ : Finset R) univ_nonempty
          (fun i => (supp A i).card)
        rw [hi]
        exact le_sup (f := fun i => (supp A i).card * B) (mem_univ i)

end Podc.CoveringPrimalDual.ILP
