import Papers.PODC2011.SymmetryBreakingTasks.Basic

/-!
# The structure of symmetric GSB tasks (Section 4)

Counting and kernel vectors (Definitions 3–4, Lemma 3), anchored tasks (Definition 5,
Theorems 3–4, Corollary 1), the hardest task (Theorem 5), and the canonical representative
(Theorems 6–7).

Arithmetic is in `ℕ` (truncated subtraction). For Theorem 3 this agrees with the paper's integer
reading on feasible tasks; for Theorem 4 it does not: the paper's integer statement is false for
`ℓ = 0` and `u (m - 1) > n` (`theorem_4_int_false`), and the `ℕ` reading is the correct one.

Two synonymous tasks have the same set of output vectors (`sgsb n m ℓ u = sgsb n m ℓ' u'`).
-/

namespace Podc.SymmetryBreakingTasks

open Finset

variable {n m ℓ u : ℕ}

lemma mul_eq_sub_one_add (hm : 1 ≤ m) (a : ℕ) : m * a = a * (m - 1) + a := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

lemma one_le_of_feasible_pos (h : Feasible n m ℓ u) (hn : n - ℓ * (m - 1) > u ∨ 0 < n) :
    1 ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have := h.2; simp at this; subst this; simp at hn
  · exact hm

/-! ### Counting vectors and kernel vectors (Definitions 3–4, Lemma 3) -/

/-- Definition 3: the counting vectors `C(T)` of the `⟨n, m, ℓ, u⟩`-GSB task. -/
def countingVectors (n m ℓ u : ℕ) : Set (Fin m → ℕ) := cnt '' sgsb n m ℓ u

lemma mem_countingVectors {c : Fin m → ℕ} :
    c ∈ countingVectors n m ℓ u ↔ ∑ v, c v = n ∧ ∀ v, ℓ ≤ c v ∧ c v ≤ u := by
  constructor
  · rintro ⟨O, hO, rfl⟩; exact ⟨sum_cnt O, hO⟩
  · rintro ⟨hs, hb⟩
    obtain ⟨O, rfl⟩ := exists_cnt_eq c hs
    exact ⟨O, hb, rfl⟩

/-- Definition 4: the kernel set (the non-increasing counting vectors). -/
def kernelSet (n m ℓ u : ℕ) : Set (Fin m → ℕ) := {K | K ∈ countingVectors n m ℓ u ∧ Antitone K}

lemma mem_kernelSet {K : Fin m → ℕ} :
    K ∈ kernelSet n m ℓ u ↔ (∑ v, K v = n ∧ ∀ v, ℓ ≤ K v ∧ K v ≤ u) ∧ Antitone K := by
  simp [kernelSet, mem_countingVectors]

/-- Every vector can be sorted non-increasingly. -/
lemma exists_perm_antitone (c : Fin m → ℕ) : ∃ σ : Equiv.Perm (Fin m), Antitone (c ∘ σ) :=
  ⟨Tuple.sort (fun v => OrderDual.toDual (c v)),
    fun _ _ hab => Tuple.monotone_sort (fun v => OrderDual.toDual (c v)) hab⟩

/-- Lemma 3: the kernel set is totally ordered by the lexicographic order. -/
theorem lemma_3 : IsChain (· ≤ ·) (toLex '' kernelSet n m ℓ u) :=
  fun a _ b _ _ => le_total a b

/-- The kernel set determines the task: two symmetric GSB tasks with the same kernel set are
synonyms (and conversely). This justifies representing a task by its kernel set (Section 4.1). -/
theorem kernelSet_eq_iff {ℓ' u' : ℕ} :
    kernelSet n m ℓ u = kernelSet n m ℓ' u' ↔ sgsb n m ℓ u = sgsb n m ℓ' u' := by
  refine ⟨fun h => ?_, fun h => by simp only [kernelSet, countingVectors, h]⟩
  -- a task is determined by the sorted versions of its counting vectors
  have key : ∀ ℓ u ℓ' u', kernelSet n m ℓ u = kernelSet n m ℓ' u' →
      sgsb n m ℓ u ⊆ sgsb n m ℓ' u' := by
    intro ℓ u ℓ' u' h O hO
    obtain ⟨σ, hσ⟩ := exists_perm_antitone (cnt O)
    have hK : cnt O ∘ σ ∈ kernelSet n m ℓ u := by
      refine mem_kernelSet.2 ⟨⟨?_, fun v => hO (σ v)⟩, hσ⟩
      simp only [Function.comp_apply]; rw [Equiv.sum_comp σ (cnt O), sum_cnt]
    rw [h, mem_kernelSet] at hK
    intro v
    simpa using hK.1.2 (σ.symm v)
  exact Set.Subset.antisymm (key _ _ _ _ h) (key _ _ _ _ h.symm)

/-- Definition 4: the balanced kernel vector `[⌈n/m⌉, …, ⌈n/m⌉, ⌊n/m⌋, …, ⌊n/m⌋]` (the first
`n mod m` entries equal to `⌈n/m⌉`). -/
def balanced (n m : ℕ) : Fin m → ℕ := fun v => n / m + if (v : ℕ) < n % m then 1 else 0

/-- Section 4.1, Examples: the balanced kernel vector belongs to (the kernel set of) every
feasible `⟨n, m, -, -⟩`-GSB task. -/
theorem balanced_mem_kernelSet (hm : 1 ≤ m) (h : Feasible n m ℓ u) :
    balanced n m ∈ kernelSet n m ℓ u := by
  have hdm := Nat.div_add_mod n m
  have hmod := Nat.mod_lt n hm
  have hℓ : ℓ ≤ n / m := (Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact h.1)
  have hu : n / m ≤ u := Nat.le_of_mul_le_mul_left ((Nat.mul_div_le n m).trans h.2) hm
  have hu' : n % m ≠ 0 → n / m + 1 ≤ u := fun hne => by
    by_contra hlt
    have : m * u ≤ m * (n / m) := Nat.mul_le_mul_left m (by omega)
    have := h.2; omega
  refine mem_kernelSet.2 ⟨⟨?_, fun v => ?_⟩, fun v w hvw => ?_⟩
  · simp only [balanced, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      sum_boole, Fin.card_filter_val_lt]
    rw [Nat.cast_id, min_eq_right hmod.le]; exact hdm
  · simp only [balanced]; split_ifs with hv
    · exact ⟨by omega, hu' (by omega)⟩
    · exact ⟨by omega, by omega⟩
  · simp only [balanced]
    have : (v : ℕ) ≤ w := hvw
    split_ifs <;> omega

/-! ### Anchored tasks (Definition 5, Theorems 3–4, Corollary 1) -/

/-- Definition 5: `⟨n, m, ℓ, u⟩` is `ℓ`-anchored if it is a synonym of `⟨n, m, ℓ, min(n, u+1)⟩`. -/
def LAnchored (n m ℓ u : ℕ) : Prop := sgsb n m ℓ u = sgsb n m ℓ (min n (u + 1))

/-- Definition 5: `⟨n, m, ℓ, u⟩` is `u`-anchored if it is a synonym of `⟨n, m, max(0, ℓ-1), u⟩`
(`ℓ - 1` is truncated subtraction). -/
def UAnchored (n m ℓ u : ℕ) : Prop := sgsb n m ℓ u = sgsb n m (ℓ - 1) u

/-- Theorem 3: a feasible `⟨n, m, ℓ, u⟩`-GSB task is `ℓ`-anchored iff `u ≥ n - ℓ (m - 1)`. -/
theorem theorem_3 (h : Feasible n m ℓ u) : LAnchored n m ℓ u ↔ n - ℓ * (m - 1) ≤ u := by
  constructor
  · intro hA
    by_contra hu
    push Not at hu
    have hm := one_le_of_feasible_pos h (Or.inl hu)
    have hℓu := h.le hm
    have e1 := mul_eq_sub_one_add hm ℓ
    have e2 := mul_eq_sub_one_add hm (u + 1)
    have e3 : m * u ≤ m * (u + 1) := Nat.mul_le_mul_left m (Nat.le_succ u)
    have h1 := h.1; have h2 := h.2
    obtain ⟨O, hO0, hO⟩ := exists_cnt_single (n := n) (⟨0, hm⟩ : Fin m) (a := u + 1) (lo := ℓ)
      (hi := u + 1) (by omega) (by omega) (by omega)
    have hmem : O ∈ sgsb n m ℓ (min n (u + 1)) := by
      rw [mem_sgsb]; intro v
      by_cases hv : v = ⟨0, hm⟩
      · subst hv; rw [hO0]; omega
      · have := hO v hv; have := cnt_le O v; omega
    rw [← hA] at hmem
    have := (mem_sgsb.1 hmem ⟨0, hm⟩).2
    omega
  · intro hu
    ext O
    simp only [mem_sgsb]
    refine ⟨fun hO v => ⟨(hO v).1, ?_⟩, fun hO v => ⟨(hO v).1, ?_⟩⟩
    · have := (hO v).2; have := cnt_le O v; omega
    · have := cnt_le_sub (fun w => (hO w).1) v; omega

/-- Theorem 4 (in `ℕ`, i.e. with `n - u (m - 1)` truncated at `0`): a feasible `⟨n, m, ℓ, u⟩`-GSB
task with `m ≥ 1` is `u`-anchored iff `ℓ ≤ n - u (m - 1)`. -/
theorem theorem_4 (hm : 1 ≤ m) (h : Feasible n m ℓ u) :
    UAnchored n m ℓ u ↔ ℓ ≤ n - u * (m - 1) := by
  constructor
  · intro hA
    by_contra hℓ
    push Not at hℓ
    have hℓu := h.le hm
    have e1 := mul_eq_sub_one_add hm ℓ
    have e3 : (ℓ - 1) * (m - 1) ≤ ℓ * (m - 1) := Nat.mul_le_mul_right _ (Nat.sub_le ℓ 1)
    have h1 := h.1
    obtain ⟨O, hO0, hO⟩ := exists_cnt_single (n := n) (⟨0, hm⟩ : Fin m) (a := ℓ - 1)
      (lo := ℓ - 1) (hi := u) (by omega) (by omega) (by omega)
    have hmem : O ∈ sgsb n m (ℓ - 1) u := by
      rw [mem_sgsb]; intro v
      by_cases hv : v = ⟨0, hm⟩
      · subst hv; rw [hO0]; omega
      · exact hO v hv
    rw [← hA] at hmem
    have := (mem_sgsb.1 hmem ⟨0, hm⟩).1
    omega
  · intro hℓ
    ext O
    simp only [mem_sgsb]
    refine ⟨fun hO v => ⟨by have := (hO v).1; omega, (hO v).2⟩, fun hO v => ⟨?_, (hO v).2⟩⟩
    have := sub_le_cnt (fun w => (hO w).2) v; omega

/-- Theorem 4 as stated in the paper, with integer arithmetic, is false: `⟨6, 3, 0, 6⟩` is
(trivially) `u`-anchored — Figure 1 of the paper calls it so — but `0 ≤ 6 - 6·2` fails. -/
theorem theorem_4_int_false :
    ¬ ∀ n m ℓ u : ℕ, 1 ≤ m → Feasible n m ℓ u →
      (UAnchored n m ℓ u ↔ (ℓ : ℤ) ≤ n - u * ((m : ℤ) - 1)) := by
  intro H
  have := (H 6 3 0 6 (by norm_num) ⟨by norm_num, by norm_num⟩).1 rfl
  norm_num at this

/-- The integer reading of Theorem 4 fails for every `(2n-1)`-renaming task with `n ≥ 3`, which is
`u`-anchored (as every `⟨n, m, 0, u⟩` task) while `0 ≤ n - 1·(2n - 2)` is false. -/
theorem theorem_4_int_false_renaming (hn : 3 ≤ n) :
    Feasible n (2 * n - 1) 0 1 ∧ UAnchored n (2 * n - 1) 0 1 ∧
      ¬ ((0 : ℤ) ≤ n - 1 * (((2 * n - 1 : ℕ) : ℤ) - 1)) := by
  refine ⟨⟨by simp, by omega⟩, rfl, ?_⟩
  push_cast [show 1 ≤ 2 * n by omega]
  omega

/-- Corollary 1: if `m ℓ ≤ n ≤ m u` (i.e. `ℓ ≤ n/m ≤ u`), then `⟨n, m, ℓ, max(ℓ, n - ℓ(m-1))⟩`
is `ℓ`-anchored and `⟨n, m, max(0, n - u(m-1)), u⟩` is `u`-anchored. -/
theorem corollary_1 (hm : 1 ≤ m) (h : Feasible n m ℓ u) :
    LAnchored n m ℓ (max ℓ (n - ℓ * (m - 1))) ∧ UAnchored n m (max 0 (n - u * (m - 1))) u := by
  obtain ⟨O, hO⟩ := h.nonempty
  constructor
  · refine (theorem_3 (feasible_iff.2 ⟨O, mem_sgsb.2 fun v => ⟨(hO v).1, ?_⟩⟩)).2
      (le_max_right _ _)
    have := cnt_le_sub (fun w => (hO w).1) v; omega
  · refine (theorem_4 hm (feasible_iff.2 ⟨O, mem_sgsb.2 fun v => ⟨?_, (hO v).2⟩⟩)).2 (by simp)
    have := sub_le_cnt (fun w => (hO w).2) v; simpa using this

/-! ### The hardest task (Theorem 5) -/

/-- Theorem 5: `⟨n, m, ⌊n/m⌋, ⌈n/m⌉⟩` is feasible and is the hardest feasible `⟨n, m, -, -⟩`-GSB
task: its output vectors are output vectors of every feasible `⟨n, m, ℓ, u⟩`-GSB task. -/
theorem theorem_5 (hm : 1 ≤ m) :
    Feasible n m (n / m) (n ⌈/⌉ m) ∧
      ∀ ℓ u, Feasible n m ℓ u → sgsb n m (n / m) (n ⌈/⌉ m) ⊆ sgsb n m ℓ u := by
  refine ⟨⟨Nat.mul_div_le n m, le_smul_ceilDiv (a := m) (b := n) (by omega)⟩, fun ℓ u h => ?_⟩
  have hℓ : ℓ ≤ n / m := (Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact h.1)
  have hu : n ⌈/⌉ m ≤ u := (ceilDiv_le_iff_le_mul (by omega)).2 h.2
  exact (lemma_4 hu).trans (lemma_5 hℓ)

/-- The hardest task's examples (Section 4.4): `⟨10, 4, 2, 3⟩` is neither `ℓ`- nor `u`-anchored,
while `⟨10, 5, 2, 2⟩` is `(ℓ, u)`-anchored. -/
theorem theorem_5_examples :
    (10 / 4 = 2 ∧ 10 ⌈/⌉ 4 = 3 ∧ ¬ LAnchored 10 4 2 3 ∧ ¬ UAnchored 10 4 2 3) ∧
    (10 / 5 = 2 ∧ 10 ⌈/⌉ 5 = 2 ∧ LAnchored 10 5 2 2 ∧ UAnchored 10 5 2 2) := by
  have f1 : Feasible 10 4 2 3 := ⟨by norm_num, by norm_num⟩
  have f2 : Feasible 10 5 2 2 := ⟨by norm_num, by norm_num⟩
  refine ⟨⟨by decide, by decide, ?_, ?_⟩, ⟨by decide, by decide, ?_, ?_⟩⟩
  · rw [theorem_3 f1]; norm_num
  · rw [theorem_4 (by norm_num) f1]; norm_num
  · rw [theorem_3 f2]
  · rw [theorem_4 (by norm_num) f2]

/-! ### Canonical representative (Theorems 6–7) -/

/-- Theorem 6 (as stated): (i) if `ℓ ≤ ℓ' := n - u(m-1)` then `S(⟨n,m,ℓ',u⟩) ⊆ S(T)`;
(ii) if `u' := n - ℓ(m-1) ≤ u` then `S(⟨n,m,ℓ,u'⟩) ⊆ S(T)`. -/
theorem theorem_6 :
    (ℓ ≤ n - u * (m - 1) → sgsb n m (n - u * (m - 1)) u ⊆ sgsb n m ℓ u) ∧
    (n - ℓ * (m - 1) ≤ u → sgsb n m ℓ (n - ℓ * (m - 1)) ⊆ sgsb n m ℓ u) :=
  ⟨lemma_5, lemma_4⟩

/-- Theorem 6, strengthened: the inclusions are equalities (the tasks are synonyms), and no
feasibility assumption is needed. -/
theorem theorem_6_eq :
    (ℓ ≤ n - u * (m - 1) → sgsb n m (n - u * (m - 1)) u = sgsb n m ℓ u) ∧
    (n - ℓ * (m - 1) ≤ u → sgsb n m ℓ (n - ℓ * (m - 1)) = sgsb n m ℓ u) := by
  refine ⟨fun h => (lemma_5 h).antisymm fun O hO v => ⟨sub_le_cnt (fun w => (hO w).2) v, (hO v).2⟩,
    fun h => (lemma_4 h).antisymm fun O hO v => ⟨(hO v).1, cnt_le_sub (fun w => (hO w).1) v⟩⟩

/-- The map `f(ℓ, u) = (max(ℓ, n - u(m-1)), min(u, n - ℓ(m-1)))` of Theorem 7. -/
def canon (n m ℓ u : ℕ) : ℕ × ℕ := (max ℓ (n - u * (m - 1)), min u (n - ℓ * (m - 1)))

/-- Applying `f` does not change the task (no feasibility needed). -/
theorem sgsb_canon (n m ℓ u : ℕ) :
    sgsb n m (canon n m ℓ u).1 (canon n m ℓ u).2 = sgsb n m ℓ u := by
  ext O
  simp only [canon, mem_sgsb]
  refine ⟨fun hO v => ⟨le_of_max_le_left (hO v).1, le_of_le_min_left (hO v).2⟩, fun hO v => ?_⟩
  have h1 := sub_le_cnt (fun w => (hO w).2) v
  have h2 := cnt_le_sub (fun w => (hO w).1) v
  exact ⟨max_le (hO v).1 h1, le_min (hO v).2 h2⟩

/-- `L` is the least number of times a value is decided in an output vector of `S`. -/
def IsMinCount (S : Set (Fin n → Fin m)) (L : ℕ) : Prop :=
  (∃ O ∈ S, ∃ v, cnt O v = L) ∧ ∀ O ∈ S, ∀ v, L ≤ cnt O v

/-- `U` is the largest number of times a value is decided in an output vector of `S`. -/
def IsMaxCount (S : Set (Fin n → Fin m)) (U : ℕ) : Prop :=
  (∃ O ∈ S, ∃ v, cnt O v = U) ∧ ∀ O ∈ S, ∀ v, cnt O v ≤ U

lemma IsMinCount.unique {S : Set (Fin n → Fin m)} {L L' : ℕ} (h : IsMinCount S L)
    (h' : IsMinCount S L') : L = L' := by
  obtain ⟨⟨O, hO, v, rfl⟩, h1⟩ := h
  obtain ⟨⟨O', hO', v', rfl⟩, h1'⟩ := h'
  exact le_antisymm (h1 O' hO' v') (h1' O hO v)

lemma IsMaxCount.unique {S : Set (Fin n → Fin m)} {U U' : ℕ} (h : IsMaxCount S U)
    (h' : IsMaxCount S U') : U = U' := by
  obtain ⟨⟨O, hO, v, rfl⟩, h1⟩ := h
  obtain ⟨⟨O', hO', v', rfl⟩, h1'⟩ := h'
  exact le_antisymm (h1' O hO v) (h1 O' hO' v')

/-- For a feasible task, `f(ℓ, u)` consists of the least and the largest number of times a value is
decided in an output vector. -/
theorem isMinCount_isMaxCount_canon (hm : 1 ≤ m) (h : Feasible n m ℓ u) :
    IsMinCount (sgsb n m ℓ u) (canon n m ℓ u).1 ∧ IsMaxCount (sgsb n m ℓ u) (canon n m ℓ u).2 := by
  have hℓu := h.le hm
  have e1 := mul_eq_sub_one_add hm ℓ
  have e2 := mul_eq_sub_one_add hm u
  have e3 : ℓ * (m - 1) ≤ u * (m - 1) := Nat.mul_le_mul_right _ hℓu
  have h1 := h.1; have h2 := h.2
  have hS := sgsb_canon n m ℓ u
  simp only [canon] at hS ⊢
  constructor
  · refine ⟨?_, fun O hO v => ?_⟩
    · obtain ⟨O, hO0, hO⟩ := exists_cnt_single (n := n) (⟨0, hm⟩ : Fin m)
        (a := max ℓ (n - u * (m - 1))) (lo := ℓ) (hi := u) hℓu (by omega) (by omega)
      refine ⟨O, mem_sgsb.2 fun v => ?_, _, hO0⟩
      by_cases hv : v = ⟨0, hm⟩
      · subst hv; rw [hO0]; omega
      · exact hO v hv
    · rw [← hS] at hO; exact (hO v).1
  · refine ⟨?_, fun O hO v => ?_⟩
    · obtain ⟨O, hO0, hO⟩ := exists_cnt_single (n := n) (⟨0, hm⟩ : Fin m)
        (a := min u (n - ℓ * (m - 1))) (lo := ℓ) (hi := u) hℓu (by omega) (by omega)
      refine ⟨O, mem_sgsb.2 fun v => ?_, _, hO0⟩
      by_cases hv : v = ⟨0, hm⟩
      · subst hv; rw [hO0]; omega
      · exact hO v hv
    · rw [← hS] at hO; exact (hO v).2

/-- Theorem 7: for a feasible `⟨n, m, ℓ, u⟩`-GSB task `T` (`m ≥ 1`) and `(ℓ_fp, u_fp) = f(ℓ, u)`:
* `(ℓ_fp, u_fp)` is a fixed point of `f` (reached after one application);
* `T_fp = ⟨n, m, ℓ_fp, u_fp⟩` is feasible and a synonym of `T`;
* `T_fp` is canonical: every synonym `⟨n, m, ℓ', u'⟩` of `T` has `ℓ' ≤ ℓ_fp` and `u_fp ≤ u'`
  (so no synonym has a larger lower bound or a smaller upper bound). -/
theorem theorem_7 (hm : 1 ≤ m) (h : Feasible n m ℓ u) :
    canon n m (canon n m ℓ u).1 (canon n m ℓ u).2 = canon n m ℓ u ∧
    Feasible n m (canon n m ℓ u).1 (canon n m ℓ u).2 ∧
    sgsb n m (canon n m ℓ u).1 (canon n m ℓ u).2 = sgsb n m ℓ u ∧
    ∀ ℓ' u', sgsb n m ℓ' u' = sgsb n m ℓ u → ℓ' ≤ (canon n m ℓ u).1 ∧ (canon n m ℓ u).2 ≤ u' := by
  have hS := sgsb_canon n m ℓ u
  have hF : Feasible n m (canon n m ℓ u).1 (canon n m ℓ u).2 :=
    feasible_iff.2 (hS ▸ h.nonempty)
  obtain ⟨hmin, hmax⟩ := isMinCount_isMaxCount_canon hm h
  obtain ⟨hmin', hmax'⟩ := isMinCount_isMaxCount_canon hm hF
  rw [hS] at hmin' hmax'
  refine ⟨Prod.ext (hmin'.unique hmin) (hmax'.unique hmax), hF, hS, fun ℓ' u' h' => ?_⟩
  obtain ⟨⟨O, hO, v, hv⟩, -⟩ := hmin
  obtain ⟨⟨O', hO', v', hv'⟩, -⟩ := hmax
  rw [← h'] at hO hO'
  exact ⟨hv ▸ (hO v).1, hv' ▸ (hO' v').2⟩

/-- Theorem 7, canonical form: two feasible `⟨n, m, -, -⟩`-GSB tasks are synonyms iff they have the
same canonical representative `f(ℓ, u)`. -/
theorem theorem_7_iff (hm : 1 ≤ m) {ℓ' u' : ℕ} (h : Feasible n m ℓ u) (h' : Feasible n m ℓ' u') :
    sgsb n m ℓ u = sgsb n m ℓ' u' ↔ canon n m ℓ u = canon n m ℓ' u' := by
  constructor
  · intro hS
    obtain ⟨hmin, hmax⟩ := isMinCount_isMaxCount_canon hm h
    obtain ⟨hmin', hmax'⟩ := isMinCount_isMaxCount_canon hm h'
    rw [hS] at hmin hmax
    exact Prod.ext (hmin.unique hmin') (hmax.unique hmax')
  · intro hc
    rw [← sgsb_canon n m ℓ u, ← sgsb_canon n m ℓ' u', hc]

end Podc.SymmetryBreakingTasks
