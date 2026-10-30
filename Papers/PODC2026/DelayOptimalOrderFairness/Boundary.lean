import Papers.PODC2026.DelayOptimalOrderFairness.Feasible

/-!
# Theorem 5.2: boundary cycles

Cai, Goharshady. *Brief Announcement: Delay-Optimal Transaction Order Fairness.* PODC 2026, §5.

The paper's construction, made exact for a finite number of nodes. Nodes are `Fin n`, the first
`hc` of them honest. With `d = Δ/k` and a cycle of `m = (k+1)(n+1)` transactions `0 → 1 → ⋯ → m-1 → 0`:

* honest node `i` stamps transaction `j` at `((j + i) mod (k+1)) · d` (offsets `0, d, …, k d = Δ`
  rotating with period `k + 1`: on each edge all honest groups but one move forward by `d ≥ θ`);
* Byzantine node `i` stamps `j` at `((j + m - 1 - i) mod m) · d`: it supports every edge except
  `i → i+1`, so each edge loses at most one Byzantine supporter.

Hence every edge has at least `n - ⌈hc/(k+1)⌉ - 1` supporters (`theorem_5_2_finite`). As `n → ∞`
with honest fraction `h` this exceeds `φ n` for every `φ < 1 - h/(k+1)` (`theorem_5_2`). For a fixed
`n` the statement can fail (`theorem_5_2_fixed_n_false` in `Feasible.lean`).

Together with Theorem 5.1 (applied with `k + 1`) this gives an exact threshold for
`Δ/(k+1) < θ ≤ Δ/k` (`threshold_tight`).
-/

namespace Podc.DelayOptimalOrderFairness

open Finset Relation

/-- One rotation step: if the counter does not wrap, it increases by one. -/
private theorem rot_step {M m c j : ℕ} (hM : 0 < M) (hMm : M ∣ m) (hne : (j + 1 + c) % M ≠ 0) :
    ((j + 1) % m + c) % M = (j + c) % M + 1 := by
  have h1 : ((j + 1) % m + c) % M = (j + 1 + c) % M := by
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ hMm, ← Nat.add_mod]
  have h2 : (j + 1 + c) % M = ((j + c) % M + 1) % M := by
    rw [Nat.mod_add_mod, add_right_comm]
  rw [h1]
  rw [h2] at hne ⊢
  have := Nat.mod_lt (j + c) hM
  rcases Nat.lt_or_ge ((j + c) % M + 1) M with h | h
  · exact Nat.mod_eq_of_lt h
  · exfalso; apply hne
    rw [show (j + c) % M + 1 = M by omega, Nat.mod_self]

/-- A closed walk `0 → 1 → ⋯ → m-1 → 0` is a cycle. -/
private theorem hasCycle_of_succ {R : ℕ → ℕ → Prop} {m : ℕ} (hm : 0 < m)
    (h : ∀ j < m, R j ((j + 1) % m)) : HasCycle R := by
  have key : ∀ j, j + 1 ≤ m → TransGen R 0 ((j + 1) % m) := by
    intro j
    induction j with
    | zero => intro _; exact .single (h 0 hm)
    | succ j ih =>
      intro hj
      have := ih (by omega)
      rw [Nat.mod_eq_of_lt (show j + 1 < m by omega)] at this
      exact this.tail (h _ (by omega))
  refine ⟨0, ?_⟩
  have := key (m - 1) (by omega)
  rwa [Nat.sub_add_cancel hm, Nat.mod_self] at this

/-- Length of the transaction cycle. -/
abbrev cycLen (n k : ℕ) : ℕ := (k + 1) * (n + 1)

/-- The rotating profile of Theorem 5.2 (nodes `i < hc` honest). -/
noncomputable def cycProfile (n hc k : ℕ) (Δ : ℝ) : Profile (Fin n) ℕ := fun i j =>
  if i.val < hc then (((j + i.val) % (k + 1) : ℕ) : ℝ) * (Δ / k)
  else (((j + (cycLen n k - 1 - i.val)) % cycLen n k : ℕ) : ℝ) * (Δ / k)

/-- The honest set: the first `hc` nodes. -/
def honestSet (n hc : ℕ) : Finset (Fin n) := univ.filter fun i => i.val < hc

theorem card_honestSet {n hc : ℕ} (h : hc ≤ n) : (honestSet n hc).card = hc := by
  have := Fin.card_filter_val_lt (n := n) (m := hc)
  simp only [honestSet]
  rw [this, min_eq_right h]

theorem cycProfile_sync {n hc k : ℕ} (hk : 0 < k) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    Synchronous (honestSet n hc) Δ (cycProfile n hc k Δ) := by
  intro i hi j hj tx
  simp only [honestSet, mem_filter, mem_univ, true_and] at hi hj
  simp only [cycProfile, hi, hj, ite_true]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hd : 0 ≤ Δ / k := div_nonneg hΔ hk'.le
  have h1 : (((tx + i.val) % (k + 1) : ℕ) : ℝ) ≤ k := by
    have := Nat.mod_lt (tx + i.val) (Nat.succ_pos k)
    exact_mod_cast Nat.lt_succ_iff.1 this
  have h2 : (0 : ℝ) ≤ (((tx + j.val) % (k + 1) : ℕ) : ℝ) * (Δ / k) := by positivity
  have h3 : (k : ℝ) * (Δ / k) = Δ := by field_simp
  nlinarith

/-- Nodes not supporting the edge `j → j+1` are either honest of the one group that wraps
around, or the Byzantine node `j`. -/
theorem compl_supp_subset {n hc k : ℕ} (hk : 0 < k) {Δ θ : ℝ} (hθ : θ ≤ Δ / k) {j : ℕ}
    (hj : j < cycLen n k) :
    univ \ supp (cycProfile n hc k Δ) θ j ((j + 1) % cycLen n k) ⊆
      (univ.filter fun i : Fin n => i.val < hc ∧ (j + 1 + i.val) % (k + 1) = 0) ∪
        (univ.filter fun i : Fin n => i.val = j) := by
  intro i hi
  simp only [mem_sdiff, mem_univ, true_and, mem_supp] at hi
  simp only [mem_union, mem_filter, mem_univ, true_and]
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply hi
  have hlt : i.val < n := i.isLt
  by_cases hh : i.val < hc
  · have hstep := rot_step (M := k + 1) (m := cycLen n k) (c := i.val) (j := j) (Nat.succ_pos k)
      (Dvd.intro _ rfl) (h1 hh)
    simp only [cycProfile, hh, ite_true, hstep]
    push_cast; linarith
  · have hne : (j + 1 + (cycLen n k - 1 - i.val)) % cycLen n k ≠ 0 := by
      have hmn : n < cycLen n k := by simp only [cycLen]; nlinarith
      set t := j + 1 + (cycLen n k - 1 - i.val) with ht
      rcases Nat.lt_or_ge t (cycLen n k) with htm | htm
      · rw [Nat.mod_eq_of_lt htm]; omega
      · rw [Nat.mod_eq_sub_mod htm, Nat.mod_eq_of_lt (by omega)]; omega
    have hstep := rot_step (M := cycLen n k) (m := cycLen n k) (j := j) (by positivity)
      dvd_rfl hne
    simp only [cycProfile, hh, ite_false, hstep]
    push_cast; linarith

/-- At most `⌈hc/(k+1)⌉ ≤ hc/(k+1) + 1` honest nodes lie in one residue class. -/
theorem card_residue_le (n hc k r : ℕ) :
    (univ.filter fun i : Fin n => i.val < hc ∧ (r + i.val) % (k + 1) = 0).card ≤ hc / (k + 1) + 1 := by
  rw [← card_range (hc / (k + 1) + 1)]
  refine card_le_card_of_injOn (fun i => i.val / (k + 1)) ?_ ?_
  · intro i hi
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi
    simp only [coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hi.1.le)
  · intro a ha b hb hab
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
    have hmod : a.val % (k + 1) = b.val % (k + 1) := by
      have : (r + a.val) ≡ (r + b.val) [MOD k + 1] := by
        unfold Nat.ModEq; rw [ha.2, hb.2]
      exact Nat.ModEq.add_left_cancel' r this
    apply Fin.ext
    rw [← Nat.mod_add_div a.val (k + 1), ← Nat.mod_add_div b.val (k + 1), hmod]
    simp only at hab
    rw [hab]

/-- **Theorem 5.2, exact finite form.** Let `0 < k`, `hc ≤ n` honest nodes, `Δ ≥ 0`,
`θ ≤ Δ/k`, and `φ n + hc/(k+1) + 2 ≤ n`. Then some `Δ`-synchronous profile with `hc` honest nodes
has a directed cycle in its `(θ, φ)`-AOF graph. -/
theorem theorem_5_2_finite {n hc k : ℕ} (hk : 0 < k) (hhc : hc ≤ n) {Δ θ φ : ℝ} (hΔ : 0 ≤ Δ)
    (hθ : θ ≤ Δ / k) (hφ : φ * n + hc / (k + 1) + 2 ≤ n) :
    ∃ (ts : Profile (Fin n) ℕ) (H : Finset (Fin n)),
      H.card = hc ∧ Synchronous H Δ ts ∧ HasCycle (Prec ts θ φ) := by
  refine ⟨cycProfile n hc k Δ, honestSet n hc, card_honestSet hhc, cycProfile_sync hk hΔ,
    hasCycle_of_succ (m := cycLen n k) (by positivity) fun j hj => ?_⟩
  have hsub := card_le_card (compl_supp_subset (hc := hc) hk hθ hj)
  have hu := card_union_le
    (univ.filter fun i : Fin n => i.val < hc ∧ (j + 1 + i.val) % (k + 1) = 0)
    (univ.filter fun i : Fin n => i.val = j)
  have hres := card_residue_le n hc k (j + 1)
  have hone : (univ.filter fun i : Fin n => i.val = j).card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact Fin.ext (ha.trans hb.symm)
  rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin] at hsub
  set S := supp (cycProfile n hc k Δ) θ j ((j + 1) % cycLen n k)
  have hS : n ≤ S.card + (hc / (k + 1) + 1) + 1 := by
    have := card_le_univ S
    rw [Fintype.card_fin] at this
    omega
  have hdiv : ((hc / (k + 1) : ℕ) : ℝ) ≤ (hc : ℝ) / (k + 1) := by
    have := Nat.cast_div_le (α := ℝ) (m := hc) (n := k + 1)
    simpa using this
  have hS' : (n : ℝ) ≤ S.card + ((hc / (k + 1) : ℕ) : ℝ) + 1 + 1 := by exact_mod_cast hS
  show φ * Fintype.card (Fin n) ≤ S.card
  rw [Fintype.card_fin]
  linarith

/-- **Theorem 5.2 (Boundary cycles)**, with the number of nodes made explicit. For every positive
integer `k`, honest fraction `h ≤ 1` and `φ < 1 - h/(k+1)`, for all sufficiently large `n` (with
`h n` an integer) and all `Δ ≥ 0`, `θ ≤ Δ/k`, there is a valid `Δ`-synchronous profile with `h n`
honest nodes whose `(θ, φ)`-AOF graph contains a directed cycle.

The paper states this for the model's `n` without a largeness assumption; its proof lets the
number of Byzantine groups grow, and for fixed `n` the claim is false
(`theorem_5_2_fixed_n_false`). The hypothesis `1 - h/k ≤ h` of the paper is not needed. -/
theorem theorem_5_2 {k : ℕ} (hk : 0 < k) {h φ : ℝ} (hh : h ≤ 1) (hφ : φ < 1 - h / (k + 1)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ hc : ℕ, (hc : ℝ) = h * n → ∀ Δ θ : ℝ, 0 ≤ Δ → θ ≤ Δ / k →
      ∃ (ts : Profile (Fin n) ℕ) (H : Finset (Fin n)),
        H.card = hc ∧ Synchronous H Δ ts ∧ HasCycle (Prec ts θ φ) := by
  set ε := 1 - h / (k + 1) - φ with hε
  have hε0 : 0 < ε := by linarith
  refine ⟨⌈2 / ε⌉₊, fun n hn hc hhc Δ θ hΔ hθ => theorem_5_2_finite hk ?_ hΔ hθ ?_⟩
  · have : (hc : ℝ) ≤ n := by rw [hhc]; nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact_mod_cast this
  · have h1 : 2 / ε ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have h2 : 2 ≤ n * ε := by rwa [div_le_iff₀ hε0] at h1
    rw [hhc]
    have : h * n / (k + 1) = h / (k + 1) * n := by ring
    rw [this]
    nlinarith

/-- **The threshold is exact** for `Δ/(k+1) < θ ≤ Δ/k` (remark to §7 of the paper, which
describes a "boundary gap" between Theorems 5.1 and 5.2): above `1 - h/(k+1)` the AOF graph is
acyclic for every profile and every `n ≥ 1` (Theorem 5.1 with `k + 1`), below it cycles exist for
all large `n` (Theorem 5.2). -/
theorem threshold_tight {k : ℕ} (hk : 0 < k) {h Δ θ : ℝ} (hh : h ≤ 1) (hΔ : 0 ≤ Δ)
    (hθ₁ : Δ / (k + 1 : ℕ) < θ) (hθ₂ : θ ≤ Δ / k) :
    (∀ φ, 1 - h / (k + 1 : ℕ) < φ → ∀ (Node Tx : Type) [Fintype Node] [Nonempty Node]
        (H : Finset Node) (ts : Profile Node Tx), (H.card : ℝ) = h * Fintype.card Node →
        Synchronous H Δ ts → ¬ HasCycle (Prec ts θ φ)) ∧
    (∀ φ, φ < 1 - h / (k + 1 : ℕ) → ∃ N : ℕ, ∀ n ≥ N, ∀ hc : ℕ, (hc : ℝ) = h * n →
        ∃ (ts : Profile (Fin n) ℕ) (H : Finset (Fin n)),
          H.card = hc ∧ Synchronous H Δ ts ∧ HasCycle (Prec ts θ φ)) := by
  refine ⟨fun φ hφ Node Tx _ _ H ts hH hsync =>
    theorem_5_1 hH hsync (Nat.succ_pos k) hθ₁ hφ, fun φ hφ => ?_⟩
  obtain ⟨N, hN⟩ := theorem_5_2 hk hh (by exact_mod_cast hφ)
  exact ⟨N, fun n hn hc hhc => hN n hn hc hhc Δ θ hΔ hθ₂⟩

end Podc.DelayOptimalOrderFairness
