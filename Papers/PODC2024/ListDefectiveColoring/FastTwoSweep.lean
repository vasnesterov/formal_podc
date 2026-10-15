import Papers.PODC2024.ListDefectiveColoring.Distributed

/-!
# Theorem 1.1 of [FK24] for `ε > 0` (Algorithm 2, Fast-Two-Sweep)

Algorithm 2 first computes a defective colouring `Ψ` with `O(p²/ε²)` colours in which every node
has at most `(ε/p) · β_v` out-neighbours of its own `Ψ`-colour (Lemma 3.4, cited from
[Kuh09, KS18]; **not formalized**, it is a hypothesis here). It then removes the monochromatic
edges (`out'`), lowers every defect by `f_v = ⌊β_v · ε/p⌋` (dropping colours whose defect would
become negative), and runs the Two-Sweep algorithm with `Ψ` as the initial (now proper)
colouring. The running time is that of Lemma 3.4 plus `2K` rounds, where `K = O(p²/ε²)` is the
number of colours of `Ψ`, i.e. `O((p/ε)² + log* q)`; the `O(q)` alternative is `twoSweep_correct`.

## Main results

* `reducedSlack`: the reduced instance satisfies the slack condition (2) (first display in the
  proof of Theorem 1.1).
* `IsOLDC.of_reduced`: a solution of the reduced instance solves the original instance.
* `fastTwoSweep_correct`: **Theorem 1.1** for `ε ≥ 0`, given the defective colouring `Ψ`.
-/

open Finset Cslib.LocallyIterative

namespace FK24

variable {V α : Type*} [DecidableEq α]

/-- The defect reduction `f_v = ⌊β_v · ε/p⌋` of Algorithm 2. -/
noncomputable def defectCut (out : V → Finset V) (ε : ℝ) (p : ℕ) (v : V) : ℕ :=
  ⌊ε * beta out v / p⌋₊

omit [DecidableEq α] in
/-- The out-neighbourhoods of `G'`: out-edges that are not monochromatic under `Ψ`. -/
def reducedOut (out : V → Finset V) (Ψ : V → ℕ) (v : V) : Finset V :=
  {u ∈ out v | Ψ u ≠ Ψ v}

/-- The instance of line 5 of Algorithm 2: `d'_v(x) = d_v(x) − f_v`,
`L'_v = {x ∈ L_v | d'_v(x) ≥ 0}`. -/
def reducedInstance (I : ListInstance V α) (f : V → ℕ) : ListInstance V α :=
  ⟨fun v => {x ∈ I.L v | f v ≤ I.d v x}, fun v x => I.d v x - f v⟩

omit [DecidableEq α] in
theorem beta_reducedOut_le (out : V → Finset V) (Ψ : V → ℕ) (v : V) :
    beta (reducedOut out Ψ) v ≤ beta out v :=
  max_le_max le_rfl (Finset.card_le_card (Finset.filter_subset _ _))

omit [DecidableEq α] in
/-- `∑_{x ∈ L_v} (d_v(x)+1) ≤ ∑_{x ∈ L'_v} (d'_v(x)+1) + |L_v| · f_v`. -/
theorem weight_le_reduced (I : ListInstance V α) (f : V → ℕ) (v : V) :
    I.weight v ≤ (reducedInstance I f).weight v + (I.L v).card * f v := by
  unfold ListInstance.weight reducedInstance
  simp only
  rw [← Finset.sum_filter_add_sum_filter_not (I.L v) (fun x => f v ≤ I.d v x)]
  have h1 : ∑ x ∈ I.L v with f v ≤ I.d v x, (I.d v x + 1) =
      ∑ x ∈ I.L v with f v ≤ I.d v x, (I.d v x - f v + 1) +
        #{x ∈ I.L v | f v ≤ I.d v x} * f v := by
    rw [← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := (Finset.mem_filter.1 hx).2
    omega
  have h2 : ∑ x ∈ I.L v with ¬ f v ≤ I.d v x, (I.d v x + 1) ≤
      #{x ∈ I.L v | ¬ f v ≤ I.d v x} * f v := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x hx => ?_
    have := (Finset.mem_filter.1 hx).2
    omega
  have h3 := Finset.card_filter_add_card_filter_not (s := I.L v) (fun x => f v ≤ I.d v x)
  rw [← h3, add_mul]
  omega

omit [DecidableEq α] in
/-- First display in the proof of Theorem 1.1 of [FK24]: if the original instance satisfies (7),
`∑_{x ∈ L_v} (d_v(x)+1) > (1+ε) · max(p, |L_v|/p) · β_v`, and `f_v ≤ ε β_v / p`, then the reduced
instance on `G'` satisfies (2). -/
theorem reducedSlack (out : V → Finset V) (Ψ : V → ℕ) (I : ListInstance V α) {p : ℕ}
    (hp : 1 ≤ p) {ε : ℝ} (hε : 0 ≤ ε) (v : V)
    (hslack : (1 + ε) * max (p : ℝ) ((I.L v).card / p) * beta out v < I.weight v) :
    max (p : ℝ) (((reducedInstance I (defectCut out ε p)).L v).card / p) *
        beta (reducedOut out Ψ) v < (reducedInstance I (defectCut out ε p)).weight v := by
  set f := defectCut out ε p
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hW := weight_le_reduced I f v
  have hWR : (I.weight v : ℝ) ≤ (reducedInstance I f).weight v + (I.L v).card * f v := by
    exact_mod_cast hW
  have hf : (f v : ℝ) ≤ ε * beta out v / p := Nat.floor_le (by positivity)
  have hβ' : (beta (reducedOut out Ψ) v : ℝ) ≤ beta out v := by
    exact_mod_cast beta_reducedOut_le out Ψ v
  have hL' : (((reducedInstance I f).L v).card : ℝ) ≤ (I.L v).card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  set n : ℝ := ((I.L v).card : ℝ)
  set β : ℝ := ((beta out v : ℕ) : ℝ)
  set M := max (p : ℝ) (n / p)
  have hβ0 : 0 ≤ β := by positivity
  have hM : n / p ≤ M := le_max_right _ _
  have hM' : max (p : ℝ) (((reducedInstance I f).L v).card / p) ≤ M :=
    max_le_max le_rfl (div_le_div_of_nonneg_right hL' hp'.le)
  have hM0 : 0 ≤ M := le_trans hp'.le (le_max_left _ _)
  -- n f ≤ ε β n / p
  have hnf : n * f v ≤ ε * β * (n / p) := by
    have : n * f v ≤ n * (ε * β / p) := mul_le_mul_of_nonneg_left hf (by positivity)
    calc n * f v ≤ n * (ε * β / p) := this
      _ = ε * β * (n / p) := by ring
  have h1 : max (p : ℝ) (((reducedInstance I f).L v).card / p) *
      beta (reducedOut out Ψ) v ≤ M * β :=
    mul_le_mul hM' hβ' (by positivity) hM0
  have h2 : ε * β * (n / p) ≤ ε * β * M := mul_le_mul_of_nonneg_left hM (by positivity)
  nlinarith

/-- A solution of the reduced instance on `G'` solves the original instance on `G`: monochromatic
(w.r.t. `Ψ`) out-neighbours contribute at most `f_v` additional conflicts (second paragraph of the
proof of Theorem 1.1). -/
theorem IsOLDC.of_reduced {out : V → Finset V} {Ψ : V → ℕ} {I : ListInstance V α}
    {f : V → ℕ} (hΨ : ∀ v, #{u ∈ out v | Ψ u = Ψ v} ≤ f v) {col : V → α}
    (h : IsOLDC (reducedInstance I f) (reducedOut out Ψ) col) : IsOLDC I out col := by
  classical
  intro v
  obtain ⟨hmem, hle⟩ := h v
  simp only [reducedInstance, Finset.mem_filter] at hmem hle
  refine ⟨hmem.1, ?_⟩
  have hsplit : {u ∈ out v | col u = col v} ⊆
      {u ∈ reducedOut out Ψ v | col u = col v} ∪ {u ∈ out v | Ψ u = Ψ v} := by
    intro u hu
    simp only [Finset.mem_union, Finset.mem_filter, reducedOut] at hu ⊢
    by_cases hΨu : Ψ u = Ψ v
    · exact Or.inr ⟨hu.1, hΨu⟩
    · exact Or.inl ⟨⟨hu.1, hΨu⟩, hu.2⟩
  have := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  have := hΨ v
  omega

/-- **Theorem 1.1** of [FK24] (Algorithm 2). Let `p ≥ 1`, `ε ≥ 0`, and assume (7):
`∑_{x ∈ L_v} (d_v(x)+1) > (1+ε) · max(p, |L_v|/p) · β_v` for all `v`. Let `Ψ` be a colouring with
values `< K` in which every node has at most `⌊ε β_v / p⌋` out-neighbours of its own `Ψ`-colour
(the output of Lemma 3.4, with `K = O(p²/ε²)`). Then, after `2K` rounds of the Two-Sweep
algorithm on the reduced instance (`reducedOut`, `reducedInstance`) with initial colouring `Ψ`,
every node has output a colour and these colours solve the original OLDC instance.

For `ε = 0` the hypothesis on `Ψ` says that `Ψ` is proper along out-edges, so this also covers the
`O(q)`-round case (take `Ψ` the initial `q`-colouring; see also `twoSweep_correct`). -/
theorem fastTwoSweep_correct (G : SimpleGraph V) (out : V → Finset V)
    (hout : ∀ v, ∀ u ∈ out v, G.Adj v u) (I : ListInstance V α) (p : ℕ) (hp : 1 ≤ p) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hslack : ∀ v, (1 + ε) * max (p : ℝ) ((I.L v).card / p) * beta out v < I.weight v)
    (Ψ : V → ℕ) (K : ℕ) (hΨK : ∀ v, Ψ v < K)
    (hΨ : ∀ v, #{u ∈ out v | Ψ u = Ψ v} ≤ defectCut out ε p v) :
    ∃ col : V → α,
      (∀ v, ((twoSweep p K).run G
          (initState (reducedOut out Ψ) Ψ (reducedInstance I (defectCut out ε p))) (2 * K) v).col
          = some (col v)) ∧
        IsOLDC I out col := by
  obtain ⟨col, hrun, hcol⟩ := twoSweep_correct G (reducedOut out Ψ)
    (fun v u hu => hout v u (Finset.mem_filter.1 hu).1) Ψ K hΨK
    (fun v u hu => (Finset.mem_filter.1 hu).2) (reducedInstance I (defectCut out ε p)) p hp
    (fun v => reducedSlack out Ψ I hp hε v (hslack v))
  exact ⟨col, hrun, hcol.of_reduced hΨ⟩

end FK24
