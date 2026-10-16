import Papers.PODC2017.StatelessComputation.Impossibility

/-!
# Example 1: tightness of Theorem 3.1

Dolev, Erdmann, Lutz, Schapira, Zair, *Stateless Computation*, PODC 2017, Section 3, Example 1.

The protocol on the complete digraph `Kₙ` (no self-loops) with label space `{0,1}`: every node
sends `1` on all its outgoing arcs iff some incoming arc carries `1` (and outputs the same bit).
It has two stable labelings (all `0`, all `1`), so by Theorem 3.1 it is not label
`(n-1)`-stabilizing; Example 1 claims that it is label `(n-2)`-stabilizing.

## Main results

* `allTrue_stable`, `allFalse_stable`, `allTrue_ne_allFalse`: two distinct stable labelings.
* `labelStabilizing`: the protocol is label `(n-2)`-stabilizing.
* `or_tight`: label `(n-2)`-stabilizing but not label `(n-1)`-stabilizing (`n ≥ 2`).
* `outputs_converge_of_run_converges`: general helper — converging labels under an `r`-fair
  schedule imply converging outputs.
-/

namespace StatelessComputation

/-- If the labeling sequence converges under an `r`-fair schedule, so does every node's
output sequence. -/
theorem outputs_converge_of_run_converges {V : Type*} [DecidableEq V] {G : Digraph V}
    {L X Y : Type*} (P : Protocol G L X Y) (x : V → X) {r : ℕ} {σ : ℕ → Finset V}
    (hσ : IsRFair r σ) (ℓ0 : Labeling G L) (y0 : V → Y) (h : Converges (P.run x ℓ0 σ))
    (i : V) : Converges (fun t => P.outputs x ℓ0 y0 σ t i) := by
  obtain ⟨a, T, hT⟩ := h
  obtain ⟨s, hs1, -, hs3⟩ := hσ.2 T i
  refine ⟨(P.δ i (inLab a i) (x i)).2, s + 1, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => simp [Protocol.outputs, hs3, hT s hs1]
  | succ t ht ih =>
    simp only [Protocol.outputs]
    split_ifs
    · rw [hT t (by omega)]
    · exact ih

/-- An `r`-fair schedule has `r ≥ 1` (there are no `0`-fair schedules). -/
lemma IsRFair.pos {V : Type*} {r : ℕ} {σ : ℕ → Finset V} (h : IsRFair r σ) : 1 ≤ r := by
  obtain ⟨v, -⟩ := h.1 0
  obtain ⟨s, h1, h2, -⟩ := h.2 0 v
  omega

namespace Example1

open Finset

/-- The complete digraph on `Fin n` without self-loops. -/
def K (n : ℕ) : Digraph (Fin n) where
  Adj u v := u ≠ v

instance (n : ℕ) : DecidableRel (K n).Adj := fun u v => inferInstanceAs (Decidable (u ≠ v))

/-- The protocol of Example 1: send (and output) `1` iff some incoming label is `1`. -/
def P (n : ℕ) : Protocol (K n) Bool Unit Bool where
  δ _ inl _ := (fun _ => decide (∃ u, inl u = true), decide (∃ u, inl u = true))

variable {n : ℕ}

/-- The all-`1` labeling. -/
def allTrue : Labeling (K n) Bool := fun _ => true

/-- The all-`0` labeling. -/
def allFalse : Labeling (K n) Bool := fun _ => false

/-- Example 1 of [paper]: the all-`1` labeling is stable. -/
theorem allTrue_stable (x : Fin n → Unit) : (P n).IsStable x allTrue := by
  intro i w
  simp only [P, allTrue, inLab, decide_eq_true_eq]
  exact ⟨⟨w.1, fun h => w.2 h.symm⟩, trivial⟩

/-- Example 1 of [paper]: the all-`0` labeling is stable. -/
theorem allFalse_stable (x : Fin n → Unit) : (P n).IsStable x allFalse := by
  intro i w
  simp [P, allFalse, inLab]

theorem allTrue_ne_allFalse (hn : 2 ≤ n) : (allTrue : Labeling (K n) Bool) ≠ allFalse := by
  intro h
  have := congrFun h ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [K]⟩
  simp [allTrue, allFalse] at this

/-! ### Reduction to a Boolean dynamics on nodes -/

/-- The labeling in which every node sends its bit `b i` on all outgoing arcs. -/
def lab (b : Fin n → Bool) : Labeling (K n) Bool := fun e => b e.1.1

/-- The node-level dynamics: activated nodes compute the OR of the other nodes' bits. -/
def bstep (b : Fin n → Bool) (T : Finset (Fin n)) : Fin n → Bool := fun i =>
  if i ∈ T then decide (∃ u, u ≠ i ∧ b u = true) else b i

lemma step_lab (x : Fin n → Unit) (b : Fin n → Bool) (T : Finset (Fin n)) :
    (P n).step x (lab b) T = lab (bstep b T) := by
  funext e
  by_cases h : e.1.1 ∈ T
  · rw [Protocol.step_of_mem _ _ h]
    simp only [P, lab, bstep, inLab, h, ite_true]
    simp only [Subtype.exists, K, exists_prop]
  · rw [Protocol.step_of_not_mem _ _ h]
    simp [lab, bstep, h]

/-- Once node `i` has been activated, all its outgoing arcs carry the same label. -/
lemma unif_run (x : Fin n → Unit) (ℓ0 : Labeling (K n) Bool) (σ : ℕ → Finset (Fin n))
    (i : Fin n) : ∀ t, (∃ s, s < t ∧ i ∈ σ s) →
      ∃ c, ∀ j (h : (K n).Adj i j), (P n).run x ℓ0 σ t ⟨(i, j), h⟩ = c := by
  intro t
  induction t with
  | zero => rintro ⟨s, hs, -⟩; omega
  | succ t ih =>
    intro hex
    by_cases hi : i ∈ σ t
    · refine ⟨decide (∃ u, inLab ((P n).run x ℓ0 σ t) i u = true), fun j h => ?_⟩
      rw [Protocol.run_succ, Protocol.step_of_mem _ _ (by exact hi)]
      rfl
    · obtain ⟨s, hs, his⟩ := hex
      have hst : s < t := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hs with h | h
        · exact h
        · exact absurd (h ▸ his) hi
      obtain ⟨c, hc⟩ := ih ⟨s, hst, his⟩
      refine ⟨c, fun j h => ?_⟩
      rw [Protocol.run_succ, Protocol.step_of_not_mem _ _ (by exact hi)]
      exact hc j h

/-- The node-bit sequence. -/
def bseq (b0 : Fin n → Bool) (τ : ℕ → Finset (Fin n)) : ℕ → Fin n → Bool
  | 0 => b0
  | k + 1 => bstep (bseq b0 τ k) (τ k)

/-- The set of nodes with bit `1`. -/
def ones (b : Fin n → Bool) : Finset (Fin n) := univ.filter fun i => b i = true

/-- Convergence of the Boolean dynamics under an `(n-2)`-fair schedule. -/
theorem bseq_converges (b0 : Fin n → Bool) (τ : ℕ → Finset (Fin n))
    (hτ : IsRFair (n - 2) τ) : ∃ a K, ∀ k, K ≤ k → bseq b0 τ k = a := by
  have hr := hτ.pos
  set b := bseq b0 τ with hbdef
  have hb : ∀ k, b (k + 1) = bstep (b k) (τ k) := fun k => rfl
  by_cases h2 : ∃ k, 2 ≤ (ones (b k)).card
  · -- two `1`s: the set of `1`s only grows, and every activated node becomes `1`
    obtain ⟨k, hk⟩ := h2
    have mono : ∀ k', 2 ≤ (ones (b k')).card →
        (∀ i, b k' i = true → b (k' + 1) i = true) ∧ ∀ i ∈ τ k', b (k' + 1) i = true := by
      intro k' hk'
      have act : ∀ i ∈ τ k', b (k' + 1) i = true := by
        intro i hi
        obtain ⟨u, hu, hui⟩ := Finset.exists_mem_ne (s := ones (b k')) (by omega) i
        rw [hb]
        simp only [bstep, hi, ite_true, decide_eq_true_eq]
        exact ⟨u, hui, (mem_filter.1 hu).2⟩
      refine ⟨fun i hi => ?_, act⟩
      by_cases hiτ : i ∈ τ k'
      · exact act i hiτ
      · rw [hb]; simp [bstep, hiτ, hi]
    have main : ∀ k', k ≤ k' → 2 ≤ (ones (b k')).card ∧
        ∀ i, (∃ s, k ≤ s ∧ s < k' ∧ i ∈ τ s) → b k' i = true := by
      intro k' hk'
      induction k', hk' using Nat.le_induction with
      | base => exact ⟨hk, fun i ⟨s, h1, h2, _⟩ => by omega⟩
      | succ k' hk' ih =>
        obtain ⟨ih1, ih2⟩ := ih
        obtain ⟨m1, m2⟩ := mono k' ih1
        refine ⟨ih1.trans (card_le_card fun i hi => ?_), fun i ⟨s, hs1, hs2, hs3⟩ => ?_⟩
        · exact mem_filter.2 ⟨mem_univ _, m1 i (mem_filter.1 hi).2⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hs2 with h | h
          · exact m1 i (ih2 i ⟨s, hs1, h, hs3⟩)
          · exact m2 i (h ▸ hs3)
    refine ⟨fun _ => true, k + (n - 2), fun k' hk' => funext fun i => ?_⟩
    obtain ⟨s, hs1, hs2, hs3⟩ := hτ.2 k i
    exact (main k' (by omega)).2 i ⟨s, hs1, by omega, hs3⟩
  by_cases h0 : ∃ k, (ones (b k)).card = 0
  · -- no `1`: the all-`0` configuration is a fixed point
    obtain ⟨k, hk⟩ := h0
    have hk0 : b k = fun _ => false := by
      funext i
      by_contra hi
      have : i ∈ ones (b k) := mem_filter.2 ⟨mem_univ _, by simpa using hi⟩
      rw [card_eq_zero.1 hk] at this
      simp at this
    refine ⟨fun _ => false, k, fun k' hk' => ?_⟩
    induction k', hk' using Nat.le_induction with
    | base => exact hk0
    | succ k' _ ih =>
      rw [hb, ih]; funext i; simp [bstep]
  · -- exactly one `1` forever: impossible under `(n-2)`-fairness
    exfalso
    push Not at h2 h0
    have h1 : ∀ k, (ones (b k)).card = 1 := fun k => by
      have := h2 k; have := h0 k; omega
    choose I hI using fun k => card_eq_one.1 (h1 k)
    have hsub : ∀ k, τ k ⊆ {I k, I (k + 1)} := by
      intro k j hj
      by_cases hjk : j = I k
      · simp [hjk]
      · have : j ∈ ones (b (k + 1)) := by
          refine mem_filter.2 ⟨mem_univ _, ?_⟩
          rw [hb]
          simp only [bstep, hj, ite_true, decide_eq_true_eq]
          have : I k ∈ ones (b k) := by rw [hI k]; exact mem_singleton_self _
          exact ⟨I k, Ne.symm hjk, (mem_filter.1 this).2⟩
        rw [hI (k + 1), mem_singleton] at this
        simp [this]
    have hcov : (univ : Finset (Fin n)) ⊆ (range (n - 2 + 1)).image I := by
      intro i _
      obtain ⟨s, -, hs2, hs3⟩ := hτ.2 0 i
      have := hsub s hs3
      rcases mem_insert.1 this with h | h
      · exact mem_image.2 ⟨s, mem_range.2 (by omega), h.symm⟩
      · exact mem_image.2 ⟨s + 1, mem_range.2 (by omega), (mem_singleton.1 h).symm⟩
    have := (card_le_card hcov).trans card_image_le
    simp only [card_univ, Fintype.card_fin, card_range] at this
    omega

/-- **Example 1** of [Dolev–Erdmann–Lutz–Schapira–Zair, PODC'17]: the OR protocol on `Kₙ` is
label `(n-2)`-stabilizing (for every input, initial labeling, initial outputs and
`(n-2)`-fair schedule, labels and outputs converge). -/
theorem labelStabilizing : LabelStabilizing (n - 2) (P n) := by
  have hlab : ∀ x ℓ0 σ, IsRFair (n - 2) σ → Converges ((P n).run x ℓ0 σ) := by
    intro x ℓ0 σ hσ
    set r := n - 2 with hrdef
    have hr := hσ.pos
    have hu : ∀ i, ∃ c, ∀ j (h : (K n).Adj i j), (P n).run x ℓ0 σ r ⟨(i, j), h⟩ = c := by
      intro i
      obtain ⟨s, -, hs2, hs3⟩ := hσ.2 0 i
      exact unif_run x ℓ0 σ i r ⟨s, by omega, hs3⟩
    choose b0 hb0 using hu
    have hrun0 : (P n).run x ℓ0 σ r = lab b0 := by
      funext e; exact hb0 e.1.1 e.1.2 e.2
    let τ : ℕ → Finset (Fin n) := fun k => σ (r + k)
    have hτ : IsRFair r τ := by
      refine ⟨fun t => hσ.1 _, fun t v => ?_⟩
      obtain ⟨s, h1, h2, h3⟩ := hσ.2 (r + t) v
      exact ⟨s - r, by omega, by omega, by simp only [τ]; rwa [Nat.add_sub_cancel' (by omega)]⟩
    have hrun : ∀ k, (P n).run x ℓ0 σ (r + k) = lab (bseq b0 τ k) := by
      intro k
      induction k with
      | zero => exact hrun0
      | succ k ih =>
        rw [← add_assoc, Protocol.run_succ, ih, step_lab]; rfl
    obtain ⟨a, K, hK⟩ := bseq_converges b0 τ hτ
    refine ⟨lab a, r + K, fun t ht => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, t = r + k := ⟨t - r, by omega⟩
    rw [hrun, hK k (by omega)]
  exact ⟨fun x ℓ0 y0 σ hσ i =>
    outputs_converge_of_run_converges _ x hσ ℓ0 y0 (hlab x ℓ0 σ hσ) i, hlab⟩

/-- **Example 1 / tightness of Theorem 3.1** of [Dolev–Erdmann–Lutz–Schapira–Zair, PODC'17]:
for `n ≥ 2`, the OR protocol on `Kₙ` has two distinct stable labelings, is label
`(n-2)`-stabilizing, and (by Theorem 3.1) is not label `(n-1)`-stabilizing. -/
theorem or_tight (hn : 2 ≤ n) :
    LabelStabilizing (n - 2) (P n) ∧ ¬ LabelStabilizing (n - 1) (P n) := by
  refine ⟨labelStabilizing, ?_⟩
  exact not_labelStabilizing (G := K n) (fun v h => h rfl) (P n) (fun _ => ())
    (allTrue_stable _) (allFalse_stable _) (allTrue_ne_allFalse hn) (by simp)

end Example1

end StatelessComputation
