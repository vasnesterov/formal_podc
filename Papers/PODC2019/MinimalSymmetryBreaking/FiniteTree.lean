import Papers.PODC2019.MinimalSymmetryBreaking.Lemmas78
import Papers.PODC2019.MinimalSymmetryBreaking.FieldProd
import Papers.PODC2019.MinimalSymmetryBreaking.Packing
import Papers.PODC2019.MinimalSymmetryBreaking.Asymptotics

/-!
# Finite trees with identifiers: Claim 10, Lemma 9, Theorems 6 and 13

The instances are finite sets `V` of nodes of the oriented `2k`-regular tree containing a ball
`B_K` around the origin; the network is the subgraph induced by `V` (with `V` connected, as in
`exists_subtree`, it is a tree of maximum degree `2k` whose ball `B_K` is a complete `2k`-regular
ball, with a consistent orientation). Every node has a unique identifier in `Fin n`, `n = |V|`,
and an independent random value from `(Ω, μ)`.

A `t`-round algorithm (`IdAlg`) maps what a node sees within distance `t` — which of the nodes
exist, their identifiers and random values, with the orientation — to a colour `Bool`. (It sees
the nodes of `V` within tree distance `t`; for a connected `V` these are exactly the nodes within
distance `t` in the network. It also knows `n`.)

Claim 10 (`succProb_le`): from a lower bound `q` on the local failure probability of anonymous
algorithms (with randomness `Fin n × Ω`), every algorithm with identifiers succeeds with
probability at most `(1-q)^|S| + |B_K|²/n` for some identifier assignment, where `S ⊆ B_{K-t-1}`
is any set of nodes with pairwise disjoint `(t+1)`-balls. The paper takes nodes at pairwise
distance `≥ 2t+1`; their failure events (which depend on the `(t+1)`-balls) need not be
independent, so we use disjoint `(t+1)`-balls (distance `≥ 2t+3`).
-/

namespace Podc.MinimalSymmetryBreaking

open Finset Function
open scoped Classical

noncomputable section

variable {k : ℕ} {Ω : Type} [Fintype Ω] [Inhabited Ω] (μ : FinDist Ω) {n t : ℕ} [NeZero n]

/-- A `t`-round randomized algorithm with identifiers in `Fin n` on finite subtrees of the oriented
tree: the output of the origin as a function of the labels `some (id, random value)` of the nodes
of the network and `none` for the nodes that do not exist, within distance `t`. -/
structure IdAlg (k n : ℕ) (Ω : Type) (t : ℕ) where
  /-- The colour of the origin. -/
  out : (Tree k → Option (Fin n × Ω)) → Bool
  /-- It only depends on the labels within distance `t`. -/
  dep : DependsOn out (ball 1 t)

/-- The labelling of the instance `V` with identifiers `id` and random values `x`. -/
def label (V : Finset (Tree k)) (id : Tree k → Fin n) (x : Tree k → Ω) :
    Tree k → Option (Fin n × Ω) :=
  fun w => if w ∈ V then some (id w, x w) else none

/-- The colour of node `v`. -/
def IdAlg.output (A : IdAlg k n Ω t) (V : Finset (Tree k)) (id : Tree k → Fin n)
    (x : Tree k → Ω) (v : Tree k) : Bool :=
  A.out (shift v (label V id x))

/-- The algorithm produces a weak 2-colouring of the network: every node of `V` has a neighbour
in `V` of the other colour. -/
def IdAlg.Success (A : IdAlg k n Ω t) (V : Finset (Tree k)) (id : Tree k → Fin n)
    (x : Tree k → Ω) : Prop :=
  ∀ v ∈ V, ∃ p, v * dir p ∈ V ∧ A.output V id x (v * dir p) ≠ A.output V id x v

/-- The (global) success probability. -/
def IdAlg.succProb (A : IdAlg k n Ω t) (V : Finset (Tree k)) (id : Tree k → Fin n) : ℝ :=
  prob μ V (A.Success V id)

/-- The anonymous algorithm on the infinite tree that uses its random value `(i, ω)` as
(possibly non-unique) identifier `i` and random value `ω`. -/
def IdAlg.anon (A : IdAlg k n Ω t) : NodeAlg k (Fin n × Ω) t Bool where
  out z := A.out (fun w => some (z w))
  dep := by
    intro z z' h
    apply A.dep
    intro w hw; simp [h w hw]

/-- Extending identifiers that are injective on `R ⊆ V` to identifiers injective on `V`. -/
lemma exists_injOn_extend {R V : Finset (Tree k)} (hRV : R ⊆ V) (hV : V.card = n)
    {y : Tree k → Fin n} (hy : Set.InjOn y R) :
    ∃ id : Tree k → Fin n, Set.InjOn id V ∧ ∀ w ∈ R, id w = y w := by
  set A' := V \ R
  set B' := (univ : Finset (Fin n)) \ R.image y
  have hcard : Fintype.card A' = Fintype.card B' := by
    simp only [Fintype.card_coe, A', B']
    rw [card_sdiff_of_subset hRV, card_sdiff_of_subset (subset_univ _), card_univ,
      Fintype.card_fin, card_image_of_injOn hy, hV]
  let e : A' ≃ B' := Fintype.equivOfCardEq hcard
  refine ⟨fun w => if w ∈ R then y w else if h : w ∈ A' then (e ⟨w, h⟩).1 else 0, ?_, ?_⟩
  · intro w₁ h₁ w₂ h₂ heq
    simp only at heq
    have hB : ∀ (w : Tree k) (h : w ∈ A'), (e ⟨w, h⟩).1 ∉ R.image y := fun w h => by
      have := (e ⟨w, h⟩).2; simp only [B', mem_sdiff] at this; exact this.2
    by_cases r₁ : w₁ ∈ R <;> by_cases r₂ : w₂ ∈ R
    · simp only [r₁, r₂, if_true] at heq; exact hy r₁ r₂ heq
    · have a₂ : w₂ ∈ A' := by simp [A', mem_coe.1 h₂, r₂]
      simp only [r₁, r₂, if_true, if_false, dif_pos a₂] at heq
      exact absurd (heq ▸ mem_image_of_mem y r₁) (hB w₂ a₂)
    · have a₁ : w₁ ∈ A' := by simp [A', mem_coe.1 h₁, r₁]
      simp only [r₁, r₂, if_true, if_false, dif_pos a₁] at heq
      exact absurd (heq.symm ▸ mem_image_of_mem y r₂) (hB w₁ a₁)
    · have a₁ : w₁ ∈ A' := by simp [A', mem_coe.1 h₁, r₁]
      have a₂ : w₂ ∈ A' := by simp [A', mem_coe.1 h₂, r₂]
      simp only [r₁, r₂, if_false, dif_pos a₁, dif_pos a₂] at heq
      have := e.injective (Subtype.ext heq)
      simpa using this
  · intro w hw; simp [hw]

variable {μ}

lemma fail_shift_dependsOn {Ω' : Type} [Fintype Ω'] [Inhabited Ω'] {β : Type}
    (B : NodeAlg k Ω' t β) (s : Tree k) :
    DependsOn (fun z => B.Fail (shift s z)) (ball s (t + 1)) := by
  have := dependsOn_shift B.fail_dependsOn s
  rwa [preimage_inv_mul_ball, mul_one] at this

/-- **Claim 10.** If every anonymous `t`-round weak 2-colouring algorithm (with randomness
`Fin n × Ω`) fails locally with probability at least `q`, then for every `t`-round algorithm with
identifiers there is an identifier assignment under which it succeeds with probability at most
`(1 − q)^|S| + |B_K|² / n`, for every `S ⊆ B_{K−t−1}` with pairwise disjoint `(t+1)`-balls. -/
theorem succProb_le (A : IdAlg k n Ω t) {V : Finset (Tree k)} (hVn : V.card = n) {K : ℕ}
    (htK : t + 1 ≤ K) (hKV : Ball K ⊆ V) {S : Finset (Tree k)} (hS : S ⊆ Ball (K - (t + 1)))
    (hsep : Separated (t + 1) S) {q : ℝ}
    (hq : q ≤ A.anon.failProb ((FinDist.uniform n).prod μ)) :
    ∃ id : Tree k → Fin n, Set.InjOn id V ∧
      A.succProb μ V id ≤ (1 - q) ^ S.card + ((Ball K : Finset (Tree k)).card : ℝ) ^ 2 / n := by
  set μ' := (FinDist.uniform n).prod μ
  set R : Finset (Tree k) := Ball K
  set B := A.anon
  have hsR : ∀ s ∈ S, ball s (t + 1) ⊆ (R : Set (Tree k)) := by
    intro s hs
    apply ball_subset_Ball
    have := mem_Ball.1 (hS hs); omega
  -- the event "all nodes of `S` are happy" in the anonymous world
  let E : (Tree k → Fin n × Ω) → Prop := fun z => ∀ s ∈ S, ¬ B.Fail (shift s z)
  -- Step 1: `Pr[E] ≤ (1 - q)^|S|` by independence
  have step1 : prob μ' R E ≤ (1 - q) ^ S.card := by
    have hind : ∀ z, ind E z = ∏ s ∈ S, (1 - ind (fun z => B.Fail (shift s z)) z) := by
      intro z
      by_cases h : E z
      · rw [show ind E z = 1 by simp [ind, h]]
        symm; apply prod_eq_one; intro s hs; simp [ind, h s hs]
      · simp only [E, not_forall, not_not] at h
        obtain ⟨s, hs, hf⟩ := h
        rw [prod_eq_zero hs (by simp [ind, hf])]
        simp only [ind]; rw [if_neg]; simp only [E, not_forall, not_not]; exact ⟨s, hs, hf⟩
    unfold prob
    rw [show ind E = fun z => ∏ s ∈ S, (1 - ind (fun z => B.Fail (shift s z)) z) from funext hind,
      expect_prod_of_disjoint S (D := fun s => ball s (t + 1))]
    · rw [← prod_const]
      apply prod_le_prod₀
      · intro s _
        rw [expect_sub, expect_const]
        have := prob_le_one (μ := μ') R (fun z => B.Fail (shift s z))
        unfold prob at this; linarith
      · intro s hs
        rw [expect_sub, expect_const]
        have : prob μ' R (fun z => B.Fail (shift s z)) = B.failProb μ' := by
          unfold NodeAlg.failProb
          apply prob_shift B.fail_dependsOn subset_rfl
          intro w hw
          simp only [mem_ball, inv_one, one_mul] at hw
          have := FreeGroup.norm_mul_le s w
          have := mem_Ball.1 (hS hs); omega
        change 1 - prob μ' R _ ≤ 1 - q
        rw [this]; linarith
    · intro s _
      intro z z' h
      simp only [ind, fail_shift_dependsOn B s h]
    · exact hsep
  -- Step 2: identifiers collide with probability at most `|R|²/n`
  have step2 : prob (FinDist.uniform n) R (fun y => ¬ Set.InjOn y R) ≤ (R.card : ℝ) ^ 2 / n :=
    prob_not_injOn_le R R subset_rfl
  -- Step 3: choose good identifiers on `R`
  set P : (Tree k → Fin n) → ℝ := fun y => prob μ R (fun x => E (fun i => (y i, x i)))
  have hPE : expect (FinDist.uniform n) R P = prob μ' R E := by
    unfold prob; rw [expect_prod]; rfl
  obtain ⟨y, hy, hPy⟩ : ∃ y : Tree k → Fin n, Set.InjOn y R ∧
      P y ≤ (1 - q) ^ S.card + (R.card : ℝ) ^ 2 / n := by
    by_cases hδ : (R.card : ℝ) ^ 2 / n < 1
    · have hpos : 0 < prob (FinDist.uniform n) R (fun y => Set.InjOn y R) := by
        have : prob (FinDist.uniform n) R (fun y => Set.InjOn y R) +
            prob (FinDist.uniform n) R (fun y => ¬ Set.InjOn y R) = 1 := by
          unfold prob; rw [← expect_add]
          have : ∀ y : Tree k → Fin n, ind (fun y => Set.InjOn y R) y +
              ind (fun y => ¬ Set.InjOn y R) y = 1 := fun y => by
            by_cases h : Set.InjOn y R <;> simp [ind, h]
          simp only [this, expect_const]
        linarith
      obtain ⟨y, hy, hle⟩ := exists_le_of_expect (h := P) hpos
      refine ⟨y, hy, ?_⟩
      have h1 : expect (FinDist.uniform n) R (fun x => ind (fun y => Set.InjOn y R) x * P x) ≤
          prob μ' R E := by
        rw [← hPE]; apply expect_mono; intro x
        have := ind_le_one (fun y => Set.InjOn y R) x
        have : 0 ≤ P x := prob_nonneg _ _
        nlinarith [ind_nonneg (fun y => Set.InjOn y R) x]
      have hcompl : prob (FinDist.uniform n) R (fun y => Set.InjOn y R) =
          1 - prob (FinDist.uniform n) R (fun y => ¬ Set.InjOn y R) := by
        have : prob (FinDist.uniform n) R (fun y => Set.InjOn y R) +
            prob (FinDist.uniform n) R (fun y => ¬ Set.InjOn y R) = 1 := by
          unfold prob; rw [← expect_add]
          have : ∀ y : Tree k → Fin n, ind (fun y => Set.InjOn y R) y +
              ind (fun y => ¬ Set.InjOn y R) y = 1 := fun y => by
            by_cases h : Set.InjOn y R <;> simp [ind, h]
          simp only [this, expect_const]
        linarith
      have hP1 : P y ≤ 1 := prob_le_one _ _
      have hP0 : 0 ≤ P y := prob_nonneg _ _
      rw [hcompl] at hle
      nlinarith [prob_nonneg (μ := FinDist.uniform n) R (fun y => ¬ Set.InjOn y R)]
    · push_neg at hδ
      obtain ⟨id, hid, -⟩ := exists_injOn_extend (R := ∅) (empty_subset V) hVn
        (y := fun _ => 0) (by simp)
      refine ⟨id, hid.mono (by simpa using hKV), ?_⟩
      have := prob_le_one (μ := μ) R (fun x => E (fun i => (id i, x i)))
      have : 0 ≤ (1 - q) ^ S.card := by
        apply pow_nonneg
        have := hq.trans (prob_le_one _ _); linarith
      linarith
  -- Step 4: extend to identifiers on `V` and compare with the anonymous world
  obtain ⟨id, hid, hidy⟩ := exists_injOn_extend hKV hVn hy
  refine ⟨id, hid, le_trans ?_ hPy⟩
  have hdepE : DependsOn (fun x : Tree k → Ω => E (fun i => (y i, x i))) (R : Set (Tree k)) := by
    intro x x' h
    simp only [E]
    apply propext; apply forall₂_congr; intro s hs
    have e : B.Fail (shift s fun i => (y i, x i)) = B.Fail (shift s fun i => (y i, x' i)) :=
      fail_shift_dependsOn B s (fun w hw => by simp [h w (hsR s hs hw)])
    rw [e]
  have hPV : P y = prob μ V (fun x => E (fun i => (y i, x i))) := by
    unfold P prob
    exact (expect_eq_of_subset hKV (ind_dependsOn hdepE)).symm
  rw [hPV]
  apply prob_mono
  intro x hsucc s hs
  have hsV : s ∈ V := hKV (hS hs |> fun h => by
    rw [mem_Ball] at h ⊢; omega)
  obtain ⟨p, hpV, hne⟩ := hsucc s hsV
  intro hfail
  apply hne
  -- outputs near `s` agree with the anonymous outputs
  have hout : ∀ v : Tree k, ball v t ⊆ ball s (t + 1) →
      A.output V id x v = B.out (shift v (fun i => (y i, x i))) := by
    intro v hv
    unfold IdAlg.output
    apply A.dep
    intro h hh
    have hvh : v * h ∈ R := by
      apply hsR s hs; apply hv; simpa [mem_ball] using hh
    simp [shift, label, hKV hvh, hidy _ hvh]
  rw [hout (s * dir p) (by
      have := ball_dir_subset s p t; exact this),
    hout s (ball_mono (Nat.le_succ t))]
  have := hfail p
  rw [shift_shift] at this
  exact this

end

end Podc.MinimalSymmetryBreaking
