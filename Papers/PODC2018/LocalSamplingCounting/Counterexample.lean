import Papers.PODC2018.LocalSamplingCounting.SSM

/-!
# Corollary 5.2 fails as stated: the hardcore model

Corollary 5.2 claims that a class of locally admissible, local Gibbs distributions has strong
spatial mixing with exponential decay in total variation distance **iff** it has it in
multiplicative error `err(μ, μ̂) = max_x |ln μ(x) - ln μ̂(x)|` (eq. (2), with only `ln 0 - ln 0 = 0`
as convention).

The direction "TV ⇒ multiplicative" fails already for the hardcore model, at distance `1`: pinning a neighbour `u` of `v` to *occupied* forces
`μ^σ_v(occupied) = 0`, while pinning it to *unoccupied* gives `μ^τ_v(occupied) > 0`, so
`err(μ^σ_v, μ^τ_v) = ∞` and no finite rate `δ_n(1)` can bound it.

* `hardcore G λ`: the hardcore model (weighted independent sets) as a Gibbs distribution;
  `hardcore_locallyAdmissible`, `hardcore_gibbsLocal` (constraints of diameter `≤ 1`).
* `hardcore_not_mssm`: on any graph with an edge, the hardcore model has **no** strong spatial
  mixing in multiplicative error with any real-valued rate.
* `corollary_5_2_false`: the class of hardcore models (`λ = 1`) on perfect matchings
  `matchingGraph m` (`n = 2m` vertices, every `m ≥ 1`) is locally admissible, local, and has strong
  spatial mixing with exponential decay in TV distance (`δ_n(d) = 2 · (1/2)^d`), but has no
  multiplicative strong spatial mixing at all.

The paper's own proof route (Theorem 5.1 for `err`) only bounds `err` at distances `> 2t + ℓ`
where `t` is the locality of the boosted algorithm, which gives decay rate `√α` at large distances.
A version restricted to large distances is plausible but not formalized. See `differencies.md`.
-/

set_option linter.unusedSectionVars false

namespace Podc.LocalSamplingCounting

open Finset

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The factors of the hardcore model: a vertex factor `λ^{σ_v}` per vertex and a hard edge
constraint `¬(σ_u ∧ σ_w)` per ordered adjacent pair. -/
noncomputable def hardcore (G : SimpleGraph V) (lam : ℝ) (hlam : 0 < lam) :
    V ⊕ (V × V) → Factor V Bool
  | Sum.inl v =>
    { scope := {v}
      f := fun σ => if σ v then lam else 1
      nonneg := fun σ => by split_ifs <;> linarith
      dep := fun σ σ' h => by rw [h v (by simp)] }
  | Sum.inr (a, b) =>
    { scope := if G.Adj a b then {a, b} else ∅
      f := fun σ => if G.Adj a b ∧ σ a = true ∧ σ b = true then 0 else 1
      nonneg := fun σ => by split_ifs <;> norm_num
      dep := fun σ σ' h => by
        by_cases hab : G.Adj a b
        · have ha := h a (by simp [hab])
          have hb := h b (by simp [hab])
          rw [ha, hb]
        · simp [hab] }

variable {G : SimpleGraph V} {lam : ℝ} {hlam : 0 < lam}

lemma hardcore_gibbsW_eq_zero {σ : V → Bool} {a b : V} (hab : G.Adj a b) (ha : σ a = true)
    (hb : σ b = true) : gibbsW (hardcore G lam hlam) σ = 0 :=
  Finset.prod_eq_zero (i := Sum.inr (a, b)) (mem_univ _) (by simp [hardcore, hab, ha, hb])

lemma hardcore_gibbsW_pos {σ : V → Bool} (h : ∀ a b, G.Adj a b → ¬ (σ a = true ∧ σ b = true)) :
    0 < gibbsW (hardcore G lam hlam) σ := by
  refine Finset.prod_pos fun i _ => ?_
  rcases i with v | ⟨a, b⟩
  · simp only [hardcore]; split_ifs <;> linarith
  · simp only [hardcore]
    rw [if_neg (fun h' => h a b h'.1 h'.2)]; norm_num

/-- Feasible pinnings are locally feasible (for any Gibbs distribution). -/
lemma locFeasible_of_feasible {S ι : Type*} [Fintype S] [DecidableEq S] [Fintype ι]
    [Nonempty S] {F : ι → Factor V S} {τ : Pin V S} (h : Feasible (gibbsW F) τ) :
    LocFeasible F τ := by
  obtain ⟨σ₀, hc, hw⟩ := exists_pos_of_feasible h
  intro i hi σ hσ
  rw [factor_eq_fill F hσ i hi, ← factor_eq_fill F hc i hi]
  exact factor_pos_of_gibbsW_pos F hw i

/-- **The hardcore model is locally admissible** (Definition 2.5). -/
theorem hardcore_locallyAdmissible : LocallyAdmissible (hardcore G lam hlam) := by
  intro τ
  refine ⟨locFeasible_of_feasible, fun h => ?_⟩
  set σ₀ : V → Bool := fun x => (τ x).getD false
  have hc : Cons σ₀ τ := fun x c hx => by simp [σ₀, hx]
  have hpos : 0 < gibbsW (hardcore G lam hlam) σ₀ := by
    refine hardcore_gibbsW_pos fun a b hab ⟨ha, hb⟩ => ?_
    have hta : τ a = some true := by
      simp only [σ₀] at ha; cases h' : τ a <;> simp_all
    have htb : τ b = some true := by
      simp only [σ₀] at hb; cases h' : τ b <;> simp_all
    have := h (Sum.inr (a, b)) (by
      intro x hx
      simp only [hardcore, if_pos hab, coe_insert, coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> simp [dom, hta, htb]) σ₀ hc
    simp [hardcore, hab, ha, hb] at this
  exact lt_of_lt_of_le hpos (le_Z_of_cons (gibbsW_nonneg _) hc)

/-- **The hardcore model is local**: its constraints have diameter `≤ 1`. -/
theorem hardcore_gibbsLocal : GibbsLocal G (hardcore G lam hlam) 1 := by
  intro i u hu u' hu'
  rcases i with v | ⟨a, b⟩
  · simp only [hardcore, mem_singleton] at hu hu'
    subst hu hu'; simp
  · simp only [hardcore] at hu hu'
    split_ifs at hu hu' with hab
    · simp only [mem_insert, mem_singleton] at hu hu'
      rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl
      · simp
      · exact (SimpleGraph.edist_eq_one_iff_adj.2 hab).le
      · exact (SimpleGraph.edist_eq_one_iff_adj.2 hab.symm).le
      · simp
    · simp at hu

/-- The pinning of the single vertex `u` to `b`. -/
def pinOne (u : V) (b : Bool) : Pin V Bool := fun x => if x = u then some b else none

/-- **The multiplicative error is infinite at distance `1`.** For adjacent `u, v`, pin `u` to
occupied (`σ`) and to unoccupied (`τ`). Both pinnings are feasible, they have the same domain
`{u}`, they differ only at `u` (at distance `1` from `v`), and `v` is free in both. Yet
`μ^σ_v(occupied) = 0 < μ^τ_v(occupied)`, so `err(μ^σ_v, μ^τ_v) = ∞`: no real `ε` bounds it.
(This does not use the degenerate case `v ∈ D`, in which `err` is infinite for every distribution.) -/
theorem hardcore_err_infinite {u v : V} (huv : G.Adj u v) (ε : ℝ) :
    pinOne u true v = none ∧ pinOne u false v = none ∧
    (∀ x, x ≠ u → pinOne u true x = pinOne u false x) ∧
    Feasible (gibbsW (hardcore G lam hlam)) (pinOne u true) ∧
    Feasible (gibbsW (hardcore G lam hlam)) (pinOne u false) ∧
    ¬ MultClose (marg (gibbsW (hardcore G lam hlam)) (pinOne u true) v)
      (marg (gibbsW (hardcore G lam hlam)) (pinOne u false) v) ε := by
  have hne : u ≠ v := G.ne_of_adj huv
  set w := gibbsW (hardcore G lam hlam)
  have hw : ∀ σ, 0 ≤ w σ := gibbsW_nonneg _
  -- configurations with a single occupied vertex
  have single_pos : ∀ a, 0 < w (fun x => decide (x = a)) := fun a =>
    hardcore_gibbsW_pos fun x y hxy ⟨hx, hy⟩ => by
      simp at hx hy; subst hx hy; exact G.ne_of_adj hxy rfl
  have hσ : Feasible w (pinOne u true) :=
    lt_of_lt_of_le (single_pos u) (le_Z_of_cons hw fun x c hx => by
      simp only [pinOne] at hx; split_ifs at hx with hxu
      · cases hx; simp [hxu])
  have hτ : Feasible w (pinOne u false) := by
    have : Cons (fun x => decide (x = v)) (pinOne u false) := fun x c hx => by
      simp only [pinOne] at hx; split_ifs at hx with hxu
      · cases hx; subst hxu; simp [hne]
    exact lt_of_lt_of_le (single_pos v) (le_Z_of_cons hw this)
  refine ⟨by simp [pinOne, hne.symm], by simp [pinOne, hne.symm],
    fun x hx => by simp [pinOne, hx], hσ, hτ, fun h => ?_⟩
  obtain ⟨h1, -⟩ := h true
  -- `μ^σ_v(true) = 0`
  have hzero : marg w (pinOne u true) v true = 0 := by
    unfold marg margNum
    rw [Finset.sum_eq_zero, zero_div]
    intro σ' _
    split_ifs with hc
    · exact hardcore_gibbsW_eq_zero huv (hc.1 u true (by simp [pinOne])) hc.2
    · rfl
  -- `μ^τ_v(true) > 0`
  have hpos : 0 < marg w (pinOne u false) v true := by
    unfold marg
    refine div_pos (lt_of_lt_of_le (single_pos v) ?_) hτ
    unfold margNum
    have hc : Cons (fun x => decide (x = v)) (pinOne u false) ∧ decide (v = v) = true := by
      refine ⟨fun x c hx => ?_, by simp⟩
      simp only [pinOne] at hx; split_ifs at hx with hxu
      · cases hx; subst hxu; simp [hne]
    have := Finset.single_le_sum (f := fun σ' => if Cons σ' (pinOne u false) ∧ σ' v = true then
      w σ' else 0) (fun σ' _ => by split_ifs <;> simp [hw]) (mem_univ (fun x => decide (x = v)))
    simpa [hc] using this
  rw [hzero] at h1
  have := mul_pos (Real.exp_pos (-ε)) hpos
  linarith

/-- **Multiplicative SSM fails for the hardcore model on any graph with an edge**, for every
real-valued rate: pinning a neighbour `u` of `v` to occupied vs. unoccupied gives
`err(μ^σ_v, μ^τ_v) = ∞` at distance `1` (`hardcore_err_infinite`). -/
theorem hardcore_not_mssm {u v : V} (huv : G.Adj u v) (R : ℕ → ℝ) :
    ¬ MSSM G (gibbsW (hardcore G lam hlam)) R := by
  intro h
  have hne : u ≠ v := G.ne_of_adj huv
  obtain ⟨-, -, -, hσ, hτ, hbad⟩ := hardcore_err_infinite (lam := lam) (hlam := hlam) huv (R 1)
  have hdom : ∀ x, pinOne u true x = none ↔ pinOne u false x = none := fun x => by
    simp [pinOne]
  have hagree : ∀ x, G.edist v x < (1 : ℕ) → pinOne u true x = pinOne u false x := fun x hx => by
    have : x = v := by
      have : G.edist v x = 0 := by exact_mod_cast ENat.lt_one_iff_eq_zero.1 (by exact_mod_cast hx)
      exact (SimpleGraph.edist_eq_zero_iff.1 this).symm
    subst this; simp [pinOne, hne.symm]
  exact hbad (h v (pinOne u true) (pinOne u false) hdom hσ hτ 1 hagree)

/-! ### A class with TV strong spatial mixing: hardcore on perfect matchings -/

/-- The perfect matching on `m` edges: vertex `(i, a)` is adjacent to `(i, !a)`. -/
def matchingGraph (m : ℕ) : SimpleGraph (Fin m × Bool) where
  Adj p q := p.1 = q.1 ∧ p.2 ≠ q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

lemma tv_le_one {α : Type*} [Fintype α] {p q : α → ℝ} (hp : IsDist p) (hq : IsDist q) :
    tv p q ≤ 1 := by
  unfold tv
  have : ∑ x, |p x - q x| ≤ ∑ x, (p x + q x) := sum_le_sum fun x _ => by
    rw [abs_le]; constructor <;> linarith [hp.1 x, hq.1 x]
  rw [sum_add_distrib, hp.2, hq.2] at this; linarith

/-- **TV strong spatial mixing with exponential decay** (`δ_n(d) = 2 · (1/2)^d`) for the hardcore
model on a perfect matching. -/
theorem matching_ssm (m : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    SSM (matchingGraph m) (gibbsW (hardcore (matchingGraph m) lam hlam))
      (fun d => ENNReal.ofReal (2 * (1 / 2) ^ d)) := by
  intro v σ τ _ hσ hτ d hagree
  set G := matchingGraph m
  set F := hardcore G lam hlam
  have hw : ∀ σ, 0 ≤ gibbsW F σ := gibbsW_nonneg F
  apply ENNReal.ofReal_le_ofReal
  rcases Nat.lt_or_ge d 2 with hd | hd
  · -- trivial bound `d_TV ≤ 1 ≤ 2 · (1/2)^d`
    refine (tv_le_one (isDist_marg hw hσ v) (isDist_marg hw hτ v)).trans ?_
    interval_cases d <;> norm_num
  · -- `σ` and `τ` agree on `v` and its partner, which form a closed component
    set p : Fin m × Bool := (v.1, !v.2)
    have hvp : G.Adj v p := ⟨rfl, by cases h : v.2 <;> simp [p, h]⟩
    let B : Set (Fin m × Bool) := {v, p}
    have hagB : ∀ u ∈ B, σ u = τ u := by
      intro u hu
      rcases hu with rfl | rfl
      · exact hagree _ (by simp; exact_mod_cast (by omega : 0 < d))
      · exact hagree _ (by rw [SimpleGraph.edist_eq_one_iff_adj.2 hvp]; exact_mod_cast hd)
    have hF : ∀ i, (∃ u ∈ (F i).scope, u ∈ B) → (↑(F i).scope : Set _) ⊆ B := by
      rintro (x | ⟨a, b⟩) ⟨u, hu, huB⟩
      · simp only [F, hardcore, mem_singleton] at hu; subst hu
        simpa [F, hardcore] using huB
      · simp only [F, hardcore] at hu ⊢
        split_ifs at hu ⊢ with hab
        · -- the edge `{a, b}` meets `{v, p}`, so it is `{v, p}`
          have hv1 : a.1 = v.1 ∧ b.1 = v.1 := by
            simp only [mem_insert, mem_singleton] at hu
            rcases huB with rfl | rfl <;> rcases hu with rfl | rfl <;>
              exact ⟨by simp [hab.1, p], by simp [← hab.1, p]⟩
          intro x hx
          simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          have hx1 : x.1 = v.1 := by rcases hx with rfl | rfl <;> simp [hv1]
          show x ∈ ({v, p} : Set _)
          rcases x with ⟨i, c⟩
          simp only at hx1; subst hx1
          rcases v with ⟨j, e⟩
          cases c <;> cases e <;> simp [p]
        · simp at hu
    have h1 := marg_eq_local (F := F) (I := B) (B := B) (v := v) le_rfl (by simp [B]) hF
      (fun u _ hu => absurd ‹u ∈ B› hu) hσ
    have h2 := marg_eq_local (F := F) (I := B) (B := B) (v := v) le_rfl (by simp [B]) hF
      (fun u _ hu => absurd ‹u ∈ B› hu) hτ
    rw [h1, h2, restrictPin_congr hagB]
    unfold tv; simp

/-- **Corollary 5.2 is false as stated.** For every `m ≥ 1`, the hardcore model (`λ = 1`) on the
perfect matching with `m` edges is a locally admissible Gibbs distribution with constraints of
diameter `≤ 1` and has strong spatial mixing with exponential decay in TV distance (rate
`2 · (1/2)^d`), but has no strong spatial mixing in multiplicative error with any rate. -/
theorem corollary_5_2_false (m : ℕ) (hm : 1 ≤ m) :
    LocallyAdmissible (hardcore (matchingGraph m) 1 one_pos) ∧
    GibbsLocal (matchingGraph m) (hardcore (matchingGraph m) 1 one_pos) 1 ∧
    SSM (matchingGraph m) (gibbsW (hardcore (matchingGraph m) 1 one_pos))
      (fun d => ENNReal.ofReal (2 * (1 / 2) ^ d)) ∧
    ∀ R : ℕ → ℝ, ¬ MSSM (matchingGraph m) (gibbsW (hardcore (matchingGraph m) 1 one_pos)) R := by
  refine ⟨hardcore_locallyAdmissible, hardcore_gibbsLocal, matching_ssm m one_pos, fun R => ?_⟩
  exact hardcore_not_mssm (u := (⟨0, hm⟩, true)) (v := (⟨0, hm⟩, false))
    (show (matchingGraph m).Adj (⟨0, hm⟩, true) (⟨0, hm⟩, false) from ⟨rfl, by simp⟩) R

/-- Non-vacuity of Theorem 5.1 (⇐): on the hardcore model on a perfect matching, the algorithm
`ssmAlg` with `t = 2`, `ℓ = 1` is `4`-local and has TV error `≤ 1/2`. -/
theorem matching_inference (m : ℕ) :
    IsLocalAlg (matchingGraph m) (2 + 2 * 1) (ssmAlg (matchingGraph m) (hardcore (matchingGraph m) 1 one_pos) 2 1) ∧
    InfAccurate (gibbsW (hardcore (matchingGraph m) 1 one_pos)) (1 / 2)
      (ssmAlg (matchingGraph m) (hardcore (matchingGraph m) 1 one_pos) 2 1) :=
  theorem_5_1_converse hardcore_gibbsLocal hardcore_locallyAdmissible (matching_ssm m one_pos)
    (by norm_num) (ENNReal.ofReal_le_ofReal (by norm_num))

end Podc.LocalSamplingCounting
