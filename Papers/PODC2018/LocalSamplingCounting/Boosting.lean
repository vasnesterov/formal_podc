import Papers.PODC2018.LocalSamplingCounting.Basic

/-!
# The boosting lemma (Lemma 4.1): the probabilistic core

Algorithm `A^×_ε` of Lemma 4.1 pins the vertices `v₁, …, v_m` of the shell
`Γ = B_{t+ℓ}(v) \ (B_t(v) ∪ Λ)` one by one, each to a value `cᵢ` maximizing the answer
`μ̂^{τ_{i-1}}_{vᵢ}` of a TV-approximate inference algorithm `Â` (error `ε / (5qn)`), and returns the
exact marginal `μ^{τ_m}_v`. Since `dist(v, vᵢ) > t`, the `t`-local algorithm `Â` cannot see the
value of `v` when answering at `vᵢ`; we keep exactly this consequence as the hypothesis `hblind`.

* `pinSeq`: the sequence `τ₀ = τ, τ_i = τ_{i-1}[vᵢ ↦ cᵢ]`.
* `lemma_4_1_core`: `τ_m` is feasible and `e^{-ε} μ^τ_v ≤ μ^{τ_m}_v ≤ e^{ε} μ^τ_v` (eq. (3)),
  for any `m ≤ n` shell vertices (the paper: `m = |Γ| ≤ n`).

The paper's proof of the Claim contains a wrong inequality
(`μ_{Λᵢ∪{v}}(τᵢᶜ) = μ_{Λ_{i-1}∪{v}}(τ_{i-1}ᶜ) · μ^{τ_{i-1}ᶜ}_{vᵢ}(cᵢ) ≥ μ^{τ_{i-1}ᶜ}_{vᵢ}(cᵢ)`: the
first factor is a probability, so `≤` holds). Only positivity is needed, which we use instead.
-/

set_option linter.unusedSectionVars false

namespace Podc.LocalSamplingCounting

open Finset

open scoped Classical

variable {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Nonempty S]

/-- A value maximizing `p` (ties broken arbitrarily but deterministically). -/
noncomputable def argmax (p : S → ℝ) : S :=
  Classical.choose (Finset.exists_max_image univ p univ_nonempty)

lemma le_argmax (p : S → ℝ) (c : S) : p c ≤ p (argmax p) :=
  (Classical.choose_spec (Finset.exists_max_image univ p univ_nonempty)).2 c (mem_univ c)

/-- The maximal entry of a probability vector is at least `1/q`. -/
lemma inv_card_le_argmax {p : S → ℝ} (hp : ∑ c, p c = 1) :
    1 / (Fintype.card S : ℝ) ≤ p (argmax p) := by
  have hq : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have : ∑ c, p c ≤ ∑ _c : S, p (argmax p) := sum_le_sum fun c _ => le_argmax p c
  rw [hp, sum_const, card_univ, nsmul_eq_mul] at this
  rw [div_le_iff₀ hq]; linarith

/-- The pinning sequence of Algorithm `A^×_ε`: pin each listed vertex to the value maximizing
the oracle's answer on the current pinning. -/
noncomputable def pinSeq (A : Pin V S → V → S → ℝ) : List V → Pin V S → Pin V S
  | [], ρ => ρ
  | u :: l, ρ => pinSeq A l (Function.update ρ u (some (argmax (A ρ u))))

/-- The numerical heart of the proof: `|a - b| ≤ 2η`, `b ≥ 1/q - η` with `η = ε/(5qn)` give
`e^{-ε/n} b ≤ a ≤ e^{ε/n} b`. -/
lemma ratio_bound {a b ε q n : ℝ} (hq : 1 ≤ q) (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hab : |a - b| ≤ 2 * (ε / (5 * q * n))) (hb : 1 / q - ε / (5 * q * n) ≤ b) :
    Real.exp (-(ε / n)) * b ≤ a ∧ a ≤ Real.exp (ε / n) * b := by
  have hq0 : 0 < q := by linarith
  have hn0 : 0 < n := by linarith
  set y := ε / n with hy
  have hy0 : 0 < y := div_pos hε0 hn0
  have hy1 : y ≤ 1 := by rw [hy, div_le_one hn0]; linarith
  set η := ε / (5 * q * n) with hη
  -- `y * b ≥ y * (5 - y) / (5 q)` and `η = y / (5 q)`
  have hηy : η = y / (5 * q) := by rw [hη, hy]; field_simp
  have hb' : (5 - y) / (5 * q) ≤ b := by
    have : 1 / q - η = (5 - y) / (5 * q) := by rw [hηy]; field_simp
    linarith
  have hb0 : 0 < b := lt_of_lt_of_le (div_pos (by linarith) (by linarith)) hb'
  have key : 2 * η * (1 + y) ≤ y * b := by
    rw [hηy]
    calc 2 * (y / (5 * q)) * (1 + y) = y * (2 * (1 + y) / (5 * q)) := by ring
      _ ≤ y * ((5 - y) / (5 * q)) := by gcongr; linarith
      _ ≤ y * b := by gcongr
  obtain ⟨h1, h2⟩ := abs_le.1 hab
  constructor
  · -- `e^{-y} ≤ 1/(1+y)`
    have he : Real.exp (-y) * (1 + y) ≤ 1 := by
      have := Real.add_one_le_exp y
      calc Real.exp (-y) * (1 + y) ≤ Real.exp (-y) * Real.exp y := by
            gcongr; linarith
        _ = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-y)
    nlinarith
  · have := Real.add_one_le_exp y
    nlinarith

variable {w : (V → S) → ℝ}

lemma update_comm {ρ : Pin V S} {u v : V} (h : u ≠ v) (a b : Option S) :
    Function.update (Function.update ρ u a) v b = Function.update (Function.update ρ v b) u a :=
  Function.update_comm h a b ρ

/-- Inductive statement behind the Claim and eq. (3). -/
lemma pinSeq_spec (hw : ∀ σ, 0 ≤ w σ) {A : Pin V S → V → S → ℝ} {v : V} {ε : ℝ} {n : ℕ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hn : 1 ≤ n)
    (hacc : ∀ ρ u, Feasible w ρ → ∑ c, A ρ u c = 1 ∧
      tv (A ρ u) (marg w ρ u) ≤ ε / (5 * Fintype.card S * n))
    {P : V → Prop} (hblind : ∀ (ρ : Pin V S) (u : V) (c : S), P u →
      A (Function.update ρ v (some c)) u = A ρ u) :
    ∀ (l : List V) (ρ : Pin V S), ρ v = none → l.Nodup → (∀ u ∈ l, u ≠ v ∧ ρ u = none) →
      (∀ u ∈ l, P u) → ∀ c,
      Feasible w (Function.update ρ v (some c)) →
      Feasible w (Function.update (pinSeq A l ρ) v (some c)) ∧
      Real.exp (-(l.length * (ε / n))) * marg w ρ v c ≤ marg w (pinSeq A l ρ) v c ∧
      marg w (pinSeq A l ρ) v c ≤ Real.exp (l.length * (ε / n)) * marg w ρ v c
  | [], ρ, _, _, _, _, c, hf => by simp [pinSeq, hf]
  | u :: l, ρ, hv, hnd, hl, hPl, c, hfc => by
    have huv : u ≠ v := (hl u (by simp)).1
    have hu : ρ u = none := (hl u (by simp)).2
    have hq : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    -- notation
    set cu := argmax (A ρ u)
    set ρ' := Function.update ρ u (some cu)
    set ρc := Function.update ρ v (some c)
    have hf : Feasible w ρ := lt_of_lt_of_le hfc (Z_mono hw fun σ h =>
      ((cons_update_of_none hv).1 h).1)
    have hρc : ρc u = ρ u := Function.update_of_ne huv _ _
    have hcu : ρc u = none := by rw [hρc, hu]
    -- (5): the chosen value has large true marginal
    obtain ⟨hA1, htv⟩ := hacc ρ u hf
    obtain ⟨hA1c, htvc⟩ := hacc ρc u hfc
    rw [show ρc = Function.update ρ v (some c) from rfl, hblind ρ u c (hPl u (by simp))] at htvc hA1c
    have hm1 := sum_marg hf u
    have hm1c := sum_marg hfc u
    have h5 : 1 / (Fintype.card S : ℝ) - ε / (5 * Fintype.card S * n) ≤ marg w ρ u cu := by
      have h1 := inv_card_le_argmax hA1
      have h2 := (abs_le.1 (abs_sub_le_tv hA1 hm1 cu)).2
      linarith
    -- (4): the two marginals at `u` are close
    have h4 : |marg w ρc u cu - marg w ρ u cu| ≤ 2 * (ε / (5 * Fintype.card S * n)) := by
      have := abs_sub_le_tv hm1c hm1 cu
      have ht := tv_triangle (marg w ρc u) (A ρ u) (marg w ρ u)
      rw [tv_comm] at htvc
      linarith
    obtain ⟨hr1, hr2⟩ := ratio_bound hq hn' hε0 hε1 h4 h5
    have hpos_b : 0 < marg w ρ u cu := lt_of_lt_of_le (by
      have : ε / (5 * Fintype.card S * n) < 1 / (Fintype.card S : ℝ) := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith) h5
    have hpos_a : 0 < marg w ρc u cu :=
      lt_of_lt_of_le (mul_pos (Real.exp_pos _) hpos_b) hr1
    -- feasibility of the new pinnings
    have hf'c : Feasible w (Function.update ρ' v (some c)) := by
      rw [show Function.update ρ' v (some c) = Function.update ρc u (some cu) from
        update_comm huv _ _]
      exact (feasible_update_iff hw hfc hcu cu).2 hpos_a
    have hf' : Feasible w ρ' := (feasible_update_iff hw hf hu cu).2 hpos_b
    have hv' : ρ' v = none := by simp only [ρ', Function.update_of_ne huv.symm, hv]
    -- (2): two orders of the chain rule
    have hchain : marg w ρ' v c * marg w ρ u cu = marg w ρc u cu * marg w ρ v c := by
      rw [marg_eq_div hv', marg_eq_div hu, marg_eq_div hcu, marg_eq_div hv,
        show Function.update ρ' v (some c) = Function.update ρc u (some cu) from
          update_comm huv _ _]
      have h1 : Z w ρ' ≠ 0 := hf'.ne'
      have h2 : Z w ρc ≠ 0 := hfc.ne'
      have h3 : Z w ρ ≠ 0 := hf.ne'
      field_simp
      simp only [ρ', ρc]
    obtain ⟨ih1, ih2, ih3⟩ :=
      pinSeq_spec hw hε0 hε1 hn hacc hblind l ρ' hv' (List.nodup_cons.1 hnd).2
        (fun x hx => ⟨(hl x (by simp [hx])).1, by
          have hxu : x ≠ u := fun h => (List.nodup_cons.1 hnd).1 (h ▸ hx)
          simp only [ρ', Function.update_of_ne hxu]; exact (hl x (by simp [hx])).2⟩)
        (fun x hx => hPl x (by simp [hx])) c hf'c
    refine ⟨ih1, ?_, ?_⟩
    · -- lower bound
      have hm0 := marg_nonneg hw ρ v c
      have : marg w ρ' v c = marg w ρc u cu / marg w ρ u cu * marg w ρ v c := by
        field_simp; linarith [hchain]
      simp only [pinSeq, List.length_cons, Nat.cast_add, Nat.cast_one]
      refine le_trans ?_ ih2
      rw [this, show -(((l.length : ℝ) + 1) * (ε / n)) = -(l.length * (ε / n)) + -(ε / n) by ring,
        Real.exp_add]
      have hr : Real.exp (-(ε / n)) ≤ marg w ρc u cu / marg w ρ u cu := by
        rw [le_div_iff₀ hpos_b]; exact hr1
      have := Real.exp_pos (-(l.length * (ε / n)))
      calc Real.exp (-(l.length * (ε / n))) * Real.exp (-(ε / n)) * marg w ρ v c
          = Real.exp (-(l.length * (ε / n))) * (Real.exp (-(ε / n)) * marg w ρ v c) := by ring
        _ ≤ Real.exp (-(l.length * (ε / n))) *
            (marg w ρc u cu / marg w ρ u cu * marg w ρ v c) := by gcongr
    · have hm0 := marg_nonneg hw ρ v c
      have : marg w ρ' v c = marg w ρc u cu / marg w ρ u cu * marg w ρ v c := by
        field_simp; linarith [hchain]
      simp only [pinSeq, List.length_cons, Nat.cast_add, Nat.cast_one]
      refine ih3.trans ?_
      rw [this, show ((l.length : ℝ) + 1) * (ε / n) = l.length * (ε / n) + ε / n by ring,
        Real.exp_add]
      have hr : marg w ρc u cu / marg w ρ u cu ≤ Real.exp (ε / n) := by
        rw [div_le_iff₀ hpos_b]; exact hr2
      have := Real.exp_pos (l.length * (ε / n))
      calc Real.exp (l.length * (ε / n)) * (marg w ρc u cu / marg w ρ u cu * marg w ρ v c)
          ≤ Real.exp (l.length * (ε / n)) * (Real.exp (ε / n) * marg w ρ v c) := by gcongr
        _ = _ := by ring


lemma pinSeq_apply_of_notMem (A : Pin V S → V → S → ℝ) {u : V} :
    ∀ (l : List V) (ρ : Pin V S), u ∉ l → pinSeq A l ρ u = ρ u
  | [], _, _ => rfl
  | x :: l, ρ, h => by
    rw [pinSeq, pinSeq_apply_of_notMem A l _ (fun h' => h (by simp [h'])),
      Function.update_of_ne (fun h' => h (by simp [h']))]

lemma cons_of_cons_pinSeq (A : Pin V S → V → S → ℝ) {σ : V → S} :
    ∀ (l : List V) (ρ : Pin V S), l.Nodup → (∀ u ∈ l, ρ u = none) →
      Cons σ (pinSeq A l ρ) → Cons σ ρ
  | [], _, _, _, h => h
  | x :: l, ρ, hnd, hfree, h => by
    have h1 := cons_of_cons_pinSeq A l _ (List.nodup_cons.1 hnd).2 (fun u hu => by
      have hux : u ≠ x := fun h' => (List.nodup_cons.1 hnd).1 (h' ▸ hu)
      rw [Function.update_of_ne hux]; exact hfree u (by simp [hu])) h
    exact ((cons_update_of_none (hfree x (by simp))).1 h1).1

/-- **Lemma 4.1 (boosting lemma), probabilistic core: eq. (3).** Let `τ` be feasible, `v` free,
and `Γ = [v₁, …, v_m]` distinct free vertices other than `v`, with `m ≤ n`. Let `Â` answer every
feasible instance at every vertex with a probability vector within TV distance `ε / (5qn)` of the
true marginal (`q = |Σ|`, `0 < ε < 1`), and let `Â`'s answer at any `u ≠ v` not depend on the
value pinned at `v` (locality: `dist(v, vᵢ) > t`, hypothesis `hblind`). Pin `vᵢ` to the maximizer of `Â`'s answer
(`τ_m = pinSeq Â Γ τ`). Then `τ_m` is feasible and `μ^{τ_m}_v` has multiplicative error at most
`ε` w.r.t. `μ^τ_v`. -/
theorem lemma_4_1_core (hw : ∀ σ, 0 ≤ w σ) {A : Pin V S → V → S → ℝ} {v : V} {ε : ℝ} {n : ℕ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hn : 1 ≤ n)
    (hacc : ∀ ρ u, Feasible w ρ → ∑ c, A ρ u c = 1 ∧
      tv (A ρ u) (marg w ρ u) ≤ ε / (5 * Fintype.card S * n))
    {τ : Pin V S} (hτ : Feasible w τ) (hv : τ v = none) (Γ : List V) (hnd : Γ.Nodup)
    (hΓ : ∀ u ∈ Γ, u ≠ v ∧ τ u = none) (hm : Γ.length ≤ n)
    (hblind : ∀ (ρ : Pin V S) (u : V) (c : S), u ∈ Γ →
      A (Function.update ρ v (some c)) u = A ρ u) :
    Feasible w (pinSeq A Γ τ) ∧ MultClose (marg w (pinSeq A Γ τ) v) (marg w τ v) ε := by
  have key := pinSeq_spec hw hε0 hε1 hn hacc hblind Γ τ hv hnd hΓ (fun u hu => hu)
  have hvΓ : v ∉ Γ := fun h => (hΓ v h).1 rfl
  have hmv : pinSeq A Γ τ v = none := by rw [pinSeq_apply_of_notMem A Γ τ hvΓ, hv]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : (Γ.length : ℝ) * (ε / n) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hn', mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hm) hε0.le
  have hcons : ∀ σ, Cons σ (pinSeq A Γ τ) → Cons σ τ :=
    fun σ => cons_of_cons_pinSeq A Γ τ hnd (fun u hu => (hΓ u hu).2)
  constructor
  · obtain ⟨c, hc⟩ : ∃ c, 0 < marg w τ v c := by
      by_contra h; push_neg at h
      have := sum_marg hτ v
      have : ∑ c, marg w τ v c ≤ 0 := sum_nonpos fun c _ => h c
      linarith
    have h1 := (key c ((feasible_update_iff hw hτ hv c).2 hc)).1
    exact lt_of_lt_of_le h1 (Z_mono hw fun σ h => ((cons_update_of_none hmv).1 h).1)
  · intro c
    rcases (marg_nonneg hw τ v c).lt_or_eq with hc | hc
    · obtain ⟨_, h2, h3⟩ := key c ((feasible_update_iff hw hτ hv c).2 hc)
      constructor
      · exact le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith))
          hc.le) h2
      · exact h3.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hexp) hc.le)
    · have hinf : ¬ Feasible w (Function.update τ v (some c)) := fun h =>
        (ne_of_gt ((feasible_update_iff hw hτ hv c).1 h)) hc.symm
      have hz : marg w (pinSeq A Γ τ) v c = 0 := by
        rw [marg_eq_div hmv]
        have : Z w (Function.update (pinSeq A Γ τ) v (some c)) ≤
            Z w (Function.update τ v (some c)) := Z_mono hw fun σ h => by
          obtain ⟨h1, h2⟩ := (cons_update_of_none hmv).1 h
          exact (cons_update_of_none hv).2 ⟨hcons σ h1, h2⟩
        rw [(not_feasible_iff hw).1 hinf] at this
        rw [le_antisymm this (Z_nonneg hw _), zero_div]
      rw [hz, ← hc]; simp

end Podc.LocalSamplingCounting
