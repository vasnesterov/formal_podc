import Papers.PODC2018.LocalSamplingCounting.Gibbs

/-!
# Approximate inference and strong spatial mixing (§5)

The LOCAL model enters only through locality: an inference algorithm `A : Pin V S → V → S → ℝ`
for a fixed instance `(G, x)` is `r`-local (`IsLocalAlg G r A`) if its answer at `v` only depends
on the pinning `τ` within distance `r` of `v` (all other data of the instance is fixed).

* `SSM G w R` (Definition 5.1): for feasible `σ, τ` on the same set `Λ` that agree within distance
  `< d` of `v`, `d_TV(μ^σ_v, μ^τ_v) ≤ R d` (`R d ∈ [0, ∞]`; since `R` is non-increasing in the
  paper, "agree within distance `< d`" is the paper's `dist(v, D) ≥ d`).
* `MSSM G w R`: the same with multiplicative error (`err ≤ R d`, `R d ∈ ℝ`).
* `theorem_5_1_forward`: approximate inference with locality `t(δ)` ⇒ SSM with rate
  `2 inf{δ | t(δ) ≤ d - 1}` (the infimum over the empty set is `∞`).
* `theorem_5_1_converse`: for locally admissible Gibbs distributions with constraints of diameter
  `≤ ℓ`, SSM with `R t ≤ δ` ⇒ the explicit algorithm `ssmAlg` is `(t + 2ℓ)`-local and has TV error
  `≤ δ` on every feasible instance.
* `tv_le_of_multClose`, `ssm_of_mssm`: multiplicative SSM implies TV SSM (the easy direction of
  Corollary 5.2).
-/

set_option linter.unusedSectionVars false

namespace Podc.LocalSamplingCounting

open Finset

open scoped Classical

variable {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]

/-- An inference algorithm (for a fixed instance) is `r`-local: its output at `v` depends only on
the pinning within distance `r` of `v`. -/
def IsLocalAlg (G : SimpleGraph V) (r : ℕ) (A : Pin V S → V → S → ℝ) : Prop :=
  ∀ (v : V) (τ τ' : Pin V S), (∀ u, G.edist v u ≤ r → τ u = τ' u) → A τ v = A τ' v

/-- `A` solves approximate inference with total variation error `δ` (on feasible instances). -/
def InfAccurate (w : (V → S) → ℝ) (δ : ℝ) (A : Pin V S → V → S → ℝ) : Prop :=
  ∀ (τ : Pin V S) (v : V), Feasible w τ → tv (A τ v) (marg w τ v) ≤ δ

/-- **Definition 5.1 (strong spatial mixing, TV).** -/
def SSM (G : SimpleGraph V) (w : (V → S) → ℝ) (R : ℕ → ENNReal) : Prop :=
  ∀ (v : V) (σ τ : Pin V S), (∀ u, σ u = none ↔ τ u = none) → Feasible w σ → Feasible w τ →
    ∀ d : ℕ, (∀ u, G.edist v u < d → σ u = τ u) → ENNReal.ofReal (tv (marg w σ v) (marg w τ v)) ≤ R d

/-- Strong spatial mixing with decay in multiplicative error (Definition 5.1 with `err` in place of
`d_TV`). -/
def MSSM (G : SimpleGraph V) (w : (V → S) → ℝ) (R : ℕ → ℝ) : Prop :=
  ∀ (v : V) (σ τ : Pin V S), (∀ u, σ u = none ↔ τ u = none) → Feasible w σ → Feasible w τ →
    ∀ d : ℕ, (∀ u, G.edist v u < d → σ u = τ u) → MultClose (marg w σ v) (marg w τ v) (R d)

variable {w : (V → S) → ℝ}

/-- **Theorem 5.1 (⇒), pointwise form.** If for every `δ > 0` an `r(δ)`-local algorithm solves
approximate inference with error `δ`, then two feasible pinnings that agree within distance
`r(δ)` of `v` induce marginals at `v` within TV distance `2δ`. -/
theorem theorem_5_1_forward_pointwise {G : SimpleGraph V} {r : ℝ → ℕ}
    {A : ℝ → Pin V S → V → S → ℝ} (hloc : ∀ δ > 0, IsLocalAlg G (r δ) (A δ))
    (hacc : ∀ δ > 0, InfAccurate w δ (A δ)) {v : V} {σ τ : Pin V S}
    (hσ : Feasible w σ) (hτ : Feasible w τ) {δ : ℝ} (hδ : 0 < δ)
    (hagree : ∀ u, G.edist v u ≤ r δ → σ u = τ u) :
    tv (marg w σ v) (marg w τ v) ≤ 2 * δ := by
  have heq : A δ σ v = A δ τ v := hloc δ hδ v σ τ hagree
  have h1 := hacc δ hδ σ v hσ
  have h2 := hacc δ hδ τ v hτ
  rw [heq] at h1
  have := tv_triangle (marg w σ v) (A δ τ v) (marg w τ v)
  rw [tv_comm] at h1
  linarith

/-- **Theorem 5.1 (⇒).** Approximate inference by `t(δ)`-local algorithms implies strong spatial
mixing with rate `δ(d) = 2 inf{δ > 0 | t(δ) ≤ d - 1}`. -/
theorem theorem_5_1_forward {G : SimpleGraph V} {r : ℝ → ℕ}
    {A : ℝ → Pin V S → V → S → ℝ} (hloc : ∀ δ > 0, IsLocalAlg G (r δ) (A δ))
    (hacc : ∀ δ > 0, InfAccurate w δ (A δ)) :
    SSM G w (fun d => 2 * ⨅ (δ : ℝ) (_ : 0 < δ ∧ r δ < d), ENNReal.ofReal δ) := by
  intro v σ τ _ hσ hτ d hagree
  show _ ≤ 2 * _
  rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
  refine le_iInf₂ fun δ ⟨hδ, hr⟩ => ?_
  have := theorem_5_1_forward_pointwise hloc hacc hσ hτ hδ (fun u hu => hagree u
    (lt_of_le_of_lt hu (by exact_mod_cast hr)))
  rw [ENNReal.div_le_iff_le_mul (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
    show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul hδ.le]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### Multiplicative error controls TV distance -/

lemma tv_eq_sum_pos {α : Type*} [Fintype α] {p q : α → ℝ} (hp : ∑ x, p x = 1)
    (hq : ∑ x, q x = 1) : tv p q = ∑ x, max (p x - q x) 0 := by
  unfold tv
  have h0 : ∑ x, (p x - q x) = 0 := by rw [sum_sub_distrib, hp, hq, sub_self]
  have : ∀ x, |p x - q x| = 2 * max (p x - q x) 0 - (p x - q x) := fun x => by
    rcases le_total (p x - q x) 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right h]; ring
    · rw [abs_of_nonneg h, max_eq_left h]; ring
  simp_rw [this]
  rw [sum_sub_distrib, h0, ← mul_sum]; ring

/-- `d_TV(p, q) ≤ err(p, q)` for probability vectors. -/
lemma tv_le_of_multClose {α : Type*} [Fintype α] {p q : α → ℝ} (hp : IsDist p) (hq : IsDist q)
    {ε : ℝ} (h : MultClose p q ε) : tv p q ≤ ε := by
  rw [tv_eq_sum_pos hp.2 hq.2]
  have hε : 0 ≤ ε := by
    by_contra hneg; push_neg at hneg
    -- `p ≤ e^ε q < q` wherever `q > 0`, contradicting `∑ p = ∑ q`
    have hlt : ∑ x, p x < ∑ x, q x := by
      obtain ⟨x0, hx0⟩ : ∃ x, 0 < q x := by
        by_contra h'; push_neg at h'
        have : ∑ x, q x ≤ 0 := sum_nonpos fun x _ => h' x
        linarith [hq.2]
      refine Finset.sum_lt_sum (fun x _ => ?_) ⟨x0, mem_univ _, ?_⟩
      · exact (h x).2.trans (mul_le_of_le_one_left (hq.1 x) (Real.exp_le_one_iff.2 hneg.le))
      · exact lt_of_le_of_lt (h x0).2 (mul_lt_of_lt_one_left hx0 (Real.exp_lt_one_iff.2 hneg))
    linarith [hp.2, hq.2]
  calc ∑ x, max (p x - q x) 0 ≤ ∑ x, (1 - Real.exp (-ε)) * p x := sum_le_sum fun x _ => by
        refine max_le ?_ (mul_nonneg (by linarith [Real.exp_le_one_iff.2 (neg_nonpos.2 hε)])
          (hp.1 x))
        -- `q ≥ e^{-ε} p` from `p ≤ e^ε q`
        have h2 := (h x).2
        have : Real.exp (-ε) * p x ≤ q x := by
          calc Real.exp (-ε) * p x ≤ Real.exp (-ε) * (Real.exp ε * q x) := by
                gcongr
            _ = q x := by rw [← mul_assoc, ← Real.exp_add]; simp
        linarith
    _ = 1 - Real.exp (-ε) := by rw [← mul_sum, hp.2, mul_one]
    _ ≤ ε := by linarith [Real.one_sub_le_exp_neg ε]

/-- **Corollary 5.2 (⇐).** Strong spatial mixing in multiplicative error implies strong spatial
mixing in total variation distance with the same rate. -/
theorem ssm_of_mssm (hw : ∀ σ, 0 ≤ w σ) {G : SimpleGraph V} {R : ℕ → ℝ} (h : MSSM G w R) :
    SSM G w (fun d => ENNReal.ofReal (R d)) := by
  intro v σ τ hdom hσ hτ d hagree
  exact ENNReal.ofReal_le_ofReal (tv_le_of_multClose (isDist_marg hw hσ v) (isDist_marg hw hτ v)
    (h v σ τ hdom hσ hτ d hagree))

/-! ### The law of total probability over a partition -/

/-- If `K` maps each configuration consistent with `τ` to a refinement `K σ` of `τ`, and these
refinements partition the consistent configurations, then `μ^τ_v` is the `μ^τ`-mixture of the
`μ^{K σ}_v`. -/
lemma marg_eq_mix (hw : ∀ σ, 0 ≤ w σ) {τ : Pin V S} (hτ : Feasible w τ)
    (K : (V → S) → Pin V S)
    (hK : ∀ σ, Cons σ τ → ∀ σ', (Cons σ' (K σ) ↔ Cons σ' τ ∧ K σ' = K σ)) (v : V) (c : S) :
    marg w τ v c = ∑ σ, cond w τ σ * marg w (K σ) v c := by
  -- `Z (K σ) = ∑_{σ' ~ σ} w σ'`, `margNum (K σ) = ∑_{σ' ~ σ, σ' v = c} w σ'`
  have hZ : ∀ σ, Cons σ τ → Z w (K σ) =
      ∑ σ', if Cons σ' τ ∧ K σ' = K σ then w σ' else 0 := fun σ hσ => by
    unfold Z; exact sum_congr rfl fun σ' _ => by rw [if_congr (hK σ hσ σ') rfl rfl]
  have hN : ∀ σ, Cons σ τ → margNum w (K σ) v c =
      ∑ σ', if (Cons σ' τ ∧ K σ' = K σ) ∧ σ' v = c then w σ' else 0 := fun σ hσ => by
    unfold margNum; exact sum_congr rfl fun σ' _ => by
      rw [if_congr (and_congr_left' (hK σ hσ σ')) rfl rfl]
  have hZpos : 0 < Z w τ := hτ
  set T : (V → S) → (V → S) → ℝ := fun σ σ' =>
    if Cons σ τ ∧ Cons σ' τ ∧ K σ' = K σ ∧ σ' v = c then
      w σ * w σ' / Z w (K σ') / Z w τ else 0 with hT
  have step1 : ∀ σ, cond w τ σ * marg w (K σ) v c = ∑ σ', T σ σ' := by
    intro σ
    unfold cond marg
    by_cases hσ : Cons σ τ
    · rw [if_pos hσ, hN σ hσ, Finset.sum_div, Finset.mul_sum]
      refine sum_congr rfl fun σ' _ => ?_
      by_cases h : Cons σ' τ ∧ K σ' = K σ ∧ σ' v = c
      · simp only [hT]; rw [if_pos ⟨⟨h.1, h.2.1⟩, h.2.2⟩, if_pos ⟨hσ, h⟩, h.2.1]; ring
      · simp only [hT]
        rw [if_neg (fun h' => h ⟨h'.1.1, h'.1.2, h'.2⟩), if_neg (fun h' => h h'.2)]; ring
    · rw [if_neg hσ, zero_mul]
      exact (sum_eq_zero fun σ' _ => by simp only [hT]; rw [if_neg (fun h => hσ h.1)]).symm
  have step3 : ∀ σ', ∑ σ, T σ σ' = if Cons σ' τ ∧ σ' v = c then w σ' / Z w τ else 0 := by
    intro σ'
    by_cases h : Cons σ' τ ∧ σ' v = c
    · rw [if_pos h]
      have hsum : ∑ σ, T σ σ' = (∑ σ, if Cons σ τ ∧ K σ = K σ' then w σ else 0) *
          (w σ' / Z w (K σ') / Z w τ) := by
        rw [Finset.sum_mul]
        refine sum_congr rfl fun σ _ => ?_
        simp only [hT]
        by_cases h2 : Cons σ τ ∧ K σ = K σ'
        · rw [if_pos ⟨h2.1, h.1, h2.2.symm, h.2⟩, if_pos h2]; ring
        · rw [if_neg (fun h' => h2 ⟨h'.1, h'.2.2.1.symm⟩), if_neg h2, zero_mul]
      rw [hsum, ← hZ σ' h.1]
      by_cases hz : Z w (K σ') = 0
      · have hw0 : w σ' = 0 := by
          have := le_Z_of_cons hw ((hK σ' h.1 σ').2 ⟨h.1, rfl⟩)
          rw [hz] at this; exact le_antisymm this (hw σ')
        rw [hz, hw0]; simp
      · field_simp
    · rw [if_neg h]
      exact sum_eq_zero fun σ _ => by
        simp only [hT]; rw [if_neg (fun h' => h ⟨h'.2.1, h'.2.2.2⟩)]
  simp_rw [step1]
  rw [Finset.sum_comm]
  simp_rw [step3]
  unfold marg margNum
  rw [Finset.sum_div]
  exact sum_congr rfl fun σ' _ => by split_ifs <;> simp

/-! ### Theorem 5.1 (⇐): an inference algorithm from strong spatial mixing -/

section converse

variable {ι : Type*} [Fintype ι] [Nonempty S]

/-- **Definition 2.4.** Every constraint has diameter at most `ℓ` in `G`. -/
def GibbsLocal (G : SimpleGraph V) (F : ι → Factor V S) (ℓ : ℕ) : Prop :=
  ∀ i, ∀ u ∈ (F i).scope, ∀ u' ∈ (F i).scope, G.edist u u' ≤ ℓ

/-- The ball `B_r(v)`. -/
def ball (G : SimpleGraph V) (v : V) (r : ℕ) : Set V := {u | G.edist v u ≤ r}

/-- The shell `Γ = B_{t+ℓ}(v) \ (B_t(v) ∪ Λ)`. -/
def shell (G : SimpleGraph V) (τ : Pin V S) (v : V) (t ℓ : ℕ) : Set V :=
  {u | (t : ℕ∞) < G.edist v u ∧ G.edist v u ≤ ((t + ℓ : ℕ) : ℕ∞) ∧ τ u = none}

/-- `τ` extended by the values of `x` on `Γ`. -/
noncomputable def extPin (Γ : Set V) (τ : Pin V S) (x : V → S) : Pin V S :=
  fun u => if u ∈ Γ then some (x u) else τ u

/-- Some configuration extending `ρ`. -/
noncomputable def fill (ρ : Pin V S) : V → S := fun u => (ρ u).getD (Classical.arbitrary S)

/-- The local test (14): every constraint inside `B_R(v)` whose scope is pinned is satisfied. -/
def localCheck (G : SimpleGraph V) (F : ι → Factor V S) (v : V) (R : ℕ) (ρ : Pin V S) : Prop :=
  ∀ i, (↑(F i).scope : Set V) ⊆ dom ρ → (∀ u ∈ (F i).scope, G.edist v u ≤ R) →
    0 < (F i).f (fill ρ)

/-- The extension of `τ` on the shell chosen by node `v` (any one passing the local test). -/
noncomputable def ssmChoice (G : SimpleGraph V) (F : ι → Factor V S) (t ℓ : ℕ) (τ : Pin V S)
    (v : V) : V → S :=
  Classical.epsilon fun x => localCheck G F v (t + 2 * ℓ) (extPin (shell G τ v t ℓ) τ x)

/-- **The algorithm of Theorem 5.1 (⇐).** Node `v` extends `τ` on the shell by a locally
feasible configuration and returns the marginal at `v` computed from the factors inside
`B_{t+ℓ}(v)` and the pinning there. -/
noncomputable def ssmAlg (G : SimpleGraph V) (F : ι → Factor V S) (t ℓ : ℕ) :
    Pin V S → V → S → ℝ := fun τ v =>
  marg (gibbsWOn F (ball G v (t + ℓ)))
    (restrictPin (extPin (shell G τ v t ℓ) τ (ssmChoice G F t ℓ τ v)) (ball G v (t + ℓ))) v

lemma fill_eq_of_cons {ρ : Pin V S} {σ : V → S} (h : Cons σ ρ) {u : V} (hu : u ∈ dom ρ) :
    fill ρ u = σ u := by
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hu
  simp [fill, hc, h u c hc]

lemma factor_eq_fill (F : ι → Factor V S) {ρ : Pin V S} {σ : V → S} (h : Cons σ ρ) (i : ι)
    (hi : (↑(F i).scope : Set V) ⊆ dom ρ) : (F i).f σ = (F i).f (fill ρ) :=
  (F i).dep _ _ fun u hu => (fill_eq_of_cons h (hi hu)).symm

lemma factor_pos_of_gibbsW_pos (F : ι → Factor V S) {σ : V → S} (h : 0 < gibbsW F σ)
    (i : ι) : 0 < (F i).f σ := by
  rcases ((F i).nonneg σ).lt_or_eq with h' | h'
  · exact h'
  · exfalso
    have : gibbsW F σ = 0 := Finset.prod_eq_zero (mem_univ i) h'.symm
    linarith

lemma exists_pos_of_feasible {w : (V → S) → ℝ} {τ : Pin V S} (h : Feasible w τ) :
    ∃ σ, Cons σ τ ∧ 0 < w σ := by
  by_contra h'; push_neg at h'
  have : Z w τ ≤ 0 := sum_nonpos fun σ _ => by
    split_ifs with hc
    · exact h' σ hc
    · rfl
  exact absurd h (not_lt.2 this)

/-- The algorithm of Theorem 5.1 (⇐) is `(t + 2ℓ)`-local. -/
theorem ssmAlg_isLocal (G : SimpleGraph V) (F : ι → Factor V S) (t ℓ : ℕ) :
    IsLocalAlg G (t + 2 * ℓ) (ssmAlg G F t ℓ) := by
  intro v τ τ' h
  have hshell : shell G τ v t ℓ = shell G τ' v t ℓ := by
    ext u
    simp only [shell, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rw [← h u (h2.trans (by exact_mod_cast (by omega : t + ℓ ≤ t + 2 * ℓ)))]; exact h3
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rw [h u (h2.trans (by exact_mod_cast (by omega : t + ℓ ≤ t + 2 * ℓ)))]; exact h3
  have hext : ∀ x u, G.edist v u ≤ ((t + 2 * ℓ : ℕ) : ℕ∞) →
      extPin (shell G τ v t ℓ) τ x u = extPin (shell G τ' v t ℓ) τ' x u := by
    intro x u hu
    simp only [extPin, hshell]
    split_ifs
    · rfl
    · exact h u hu
  have hcheck : (fun x => localCheck G F v (t + 2 * ℓ) (extPin (shell G τ v t ℓ) τ x)) =
      (fun x => localCheck G F v (t + 2 * ℓ) (extPin (shell G τ' v t ℓ) τ' x)) := by
    funext x
    apply propext
    unfold localCheck
    refine forall_congr' fun i => ?_
    constructor
    · intro hi hdom hball
      have hdom' : (↑(F i).scope : Set V) ⊆ dom (extPin (shell G τ v t ℓ) τ x) := fun u hu => by
        have := hdom hu
        simp only [dom, Set.mem_setOf_eq] at this ⊢
        rwa [hext x u (by exact_mod_cast hball u hu)]
      have := hi hdom' hball
      rwa [(F i).dep (fill (extPin (shell G τ v t ℓ) τ x)) (fill (extPin (shell G τ' v t ℓ) τ' x))
        fun u hu => by simp only [fill, hext x u (by exact_mod_cast hball u hu)]] at this
    · intro hi hdom hball
      have hdom' : (↑(F i).scope : Set V) ⊆ dom (extPin (shell G τ' v t ℓ) τ' x) := fun u hu => by
        have := hdom hu
        simp only [dom, Set.mem_setOf_eq] at this ⊢
        rwa [← hext x u (by exact_mod_cast hball u hu)]
      have := hi hdom' hball
      rwa [← (F i).dep (fill (extPin (shell G τ v t ℓ) τ x)) (fill (extPin (shell G τ' v t ℓ) τ' x))
        fun u hu => by simp only [fill, hext x u (by exact_mod_cast hball u hu)]] at this
  have hchoice : ssmChoice G F t ℓ τ v = ssmChoice G F t ℓ τ' v := by
    unfold ssmChoice; rw [hcheck]
  unfold ssmAlg
  rw [hchoice]
  congr 1
  exact restrictPin_congr fun u hu => hext _ u (le_trans hu (by
    exact_mod_cast (by omega : t + ℓ ≤ t + 2 * ℓ)))

/-- **Theorem 5.1 (⇐).** For a locally admissible Gibbs distribution whose constraints have
diameter `≤ ℓ` and which exhibits strong spatial mixing with rate `R`, if `R t ≤ δ` then the
`(t + 2ℓ)`-local algorithm `ssmAlg` solves approximate inference with TV error `δ`. -/
theorem theorem_5_1_converse {G : SimpleGraph V} {F : ι → Factor V S} {ℓ : ℕ}
    (hℓ : GibbsLocal G F ℓ) (hadm : LocallyAdmissible F) {R : ℕ → ENNReal}
    (hssm : SSM G (gibbsW F) R) {t : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hR : R t ≤ ENNReal.ofReal δ) :
    IsLocalAlg G (t + 2 * ℓ) (ssmAlg G F t ℓ) ∧ InfAccurate (gibbsW F) δ (ssmAlg G F t ℓ) := by
  refine ⟨ssmAlg_isLocal G F t ℓ, fun τ v hτ => ?_⟩
  have hw : ∀ σ, 0 ≤ gibbsW F σ := gibbsW_nonneg F
  set Γ := shell G τ v t ℓ with hΓ
  obtain ⟨σ₀, hσ₀c, hσ₀w⟩ := exists_pos_of_feasible hτ
  have hΓfree : ∀ u ∈ Γ, τ u = none := fun u hu => hu.2.2
  have hcons_ext : ∀ x, Cons x τ → Cons x (extPin Γ τ x) := fun x hx u c hc => by
    unfold extPin at hc
    split_ifs at hc with hu
    · exact Option.some_inj.1 hc
    · exact hx u c hc
  -- (b) `σ₀` passes the local test, hence so does the chosen extension
  have hcheck0 : localCheck G F v (t + 2 * ℓ) (extPin Γ τ σ₀) := fun i hi _ => by
    rw [← factor_eq_fill F (hcons_ext σ₀ hσ₀c) i hi]
    exact factor_pos_of_gibbsW_pos F hσ₀w i
  set x := ssmChoice G F t ℓ τ v
  have hcheck : localCheck G F v (t + 2 * ℓ) (extPin Γ τ x) :=
    Classical.epsilon_spec (p := fun x => localCheck G F v (t + 2 * ℓ) (extPin Γ τ x))
      ⟨σ₀, hcheck0⟩
  set τ' := extPin Γ τ x
  -- (d) `τ'` is locally feasible
  have hloc' : LocFeasible F τ' := by
    intro i hi σ hσ
    rw [factor_eq_fill F hσ i hi]
    by_cases hball : ∀ u ∈ (F i).scope, G.edist v u ≤ ((t + 2 * ℓ : ℕ) : ℕ∞)
    · exact hcheck i hi hball
    · push_neg at hball
      obtain ⟨u', hu', hfar⟩ := hball
      -- every vertex of the scope is beyond the shell, so `τ'` agrees with `τ` there
      have hnotΓ : ∀ u ∈ (F i).scope, u ∉ Γ := by
        intro u hu hΓu
        have h1 := hΓu.2.1
        have h2 : G.edist v u' ≤ G.edist v u + G.edist u u' := SimpleGraph.edist_triangle
        have h3 := hℓ i u hu u' hu'
        have : G.edist v u' ≤ ((t + 2 * ℓ : ℕ) : ℕ∞) := by
          calc G.edist v u' ≤ G.edist v u + G.edist u u' := h2
            _ ≤ ((t + ℓ : ℕ) : ℕ∞) + (ℓ : ℕ∞) := add_le_add h1 h3
            _ = ((t + 2 * ℓ : ℕ) : ℕ∞) := by push_cast; ring
        exact absurd this (not_le.2 hfar)
      have key : ∀ u ∈ (F i).scope, fill τ' u = σ₀ u := fun u hu => by
        have hτ'u : τ' u = τ u := by simp only [τ', extPin, if_neg (hnotΓ u hu)]
        have hd : τ' u ≠ none := hi hu
        obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hd
        have hc' := hc
        rw [hτ'u] at hc'
        simp only [fill, hc, Option.getD_some]
        exact (hσ₀c u c hc').symm
      rw [(F i).dep (fill τ') σ₀ key]
      exact factor_pos_of_gibbsW_pos F hσ₀w i
  -- (e) `τ'` is feasible
  have hτ' : Feasible (gibbsW F) τ' := (hadm τ').2 hloc'
  -- (f) the algorithm returns the exact marginal `μ^{τ'}_v`
  have hout : ssmAlg G F t ℓ τ v = marg (gibbsW F) τ' v := by
    symm
    refine marg_eq_local (I := ball G v t) (B := ball G v (t + ℓ))
      (fun u (hu : G.edist v u ≤ t) => show G.edist v u ≤ ((t + ℓ : ℕ) : ℕ∞) from
        le_trans hu (by exact_mod_cast (by omega : t ≤ t + ℓ)))
      (by simp [ball])
      (fun i ⟨u, hu, (huI : G.edist v u ≤ t)⟩ u' hu' => show G.edist v u' ≤ ((t + ℓ : ℕ) : ℕ∞) by
        calc G.edist v u' ≤ G.edist v u + G.edist u u' := SimpleGraph.edist_triangle
          _ ≤ (t : ℕ∞) + (ℓ : ℕ∞) := add_le_add huI (hℓ i u hu u' (by simpa using hu'))
          _ = ((t + ℓ : ℕ) : ℕ∞) := by push_cast; ring)
      (fun u (huB : G.edist v u ≤ ((t + ℓ : ℕ) : ℕ∞)) (huI : ¬ G.edist v u ≤ t) => by
        simp only [τ', extPin]
        split_ifs with hΓu
        · simp
        · intro hnone
          exact hΓu ⟨not_le.1 huI, huB, hnone⟩) hτ'
  -- (g) `μ^τ_v` is a mixture of the `μ^{K σ}_v` over the extensions `K σ` of `τ` on the shell
  set K : (V → S) → Pin V S := fun σ => extPin Γ τ σ
  have hK : ∀ σ, Cons σ τ → ∀ σ', (Cons σ' (K σ) ↔ Cons σ' τ ∧ K σ' = K σ) := by
    intro σ hσ σ'
    constructor
    · intro h
      have h1 : Cons σ' τ := fun u c hc => by
        by_cases hu : u ∈ Γ
        · rw [hΓfree u hu] at hc; cases hc
        · exact h u c (by simp only [K, extPin, if_neg hu]; exact hc)
      refine ⟨h1, funext fun u => ?_⟩
      simp only [K, extPin]
      split_ifs with hu
      · rw [h u (σ u) (by simp only [K, extPin, if_pos hu])]
      · rfl
    · rintro ⟨h1, h2⟩
      rw [← h2]; exact hcons_ext σ' h1
  have hmix : marg (gibbsW F) τ v = fun c => ∑ σ, cond (gibbsW F) τ σ * marg (gibbsW F) (K σ) v c :=
    funext fun c => marg_eq_mix hw hτ K hK v c
  -- (h) each component is `δ`-close to `μ^{τ'}_v` by strong spatial mixing
  rw [hout, tv_comm, hmix]
  refine (tv_mix_le univ (cond (gibbsW F) τ) (fun σ => marg (gibbsW F) (K σ) v)
    (marg (gibbsW F) τ' v) (fun σ _ => cond_nonneg hw τ σ) (sum_cond hτ)).trans ?_
  calc ∑ σ, cond (gibbsW F) τ σ * tv (marg (gibbsW F) (K σ) v) (marg (gibbsW F) τ' v)
      ≤ ∑ σ, cond (gibbsW F) τ σ * δ := sum_le_sum fun σ _ => by
        rcases (cond_nonneg hw τ σ).lt_or_eq with hpos | hzero
        · refine mul_le_mul_of_nonneg_left ?_ hpos.le
          have hcσ : Cons σ τ := by
            by_contra hc; unfold cond at hpos; rw [if_neg hc] at hpos; exact lt_irrefl _ hpos
          have hwσ : 0 < gibbsW F σ := by
            unfold cond at hpos; rw [if_pos hcσ] at hpos
            exact (div_pos_iff_of_pos_right hτ).1 hpos
          have hfK : Feasible (gibbsW F) (K σ) :=
            lt_of_lt_of_le hwσ (le_Z_of_cons hw (hcons_ext σ hcσ))
          have hdom : ∀ u, K σ u = none ↔ τ' u = none := fun u => by
            simp only [K, τ', extPin]; split_ifs <;> simp
          have hagree : ∀ u, G.edist v u < t → K σ u = τ' u := fun u hu => by
            have hu' : u ∉ Γ := fun h => absurd h.1 (not_lt.2 (le_of_lt (by exact_mod_cast hu)))
            simp only [K, τ', extPin, if_neg hu']
          have := (hssm v (K σ) τ' hdom hfK hτ' t hagree).trans hR
          exact (ENNReal.ofReal_le_ofReal_iff hδ).1 this
        · rw [← hzero]; simp
    _ = δ := by rw [← sum_mul, sum_cond hτ, one_mul]

end converse

end Podc.LocalSamplingCounting
