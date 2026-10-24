import Papers.PODC2017.ZigzagCausality.RunByTiming

/-!
# Theorem 2 (zigzag necessity) — Section 3, Appendix B

* `precSet σ` — the σ-precedence set `V_σ` (Definition 12), p-closed by **Lemma 6**
  (`precSet_closed`).
* `dist σ' σ` — the weight `d(σ')` of the longest path from `σ'` to `σ` in `G_B(r)` (it exists:
  path weights are bounded by Lemma 1); `maxW σ` — the weight `D` of the longest path ending in `σ`.
* `slowTiming σ` — the slow timing `T(σ') = D − d(σ')` (Definition 13), a valid timing by
  **Lemma 7** (`slowTiming_valid`).
* `zigzag_necessity` — **Theorem 2**.
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

open Classical

variable {P S M E : Type*}

namespace Sys

variable {γ : Sys P S M E} {r : Sched P S E} [Finite P]

variable (γ r) in
/-- The σ-precedence set `V_σ` in `G_B(r)` (Definition 12): the nodes with a path to `σ`. -/
def precSet (σ : BNode P S M E) : Set (BNode P S M E) := {σ' | ∃ w, γ.BPath r σ' w σ}

/-- **Lemma 6.** `V_σ` is p-closed. -/
theorem precSet_closed (σ : BNode P S M E) : γ.PClosed r (γ.precSet r σ) :=
  fun _ _ _ e ⟨_, p⟩ => ⟨_, BPath.cons e p⟩

theorem precSet_appears {σ σ' : BNode P S M E} (h : σ' ∈ γ.precSet r σ) : γ.appears r σ' := by
  obtain ⟨w, p⟩ := h
  exact p.appears.1

/-- Path weights into `σ` are bounded (Lemma 1), so longest paths exist. -/
theorem exists_longest (hr : γ.Valid r) {σ σ' : BNode P S M E} (h : σ' ∈ γ.precSet r σ) :
    ∃ d, γ.BPath r σ' d σ ∧ ∀ w, γ.BPath r σ' w σ → w ≤ d :=
  Int.exists_greatest_of_bdd ⟨γ.timer r σ - γ.timer r σ', fun w p => by
    have := p.timer_le hr; omega⟩ h

theorem exists_longest_to (hr : γ.Valid r) {σ : BNode P S M E} (h : γ.appears r σ) :
    ∃ D, (∃ σ', γ.BPath r σ' D σ) ∧ ∀ w, (∃ σ', γ.BPath r σ' w σ) → w ≤ D :=
  Int.exists_greatest_of_bdd ⟨γ.timer r σ, fun w ⟨σ', p⟩ => by
    have := p.timer_le hr; omega⟩ ⟨0, σ, BPath.nil h⟩

variable (γ r) in
/-- `d(σ')`: the weight of the longest path from `σ'` to `σ` in `G_B(r)` (junk `0` if there is
no path or no longest one). -/
noncomputable def dist (σ' σ : BNode P S M E) : ℤ :=
  if h : ∃ d, γ.BPath r σ' d σ ∧ ∀ w, γ.BPath r σ' w σ → w ≤ d then h.choose else 0

variable (γ r) in
/-- `D`: the weight of the longest path in `G_B(r)` that ends in `σ` (junk `0` if none). -/
noncomputable def maxW (σ : BNode P S M E) : ℤ :=
  if h : ∃ D, (∃ σ', γ.BPath r σ' D σ) ∧ ∀ w, (∃ σ', γ.BPath r σ' w σ) → w ≤ D then h.choose
  else 0

variable (γ r) in
/-- The slow timing function `T(σ') = D − d(σ')` for `V_σ` (Definition 13). -/
noncomputable def slowTiming (σ : BNode P S M E) (σ' : BNode P S M E) : ℕ :=
  (γ.maxW r σ - γ.dist r σ' σ).toNat

theorem dist_spec (hr : γ.Valid r) {σ σ' : BNode P S M E} (h : σ' ∈ γ.precSet r σ) :
    γ.BPath r σ' (γ.dist r σ' σ) σ ∧ ∀ w, γ.BPath r σ' w σ → w ≤ γ.dist r σ' σ := by
  have he := exists_longest hr h
  simp only [dist, he, ↓reduceDIte]
  exact he.choose_spec

theorem maxW_spec (hr : γ.Valid r) {σ : BNode P S M E} (h : γ.appears r σ) :
    (∃ σ', γ.BPath r σ' (γ.maxW r σ) σ) ∧
      ∀ w, (∃ σ', γ.BPath r σ' w σ) → w ≤ γ.maxW r σ := by
  have he := exists_longest_to hr h
  simp only [maxW, he, ↓reduceDIte]
  exact he.choose_spec

theorem slowTiming_eq (hr : γ.Valid r) {σ σ' : BNode P S M E} (h : σ' ∈ γ.precSet r σ) :
    (γ.slowTiming r σ σ' : ℤ) = γ.maxW r σ - γ.dist r σ' σ := by
  have hσ : γ.appears r σ := (dist_spec hr h).1.appears.2
  have := (maxW_spec hr hσ).2 _ ⟨σ', (dist_spec hr h).1⟩
  simp only [slowTiming]
  omega

/-- **Lemma 7.** The slow timing function is a valid timing function for `V_σ` w.r.t.
`G_B(r)`. -/
theorem slowTiming_valid (hr : γ.Valid r) (σ : BNode P S M E) :
    γ.ValidTiming r (γ.precSet r σ) (γ.slowTiming r σ) := by
  intro a w b e ha hb
  rw [slowTiming_eq hr ha, slowTiming_eq hr hb]
  have := (dist_spec hr ha).2 _ (BPath.cons e (dist_spec hr hb).1)
  omega

variable (γ r) in
/-- The slow timing as a `Timing` (p-closed set `V_σ` with a valid timing). -/
noncomputable def slow (hr : γ.Valid r) (σ : BNode P S M E) : γ.Timing r :=
  ⟨γ.precSet r σ, γ.slowTiming r σ, fun _ h => precSet_appears h, precSet_closed σ,
    slowTiming_valid hr σ⟩

/-- **Theorem 2 (Zigzag Necessity).** If `R = R(P, γ)` supports `θ₁ --x--> θ₂`, and `θ₁`, `θ₂`
are nodes of a run `r ∈ R` with `timer_r(θ₁) > 0` and `timer_r(θ₂) > 0`, then there is a zigzag
pattern `Z` from `θ₁` to `θ₂` in `r` with `wt(Z) ≥ x`. -/
theorem zigzag_necessity (hr : γ.Valid r) {θ₁ θ₂ : GNode P S M E} {x : ℤ}
    (hs : γ.Supports θ₁ x θ₂) (h1 : γ.appearsG r θ₁) (h2 : γ.appearsG r θ₂)
    (t1 : 0 < γ.timerG r θ₁) (t2 : 0 < γ.timerG r θ₂) :
    ∃ Z, γ.IsZigzag r Z θ₁ θ₂ ∧ x ≤ γ.wtZ r Z := by
  obtain ⟨σ₁, hb1⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨σ₂, hb2⟩ := Option.isSome_iff_exists.1 h2
  rw [γ.timerG_of_basic r hb1] at t1
  rw [γ.timerG_of_basic r hb2] at t2
  have hσ₂ : γ.appears r σ₂ := (gbasic_appears γ r hb2).2
  -- the run `r' = r[T]` for the slow timing of `θ₂`
  set τ := slow γ r hr σ₂ with hτ
  have hσ₂V : σ₂ ∈ τ.V := ⟨0, BPath.nil hσ₂⟩
  have hb2' : γ.basic τ.run θ₂ = some σ₂ :=
    (Timing.basic_run hr hb2).1 ((Timing.appears_run_iff hr σ₂).2 (Or.inl hσ₂V))
  obtain ⟨ρ₁, ρ₂, hρ₁, hρ₂, hle⟩ :=
    hs τ.run (Timing.valid_run hr) (Or.inr (by simp [appearsG, hb2']))
  rw [hb2'] at hρ₂
  cases hρ₂
  have e : ρ₁ = σ₁ := Option.some_injective _ ((Timing.gbasic_of_run hr hρ₁).symm.trans hb1)
  subst e
  -- `σ₁` appears in `r'` and is not initial, so it has a path to `σ₂`
  have hσ₁V : ρ₁ ∈ τ.V := by
    rcases (Timing.appears_run_iff hr ρ₁).1 (gbasic_appears γ τ.run hρ₁).2 with h | h
    · exact h
    · omega
  rw [Timing.timer_run hr ⟨hσ₁V, t1⟩, Timing.timer_run hr ⟨hσ₂V, t2⟩] at hle
  have e1 : (τ.T ρ₁ : ℤ) = γ.maxW r σ₂ - γ.dist r ρ₁ σ₂ := slowTiming_eq hr hσ₁V
  have e2 : (τ.T σ₂ : ℤ) = γ.maxW r σ₂ - γ.dist r σ₂ σ₂ := slowTiming_eq hr hσ₂V
  have d2 : 0 ≤ γ.dist r σ₂ σ₂ := (dist_spec hr hσ₂V).2 0 (BPath.nil hσ₂)
  obtain ⟨Z, hZ, hw⟩ := zigzag_of_bpath (dist_spec hr hσ₁V).1 hb1 hb2
  exact ⟨Z, hZ, by omega⟩

end Sys

end Podc.ZigzagCausality
