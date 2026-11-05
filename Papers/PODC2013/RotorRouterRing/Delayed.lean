import Papers.PODC2013.RotorRouterRing.Model

/-!
# Delayed deployments: Lemmas 2.1, 2.2 and 2.3 (the slow-down lemma)

Klasing, Kosowski, Pająk, Sauerwald, PODC 2013, Section 2.1. All statements hold on any rotor
graph (any graph, any port orders, any initial pointers and agent placement).
-/

open Finset

namespace Podc.RotorRouterRing

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RotorGraph V}

set_option linter.unusedSectionVars false

namespace RotorGraph

/-- Monotonicity in the initial placement and in the delays: more agents initially (same
pointers) and fewer delays give at least as many cumulative exits. -/
lemma exits_mono {c₁ c₂ : Config V} (hpos : c₁.pos ≤ c₂.pos) (hptr : c₁.ptr = c₂.ptr)
    {D₁ D₂ : ℕ → V → ℕ} (hD : ∀ t v, D₂ t v ≤ D₁ t v) (t : ℕ) :
    G.exits c₁ D₁ t ≤ G.exits c₂ D₂ t := by
  induction t with
  | zero => intro v; simp [exits]
  | succ t ih =>
    have hvis : G.visits c₁ D₁ t ≤ G.visits c₂ D₂ t := by
      rw [visits_eq_visitsOf, visits_eq_visitsOf]
      intro u
      simp only [visitsOf, hptr]
      gcongr with w
      · exact hpos u
      · exact G.sent_mono w _ (ih w) u
    intro v
    rw [exits_succ_eq, exits_succ_eq]
    exact max_le_max (ih v) (tsub_le_tsub (hvis v) (hD (t + 1) v))

lemma visits_mono {c₁ c₂ : Config V} (hpos : c₁.pos ≤ c₂.pos) (hptr : c₁.ptr = c₂.ptr)
    {D₁ D₂ : ℕ → V → ℕ} (hD : ∀ t v, D₂ t v ≤ D₁ t v) (t : ℕ) :
    G.visits c₁ D₁ t ≤ G.visits c₂ D₂ t := by
  rw [visits_eq_visitsOf, visits_eq_visitsOf]
  intro u
  simp only [visitsOf, hptr]
  gcongr with w
  · exact hpos u
  · exact G.sent_mono w _ (exits_mono hpos hptr hD t w) u

/-- **Lemma 2.1.** If `D₁(v,t) ≥ D₂(v,t)` for all `v, t`, then `n_v^{D₁}(t) ≤ n_v^{D₂}(t)` for all
`v, t` (both deployments start from the same configuration). -/
theorem lemma_2_1 (c₀ : Config V) {D₁ D₂ : ℕ → V → ℕ} (hD : ∀ t v, D₂ t v ≤ D₁ t v) (t : ℕ)
    (v : V) : G.visits c₀ D₁ t v ≤ G.visits c₀ D₂ t v :=
  visits_mono le_rfl rfl hD t v

/-- The remark after Lemma 2.1 (due to Yanovski et al.): removing an agent cannot increase the
number of visits, `n_v^{R[k-1]}(t) ≤ n_v^{R[k]}(t)` (same pointers, one agent fewer). -/
theorem visits_remove_agent (c : Config V) (x : V) (t : ℕ) (v : V) :
    G.visits ⟨Function.update c.pos x (c.pos x - 1), c.ptr⟩ undelayed t v
      ≤ G.visits c undelayed t v := by
  refine visits_mono (G := G) (c₁ := ⟨Function.update c.pos x (c.pos x - 1), c.ptr⟩) (c₂ := c)
    (fun u => ?_) rfl (fun _ _ => le_rfl) t v
  by_cases h : u = x
  · subst h; simp
  · simp [h]

/-- Rounds `1, …, t` in which all agents are active (no node stops any agent). -/
def activeRounds (D : ℕ → V → ℕ) (t : ℕ) : ℕ :=
  ((range t).filter (fun s => ∀ v, D (s + 1) v = 0)).card

lemma activeRounds_succ (D : ℕ → V → ℕ) (t : ℕ) :
    activeRounds D (t + 1) = activeRounds D t + if ∀ v, D (t + 1) v = 0 then 1 else 0 := by
  simp only [activeRounds, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

lemma activeRounds_le (D : ℕ → V → ℕ) (t : ℕ) : activeRounds D t ≤ t := by
  simpa [activeRounds] using Finset.card_filter_le (range t) _

lemma exits_undelayed_succ (c₀ : Config V) (t : ℕ) (v : V) :
    G.exits c₀ undelayed (t + 1) v = G.visits c₀ undelayed t v := by
  rw [exits_succ_eq]
  have := exits_le_visits (G := G) c₀ undelayed t v
  simp only [undelayed]
  omega

lemma exits_undelayed_le (c₀ : Config V) (D : ℕ → V → ℕ) (t : ℕ) :
    G.exits c₀ undelayed (activeRounds D t) ≤ G.exits c₀ D t := by
  induction t with
  | zero => intro v; simp [activeRounds, exits]
  | succ t ih =>
    intro v
    rw [activeRounds_succ]
    split_ifs with h
    · rw [exits_undelayed_succ, exits_succ_eq, h v]
      have : G.visits c₀ undelayed (activeRounds D t) v ≤ G.visits c₀ D t v := by
        rw [visits_eq_visitsOf, visits_eq_visitsOf]; exact visitsOf_mono ih v
      exact le_max_of_le_right (by omega)
    · simp only [add_zero]
      exact (ih v).trans (exits_mono_time c₀ D (Nat.le_succ t) v)

/-- **Lemma 2.2.** Let `τ` be the number of rounds in `[1, T]` in which all agents are active in
the delayed deployment `D`. Then `n_v^{R[k]}(τ) ≤ n_v^D(T) ≤ n_v^{R[k]}(T)` for all `v`. -/
theorem lemma_2_2 (c₀ : Config V) (D : ℕ → V → ℕ) (T : ℕ) (v : V) :
    G.visits c₀ undelayed (activeRounds D T) v ≤ G.visits c₀ D T v ∧
      G.visits c₀ D T v ≤ G.visits c₀ undelayed T v := by
  refine ⟨?_, lemma_2_1 c₀ (fun _ _ => Nat.zero_le _) T v⟩
  rw [visits_eq_visitsOf, visits_eq_visitsOf]
  exact visitsOf_mono (exits_undelayed_le c₀ D T) v

/-- **Lemma 2.3 (the slow-down lemma).** If the delayed deployment `D` covers the graph after
exactly `T = C(D)` rounds and all agents are active in `τ` of these rounds, then the cover time of
the undelayed system satisfies `τ ≤ C(R[k]) ≤ T`. -/
theorem lemma_2_3 (c₀ : Config V) (D : ℕ → V → ℕ) {T : ℕ} (hT : G.CoverTime c₀ D T) :
    ∃ C, G.CoverTime c₀ undelayed C ∧ activeRounds D T ≤ C ∧ C ≤ T := by
  classical
  have hR : G.Covered c₀ undelayed T := fun v =>
    lt_of_lt_of_le (hT.1 v) (lemma_2_2 c₀ D T v).2
  have hex : ∃ C, G.Covered c₀ undelayed C := ⟨T, hR⟩
  refine ⟨Nat.find hex, ⟨Nat.find_spec hex, fun t ht => Nat.find_min hex ht⟩, ?_,
    Nat.find_min' hex hR⟩
  by_contra hlt
  push Not at hlt
  set C := Nat.find hex
  -- `C < τ_T`, hence `T ≥ 1` and `C ≤ τ_{T-1}`
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := by
    rcases T with _ | T'
    · simp [activeRounds] at hlt
    · exact ⟨T', rfl⟩
  have hτ : activeRounds D (T' + 1) ≤ activeRounds D T' + 1 := by
    rw [activeRounds_succ]; split_ifs <;> omega
  have hcov : G.Covered c₀ undelayed (activeRounds D T') :=
    (Nat.find_spec hex).mono c₀ undelayed (by omega)
  exact hT.2 T' (Nat.lt_succ_self _) fun v =>
    lt_of_lt_of_le (hcov v) (lemma_2_2 c₀ D T' v).1

end RotorGraph

end Podc.RotorRouterRing
