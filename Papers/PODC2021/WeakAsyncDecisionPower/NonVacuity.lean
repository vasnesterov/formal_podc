import Podc.Computability.Distributed.DistributedAutomata.Fairness

/-!
# Non-vacuity: a non-trivial distributed automaton

The hypotheses of Lemmas 3.2–3.5 (consistency, deciding a labelling property, adversarial or
pseudo-stochastic fairness, non-counting) are satisfied by non-trivial automata. `flood` (states
`Bool`, non-counting, a node becomes `true` once it or a neighbour is `true`) decides "some node is
labelled `true`" — a property in `Cutoff(1)` — on every class of connected graphs, for every
selection constraint and every fairness constraint. The hypotheses of Lemma 3.1 (halting and
consistent) are met by the constant accepting automaton `acceptAll` (`acceptAll_halting`,
`acceptAll_consistent`).
-/

namespace Podc.WeakAsyncDecisionPower

open Cslib.DistributedAutomata Set

/-- Flooding: a node becomes `true` once it or one of its neighbours is `true`. -/
def floodM : Machine Bool Bool where
  β := 1
  one_le_β := le_rfl
  init := id
  δ := fun q N => q || decide (1 ≤ N true)
  Y := {true}
  N := {false}
  disjoint := by simp

/-- The flooding automaton for a given scheduler. -/
def flood (κ : Selection) (φ : Fairness) : Automaton Bool Bool := ⟨floodM, κ, φ⟩

section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

lemma flood_step_true {C : V → Bool} {S : Set V} {v : V} (h : C v = true) :
    step floodM G C S v = true := by
  by_cases hv : v ∈ S
  · rw [step_of_mem _ _ hv]; simp [floodM, h]
  · rw [step_of_notMem _ _ hv, h]

lemma flood_mono (C : V → Bool) (σ : ℕ → Set V) {v : V} {t t' : ℕ} (htt : t ≤ t')
    (h : runFrom floodM G C σ t v = true) : runFrom floodM G C σ t' v = true := by
  induction t' with
  | zero => simpa [Nat.le_zero.1 htt] using h
  | succ t' ih =>
    rcases Nat.eq_or_lt_of_le htt with rfl | hlt
    · exact h
    · rw [runFrom_succ]; exact flood_step_true G (ih (by omega))

lemma flood_spread (C : V → Bool) (σ : ℕ → Set V) (hσ : ∀ v N, ∃ t ≥ N, v ∈ σ t) {u v : V}
    (huv : G.Adj u v) {t : ℕ} (hu : runFrom floodM G C σ t u = true) :
    ∃ t', runFrom floodM G C σ t' v = true := by
  obtain ⟨t', ht', hv⟩ := hσ v t
  refine ⟨t' + 1, ?_⟩
  rw [runFrom_succ, step_of_mem _ _ hv]
  have hu' := flood_mono G C σ ht' hu
  have hpos : 1 ≤ {w | G.Adj v w ∧ runFrom floodM G C σ t' w = true}.ncard :=
    (ncard_pos (toFinite _)).2 ⟨u, huv.symm, hu'⟩
  change (runFrom floodM G C σ t' v || decide (1 ≤ min 1
    {w | G.Adj v w ∧ runFrom floodM G C σ t' w = true}.ncard)) = true
  simp [hpos]

lemma flood_reach (C : V → Bool) (σ : ℕ → Set V) (hσ : ∀ v N, ∃ t ≥ N, v ∈ σ t) {u v : V}
    (huv : G.Reachable u v) {t₀ : ℕ} (hu : runFrom floodM G C σ t₀ u = true) :
    ∃ t, runFrom floodM G C σ t v = true := by
  obtain ⟨p⟩ := huv
  induction p generalizing t₀ with
  | nil => exact ⟨t₀, hu⟩
  | cons h p ih =>
    obtain ⟨t₁, ht₁⟩ := flood_spread G C σ hσ h hu
    exact ih ht₁

/-- Runs from an all-`false` configuration stay all-`false`. -/
lemma flood_false (σ : ℕ → Set V) (t : ℕ) : runFrom floodM G (fun _ => false) σ t = fun _ => false := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext v
    rw [runFrom_succ, ih]
    by_cases hv : v ∈ σ t
    · rw [step_of_mem _ _ hv]
      simp [floodM, view]
    · rw [step_of_notMem _ _ hv]

end

/-- `flood κ φ` decides "some node is labelled `true`" on connected graphs (any degree bound), for
every selection and fairness constraint. -/
theorem flood_decides (κ : Selection) (φ : Fairness) (k : ℕ∞) :
    (flood κ φ).Decides k fun G => ∃ v, G.label v = true := by
  have key : ∀ G : LGraph Bool, G.Admissible k → ∀ σ, (flood κ φ).FairSchedule G σ →
      ((∃ v, G.label v = true) → EventuallyIn floodM.Y ((flood κ φ).run G σ)) ∧
      ((¬ ∃ v, G.label v = true) → EventuallyIn floodM.N ((flood κ φ).run G σ)) := by
    intro G hG σ hσ
    constructor
    · rintro ⟨u, hu⟩
      have hev : ∀ v, ∃ t, (flood κ φ).run G σ t v = true := fun v =>
        flood_reach G.graph _ σ hσ.2.1 (hG.connected.preconnected u v) (t₀ := 0) hu
      choose T hT using hev
      have : Fintype G.V := Fintype.ofFinite _
      refine ⟨Finset.univ.sup T, fun t ht v => ?_⟩
      exact flood_mono G.graph _ σ ((Finset.le_sup (Finset.mem_univ v)).trans ht) (hT v)
    · intro hno
      push_neg at hno
      have hinit : (flood κ φ).init G = fun _ => false := by
        funext v; simpa [Automaton.init, flood, floodM] using hno v
      refine ⟨0, fun t _ v => ?_⟩
      show runFrom floodM G.graph ((flood κ φ).init G) σ t v ∈ floodM.N
      rw [hinit, flood_false]
      rfl
  have hcons : (flood κ φ).Consistent k := by
    intro G hG
    by_cases h : ∃ v, G.label v = true
    · exact Or.inl fun σ hσ => (key G hG σ hσ).1 h
    · exact Or.inr fun σ hσ => (key G hG σ hσ).2 h
  refine ⟨hcons, fun G hG => ?_⟩
  have := hG.nonempty
  obtain ⟨σ, hσ⟩ := exists_fair (V := G.V) κ φ
  rw [(flood κ φ).accepts_iff hcons hG hσ]
  constructor
  · intro hacc
    by_contra h
    exact not_eventuallyIn_both floodM.disjoint hacc ((key G hG σ hσ).2 h)
  · intro h
    exact (key G hG σ hσ).1 h

/-- The property decided by `flood` is a labelling property. -/
theorem flood_isLabelling (κ : Selection) (φ : Fairness) (k : ℕ∞) :
    (flood κ φ).IsLabelling k := by
  intro G H hG hH hc
  rw [((flood_decides κ φ k).2 G hG), ((flood_decides κ φ k).2 H hH)]
  have hc' := congrFun hc true
  simp only [LGraph.count] at hc'
  constructor
  · rintro ⟨v, hv⟩
    have : 0 < {v | H.label v = true}.ncard := by
      rw [← hc']; exact (ncard_pos (toFinite _)).2 ⟨v, hv⟩
    obtain ⟨w, hw⟩ := (ncard_pos (toFinite _)).1 this
    exact ⟨w, hw⟩
  · rintro ⟨v, hv⟩
    have : 0 < {v | G.label v = true}.ncard := by
      rw [hc']; exact (ncard_pos (toFinite _)).2 ⟨v, hv⟩
    obtain ⟨w, hw⟩ := (ncard_pos (toFinite _)).1 this
    exact ⟨w, hw⟩

/-- The one-state machine that accepts everything. -/
def acceptAllM (Λ : Type*) : Machine Λ Unit where
  β := 1
  one_le_β := le_rfl
  init := fun _ => ()
  δ := fun q _ => q
  Y := univ
  N := ∅
  disjoint := disjoint_empty _

/-- The constant accepting automaton, for any scheduler. -/
def acceptAll (Λ : Type*) (κ : Selection) (φ : Fairness) : Automaton Λ Unit :=
  ⟨acceptAllM Λ, κ, φ⟩

theorem acceptAll_halting (Λ : Type*) : (acceptAllM Λ).Halting := fun _ _ _ => rfl

theorem acceptAll_consistent (Λ : Type*) (κ : Selection) (φ : Fairness) (k : ℕ∞) :
    (acceptAll Λ κ φ).Consistent k :=
  fun _ _ => Or.inl fun _ _ => ⟨0, fun _ _ _ => mem_univ _⟩

end Podc.WeakAsyncDecisionPower
