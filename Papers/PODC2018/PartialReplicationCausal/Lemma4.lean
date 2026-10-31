import Papers.PODC2018.PartialReplicationCausal.Runs

/-!
# Lemma 4 is false

Lemma 4 of the paper: *Let `u` be an update with timestamp `T` from replica `j` to `i`. Let `u'` be
an update with timestamp `T'` from replica `k` to `i` such that `u' ↪ u`. Then `T[e_ki] ≥ T'[e_ki]`
when `k ≠ j`, and `T[e_ki] > T'[e_ki]` when `k = j`.*

As stated, `T[e_ki]` is not even defined when `e_ki ∉ E_j` (and the proof of Lemma 5 applies
Lemma 4 to such edges). But the lemma also fails when `e_ki ∈ E_j`. Five replicas
`A, B, C, D, I` and five registers `f, e, b, a, g`:

```
X_A = {f, e, b}   X_B = {e, a}   X_C = {a, g}   X_D = {g, b}   X_I = {f, a, g}
```

Execution: `A` writes `f` (`u'`, sent to `I` only; delayed), `A` writes `e`, `B` applies it and
writes `a`, `C` applies that and writes `g`, `D` applies that and writes `g` (`u`, sent to `I`).
Then `u' ↪ u`, `e_AI ∈ E_D` (triangle `D, I, A`), but `e_AI ∉ E_C` (as `X_C ⊆ X_I`, every loop
through `C` violates condition (iii)), so `C` does not forward the information about `u'` and
`T[e_AI] = 0 < 1 = T'[e_AI]`. Safety is not violated: `I` receives `B`'s and `C`'s updates (on
`a` and `g`) too, and `B` does track `e_AI`. Theorem 3 holds (`theorem_3_safety`); only the
paper's proof route via Lemma 4 is broken.
-/

namespace Podc.PartialReplicationCausal.Lemma4

open Classical

/-- Replicas `A = 0, B = 1, C = 2, D = 3, I = 4`; registers `f = 0, e = 1, b = 2, a = 3, g = 4`. -/
def X : Fin 5 → Set (Fin 5) := ![{0, 1, 2}, {1, 3}, {3, 4}, {4, 2}, {0, 3, 4}]

lemma adj_iff (j k : Fin 5) : Adj X j k ↔ j ≠ k ∧ ∃ x, x ∈ X j ∧ x ∈ X k := by
  simp [Adj, Set.Nonempty]

/-- `e_AI ∉ E_C`. -/
theorem not_tsEdge_C : ¬ TsEdge X 2 0 4 := by
  rintro ⟨-, h | h | ⟨l, r, hl⟩⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · refine not_isLoop_of_subset ?_ ?_ l r hl
    · intro x hx; simp [X] at hx ⊢; omega
    · rw [adj_iff]; rintro ⟨-, x, hx, hx'⟩; simp [X] at hx hx'; omega

/-- `e_AI ∈ E_D`: `(D, I, A)` is a `(D, e_AI)`-loop. -/
theorem tsEdge_D : TsEdge X 3 0 4 := by
  refine ⟨(adj_iff _ _).2 ⟨by decide, 0, by simp [X], by simp [X]⟩, Or.inr (Or.inr ⟨[], [], ?_⟩)⟩
  refine ⟨by decide, ?_, ⟨0, by simp [X], by simp⟩, ⟨2, by simp [X], by simp⟩, by simp⟩
  simp only [List.nil_append, List.cons_append, List.isChain_cons_cons, List.isChain_singleton,
    and_true]
  refine ⟨(adj_iff _ _).2 ⟨by decide, 4, by simp [X], by simp [X]⟩,
    (adj_iff _ _).2 ⟨by decide, 0, by simp [X], by simp [X]⟩,
    (adj_iff _ _).2 ⟨by decide, 2, by simp [X], by simp [X]⟩⟩

lemma adj_A_I : Adj X 0 4 := (adj_iff _ _).2 ⟨by decide, 0, by simp [X], by simp [X]⟩

/-! ### The execution -/

/-- Initial state. -/
noncomputable def s₀ : State (Fin 5) (Fin 5) :=
  ⟨0, fun _ => ⟨0, 0, fun _ _ => 0, ∅⟩, fun _ _ _ => 0, fun _ => ∅⟩

noncomputable def s₁ := s₀.write X 0 0   -- A writes f   (update 0 = u')
noncomputable def s₂ := s₁.write X 0 1   -- A writes e   (update 1)
noncomputable def s₃ := s₂.apply X 1 1   -- B applies 1
noncomputable def s₄ := s₃.write X 1 3   -- B writes a   (update 2)
noncomputable def s₅ := s₄.apply X 2 2   -- C applies 2
noncomputable def s₆ := s₅.write X 2 4   -- C writes g   (update 3)
noncomputable def s₇ := s₆.apply X 3 3   -- D applies 3
noncomputable def s₈ := s₇.write X 3 4   -- D writes g   (update 4 = u)

lemma r₀ : Reachable X s₀ := ⟨s₀, ⟨rfl, rfl, rfl⟩, .refl⟩

lemma r₈ : Reachable X s₈ := by
  have r₁ : Reachable X s₁ := r₀.write (by simp [X])
  have r₂ : Reachable X s₂ := r₁.write (by simp [X])
  have r₃ : Reachable X s₃ := r₂.apply (by simp [s₂, s₁, s₀])
    (by simp [s₂, s₁, s₀, State.write]) (by simp [s₂, s₁, s₀, State.write, X])
    (by simp [s₂, s₁, s₀, State.write])
    (by intro a ha; obtain rfl : a = 0 := by omega
        simp [s₂, s₁, s₀, State.write, X])
  have r₄ : Reachable X s₄ := r₃.write (by simp [X])
  have r₅ : Reachable X s₅ := r₄.apply (by simp [s₄, s₃, s₂, s₁, s₀, State.apply])
    (by simp [s₄, s₃, s₂, s₁, s₀, State.write, State.apply])
    (by simp [s₄, s₃, s₂, s₁, s₀, State.write, State.apply, X])
    (by simp [s₄, s₃, s₂, s₁, s₀, State.write, State.apply])
    (by intro a ha
        interval_cases a <;> simp [s₄, s₃, s₂, s₁, s₀, State.write, State.apply, X])
  have r₆ : Reachable X s₆ := r₅.write (by simp [X])
  have r₇ : Reachable X s₇ := r₆.apply (by simp [s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.apply])
    (by simp [s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.write, State.apply])
    (by simp [s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.write, State.apply, X])
    (by simp [s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.write, State.apply])
    (by intro a ha
        interval_cases a <;> simp [s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.write, State.apply, X])
  exact r₇.write (by simp [X])

/-- `u' ↪ u`. -/
lemma hb_0_4 : HB s₈ 0 4 := by
  have e : ∀ a b : ℕ, b < s₈.n → a ∈ (s₈.log b).pre → HB s₈ a b := fun a b hb hab => .single ⟨hb, hab⟩
  refine .trans (e 0 1 ?_ ?_) (.trans (e 1 2 ?_ ?_) (.trans (e 2 3 ?_ ?_) (e 3 4 ?_ ?_))) <;>
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.write, State.apply]

/-- **Lemma 4 is false**, even restricted to edges `e_ki ∈ E_j`: in a reachable state of the
algorithm, update `u = 4` from `j = D` to `i = I` and update `u' = 0` from `k = A` to `I` satisfy
`u' ↪ u` and `e_AI ∈ E_D`, but `T[e_AI] = 0 < 1 = T'[e_AI]`. -/
theorem lemma_4_false :
    Reachable X s₈ ∧
    (s₈.log 4).src = 3 ∧ (s₈.log 4).reg ∈ X 4 ∧ (s₈.log 0).src = 0 ∧ (s₈.log 0).reg ∈ X 4 ∧
    HB s₈ 0 4 ∧ TsEdge X 3 0 4 ∧
    (s₈.log 4).ts 0 4 = 0 ∧ (s₈.log 0).ts 0 4 = 1 := by
  refine ⟨r₈, by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.write, State.apply], by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.write, State.apply, X], ?_, ?_, hb_0_4, tsEdge_D,
    ?_, ?_⟩
  · simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.write, State.apply]
  · simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.write, State.apply, X]
  · simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.write, State.apply, incr, merge, not_tsEdge_C]
  · rw [show (s₈.log 0).ts = incr X (fun _ _ => 0) 0 0 by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.write, State.apply]]
    simp only [incr]
    rw [ite_eq_left ⟨tsEdge_self_iff.2 adj_A_I, trivial, by simp [X]⟩]

/-- Lemma 4 as stated in the paper (for `k ≠ j`), for the algorithm of Section 3.2 and every share
graph. It is refuted by `lemma_4_false`. -/
def Lemma4Statement : Prop :=
  ∀ {ι Reg : Type} (X : ι → Set Reg) (s : State ι Reg), Reachable X s →
    ∀ (u u' : ℕ) (i : ι), u < s.n → (s.log u).src ≠ i → (s.log u).reg ∈ X i →
      (s.log u').src ≠ i → (s.log u').reg ∈ X i → (s.log u').src ≠ (s.log u).src →
      TsEdge X (s.log u).src (s.log u').src i → HB s u' u →
      (s.log u').ts (s.log u').src i ≤ (s.log u).ts (s.log u').src i

theorem not_lemma4Statement : ¬ Lemma4Statement := by
  intro h
  obtain ⟨hr, h1, h2, h3, h4, h5, h6, h7, h8⟩ := lemma_4_false
  have := h X s₈ hr 4 0 4 (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.write, State.apply])
    (by rw [h1]; decide) h2 (by rw [h3]; decide) h4 (by rw [h1, h3]; decide)
    (by rw [h1, h3]; exact h6) h5
  rw [h3, h7, h8] at this
  omega

end Podc.PartialReplicationCausal.Lemma4
