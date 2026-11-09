import Papers.PODC2012.TVGWaitingExpressivity.NoWait

/-!
# Bounded waiting: `𝓛_wait[d] = 𝓛_nowait` (Theorem 5.1)

The paper proves only that every language `L` is `L_wait[d](G_{2,d})` for the time-dilated TVG
`G_{2,d}` (here `G2d_LwaitAtMost`). The equality of the two *families* needs two simulations,
which we give for arbitrary TVGs (they keep the node set finite and preserve computability of
`ρ` and `ζ`):

* `dilate d A`: time stretched by `d + 1`, edges present only at multiples of `d + 1`; a pause of
  at most `d` cannot reach the next multiple, so `L_wait[d](dilate d A) = L_nowait(A)`;
* `withPause d A`: nodes `V × Fin (d + 1)`; being in `(u, j)` means "leave `u` after a pause of `j`",
  so direct journeys of `withPause d A` simulate `d`-bounded journeys of `A`:
  `L_nowait(withPause d A) = L_wait[d](A)`.
-/

namespace Podc.TVGWaitingExpressivity

open TVG TVGAutomaton

variable {V α : Type*}

/-- Time dilation by `d + 1`. -/
def dilate (d : ℕ) (A : TVGAutomaton V α) : TVGAutomaton V α where
  present e t := (d + 1) ∣ t ∧ A.present e (t / (d + 1))
  latency e t := (d + 1) * A.latency e (t / (d + 1))
  init := A.init
  accept := A.accept
  start := (d + 1) * A.start

theorem dilate_journey_iff (d : ℕ) (A : TVGAutomaton V α) (u : V) (t : ℕ) (w : List α) (v : V)
    (t'' : ℕ) : (dilate d A).Journey (waitAtMost d) u ((d + 1) * t) w v t'' ↔
      ∃ t', t'' = (d + 1) * t' ∧ A.Journey noWait u t w v t' := by
  induction w generalizing u t with
  | nil =>
    simp only [journey_nil_iff]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨t, rfl, rfl, rfl⟩
    · rintro ⟨_, rfl, rfl, rfl⟩; exact ⟨rfl, rfl⟩
  | cons a w ih =>
    simp only [journey_cons_iff]
    constructor
    · rintro ⟨v', t₁, ⟨h1, h2⟩, ⟨⟨k, rfl⟩, hp⟩, hj⟩
      have hk : k = t := by
        rcases lt_trichotomy k t with h | h | h
        · have : (d + 1) * k < (d + 1) * t := by
            exact Nat.mul_lt_mul_of_pos_left h (by omega)
          omega
        · exact h
        · have : (d + 1) * (t + 1) ≤ (d + 1) * k := Nat.mul_le_mul_left _ h
          rw [Nat.mul_succ] at this; omega
      subst hk
      have hdiv : (d + 1) * k / (d + 1) = k := Nat.mul_div_cancel_left _ (by omega)
      simp only [dilate, hdiv, ← Nat.mul_add] at hp hj
      obtain ⟨t', rfl, hj'⟩ := (ih _ _).mp hj
      exact ⟨t', rfl, v', k, rfl, hp, hj'⟩
    · rintro ⟨t', rfl, v', t₁, hw, hp, hj⟩
      rw [show t₁ = t from hw] at hp hj
      have hdiv : (d + 1) * t / (d + 1) = t := Nat.mul_div_cancel_left _ (by omega)
      refine ⟨v', (d + 1) * t, ⟨le_rfl, by omega⟩, ⟨⟨t, rfl⟩, by simpa [dilate, hdiv] using hp⟩, ?_⟩
      simp only [dilate, hdiv, ← Nat.mul_add]
      exact (ih _ _).mpr ⟨t', rfl, hj⟩

theorem dilate_LwaitAtMost (d : ℕ) (A : TVGAutomaton V α) :
    (dilate d A).LwaitAtMost d = A.Lnowait := by
  ext w
  simp only [LwaitAtMost, Lnowait, lang]
  show (∃ s ∈ A.init, ∃ f ∈ A.accept, ∃ t'', _) ↔ _
  simp only [show (dilate d A).start = (d + 1) * A.start from rfl, dilate_journey_iff]
  constructor
  · rintro ⟨s, hs, f, hf, _, t', -, h⟩; exact ⟨s, hs, f, hf, t', h⟩
  · rintro ⟨s, hs, f, hf, t', h⟩; exact ⟨s, hs, f, hf, _, t', rfl, h⟩

/-- Pauses made explicit: node `(u, j)` leaves `u` after a pause of `j ≤ d`. -/
def withPause (d : ℕ) (A : TVGAutomaton V α) : TVGAutomaton (V × Fin (d + 1)) α where
  present e t := A.present (e.1.1, e.2.1, e.2.2.1) (t + e.1.2)
  latency e t := e.1.2 + A.latency (e.1.1, e.2.1, e.2.2.1) (t + e.1.2)
  init := {x | x.1 ∈ A.init}
  accept := {x | x.1 ∈ A.accept}
  start := A.start

theorem withPause_journey (d : ℕ) (A : TVGAutomaton V α) {x : V × Fin (d + 1)} {t : ℕ}
    {w : List α} {y : V × Fin (d + 1)} {t' : ℕ}
    (h : (withPause d A).Journey noWait x t w y t') : A.Journey (waitAtMost d) x.1 t w y.1 t' := by
  induction h with
  | nil => exact .nil _ _
  | @cons u t a v t₁ w x t' hp hpres _ ih =>
    cases hp
    refine .cons (t₁ := t + u.2) ⟨by omega, by have := u.2.2; omega⟩ hpres ?_
    simpa [withPause, Nat.add_assoc] using ih

theorem journey_withPause (d : ℕ) (A : TVGAutomaton V α) {u : V} {t : ℕ} {w : List α} {v : V}
    {t' : ℕ} (h : A.Journey (waitAtMost d) u t w v t') :
    ∃ j, (withPause d A).Journey noWait (u, j) t w (v, 0) t' := by
  induction h with
  | nil => exact ⟨0, .nil _ _⟩
  | @cons u t a v t₁ w x t' hp hpres _ ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨h1, h2⟩ := hp
    refine ⟨⟨t₁ - t, by omega⟩, .cons (v := (v, j)) rfl ?_ ?_⟩
    · simpa [withPause, show t + (t₁ - t) = t₁ by omega] using hpres
    · simpa [withPause, show t + (t₁ - t) = t₁ by omega, ← Nat.add_assoc] using hj

theorem withPause_Lnowait (d : ℕ) (A : TVGAutomaton V α) :
    (withPause d A).Lnowait = A.LwaitAtMost d := by
  ext w
  constructor
  · rintro ⟨s, hs, f, hf, t', h⟩
    exact ⟨s.1, hs, f.1, hf, t', withPause_journey d A h⟩
  · rintro ⟨s, hs, f, hf, t', h⟩
    obtain ⟨j, hj⟩ := journey_withPause d A h
    exact ⟨(s, j), hs, (f, 0), hf, t', hj⟩

/-- **Theorem 5.1** of [CFGSY'12]: for every `d`, `𝓛_wait[d] = 𝓛_nowait`. -/
theorem theorem_5_1 (α : Type) (d : ℕ) : LwaitAtMostFamily α d = LnowaitFamily α := by
  ext L
  constructor
  · rintro ⟨V, _, A, rfl⟩
    exact ⟨V × Fin (d + 1), inferInstance, withPause d A, withPause_Lnowait d A⟩
  · rintro ⟨V, _, A, rfl⟩
    exact ⟨V, inferInstance, dilate d A, dilate_LwaitAtMost d A⟩

end Podc.TVGWaitingExpressivity
