import Papers.PODC2012.IteratedSnapshotFD.Model

/-!
# The strong-correctness arguments of Theorems 2, 3 and 4, at the level of IIS schedules

The proofs of Theorems 2(c), 3 and 4(b) end with a short argument about the IIS schedule produced by
the simulation of Figure 3: the owner of a round waits (predicate `PROP_C`) until certain
processes have written, so its view contains them. We formalize these final steps for an arbitrary
IIS schedule `σ` and an arbitrary assignment `own : ℕ → P` of rounds to owners, taking the
consequence of the wait as a hypothesis. (The operational semantics of Figure 3 is in `Fig3.lean`.)

* `thm3_core` (Theorem 3, `◇P`): if after some round every owner sees all correct processes, and
  every correct process owns infinitely many rounds, then every correct process is strongly
  correct.
* `thm2c_core` (Theorem 2(c), `Ω_k`): if after some round every strongly correct owner outside the
  eventual leader set `L` sees a correct member of `L`, then `L` contains a strongly correct process.
* `thm4b_core` (Theorem 4(b), `t`-resilience): if a strongly correct process owns infinitely many
  rounds and then always sees at least `m` processes, at least `m` processes are strongly correct.
-/

namespace Podc.IteratedSnapshotFD.Schedule

variable {P : Type} (σ : Schedule P)

/-- Pigeonhole: if infinitely often some element satisfies `Q r`, some element satisfies it
infinitely often. -/
theorem exists_frequently_of_frequently {α : Type} [Finite α] {Q : ℕ → α → Prop}
    (h : ∀ R, ∃ r ≥ R, ∃ a, Q r a) : ∃ a, ∀ R, ∃ r ≥ R, Q r a := by
  classical
  have := Fintype.ofFinite α
  by_contra hc
  push Not at hc
  choose B hB using hc
  obtain ⟨r, hr, a, ha⟩ := h (Finset.univ.sup B)
  exact hB a r (le_trans (Finset.le_sup (f := B) (Finset.mem_univ a)) hr) ha

/-- Core of **Theorem 3**: with `◇P` every correct simulated process is strongly correct. -/
theorem thm3_core [Finite P] (own : ℕ → P) (hown : ∀ i, σ.Correct i → ∀ R, ∃ r ≥ R, own r = i)
    (R₀ : ℕ) (hsee : ∀ r ≥ R₀, ∀ j, σ.Correct (own r) → σ.Correct j → σ.Sees r (own r) j)
    {c : P} (hc : σ.Correct c) : ∀ j, σ.Correct j → j ∈ σ.SC := by
  obtain ⟨s, hs⟩ := σ.SC_nonempty hc
  intro j hj
  refine σ.mem_SC_of_frequently_seen hs fun R => ?_
  obtain ⟨r, hr, hor⟩ := hown s (σ.correct_of_mem_SC hs) (max R R₀)
  refine ⟨r, le_trans (le_max_left _ _) hr, ?_⟩
  have := hsee r (le_trans (le_max_right _ _) hr) j (hor ▸ σ.correct_of_mem_SC hs) hj
  rwa [hor] at this

/-- Core of **Theorem 2(c)**: the eventual leader set `L` of `Ω_k` contains a strongly correct
process. -/
theorem thm2c_core [Finite P] (own : ℕ → P) (hown : ∀ i ∈ σ.SC, ∀ R, ∃ r ≥ R, own r = i)
    (L : Set P) (R₀ : ℕ)
    (hsee : ∀ r ≥ R₀, own r ∈ σ.SC → own r ∉ L → ∃ l ∈ L, σ.Correct l ∧ σ.Sees r (own r) l)
    {c : P} (hc : σ.Correct c) : ∃ l ∈ L, l ∈ σ.SC := by
  obtain ⟨s, hs⟩ := σ.SC_nonempty hc
  by_cases hsL : s ∈ L
  · exact ⟨s, hsL, hs⟩
  obtain ⟨l, hl⟩ := exists_frequently_of_frequently (Q := fun r l => l ∈ L ∧ σ.Sees r s l)
    fun R => by
      obtain ⟨r, hr, hor⟩ := hown s hs (max R R₀)
      obtain ⟨l, hlL, -, hsee'⟩ := hsee r (le_trans (le_max_right _ _) hr) (hor ▸ hs) (hor ▸ hsL)
      exact ⟨r, le_trans (le_max_left _ _) hr, l, hlL, hor ▸ hsee'⟩
  obtain ⟨-, -, hlL, -⟩ := hl 0
  exact ⟨l, hlL, σ.mem_SC_of_frequently_seen hs fun R => by
    obtain ⟨r, hr, -, h⟩ := hl R; exact ⟨r, hr, h⟩⟩

/-- Core of **Theorem 4(b)**: if a strongly correct process `s` sees at least `m` processes in
infinitely many rounds, at least `m` processes are strongly correct. -/
theorem thm4b_core [Fintype P] [DecidableEq P] {s : P} (hs : s ∈ σ.SC) {m : ℕ}
    (hbig : ∀ R, ∃ r ≥ R, s ∈ (σ.rd r).part ∧ m ≤ ((σ.rd r).view s).card) :
    ∃ X : Finset P, m ≤ X.card ∧ ∀ i ∈ X, i ∈ σ.SC := by
  classical
  -- processes seen by `s` only finitely often stop being seen
  have key : ∀ i, ∃ B, (∀ R, ∃ r ≥ R, σ.Sees r s i) ∨ ∀ r ≥ B, ¬ σ.Sees r s i := by
    intro i
    by_cases h : ∀ R, ∃ r ≥ R, σ.Sees r s i
    · exact ⟨0, Or.inl h⟩
    · push Not at h
      obtain ⟨B, hB⟩ := h
      exact ⟨B, Or.inr hB⟩
  choose B hB using key
  obtain ⟨r, hr, hsr, hcard⟩ := hbig (Finset.univ.sup B)
  refine ⟨(σ.rd r).view s, hcard, fun i hi => σ.mem_SC_of_frequently_seen hs ?_⟩
  rcases hB i with h | h
  · exact h
  · exact absurd ⟨hsr, hi⟩ (h r (le_trans (Finset.le_sup (f := B) (Finset.mem_univ i)) hr))

end Podc.IteratedSnapshotFD.Schedule
