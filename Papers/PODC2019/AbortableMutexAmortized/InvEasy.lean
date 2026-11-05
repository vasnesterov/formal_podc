import Papers.PODC2019.AbortableMutexAmortized.InvBasic

/-!
# Preservation of the invariant: lines 4, 5, 8, 11 (no node is written)
-/

namespace Podc.AbortableMutexAmortized

variable {n : ℕ} {s : State n} {Q : List (Fin n)} {a0 : Node n}

/-- Line 4 with `go_p = true`: move to line 5. -/
theorem inv_l4_go (hs : Struct s Q a0) (hl : Loc s a0) {p : Fin n} (hp : s.pc p = .l4)
    (hg : s.go p = true) :
    Struct { s with pc := Function.update s.pc p .l5 } Q a0 ∧
      Loc { s with pc := Function.update s.pc p .l5 } a0 := by
  have hInQ : ∀ q, InQ { s with pc := Function.update s.pc p .l5 } q ↔ InQ s q := by
    intro q
    by_cases hq : q = p
    · subst hq; simp [InQ, hp]
    · simp [InQ, Function.update_of_ne hq]
  refine ⟨⟨hs.ok, hs.last, fun q => (hs.mem q).trans (hInQ q).symm, hs.a0_ne⟩, ?_⟩
  constructor
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq ⊢; exact hl.i6a q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq ⊢; exact hl.i6b q hq
  · intro q hq
    simp only [hInQ]
    by_cases e : q = p
    · subst e; exact hl.i7 q (by simp [hp])
    · simp [Function.update_of_ne e] at hq; exact hl.i7 q hq
  · intro h; apply hl.i9a; intro y hy
    by_cases e : y = p
    · subst e; simp [hp]
    · have := h y hy; simpa [Function.update_of_ne e] using this
  · intro y hy h7; by_cases e : y = p
    · subst e; simp at h7
    · simp [Function.update_of_ne e] at h7; exact hl.i9b y hy h7
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq; exact hl.i10 q hq
  · intro y hy h4 hg'; by_cases e : y = p
    · subst e; simp at h4
    · simp [Function.update_of_ne e] at h4
      obtain ⟨q, hq, hv⟩ := hl.i11a y hy h4 hg'
      refine ⟨q, ?_, hv⟩
      by_cases e' : q = p
      · subst e'; simp [hp] at hq
      · simpa [Function.update_of_ne e'] using hq
  · intro x y hx hy h4 hg'
    rw [hInQ] at hx
    by_cases e : y = p
    · subst e; simp at h4
    · simp [Function.update_of_ne e] at h4
      rcases hl.i11b x y hx hy h4 hg' with h | ⟨h1, h2, h3⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, ?_, h3⟩
        by_cases e' : x = p
        · subst e'; simp [hp] at h2
        · simpa [Function.update_of_ne e'] using h2
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq; exact hl.i11c q hq
  · intro q hq; by_cases e : q = p
    · subst e; exact hg
    · simp [Function.update_of_ne e] at hq; exact hl.i12 q hq
  · intro q hq h1; rw [hInQ] at hq; by_cases e : q = p
    · subst e; simp at h1
    · simp [Function.update_of_ne e] at h1; exact hl.x1 q hq h1

/-- Line 5: `go_p ← false`, move to line 6. -/
theorem inv_l5 (hs : Struct s Q a0) (hl : Loc s a0) {p : Fin n} (hp : s.pc p = .l5) :
    Struct { s with go := Function.update s.go p false, pc := Function.update s.pc p .l6 } Q a0 ∧
      Loc { s with go := Function.update s.go p false, pc := Function.update s.pc p .l6 } a0 := by
  have hInQ : ∀ q,
      InQ { s with go := Function.update s.go p false, pc := Function.update s.pc p .l6 } q ↔
        InQ s q := by
    intro q
    by_cases hq : q = p
    · subst hq; simp [InQ, hp]
    · simp [InQ, Function.update_of_ne hq]
  refine ⟨⟨hs.ok, hs.last, fun q => (hs.mem q).trans (hInQ q).symm, hs.a0_ne⟩, ?_⟩
  constructor
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq ⊢; exact hl.i6a q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq ⊢; exact hl.i6b q hq
  · intro q hq
    simp only [hInQ]
    by_cases e : q = p
    · subst e; exact hl.i7 q (by simp [hp])
    · simp [Function.update_of_ne e] at hq; exact hl.i7 q hq
  · intro h; apply hl.i9a; intro y hy
    by_cases e : y = p
    · subst e; simp [hp]
    · have := h y hy; simpa [Function.update_of_ne e] using this
  · intro y hy h7; by_cases e : y = p
    · subst e; simp at h7
    · simp [Function.update_of_ne e] at h7; exact hl.i9b y hy h7
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq; exact hl.i10 q hq
  · intro y hy h4 hg'; by_cases e : y = p
    · subst e; simp at h4
    · simp [Function.update_of_ne e] at h4 hg'
      obtain ⟨q, hq, hv⟩ := hl.i11a y hy h4 hg'
      refine ⟨q, ?_, hv⟩
      by_cases e' : q = p
      · subst e'; simp [hp] at hq
      · simpa [Function.update_of_ne e'] using hq
  · intro x y hx hy h4 hg'
    rw [hInQ] at hx
    by_cases e : y = p
    · subst e; simp at h4
    · simp [Function.update_of_ne e] at h4 hg'
      rcases hl.i11b x y hx hy h4 hg' with h | ⟨h1, h2, h3⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, ?_, h3⟩
        by_cases e' : x = p
        · subst e'; simp [hp] at h2
        · simpa [Function.update_of_ne e'] using h2
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq; exact hl.i11c q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq ⊢; exact hl.i12 q hq
  · intro q hq h1; rw [hInQ] at hq; by_cases e : q = p
    · subst e; simp at h1
    · simp [Function.update_of_ne e] at h1; exact hl.x1 q hq h1

theorem wake_eq {p q : Fin n} (hv : s.v p = .go q) :
    wake s p = { s with go := Function.update s.go q true, pc := Function.update s.pc p .l1 } := by
  simp [wake, hv]

/-- Lines 8 and 11: `*v_p ← true`, back to the Remainder section. -/
theorem inv_wake (hs : Struct s Q a0) (hl : Loc s a0) {p : Fin n}
    (hp : s.pc p = .l8 ∨ s.pc p = .l11) :
    Struct (wake s p) Q a0 ∧ Loc (wake s p) a0 := by
  obtain ⟨g, hv⟩ := hl.i11c p hp
  rw [wake_eq hv]
  have hInQ : ∀ q,
      InQ { s with go := Function.update s.go g true, pc := Function.update s.pc p .l1 } q ↔
        InQ s q := by
    intro q
    by_cases hq : q = p
    · subst hq
      rcases hp with hp | hp
      · have := hl.i6b q hp
        simp only [InQ, hp]
        rcases this with h | h <;> simp [h]
      · simp [InQ, hp]
    · simp [InQ, Function.update_of_ne hq]
  refine ⟨⟨hs.ok, hs.last, fun q => (hs.mem q).trans (hInQ q).symm, hs.a0_ne⟩, ?_⟩
  constructor
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq ⊢; exact hl.i6a q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq ⊢; exact hl.i6b q hq
  · intro q hq
    simp only [hInQ]
    by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq; exact hl.i7 q hq
  · intro h; apply hl.i9a; intro y hy
    by_cases e : y = p
    · subst e; rcases hp with hp | hp <;> simp [hp]
    · have := h y hy; simpa [Function.update_of_ne e] using this
  · intro y hy h7; by_cases e : y = p
    · subst e; simp at h7
    · simp [Function.update_of_ne e] at h7; exact hl.i9b y hy h7
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq; exact hl.i10 q hq
  · intro y hy h4 hg'; by_cases e : y = p
    · subst e; simp at h4
    · simp [Function.update_of_ne e] at h4
      by_cases eg : y = g
      · subst eg; simp at hg'
      simp [Function.update_of_ne eg] at hg'
      obtain ⟨q, hq, hv'⟩ := hl.i11a y hy h4 hg'
      refine ⟨q, ?_, hv'⟩
      by_cases e' : q = p
      · subst e'; rw [hv] at hv'; cases hv'; exact absurd rfl eg
      · simpa [Function.update_of_ne e'] using hq
  · intro x y hx hy h4 hg'
    rw [hInQ] at hx
    by_cases e : y = p
    · subst e; simp at h4
    · simp [Function.update_of_ne e] at h4
      by_cases eg : y = g
      · subst eg; simp at hg'
      simp [Function.update_of_ne eg] at hg'
      rcases hl.i11b x y hx hy h4 hg' with h | ⟨h1, h2, h3⟩
      · exact Or.inl h
      · by_cases e' : x = p
        · subst e'; rw [hv] at h3; cases h3; exact absurd rfl eg
        · exact Or.inr ⟨h1, by simpa [Function.update_of_ne e'] using h2, h3⟩
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq; exact hl.i11c q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq
      by_cases eg : q = g
      · subst eg; simp
      · simp [Function.update_of_ne eg]; exact hl.i12 q hq
  · intro q hq h1; rw [hInQ] at hq; by_cases e : q = p
    · subst e
      rcases hp with hp | hp
      · exact absurd hq (not_InQ_l8 hp)
      · exact hl.x1 q hq (by simp [hp])
    · simp [Function.update_of_ne e] at h1; exact hl.x1 q hq h1

end Podc.AbortableMutexAmortized
