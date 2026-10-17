import Papers.PODC2020.BezoutElection.Alg2GlobStep

/-!
# Algorithm 2: the global invariant is preserved by writes
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P] {m : ℕ}
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id}

/-- While the winner's write of line N(11) is pending, nobody else has a pending write to the
register. -/
theorem n11_others {n U : ℕ} (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {A : AState Id P} {p : P} {w : Reg Id} (hI : AInv n U ids A) (hp : (A.loc p).st = .pend w)
    (hN : w.level = A.reg.level + 1) : ∀ j, j ≠ p → ∀ w', (A.loc j).st ≠ .pend w' := by
  obtain ⟨B, hL⟩ := hI
  obtain ⟨ℓ, E⟩ : ∃ ℓ, Lead n ids A ℓ := by
    rcases hL with N | h
    · have := N.noN11 p w hp; omega
    · exact h
  have hphℓ : (A.loc ℓ).ph = .committing := by
    rcases hph : (A.loc ℓ).ph with _ | _
    · have := (E.el hph).noN11 p w hp; omega
    · rfl
  have Co := E.co hphℓ
  have hpℓ := Co.n11 p w hp hN; subst hpℓ
  obtain ⟨hcard, -⟩ := Co.closing w hp hN
  intro j hj w' h
  refine (Co.quiet j (mem_of_card_eq_of_ne hid hn _ p (fun a ha => ?_) hcard j hj)).2.1 w' h
  obtain ⟨i, rfl, -, hi⟩ := B.discLoc p E.act.1 a ha
  exact ⟨i, rfl, by rintro rfl; rw [E.act.2] at hi; cases hi⟩

lemma pendAt_write_self {vpc : P → VPC Id} {q : P} {j : ℕ} (hj : j < m) {w : Reg Id}
    (hq : vpc q = .pc (.write j w)) {x : Fin m} {w' : Reg Id} (h : PendAt π vpc q x w') :
    x = π q ⟨j, hj⟩ ∧ w' = w := by
  obtain ⟨k, h1, h2⟩ := h
  rw [hq] at h1
  simp only [VPC.pc.injEq, PC.write.injEq] at h1
  obtain ⟨h1, rfl⟩ := h1
  refine ⟨?_, rfl⟩
  rw [← h2]; congr 1; exact Fin.ext h1.symm

lemma pendAt_update_loop {vpc : P → VPC Id} {q : P} {j : ℕ} {q' : P} {x : Fin m} {w : Reg Id} :
    PendAt π (Function.update vpc q (.loop j)) q' x w ↔ q' ≠ q ∧ PendAt π vpc q' x w :=
  pendAt_update_noPend (by intro _ _ h; cases h)

theorem ginv_write (hid : Function.Injective ids) (hn : Fintype.card P = pp.n)
    {mem : Fin m → Reg Id} {loc : P → St Id m} {vpc : P → VPC Id} {g : Ghost P}
    (G : GInv π pp ids mem loc vpc g) {q : P} {j : ℕ} (hj : j < m) {w : Reg Id}
    (hq : vpc q = .pc (.write j w)) :
    GInv π pp ids (Function.update mem (π q ⟨j, hj⟩) w) loc
      (Function.update vpc q (.loop (j + 1))) g := by
  obtain ⟨k, hk⟩ : ∃ k : Fin m, k = ⟨j, hj⟩ := ⟨_, rfl⟩
  rw [← hk]
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 = π q k := ⟨_, rfl⟩
  rw [← hx0]
  set mem' := Function.update mem x0 w with hmem'
  set vpc' := Function.update vpc q (VPC.loop (j + 1)) with hvpc'
  have hst : ((absAt π mem loc vpc x0).loc q).st = .pend w := by
    rw [absAt_loc, hq, hx0, Equiv.symm_apply_apply]; simp [locX, vstatus, hk]
  have A0 := G.abs x0
  obtain ⟨-, hLU, hcase⟩ := A0.1.pendLv q w hst
  simp only [absAt_reg] at hLU hcase
  have hpq : PendAt π vpc q x0 w := ⟨k, by rw [hq, hk], hx0.symm⟩
  -- abstract states
  have habs0 : absAt π mem' loc vpc' x0 = (absAt π mem loc vpc x0).wr q w := by
    unfold absAt AState.wr AState.setSt AState.upd
    simp only [hmem', Function.update_self]
    congr 1
    funext q'
    by_cases hq' : q' = q
    · subst hq'; simp [hvpc', locX, vstatus, hx0, hk, AStatus.fresh]
    · simp [hvpc', Function.update_of_ne hq']
  have habs1 : ∀ x, x ≠ x0 → absAt π mem' loc vpc' x = absAt π mem loc vpc x := by
    intro x hx
    have hk' : (π q).symm x ≠ k := by intro h; apply hx; rw [hx0, ← h]; simp
    have hv : ((π q).symm x).val ≠ j := fun h => hk' (by rw [hk]; exact Fin.ext h)
    unfold absAt
    simp only [hmem', Function.update_of_ne hx]
    congr 1
    funext q'
    by_cases hq' : q' = q
    · subst hq'; simp only [hvpc', Function.update_self, hq, vstatus]
      by_cases h : j < ((π q').symm x).val
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h, if_neg (fun h' => hv h'.symm)]
    · simp [hvpc', Function.update_of_ne hq']
  -- other pending writes are unaffected
  have hother : ∀ j', j' ≠ q → ∀ x w', PendAt π vpc j' x w' →
      (mem' x).level = (mem x).level ∧ (w'.level = (mem x).level + 1 → x ≠ x0 ∨
        (mem' x).leaders = (mem x).leaders) := by
    intro j' hj' x w' h
    by_cases hx : x = x0
    · subst hx
      rcases hcase with ⟨h1, h2⟩ | hN
      · exact ⟨by simp [hmem', h1], fun _ => Or.inr (by simp [hmem', h2])⟩
      · exfalso
        exact n11_others hid hn A0 hst hN.1 j' hj' w' (pendAt_iff.1 h)
    · exact ⟨by simp [hmem', Function.update_of_ne hx], fun _ => Or.inl hx⟩
  have hN11 : ∀ j', j' ≠ q → (IsN11At π mem vpc j' ↔ IsN11At π mem' vpc' j') := by
    intro j' hj'
    constructor
    · rintro ⟨x, w', h1, h2⟩
      exact ⟨x, w', pendAt_update_loop.2 ⟨hj', h1⟩, by rw [(hother j' hj' x w' h1).1]; exact h2⟩
    · rintro ⟨x, w', h1, h2⟩
      have h1 := (pendAt_update_loop.1 h1).2
      exact ⟨x, w', h1, by rw [← (hother j' hj' x w' h1).1]; exact h2⟩
  have hnotN : ¬IsN11At π mem' vpc' q :=
    not_isN11At_of_noPend (by simp [hvpc']; intro _ _ h; cases h)
  have hcnt := n11Count_change (π := π) mem mem' vpc vpc' q hN11
  rw [if_neg hnotN] at hcnt
  have hsum : ∑ x, (mem' x).level + (mem x0).level = ∑ x, (mem x).level + w.level := by
    have := Fintype.sum_update_add (fun x => (mem x).level) x0 w.level
    rw [← this]; congr 1
    apply Finset.sum_congr rfl; intro x _
    by_cases hx : x = x0
    · subst hx; simp [hmem']
    · simp [hmem', Function.update_of_ne hx]
  refine ⟨fun x => ?_, G.me, G.g1, G.g2, G.g3, G.g4, ?_, ?_, ?_, ?_, G.g7, ?_⟩
  · by_cases hx : x = x0
    · rw [hx, habs0]; exact ainv_write hid hn A0 hst
    · rw [habs1 x hx]; exact G.abs x
  · have h5 := G.g5
    rcases hcase with ⟨h1, -⟩ | hN
    · have hq11 : ¬IsN11At π mem vpc q := by
        rintro ⟨x, w', h, h2⟩
        obtain ⟨hx, rfl⟩ := pendAt_write_self hj hq h
        rw [← hk, ← hx0] at hx; subst hx
        omega
      rw [if_neg hq11] at hcnt
      omega
    · have hN1 : w.level = (mem x0).level + 1 := hN.1
      have hq11 : IsN11At π mem vpc q := ⟨x0, w, hpq, hN1⟩
      rw [if_pos hq11] at hcnt
      omega
  · intro x a ha
    by_cases hx : x = x0
    · rw [hx] at ha; simp only [hmem', Function.update_self] at ha
      rcases hcase with ⟨-, h2⟩ | hN
      · rw [h2] at ha; exact G.g6a x0 a ha
      · rcases G.g6c q x0 w hpq hN.1 a ha with h | ⟨rfl, h⟩
        · exact G.g6a x0 _ h
        · exact ⟨q, rfl, h⟩
    · rw [show mem' x = mem x by simp [hmem', Function.update_of_ne hx]] at ha
      exact G.g6a x a ha
  · intro j' hj'
    rcases G.g6b j' hj' with ⟨x, hx⟩ | ⟨x, w', h1, h2, h3⟩
    · left
      by_cases hxx : x = x0
      · rw [hxx] at hx; refine ⟨x0, ?_⟩
        simp only [hmem', Function.update_self]
        rcases hcase with ⟨-, h2⟩ | hN
        · rw [h2]; exact hx
        · exact hN.2.2.2.2.1 hx
      · exact ⟨x, by simp [hmem', Function.update_of_ne hxx]; exact hx⟩
    · by_cases hjq : j' = q
      · subst hjq
        obtain ⟨hx, rfl⟩ := pendAt_write_self hj hq h1
        exact Or.inl ⟨x0, by simp [hmem']; exact h3⟩
      · right
        refine ⟨x, w', pendAt_update_loop.2 ⟨hjq, h1⟩, ?_, h3⟩
        rw [(hother j' hjq x w' h1).1]; exact h2
  · intro j' x w' h1 h2 a ha
    obtain ⟨hjq, h1⟩ := pendAt_update_loop.1 h1
    obtain ⟨hl, hld⟩ := hother j' hjq x w' h1
    rw [hl] at h2
    rcases hld h2 with hx | hld
    · rw [show mem' x = mem x by simp [hmem', Function.update_of_ne hx]]
      exact G.g6c j' x w' h1 h2 a ha
    · rw [hld]; exact G.g6c j' x w' h1 h2 a ha
  · intro j' L h
    have hjq : j' ≠ q := by rintro rfl; simp [hvpc'] at h
    rw [hvpc', Function.update_of_ne hjq] at h
    have := (G.ret j' L h).1 x0
    omega

end BezoutElection.Alg2
