import Papers.PODC2019.AbortableMutexAmortized.InvFas

/-!
# Preservation of the invariant: lines 1, 2, 7, 10
-/

namespace Podc.AbortableMutexAmortized

variable {n : ℕ} {s : State n} {Q : List (Fin n)} {a0 : Node n}

/-- The state after line 1, moving to line `c`. -/
@[simps]
def l1Upd (s : State n) (p : Fin n) (c : PC) : State n :=
  { s with
    node := Function.update s.node (s.mynode p) .nil
    pc := Function.update s.pc p c }

/-- Line 1 (both outcomes): `FAS(*mynode_p, nil)`, then line 3 (reclaim) or line 2. -/
theorem inv_l1 (hs : Struct s Q a0) (hl : Loc s a0) {p : Fin n} (hp : s.pc p = .l1) :
    Struct (l1Upd s p (if s.node (s.mynode p) = .addr (s.pred p) then .l3 else .l2)) Q a0 ∧
      Loc (l1Upd s p (if s.node (s.mynode p) = .addr (s.pred p) then .l3 else .l2)) a0 := by
  set c : PC := if s.node (s.mynode p) = .addr (s.pred p) then .l3 else .l2 with hc
  have hInQp : InQ s p ↔ c = .l3 := by
    simp only [InQ, hp, hc]; split_ifs with h <;> simp [h]
  have hnode : ∀ q, q ≠ p →
      Function.update s.node (s.mynode p) .nil (s.mynode q) = s.node (s.mynode q) := by
    intro q hq; rw [Function.update_of_ne (fun h => hq (hs.inj h))]
  have hc37 : c ≠ .l7 ∧ c ≠ .l4 ∧ c ≠ .l5 ∧ c ≠ .l8 ∧ c ≠ .l11 := by
    simp only [hc]; split_ifs <;> simp
  have hInQ : ∀ q, InQ (l1Upd s p c) q ↔ InQ s q := by
    intro q
    by_cases hq : q = p
    · subst hq; rw [hInQp]
      simp only [InQ, l1Upd_pc, l1Upd_node, l1Upd_mynode, l1Upd_pred, Function.update_self]
      simp only [hc]; split_ifs <;> simp
    · simp only [InQ, l1Upd_pc, l1Upd_node, l1Upd_mynode, l1Upd_pred, Function.update_of_ne hq,
        hnode q hq]
  have hpc : ∀ q, q ≠ p → (l1Upd s p c).pc q = s.pc q := by
    intro q hq; simp [Function.update_of_ne hq]
  have hnd : ∀ q, q ≠ p → (l1Upd s p c).node ((l1Upd s p c).mynode q) = s.node (s.mynode q) := by
    intro q hq; simp only [l1Upd_node, l1Upd_mynode]; exact hnode q hq
  have hna0 : (l1Upd s p c).node a0 = s.node a0 := by
    simp only [l1Upd_node]; rw [Function.update_of_ne (hs.a0_ne p).symm]
  refine ⟨⟨hs.ok, hs.last, fun q => (hs.mem q).trans (hInQ q).symm, hs.a0_ne⟩, ?_⟩
  constructor
  · intro q hq; by_cases e : q = p
    · subst e; simp
    · rw [hpc q e] at hq; rw [hnd q e]; exact hl.i6a q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq; exact absurd hq hc37.2.2.2.1
    · rw [hpc q e] at hq; rw [hnd q e]; exact hl.i6b q hq
  · intro q hq
    simp only [hInQ]
    by_cases e : q = p
    · subst e; simp
    · rw [hpc q e] at hq; rw [hnd q e]; exact hl.i7 q hq
  · intro h
    rw [hna0]
    apply hl.i9a; intro y hy h7'
    by_cases e : y = p
    · subst e; rw [hp] at h7'; simp at h7'
    · exact h y hy (by rw [hpc y e]; exact h7')
  · intro y hy h7'
    by_cases e : y = p
    · subst e; simp at h7'; exact absurd h7' hc37.1
    · rw [hpc y e] at h7'; rw [hna0]; exact hl.i9b y hy h7'
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq; exact absurd hq hc37.1
    · rw [hpc q e] at hq; exact hl.i10 q hq
  · intro y hy h4 hg'
    by_cases e : y = p
    · subst e; simp at h4; exact absurd h4 hc37.2.1
    · rw [hpc y e] at h4
      obtain ⟨q, hq, hv⟩ := hl.i11a y hy h4 hg'
      have e' : q ≠ p := fun h => by subst h; rw [hp] at hq; simp at hq
      exact ⟨q, by rw [hpc q e']; exact hq, hv⟩
  · intro x y hx hy h4 hg'
    rw [hInQ] at hx
    by_cases e : y = p
    · subst e; simp at h4; exact absurd h4 hc37.2.1
    · rw [hpc y e] at h4
      by_cases e' : x = p
      · subst e'
        exfalso
        rcases hl.i11b x y hx hy h4 hg' with h | ⟨-, h2, -⟩
        · rcases hx with hx | ⟨-, hx⟩
          · rw [hp] at hx; simp at hx
          · rw [hx] at h; simp at h
        · rw [hp] at h2; simp at h2
      · rw [hnd x e', hpc x e']
        exact hl.i11b x y hx hy h4 hg'
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
      rcases hq with hq | hq
      · exact absurd hq hc37.2.2.2.1
      · exact absurd hq hc37.2.2.2.2
    · rw [hpc q e] at hq; exact hl.i11c q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq; exact absurd hq hc37.2.2.1
    · rw [hpc q e] at hq; exact hl.i12 q hq
  · intro q hq h1; rw [hInQ] at hq
    by_cases e : q = p
    · subst e; simp at h1; simp only [hc] at h1; split_ifs at h1 <;> simp at h1
    · rw [hpc q e] at h1
      simp only [l1Upd_node, l1Upd_pred]
      by_cases hpq : s.pred q = s.mynode p
      · rw [hpq, Function.update_self]; simp
      · rw [Function.update_of_ne hpq]; exact hl.x1 q hq h1

/-- The state after line 2. -/
@[simps]
def l2Upd (s : State n) (p : Fin n) : State n :=
  { s with
    pred := Function.update s.pred p s.tail
    tail := s.mynode p
    pc := Function.update s.pc p .l3 }

/-- Line 2: `pred_p ← FAS(tail, mynode_p)`: `p` joins the end of the queue. -/
theorem inv_l2 (hs : Struct s Q a0) (hl : Loc s a0) {p : Fin n} (hp : s.pc p = .l2) :
    Struct (l2Upd s p) (Q ++ [p]) a0 ∧ Loc (l2Upd s p) a0 := by
  have hpQ : ¬ InQ s p := not_InQ_l2 hp
  have hpc : ∀ q, q ≠ p → (l2Upd s p).pc q = s.pc q := by
    intro q hq; simp [Function.update_of_ne hq]
  have hpr : ∀ q, q ≠ p → (l2Upd s p).pred q = s.pred q := by
    intro q hq; simp [Function.update_of_ne hq]
  have hInQ : ∀ q, InQ (l2Upd s p) q ↔ InQ s q ∨ q = p := by
    intro q
    by_cases hq : q = p
    · subst hq; simp [InQ]
    · simp only [InQ, l2Upd_node, l2Upd_mynode, hpc q hq, hpr q hq, hq, or_false]
  have hpL : p ∉ Q := fun h => hpQ ((hs.mem p).1 h)
  have hmy : (l2Upd s p).mynode = s.mynode := rfl
  have hstruct : Struct (l2Upd s p) (Q ++ [p]) a0 := by
    refine ⟨⟨?_, ?_, hs.inj, ?_⟩, ?_, ?_, hs.a0_ne⟩
    · rw [chain_append]
      refine ⟨?_, ?_⟩
      · rw [hmy, ← chain_congr (fun q hq => ⟨(hpr q (fun h => hpL (h ▸ hq))).symm,
          rfl⟩)]
        exact hs.ok.chain
      · rw [hmy, hs.last]; simp
    · exact List.nodup_append.2 ⟨hs.ok.nodup, by simp, by
        intro a ha b hb; simp at hb; subst hb; exact fun h => hpL (h ▸ ha)⟩
    · intro q _; exact hs.a0_ne q
    · rw [hmy, lastN_concat]; rfl
    · intro q; rw [hInQ, ← hs.mem]; simp
  refine ⟨hstruct, ?_⟩
  constructor
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · rw [hpc q e] at hq; exact hl.i6a q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · rw [hpc q e] at hq; exact hl.i6b q hq
  · intro q hq
    by_cases e : q = p
    · subst e; exact Or.inl (hl.i6a q hp)
    · rw [hpc q e] at hq
      rcases hl.i7 q hq with h | ⟨y, hy, hyq, h⟩
      · exact Or.inl h
      · have hyp : y ≠ p := fun h' => hpQ (h' ▸ hy)
        exact Or.inr ⟨y, (hInQ y).2 (Or.inl hy), by rw [hpr y hyp]; exact hyq, h⟩
  · intro h
    apply hl.i9a; intro y hy h7'
    by_cases e : y = p
    · subst e; rw [hp] at h7'; simp at h7'
    · exact h y (by rw [hpr y e]; exact hy) (by rw [hpc y e]; exact h7')
  · intro y hy h7'
    by_cases e : y = p
    · subst e; simp at h7'
    · rw [hpc y e] at h7'; rw [hpr y e] at hy; exact hl.i9b y hy h7'
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · rw [hpc q e] at hq; rw [hpr q e]; exact hl.i10 q hq
  · intro y hy h4 hg'
    by_cases e : y = p
    · subst e; simp at h4
    · rw [hpc y e] at h4; rw [hpr y e] at hy
      obtain ⟨q, hq, hv⟩ := hl.i11a y hy h4 hg'
      have e' : q ≠ p := fun h => by subst h; rw [hp] at hq; simp at hq
      exact ⟨q, by rw [hpc q e']; exact hq, hv⟩
  · intro x y hx hy h4 hg'
    rw [hInQ] at hx
    by_cases e : y = p
    · subst e; simp at h4
    · rw [hpc y e] at h4; rw [hpr y e] at hy
      have e' : x ≠ p := by
        rintro rfl
        rcases hs.pred_cases (InQ.of_pc h4 rfl) with h | ⟨x', hx', h⟩
        · exact hs.a0_ne x (hy.symm.trans h)
        · exact hpQ ((hs.inj (hy.symm.trans h)) ▸ hx')
      have hx' : InQ s x := hx.resolve_right e'
      rw [hpc x e', hpr x e']
      exact hl.i11b x y hx' hy h4 hg'
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · rw [hpc q e] at hq; exact hl.i11c q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · rw [hpc q e] at hq; exact hl.i12 q hq
  · intro q hq h1
    by_cases e : q = p
    · subst e; simp at h1
    · rw [hpc q e] at h1; rw [hpr q e]
      exact hl.x1 q ((hInQ q).1 hq |>.resolve_right e) h1

/-- The state after line 10. -/
@[simps]
def l10Upd (s : State n) (p : Fin n) : State n :=
  { s with
    node := Function.update s.node (s.mynode p) (.addr (s.pred p))
    v := Function.update s.v p (s.node (s.mynode p))
    pc := Function.update s.pc p (if s.node (s.mynode p) = .nil then .l1 else .l11) }

/-- Line 10: `v_p ← FAS(*mynode_p, pred_p)`: `p` marks its node aborted (stays in `Q`). -/
theorem inv_l10 (hs : Struct s Q a0) (hl : Loc s a0) {p : Fin n} (hp : s.pc p = .l10) :
    Struct (l10Upd s p) Q a0 ∧ Loc (l10Upd s p) a0 := by
  have hpQ : InQ s p := InQ.of_pc hp rfl
  set o := s.node (s.mynode p) with ho
  have ho' : o = .nil ∨ ∃ y, InQ s y ∧ s.pred y = s.mynode p ∧ o = .go y := hl.i7 p (by simp [hp])
  set c : PC := if o = .nil then .l1 else .l11 with hc
  have hcab : c = .l1 ∨ c = .l11 := by simp only [hc]; split_ifs <;> simp
  have hpc : ∀ q, q ≠ p → (l10Upd s p).pc q = s.pc q := by
    intro q hq; simp [Function.update_of_ne hq]
  have hpcp : (l10Upd s p).pc p = c := by simp [hc, ho]
  have hmy : (l10Upd s p).mynode = s.mynode := rfl
  have hpr : (l10Upd s p).pred = s.pred := rfl
  have hnd : ∀ q, q ≠ p → (l10Upd s p).node (s.mynode q) = s.node (s.mynode q) := by
    intro q hq; simp only [l10Upd_node]; rw [Function.update_of_ne (fun h => hq (hs.inj h))]
  have hndp : (l10Upd s p).node (s.mynode p) = .addr (s.pred p) := by simp
  have hna0 : (l10Upd s p).node a0 = s.node a0 := by
    simp only [l10Upd_node]; rw [Function.update_of_ne (hs.a0_ne p).symm]
  have hInQ : ∀ q, InQ (l10Upd s p) q ↔ InQ s q := by
    intro q
    by_cases hq : q = p
    · subst hq
      refine iff_of_true ?_ hpQ
      simp only [InQ, hpcp, hmy, hndp, hpr]
      rcases hcab with h | h <;> simp [h]
    · simp only [InQ, hpc q hq, hmy, hnd q hq, hpr]
  refine ⟨⟨hs.ok, hs.last, fun q => (hs.mem q).trans (hInQ q).symm, hs.a0_ne⟩, ?_⟩
  constructor
  · intro q hq; by_cases e : q = p
    · subst e; rw [hpcp] at hq; rcases hcab with h | h <;> simp [h] at hq
    · rw [hpc q e] at hq; rw [hmy, hnd q e]; exact hl.i6a q hq
  · intro q hq; by_cases e : q = p
    · subst e; rw [hpcp] at hq; rcases hcab with h | h <;> simp [h] at hq
    · rw [hpc q e] at hq; rw [hmy, hnd q e]; exact hl.i6b q hq
  · intro q hq
    simp only [hInQ, hmy, hpr]
    by_cases e : q = p
    · subst e; rw [hpcp] at hq; rcases hcab with h | h <;> simp [h] at hq
    · rw [hpc q e] at hq; rw [hnd q e]; exact hl.i7 q hq
  · intro h
    rw [hna0]
    apply hl.i9a; intro y hy h7'
    by_cases e : y = p
    · subst e; rw [hp] at h7'; simp at h7'
    · exact h y hy (by rw [hpc y e]; exact h7')
  · intro y hy h7'
    by_cases e : y = p
    · subst e; rw [hpcp] at h7'; rcases hcab with h | h <;> simp [h] at h7'
    · rw [hpc y e] at h7'; rw [hna0]; exact hl.i9b y hy h7'
  · intro q hq; by_cases e : q = p
    · subst e; rw [hpcp] at hq; rcases hcab with h | h <;> simp [h] at hq
    · rw [hpc q e] at hq; exact hl.i10 q hq
  · intro y hy h4 hg'
    by_cases e : y = p
    · subst e; rw [hpcp] at h4; rcases hcab with h | h <;> simp [h] at h4
    · rw [hpc y e] at h4
      obtain ⟨q, hq, hv⟩ := hl.i11a y hy h4 hg'
      have e' : q ≠ p := fun h => by subst h; rw [hp] at hq; simp at hq
      exact ⟨q, by rw [hpc q e']; exact hq, by simp [Function.update_of_ne e', hv]⟩
  · intro x y hx hy h4 hg'
    rw [hInQ] at hx
    rw [hmy] at hy ⊢
    by_cases e : y = p
    · subst e; rw [hpcp] at h4; rcases hcab with h | h <;> simp [h] at h4
    · rw [hpc y e] at h4
      by_cases e' : x = p
      · subst e'
        rcases hl.i11b x y hx hy h4 hg' with h | ⟨-, h2, -⟩
        · right
          have hc11 : c = .l11 := by simp only [hc]; rw [ho, h]; simp
          refine ⟨hndp, by rw [hpcp, hc11], ?_⟩
          simp [ho, h]
        · rw [hp] at h2; simp at h2
      · rw [hnd x e', hpc x e', hpr]
        simpa [Function.update_of_ne e'] using hl.i11b x y hx hy h4 hg'
  · intro q hq; by_cases e : q = p
    · subst e
      rcases ho' with h | ⟨y, -, -, h⟩
      · rw [hpcp] at hq; simp only [hc, h] at hq; simp at hq
      · exact ⟨y, by simp; exact h⟩
    · rw [hpc q e] at hq; simp [Function.update_of_ne e]; exact hl.i11c q hq
  · intro q hq; by_cases e : q = p
    · subst e; rw [hpcp] at hq; rcases hcab with h | h <;> simp [h] at hq
    · rw [hpc q e] at hq; exact hl.i12 q hq
  · intro q hq h1; rw [hInQ] at hq; rw [hpr]
    by_cases e : q = p
    · subst e
      rw [l10Upd_node, Function.update_of_ne (hs.pred_ne_mynode_self hpQ)]
      exact hl.x1 q hpQ (by simp [hp])
    · rw [hpc q e] at h1
      rw [l10Upd_node]
      by_cases hpq : s.pred q = s.mynode p
      · rw [hpq, Function.update_self]; simp
      · rw [Function.update_of_ne hpq]; exact hl.x1 q hq h1

/-- The state after line 7. -/
@[simps]
def l7Upd (s : State n) (p : Fin n) : State n :=
  { s with
    node := Function.update s.node (s.mynode p) .token
    v := Function.update s.v p (s.node (s.mynode p))
    mynode := Function.update s.mynode p (s.pred p)
    pc := Function.update s.pc p (if s.node (s.mynode p) = .nil then .l1 else .l8) }

/-- Line 7: `v_p ← FAS(*mynode_p, token)`, `mynode_p ← pred_p`: `p = q₁` leaves the queue, its
node becomes the new `a₀`. -/
theorem inv_l7 (hs : Struct s Q a0) (hl : Loc s a0) {p : Fin n} (hp : s.pc p = .l7) :
    ∃ R, Q = p :: R ∧ Struct (l7Upd s p) R (s.mynode p) ∧ Loc (l7Upd s p) (s.mynode p) := by
  have hpQ : InQ s p := InQ.of_pc hp rfl
  have hpa : s.pred p = a0 := hl.i10 p hp
  obtain ⟨R, hQ⟩ := hs.ok.head ((hs.mem p).2 hpQ) hpa
  refine ⟨R, hQ, ?_⟩
  have ha0 : s.node a0 = .nil ∨ s.node a0 = .go p := hl.i9b p hpa hp
  set o := s.node (s.mynode p) with ho
  have ho' : o = .nil ∨ ∃ y, InQ s y ∧ s.pred y = s.mynode p ∧ o = .go y := hl.i7 p (by simp [hp])
  set c : PC := if o = .nil then .l1 else .l8 with hc
  have hcab : c = .l1 ∨ c = .l8 := by simp only [hc]; split_ifs <;> simp
  have hpc : ∀ q, q ≠ p → (l7Upd s p).pc q = s.pc q := by
    intro q hq; simp [Function.update_of_ne hq]
  have hpcp : (l7Upd s p).pc p = c := by simp [hc, ho]
  have hmy : ∀ q, q ≠ p → (l7Upd s p).mynode q = s.mynode q := by
    intro q hq; simp [Function.update_of_ne hq]
  have hmyp : (l7Upd s p).mynode p = a0 := by simp [hpa]
  have hpr : (l7Upd s p).pred = s.pred := rfl
  have hnd : ∀ q, q ≠ p → (l7Upd s p).node (s.mynode q) = s.node (s.mynode q) := by
    intro q hq; simp only [l7Upd_node]; rw [Function.update_of_ne (fun h => hq (hs.inj h))]
  have hndp : (l7Upd s p).node (s.mynode p) = .token := by simp
  have hna0 : (l7Upd s p).node a0 = s.node a0 := by
    simp only [l7Upd_node]; rw [Function.update_of_ne (hs.a0_ne p).symm]
  have hInQ : ∀ q, InQ (l7Upd s p) q ↔ InQ s q ∧ q ≠ p := by
    intro q
    by_cases hq : q = p
    · subst hq
      simp only [ne_eq, not_true_eq_false, and_false, iff_false]
      simp only [InQ, hpcp, hmyp, hna0, hpr]
      rcases hcab with h | h <;> rcases ha0 with h' | h' <;> simp [h, h']
    · simp only [InQ, hpc q hq, hmy q hq, hnd q hq, hpr, ne_eq, hq, not_false_eq_true, and_true]
  have hnd' := hs.ok.nodup
  rw [hQ] at hnd'
  have hpR : p ∉ R := (List.nodup_cons.1 hnd').1
  have hstruct : Struct (l7Upd s p) R (s.mynode p) := by
    refine ⟨⟨?_, (List.nodup_cons.1 hnd').2, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hpr, ← chain_congr (fun q hq => ⟨rfl, (hmy q (fun h => hpR (h ▸ hq))).symm⟩)]
      have := hs.ok.chain; rw [hQ] at this; exact this.2
    · intro a b hab
      by_cases ha : a = p <;> by_cases hb : b = p
      · rw [ha, hb]
      · subst ha; rw [hmyp, hmy b hb] at hab; exact absurd hab.symm (hs.a0_ne b)
      · subst hb; rw [hmyp, hmy a ha] at hab; exact absurd hab (hs.a0_ne a)
      · rw [hmy a ha, hmy b hb] at hab; exact hs.inj hab
    · intro x hx; have hxp : x ≠ p := fun h => hpR (h ▸ hx)
      rw [hmy x hxp]; exact fun h => hxp (hs.inj h)
    · rw [← lastN_congr (fun q hq => (hmy q (fun h => hpR (h ▸ hq))).symm)]
      have := hs.last; rw [hQ, lastN_cons] at this; exact this
    · intro q
      rw [hInQ, ← hs.mem, hQ]
      by_cases hqp : q = p
      · subst hqp; simp [hpR]
      · simp [hqp]
    · intro q
      by_cases hqp : q = p
      · subst hqp; rw [hmyp]; exact (hs.a0_ne q).symm
      · rw [hmy q hqp]; exact fun h => hqp (hs.inj h)
  refine ⟨hstruct, ?_⟩
  constructor
  · intro q hq; by_cases e : q = p
    · subst e; rw [hpcp] at hq; rcases hcab with h | h <;> simp [h] at hq
    · rw [hpc q e] at hq; rw [hmy q e, hnd q e]; exact hl.i6a q hq
  · intro q hq; by_cases e : q = p
    · subst e; rw [hmyp, hna0]; exact ha0
    · rw [hpc q e] at hq; rw [hmy q e, hnd q e]; exact hl.i6b q hq
  · intro q hq
    by_cases e : q = p
    · subst e; rw [hpcp] at hq; rcases hcab with h | h <;> simp [h] at hq
    · rw [hpc q e] at hq; rw [hmy q e, hnd q e]
      rcases hl.i7 q hq with h | ⟨y, hy, hyq, h⟩
      · exact Or.inl h
      · have hyp : y ≠ p := fun h' => by
          subst h'; rw [hpa] at hyq; exact hs.a0_ne q hyq.symm
        exact Or.inr ⟨y, (hInQ y).2 ⟨hy, hyp⟩, hyq, h⟩
  · intro _; exact hndp
  · intro y hy h7'
    exfalso
    by_cases e : y = p
    · subst e; rw [hpcp] at h7'; rcases hcab with h | h <;> simp [h] at h7'
    · rw [hpc y e] at h7'; rw [hpr] at hy
      exact hs.a0_ne p (hy.symm.trans (hl.i10 y h7'))
  · intro q hq
    exfalso
    by_cases e : q = p
    · subst e; rw [hpcp] at hq; rcases hcab with h | h <;> simp [h] at hq
    · rw [hpc q e] at hq
      exact e (hs.pred_inj (InQ.of_pc hq rfl) hpQ ((hl.i10 q hq).trans hpa.symm))
  · intro y hy h4 hg'
    rw [hpr] at hy
    have e : y ≠ p := fun h => by subst h; rw [hpa] at hy; exact hs.a0_ne y hy.symm
    rw [hpc y e] at h4
    rcases hl.i11b p y hpQ hy h4 hg' with h | ⟨-, h2, -⟩
    · refine ⟨p, ?_, by simp; exact h⟩
      rw [hpcp]; simp only [hc, ho, h]; simp
    · rw [hp] at h2; simp at h2
  · intro x y hx hy h4 hg'
    rw [hInQ] at hx
    rw [hpr] at hy
    rw [hmy x hx.2] at hy ⊢
    have e : y ≠ p := fun h => by
      subst h; rw [hpa] at hy; exact hs.a0_ne x hy.symm
    rw [hpc y e] at h4
    rw [hnd x hx.2, hpc x hx.2, hpr]
    simpa [Function.update_of_ne hx.2] using hl.i11b x y hx.1 hy h4 hg'
  · intro q hq; by_cases e : q = p
    · subst e
      rcases ho' with h | ⟨y, -, -, h⟩
      · rw [hpcp] at hq; simp only [hc, h] at hq; simp at hq
      · exact ⟨y, by simp; exact h⟩
    · rw [hpc q e] at hq; simp [Function.update_of_ne e]; exact hl.i11c q hq
  · intro q hq; by_cases e : q = p
    · subst e; rw [hpcp] at hq; rcases hcab with h | h <;> simp [h] at hq
    · rw [hpc q e] at hq; exact hl.i12 q hq
  · intro q hq h1; rw [hInQ] at hq; rw [hpr]
    rw [hpc q hq.2] at h1
    rw [l7Upd_node]
    by_cases hpq : s.pred q = s.mynode p
    · rw [hpq, Function.update_self]; simp
    · rw [Function.update_of_ne hpq]; exact hl.x1 q hq.1 h1

end Podc.AbortableMutexAmortized
