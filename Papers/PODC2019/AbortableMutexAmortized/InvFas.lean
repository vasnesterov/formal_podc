import Papers.PODC2019.AbortableMutexAmortized.InvBasic

/-!
# Preservation of the invariant: lines 3, 6, 9 (a FAS on the predecessor node)

Lines 3/6 write `&go_p`, line 9 writes `nil` into `*pred_p`. Three cases (paper, Appendix A):
`p = q₁` (the predecessor node is `a₀`, holding `token`); the predecessor `q_{i-1}` is active
(its node holds `nil` or `&go_p`); the predecessor is aborted (its node holds `pred_{q_{i-1}}`:
splice).
-/

namespace Podc.AbortableMutexAmortized

variable {n : ℕ} {s : State n} {Q : List (Fin n)} {a0 : Node n}

/-- A FAS on `*pred_p` writing `w`, followed by the local actions, ending at line `c`. -/
def fasUpd (s : State n) (p : Fin n) (w : Val n) (c : PC) : State n :=
  { s with
    node := Function.update s.node (s.pred p) w
    v := Function.update s.v p (s.node (s.pred p))
    pred := Function.update s.pred p (newPred (s.node (s.pred p)) (s.pred p))
    pc := Function.update s.pc p c }

@[simp] theorem fasUpd_mynode (s : State n) (p : Fin n) (w : Val n) (c : PC) :
    (fasUpd s p w c).mynode = s.mynode := rfl
@[simp] theorem fasUpd_tail (s : State n) (p : Fin n) (w : Val n) (c : PC) :
    (fasUpd s p w c).tail = s.tail := rfl
@[simp] theorem fasUpd_go (s : State n) (p : Fin n) (w : Val n) (c : PC) :
    (fasUpd s p w c).go = s.go := rfl
@[simp] theorem fasUpd_pc (s : State n) (p : Fin n) (w : Val n) (c : PC) :
    (fasUpd s p w c).pc = Function.update s.pc p c := rfl
@[simp] theorem fasUpd_node (s : State n) (p : Fin n) (w : Val n) (c : PC) :
    (fasUpd s p w c).node = Function.update s.node (s.pred p) w := rfl
@[simp] theorem fasUpd_v (s : State n) (p : Fin n) (w : Val n) (c : PC) :
    (fasUpd s p w c).v = Function.update s.v p (s.node (s.pred p)) := rfl
@[simp] theorem fasUpd_pred (s : State n) (p : Fin n) (w : Val n) (c : PC) :
    (fasUpd s p w c).pred =
      Function.update s.pred p (newPred (s.node (s.pred p)) (s.pred p)) := rfl

theorem fasPred_eq (s : State n) (p : Fin n) :
    fasPred s p = fasUpd s p (.go p) (loopPC (s.node (s.pred p))) := rfl

theorem line9_eq (s : State n) (p : Fin n) :
    line9 s p = fasUpd s p .nil (if s.node (s.pred p) = .token then .l7 else .l10) := rfl

/-- If the head is not at line 7, `*a₀ = token`. -/
theorem Loc.token_of (hs : Struct s Q a0) (hl : Loc s a0) {p : Fin n} (hp : InQ s p)
    (hpa : s.pred p = a0) (h7 : s.pc p ≠ .l7) : s.node a0 = .token := by
  apply hl.i9a
  intro y hy h
  have hyQ : InQ s y := InQ.of_pc h rfl
  have := hs.pred_inj hyQ hp (hy.trans hpa.symm)
  subst this; exact h7 h

/-- Case 1: `p` is the head; it reads `token` and enters the CS. -/
theorem inv_fas_head (hs : Struct s Q a0) (hl : Loc s a0) {p : Fin n}
    (hp : (s.pc p).act = true) (h7 : s.pc p ≠ .l7) (hpa : s.pred p = a0)
    {w : Val n} (hw : w = .go p ∨ w = .nil) :
    Struct (fasUpd s p w .l7) Q a0 ∧ Loc (fasUpd s p w .l7) a0 := by
  have hpQ : InQ s p := Or.inl hp
  have htok : s.node a0 = .token := hl.token_of hs hpQ hpa h7
  have hpred : (fasUpd s p w .l7).pred = s.pred := by
    simp [hpa, htok, newPred]
  have hnode : ∀ q, (fasUpd s p w .l7).node (s.mynode q) = s.node (s.mynode q) := by
    intro q; simp [hpa, Function.update_of_ne (hs.a0_ne q)]
  have hInQ : ∀ q, InQ (fasUpd s p w .l7) q ↔ InQ s q := by
    intro q
    by_cases hq : q = p
    · subst hq; simp [InQ, fasUpd, hp]
    · simp only [InQ, fasUpd_mynode]
      rw [hnode, hpred]
      simp [Function.update_of_ne hq]
  refine ⟨⟨by rw [hpred]; exact hs.ok, hs.last, fun q => (hs.mem q).trans (hInQ q).symm,
    hs.a0_ne⟩, ?_⟩
  constructor
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq
      rw [fasUpd_mynode, hnode]; exact hl.i6a q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq
      rw [fasUpd_mynode, hnode]; exact hl.i6b q hq
  · intro q hq
    simp only [hInQ, hpred]
    rw [fasUpd_mynode, hnode]
    by_cases e : q = p
    · subst e; exact hl.i7 q hp
    · simp [Function.update_of_ne e] at hq; exact hl.i7 q hq
  · intro h; exfalso; exact h p (by rw [hpred, hpa]) (by simp)
  · intro y hy h7'
    rw [hpred] at hy
    have hyQ : InQ s y := by
      by_cases e : y = p
      · subst e; exact hpQ
      · simp [Function.update_of_ne e] at h7'; exact InQ.of_pc h7' rfl
    have := hs.pred_inj hyQ hpQ (hy.trans hpa.symm); subst this
    rcases hw with hw | hw <;> simp [hpa, hw]
  · intro q hq; rw [hpred]; by_cases e : q = p
    · subst e; exact hpa
    · simp [Function.update_of_ne e] at hq; exact hl.i10 q hq
  · intro y hy h4 hg'
    rw [hpred] at hy
    by_cases e : y = p
    · subst e; simp at h4
    · simp [Function.update_of_ne e] at h4 hg'
      obtain ⟨q, hq, hv⟩ := hl.i11a y hy h4 hg'
      by_cases e' : q = p
      · subst e'; rw [hq] at hp; simp at hp
      · exact ⟨q, by simpa [fasUpd, Function.update_of_ne e'] using hq,
          by simpa [fasUpd, Function.update_of_ne e'] using hv⟩
  · intro x y hx hy h4 hg'
    rw [hInQ] at hx; rw [hpred] at hy
    by_cases e : y = p
    · subst e; simp at h4
    · simp [Function.update_of_ne e] at h4 hg'
      rw [fasUpd_mynode, hnode]
      rcases hl.i11b x y hx hy h4 hg' with h | ⟨h1, h2, h3⟩
      · exact Or.inl h
      · by_cases e' : x = p
        · subst e'; rw [h2] at hp; simp at hp
        · right
          simp [Function.update_of_ne e', h1, h2, h3]
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq ⊢; exact hl.i11c q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq
    · simp [Function.update_of_ne e] at hq ⊢; exact hl.i12 q hq
  · intro q hq h1; rw [hInQ] at hq; rw [hpred]
    by_cases e : q = p
    · subst e; simp at h1
    · simp [Function.update_of_ne e] at h1
      have hne : s.pred q ≠ a0 := fun h => e (hs.pred_inj hq hpQ (h.trans hpa.symm))
      simp only [fasUpd_node]; rw [hpa, Function.update_of_ne hne]
      exact hl.x1 q hq h1

/-- Case 2: the predecessor `x` is active; its node holds `nil` or `&go_p`. -/
theorem inv_fas_act (hs : Struct s Q a0) (hl : Loc s a0) {p x : Fin n}
    (hp : (s.pc p).act = true) (hpx : s.pred p = s.mynode x) (hx : (s.pc x).act = true)
    {w : Val n} {c : PC} (hc : (c = .l4 ∧ w = .go p) ∨ (c = .l10 ∧ w = .nil)) :
    Struct (fasUpd s p w c) Q a0 ∧ Loc (fasUpd s p w c) a0 := by
  have hpQ : InQ s p := Or.inl hp
  have hxQ : InQ s x := Or.inl hx
  have hxp : x ≠ p := fun h => hs.pred_ne_mynode_self hpQ (h ▸ hpx)
  have ho : s.node (s.mynode x) = .nil ∨ s.node (s.mynode x) = .go p := by
    rcases hl.i7 x hx with h | ⟨y, hy, hyx, h⟩
    · exact Or.inl h
    · have := hs.pred_inj hy hpQ (hyx.trans hpx.symm); subst this; exact Or.inr h
  have hpred : (fasUpd s p w c).pred = s.pred := by
    rcases ho with h | h <;> simp [hpx, h, newPred]
  have hnode : ∀ q, q ≠ x → (fasUpd s p w c).node (s.mynode q) = s.node (s.mynode q) := by
    intro q hq; simp [hpx, Function.update_of_ne (fun h => hq (hs.inj h))]
  have hnx : (fasUpd s p w c).node (s.mynode x) = w := by simp [hpx]
  have hca : c.act = true := by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  have hc7 : c ≠ .l7 := by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hc5 : c ≠ .l5 := by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hInQ : ∀ q, InQ (fasUpd s p w c) q ↔ InQ s q := by
    intro q
    by_cases hq : q = p
    · subst hq; simp [InQ, hp, hca]
    · by_cases hqx : q = x
      · subst hqx; simp [InQ, hx, Function.update_of_ne hq]
      · simp only [InQ, fasUpd_mynode]
        rw [hnode q hqx, hpred]
        simp [Function.update_of_ne hq]
  refine ⟨⟨by rw [hpred]; exact hs.ok, hs.last, fun q => (hs.mem q).trans (hInQ q).symm,
    hs.a0_ne⟩, ?_⟩
  constructor
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq; exact absurd hq (by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)
    · simp [Function.update_of_ne e] at hq
      have hqx : q ≠ x := fun h => by subst h; rw [hq] at hx; simp at hx
      rw [fasUpd_mynode, hnode q hqx]; exact hl.i6a q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq; exact absurd hq (by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)
    · simp [Function.update_of_ne e] at hq
      have hqx : q ≠ x := fun h => by subst h; rw [hq] at hx; simp at hx
      rw [fasUpd_mynode, hnode q hqx]; exact hl.i6b q hq
  · intro q hq
    simp only [hInQ, hpred, fasUpd_mynode]
    by_cases hqx : q = x
    · subst hqx; rw [hnx]
      rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr ⟨p, hpQ, hpx, rfl⟩
      · exact Or.inl rfl
    rw [hnode q hqx]
    by_cases e : q = p
    · subst e; exact hl.i7 q hp
    · simp [Function.update_of_ne e] at hq; exact hl.i7 q hq
  · intro h
    rw [fasUpd_node, Function.update_of_ne (by rw [hpx]; exact (hs.a0_ne x).symm)]
    apply hl.i9a; intro y hy h7'
    by_cases e : y = p
    · subst e; exact hs.a0_ne x (hpx ▸ hy)
    · exact h y (by rw [hpred]; exact hy) (by simp [Function.update_of_ne e, h7'])
  · intro y hy h7'
    rw [hpred] at hy
    by_cases e : y = p
    · subst e; simp at h7'; exact absurd h7' hc7
    · simp [Function.update_of_ne e] at h7'
      rw [fasUpd_node, Function.update_of_ne (by rw [hpx]; exact (hs.a0_ne x).symm)]
      rcases hl.i9b y hy h7' with h | h
      · exact Or.inl h
      · exact Or.inr h
  · intro q hq; rw [hpred]; by_cases e : q = p
    · subst e; simp at hq; exact absurd hq hc7
    · simp [Function.update_of_ne e] at hq; exact hl.i10 q hq
  · intro y hy h4 hg'
    rw [hpred] at hy
    by_cases e : y = p
    · subst e; exact absurd (hpx ▸ hy) (hs.a0_ne x)
    · simp [Function.update_of_ne e] at h4 hg'
      obtain ⟨q, hq, hv⟩ := hl.i11a y hy h4 hg'
      by_cases e' : q = p
      · subst e'; rw [hq] at hp; simp at hp
      · exact ⟨q, by simpa [Function.update_of_ne e'] using hq,
          by simpa [Function.update_of_ne e'] using hv⟩
  · intro x' y hx' hy h4 hg'
    rw [hInQ] at hx'; rw [hpred] at hy
    simp only [fasUpd_mynode] at hy ⊢
    by_cases e : y = p
    · subst e
      have := hs.inj (hpx.symm.trans hy); subst this
      rw [hnx]
      rcases hc with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · exact Or.inl rfl
      · simp at h4
    · simp [Function.update_of_ne e] at h4 hg'
      have hx'x : x' ≠ x := fun h => by
        subst h; exact e (hs.pred_inj (InQ.of_pc h4 rfl) hpQ (hy.trans hpx.symm))
      rw [hnode x' hx'x]
      rcases hl.i11b x' y hx' hy h4 hg' with h | ⟨h1, h2, h3⟩
      · exact Or.inl h
      · by_cases e' : x' = p
        · subst e'; rw [h2] at hp; simp at hp
        · right
          simp [Function.update_of_ne e', h1, h2, h3]
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq; rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp at hq
    · simp [Function.update_of_ne e] at hq ⊢; exact hl.i11c q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq; exact absurd hq hc5
    · simp [Function.update_of_ne e] at hq ⊢; exact hl.i12 q hq
  · intro q hq h1; rw [hInQ] at hq; rw [hpred]
    by_cases e : q = p
    · subst e
      rcases hc with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · simp at h1
      · rw [fasUpd_node, hpx, Function.update_self]; simp
    · simp [Function.update_of_ne e] at h1
      have hne : s.pred q ≠ s.pred p := fun h => e (hs.pred_inj hq hpQ h)
      simp only [fasUpd_node]; rw [Function.update_of_ne hne]
      exact hl.x1 q hq h1

theorem InQ.ab_cases {q : Fin n} (h : InQ s q) (hq : (s.pc q).act = false) :
    (s.pc q = .l1 ∨ s.pc q = .l11) ∧ s.node (s.mynode q) = .addr (s.pred q) := by
  rcases h with h | ⟨h1, h2⟩
  · simp_all
  · refine ⟨?_, h2⟩
    revert h1; cases s.pc q <;> simp

/-- Case 3: the predecessor `x` is aborted (line 1 or 11, node marked); `p` splices it out. -/
theorem inv_fas_splice (hs : Struct s Q a0) (hl : Loc s a0) {p x : Fin n}
    (hp : (s.pc p).act = true) (hpx : s.pred p = s.mynode x) (hxQ : InQ s x)
    (hx : (s.pc x).act = false)
    {w : Val n} {c : PC} (hc : (c = .l6 ∧ w = .go p) ∨ (c = .l10 ∧ w = .nil)) :
    ∃ L R, Q = L ++ x :: p :: R ∧
      Struct (fasUpd s p w c) (L ++ p :: R) a0 ∧ Loc (fasUpd s p w c) a0 := by
  have hpQ : InQ s p := Or.inl hp
  obtain ⟨hxpc, hxn⟩ := InQ.ab_cases hxQ hx
  have hxp : x ≠ p := fun h => by subst h; rw [hx] at hp; simp at hp
  obtain ⟨L, R, hQ⟩ := hs.ok.adj ((hs.mem x).2 hxQ) ((hs.mem p).2 hpQ) hpx
  refine ⟨L, R, hQ, ?_⟩
  have hpred : (fasUpd s p w c).pred = Function.update s.pred p (s.pred x) := by
    simp [hpx, hxn, newPred]
  have hnode : ∀ q, q ≠ x → (fasUpd s p w c).node (s.mynode q) = s.node (s.mynode q) := by
    intro q hq; simp [hpx, Function.update_of_ne (fun h => hq (hs.inj h))]
  have hnx : (fasUpd s p w c).node (s.mynode x) = w := by simp [hpx]
  have hwa : ∀ a, w ≠ .addr a := by rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hca : c.act = true := by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  have hc7 : c ≠ .l7 := by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hc5 : c ≠ .l5 := by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hc4 : c ≠ .l4 := by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hpredq : ∀ q, q ≠ p → (fasUpd s p w c).pred q = s.pred q := by
    intro q hq; rw [hpred, Function.update_of_ne hq]
  have hpcq : ∀ q, q ≠ p → (fasUpd s p w c).pc q = s.pc q := by
    intro q hq; simp [Function.update_of_ne hq]
  have hInQ : ∀ q, InQ (fasUpd s p w c) q ↔ InQ s q ∧ q ≠ x := by
    intro q
    by_cases hq : q = p
    · subst hq; simp [InQ, hp, hca, hxp.symm]
    · by_cases hqx : q = x
      · subst hqx
        simp only [InQ, fasUpd_mynode, hnx, hpcq q hq, hx]
        simp [hwa]
      · simp only [InQ, fasUpd_mynode]
        rw [hnode q hqx, hpredq q hq, hpcq q hq]
        simp [hqx]
  -- structure
  have hnd := hs.ok.nodup
  rw [hQ] at hnd
  have hpL : p ∉ L := fun h => by
    have := (List.nodup_append.1 hnd).2.2 p h p (by simp); exact this rfl
  have hpR : p ∉ R := by
    have := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).2
    exact (List.nodup_cons.1 this).1
  have hch := hs.ok.chain
  rw [hQ, chain_append] at hch
  obtain ⟨hchL, hchx, hchp, hchR⟩ := hch
  have hstruct : Struct (fasUpd s p w c) (L ++ p :: R) a0 := by
    refine ⟨⟨?_, ?_, hs.inj, fun q _ => hs.a0_ne q⟩, ?_, ?_, hs.a0_ne⟩
    · rw [chain_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [fasUpd_mynode, ← chain_congr (fun q hq => ⟨(hpredq q (fun h => hpL (h ▸ hq))).symm,
          rfl⟩)]
        exact hchL
      · rw [hpred, Function.update_self, fasUpd_mynode]; exact hchx
      · rw [fasUpd_mynode, ← chain_congr (fun q hq => ⟨(hpredq q (fun h => hpR (h ▸ hq))).symm,
          rfl⟩)]
        exact hchR
    · have h1 : (L ++ p :: R).Sublist (L ++ x :: p :: R) :=
        List.Sublist.append_left (List.sublist_cons_self _ _) L
      exact h1.nodup hnd
    · rw [fasUpd_mynode, fasUpd_tail, ← hs.last, hQ, lastN_append, lastN_append]; rfl
    · intro q
      rw [hInQ, ← hs.mem, hQ]
      by_cases hqx : q = x
      · subst hqx
        simp only [ne_eq, not_true_eq_false, and_false, iff_false]
        intro h
        have hxL : q ∉ L := fun h' => by
          have := (List.nodup_append.1 hnd).2.2 q h' q (by simp); exact this rfl
        have hxR : q ∉ R := by
          have := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
          exact fun h' => this (by simp [h'])
        simp at h; rcases h with h | h | h
        · exact hxL h
        · exact hxp h
        · exact hxR h
      · simp [hqx]
  refine ⟨hstruct, ?_⟩
  -- the predecessor of `x` holds neither `&go_x` (by `x1`) nor, therefore, anything pointing to `x`
  have hx1 : s.node (s.pred x) ≠ .go x := hl.x1 x hxQ (by rcases hxpc with h | h <;> simp [h])
  constructor
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq; exact absurd hq (by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)
    · rw [hpcq q e] at hq
      have hqx : q ≠ x := fun h => by subst h; rcases hxpc with h | h <;> rw [h] at hq <;> simp at hq
      rw [fasUpd_mynode, hnode q hqx]; exact hl.i6a q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq; exact absurd hq (by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)
    · rw [hpcq q e] at hq
      have hqx : q ≠ x := fun h => by subst h; rcases hxpc with h | h <;> rw [h] at hq <;> simp at hq
      rw [fasUpd_mynode, hnode q hqx]; exact hl.i6b q hq
  · intro q hq
    have hqact : (s.pc q).act = true := by
      by_cases e : q = p
      · subst e; exact hp
      · rwa [hpcq q e] at hq
    have hqx : q ≠ x := fun h => by subst h; rw [hx] at hqact; simp at hqact
    rw [fasUpd_mynode, hnode q hqx]
    rcases hl.i7 q hqact with h | ⟨y, hy, hyq, h⟩
    · exact Or.inl h
    · right
      have hyx : y ≠ x := fun e => by subst e; exact hx1 (hyq ▸ h)
      have hyp : y ≠ p := fun e => by
        subst e
        by_cases hqp : q = y
        · subst hqp; exact hs.pred_ne_mynode_self hpQ hyq
        · exact hqx (hs.inj (hpx.symm.trans hyq)).symm
      exact ⟨y, (hInQ y).2 ⟨hy, hyx⟩, by rw [hpredq y hyp]; exact hyq, h⟩
  · intro h
    rw [fasUpd_node, Function.update_of_ne (by rw [hpx]; exact (hs.a0_ne x).symm)]
    apply hl.i9a; intro y hy h7'
    have hyp : y ≠ p := fun e => by subst e; exact hs.a0_ne x (hpx ▸ hy)
    have hyx : y ≠ x := fun e => by subst e; rcases hxpc with h | h <;> rw [h] at h7' <;> simp at h7'
    exact h y (by rw [hpredq y hyp]; exact hy) (by rw [hpcq y hyp]; exact h7')
  · intro y hy h7'
    have hyp : y ≠ p := fun e => by subst e; simp at h7'; exact hc7 h7'
    rw [hpredq y hyp] at hy; rw [hpcq y hyp] at h7'
    rw [fasUpd_node, Function.update_of_ne (by rw [hpx]; exact (hs.a0_ne x).symm)]
    exact hl.i9b y hy h7'
  · intro q hq
    have hqp : q ≠ p := fun e => by subst e; simp at hq; exact hc7 hq
    rw [hpredq q hqp]; rw [hpcq q hqp] at hq; exact hl.i10 q hq
  · intro y hy h4 hg'
    have hyp : y ≠ p := fun e => by subst e; simp at h4; exact hc4 h4
    rw [hpredq y hyp] at hy; rw [hpcq y hyp] at h4
    simp only [fasUpd_go] at hg'
    obtain ⟨q, hq, hv⟩ := hl.i11a y hy h4 hg'
    have hqp : q ≠ p := fun e => by subst e; rw [hq] at hp; simp at hp
    exact ⟨q, by rw [hpcq q hqp]; exact hq, by simpa [Function.update_of_ne hqp] using hv⟩
  · intro x' y hx' hy h4 hg'
    rw [hInQ] at hx'
    have hyp : y ≠ p := fun e => by subst e; simp at h4; exact hc4 h4
    rw [hpredq y hyp] at hy; rw [hpcq y hyp] at h4
    simp only [fasUpd_go, fasUpd_mynode] at hg' hy ⊢
    rw [hnode x' hx'.2]
    rcases hl.i11b x' y hx'.1 hy h4 hg' with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · have e' : x' ≠ p := fun e => by subst e; rw [h2] at hp; simp at hp
      right
      simp [Function.update_of_ne e', h1, h2, h3, hpredq x' e']
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq; rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp at hq
    · rw [hpcq q e] at hq; simp [Function.update_of_ne e]; exact hl.i11c q hq
  · intro q hq; by_cases e : q = p
    · subst e; simp at hq; exact absurd hq hc5
    · rw [hpcq q e] at hq; simp; exact hl.i12 q hq
  · intro q hq h1
    rw [hInQ] at hq
    by_cases e : q = p
    · subst e
      rcases hc with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · simp at h1
      · -- `pred'_p = pred_x`; its node is `token` (if `x` was the head), `nil`/`&go_x` or
        -- an address: never `&go_p`.
        rw [hpred, Function.update_self, fasUpd_node,
          Function.update_of_ne (by rw [hpx]; exact hs.pred_ne_mynode_self hxQ)]
        rcases hs.pred_cases hxQ with ha | ⟨w', hw', hww⟩
        · rw [ha, hl.token_of hs hxQ ha (by rcases hxpc with h | h <;> simp [h])]; simp
        · rw [hww]
          by_cases hwa : (s.pc w').act = true
          · rcases hl.i7 w' hwa with h | ⟨y, hy, hyw, h⟩
            · rw [h]; simp
            · rw [h]
              have := hs.pred_inj hy hxQ (hyw.trans hww.symm); subst this
              simpa using hxp
          · rw [(InQ.ab_cases hw' (by simpa using hwa)).2]; simp
    · rw [hpcq q e] at h1
      have hne : s.pred q ≠ s.pred p := fun h => e (hs.pred_inj hq.1 hpQ h)
      rw [hpredq q e, fasUpd_node, Function.update_of_ne hne]
      exact hl.x1 q hq.1 h1

end Podc.AbortableMutexAmortized
