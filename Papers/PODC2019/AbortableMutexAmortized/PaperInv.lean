import Papers.PODC2019.AbortableMutexAmortized.Invariant

/-!
# Theorem 4.1 and Corollary 4.1.1 in the paper's form

`PaperInv s A Q` is the paper's invariant `I = I1 ∧ … ∧ I12` (Figure 1) verbatim, for the node queue
`A = [a₀, …, a_k]` and the process queue `Q = [q₁, …, q_k]`. Lists are 0-based: `a_i = A[i]`,
`q_{i+1} = Q[i]`. Two typos of Figure 1 are corrected: in `I7` the paper writes `*mynode_p` for
`*mynode_{q_i}`, and in `I9` `go_{q₁}` for `&go_{q₁}`.
-/

namespace Podc.AbortableMutexAmortized

variable {n : ℕ}

/-- Lines `{3,4,5,6,7,9,10}` of `I7`. -/
def PC.inI7 (c : PC) : Prop := c ∈ [.l3, .l4, .l5, .l6, .l7, .l9, .l10]

instance : DecidablePred PC.inI7 := fun c => by unfold PC.inI7; infer_instance

/-- The paper's invariant `I` (Figure 1), for `A = [a₀,…,a_k]`, `Q = [q₁,…,q_k]`. -/
structure PaperInv (s : State n) (A : List (Node n)) (Q : List (Fin n)) : Prop where
  /-- `A` has `k + 1` entries, `Q` has `k`. -/
  len : A.length = Q.length + 1
  /-- the nodes `a₀, …, a_k` are distinct -/
  distA : A.Nodup
  /-- the processes `q₁, …, q_k` are distinct -/
  distQ : Q.Nodup
  /-- `I1`: `tail = a_k` -/
  I1 : A.getLast? = some s.tail
  /-- `I2`: `mynode_{q_i} = a_i` -/
  I2 : ∀ (i : ℕ) p, Q[i]? = some p → A[i + 1]? = some (s.mynode p)
  /-- `I3`: `pred_{q_i} = a_{i-1}` -/
  I3 : ∀ (i : ℕ) p, Q[i]? = some p → A[i]? = some (s.pred p)
  /-- `I4`: `N = {a₀} ∪ {mynode_p | p ∈ P}` (`N` = all `n + 1` nodes) -/
  I4 : ∀ x : Node n, A.head? = some x ∨ ∃ p, s.mynode p = x
  /-- `I5`: `pred_p ∈ N` -/
  I5 : ∀ p, A.head? = some (s.pred p) ∨ ∃ r, s.mynode r = s.pred p
  /-- `I6` -/
  I6 : ∀ p, ((s.pc p = .l2 ∨ s.pc p = .l8) → p ∉ Q) ∧
    (s.pc p = .l2 → s.node (s.mynode p) = .nil) ∧
    (s.pc p = .l8 → s.node (s.mynode p) = .nil ∨ s.node (s.mynode p) = .go p)
  /-- `I7` for `q_k` -/
  I7last : ∀ p, Q.getLast? = some p →
    ((s.pc p).inI7 → s.node (s.mynode p) = .nil) ∧
    (s.pc p ∈ [.l1, .l11] → s.node (s.mynode p) = .addr (s.pred p))
  /-- `I7` for `q_i`, `i < k` (successor `q_{i+1}`) -/
  I7mid : ∀ (i : ℕ) x y, Q[i]? = some x → Q[i + 1]? = some y →
    ((s.pc x).inI7 → s.node (s.mynode x) = .nil ∨ s.node (s.mynode x) = .go y) ∧
    (s.pc x ∈ [.l1, .l11] → s.node (s.mynode x) = .addr (s.pred x))
  /-- `I8` -/
  I8 : ∀ p, p ∉ Q → s.pc p ∈ [.l1, .l2, .l8, .l11] ∧ s.node (s.mynode p) ≠ .addr (s.pred p)
  /-- `I9` -/
  I9 : ∀ a0, A.head? = some a0 →
    ((∀ q1, Q.head? = some q1 → s.pc q1 ≠ .l7) → s.node a0 = .token) ∧
    (∀ q1, Q.head? = some q1 → s.pc q1 = .l7 → s.node a0 = .nil ∨ s.node a0 = .go q1)
  /-- `I10` (only `q₁` can be at line 7) -/
  I10 : ∀ p, s.pc p = .l7 → Q.head? = some p
  /-- `I11`, first line -/
  I11a : ∀ q1, Q.head? = some q1 → s.pc q1 = .l4 → s.go q1 = false →
    ∃ p, s.pc p = .l8 ∧ s.v p = .go q1
  /-- `I11`, second line (`x = q_{i-1}`, `y = q_i`, `a = a_{i-1}`) -/
  I11b : ∀ (i : ℕ) x y, Q[i]? = some x → Q[i + 1]? = some y → s.pc y = .l4 → s.go y = false →
    ∀ a, A[i + 1]? = some a →
      s.node a = .go y ∨ (s.node a = .addr (s.pred x) ∧ s.pc x = .l11 ∧ s.v x = .go y)
  /-- `I11`, third line -/
  I11c : ∀ p, s.pc p = .l8 ∨ s.pc p = .l11 → ∃ r, s.v p = .go r
  /-- `I12` -/
  I12 : ∀ p, s.pc p = .l5 → s.go p = true

/-! ## List helpers -/

section Lists

variable {α β : Type*} {pr my : α → β}

theorem chain_getElem? {a : β} {Q : List α} (h : Chain pr my a Q) :
    ∀ (i : ℕ) p, Q[i]? = some p → (a :: Q.map my)[i]? = some (pr p) := by
  induction Q generalizing a with
  | nil => simp
  | cons q Q ih =>
    intro i p hi
    cases i with
    | zero => simp at hi; subst hi; simp [h.1]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := ih h.2 i p hi
      simpa using this

theorem chain_of_getElem? {a : β} {Q : List α}
    (h : ∀ (i : ℕ) p, Q[i]? = some p → (a :: Q.map my)[i]? = some (pr p)) : Chain pr my a Q := by
  induction Q generalizing a with
  | nil => trivial
  | cons q Q ih =>
    refine ⟨?_, ih fun i p hi => ?_⟩
    · have := h 0 q (by simp); simpa using this.symm
    · have := h (i + 1) p (by simpa using hi); simpa using this

theorem getLast?_cons_map (a : β) (Q : List α) :
    (a :: Q.map my).getLast? = some (lastN my a Q) := by
  induction Q generalizing a with
  | nil => simp
  | cons q Q ih =>
    rw [List.map_cons, List.getLast?_cons_cons, ih, lastN_cons]

theorem lastN_of_getLast? {a : β} {Q : List α} {p : α} (h : Q.getLast? = some p) :
    lastN my a Q = my p := by
  obtain ⟨L, rfl⟩ : ∃ L, Q = L ++ [p] := by
    rcases List.eq_nil_or_concat Q with rfl | ⟨L, b, rfl⟩
    · simp at h
    · simp at h; subst h; exact ⟨L, List.concat_eq_append ..⟩
  exact lastN_concat a L p

/-- Chains from a start that is nobody's node and with the same last node coincide. -/
theorem chain_unique_back (hinj : Function.Injective my) {a : β} (ha : ∀ x, my x ≠ a)
    {Q Q' : List α} (h : Chain pr my a Q) (h' : Chain pr my a Q')
    (hl : lastN my a Q = lastN my a Q') : Q = Q' := by
  induction Q using List.reverseRecOn generalizing Q' with
  | nil =>
    rcases List.eq_nil_or_concat Q' with rfl | ⟨L, b, rfl⟩
    · rfl
    rw [List.concat_eq_append] at hl ⊢
    · rw [lastN_concat] at hl; exact absurd hl.symm (ha b)
  | append_singleton L x ih =>
    rcases List.eq_nil_or_concat Q' with rfl | ⟨L', b, rfl⟩
    · rw [lastN_concat] at hl; exact absurd hl (ha x)
    · rw [List.concat_eq_append] at hl h' ⊢
      rw [lastN_concat, lastN_concat] at hl
      have hxb := hinj hl; subst hxb
      rw [chain_append] at h h'
      have e := h.2.1.symm.trans h'.2.1
      rw [ih h.1 h'.1 e]

end Lists

/-- `N = {a₀} ∪ {mynode_p}` with `|N| = n + 1` forces `mynode` injective and `a₀` nobody's node. -/
theorem cover_inj {my : Fin n → Node n} {a0 : Node n} (h : ∀ x, x = a0 ∨ ∃ p, my p = x) :
    Function.Injective my ∧ ∀ p, my p ≠ a0 := by
  have hcov : (Finset.univ : Finset (Node n)) ⊆ insert a0 (Finset.univ.image my) := by
    intro x _
    rcases h x with rfl | ⟨p, rfl⟩ <;> simp
  have hcard := Finset.card_le_card hcov
  simp only [Finset.card_univ, Fintype.card_option, Fintype.card_fin] at hcard
  have him : (Finset.univ.image my).card ≤ n := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := my)
  constructor
  · have hc : n ≤ (Finset.univ.image my).card := by
      have := (Finset.card_insert_le a0 (Finset.univ.image my)).trans' hcard; omega
    have heq : (Finset.univ.image my).card = (Finset.univ : Finset (Fin n)).card := by
      simp only [Finset.card_univ, Fintype.card_fin]; omega
    intro x y hxy
    exact Finset.injOn_of_card_image_eq heq (by simp) (by simp) hxy
  · intro p hp
    have : a0 ∈ Finset.univ.image my := by rw [← hp]; simp
    rw [Finset.insert_eq_of_mem this] at hcard
    have := hcard.trans him; omega

/-! ## Theorem 4.1 -/

/-- The strengthened invariant implies the paper's invariant. -/
theorem paperInv_of {s : State n} {Q : List (Fin n)} {a0 : Node n} (hs : Struct s Q a0)
    (hl : Loc s a0) : PaperInv s (a0 :: Q.map s.mynode) Q := by
  have hchain := chain_getElem? hs.ok.chain
  have hmemQ : ∀ (i : ℕ) p, Q[i]? = some p → InQ s p := fun i p h =>
    (hs.mem p).1 (List.mem_of_getElem? h)
  -- adjacency in `Q` is `pred_y = mynode_x`
  have hadj : ∀ (i : ℕ) x y, Q[i]? = some x → Q[i + 1]? = some y → s.pred y = s.mynode x := by
    intro i x y hx hy
    have := hchain (i + 1) y hy
    simp only [List.getElem?_cons_succ, List.getElem?_map, hx, Option.map_some] at this
    exact (Option.some.inj this).symm
  have hhead : ∀ q1, Q.head? = some q1 → s.pred q1 = a0 := by
    intro q1 h
    have := hchain 0 q1 (by simpa [List.head?_eq_getElem?] using h)
    simpa using this.symm
  have hheadQ : ∀ p, InQ s p → s.pred p = a0 → Q.head? = some p := by
    intro p hp hpa
    obtain ⟨R, hR⟩ := hs.ok.head ((hs.mem p).2 hp) hpa
    simp [hR]
  refine ⟨by simp, ?_, hs.ok.nodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine List.nodup_cons.2 ⟨?_, (List.nodup_map_iff hs.inj).2 hs.ok.nodup⟩
    simp only [List.mem_map, not_exists, not_and]
    exact fun p _ => hs.a0_ne p
  · rw [getLast?_cons_map, hs.last]
  · intro i p h; simp [h]
  · exact hchain
  · intro x
    by_cases hx : ∃ p, s.mynode p = x
    · exact Or.inr hx
    · left; push_neg at hx
      simp [a0_unique hs.inj hx hs.a0_ne]
  · intro p
    by_cases hx : ∃ r, s.mynode r = s.pred p
    · exact Or.inr hx
    · left; push_neg at hx
      simp [a0_unique hs.inj hx hs.a0_ne]
  · intro p
    refine ⟨fun h hp => ?_, hl.i6a p, hl.i6b p⟩
    have := (hs.mem p).1 hp
    rcases h with h | h
    · exact not_InQ_l2 h this
    · exact not_InQ_l8 h this
  · intro p hp
    have hpQ : InQ s p := (hs.mem p).1 (List.mem_of_getLast? hp)
    have hlast : s.mynode p = s.tail := by rw [← hs.last, lastN_of_getLast? hp]
    refine ⟨fun h7 => ?_, fun h1 => ?_⟩
    · have hact : (s.pc p).act = true := by
        simp only [PC.inI7, List.mem_cons, List.not_mem_nil] at h7
        rcases h7 with h | h | h | h | h | h | h | h <;> simp_all
      rcases hl.i7 p hact with h | ⟨y, hy, hyp, -⟩
      · exact h
      · exact absurd (hyp.trans hlast) (hs.pred_ne_tail hy)
    · rcases hpQ with h | h
      · simp only [List.mem_cons, List.not_mem_nil] at h1
        rcases h1 with h1 | h1 | h1 <;> simp_all
      · exact h.2
  · intro i x y hx hy
    have hxQ := hmemQ i x hx
    have hyQ := hmemQ (i + 1) y hy
    refine ⟨fun h7 => ?_, fun h1 => ?_⟩
    · have hact : (s.pc x).act = true := by
        simp only [PC.inI7, List.mem_cons, List.not_mem_nil] at h7
        rcases h7 with h | h | h | h | h | h | h | h <;> simp_all
      rcases hl.i7 x hact with h | ⟨y', hy', hyx, h⟩
      · exact Or.inl h
      · right
        have := hs.pred_inj hy' hyQ (hyx.trans (hadj i x y hx hy).symm)
        subst this; exact h
    · rcases hxQ with h | h
      · simp only [List.mem_cons, List.not_mem_nil] at h1
        rcases h1 with h1 | h1 | h1 <;> simp_all
      · exact h.2
  · intro p hp
    have hpQ : ¬ InQ s p := fun h => hp ((hs.mem p).2 h)
    have hact : (s.pc p).act = false := by
      by_contra h; exact hpQ (Or.inl (by simpa using h))
    refine ⟨?_, ?_⟩
    · revert hact; cases s.pc p <;> simp
    · intro h
      rcases PC.act_or_ab (s.pc p) with h' | h' | h' | h'
      · simp_all
      · exact hpQ (Or.inr ⟨h', h⟩)
      · rw [hl.i6a p h'] at h; simp at h
      · rcases hl.i6b p h' with h'' | h'' <;> rw [h''] at h <;> simp at h
  · intro a h
    simp only [List.head?_cons, Option.some.injEq] at h; subst h
    refine ⟨fun h => hl.i9a fun y hy h7 => ?_, fun q1 hq1 h7 => hl.i9b q1 (hhead q1 hq1) h7⟩
    exact h y (hheadQ y (InQ.of_pc h7 rfl) hy) h7
  · intro p h7
    exact hheadQ p (InQ.of_pc h7 rfl) (hl.i10 p h7)
  · intro q1 hq1 h4 hg
    exact hl.i11a q1 (hhead q1 hq1) h4 hg
  · intro i x y hx hy h4 hg a ha
    have : a = s.mynode x := by simp [hx] at ha; exact ha.symm
    subst this
    exact hl.i11b x y (hmemQ i x hx) (hadj i x y hx hy) h4 hg
  · exact hl.i11c
  · exact hl.i12

/-- **Theorem 4.1** (existence). In every reachable configuration of Algorithm 1 there are
`A = [a₀, …, a_k]` and `Q = [q₁, …, q_k]` satisfying the invariant `I = I1 ∧ … ∧ I12`. -/
theorem theorem_4_1 {s : State n} (h : Reachable s) : ∃ A Q, PaperInv s A Q := by
  obtain ⟨Q, a0, hs, hl⟩ := h.inv
  exact ⟨_, Q, paperInv_of hs hl⟩

/-- The paper's remark after Figure 1: `I1`–`I4` alone determine `A` and `Q`. -/
theorem unique_of_I1_I4 {s : State n} {A A' : List (Node n)} {Q Q' : List (Fin n)}
    (hlen : A.length = Q.length + 1) (hI1 : A.getLast? = some s.tail)
    (hI2 : ∀ (i : ℕ) p, Q[i]? = some p → A[i + 1]? = some (s.mynode p))
    (hI3 : ∀ (i : ℕ) p, Q[i]? = some p → A[i]? = some (s.pred p))
    (hI4 : ∀ x : Node n, A.head? = some x ∨ ∃ p, s.mynode p = x)
    (hlen' : A'.length = Q'.length + 1) (hI1' : A'.getLast? = some s.tail)
    (hI2' : ∀ (i : ℕ) p, Q'[i]? = some p → A'[i + 1]? = some (s.mynode p))
    (hI3' : ∀ (i : ℕ) p, Q'[i]? = some p → A'[i]? = some (s.pred p))
    (hI4' : ∀ x : Node n, A'.head? = some x ∨ ∃ p, s.mynode p = x) : A = A' ∧ Q = Q' := by
  -- `A = a₀ :: Q.map mynode`
  have hform : ∀ {A : List (Node n)} {Q : List (Fin n)}, A.length = Q.length + 1 →
      (∀ (i : ℕ) p, Q[i]? = some p → A[i + 1]? = some (s.mynode p)) →
      (∀ x : Node n, A.head? = some x ∨ ∃ p, s.mynode p = x) →
      ∃ a0, A = a0 :: Q.map s.mynode ∧ (∀ x, x = a0 ∨ ∃ p, s.mynode p = x) := by
    intro A Q hlen hI2 hI4
    cases A with
    | nil => exact absurd hlen (by simp)
    | cons a0 As =>
      refine ⟨a0, ?_, fun x => ?_⟩
      · congr 1
        apply List.ext_getElem?
        intro i
        by_cases hi : i < Q.length
        · have := hI2 i Q[i] (by simp [hi]); simp at this; simp [this, hi]
        · have hl := hlen; simp at hl
          rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
      · rcases hI4 x with hx | hx
        · simp at hx; exact Or.inl hx.symm
        · exact Or.inr hx
  obtain ⟨a0, rfl, hc⟩ := hform hlen hI2 hI4
  obtain ⟨a0', rfl, hc'⟩ := hform hlen' hI2' hI4'
  obtain ⟨hinj, ha0⟩ := cover_inj hc
  obtain ⟨-, ha0'⟩ := cover_inj hc'
  have e : a0 = a0' := a0_unique hinj ha0 ha0'
  subst e
  have hch := chain_of_getElem? hI3
  have hch' := chain_of_getElem? hI3'
  have hl : lastN s.mynode a0 Q = lastN s.mynode a0 Q' := by
    rw [getLast?_cons_map] at hI1 hI1'
    exact (Option.some.inj hI1).trans (Option.some.inj hI1').symm
  have := chain_unique_back hinj ha0 hch hch' hl
  subst this
  exact ⟨rfl, rfl⟩

/-- **Theorem 4.1** (uniqueness). `k`, `A` and `Q` are determined by the configuration. -/
theorem theorem_4_1_unique {s : State n} {A A' : List (Node n)} {Q Q' : List (Fin n)}
    (h : PaperInv s A Q) (h' : PaperInv s A' Q') : A = A' ∧ Q = Q' :=
  unique_of_I1_I4 h.len h.I1 h.I2 h.I3 h.I4 h'.len h'.I1 h'.I2 h'.I3 h'.I4

/-- **Corollary 4.1.1** (mutual exclusion): at most one process is in the CS (line 7). -/
theorem mutual_exclusion {s : State n} (h : Reachable s) {p q : Fin n}
    (hp : s.pc p = .l7) (hq : s.pc q = .l7) : p = q := by
  obtain ⟨A, Q, hI⟩ := theorem_4_1 h
  have h1 := hI.I10 p hp
  have h2 := hI.I10 q hq
  rw [h1] at h2; exact Option.some.inj h2

end Podc.AbortableMutexAmortized
