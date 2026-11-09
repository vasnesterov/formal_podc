import Papers.PODC2026.RandomizedWaitFreeLocks.Alg2Model

/-!
# Algorithm 2: the inductive invariant

Every step preserves `Inv` (`inv_step`), hence every reachable configuration satisfies it
(`inv_reachable`). The proof is one lemma per program line.
-/

set_option linter.unusedSectionVars false

namespace Podc.RandomizedWaitFreeLocks.Alg2

variable {P D : Type*} [DecidableEq P] [DecidableEq D]

open Function

variable {c c' : Cfg P D} {x : D}

/-! ## Stability under the steps of other processes -/

lemma EnvOK.post (e : EnvOK c c') (h : Post c x) : Post c' x := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [e.stat x h1]; exact h1, ?_⟩
  rw [e.stat x h1]; exact fun h => e.done x (h2 h)

lemma EnvOK.L_some (e : EnvOK c c') (h : c.L = some x) : c'.L = some x ∨ Post c x := by
  rcases e.L with h' | h'
  · left; rw [h', h]
  · right; exact h' x h

lemma EnvOK.stat_exec (e : EnvOK c c') (h : c.stat x = .exec) : c'.stat x = .exec := by
  rw [e.stat x (by rw [h]; decide), h]

lemma EnvOK.stat_susp (e : EnvOK c c') (h : c.stat x = .susp) : c'.stat x = .susp := by
  rw [e.stat x (by rw [h]; decide), h]

lemma EnvOK.of_eq (h1 : c'.stat = c.stat) (h2 : c'.done = c.done) (h3 : c'.started = c.started)
    (h4 : c'.used = c.used) (h5 : c'.L = c.L) : EnvOK c c' where
  stat x _ := by rw [h1]
  done x h := by rw [h2]; exact h
  started x h := by rw [h3]; exact h
  used x h := by rw [h4]; exact h
  L := Or.inl h5

lemma HapInv.mono (e : EnvOK c c') : ∀ {l : HLine}, HapInv c l x → HapInv c' l x
  | .l11, _ => trivial
  | .l12, h => by
    rcases h with h | h
    · rcases e.L_some h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (e.post h')
    · exact Or.inr (e.post h)
  | .l13, ⟨h1, h2⟩ => by
    refine ⟨by rw [e.stat x h1]; exact h1, ?_⟩
    rcases h2 with h | h
    · rcases e.L_some h with h' | h'
      · exact Or.inl h'
      · right; rw [e.stat x h1]; exact fun h'' => e.done x (h'.2 h'')
    · right; rw [e.stat x h1]; exact fun h' => e.done x (h h')
  | .l14s, ⟨h1, h2⟩ => by
    refine ⟨e.stat_exec h1, ?_⟩
    rcases h2 with h | h
    · rcases e.L_some h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (e.done x (h'.2 h1))
    · exact Or.inr (e.done x h)
  | .l14e, ⟨h1, h0, h2⟩ => by
    refine ⟨e.stat_exec h1, e.started x h0, ?_⟩
    rcases h2 with h | h
    · rcases e.L_some h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (e.done x (h'.2 h1))
    · exact Or.inr (e.done x h)
  | .l15, h => e.post h
  | .l16, h => e.post h
  | .l17, h => e.post h
  | .l18, h => e.post h
  | .l21, h => e.post h

lemma Loc.frame {q : P} (h : Loc c q) (e : EnvOK c c') (hpc : c'.pc q = c.pc q)
    (hcall : c'.call q = c.call q) (hw : c'.w q = c.w q) (hd : c'.d q = c.d q)
    (hw2 : c'.w2 q = c.w2 q) : Loc c' q where
  idle_iff := by rw [hpc, hcall]; exact h.idle_iff
  call_used x hx := e.used x (h.call_used x (hcall ▸ hx))
  w_used x hx := e.used x (h.w_used x (hw ▸ hx))
  d_used x hx := e.used x (h.d_used x (hd ▸ hx))
  w2_used x hx := e.used x (h.w2_used x (hw2 ▸ hx))
  hap r l x hp hx := (h.hap r l x (hpc ▸ hp) (hw ▸ hx)).mono e
  fin hp := by
    obtain ⟨x, hx, h'⟩ := h.fin (hpc ▸ hp)
    refine ⟨x, hcall ▸ hx, ?_⟩
    rcases h' with h' | h'
    · exact Or.inl (e.done x h')
    · exact Or.inr (e.stat_susp h')

lemma Glob.of_shared (h : Glob c) (h1 : c'.L = c.L) (h2 : c'.R = c.R) (h3 : c'.stat = c.stat)
    (h4 : c'.done = c.done) (h5 : c'.started = c.started) (h6 : c'.used = c.used)
    (h7 : c'.call = c.call) (h8 : c'.abort = c.abort) : Glob c' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  constructor <;> simp only [h1, h2, h3, h4, h5, h6, h7, h8] <;> assumption

lemma Inv.of {p : P} (h : Inv c) (hG : Glob c') (e : EnvOK c c')
    (hF : ∀ q, q ≠ p → c'.pc q = c.pc q ∧ c'.call q = c.call q ∧ c'.w q = c.w q ∧
      c'.d q = c.d q ∧ c'.w2 q = c.w2 q)
    (hp : Loc c' p) : Inv c' := by
  refine ⟨hG, fun q => ?_⟩
  by_cases hq : q = p
  · exact hq ▸ hp
  · obtain ⟨a, b, d, f, g⟩ := hF q hq
    exact (h.2 q).frame e a b d f g

lemma Loc.call_ne_none {q : P} (h : Loc c q) (hpc : c.pc q ≠ .idle) : c.call q ≠ none :=
  fun h' => hpc (h.idle_iff.2 h')

/-- Building `Loc c' p` after a step of `p` that keeps `p`'s call. -/
lemma Loc.of_step {p : P} (hp : Loc c p) (e : EnvOK c c') (h7 : c'.call p = c.call p)
    (hidle : c.pc p ≠ .idle) (hidle' : c'.pc p ≠ .idle)
    (hw : ∀ x, c'.w p = some x → c.used x = true)
    (hd : ∀ x, c'.d p = some x → c.used x = true)
    (hw2 : ∀ x, c'.w2 p = some x → c.used x = true)
    (hhap : ∀ r l x, c'.pc p = .hap r l → c'.w p = some x → HapInv c' l x)
    (hfin : c'.pc p = .l33 ∨ c'.pc p = .l34 →
      ∃ x, c'.call p = some x ∧ (c'.done x = true ∨ c'.stat x = .susp)) : Loc c' p where
  idle_iff := by rw [h7]; exact iff_of_false hidle' (hp.call_ne_none hidle)
  call_used x hx := e.used x (hp.call_used x (h7 ▸ hx))
  w_used x hx := e.used x (hw x hx)
  d_used x hx := e.used x (hd x hx)
  w2_used x hx := e.used x (hw2 x hx)
  hap := hhap
  fin := hfin

/-- A step of `p` that changes only `p`'s program counter, `p`'s locals and possibly
`C` and `R`. -/
lemma Inv.of_local {p : P} (h : Inv c) (hG : Glob c') (h1 : c'.L = c.L)
    (h3 : c'.stat = c.stat) (h4 : c'.done = c.done) (h5 : c'.started = c.started)
    (h6 : c'.used = c.used) (h7 : c'.call = c.call)
    (hF : ∀ q, q ≠ p → c'.pc q = c.pc q ∧ c'.w q = c.w q ∧ c'.d q = c.d q ∧ c'.w2 q = c.w2 q)
    (hidle : c.pc p ≠ .idle) (hidle' : c'.pc p ≠ .idle)
    (hw : ∀ x, c'.w p = some x → c.used x = true)
    (hd : ∀ x, c'.d p = some x → c.used x = true)
    (hw2 : ∀ x, c'.w2 p = some x → c.used x = true)
    (hhap : ∀ r l x, c'.pc p = .hap r l → c'.w p = some x → HapInv c' l x)
    (hfin : c'.pc p = .l33 ∨ c'.pc p = .l34 →
      ∃ x, c.call p = some x ∧ (c.done x = true ∨ c.stat x = .susp)) : Inv c' := by
  have e : EnvOK c c' := EnvOK.of_eq h3 h4 h5 h6 h1
  refine Inv.of (p := p) h hG e (fun q hq => ?_)
    ((h.2 p).of_step e (by rw [h7]) hidle hidle' hw hd hw2 hhap ?_)
  · obtain ⟨a, b, d, f⟩ := hF q hq; exact ⟨a, by rw [h7], b, d, f⟩
  · intro hp; rw [h7, h4, h3]; exact hfin hp

/-- The local steps keep the global invariant. -/
lemma Glob.of_local (h : Glob c) (h1 : c'.L = c.L) (h3 : c'.stat = c.stat)
    (h4 : c'.done = c.done) (h5 : c'.started = c.started) (h6 : c'.used = c.used)
    (h7 : c'.call = c.call) (h8 : c'.abort = c.abort) (h2 : c'.R = c.R) : Glob c' :=
  h.of_shared h1 h2 h3 h4 h5 h6 h7 h8

/-! ## One lemma per line -/

section Lines

variable {p : P} {r : Ret} (j : ℕ)

lemma inv_l11 (h : Inv c) (hpc : c.pc p = .hap r .l11) :
    Inv (stepAt c p j (.hap r .l11)).1 := by
  refine Inv.of_local (p := p) h (h.1.of_local rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl
    rfl (fun q hq => by simp [stepAt, update_of_ne hq]) (by simp [hpc]) (by simp [stepAt])
    ?_ ?_ ?_ ?_ (by simp [stepAt])
  · intro x hx; simp [stepAt] at hx; exact h.1.L_used x hx
  · intro x hx; simp [stepAt] at hx; exact (h.2 p).d_used x hx
  · intro x hx; simp [stepAt] at hx; exact (h.2 p).w2_used x hx
  · intro r' l x hp hx
    simp [stepAt] at hp hx
    obtain ⟨rfl, rfl⟩ := hp
    exact Or.inl hx

lemma inv_l13 (h : Inv c) (hpc : c.pc p = .hap r .l13) :
    Inv (stepAt c p j (.hap r .l13)).1 := by
  refine Inv.of_local (p := p) h (h.1.of_local rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl
    rfl (fun q hq => by simp [stepAt, update_of_ne hq]) (by simp [hpc]) (by simp [stepAt]; split_ifs <;> simp)
    (fun x hx => (h.2 p).w_used x hx) (fun x hx => (h.2 p).d_used x hx)
    (fun x hx => (h.2 p).w2_used x hx) ?_ (by simp [stepAt]; split_ifs <;> simp)
  intro r' l x hp hx
  have H := (h.2 p).hap r .l13 x hpc hx
  change c.w p = some x at hx
  simp only [stepAt, update_self, hx, statO] at hp
  obtain ⟨H1, H2⟩ := H
  by_cases hs : c.stat x = .exec
  · simp [hs] at hp; obtain ⟨rfl, rfl⟩ := hp
    exact ⟨hs, H2.imp id (fun h' => h' hs)⟩
  · simp [hs] at hp; obtain ⟨rfl, rfl⟩ := hp
    exact ⟨H1, fun h' => absurd h' hs⟩

lemma inv_l15 (h : Inv c) (hpc : c.pc p = .hap r .l15) :
    Inv (stepAt c p j (.hap r .l15)).1 := by
  refine Inv.of_local (p := p) h (h.1.of_local rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl
    rfl (fun q hq => by simp [stepAt, update_of_ne hq]) (by simp [hpc]) (by simp [stepAt])
    (fun x hx => (h.2 p).w_used x hx) (fun x hx => (h.2 p).d_used x hx)
    (fun x hx => (h.2 p).w2_used x hx) ?_ (by simp [stepAt])
  intro r' l x hp hx
  simp [stepAt] at hp; obtain ⟨rfl, rfl⟩ := hp
  exact (h.2 p).hap r .l15 x hpc hx

lemma inv_l16 (h : Inv c) (hpc : c.pc p = .hap r .l16) :
    Inv (stepAt c p j (.hap r .l16)).1 := by
  refine Inv.of_local (p := p) h (h.1.of_local rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl
    rfl (fun q hq => by simp [stepAt, update_of_ne hq]) (by simp [hpc]) (by simp [stepAt])
    (fun x hx => (h.2 p).w_used x hx) (fun x hx => (h.2 p).d_used x hx)
    (fun x hx => (h.2 p).w2_used x hx) ?_ (by simp [stepAt])
  intro r' l x hp hx
  simp [stepAt] at hp; obtain ⟨rfl, rfl⟩ := hp
  exact (h.2 p).hap r .l16 x hpc hx

lemma inv_l17 (h : Inv c) (hpc : c.pc p = .hap r .l17) :
    Inv (stepAt c p j (.hap r .l17)).1 := by
  refine Inv.of_local (p := p) h (h.1.of_local rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl
    rfl (fun q hq => by simp [stepAt, update_of_ne hq]) (by simp [hpc]) (by simp [stepAt])
    (fun x hx => (h.2 p).w_used x hx) ?_ (fun x hx => (h.2 p).w2_used x hx) ?_ (by simp [stepAt])
  · intro x hx; simp [stepAt] at hx; exact h.1.R_used _ x hx
  · intro r' l x hp hx
    simp [stepAt] at hp; obtain ⟨rfl, rfl⟩ := hp
    exact (h.2 p).hap r .l17 x hpc hx

lemma inv_l18 (h : Inv c) (hpc : c.pc p = .hap r .l18) :
    Inv (stepAt c p j (.hap r .l18)).1 := by
  refine Inv.of_local (p := p) h (h.1.of_local rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl
    rfl (fun q hq => by simp [stepAt, update_of_ne hq]) (by simp [hpc]) (by simp [stepAt])
    (fun x hx => (h.2 p).w_used x hx) (fun x hx => (h.2 p).d_used x hx) ?_ ?_ (by simp [stepAt])
  · intro x hx; simp only [stepAt, update_self] at hx
    split_ifs at hx
    · exact (h.2 p).d_used x hx
    · exact (h.2 p).call_used x hx
    · exact (h.2 p).w_used x hx
  · intro r' l x hp hx
    simp [stepAt] at hp; obtain ⟨rfl, rfl⟩ := hp
    exact (h.2 p).hap r .l18 x hpc hx

lemma inv_l23 (h : Inv c) (hpc : c.pc p = .l23) : Inv (stepAt c p j .l23).1 := by
  refine Inv.of_local (p := p) h (h.1.of_local rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl
    rfl (fun q hq => by simp [stepAt, update_of_ne hq]) (by simp [hpc]) (by simp [stepAt])
    (fun x hx => (h.2 p).w_used x hx) (fun x hx => (h.2 p).d_used x hx)
    (fun x hx => (h.2 p).w2_used x hx) ?_ (by simp [stepAt])
  intro r' l x hp hx
  simp [stepAt] at hp; obtain ⟨rfl, rfl⟩ := hp
  trivial

lemma inv_l25a (h : Inv c) (hpc : c.pc p = .l25a) : Inv (stepAt c p j .l25a).1 := by
  refine Inv.of_local (p := p) h (h.1.of_local rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl
    rfl (fun q hq => by simp [stepAt, update_of_ne hq]) (by simp [hpc]) (by simp [stepAt]; split_ifs <;> simp)
    (fun x hx => (h.2 p).w_used x hx) (fun x hx => (h.2 p).d_used x hx)
    (fun x hx => (h.2 p).w2_used x hx) (by intro r' l x hp; simp [stepAt] at hp; split_ifs at hp) ?_
  intro hp
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 ((h.2 p).call_ne_none (by simp [hpc]))
  simp only [stepAt, update_self, hx, doneO] at hp
  by_cases hd : c.done x = true
  · exact ⟨x, hx, Or.inl hd⟩
  · simp [hd] at hp

lemma inv_l25b (h : Inv c) (hpc : c.pc p = .l25b) : Inv (stepAt c p j .l25b).1 := by
  refine Inv.of_local (p := p) h (h.1.of_local rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl
    rfl (fun q hq => by simp [stepAt, update_of_ne hq]) (by simp [hpc]) (by simp [stepAt]; split_ifs <;> simp)
    (fun x hx => (h.2 p).w_used x hx) (fun x hx => (h.2 p).d_used x hx)
    (fun x hx => (h.2 p).w2_used x hx) (by intro r' l x hp; simp [stepAt] at hp; split_ifs at hp) ?_
  intro hp
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 ((h.2 p).call_ne_none (by simp [hpc]))
  simp only [stepAt, update_self, hx, statO] at hp
  by_cases hd : c.stat x = .susp
  · exact ⟨x, hx, Or.inr hd⟩
  · simp [hd] at hp

lemma inv_l33 (h : Inv c) (hpc : c.pc p = .l33) : Inv (stepAt c p j .l33).1 := by
  refine Inv.of_local (p := p) h (h.1.of_local rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl
    rfl (fun q hq => by simp [stepAt, update_of_ne hq]) (by simp [hpc]) (by simp [stepAt])
    (fun x hx => (h.2 p).w_used x hx) (fun x hx => (h.2 p).d_used x hx)
    (fun x hx => (h.2 p).w2_used x hx) (by intro r' l x hp; simp [stepAt] at hp) (fun _ => (h.2 p).fin (Or.inl hpc))

lemma inv_l26_write (h : Inv c) (hpc : c.pc p = .l26) (ha : c.abort p = false) :
    Inv (stepAt c p j .l26).1 := by
  have hc : (stepAt c p j .l26).1 =
      { c with
          clock := c.clock + 1, R := update c.R j (c.call p)
          pc := update c.pc p (.hap .r32a .l11) } := by simp [stepAt, ha]
  rw [hc]
  refine Inv.of_local (p := p) h ?_ rfl rfl rfl rfl rfl rfl
    (fun q hq => by simp [update_of_ne hq]) (by simp [hpc]) (by simp)
    (fun x hx => (h.2 p).w_used x hx) (fun x hx => (h.2 p).d_used x hx)
    (fun x hx => (h.2 p).w2_used x hx) (by intro r' l x hp hx; simp at hp; obtain ⟨rfl, rfl⟩ := hp; trivial) (by simp)
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h.1
  refine ⟨a1, ?_, a3, a4, a5, a6, a7, a8, a9⟩
  intro i x hx
  simp only [update_apply] at hx
  split_ifs at hx
  · exact (h.2 p).call_used x hx
  · exact a2 i x hx

lemma inv_l12 (h : Inv c) (hpc : c.pc p = .hap r .l12) :
    Inv (stepAt c p j (.hap r .l12)).1 := by
  set c' := (stepAt c p j (.hap r .l12)).1 with hc'
  have hpc' : c'.pc p = .hap r .l13 := by simp [c', stepAt]
  have hF : ∀ q, q ≠ p → c'.pc q = c.pc q ∧ c'.w q = c.w q ∧ c'.d q = c.d q ∧ c'.w2 q = c.w2 q :=
    fun q hq => by simp [c', stepAt, update_of_ne hq]
  rcases hw : c.w p with _ | x
  · have hst : c'.stat = c.stat := by simp [c', stepAt, hw, casStat]
    refine Inv.of_local (p := p) h (Glob.of_local (c' := c') h.1 rfl hst rfl rfl rfl rfl rfl rfl) rfl hst rfl rfl
      rfl rfl hF (by simp [hpc]) (by simp [hpc'])
      (fun x hx => (h.2 p).w_used x hx) (fun x hx => (h.2 p).d_used x hx)
      (fun x hx => (h.2 p).w2_used x hx) ?_ (by simp [hpc'])
    intro r' l x hp hx; change c.w p = some x at hx; simp [hw] at hx
  have H := (h.2 p).hap r .l12 x hpc hw
  by_cases hs : c.stat x = .wait
  swap
  · have hst : c'.stat = c.stat := by simp [c', stepAt, hw, casStat, hs]
    refine Inv.of_local (p := p) h (Glob.of_local (c' := c') h.1 rfl hst rfl rfl rfl rfl rfl rfl) rfl hst rfl rfl
      rfl rfl hF (by simp [hpc]) (by simp [hpc'])
      (fun x hx => (h.2 p).w_used x hx) (fun x hx => (h.2 p).d_used x hx)
      (fun x hx => (h.2 p).w2_used x hx) ?_ (by simp [hpc'])
    intro r' l y hp hy
    rw [hpc'] at hp; cases hp
    change c.w p = some y at hy; rw [hw] at hy; cases hy
    show c'.stat x ≠ .wait ∧ (c.L = some x ∨ (c'.stat x = .exec → c.done x = true))
    rw [hst]
    refine ⟨hs, ?_⟩
    rcases H with H | H
    · exact Or.inl H
    · exact Or.inr H.2
  have hxu : c.used x = true := (h.2 p).w_used x hw
  have hL : c.L = some x := H.resolve_right (fun h' => h'.1 hs)
  have hst : c'.stat = update c.stat x .exec := by simp [c', stepAt, hw, casStat, hs]
  have e : EnvOK c c' :=
    ⟨fun y hy => by rw [hst, update_of_ne (by rintro rfl; exact hy hs)], fun y hy => hy,
      fun y hy => hy, fun y hy => hy, Or.inl rfl⟩
  refine Inv.of (p := p) h ?_ e (fun q hq => by simp [c', stepAt, update_of_ne hq]) ?_
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h.1
    refine ⟨a1, a2, ?_, ?_, a5, a6, ?_, a8, ?_⟩
    · intro y hy
      have hy' : c.used y = false := hy
      rw [hst, update_of_ne (by rintro rfl; simp [hxu] at hy')]; exact a3 y hy'
    · intro y hy; rw [hst]
      by_cases hyx : y = x
      · subst hyx; simp
      · rw [update_of_ne hyx]; exact a4 y hy
    · intro y hu hd hsu
      by_cases hyx : y = x
      · subst hyx; exact a7 y hu hd (by rw [hs]; decide)
      · rw [hst, update_of_ne hyx] at hsu; exact a7 y hu hd hsu
    · intro q y hq hsu
      by_cases hyx : y = x
      · subst hyx; rw [hst] at hsu; simp at hsu
      · rw [hst, update_of_ne hyx] at hsu; exact a9 q y hq hsu
  · refine (h.2 p).of_step e rfl (by simp [hpc]) (by simp [hpc'])
      (fun x hx => (h.2 p).w_used x hx) (fun x hx => (h.2 p).d_used x hx)
      (fun x hx => (h.2 p).w2_used x hx) ?_ (by simp [hpc'])
    intro r' l y hp hy
    rw [hpc'] at hp; cases hp
    change c.w p = some y at hy; rw [hw] at hy; cases hy
    show c'.stat x ≠ .wait ∧ (c.L = some x ∨ (c'.stat x = .exec → c.done x = true))
    rw [hst]; simp [hL]

lemma inv_l14s (h : Inv c) (hpc : c.pc p = .hap r .l14s) :
    Inv (stepAt c p j (.hap r .l14s)).1 := by
  set c' := (stepAt c p j (.hap r .l14s)).1 with hc'
  rcases hw : c.w p with _ | x
  · have hpc' : c'.pc p = .hap r .l14e := by simp [c', stepAt, hw]
    refine Inv.of_local (p := p) h (h.1.of_local (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw])
      (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw])
      (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw]))
      (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw])
      (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw])
      (fun q hq => by simp [c', stepAt, hw, update_of_ne hq]) (by simp [hpc]) (by simp [hpc'])
      (fun x hx => by simp [c', stepAt, hw] at hx) (fun x hx => (h.2 p).d_used x (by simpa [c', stepAt, hw] using hx))
      (fun x hx => (h.2 p).w2_used x (by simpa [c', stepAt, hw] using hx))
      (fun r' l x hp hx => by simp [c', stepAt, hw] at hx) (by simp [hpc'])
  have H := (h.2 p).hap r .l14s x hpc hw
  obtain ⟨H1, H2⟩ := H
  have hxu : c.used x = true := (h.2 p).w_used x hw
  have hst : c'.started = update c.started x true := by simp [c', stepAt, hw]
  have hpc' : c'.pc p = .hap r .l14e := by simp [c', stepAt, hw]
  have hsame : c'.stat = c.stat ∧ c'.done = c.done ∧ c'.used = c.used ∧ c'.L = c.L ∧
      c'.R = c.R ∧ c'.call = c.call ∧ c'.abort = c.abort ∧ c'.w = c.w ∧ c'.d = c.d ∧
      c'.w2 = c.w2 := by simp [c', stepAt, hw]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := hsame
  have e : EnvOK c c' := by
    refine ⟨fun y _ => by rw [s1], fun y hy => by rw [s2]; exact hy, fun y hy => ?_,
      fun y hy => by rw [s3]; exact hy, Or.inl s4⟩
    rw [hst]
    by_cases hyx : y = x
    · subst hyx; simp
    · rw [update_of_ne hyx]; exact hy
  refine Inv.of (p := p) h ?_ e (fun q hq => by simp [c', stepAt, hw, update_of_ne hq]) ?_
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [s1, s2, s3, s4, s5, s6, s7, hst]
    · exact a1
    · exact a2
    · intro y hy
      rw [update_of_ne (by rintro rfl; simp [hxu] at hy)]; exact a3 y hy
    · intro y hy
      by_cases hyx : y = x
      · subst hyx; exact H1
      · rw [update_of_ne hyx] at hy; exact a4 y hy
    · intro y hy
      by_cases hyx : y = x
      · subst hyx; simp
      · rw [update_of_ne hyx]; exact a5 y hy
    · intro y hy hd
      by_cases hyx : y = x
      · subst hyx; rcases H2 with H2 | H2
        · exact H2
        · simp [H2] at hd
      · rw [update_of_ne hyx] at hy; exact a6 y hy hd
    · exact a7
    · exact a8
    · exact a9
  · refine (h.2 p).of_step e (by rw [s6]) (by simp [hpc]) (by simp [hpc'])
      (fun y hy => (h.2 p).w_used y (by rw [s8] at hy; exact hy))
      (fun y hy => (h.2 p).d_used y (by rw [s9] at hy; exact hy))
      (fun y hy => (h.2 p).w2_used y (by rw [s10] at hy; exact hy)) ?_ (by simp [hpc'])
    intro r' l y hp hy
    rw [hpc'] at hp; cases hp
    rw [s8, hw] at hy; cases hy
    show c'.stat x = .exec ∧ c'.started x = true ∧ (c'.L = some x ∨ c'.done x = true)
    rw [s1, s2, s4, hst]; simp [H1, H2]

lemma inv_l14e (h : Inv c) (hpc : c.pc p = .hap r .l14e) :
    Inv (stepAt c p j (.hap r .l14e)).1 := by
  set c' := (stepAt c p j (.hap r .l14e)).1 with hc'
  rcases hw : c.w p with _ | x
  · have hpc' : c'.pc p = .hap r .l15 := by simp [c', stepAt, hw]
    refine Inv.of_local (p := p) h (h.1.of_local (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw])
      (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw])
      (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw]))
      (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw])
      (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw]) (by simp [c', stepAt, hw])
      (fun q hq => by simp [c', stepAt, hw, update_of_ne hq]) (by simp [hpc]) (by simp [hpc'])
      (fun x hx => by simp [c', stepAt, hw] at hx) (fun x hx => (h.2 p).d_used x (by simpa [c', stepAt, hw] using hx))
      (fun x hx => (h.2 p).w2_used x (by simpa [c', stepAt, hw] using hx))
      (fun r' l x hp hx => by simp [c', stepAt, hw] at hx) (by simp [hpc'])
  have H := (h.2 p).hap r .l14e x hpc hw
  obtain ⟨H1, H0, H2⟩ := H
  have hxu : c.used x = true := (h.2 p).w_used x hw
  have hdn : c'.done = update c.done x true := by simp [c', stepAt, hw]
  have hpc' : c'.pc p = .hap r .l15 := by simp [c', stepAt, hw]
  have hsame : c'.stat = c.stat ∧ c'.started = c.started ∧ c'.used = c.used ∧ c'.L = c.L ∧
      c'.R = c.R ∧ c'.call = c.call ∧ c'.abort = c.abort ∧ c'.w = c.w ∧ c'.d = c.d ∧
      c'.w2 = c.w2 := by simp [c', stepAt, hw]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := hsame
  have e : EnvOK c c' := by
    refine ⟨fun y _ => by rw [s1], fun y hy => ?_, fun y hy => by rw [s2]; exact hy,
      fun y hy => by rw [s3]; exact hy, Or.inl s4⟩
    rw [hdn]
    by_cases hyx : y = x
    · subst hyx; simp
    · rw [update_of_ne hyx]; exact hy
  refine Inv.of (p := p) h ?_ e (fun q hq => by simp [c', stepAt, hw, update_of_ne hq]) ?_
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [s1, s2, s3, s4, s5, s6, s7, hdn]
    · exact a1
    · exact a2
    · intro y hy
      rw [update_of_ne (by rintro rfl; simp [hxu] at hy)]; exact a3 y hy
    · exact a4
    · intro y hy
      by_cases hyx : y = x
      · subst hyx; exact H0
      · rw [update_of_ne hyx] at hy; exact a5 y hy
    · intro y hy hd
      by_cases hyx : y = x
      · subst hyx; simp at hd
      · rw [update_of_ne hyx] at hd; exact a6 y hy hd
    · intro y hu hd
      by_cases hyx : y = x
      · subst hyx; simp at hd
      · rw [update_of_ne hyx] at hd; exact a7 y hu hd
    · exact a8
    · exact a9
  · refine (h.2 p).of_step e (by rw [s6]) (by simp [hpc]) (by simp [hpc'])
      (fun y hy => (h.2 p).w_used y (by rw [s8] at hy; exact hy))
      (fun y hy => (h.2 p).d_used y (by rw [s9] at hy; exact hy))
      (fun y hy => (h.2 p).w2_used y (by rw [s10] at hy; exact hy)) ?_ (by simp [hpc'])
    intro r' l y hp hy
    rw [hpc'] at hp; cases hp
    rw [s8, hw] at hy; cases hy
    show c'.stat x ≠ .wait ∧ (c'.stat x = .exec → c'.done x = true)
    rw [s1, hdn]; simp [H1]

lemma inv_l21 (h : Inv c) (hpc : c.pc p = .hap r .l21) :
    Inv (stepAt c p j (.hap r .l21)).1 := by
  set c' := (stepAt c p j (.hap r .l21)).1 with hc'
  have hL : c'.L = if c.L = c.w p then c.w2 p else c.L := by simp [c', stepAt]
  have hpc' : c'.pc p = r.next := by simp [c', stepAt]
  have hsame : c'.stat = c.stat ∧ c'.done = c.done ∧ c'.started = c.started ∧
      c'.used = c.used ∧ c'.R = c.R ∧ c'.call = c.call ∧ c'.abort = c.abort ∧ c'.w = c.w ∧
      c'.d = c.d ∧ c'.w2 = c.w2 := by simp [c', stepAt]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := hsame
  -- Lemma 4.11: the CAS only replaces a descriptor that has left `L` for good
  have hpost : c'.L = c.L ∨ ∀ y, c.L = some y → Post c y := by
    rw [hL]; split_ifs with hc
    · right; intro y hy; exact (h.2 p).hap r .l21 y hpc (hc ▸ hy)
    · left; rfl
  have e : EnvOK c c' := ⟨fun y _ => by rw [s1], fun y hy => by rw [s2]; exact hy,
    fun y hy => by rw [s3]; exact hy, fun y hy => by rw [s4]; exact hy, hpost⟩
  have hnext : ∀ r' l, r.next = .hap r' l → l = .l11 := by
    intro r' l h'; cases r <;> simp [Ret.next] at h' <;> exact h'.2.symm
  have hnext_idle : r.next ≠ .idle := by cases r <;> simp [Ret.next]
  have hnext_fin : ¬ (r.next = .l33 ∨ r.next = .l34) := by cases r <;> simp [Ret.next]
  refine Inv.of (p := p) h ?_ e (fun q hq => by simp [c', stepAt, update_of_ne hq]) ?_
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [s1, s2, s3, s4, s5, s6, s7]
    · intro y hy; rw [hL] at hy; split_ifs at hy
      · exact (h.2 p).w2_used y hy
      · exact a1 y hy
    · exact a2
    · exact a3
    · exact a4
    · exact a5
    · intro y hy hd
      have hLy := a6 y hy hd
      rcases hpost with hp' | hp'
      · rw [hp', hLy]
      · have := (hp' y hLy).2 (a4 y hy); simp [this] at hd
    · exact a7
    · exact a8
    · exact a9
  · refine (h.2 p).of_step e (by rw [s6]) (by simp [hpc]) (by rw [hpc']; exact hnext_idle)
      (fun y hy => (h.2 p).w_used y (by rw [s8] at hy; exact hy))
      (fun y hy => (h.2 p).d_used y (by rw [s9] at hy; exact hy))
      (fun y hy => (h.2 p).w2_used y (by rw [s10] at hy; exact hy))
      (fun r' l y hp _ => by rw [hpc'] at hp; rw [hnext r' l hp]; trivial)
      (fun hp => absurd (hpc' ▸ hp) hnext_fin)

lemma inv_l26_abort (h : Inv c) (hpc : c.pc p = .l26) (ha : c.abort p = true) :
    Inv (stepAt c p j .l26).1 := by
  set c' := (stepAt c p j .l26).1 with hc'
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 ((h.2 p).call_ne_none (by simp [hpc]))
  have hxu := (h.2 p).call_used x hx
  have hpc' : c'.pc p = .hap .r28 .l11 := by simp [c', stepAt, ha]
  have hsame : c'.done = c.done ∧ c'.started = c.started ∧
      c'.used = c.used ∧ c'.R = c.R ∧ c'.call = c.call ∧ c'.abort = c.abort ∧ c'.w = c.w ∧
      c'.d = c.d ∧ c'.w2 = c.w2 ∧ c'.L = c.L := by simp [c', stepAt, ha]
  obtain ⟨s2, s3, s4, s5, s6, s7, s8, s9, s10, s1⟩ := hsame
  have hF : ∀ q, q ≠ p → c'.pc q = c.pc q ∧ c'.w q = c.w q ∧ c'.d q = c.d q ∧ c'.w2 q = c.w2 q :=
    fun q hq => by simp [c', stepAt, ha, update_of_ne hq]
  by_cases hs : c.stat x = .wait
  swap
  · have hst : c'.stat = c.stat := by simp [c', stepAt, ha, hx, casStat, hs]
    exact Inv.of_local (p := p) h (Glob.of_local (c' := c') h.1 s1 hst s2 s3 s4 s6 s7 s5) s1 hst s2
      s3 s4 s6 hF (by simp [hpc]) (by simp [hpc'])
      (fun y hy => (h.2 p).w_used y (by rw [s8] at hy; exact hy))
      (fun y hy => (h.2 p).d_used y (by rw [s9] at hy; exact hy))
      (fun y hy => (h.2 p).w2_used y (by rw [s10] at hy; exact hy))
      (fun r' l y hp _ => by rw [hpc'] at hp; cases hp; trivial) (by simp [hpc'])
  have hst : c'.stat = update c.stat x .susp := by simp [c', stepAt, ha, hx, casStat, hs]
  have e : EnvOK c c' := ⟨fun y hy => by rw [hst, update_of_ne (by rintro rfl; exact hy hs)],
    fun y hy => by rw [s2]; exact hy, fun y hy => by rw [s3]; exact hy,
    fun y hy => by rw [s4]; exact hy, Or.inl s1⟩
  refine Inv.of (p := p) h ?_ e (fun q hq => by
    obtain ⟨a, b, d, f⟩ := hF q hq; exact ⟨a, by rw [s6], b, d, f⟩) ?_
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [s1, s2, s3, s4, s5, s6, s7, hst]
    · exact a1
    · exact a2
    · intro y hy
      rw [update_of_ne (by rintro rfl; simp [hxu] at hy)]; exact a3 y hy
    · intro y hy
      have hyx : y ≠ x := by rintro rfl; rw [a4 y hy] at hs; cases hs
      rw [update_of_ne hyx]; exact a4 y hy
    · exact a5
    · exact a6
    · intro y hu hd hsu
      have hyx : y ≠ x := by rintro rfl; simp at hsu
      rw [update_of_ne hyx] at hsu; exact a7 y hu hd hsu
    · exact a8
    · intro q y hq hsu
      by_cases hyx : y = x
      · subst hyx; rw [a8 q p y hq hx]; exact ha
      · rw [update_of_ne hyx] at hsu; exact a9 q y hq hsu
  · exact (h.2 p).of_step e (by rw [s6]) (by simp [hpc]) (by simp [hpc'])
      (fun y hy => (h.2 p).w_used y (by rw [s8] at hy; exact hy))
      (fun y hy => (h.2 p).d_used y (by rw [s9] at hy; exact hy))
      (fun y hy => (h.2 p).w2_used y (by rw [s10] at hy; exact hy))
      (fun r' l y hp _ => by rw [hpc'] at hp; cases hp; trivial) (by simp [hpc'])

lemma inv_l34 (h : Inv c) (hpc : c.pc p = .l34) : Inv (stepAt c p j .l34).1 := by
  obtain ⟨x, hx, hfin⟩ := (h.2 p).fin (Or.inr hpc)
  set c' := (stepAt c p j .l34).1 with hc'
  have hcall : c'.call = update c.call p none := by simp [c', stepAt, hx]
  have hpc' : c'.pc p = .idle := by simp [c', stepAt, hx]
  have hsame : c'.stat = c.stat ∧ c'.done = c.done ∧ c'.started = c.started ∧
      c'.used = c.used ∧ c'.R = c.R ∧ c'.L = c.L ∧ c'.abort = c.abort ∧ c'.w = c.w ∧
      c'.d = c.d ∧ c'.w2 = c.w2 := by simp [c', stepAt, hx]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := hsame
  have e : EnvOK c c' := EnvOK.of_eq s1 s2 s3 s4 s6
  refine Inv.of (p := p) h ?_ e (fun q hq => by simp [c', stepAt, hx, update_of_ne hq]) ?_
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [s1, s2, s3, s4, s5, s6, s7, hcall]
    · exact a1
    · exact a2
    · exact a3
    · exact a4
    · exact a5
    · exact a6
    · intro y hu hd hs
      obtain ⟨q, hq⟩ := a7 y hu hd hs
      refine ⟨q, ?_⟩
      by_cases hqp : q = p
      · subst hqp; rw [hx] at hq; cases hq
        rcases hfin with hf | hf
        · simp [hf] at hd
        · exact absurd hf hs
      · rw [update_of_ne hqp]; exact hq
    · intro q1 q2 y h1 h2
      by_cases h1p : q1 = p
      · subst h1p; simp at h1
      by_cases h2p : q2 = p
      · subst h2p; simp at h2
      rw [update_of_ne h1p] at h1; rw [update_of_ne h2p] at h2; exact a8 q1 q2 y h1 h2
    · intro q y hq hs
      by_cases hqp : q = p
      · subst hqp; simp at hq
      · rw [update_of_ne hqp] at hq; exact a9 q y hq hs
  · refine ⟨by rw [hpc', hcall]; simp, by rw [hcall]; simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy; rw [s4]; exact (h.2 p).w_used y (by rw [s8] at hy; exact hy)
    · intro y hy; rw [s4]; exact (h.2 p).d_used y (by rw [s9] at hy; exact hy)
    · intro y hy; rw [s4]; exact (h.2 p).w2_used y (by rw [s10] at hy; exact hy)
    · intro r' l y hp; rw [hpc'] at hp; cases hp
    · rw [hpc']; simp

end Lines

lemma Inv.tick (h : Inv c) : Inv (tick c) :=
  ⟨h.1.of_shared rfl rfl rfl rfl rfl rfl rfl rfl,
    fun q => (h.2 q).frame (EnvOK.of_eq rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl⟩

lemma inv_abort {p : P} {b : Bool} (h : Inv c) (hs : (c.call p).isSome) :
    Inv (step c (.abort p) b).1 := by
  have hc : (step c (.abort p) b).1 = { c with clock := c.clock + 1, abort := update c.abort p true } := by
    simp [step, hs]
  rw [hc]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h.1
  refine ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, ?_⟩,
    fun q => (h.2 q).frame (EnvOK.of_eq rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl⟩
  intro q y hq hs'
  simp only [update_apply]
  split_ifs
  · rfl
  · exact a9 q y hq hs'

lemma inv_invoke {p : P} {b : Bool} (h : Inv c) (hpc : c.pc p = .idle) (hu : c.used x = false) :
    Inv (step c (.invoke p x) b).1 := by
  set c' := (step c (.invoke p x) b).1 with hc'
  have hcp : c.call p = none := (h.2 p).idle_iff.1 hpc
  obtain ⟨hxw, hxs, hxd⟩ := h.1.unused x hu
  have hused : c'.used = update c.used x true := by simp [c', step, hpc, hu]
  have hcall : c'.call = update c.call p (some x) := by simp [c', step, hpc, hu]
  have habort : c'.abort = update c.abort p false := by simp [c', step, hpc, hu]
  have hpc' : c'.pc p = .hap .r22a .l12 := by simp [c', step, hpc, hu]
  have hw' : c'.w p = c.L := by simp [c', step, hpc, hu]
  have hsame : c'.stat = c.stat ∧ c'.done = c.done ∧ c'.started = c.started ∧
      c'.R = c.R ∧ c'.L = c.L ∧ c'.d = c.d ∧ c'.w2 = c.w2 := by simp [c', step, hpc, hu]
  obtain ⟨s1, s2, s3, s5, s6, s9, s10⟩ := hsame
  have hum : ∀ y, c.used y = true → c'.used y = true := by
    intro y hy; rw [hused]
    by_cases hyx : y = x
    · subst hyx; simp
    · rw [update_of_ne hyx]; exact hy
  have e : EnvOK c c' := ⟨fun y _ => by rw [s1], fun y hy => by rw [s2]; exact hy,
    fun y hy => by rw [s3]; exact hy, hum, Or.inl s6⟩
  have hnx : ∀ q, c.call q ≠ some x := fun q hq => by simp [(h.2 q).call_used x hq] at hu
  refine Inv.of (p := p) h ?_ e (fun q hq => by simp [c', step, hpc, hu, update_of_ne hq]) ?_
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [s1, s2, s3, s5, s6, hcall, habort]
    · intro y hy; exact hum y (a1 y hy)
    · intro i y hy; exact hum y (a2 i y hy)
    · intro y hy
      have hyx : y ≠ x := by rintro rfl; rw [hused] at hy; simp at hy
      rw [hused, update_of_ne hyx] at hy; exact a3 y hy
    · exact a4
    · exact a5
    · exact a6
    · intro y hu' hd hs
      by_cases hyx : y = x
      · subst hyx; exact ⟨p, by simp⟩
      · rw [hused, update_of_ne hyx] at hu'
        obtain ⟨q, hq⟩ := a7 y hu' hd hs
        have hqp : q ≠ p := by rintro rfl; rw [hcp] at hq; cases hq
        exact ⟨q, by rw [update_of_ne hqp]; exact hq⟩
    · intro q1 q2 y h1 h2
      by_cases h1p : q1 = p <;> by_cases h2p : q2 = p
      · rw [h1p, h2p]
      · subst h1p; simp at h1; subst h1; rw [update_of_ne h2p] at h2; exact absurd h2 (hnx q2)
      · subst h2p; simp at h2; subst h2; rw [update_of_ne h1p] at h1; exact absurd h1 (hnx q1)
      · rw [update_of_ne h1p] at h1; rw [update_of_ne h2p] at h2; exact a8 q1 q2 y h1 h2
    · intro q y hq hs
      by_cases hqp : q = p
      · subst hqp; simp at hq; subst hq; rw [hxw] at hs; cases hs
      · rw [update_of_ne hqp] at hq; rw [update_of_ne hqp]; exact a9 q y hq hs
  · refine ⟨by rw [hpc', hcall]; simp, ?_, ?_, ?_, ?_, ?_, by rw [hpc']; simp⟩
    · intro y hy; rw [hcall] at hy; simp at hy; subst hy; rw [hused]; simp
    · intro y hy; rw [hw'] at hy; exact hum y (h.1.L_used y hy)
    · intro y hy; rw [s9] at hy; exact hum y ((h.2 p).d_used y hy)
    · intro y hy; rw [s10] at hy; exact hum y ((h.2 p).w2_used y hy)
    · intro r' l y hp hy
      rw [hpc'] at hp; cases hp
      rw [hw'] at hy
      exact Or.inl (by rw [s6]; exact hy)

lemma inv_init : Inv (init : Cfg P D) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun q => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [init]

/-- Every step preserves the invariant. -/
theorem inv_step (h : Inv c) (a : Act P D) (b : Bool) : Inv (step c a b).1 := by
  cases a with
  | invoke p x =>
    by_cases hv : c.pc p = .idle ∧ c.used x = false
    · exact inv_invoke h hv.1 hv.2
    · have : (step c (.invoke p x) b).1 = tick c := by simp [step, hv]
      rw [this]; exact h.tick
  | abort p =>
    by_cases hv : (c.call p).isSome
    · exact inv_abort h hv
    · have : (step c (.abort p) b).1 = tick c := by simp [step, hv]
      rw [this]; exact h.tick
  | sched p j =>
    show Inv (stepAt c p j (c.pc p)).1
    rcases hpc : c.pc p with _ | ⟨r, l⟩ | _ | _ | _ | _ | _ | _
    · exact h.tick
    · cases l
      · exact inv_l11 j h hpc
      · exact inv_l12 j h hpc
      · exact inv_l13 j h hpc
      · exact inv_l14s j h hpc
      · exact inv_l14e j h hpc
      · exact inv_l15 j h hpc
      · exact inv_l16 j h hpc
      · exact inv_l17 j h hpc
      · exact inv_l18 j h hpc
      · exact inv_l21 j h hpc
    · exact inv_l23 j h hpc
    · exact inv_l25a j h hpc
    · exact inv_l25b j h hpc
    · cases ha : c.abort p
      · exact inv_l26_write j h hpc ha
      · exact inv_l26_abort j h hpc ha
    · exact inv_l33 j h hpc
    · exact inv_l34 j h hpc

/-- Every reachable configuration satisfies the invariant. -/
theorem inv_reachable {c : Cfg P D} (hc : Reachable init step c) : Inv c :=
  Reachable.induction init step inv_init (fun _ a b _ h => inv_step h a b) hc

end Podc.RandomizedWaitFreeLocks.Alg2
