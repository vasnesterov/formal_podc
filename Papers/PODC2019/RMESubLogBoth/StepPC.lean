import Papers.PODC2019.RMESubLogBoth.Frame

/-!
# The program counter after a step, by line
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ} {c c' : Cfg k} {p : Fin k}

lemma Cfg.setPc_eq_self {r : PC k} (h : c.pc p = r) : c.setPc p r = c := by
  subst h; simp [Cfg.setPc]

lemma step_l10 (h : Step c p c') (hp : c.pc p = .rem ∨ c.pc p = .l10) :
    (c.node p = none ∧ c'.pc p = .l11) ∨ ∃ x, c.node p = some x ∧ c'.pc p = .l18 x := by
  rcases hp with hp | hp <;> cases h <;> simp_all [Cfg.setPc]

lemma step_l11 (h : Step c p c') (hp : c.pc p = .l11) : c'.pc p = .l13 c.nxt := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l13 {x : ℕ} (h : Step c p c') (hp : c.pc p = .l13 x) :
    c'.pc p = .l14 x c.tail := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l14 {x m : ℕ} (h : Step c p c') (hp : c.pc p = .l14 x m) : c'.pc p = .l15 x m := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l15 {x m : ℕ} (h : Step c p c') (hp : c.pc p = .l15 x m) :
    c'.pc p = .l25 x (.node m) := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l18 {x : ℕ} (h : Step c p c') (hp : c.pc p = .l18 x) :
    c'.pc p = .l18w x ∨ c'.pc p = .l19 x := by
  cases h <;> simp_all [Cfg.setPc]; tauto

lemma step_l18w {x : ℕ} (h : Step c p c') (hp : c.pc p = .l18w x) : c'.pc p = .l19 x := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l19 {x : ℕ} (h : Step c p c') (hp : c.pc p = .l19 x) :
    c'.pc p = .cs x ∨ c'.pc p = .l22a x ∨ ∃ v, c'.pc p = .l23 x v := by
  cases h <;> simp_all [Cfg.setPc]; split <;> simp

lemma step_l22a {x : ℕ} (h : Step c p c') (hp : c.pc p = .l22a x) : c'.pc p = .l22b := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l22b (h : Step c p c') (hp : c.pc p = .l22b) :
    c'.pc p = .l10 ∧ c'.node p = none := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l23 {x : ℕ} {v : PV} (h : Step c p c') (hp : c.pc p = .l23 x v) :
    c'.pc p = .l24 x v := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l24 {x : ℕ} {v : PV} (h : Step c p c') (hp : c.pc p = .l24 x v) :
    (c'.pc p = .l30 x v ∧ (c.holder = none ∨ c.holder = some p)) ∨
      (c'.pc p = .l24 x v ∧ c' = c ∧ ∃ q, c.holder = some q ∧ q ≠ p) := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l30 {x : ℕ} {v : PV} (h : Step c p c') (hp : c.pc p = .l30 x v) :
    c'.pc p = .l31 x ∨ c'.pc p = .rx x v := by
  cases h <;> simp_all [Cfg.setPc]; tauto

lemma step_l31 {x : ℕ} (h : Step c p c') (hp : c.pc p = .l31 x) :
    c'.pc p = .l33 x c.tail ∅ ∅ 0 := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l33 {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {i : ℕ} (h : Step c p c')
    (hp : c.pc p = .l33 x tl V E i) :
    (i < k ∧ c'.pc p = .l33 x tl V E (i + 1)) ∨ (i < k ∧ ∃ a, c'.pc p = .l35 x tl V E i a) ∨
      (k ≤ i ∧ c'.pc p = .l39 x tl V E) := by
  cases h with
  | l33 _ _ _ _ _ h' hi =>
    rw [hp] at h'; cases h'
    simp only [Cfg.setPc, Function.update_self]
    split
    · exact .inl ⟨hi, rfl⟩
    · exact .inr (.inl ⟨hi, _, rfl⟩)
  | l33_end _ _ _ _ _ h' hi =>
    rw [hp] at h'; cases h'
    exact .inr (.inr ⟨hi, by simp [Cfg.setPc]⟩)
  | _ => simp_all

lemma step_l35 {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {i a : ℕ} (h : Step c p c')
    (hp : c.pc p = .l35 x tl V E i a) :
    (c.nn a = true ∧ c'.pc p = .l36 x tl V E i a) ∨ (c.nn a = false ∧ c' = c) := by
  cases h with
  | l35 _ _ _ _ _ _ h' =>
    rw [hp] at h'; cases h'
    split_ifs with ha
    · exact .inl ⟨ha, by simp [Cfg.setPc]⟩
    · exact .inr ⟨by simpa using ha, Cfg.setPc_eq_self hp⟩
  | _ => simp_all

lemma step_l36 {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {i a : ℕ} (h : Step c p c')
    (hp : c.pc p = .l36 x tl V E i a) :
    c'.pc p = .l33 x tl (addV V a (c.pred a)) (addE E a (c.pred a)) (i + 1) := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l39 {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} (h : Step c p c')
    (hp : c.pc p = .l39 x tl V E) : ∃ mp tp, c'.pc p = .l42 x tl V E mp tp none [] := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l42 {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {mp : List ℕ}
    {tp hp' : Option (List ℕ)} {dn : List (List ℕ)} (h : Step c p c')
    (hp : c.pc p = .l42 x tl V E mp tp hp' dn) :
    (∃ σ, IsMaxPath V E σ ∧ σ ∉ dn ∧ c'.pc p = .l43 x tl V E mp tp hp' (σ :: dn) σ) ∨
      c'.pc p = .l46 x tl V E mp tp hp' := by
  cases h with
  | l42_next _ _ _ _ _ _ _ _ h' σ hσ hσd =>
    rw [hp] at h'; cases h'; exact .inl ⟨σ, hσ, hσd, by simp [Cfg.setPc]⟩
  | l42_end _ _ _ _ _ _ _ _ h' _ => rw [hp] at h'; cases h'; exact .inr (by simp [Cfg.setPc])
  | _ => simp_all

lemma step_l43 {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {mp : List ℕ}
    {tp hp' : Option (List ℕ)} {dn : List (List ℕ)} {σ : List ℕ} (h : Step c p c')
    (hp : c.pc p = .l43 x tl V E mp tp hp' dn σ) :
    c'.pc p = .l44 x tl V E mp tp hp' dn σ ∨ c'.pc p = .l42 x tl V E mp tp hp' dn := by
  cases h <;> simp_all [Cfg.setPc]
  all_goals (split_ifs <;> simp)

lemma step_l44 {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {mp : List ℕ}
    {tp hp' : Option (List ℕ)} {dn : List (List ℕ)} {σ : List ℕ} (h : Step c p c')
    (hp : c.pc p = .l44 x tl V E mp tp hp' dn σ) :
    ∃ hp'', c'.pc p = .l42 x tl V E mp tp hp'' dn := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l46 {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {mp : List ℕ}
    {tp hp' : Option (List ℕ)} (h : Step c p c') (hp : c.pc p = .l46 x tl V E mp tp hp') :
    (∃ s, c'.pc p = .l47 x s) ∨ ∃ m, c'.pc p = .l49 x m := by
  cases h <;> simp_all [Cfg.setPc]
  split_ifs <;> simp

lemma step_l47 {x s : ℕ} (h : Step c p c') (hp : c.pc p = .l47 x s) :
    c'.pc p = .l49 x c.tail := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l49 {x m : ℕ} (h : Step c p c') (hp : c.pc p = .l49 x m) :
    c'.pc p = .rx x (.node m) := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_rx {x : ℕ} {v : PV} (h : Step c p c') (hp : c.pc p = .rx x v) :
    c'.pc p = .l25 x v ∧ c'.holder = none := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l25 {x m : ℕ} (h : Step c p c') (hp : c.pc p = .l25 x (.node m)) :
    (c.csig m = true ∧ c'.pc p = .l26 x) ∨ (c.csig m = false ∧ c' = c) := by
  cases h with
  | l25 _ _ h' =>
    rw [hp] at h'; cases h'
    simp only
    split_ifs with ha
    · exact .inl ⟨ha, by simp [Cfg.setPc]⟩
    · exact .inr ⟨by simpa using ha, Cfg.setPc_eq_self hp⟩
  | _ => simp_all

lemma step_l26 {x : ℕ} (h : Step c p c') (hp : c.pc p = .l26 x) : c'.pc p = .cs x := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_cs {x : ℕ} (h : Step c p c') (hp : c.pc p = .cs x) : c'.pc p = .l28 x := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l28 {x : ℕ} (h : Step c p c') (hp : c.pc p = .l28 x) : c'.pc p = .l29 := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_l29 (h : Step c p c') (hp : c.pc p = .l29) : c'.pc p = .rem := by
  cases h <;> simp_all [Cfg.setPc]

end Podc.RMESubLogBoth
