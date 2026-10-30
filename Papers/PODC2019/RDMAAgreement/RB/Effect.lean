import Papers.PODC2019.RDMAAgreement.RB.InvA

/-!
# Algorithm 2 — effects of a step on memory, pending writes and candidate sets

These lemmas express the regular-register semantics at the level of single steps: every value a
register holds, every candidate of a pending read, and every pending write value, was either
already there or was produced by the write invoked in this step.
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

lemma St.pendW_go (X : St P M) (p q : P) (c : PC P M) (r : Reg P) :
    (X.go p q c).pendW r = ({ X with pc := upd2 X.pc p q c } : St P M).pendW r := by
  ext x; simp only [mem_pendW, go_pc, go_bpend, key, go_last]

lemma St.tick_go_cand_other (X : St P M) (p q : P) (c : PC P M) {p' q' : P}
    (hne : ¬ (p' = p ∧ q' = q)) {x : Val P M} (hx : x ∈ ((X.go p q c).tick).cand p' q') :
    x ∈ X.cand p' q' ∨ ∃ r, c.wr p q (X.key p q) = some (r, x) ∧
      (X.pc p' q').rd q' (X.key p' q') = some r := by
  have := (mem_go_cand X p q c x p' q').1 hx
  simp only [hne, if_false] at this
  rcases this with h | ⟨r, v, h1, h2, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨r, h1, h2⟩

lemma St.tick_go_cand_self (X : St P M) (p q : P) (c : PC P M) {r : Reg P}
    (hr : c.rd q (X.key p q) = some r) {x : Val P M} (hx : x ∈ ((X.go p q c).tick).cand p q) :
    x = X.mem r ∨ x ∈ ((X.go p q c).tick).pendW r := by
  have := (mem_go_cand X p q c x p q).1 hx
  simp only [and_self, if_true] at this
  rcases this.1 r hr with h | h
  · exact Or.inl h
  · right
    have e : ((X.go p q c).tick).pendW r = (X.go p q c).pendW r := rfl
    rw [e, St.pendW_go]; exact h

/-- Effect of a step of delivery thread `(p,q)` on candidate sets, memory and pending writes. -/
structure ThrEffect (s s' : St P M) (p q : P) : Prop where
  cand_other : ∀ p' q', ¬ (p' = p ∧ q' = q) → ∀ x ∈ s'.cand p' q', x ∈ s.cand p' q' ∨
    ∃ r, (s'.pc p q).wr p q (s'.key p q) = some (r, x) ∧ (s.pc p' q').rd q' (s.key p' q') = some r
  cand_self : ∀ r, (s'.pc p q).rd q (s'.key p q) = some r → ∀ x ∈ s'.cand p q,
    x = s'.mem r ∨ x ∈ s'.pendW r
  mem : ∀ r, s'.mem r = s.mem r ∨ (s.pc p q).wr p q (s.key p q) = some (r, s'.mem r)
  pendW : ∀ r, ∀ x ∈ s'.pendW r, x ∈ s.pendW r ∨ (s'.pc p q).wr p q (s'.key p q) = some (r, x)
  cand_mono : ∀ p' q', ¬ (p' = p ∧ q' = q) → s.cand p' q' ⊆ s'.cand p' q'
  cand_mem : ∀ r, (s'.pc p q).rd q (s'.key p q) = some r → s'.mem r ∈ s'.cand p q

/-- Generic form of the new state of a thread step. -/
private lemma thrEffect_of {s X : St P M} {p q : P} {c : PC P M} (s' : St P M)
    (hs' : s' = (X.go p q c).tick ∨ ∃ t, s' = { (X.go p q c) with scanT := t }.tick)
    (hpc : X.pc = s.pc) (hcand : X.cand = s.cand) (hb : X.bpend = s.bpend)
    (hlast : ∀ p' q', ¬ (p' = p ∧ q' = q) → X.last p' q' = s.last p' q')
    (hmem : ∀ r, X.mem r = s.mem r ∨ (s.pc p q).wr p q (s.key p q) = some (r, X.mem r)) :
    ThrEffect s s' p q := by
  have hkey : ∀ p' q', ¬ (p' = p ∧ q' = q) → X.key p' q' = s.key p' q' := fun p' q' h => by
    simp [St.key, hlast p' q' h]
  have hcand' : s'.cand = ((X.go p q c).tick).cand := by rcases hs' with rfl | ⟨t, rfl⟩ <;> rfl
  have hpc' : s'.pc = upd2 X.pc p q c := by rcases hs' with rfl | ⟨t, rfl⟩ <;> simp [St.tick]
  have hmem' : s'.mem = X.mem := by rcases hs' with rfl | ⟨t, rfl⟩ <;> simp [St.tick]
  have hlast' : s'.last = X.last := by rcases hs' with rfl | ⟨t, rfl⟩ <;> simp [St.tick]
  have hbp' : s'.bpend = X.bpend := by rcases hs' with rfl | ⟨t, rfl⟩ <;> simp [St.tick]
  have hkey' : s'.key = X.key := by unfold St.key; rw [hlast']
  have hpW : ∀ r, s'.pendW r = ((X.go p q c).tick).pendW r := fun r => by
    ext x
    simp only [mem_pendW, hpc', hbp', hkey', St.tick, go_pc, go_bpend, key_go, St.key, go_last,
      hlast']
  refine ⟨fun p' q' hne x hx => ?_, fun r hr x hx => ?_, fun r => ?_, fun r x hx => ?_,
    fun p' q' hne x hx => ?_, fun r hr => ?_⟩
  · rw [hcand'] at hx
    rcases St.tick_go_cand_other X p q c hne hx with h | ⟨r, h1, h2⟩
    · left; rw [← hcand]; exact h
    · right; refine ⟨r, ?_, ?_⟩
      · rw [hpc', hkey']; simpa using h1
      · rw [← hpc, ← hkey p' q' hne]; exact h2
  · rw [hcand'] at hx
    rw [hpc', hkey'] at hr; simp only [upd2_apply, and_self, if_true] at hr
    rcases St.tick_go_cand_self X p q c hr hx with h | h
    · left; rw [hmem']; exact h
    · right; rw [hpW]; exact h
  · rw [hmem']; exact hmem r
  · rw [hpW] at hx
    rcases hx with ⟨p', q', h⟩ | ⟨p', b, h1, h2, h3⟩
    · simp only [St.tick, go_pc, key_go, upd2_apply, St.key, go_last] at h
      by_cases hne : p' = p ∧ q' = q
      · obtain ⟨rfl, rfl⟩ := hne
        right; rw [hpc', hkey']; simpa [St.key] using h
      · simp only [hne, if_false] at h
        left; left; refine ⟨p', q', ?_⟩
        rw [← hpc, ← hkey p' q' hne]; simpa [St.key] using h
    · left; right; refine ⟨p', b, ?_, h2, h3⟩
      simp only [St.tick, go_bpend] at h1; rw [← hb]; exact h1
  · rw [hcand']
    have := (mem_go_cand X p q c x p' q').2 (by
      simp only [hne, if_false]; left; rw [hcand]; exact hx)
    exact this
  · rw [hcand', hmem']
    rw [hpc', hkey'] at hr; simp only [upd2_apply, and_self, if_true] at hr
    refine (mem_go_cand X p q c _ p q).2 ?_
    simp only [and_self, if_true]
    exact ⟨fun r' hr' => by rw [hr] at hr'; cases hr'; exact Or.inl rfl,
      fun hn => by rw [hr] at hn; cases hn⟩

lemma Step.thrEffect {s s' : St P M} {p q : P} (h : Step F f s (.thr p q) s') :
    ThrEffect s s' p q := by
  cases h with
  | l2EndV =>
    exact thrEffect_of _ (Or.inr ⟨_, rfl⟩) (by rfl) (by rfl) (by rfl) (fun _ _ _ => rfl)
      (fun _ => Or.inl rfl)
  | copyDone hp hpc =>
    refine thrEffect_of _ (Or.inl rfl) (by rfl) (by rfl) (by rfl) ?_ ?_
    · intro p' q' hne; simp [St.deliver, St.write, hne]
    · intro r; simp only [St.deliver, St.write]
      by_cases hr : r = ⟨.l2, p, s.key p q, q⟩
      · subst hr; right; simp [hpc, PC.wr]
      · left; simp [Function.update_of_ne hr]
  | echoDone hp hpc =>
    refine thrEffect_of _ (Or.inl rfl) (by rfl) (by rfl) (by rfl) (fun _ _ _ => rfl) ?_
    intro r; simp only [St.setPhase, St.write]
    by_cases hr : r = ⟨.val, p, s.key p q, q⟩
    · subst hr; right; simp [hpc, PC.wr]
    · left; simp [Function.update_of_ne hr]
  | l1Done hp hpc =>
    refine thrEffect_of _ (Or.inl rfl) (by rfl) (by rfl) (by rfl) (fun _ _ _ => rfl) ?_
    intro r; simp only [St.setPhase, St.write]
    by_cases hr : r = ⟨.l1, p, s.key p q, q⟩
    · subst hr; right; simp [hpc, PC.wr]
    · left; simp [Function.update_of_ne hr]
  | l2Done hp hpc =>
    refine thrEffect_of _ (Or.inl rfl) (by rfl) (by rfl) (by rfl) (fun _ _ _ => rfl) ?_
    intro r; simp only [St.write]
    by_cases hr : r = ⟨.l2, p, s.key p q, q⟩
    · subst hr; right; simp [hpc, PC.wr]
    · left; simp [Function.update_of_ne hr]
  | _ =>
    exact thrEffect_of _ (Or.inl rfl) (by rfl) (by rfl) (by rfl) (fun _ _ _ => rfl)
      (fun _ => Or.inl rfl)

/-- A per-register property of all values "in" a register: its current value, the values of the
pending writes to it, and the candidates of the pending reads of it. -/
structure RegInv (s : St P M) (Q : Reg P → Val P M → Prop) : Prop where
  mem : ∀ r, Q r (s.mem r)
  pend : ∀ r, ∀ x ∈ s.pendW r, Q r x
  cand : ∀ p q r, (s.pc p q).rd q (s.key p q) = some r → ∀ x ∈ s.cand p q, Q r x

/-- Register invariants are preserved if the values newly written in the step satisfy them. -/
lemma RegInv.step {s s' : St P M} {ℓ : Label P M} {Q Q' : Reg P → Val P M → Prop}
    (I : RegInv s Q) (h : Step F f s ℓ s') (hQ : ∀ r x, Q r x → Q' r x)
    (hthr : ∀ p q, ℓ = .thr p q → ∀ r x, (s'.pc p q).wr p q (s'.key p q) = some (r, x) → Q' r x)
    (hbc : ∀ p m, ℓ = .bcast p m →
      Q' ⟨.val, p, s.bnext p + 1, p⟩ (.cp ⟨p, ⟨p, s.bnext p + 1, m⟩⟩))
    (hbyz : ∀ p r v, ℓ = .byz p r v → Q' r v) : RegInv s' Q' := by
  by_cases hℓ : ∃ p q, ℓ = .thr p q
  · obtain ⟨p, q, rfl⟩ := hℓ
    have E := h.thrEffect
    obtain ⟨hfr, -⟩ := h.frame_thr
    have hmem : ∀ r, Q' r (s'.mem r) := fun r => by
      rcases E.mem r with e | e
      · rw [e]; exact hQ _ _ (I.mem r)
      · exact hQ _ _ (I.pend r _ (Or.inl ⟨p, q, e⟩))
    have hpend : ∀ r, ∀ x ∈ s'.pendW r, Q' r x := fun r x hx => by
      rcases E.pendW r x hx with e | e
      · exact hQ _ _ (I.pend r x e)
      · exact hthr p q rfl r x e
    refine ⟨hmem, hpend, fun p' q' r hr x hx => ?_⟩
    by_cases hpq : p' = p ∧ q' = q
    · obtain ⟨rfl, rfl⟩ := hpq
      rcases E.cand_self r hr x hx with e | e
      · rw [e]; exact hmem r
      · exact hpend r x e
    · have hl := hfr p' q' hpq
      simp only [St.loc, Loc.mk.injEq] at hl
      have hk : s'.key p' q' = s.key p' q' := by simp [St.key, hl.2.1]
      rw [hl.1, hk] at hr
      rcases E.cand_other p' q' hpq x hx with e | ⟨r', e1, e2⟩
      · exact hQ _ _ (I.cand p' q' r hr x e)
      · rw [hr] at e2; cases e2; exact hthr p q rfl r x e1
  · push_neg at hℓ
    cases h with
    | bcast hp hidle =>
      rename_i p m
      refine ⟨fun r => hQ _ _ (I.mem r), fun r x hx => ?_, fun p' q' r hr x hx => ?_⟩
      · rcases hx with ⟨p', q', e⟩ | ⟨p', b, e1, e2, e3⟩
        · exact hQ _ _ (I.pend r x (Or.inl ⟨p', q', e⟩))
        · simp only [St.tick, St.doBcast] at e1
          by_cases hpp : p' = p
          · subst hpp; simp only [Function.update_self, Option.some.injEq] at e1
            subst e1; subst e2; subst e3; exact hbc _ _ rfl
          · rw [Function.update_of_ne hpp] at e1
            exact hQ _ _ (I.pend r x (Or.inr ⟨p', b, e1, e2, e3⟩))
      · simp only [St.tick, St.doBcast, mem_addCand, St.key] at hx hr
        rcases hx with e | ⟨e1, e2⟩
        · exact hQ _ _ (I.cand p' q' r hr x e)
        · rw [hr] at e1; cases e1; subst e2; exact hbc _ _ rfl
    | bret hp hb =>
      rename_i p b
      refine ⟨fun r => ?_, fun r x hx => ?_, fun p' q' r hr x hx => ?_⟩
      · simp only [St.tick, St.write]
        by_cases hr : r = ⟨.val, p, b.key, p⟩
        · subst hr; simp only [Function.update_self]
          exact hQ _ _ (I.pend _ _ (Or.inr ⟨p, b, hb, rfl, rfl⟩))
        · rw [Function.update_of_ne hr]; exact hQ _ _ (I.mem r)
      · rcases hx with ⟨p', q', e⟩ | ⟨p', b', e1, e2, e3⟩
        · exact hQ _ _ (I.pend r x (Or.inl ⟨p', q', e⟩))
        · simp only [St.tick] at e1
          by_cases hpp : p' = p
          · subst hpp; simp at e1
          · rw [Function.update_of_ne hpp] at e1
            exact hQ _ _ (I.pend r x (Or.inr ⟨p', b', e1, e2, e3⟩))
      · exact hQ _ _ (I.cand p' q' r hr x hx)
    | bretIdle hp hidle =>
      exact ⟨fun r => hQ _ _ (I.mem r), fun r x hx => hQ _ _ (I.pend r x hx),
        fun p' q' r hr x hx => hQ _ _ (I.cand p' q' r hr x hx)⟩
    | byz hp hr' hv =>
      rename_i p r0 v
      refine ⟨fun r => ?_, fun r x hx => hQ _ _ (I.pend r x hx), fun p' q' r hr x hx => ?_⟩
      · simp only [St.tick, St.write]
        by_cases hr : r = r0
        · subst hr; simp only [Function.update_self]; exact hbyz _ _ _ rfl
        · rw [Function.update_of_ne hr]; exact hQ _ _ (I.mem r)
      · simp only [St.tick, St.write, mem_addCand, St.key] at hx hr
        rcases hx with e | ⟨e1, e2⟩
        · exact hQ _ _ (I.cand p' q' r hr x e)
        · rw [hr] at e1; cases e1; subst e2; exact hbyz _ _ _ rfl
    | _ => exact absurd rfl (hℓ _ _)

end Podc.RDMAAgreement.RB
