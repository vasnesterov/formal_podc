import Papers.PODC2019.RDMAAgreement.RB.Basic

/-!
# Algorithm 2 — local invariants of correct processes

Phases vs. program counters, write-once ghost variables, clock facts.
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

/-- The local view of delivery thread `(p,q)`: its local state and its ghost variables. -/
structure Loc (P M : Type) where
  pc : PC P M
  last : ℕ
  phase : Phase
  scanT : ℕ
  echo : ℕ → Option (Base P M)
  echoT : ℕ → Option ℕ
  l1 : ℕ → Option (Base P M × ℕ)
  dlv : ℕ → Option M

/-- The local view of thread `(p,q)` in state `s`. -/
def St.loc (s : St P M) (p q : P) : Loc P M :=
  ⟨s.pc p q, s.last p q, s.phase p q, s.scanT p q, s.echo p q, s.echoT p q, s.l1 p q, s.dlv p q⟩

/-- Local invariants of a delivery thread of a correct process (`now` = current time). -/
structure ThreadOK (now : ℕ) (l : Loc P M) : Prop where
  ph : ∀ ph, l.pc.ph = some ph → l.phase = ph
  wrEcho : ∀ b, l.pc = .wrEcho b → l.echo (l.last + 1) = some b
  future : ∀ k, l.last + 1 < k → l.echo k = none ∧ l.echoT k = none ∧ l.l1 k = none ∧ l.dlv k = none
  dlvCur : l.dlv (l.last + 1) = none
  wfs : l.phase = .wfs → l.echoT (l.last + 1) = none ∧ l.l1 (l.last + 1) = none ∧
    (l.echo (l.last + 1) = none ∨ ∃ b, l.pc = .wrEcho b)
  wfl1 : l.phase = .wfl1 → l.l1 (l.last + 1) = none ∨ ∃ π, l.pc = .wrL1 π
  echoed : l.phase ≠ .wfs → ∃ e, l.echoT (l.last + 1) = some e
  echoT : ∀ k e, l.echoT k = some e → e < now ∧ l.echo k ≠ none
  scan : ∀ i todo acc, l.pc = .rdVal i todo acc → l.scanT < now
  l1T : ∀ k b sc, l.l1 k = some (b, sc) → sc < now

lemma ThreadOK.mono {now now' : ℕ} {l : Loc P M} (h : ThreadOK now l) (hle : now ≤ now') :
    ThreadOK now' l where
  ph := h.ph
  wrEcho := h.wrEcho
  future := h.future
  dlvCur := h.dlvCur
  wfs := h.wfs
  wfl1 := h.wfl1
  echoed := h.echoed
  echoT k e he := ⟨lt_of_lt_of_le (h.echoT k e he).1 hle, (h.echoT k e he).2⟩
  scan i todo acc hpc := lt_of_lt_of_le (h.scan i todo acc hpc) hle
  l1T k b sc hl := lt_of_lt_of_le (h.l1T k b sc hl) hle

/-- Invariants of the broadcast thread of a correct process. -/
structure BcastOK (bnext : ℕ) (bc : ℕ → Option M) (bpend : Option (Base P M)) (p : P) : Prop where
  bcNone : ∀ k, bnext < k → bc k = none
  bpend : ∀ b, bpend = some b → b.sender = p ∧ b.key = bnext ∧ bc b.key = some b.msg

/-- Local invariants of correct processes. -/
structure InvA (F : Finset P) (s : St P M) : Prop where
  thr : ∀ p ∉ F, ∀ q, ThreadOK s.now (s.loc p q)
  bcast : ∀ p ∉ F, BcastOK (s.bnext p) (s.bc p) (s.bpend p) p

/-- Frame lemma: a step of thread `(p,q)` changes no other thread's local view and no broadcast
state. -/
lemma Step.frame_thr {s s' : St P M} {p q : P} (h : Step F f s (.thr p q) s') :
    (∀ p' q', ¬ (p' = p ∧ q' = q) → s'.loc p' q' = s.loc p' q') ∧ s'.now = s.now + 1 ∧
      s'.bnext = s.bnext ∧ s'.bc = s.bc ∧ s'.bpend = s.bpend := by
  refine ⟨fun p' q' hne => ?_, ?_⟩
  · have hne' : ∀ k, ¬ (p' = p ∧ q' = q ∧ k = s.key p q) := fun k h => hne ⟨h.1, h.2.1⟩
    cases h <;> simp [St.loc, St.tick, St.write, St.sign, St.deliver, St.setPhase, hne]
  · cases h <;> simp [St.tick, St.write, St.sign, St.deliver, St.setPhase]

/-- Non-thread steps change no thread's local view. -/
lemma Step.frame_other {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s')
    (hℓ : ∀ p q, ℓ ≠ .thr p q) : (∀ p' q', s'.loc p' q' = s.loc p' q') ∧ s'.now = s.now + 1 := by
  cases h <;> first | exact absurd rfl (hℓ _ _) | simp [St.loc, St.tick, St.write, St.doBcast]

lemma InvA.init [Inhabited P] : InvA F (St.init : St P M) := by
  constructor
  · intro p _ q; constructor <;> intros <;> simp_all [St.init, St.loc, PC.start, PC.ph]
  · intro p _; constructor <;> intros <;> simp_all [St.init]

/-- Changing only the program counter (and the clock) preserves the local invariants, under
side conditions on the old and new program counters. -/
lemma ThreadOK.setPc {now : ℕ} {l : Loc P M} (I : ThreadOK now l) (c : PC P M)
    (hph : ∀ ph, c.ph = some ph → l.phase = ph)
    (hold1 : ∀ b, l.pc ≠ .wrEcho b) (hold2 : ∀ π, l.pc ≠ .wrL1 π)
    (hnew1 : ∀ b, c ≠ .wrEcho b) (hnew2 : ∀ π, c ≠ .wrL1 π)
    (hscan : ∀ i todo acc, c = .rdVal i todo acc → l.scanT < now + 1) :
    ThreadOK (now + 1) { l with pc := c } where
  ph := hph
  wrEcho b h := absurd h (hnew1 b)
  future := I.future
  dlvCur := I.dlvCur
  wfs h := by
    obtain ⟨h1, h2, h3⟩ := I.wfs h
    refine ⟨h1, h2, ?_⟩
    rcases h3 with h3 | ⟨b, hb⟩
    · exact Or.inl h3
    · exact absurd hb (hold1 b)
  wfl1 h := by
    rcases I.wfl1 h with h' | ⟨π, hπ⟩
    · exact Or.inl h'
    · exact absurd hπ (hold2 π)
  echoed := I.echoed
  echoT k e he := ⟨Nat.lt_succ_of_lt (I.echoT k e he).1, (I.echoT k e he).2⟩
  scan := hscan
  l1T k b sc hl := Nat.lt_succ_of_lt (I.l1T k b sc hl)

lemma ThreadOK.of_eq {n n' : ℕ} {l l' : Loc P M} (h : ThreadOK n l) (hn : n = n') (hl : l = l') :
    ThreadOK n' l' := hn ▸ hl ▸ h

/-- The local invariants are preserved by the step of the thread itself. -/
lemma ThreadOK.step {s s' : St P M} {p q : P} (h : Step F f s (.thr p q) s')
    (I : ThreadOK s.now (s.loc p q)) : ThreadOK s'.now (s'.loc p q) := by
  have I' := I
  obtain ⟨I1, I2, I3, I4, I5, I6, I7, I8, I9, I10⟩ := I'
  simp only [St.loc] at I1 I2 I3 I4 I5 I6 I7 I8 I9 I10
  cases h with
  | @l2Found _ _ i todo v ρ m hp hpc hv hρ hval =>
    exact (I.setPc (.wrCopy ρ m) (by simp [PC.ph]) (by simp [St.loc, hpc]) (by simp [St.loc, hpc])
      (by simp) (by simp) (by simp)).of_eq (by simp [St.tick]) (by simp [St.loc, St.tick])
  | @l2Next _ _ i j todo v hp hpc hv hnv hj =>
    exact (I.setPc (.rdL2 j (todo.erase j)) (by simp [PC.ph]) (by simp [St.loc, hpc])
      (by simp [St.loc, hpc]) (by simp) (by simp) (by simp)).of_eq (by simp [St.tick])
      (by simp [St.loc, St.tick])
  | @l2EndS _ _ i v hp hpc hv hnv hph =>
    exact (I.setPc .rdSnd (by simp [PC.ph, St.loc, hph]) (by simp [St.loc, hpc])
      (by simp [St.loc, hpc]) (by simp) (by simp) (by simp)).of_eq (by simp [St.tick])
      (by simp [St.loc, St.tick])
  | @l2EndL _ _ i j v hp hpc hv hnv hph =>
    exact (I.setPc (.rdL1 j (Finset.univ.erase j) ∅) (by simp [PC.ph, St.loc, hph])
      (by simp [St.loc, hpc]) (by simp [St.loc, hpc]) (by simp) (by simp) (by simp)).of_eq
      (by simp [St.tick]) (by simp [St.loc, St.tick])
  | @sndBad _ _ j v hp hpc hv hbad =>
    exact (I.setPc (PC.start j) (by simp [PC.ph, PC.start]) (by simp [St.loc, hpc])
      (by simp [St.loc, hpc]) (by simp [PC.start]) (by simp [PC.start])
      (by simp [PC.start])).of_eq (by simp [St.tick]) (by simp [St.loc, St.tick])
  | @valNext _ _ i j todo acc v hp hpc hv hj =>
    have hph := I1 .wfl1 (by simp [hpc, PC.ph])
    exact (I.setPc (.rdVal j (todo.erase j) (addVal i q (s.key p q) v acc))
      (by simp [PC.ph, St.loc, hph]) (by simp [St.loc, hpc]) (by simp [St.loc, hpc]) (by simp)
      (by simp) (fun _ _ _ _ => Nat.lt_succ_of_lt (I9 _ _ _ hpc))).of_eq (by simp [St.tick])
      (by simp [St.loc, St.tick])
  | @valBad _ _ i j acc v hp hpc hv hbad =>
    exact (I.setPc (PC.start j) (by simp [PC.ph, PC.start]) (by simp [St.loc, hpc])
      (by simp [St.loc, hpc]) (by simp [PC.start]) (by simp [PC.start])
      (by simp [PC.start])).of_eq (by simp [St.tick]) (by simp [St.loc, St.tick])
  | @l1Next _ _ i j todo acc v hp hpc hv hj =>
    have hph := I1 .wfl2 (by simp [hpc, PC.ph])
    exact (I.setPc (.rdL1 j (todo.erase j) (addL1 v acc)) (by simp [PC.ph, St.loc, hph])
      (by simp [St.loc, hpc]) (by simp [St.loc, hpc]) (by simp) (by simp) (by simp)).of_eq
      (by simp [St.tick]) (by simp [St.loc, St.tick])
  | @l1Ok _ _ i acc v S m hp hpc hv hS hval =>
    have hph := I1 .wfl2 (by simp [hpc, PC.ph])
    exact (I.setPc (.wrL2 ⟨p, S⟩) (by simp [PC.ph, St.loc, hph])
      (by simp [St.loc, hpc]) (by simp [St.loc, hpc]) (by simp) (by simp) (by simp)).of_eq
      (by simp [St.tick, St.sign]) (by simp [St.loc, St.tick, St.sign])
  | @l1Bad _ _ i j acc v hp hpc hv hbad =>
    exact (I.setPc (PC.start j) (by simp [PC.ph, PC.start]) (by simp [St.loc, hpc])
      (by simp [St.loc, hpc]) (by simp [PC.start]) (by simp [PC.start])
      (by simp [PC.start])).of_eq (by simp [St.tick]) (by simp [St.loc, St.tick])
  | @l2Done _ _ j ρ hp hpc =>
    exact (I.setPc (PC.start j) (by simp [PC.ph, PC.start]) (by simp [St.loc, hpc])
      (by simp [St.loc, hpc]) (by simp [PC.start]) (by simp [PC.start])
      (by simp [PC.start])).of_eq (by simp [St.tick, St.write])
      (by simp [St.loc, St.tick, St.write])
  | @l2EndV _ _ i j v hp hpc hv hnv hph =>
    simp only [St.loc, St.tick, go_pc, go_last, go_phase, go_echo, go_echoT, go_l1, go_dlv,
      go_now, upd2_apply, and_self, ite_true]
    refine ⟨?_, ?_, ?_, I4, ?_, ?_, fun _ => I7 (by simp [hph]), fun k e he => ?_, ?_,
      fun k b sc hl => ?_⟩ <;> try dsimp only at *
    · intro ph h; simp [PC.ph] at h; rw [hph, h]
    · intro b h; simp at h
    · exact I3
    · intro h; simp [hph] at h
    · intro _; rcases I6 hph with h | ⟨π, h⟩
      · exact Or.inl h
      · simp [hpc] at h
    · exact ⟨Nat.lt_succ_of_lt (I8 k e he).1, (I8 k e he).2⟩
    · intros; omega
    · exact Nat.lt_succ_of_lt (I10 k b sc hl)
  | @copyDone _ _ j ρ m hp hpc =>
    simp only [St.loc, St.tick, St.write, St.deliver, St.key, go_pc, go_last, go_phase, go_echo,
      go_echoT, go_l1, go_dlv, go_now, go_scanT, upd2_apply, upd3_apply2, and_self, ite_true]
    refine ⟨?_, ?_, fun k hk => ?_, ?_, fun _ => ?_, ?_, ?_, fun k e he => ?_, ?_,
      fun k b sc hl => ?_⟩ <;> try dsimp only at *
    · intro ph h; simp [PC.ph, PC.start] at h
    · intro b h; simp [PC.start] at h
    · have := I3 k (by omega)
      refine ⟨this.1, this.2.1, this.2.2.1, ?_⟩
      rw [Function.update_of_ne (by omega)]; exact this.2.2.2
    · rw [Function.update_of_ne (by omega)]; exact (I3 _ (by omega)).2.2.2
    · exact ⟨(I3 _ (by omega)).2.1, (I3 _ (by omega)).2.2.1, Or.inl (I3 _ (by omega)).1⟩
    · intro h; simp at h
    · intro h; simp at h
    · exact ⟨Nat.lt_succ_of_lt (I8 k e he).1, (I8 k e he).2⟩
    · intro i t a h; simp [PC.start] at h
    · exact Nat.lt_succ_of_lt (I10 k b sc hl)
  | @sndOk _ _ v c hp hpc hv hc hs hk =>
    have hph : s.phase p q = .wfs := I1 .wfs (by simp [hpc, PC.ph])
    simp only [St.loc, St.tick, St.sign, St.key, go_pc, go_last, go_phase, go_echo,
      go_echoT, go_l1, go_dlv, go_now, go_scanT, upd2_apply, upd3_apply2, and_self, ite_true]
    refine ⟨?_, ?_, fun k hk => ?_, I4, fun _ => ?_, ?_, ?_, fun k e he => ?_, ?_,
      fun k b sc hl => ?_⟩ <;> try dsimp only at *
    · intro ph h; simp [PC.ph] at h; rw [hph, h]
    · intro b h; simp at h; simp [h]
    · rw [Function.update_of_ne (by omega)]; exact I3 k hk
    · exact ⟨(I5 hph).1, (I5 hph).2.1, Or.inr ⟨_, rfl⟩⟩
    · intro h; simp [hph] at h
    · intro h; exact absurd hph h
    · refine ⟨Nat.lt_succ_of_lt (I8 k e he).1, ?_⟩
      by_cases hkk : k = s.last p q + 1
      · subst hkk; simp
      · rw [Function.update_of_ne hkk]; exact (I8 k e he).2
    · intro i t a h; simp at h
    · exact Nat.lt_succ_of_lt (I10 k b sc hl)
  | @echoDone _ _ j b hp hpc =>
    have hph : s.phase p q = .wfs := I1 .wfs (by simp [hpc, PC.ph])
    simp only [St.loc, St.tick, St.write, St.setPhase, St.key, go_pc, go_last, go_phase, go_echo,
      go_echoT, go_l1, go_dlv, go_now, go_scanT, upd2_apply, upd3_apply2, and_self, ite_true]
    refine ⟨?_, ?_, fun k hk => ?_, I4, fun h => ?_, fun _ => ?_, fun _ => ?_, fun k e he => ?_, ?_,
      fun k b sc hl => ?_⟩ <;> try dsimp only at *
    · intro ph h; simp [PC.ph, PC.start] at h
    · intro b h; simp [PC.start] at h
    · rw [Function.update_of_ne (by omega)]; exact I3 k hk
    · simp at h
    · exact Or.inl (I5 hph).2.1
    · exact ⟨s.now, by simp⟩
    · by_cases hkk : k = s.last p q + 1
      · subst hkk; simp at he; subst he; exact ⟨by omega, by simp [I2 b hpc]⟩
      · rw [Function.update_of_ne hkk] at he
        exact ⟨Nat.lt_succ_of_lt (I8 k e he).1, (I8 k e he).2⟩
    · intro i t a h; simp [PC.start] at h
    · exact Nat.lt_succ_of_lt (I10 k b sc hl)
  | @valOk _ _ i acc v b hp hpc hv hcard hb =>
    have hph : s.phase p q = .wfl1 := I1 .wfl1 (by simp [hpc, PC.ph])
    simp only [St.loc, St.tick, St.sign, St.key, go_pc, go_last, go_phase, go_echo,
      go_echoT, go_l1, go_dlv, go_now, go_scanT, upd2_apply, upd3_apply2, and_self, ite_true]
    refine ⟨?_, ?_, fun k hk => ?_, I4, fun h => ?_, fun _ => ?_, fun _ => I7 (by simp [hph]),
      fun k e he => ⟨Nat.lt_succ_of_lt (I8 k e he).1, (I8 k e he).2⟩, ?_,
      fun k b' sc hl => ?_⟩ <;> try dsimp only at *
    · intro ph h; simp [PC.ph] at h; rw [hph, h]
    · intro b h; simp at h
    · rw [Function.update_of_ne (by omega)]; exact I3 k hk
    · simp [hph] at h
    · exact Or.inr ⟨_, rfl⟩
    · intro i t a h; simp at h
    · by_cases hkk : k = s.last p q + 1
      · subst hkk; simp at hl; have := I9 _ _ _ hpc; omega
      · rw [Function.update_of_ne hkk] at hl; exact Nat.lt_succ_of_lt (I10 k b' sc hl)
  | @l1Done _ _ j π hp hpc =>
    have hph : s.phase p q = .wfl1 := I1 .wfl1 (by simp [hpc, PC.ph])
    simp only [St.loc, St.tick, St.write, St.setPhase, St.key, go_pc, go_last, go_phase, go_echo,
      go_echoT, go_l1, go_dlv, go_now, go_scanT, upd2_apply, upd3_apply2, and_self, ite_true]
    refine ⟨?_, ?_, I3, I4, fun h => ?_, fun h => ?_, fun _ => I7 (by simp [hph]),
      fun k e he => ⟨Nat.lt_succ_of_lt (I8 k e he).1, (I8 k e he).2⟩, ?_,
      fun k b sc hl => Nat.lt_succ_of_lt (I10 k b sc hl)⟩ <;> try dsimp only at *
    · intro ph h; simp [PC.ph, PC.start] at h
    · intro b h; simp [PC.start] at h
    · simp at h
    · simp at h
    · intro i t a h; simp [PC.start] at h

end Podc.RDMAAgreement.RB

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

lemma InvA.step {s s' : St P M} {ℓ : Label P M} (I : InvA F s) (h : Step F f s ℓ s') :
    InvA F s' := by
  constructor
  · intro p' hp' q'
    by_cases hℓ : ∃ p q, ℓ = .thr p q
    · obtain ⟨p, q, rfl⟩ := hℓ
      obtain ⟨hfr, hnow, -⟩ := h.frame_thr
      by_cases hpq : p' = p ∧ q' = q
      · obtain ⟨rfl, rfl⟩ := hpq
        exact ThreadOK.step h (I.thr p' hp' q')
      · rw [hfr p' q' hpq, hnow]; exact (I.thr p' hp' q').mono (Nat.le_succ _)
    · push_neg at hℓ
      obtain ⟨hfr, hnow⟩ := h.frame_other hℓ
      rw [hfr p' q', hnow]; exact (I.thr p' hp' q').mono (Nat.le_succ _)
  · intro p' hp'
    have B := I.bcast p' hp'
    cases h with
    | bcast hp hidle =>
      rename_i p m
      simp only [St.tick, St.doBcast]
      by_cases hpp : p' = p
      · subst hpp
        constructor
        · intro k hk; simp only [Function.update_self] at hk ⊢
          rw [Function.update_of_ne (by omega)]; exact B.bcNone k (by omega)
        · intro b hb; simp only [Function.update_self, Option.some.injEq] at hb ⊢
          subst hb; simp
      · simpa [Function.update_of_ne hpp] using B
    | bret hp hb =>
      rename_i p b
      simp only [St.tick, St.write]
      by_cases hpp : p' = p
      · subst hpp; exact ⟨B.bcNone, by simp⟩
      · simpa [Function.update_of_ne hpp] using B
    | byz => simpa [St.tick, St.write] using B
    | bretIdle => simpa [St.tick] using B
    | _ =>
      simpa [St.tick, St.write, St.sign, St.deliver, St.setPhase] using B

lemma InvA.reach [Inhabited P] {s : St P M} (h : Reachable F f s) : InvA F s := by
  induction h with
  | init => exact InvA.init
  | step _ hs ih => exact ih.step hs

end Podc.RDMAAgreement.RB
