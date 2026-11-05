import Papers.PODC2019.RMESubLogBoth.InvDerived

/-!
# Transfer lemmas for steps of processes other than the repairer

Generic lemmas used to show that the local invariant `LI` of a port `q` survives a step of
another port `p` (or a crash), and the corresponding facts about the repairer's view
(`ScanInv`, `PathInv`).

`PredStep c c'` describes how `Pred` fields may change in such a step: unchanged, written from
`NIL` (to a value other than `&InCS`/`&Exit`), `&InCS → &Exit` (line 27), or `node m → &InCS`
where `m` is released (line 26).
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation

lemma PV.isInOut_iff (v : PV) : v.isInOut = true ↔ v = .incs ∨ v = .exit := by
  cases v <;> simp [PV.isInOut]

/-- How `Pred` fields may change in a step of a process that is not the repairer. -/
def PredStep (c c' : Cfg k) : Prop :=
  ∀ a, c'.pred a = c.pred a ∨ (c.pred a = .nil ∧ c'.pred a ≠ .incs ∧ c'.pred a ≠ .exit) ∨
    (c.pred a = .incs ∧ c'.pred a = .exit) ∨
    (∃ m, c.pred a = .node m ∧ c.Bh a m ∧ c.Rel m ∧ c'.pred a = .incs)

/-- The `Bh`-related facts of `ScanInv` in the new configuration. -/
structure ScanBh (c c' : Cfg k) (tl : ℕ) (E : Finset (ℕ × ℕ)) (EA : Set ℕ) : Prop where
  tail : c'.tail = tl ∨ c'.tail ∉ EA
  bhLate : ∀ a b, c'.Bh a b → a ∉ EA → b = tl ∨ b ∉ EA
  bhEarly : ∀ a b, c'.Bh a b → a ∈ EA → b ∈ EA
  E2 : ∀ u v w, (u, v) ∈ E → c'.Bh w v → w = u
  Etail : ∀ u v, (u, v) ∈ E → v ≠ c'.tail
  vp : ∀ (j : Fin k) a v, c'.node j = some a → a ∈ EA → c'.vp j = .node v → c.vp j = .node v

section
variable {c c' : Cfg k}

lemma PredStep.of_eq (h : c'.pred = c.pred) : PredStep c c' := fun a => .inl (by rw [h])

lemma PredStep.exit (h : PredStep c c') {a : ℕ} (ha : c.pred a = .exit) : c'.pred a = .exit := by
  rcases h a with h1 | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨m, h1, -⟩
  · rw [h1, ha]
  all_goals rw [ha] at h1; cases h1

lemma PredStep.crash (h : PredStep c c') {a : ℕ} (ha : c.pred a = .crash) :
    c'.pred a = .crash := by
  rcases h a with h1 | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨m, h1, -⟩
  · rw [h1, ha]
  all_goals rw [ha] at h1; cases h1

lemma PredStep.io (h : PredStep c c') {a : ℕ} (ha : c.pred a = .incs ∨ c.pred a = .exit) :
    c'.pred a = .incs ∨ c'.pred a = .exit := by
  rcases h a with h1 | ⟨h1, -⟩ | ⟨-, h1⟩ | ⟨m, -, -, -, h1⟩
  · rw [h1]; exact ha
  · rcases ha with ha | ha <;> rw [ha] at h1 <;> cases h1
  · exact .inr h1
  · exact .inl h1

lemma PredStep.isInOut (h : PredStep c c') {a : ℕ} (ha : (c.pred a).isInOut = true) :
    (c'.pred a).isInOut = true := by
  rw [PV.isInOut_iff] at ha ⊢; exact h.io ha

lemma PredStep.io_back (h : PredStep c c') {a : ℕ}
    (ha : c'.pred a = .incs ∨ c'.pred a = .exit) :
    (c.pred a = .incs ∨ c.pred a = .exit) ∨ ∃ m, c.pred a = .node m ∧ c.Bh a m ∧ c.Rel m := by
  rcases h a with h1 | ⟨-, h1, h2⟩ | ⟨h1, -⟩ | ⟨m, h1, h2, h3, -⟩
  · rw [h1] at ha; exact .inl ha
  · rcases ha with ha | ha
    · exact absurd ha h1
    · exact absurd ha h2
  · exact .inl (.inl h1)
  · exact .inr ⟨m, h1, h2, h3⟩

lemma PredStep.node (h : PredStep c c') {a b : ℕ} (ha : c.pred a = .node b) :
    c'.pred a = .node b ∨ (c'.pred a = .incs ∧ c.Rel b) := by
  rcases h a with h1 | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨m, h1, -, h3, h4⟩
  · exact .inl (h1.trans ha)
  · rw [ha] at h1; cases h1
  · rw [ha] at h1; cases h1
  · rw [ha] at h1; cases h1; exact .inr ⟨h4, h3⟩

lemma PredStep.attachBr (h : PredStep c c') {t : Option (List ℕ)} (ht : AttachBr c' t) :
    AttachBr c t := by
  obtain ⟨τ, h1, h2⟩ := ht
  refine ⟨τ, h1, ?_⟩
  cases h3 : (c.pred (pend τ)).isInOut
  · rfl
  · rw [h.isInOut h3] at h2; cases h2

/-- `Pred`-chains ending at a node with `Pred = &Crash` survive. -/
lemma PredStep.PL (h : PredStep c c') {s y : ℕ}
    (hc : ReflTransGen (fun a b => c.pred a = .node b) s y) (hy : c.pred y = .crash) :
    ReflTransGen (fun a b => c'.pred a = .node b) s y := by
  induction hc using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a b e1 rest ih =>
    rcases h.node e1 with h1 | ⟨-, h1⟩
    · exact .head h1 ih
    · exfalso
      rcases ReflTransGen.cases_head rest with h2 | ⟨d, h2, -⟩
      · subst h2; have := h1.1; rw [hy] at this; cases this
      · rw [h1.1] at h2; cases h2

lemma not_rel_of_PL {s y : ℕ} (hc : ReflTransGen (fun a b => c.pred a = .node b) s y)
    (hy : c.pred y = .crash) : ¬ c.Rel s := by
  intro hr
  rcases ReflTransGen.cases_head hc with h2 | ⟨d, h2, -⟩
  · subst h2; have := hr.1; rw [hy] at this; cases this
  · rw [hr.1] at h2; cases h2

section
variable {own own' : ℕ → ℕ} {q : Fin k} {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)}
  {i : ℕ} {EA : Set ℕ}

/-- `ScanBh` when `Bh` only shrinks and `Tail` is unchanged. -/
lemma ScanBh.of_sub (h : ScanInv c own q x tl V E i EA) (hBh : ∀ a b, c'.Bh a b → c.Bh a b)
    (htail : c'.tail = c.tail) (hvp : ∀ j v, c'.vp j = .node v → c.vp j = .node v) :
    ScanBh c c' tl E EA where
  tail := htail ▸ h.tail
  bhLate a b hab := h.bhLate a b (hBh a b hab)
  bhEarly a b hab := h.bhEarly a b (hBh a b hab)
  E2 u v w he hw := h.E2 u v w he (hBh w v hw)
  Etail := htail ▸ h.Etail
  vp j _ v _ _ hv := hvp j v hv

lemma ScanInv.transfer (h : ScanInv c own q x tl V E i EA) (hB : ScanBh c c' tl E EA)
    (hPS : PredStep c c') (hRel : ∀ m, c.Rel m → c'.Rel m)
    (hnxt : c.nxt ≤ c'.nxt) (hown : ∀ a, a < c.nxt → own' a = own a)
    (h13 : ∀ j a, c'.pc j = .l13 a → c.pc j = .l13 a ∨ c.nxt ≤ a)
    (hnodes : ∀ j a, c'.node j = some a → c.node j = some a ∨ c.nxt ≤ a)
    (hnn : ∀ a, c.nn a = true → c'.nn a = true) : ScanInv c' own' q x tl V E i EA where
  tlEA := h.tlEA
  xEA := h.xEA
  EAlt a ha := lt_of_lt_of_le (h.EAlt a ha) hnxt
  tail := hB.tail
  bhLate := hB.bhLate
  bhEarly := hB.bhEarly
  lateIO a ha hio := by
    rcases hPS.io_back hio with h1 | ⟨m, h1, h2, h3⟩
    · exact hPS.exit (h.lateIO a ha h1)
    · rcases h.bhLate a m h2 ha with h4 | h4
      · subst h4; exact hPS.exit h3.1
      · exact hPS.exit (h.lateIO m h4 (.inr h3.1))
  l13Late j a hj := by
    rcases h13 j a hj with h1 | h1
    · exact h.l13Late j a h1
    · exact fun ha => absurd (h.EAlt a ha) (not_lt.mpr h1)
  Vlt v hv := lt_of_lt_of_le (h.Vlt v hv) hnxt
  Vl13 v hv j hj := by
    rcases h13 j v hj with h1 | h1
    · exact h.Vl13 v hv j h1
    · exact absurd (h.Vlt v hv) (not_lt.mpr h1)
  Esrc := h.Esrc
  Etgt := h.Etgt
  E1 u v he := by
    rcases h.E1 u v he with h1 | ⟨h1, h2⟩
    · rcases hPS.node h1 with h3 | ⟨h3, h4⟩
      · exact .inl h3
      · exact .inr ⟨.inl h3, hRel v h4⟩
    · exact .inr ⟨hPS.io h1, hRel v h2⟩
  E2 := hB.E2
  Etail := hB.Etail
  El13 u v j he hj := by
    rcases h13 j v hj with h1 | h1
    · exact h.El13 u v j he h1
    · exact absurd (h.Vlt v (h.Etgt u v he)) (not_lt.mpr h1)
  Ein := h.Ein
  Eown u v he := by rw [hown u (h.Vlt u (h.Esrc u v he))]; exact h.Eown u v he
  Eout := h.Eout
  EEA := h.EEA
  Eacyc := h.Eacyc
  scanned j hj a ha := by
    by_cases haEA : a ∈ EA
    · rcases hnodes j a ha with h1 | h1
      · rcases h.scanned j hj a h1 with h2 | ⟨h2, h3, h4⟩
        · exact .inl h2
        · exact .inr ⟨h2, hnn a h3, fun v hv => h4 v (hB.vp j a v ha haEA hv)⟩
      · exact absurd (h.EAlt a haEA) (not_lt.mpr h1)
    · exact .inl haEA

lemma PathInv.transfer {mp : List ℕ} {tp hp : Option (List ℕ)} {dn : List (List ℕ)}
    (h : PathInv c x tl V E EA mp tp hp dn) (hS : ScanInv c own q x tl V E k EA)
    (hG : Glob c own) (hL : ∀ j, LI c own j) (hPS : PredStep c c')
    (hInH : AttachBr c tp → (∀ y, ¬ c.InH y) → ∀ y, ¬ c'.InH y)
    (hcs : ∀ σ, hp = some σ → c.pred (pstart σ) = .incs → c'.pred (pstart σ) = .exit →
      AttachBr c tp → ∀ y, ¬ c'.InH y) :
    PathInv c' x tl V E EA mp tp hp dn := by
  refine ⟨h.mp, h.tpIn, h.tpOut, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨h1, h2, h3⟩ := h.hp σ hσ
    refine ⟨h1, hPS.isInOut h2, fun hA he => ?_⟩
    have hA' := hPS.attachBr hA
    rcases hPS (pstart σ) with h4 | ⟨-, -, h4⟩ | ⟨h4, -⟩ | ⟨m, -, -, -, h4⟩
    · rw [h4] at he; exact hInH hA' (h3 hA' he)
    · exact absurd he h4
    · exact hcs σ hσ h4 he hA'
    · rw [h4] at he; cases he
  · intro hn σ hσ hmax hEA hio
    have hV : pend σ ∈ V := hmax.1.2.1 _ (pend_mem hmax.1.1)
    rcases hS.sink_pred hG hL hV hEA hmax.2.2 with h1 | h1 | h1
    · rw [hPS.crash h1] at hio; cases hio
    · exact hPS.exit (h.visited hn σ hσ hmax hEA (by rw [h1]; rfl))
    · exact hPS.exit (h.visited hn σ hσ hmax hEA (by rw [h1]; rfl))

/-- The local invariant of a port `q` survives a step of another process (or a crash), given
the effect of the step on the shared state. -/
lemma LI.transfer (hG : Glob c own) (hL : ∀ j, LI c own j)
    (hpc : c'.pc q = c.pc q) (hnode : c'.node q = c.node q)
    (hpredq : ∀ y, c.node q = some y → c'.pred y = c.pred y)
    (hnnq : ∀ y, c.node q = some y → c'.nn y = c.nn y)
    (hcsigq : ∀ y, c.node q = some y → c'.csig y = c.csig y)
    (hPS : PredStep c c') (hRel : ∀ m, c.Rel m → c'.Rel m)
    (hnxt : c.nxt ≤ c'.nxt) (hown : ∀ a, a < c.nxt → own' a = own a)
    (h13pc : ∀ j a, c'.pc j = .l13 a → c.pc j = .l13 a ∨ c.nxt ≤ a)
    (hnodes : ∀ j a, c'.node j = some a → c.node j = some a ∨ c.nxt ≤ a)
    (hnn : ∀ a, c.nn a = true → c'.nn a = true)
    (h13 : ∀ y, c.pc q = .l13 y → (∀ w, ¬ c.Bh w y) → c.tail ≠ y →
      (∀ w, ¬ c'.Bh w y) ∧ c'.tail ≠ y)
    (hB : (c.pc q).InR → ∀ {x tl V E i EA}, ScanInv c own q x tl V E i EA →
      ScanBh c c' tl E EA)
    (hInH : (c.pc q).InR → ∀ {x tl V E EA mp tp hp dn}, ScanInv c own q x tl V E k EA →
      PathInv c x tl V E EA mp tp hp dn → AttachBr c tp → (∀ y, ¬ c.InH y) →
      ∀ y, ¬ c'.InH y)
    (hcs : (c.pc q).InR → ∀ {x tl V E EA mp tp hp dn}, ScanInv c own q x tl V E k EA →
      PathInv c x tl V E EA mp tp hp dn → ∀ σ, hp = some σ → c.pred (pstart σ) = .incs →
      c'.pred (pstart σ) = .exit → AttachBr c tp → ∀ y, ¬ c'.InH y)
    (h47 : ∀ y s, c.pc q = .l47 y s → (∀ w, ¬ c.Bh w s) → c.tail ≠ s →
      ¬ ReflTransGen c.Bh c.tail y →
      (∀ w, ¬ c'.Bh w s) ∧ c'.tail ≠ s ∧ ¬ ReflTransGen c'.Bh c'.tail y) :
    LI c' own' q := by
  have h := hL q
  unfold LI at h ⊢
  rw [hpc]
  have SI : (c.pc q).InR → ∀ {x tl V E i EA}, ScanInv c own q x tl V E i EA →
      ScanInv c' own' q x tl V E i EA := fun hR _ _ _ _ _ _ hs =>
    hs.transfer (hB hR hs) hPS hRel hnxt hown h13pc hnodes hnn
  have PI : (c.pc q).InR → ∀ {x tl V E EA mp tp hp dn}, ScanInv c own q x tl V E k EA →
      PathInv c x tl V E EA mp tp hp dn → PathInv c' x tl V E EA mp tp hp dn :=
    fun hR _ _ _ _ _ _ _ _ _ hs hp => hp.transfer hs hG hL hPS (hInH hR hs hp) (hcs hR hs hp)
  have hEA : ∀ {x tl V E i EA}, ScanInv c own q x tl V E i EA → ∀ b, (hi : i < k) →
      c'.node ⟨i, hi⟩ = some b → b ∈ EA → c.node ⟨i, hi⟩ = some b := by
    intro x tl V E i EA hs b hi hb hbEA
    rcases hnodes _ b hb with h1 | h1
    · exact h1
    · exact absurd (hs.EAlt b hbEA) (not_lt.mpr h1)
  cases hq : c.pc q with
  | rem => rw [hq] at h; rwa [hnode]
  | l10 => trivial
  | l11 => rw [hq] at h; rwa [hnode]
  | l13 y =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    have := h13 y hq h5 h6
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1], by rwa [hcsigq y h1],
      this.1, this.2⟩
  | l14 y m =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1], by rwa [hcsigq y h1]⟩
  | l15 y m =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1], by rwa [hcsigq y h1]⟩
  | l18 y => rw [hq] at h; rwa [hnode]
  | l18w y => rw [hq] at h; exact ⟨by rw [hnode]; exact h.1, by rw [hpredq y h.1]; exact h.2⟩
  | l19 y => rw [hq] at h; exact ⟨by rw [hnode]; exact h.1, by rw [hpredq y h.1]; exact h.2⟩
  | l22a y => rw [hq] at h; exact ⟨by rw [hnode]; exact h.1, by rw [hpredq y h.1]; exact h.2⟩
  | l22b =>
    rw [hq] at h; obtain ⟨y, h1, h2⟩ := h; exact ⟨y, by rwa [hnode], hRel y h2⟩
  | l23 y v =>
    rw [hq] at h; obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], h3⟩
  | l24 y v =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], h3, by rwa [hnnq y h1]⟩
  | l30 y v =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], h3, by rwa [hnnq y h1]⟩
  | l31 y =>
    rw [hq] at h; obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1]⟩
  | l33 y tl V E i =>
    have hR : (c.pc q).InR := by rw [hq]; trivial
    rw [hq] at h; obtain ⟨h1, h2, h3, h4, EA, h5⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1], h4, EA, SI hR h5⟩
  | l35 y tl V E i a =>
    have hR : (c.pc q).InR := by rw [hq]; trivial
    rw [hq] at h; obtain ⟨h1, h2, h3, h4, EA, h5, h6, h7, h8⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1], h4, EA, SI hR h5,
      by rw [hown a h7]; exact h6, lt_of_lt_of_le h7 hnxt,
      fun b hi hb hbEA => h8 b hi (hEA h5 b hi hb hbEA) hbEA⟩
  | l36 y tl V E i a =>
    have hR : (c.pc q).InR := by rw [hq]; trivial
    rw [hq] at h; obtain ⟨h1, h2, h3, h4, EA, h5, h6, h7, h8, h9⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1], h4, EA, SI hR h5,
      by rw [hown a h7]; exact h6, lt_of_lt_of_le h7 hnxt, hnn a h8,
      fun b hi hb hbEA => h9 b hi (hEA h5 b hi hb hbEA) hbEA⟩
  | l39 y tl V E =>
    have hR : (c.pc q).InR := by rw [hq]; trivial
    rw [hq] at h; obtain ⟨h1, h2, h3, EA, h5⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1], EA, SI hR h5⟩
  | l42 y tl V E mp tp hp dn =>
    have hR : (c.pc q).InR := by rw [hq]; trivial
    rw [hq] at h; obtain ⟨h1, h2, h3, EA, h5, h6⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1], EA, SI hR h5,
      PI hR h5 h6⟩
  | l43 y tl V E mp tp hp dn σ =>
    have hR : (c.pc q).InR := by rw [hq]; trivial
    rw [hq] at h; obtain ⟨h1, h2, h3, EA, h5, h6, h7, h8⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1], EA, SI hR h5,
      PI hR h5 h6, h7, h8⟩
  | l44 y tl V E mp tp hp dn σ =>
    have hR : (c.pc q).InR := by rw [hq]; trivial
    rw [hq] at h; obtain ⟨h1, h2, h3, EA, h5, h6, h7, h8, h9⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1], EA, SI hR h5,
      PI hR h5 h6, h7, h8, hPS.isInOut h9⟩
  | l46 y tl V E mp tp hp =>
    have hR : (c.pc q).InR := by rw [hq]; trivial
    rw [hq] at h; obtain ⟨h1, h2, h3, EA, h5, h6, h7⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1], EA, SI hR h5,
      PI hR h5 h6, fun hA hn => hInH hR h5 h6 (hPS.attachBr hA) (h7 (hPS.attachBr hA) hn)⟩
  | l47 y s =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    obtain ⟨h4', h5', h8'⟩ := h47 y s hq h4 h5 h8
    refine ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1], h4', h5',
      lt_of_lt_of_le h6 hnxt, ?_, h8', hPS.PL h9 h2⟩
    intro j hj
    rcases h13pc j s hj with h10 | h10
    · exact h7 j h10
    · exact absurd h6 (not_lt.mpr h10)
  | l49 y m =>
    rw [hq] at h; obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1]⟩
  | rx y v =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], h3, by rwa [hnnq y h1]⟩
  | l25 y v =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], h3, by rwa [hnnq y h1]⟩
  | l26 y =>
    rw [hq] at h; obtain ⟨h1, ⟨m, h2, h2'⟩, h3⟩ := h
    exact ⟨by rwa [hnode], ⟨m, by rwa [hpredq y h1], hRel m h2'⟩, by rwa [hnnq y h1]⟩
  | cs y =>
    rw [hq] at h; obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hnnq y h1]⟩
  | l28 y =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpredq y h1], by rwa [hcsigq y h1], by rwa [hnnq y h1]⟩
  | l29 => rw [hq] at h; obtain ⟨y, h1, h2⟩ := h; exact ⟨y, by rwa [hnode], hRel y h2⟩

end

end


/-! ### The main transfer lemma for local steps -/

section
variable {c c' : Cfg k} {own : ℕ → ℕ}

lemma rtg_mono_sub {r r' : ℕ → ℕ → Prop} (h : ∀ a b, r' a b → r a b) {u v : ℕ}
    (hr : ReflTransGen r' u v) : ReflTransGen r u v := by
  induction hr with
  | refl => exact .refl
  | tail _ e ih => exact .tail ih (h _ _ e)

/-- The invariant survives a step of `p` that changes only the fields of `p`'s node `x`,
the program counter of `p` and possibly `holder`, provided `Bh` only shrinks. -/
lemma inv_of_local (hG : Glob c own) (hL : ∀ j, LI c own j)
    {p : Fin k} {x : ℕ} (hn : c.node p = some x)
    (hnodeq : ∀ j, j ≠ p → c'.node j = c.node j)
    (hnodep : c'.node p = c.node p ∨ (c'.node p = none ∧ c.Rel x))
    (hnxt : c'.nxt = c.nxt) (htail : c'.tail = c.tail)
    (hpred : ∀ a, a ≠ x → c'.pred a = c.pred a) (hnnx : ∀ a, a ≠ x → c'.nn a = c.nn a)
    (hcsig : ∀ a, a ≠ x → c'.csig a = c.csig a)
    (hpc : ∀ j, j ≠ p → c'.pc j = c.pc j) (h13p : ∀ a, c'.pc p ≠ .l13 a)
    (hPS : PredStep c c') (hRel : ∀ a, c.Rel a → c'.Rel a)
    (hnn : ∀ a, c.nn a = true → c'.nn a = true)
    (hBh : ∀ a b, c'.Bh a b → c.Bh a b) (hvp : ∀ j v, c'.vp j = .node v → c.vp j = .node v)
    (hnnPx : c'.nn x = true → c'.pred x ≠ .nil) (hcsPx : c'.csig x = true → c'.pred x = .exit)
    (hioNx : (c'.pred x = .incs ∨ c'.pred x = .exit) → c'.nn x = true)
    (hUniq : ∀ y y', c'.InH y → c'.InH y' → y = y')
    (hrelTail : c'.Rel c'.tail → ∀ y, ¬ c'.InH y)
    (hhold : ∀ j, (c'.pc j).InR → c'.holder = some j)
    (hInH : ∀ q, q ≠ p → (c.pc q).InR → ∀ {x tl V E EA mp tp hp dn},
      ScanInv c own q x tl V E k EA → PathInv c x tl V E EA mp tp hp dn → AttachBr c tp →
      (∀ y, ¬ c.InH y) → ∀ y, ¬ c'.InH y)
    (hcs : ∀ q, q ≠ p → (c.pc q).InR → ∀ {x tl V E EA mp tp hp dn},
      ScanInv c own q x tl V E k EA → PathInv c x tl V E EA mp tp hp dn → ∀ σ, hp = some σ →
      c.pred (pstart σ) = .incs → c'.pred (pstart σ) = .exit → AttachBr c tp →
      ∀ y, ¬ c'.InH y)
    (hself : LI c' own p) : Inv c' := by
  have hx0 := hG.nodeLt p x hn
  have hfar : ∀ a, (a = 0 ∨ c.nxt ≤ a) → a ≠ x := by
    rintro a (rfl | ha) rfl
    · omega
    · omega
  have hnsub : ∀ j a, c'.node j = some a → c.node j = some a := by
    intro j a hj
    by_cases hjp : j = p
    · subst hjp
      rcases hnodep with h1 | ⟨h1, -⟩
      · rwa [← h1]
      · rw [h1] at hj; cases hj
    · rwa [← hnodeq j hjp]
  refine ⟨own, ?_, ?_⟩
  · refine
      { own := fun j a hj => hG.own j a (hnsub j a hj)
        nodeLt := fun j a hj => by rw [hnxt]; exact hG.nodeLt j a (hnsub j a hj)
        fresh := by
          intro a ha; rw [hnxt] at ha
          have hax := hfar a (.inr ha)
          rw [hpred a hax, hnnx a hax, hcsig a hax]; exact hG.fresh a ha
        special := by
          have hax := hfar 0 (.inl rfl)
          rw [hpred _ hax, hnnx _ hax, hcsig _ hax]; exact hG.special
        nxtPos := by rw [hnxt]; exact hG.nxtPos
        table := by
          intro a h1 h2; rw [hnxt] at h2
          rcases hG.table a h1 h2 with ⟨j, h3⟩ | h3
          · by_cases hjp : j = p
            · subst hjp
              rcases hnodep with h4 | ⟨-, h4⟩
              · exact .inl ⟨j, by rw [h4, h3]⟩
              · rw [hn] at h3; cases h3; exact .inr (hRel _ h4)
            · exact .inl ⟨j, by rw [hnodeq j hjp, h3]⟩
          · exact .inr (hRel a h3)
        nnPred := by
          intro a ha
          by_cases hax : a = x
          · subst hax; exact hnnPx ha
          · rw [hpred a hax]; rw [hnnx a hax] at ha; exact hG.nnPred a ha
        csigPred := by
          intro a ha
          by_cases hax : a = x
          · subst hax; exact hcsPx ha
          · rw [hpred a hax]; rw [hcsig a hax] at ha; exact hG.csigPred a ha
        ioNN := by
          intro a ha
          by_cases hax : a = x
          · subst hax; exact hioNx ha
          · rw [hnnx a hax]; rw [hpred a hax] at ha; exact hG.ioNN a ha
        tailLt := by rw [htail, hnxt]; exact hG.tailLt
        bhLt := fun y z h => by rw [hnxt]; exact hG.bhLt y z (hBh y z h)
        bhInj := fun y y' z h h' => hG.bhInj y y' z (hBh y z h) (hBh y' z h')
        noBhTail := fun y h => hG.noBhTail y (by rw [← htail]; exact hBh _ _ h)
        hUniq := hUniq
        relTail := hrelTail
        wf := Subrelation.wf (fun {a b} h => hBh b a h) hG.wf
        holder := hhold }
  · intro q
    by_cases hqp : q = p
    · subst hqp; exact hself
    have hyx : ∀ y, c.node q = some y → y ≠ x := by
      rintro y hy rfl; exact hqp (hG.node_inj hy hn)
    refine LI.transfer hG hL (hpc q hqp) (hnodeq q hqp)
      (fun y hy => hpred y (hyx y hy)) (fun y hy => hnnx y (hyx y hy))
      (fun y hy => hcsig y (hyx y hy)) hPS hRel (le_of_eq hnxt.symm) (fun _ _ => rfl) ?_
      (fun j a hj => .inl (hnsub j a hj)) hnn ?_ ?_ (hInH q hqp) (hcs q hqp) ?_
    · intro j a hj
      by_cases hjp : j = p
      · subst hjp; exact absurd hj (h13p a)
      · rw [hpc j hjp] at hj; exact .inl hj
    · intro y _ h1 h2
      exact ⟨fun w hw => h1 w (hBh w y hw), by rwa [htail]⟩
    · intro _ x tl V E i EA hs
      exact ScanBh.of_sub hs hBh htail hvp
    · intro y s _ h1 h2 h3
      refine ⟨fun w hw => h1 w (hBh w s hw), by rwa [htail], fun h4 => h3 ?_⟩
      rw [htail] at h4
      exact rtg_mono_sub hBh h4

end


/-! ### Helpers for the hypotheses of `inv_of_local` -/

section
variable {c c' : Cfg k} {own : ℕ → ℕ}

lemma hInH_of_sub (h : ∀ y, c'.InH y → c.InH y) (p : Fin k) :
    ∀ q, q ≠ p → (c.pc q).InR → ∀ {x tl V E EA mp tp hp dn},
      ScanInv c own q x tl V E k EA → PathInv c x tl V E EA mp tp hp dn → AttachBr c tp →
      (∀ y, ¬ c.InH y) → ∀ y, ¬ c'.InH y :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 y hy => h1 y (h y hy)

lemma hcs_of_incs (h : ∀ a, c.pred a = .incs → c'.pred a ≠ .exit) (p : Fin k) :
    ∀ q, q ≠ p → (c.pc q).InR → ∀ {x tl V E EA mp tp hp dn},
      ScanInv c own q x tl V E k EA → PathInv c x tl V E EA mp tp hp dn → ∀ σ, hp = some σ →
      c.pred (pstart σ) = .incs → c'.pred (pstart σ) = .exit → AttachBr c tp →
      ∀ y, ¬ c'.InH y :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 => absurd h2 (h _ h1)

/-- `vp` of a port other than `p` is unchanged when only `Pred` of `p`'s node changes. -/
lemma vp_eq_other (hG : Glob c own) {p j : Fin k} {x : ℕ} (hx : c.node p = some x)
    (hjp : j ≠ p) (hpc : c'.pc j = c.pc j) (hnode : c'.node j = c.node j)
    (hpred : ∀ a, a ≠ x → c'.pred a = c.pred a) : c'.vp j = c.vp j :=
  vp_congr (by rw [hpc]) hnode (fun y hy => hpred y (fun h => hjp (hG.node_inj hy (h ▸ hx))))

/-- `InH` is unchanged when `Pred` changes only between values other than `&InCS`/`&Exit`. -/
lemma InH_eq_of_pred (hnode : c'.node = c.node) (hBh : c'.Bh = c.Bh) (hRel : c'.Rel = c.Rel)
    (htail : c'.tail = c.tail) (hcsig : c'.csig = c.csig)
    (hpred : ∀ a, c'.pred a = c.pred a ∨ ((c.pred a ≠ .incs ∧ c.pred a ≠ .exit) ∧
      (c'.pred a ≠ .incs ∧ c'.pred a ≠ .exit))) : c'.InH = c.InH := by
  funext y
  simp only [Cfg.InH, Act_congr hnode, hBh, hRel, htail, hcsig]
  rcases hpred y with h | ⟨⟨h1, h2⟩, h3, h4⟩
  · rw [h]
  · simp [h1, h2, h3, h4]

lemma Rel_eq_of_pred (hcsig : c'.csig = c.csig)
    (hpred : ∀ a, c'.pred a = c.pred a ∨ (c.pred a ≠ .exit ∧ c'.pred a ≠ .exit)) :
    c'.Rel = c.Rel := by
  funext y
  simp only [Cfg.Rel, hcsig]
  rcases hpred y with h | ⟨h1, h2⟩
  · rw [h]
  · simp [h1, h2]

end


section
variable {c c' : Cfg k}

lemma Bh_sub_of (hnsub : ∀ j a, c'.node j = some a → c.node j = some a)
    (hvp : ∀ j v, c'.vp j = .node v → c.vp j = .node v) : ∀ a b, c'.Bh a b → c.Bh a b :=
  fun a b ⟨j, h1, h2⟩ => ⟨j, hnsub j a h1, hvp j b h2⟩

lemma vp_eq_all (hnode : c'.node = c.node) (hpred : c'.pred = c.pred)
    (hovr : ∀ j, (c'.pc j).ovr = (c.pc j).ovr) (j : Fin k) : c'.vp j = c.vp j :=
  vp_congr (hovr j) (by rw [hnode]) (fun _ _ => by rw [hpred])

lemma InH_sub_of (hnsub : ∀ j a, c'.node j = some a → c.node j = some a)
    (hBh : ∀ a b, c'.Bh a b → c.Bh a b) (hRel : ∀ z, c'.Rel z → c.Rel z)
    (htail : c'.tail = c.tail) {y : ℕ} (hy : c'.pred y = c.pred y)
    (hcy : c'.csig y = c.csig y) (h : c'.InH y) : c.InH y := by
  obtain ⟨⟨j, hj⟩, h | ⟨z, h1, h2⟩ | ⟨h1, h2, h3⟩⟩ := h
  · exact ⟨⟨j, hnsub j y hj⟩, .inl (hy ▸ h)⟩
  · exact ⟨⟨j, hnsub j y hj⟩, .inr (.inl ⟨z, hBh y z h1, hRel z h2⟩)⟩
  · refine ⟨⟨j, hnsub j y hj⟩, .inr (.inr ⟨hy ▸ h1, hcy ▸ h2, ?_⟩)⟩
    rcases h3 with ⟨w, hw⟩ | h3
    · exact .inl ⟨w, hBh w y hw⟩
    · exact .inr (htail ▸ h3)

end

end Podc.RMESubLogBoth
