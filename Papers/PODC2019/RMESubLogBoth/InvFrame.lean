import Papers.PODC2019.RMESubLogBoth.InvBasic

/-!
# Frame lemmas: steps that do not change the view of the queue
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation

section
variable {c c' : Cfg k} {own : ℕ → ℕ}

lemma AttachBr_congr (hp : c'.pred = c.pred) (t : Option (List ℕ)) :
    AttachBr c' t ↔ AttachBr c t := by
  simp only [AttachBr, hp]

lemma ScanInv.of_eq {q : Fin k} {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {i : ℕ}
    {EA : Set ℕ} (h : ScanInv c own q x tl V E i EA)
    (h13 : ∀ j a, c'.pc j = .l13 a → c.pc j = .l13 a)
    (hnode : c'.node = c.node) (hpred : c'.pred = c.pred) (hcsig : c'.csig = c.csig)
    (htail : c'.tail = c.tail) (hnxt : c'.nxt = c.nxt) (hvp : ∀ j, c'.vp j = c.vp j)
    (hnn : ∀ a, c.nn a = true → c'.nn a = true) : ScanInv c' own q x tl V E i EA := by
  have hBh := Bh_congr hnode hvp
  have hRel := Rel_congr hpred hcsig
  refine
    { tlEA := h.tlEA, xEA := h.xEA
      EAlt := by rw [hnxt]; exact h.EAlt
      tail := by rw [htail]; exact h.tail
      bhLate := by rw [hBh]; exact h.bhLate
      bhEarly := by rw [hBh]; exact h.bhEarly
      lateIO := by rw [hpred]; exact h.lateIO
      l13Late := fun j a hj => h.l13Late j a (h13 j a hj)
      Vlt := by rw [hnxt]; exact h.Vlt
      Vl13 := fun v hv j hj => h.Vl13 v hv j (h13 j v hj)
      Esrc := h.Esrc, Etgt := h.Etgt
      E1 := by rw [hpred, hRel]; exact h.E1
      E2 := by rw [hBh]; exact h.E2
      Etail := by rw [htail]; exact h.Etail
      El13 := fun u v j he hj => h.El13 u v j he (h13 j v hj)
      Ein := h.Ein, Eown := h.Eown, Eout := h.Eout, EEA := h.EEA, Eacyc := h.Eacyc
      scanned := by
        intro j hj a ha
        rw [hnode] at ha
        rcases h.scanned j hj a ha with h1 | ⟨h1, h2, h3⟩
        · exact .inl h1
        · exact .inr ⟨h1, hnn a h2, by rw [hvp]; exact h3⟩ }

lemma PathInv.of_eq {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {EA : Set ℕ}
    {mpath : List ℕ} {tpath hpath : Option (List ℕ)} {done : List (List ℕ)}
    (h : PathInv c x tl V E EA mpath tpath hpath done)
    (hpred : c'.pred = c.pred) (hInH : c'.InH = c.InH) :
    PathInv c' x tl V E EA mpath tpath hpath done := by
  refine ⟨h.mp, h.tpIn, h.tpOut, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨h1, h2, h3⟩ := h.hp σ hσ
    refine ⟨h1, by rw [hpred]; exact h2, ?_⟩
    rw [AttachBr_congr hpred, hpred, hInH]; exact h3
  · rw [hpred]; exact h.visited

/-- Local invariants of other ports survive steps that do not change the view of the queue. -/
lemma LI.of_eq {q : Fin k} (h : LI c own q) (hpc : c'.pc q = c.pc q)
    (h13 : ∀ j a, c'.pc j = .l13 a → c.pc j = .l13 a)
    (hnode : c'.node = c.node) (hpred : c'.pred = c.pred) (hcsig : c'.csig = c.csig)
    (htail : c'.tail = c.tail) (hnxt : c'.nxt = c.nxt) (hvp : ∀ j, c'.vp j = c.vp j)
    (hnn : ∀ a, c.nn a = true → c'.nn a = true)
    (hnnq : ∀ y, c.node q = some y → c'.nn y = c.nn y) : LI c' own q := by
  have hBh := Bh_congr hnode hvp
  have hRel := Rel_congr hpred hcsig
  have hInH := InH_congr hnode hvp hpred hcsig htail
  unfold LI at h ⊢
  rw [hpc]
  have SI := fun {x tl V E i EA} (hs : ScanInv c own q x tl V E i EA) =>
    hs.of_eq h13 hnode hpred hcsig htail hnxt hvp hnn
  cases hq : c.pc q with
  | rem => rw [hq] at h; rwa [hnode]
  | l10 => trivial
  | l11 => rw [hq] at h; rwa [hnode]
  | l13 y =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1], by rwa [hcsig],
      by rwa [hBh], by rwa [htail]⟩
  | l14 y m =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1], by rwa [hcsig]⟩
  | l15 y m =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1], by rwa [hcsig]⟩
  | l18 y => rw [hq] at h; rwa [hnode]
  | l18w y => rw [hq] at h; rwa [hnode, hpred]
  | l19 y => rw [hq] at h; rwa [hnode, hpred]
  | l22a y => rw [hq] at h; rwa [hnode, hpred]
  | l22b => rw [hq] at h; rwa [hnode, hRel]
  | l23 y v => rw [hq] at h; rwa [hnode, hpred]
  | l24 y v =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], h3, by rwa [hnnq y h1]⟩
  | l30 y v =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], h3, by rwa [hnnq y h1]⟩
  | l31 y =>
    rw [hq] at h; obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1]⟩
  | l33 y tl V E i =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4, EA, h5⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1], h4, EA, SI h5⟩
  | l35 y tl V E i a =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4, EA, h5, h6, h7, h8⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1], h4, EA, SI h5, h6,
      by rwa [hnxt], by rwa [hnode]⟩
  | l36 y tl V E i a =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4, EA, h5, h6, h7, h8, h9⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1], h4, EA, SI h5, h6,
      by rwa [hnxt], hnn a h8, by rwa [hnode]⟩
  | l39 y tl V E =>
    rw [hq] at h; obtain ⟨h1, h2, h3, EA, h5⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1], EA, SI h5⟩
  | l42 y tl V E mp tp hp dn =>
    rw [hq] at h; obtain ⟨h1, h2, h3, EA, h5, h6⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1], EA, SI h5, h6.of_eq hpred hInH⟩
  | l43 y tl V E mp tp hp dn σ =>
    rw [hq] at h; obtain ⟨h1, h2, h3, EA, h5, h6, h7, h8⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1], EA, SI h5,
      h6.of_eq hpred hInH, h7, h8⟩
  | l44 y tl V E mp tp hp dn σ =>
    rw [hq] at h; obtain ⟨h1, h2, h3, EA, h5, h6, h7, h8, h9⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1], EA, SI h5,
      h6.of_eq hpred hInH, h7, h8, by rwa [hpred]⟩
  | l46 y tl V E mp tp hp =>
    rw [hq] at h; obtain ⟨h1, h2, h3, EA, h5, h6, h7⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1], EA, SI h5,
      h6.of_eq hpred hInH, by rwa [AttachBr_congr hpred, hInH]⟩
  | l47 y s =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4, h5, h7, h8, h9, h10⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1], by rwa [hBh], by rwa [htail],
      by rwa [hnxt], fun j hj => h8 j (h13 j s hj), by rwa [hBh, htail],
      by rwa [hpred]⟩
  | l49 y m =>
    rw [hq] at h; obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1]⟩
  | rx y v =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], h3, by rwa [hnnq y h1]⟩
  | l25 y v =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], h3, by rwa [hnnq y h1]⟩
  | l26 y =>
    rw [hq] at h; obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred, hRel], by rwa [hnnq y h1]⟩
  | cs y =>
    rw [hq] at h; obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hnnq y h1]⟩
  | l28 y =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [hpred], by rwa [hcsig], by rwa [hnnq y h1]⟩
  | l29 => rw [hq] at h; rwa [hnode, hRel]

/-- `Glob` survives steps that do not change the view of the queue. -/
lemma Glob.of_eq (h : Glob c own) (hnode : c'.node = c.node) (hpred : c'.pred = c.pred)
    (hcsig : c'.csig = c.csig) (htail : c'.tail = c.tail) (hnxt : c'.nxt = c.nxt)
    (hvp : ∀ j, c'.vp j = c.vp j) (hnn : ∀ a, c'.nn a = true ↔ c.nn a = true)
    (hhold : ∀ q, (c'.pc q).InR → c'.holder = some q) : Glob c' own := by
  have hBh := Bh_congr hnode hvp
  have hRel := Rel_congr hpred hcsig
  have hInH := InH_congr hnode hvp hpred hcsig htail
  refine
    { own := by rw [hnode]; exact h.own
      nodeLt := by rw [hnode, hnxt]; exact h.nodeLt
      fresh := by
        intro a ha; rw [hnxt] at ha; obtain ⟨h1, h2, h3⟩ := h.fresh a ha
        refine ⟨by rw [hpred]; exact h1, ?_, by rw [hcsig]; exact h3⟩
        cases h4 : c'.nn a
        · rfl
        · rw [(hnn a).mp h4] at h2; cases h2
      special := by rw [hpred, hcsig]; exact ⟨h.special.1, h.special.2.1, (hnn _).mpr h.special.2.2⟩
      nxtPos := by rw [hnxt]; exact h.nxtPos
      table := by rw [hnxt, Act_congr hnode, hRel]; exact h.table
      nnPred := fun a ha => by rw [hpred]; exact h.nnPred a ((hnn a).mp ha)
      csigPred := by rw [hcsig, hpred]; exact h.csigPred
      ioNN := fun a ha => (hnn a).mpr (h.ioNN a (by rwa [hpred] at ha))
      tailLt := by rw [htail, hnxt]; exact h.tailLt
      bhLt := by rw [hBh, hnxt]; exact h.bhLt
      bhInj := by rw [hBh]; exact h.bhInj
      noBhTail := by rw [hBh, htail]; exact h.noBhTail
      hUniq := by rw [hInH]; exact h.hUniq
      relTail := by rw [hRel, htail, hInH]; exact h.relTail
      wf := by rw [hBh]; exact h.wf
      holder := hhold }

end

end Podc.RMESubLogBoth
