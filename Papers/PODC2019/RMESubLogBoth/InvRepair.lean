import Papers.PODC2019.RMESubLogBoth.InvScan

/-!
# The repairer's local steps (lines 31–46) preserve the invariant
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation

section
variable {c : Cfg k} {own : ℕ → ℕ}

lemma ScanInv.setPc {q p : Fin k} {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {i : ℕ}
    {EA : Set ℕ} (h : ScanInv c own q x tl V E i EA) {r : PC k} (ho : r.ovr = (c.pc p).ovr)
    (hr : ∀ a, r ≠ .l13 a) : ScanInv (c.setPc p r) own q x tl V E i EA := by
  refine h.of_eq ?_ rfl rfl rfl rfl rfl (vp_setPc ho) (fun _ h => h)
  intro j a hj
  by_cases hjp : j = p
  · subst hjp; simp at hj; exact absurd hj (hr a)
  · simpa [hjp] using hj

lemma InH_setPc {p : Fin k} {r : PC k} (ho : r.ovr = (c.pc p).ovr) : (c.setPc p r).InH = c.InH :=
  InH_congr rfl (vp_setPc ho) rfl rfl rfl

lemma PathInv.setPc {p : Fin k} {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {EA : Set ℕ}
    {mpath : List ℕ} {tpath hpath : Option (List ℕ)} {dn : List (List ℕ)}
    (h : PathInv c x tl V E EA mpath tpath hpath dn) {r : PC k} (ho : r.ovr = (c.pc p).ovr) :
    PathInv (c.setPc p r) x tl V E EA mpath tpath hpath dn :=
  h.of_eq rfl (InH_setPc ho)

lemma holder_of_pc {hG : Glob c own} {p : Fin k} (h : (c.pc p).InR) : c.holder = some p :=
  hG.holder p h

/-- Line 31. -/
lemma inv_step_l31 (hI : Inv c) (p : Fin k) (x : ℕ) (h : c.pc p = .l31 x) :
    Inv (c.setPc p (.l33 x c.tail ∅ ∅ 0)) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl; obtain ⟨hn, hx, hnn⟩ := hl
  have ho : (PC.l33 x c.tail ∅ ∅ 0 : PC k).ovr = (c.pc p).ovr := by simp [h, PC.ovr]
  refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
  unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
  exact ⟨hn, hx, hnn, Nat.zero_le _, _, (scanInv_init hG hL hn h).setPc ho (by simp)⟩

/-- Lines 32–34. -/
lemma inv_step_l33 (hI : Inv c) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
    (i : ℕ) (h : c.pc p = .l33 x tl V E i) (hi : i < k) :
    Inv (c.setPc p (match c.node ⟨i, hi⟩ with
        | none => .l33 x tl V E (i + 1)
        | some a => .l35 x tl V E i a)) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl; obtain ⟨hn, hx, hnn, -, EA, hS⟩ := hl
  cases hni : c.node ⟨i, hi⟩ with
  | none =>
    have ho : (PC.l33 x tl V E (i + 1) : PC k).ovr = (c.pc p).ovr := by simp [h, PC.ovr]
    refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
    unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
    exact ⟨hn, hx, hnn, hi, EA, (hS.succ_none hi hni).setPc ho (by simp)⟩
  | some a =>
    have ho : (PC.l35 x tl V E i a : PC k).ovr = (c.pc p).ovr := by simp [h, PC.ovr]
    refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
    unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn,
      Cfg.setPc_nxt]
    refine ⟨hn, hx, hnn, hi, EA, hS.setPc ho (by simp), hG.own _ a hni,
      (hG.nodeLt _ a hni).2, fun b h' hb _ => ?_⟩
    rw [hni] at hb; exact (Option.some.inj hb).symm

/-- Line 32: end of the loop. -/
lemma inv_step_l33_end (hI : Inv c) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
    (i : ℕ) (h : c.pc p = .l33 x tl V E i) (hi : k ≤ i) : Inv (c.setPc p (.l39 x tl V E)) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl; obtain ⟨hn, hx, hnn, hik, EA, hS⟩ := hl
  have hik' : i = k := le_antisymm hik hi
  rw [hik'] at hS
  have ho : (PC.l39 x tl V E : PC k).ovr = (c.pc p).ovr := by simp [h, PC.ovr]
  refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
  unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
  exact ⟨hn, hx, hnn, EA, hS.setPc ho (by simp)⟩

/-- Line 35. -/
lemma inv_step_l35 (hI : Inv c) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
    (i a : ℕ) (h : c.pc p = .l35 x tl V E i a) :
    Inv (c.setPc p (if c.nn a then .l36 x tl V E i a else .l35 x tl V E i a)) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl
  obtain ⟨hn, hx, hnn, hi, EA, hS, h1, h2, h3⟩ := hl
  split_ifs with ha
  · have ho : (PC.l36 x tl V E i a : PC k).ovr = (c.pc p).ovr := by simp [h, PC.ovr]
    refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
    unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn,
      Cfg.setPc_nxt]
    exact ⟨hn, hx, hnn, hi, EA, hS.setPc ho (by simp), h1, h2, ha, h3⟩
  · have ho : (PC.l35 x tl V E i a : PC k).ovr = (c.pc p).ovr := by simp [h, PC.ovr]
    refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
    unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn,
      Cfg.setPc_nxt]
    exact ⟨hn, hx, hnn, hi, EA, hS.setPc ho (by simp), h1, h2, h3⟩

/-- Lines 36–38. -/
lemma inv_step_l36 (hI : Inv c) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
    (i a : ℕ) (h : c.pc p = .l36 x tl V E i a) :
    Inv (c.setPc p (.l33 x tl (addV V a (c.pred a)) (addE E a (c.pred a)) (i + 1))) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl
  obtain ⟨hn, hx, hnn, hi, EA, hS, h1, h2, h3, h4⟩ := hl
  have ho : (PC.l33 x tl (addV V a (c.pred a)) (addE E a (c.pred a)) (i + 1) : PC k).ovr =
      (c.pc p).ovr := by simp [h, PC.ovr]
  refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
  unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
  exact ⟨hn, hx, hnn, hi, EA, (hS.add hG hL hi h1 h2 h3 h4 h).setPc ho (by simp)⟩

/-- Lines 39–41. -/
lemma inv_step_l39 (hI : Inv c) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
    (h : c.pc p = .l39 x tl V E) (mpath : List ℕ) (hm : IsMaxPath V E mpath ∧ x ∈ mpath)
    (tpath : Option (List ℕ))
    (ht : (tl ∈ V → ∃ τ, tpath = some τ ∧ IsMaxPath V E τ ∧ tl ∈ τ) ∧
      (tl ∉ V → tpath = none)) :
    Inv (c.setPc p (.l42 x tl V E mpath tpath none [])) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl
  obtain ⟨hn, hx, hnn, EA, hS⟩ := hl
  have ho : (PC.l42 x tl V E mpath tpath none [] : PC k).ovr = (c.pc p).ovr := by simp [h, PC.ovr]
  refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
  unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
  exact ⟨hn, hx, hnn, EA, hS.setPc ho (by simp),
    PathInv.mk hm ht.1 ht.2 (fun σ hσ => by simp at hσ) (fun _ σ hσ => by simp at hσ)⟩

/-- Line 42: visit a new path. -/
lemma inv_step_l42_next (hI : Inv c) (p : Fin k) (x tl : ℕ) (V : Finset ℕ)
    (E : Finset (ℕ × ℕ)) (mpath : List ℕ) (tpath hpath : Option (List ℕ))
    (done : List (List ℕ)) (h : c.pc p = .l42 x tl V E mpath tpath hpath done) (σ : List ℕ)
    (hσ : IsMaxPath V E σ) :
    Inv (c.setPc p (.l43 x tl V E mpath tpath hpath (σ :: done) σ)) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl
  obtain ⟨hn, hx, hnn, EA, hS, hP⟩ := hl
  have ho : (PC.l43 x tl V E mpath tpath hpath (σ :: done) σ : PC k).ovr = (c.pc p).ovr := by
    simp [h, PC.ovr]
  refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
  unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
  exact ⟨hn, hx, hnn, EA, hS.setPc ho (by simp), hP.setPc ho, rfl, hσ⟩

/-- Line 43. -/
lemma inv_step_l43 (hI : Inv c) (p : Fin k) (x tl : ℕ) (V : Finset ℕ)
    (E : Finset (ℕ × ℕ)) (mpath : List ℕ) (tpath hpath : Option (List ℕ))
    (done : List (List ℕ)) (σ : List ℕ) (h : c.pc p = .l43 x tl V E mpath tpath hpath done σ) :
    Inv (c.setPc p (if (c.pred (pend σ)).isInOut then .l44 x tl V E mpath tpath hpath done σ
        else .l42 x tl V E mpath tpath hpath done)) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl
  obtain ⟨hn, hx, hnn, EA, hS, hP, hd, hσ⟩ := hl
  split_ifs with hio
  · have ho : (PC.l44 x tl V E mpath tpath hpath done σ : PC k).ovr = (c.pc p).ovr := by
      simp [h, PC.ovr]
    refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
    unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
    exact ⟨hn, hx, hnn, EA, hS.setPc ho (by simp), hP.setPc ho, hd, hσ, hio⟩
  · have ho : (PC.l42 x tl V E mpath tpath hpath done : PC k).ovr = (c.pc p).ovr := by
      simp [h, PC.ovr]
    refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
    unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
    refine ⟨hn, hx, hnn, EA, hS.setPc ho (by simp), ?_⟩
    have hP' := hP.setPc (p := p) ho
    obtain ⟨d, rfl⟩ : ∃ d, done = σ :: d := by
      cases done with
      | nil => cases hd
      | cons a d => simp at hd; exact ⟨d, by rw [hd]⟩
    refine ⟨hP'.mp, hP'.tpIn, hP'.tpOut, hP'.hp, ?_⟩
    intro hh σ' hσ' hm he hio'
    rcases List.mem_cons.mp hσ' with rfl | hσ'
    · simp at hio' hio; rw [hio] at hio'; cases hio'
    · exact hP'.visited hh σ' hσ' hm he hio'

/-- Lines 44–45. -/
lemma inv_step_l44 (hI : Inv c) (p : Fin k) (x tl : ℕ) (V : Finset ℕ)
    (E : Finset (ℕ × ℕ)) (mpath : List ℕ) (tpath hpath : Option (List ℕ))
    (done : List (List ℕ)) (σ : List ℕ) (h : c.pc p = .l44 x tl V E mpath tpath hpath done σ) :
    Inv (c.setPc p (.l42 x tl V E mpath tpath
        (if c.pred (pstart σ) ≠ .exit then some σ else hpath) done)) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl
  obtain ⟨hn, hx, hnn, EA, hS, hP, hd, hσ, hio⟩ := hl
  obtain ⟨d, rfl⟩ : ∃ d, done = σ :: d := by
    cases done with
    | nil => cases hd
    | cons a d => simp at hd; exact ⟨d, by rw [hd]⟩
  by_cases hs : c.pred (pstart σ) ≠ .exit
  · rw [if_pos hs]
    have ho : (PC.l42 x tl V E mpath tpath (some σ) (σ :: d) : PC k).ovr = (c.pc p).ovr := by
      simp [h, PC.ovr]
    refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
    unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
    refine ⟨hn, hx, hnn, EA, hS.setPc ho (by simp), ?_⟩
    have hP' := hP.setPc (p := p) ho
    simp only [List.tail_cons] at hP'
    refine ⟨hP'.mp, hP'.tpIn, hP'.tpOut, ?_, fun hh => by cases hh⟩
    intro σ' hσ'; cases hσ'
    exact ⟨hσ, by simpa using hio, fun _ h' => absurd h' (by simpa using hs)⟩
  · rw [if_neg hs]
    have ho : (PC.l42 x tl V E mpath tpath hpath (σ :: d) : PC k).ovr = (c.pc p).ovr := by
      simp [h, PC.ovr]
    refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
    unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
    refine ⟨hn, hx, hnn, EA, hS.setPc ho (by simp), ?_⟩
    have hP' := hP.setPc (p := p) ho
    simp only [List.tail_cons] at hP'
    refine ⟨hP'.mp, hP'.tpIn, hP'.tpOut, hP'.hp, ?_⟩
    intro hh σ' hσ' hm he hio'
    rcases List.mem_cons.mp hσ' with rfl | hσ'
    · simpa using hs
    · exact hP'.visited hh σ' hσ' hm he hio'

/-- Line 42: end of the loop. -/
lemma inv_step_l42_end (hI : Inv c) (p : Fin k) (x tl : ℕ) (V : Finset ℕ)
    (E : Finset (ℕ × ℕ)) (mpath : List ℕ) (tpath hpath : Option (List ℕ))
    (done : List (List ℕ)) (h : c.pc p = .l42 x tl V E mpath tpath hpath done)
    (hall : ∀ σ, IsMaxPath V E σ → σ ∈ done) :
    Inv (c.setPc p (.l46 x tl V E mpath tpath hpath)) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl
  obtain ⟨hn, hx, hnn, EA, hS, hP⟩ := hl
  have ho : (PC.l46 x tl V E mpath tpath hpath : PC k).ovr = (c.pc p).ovr := by simp [h, PC.ovr]
  refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
  unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
  have hP' := hP.setPc (p := p) ho
  refine ⟨hn, hx, hnn, EA, hS.setPc ho (by simp),
    ⟨hP'.mp, hP'.tpIn, hP'.tpOut, hP'.hp, fun _ σ hσ => by cases hσ⟩, ?_⟩
  rw [AttachBr_congr rfl, InH_setPc ho]
  intro hA hnone
  subst hnone
  exact hS.none_noH hG hL hP hA hall

/-- Line 46 with `tailpath = NIL`: go to line 47. -/
lemma inv_step_l46_none (hI : Inv c) (p : Fin k) (x tl : ℕ) (V : Finset ℕ)
    (E : Finset (ℕ × ℕ)) (mpath : List ℕ) (hpath : Option (List ℕ))
    (h : c.pc p = .l46 x tl V E mpath none hpath) :
    Inv (c.setPc p (.l47 x (pstart mpath))) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl
  obtain ⟨hn, hx, hnn, EA, hS, hP, -⟩ := hl
  have ho : (PC.l47 x (pstart mpath) : PC k).ovr = (c.pc p).ovr := by simp [h, PC.ovr]
  refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
  have hvp := vp_setPc (c := c) ho
  have hBh := Bh_congr (c := c) (c' := c.setPc p (.l47 x (pstart mpath))) rfl hvp
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := hS.fas_facts hG hL hn hx hP (.inl rfl)
  unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn,
    Cfg.setPc_tail, Cfg.setPc_nxt, hBh]
  refine ⟨hn, hx, hnn, h1, h2, h4, fun j hj => ?_, h6, h7⟩
  by_cases hjp : j = p
  · subst hjp; simp at hj
  · simp [hjp] at hj; exact h5 j hj

/-- Line 46 with `tailpath ≠ NIL`, FAS branch: go to line 47. -/
lemma inv_step_l46_fas (hI : Inv c) (p : Fin k) (x tl : ℕ) (V : Finset ℕ)
    (E : Finset (ℕ × ℕ)) (mpath τ : List ℕ) (hpath : Option (List ℕ))
    (h : c.pc p = .l46 x tl V E mpath (some τ) hpath) (hio : (c.pred (pend τ)).isInOut = true) :
    Inv (c.setPc p (.l47 x (pstart mpath))) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl
  obtain ⟨hn, hx, hnn, EA, hS, hP, -⟩ := hl
  have ho : (PC.l47 x (pstart mpath) : PC k).ovr = (c.pc p).ovr := by simp [h, PC.ovr]
  refine inv_setPc hG hL ho (by simp) (fun _ => hG.holder p (by simp [h, PC.InR])) ?_
  have hvp := vp_setPc (c := c) ho
  have hBh := Bh_congr (c := c) (c' := c.setPc p (.l47 x (pstart mpath))) rfl hvp
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := hS.fas_facts hG hL hn hx hP (.inr ⟨τ, rfl, hio⟩)
  unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn,
    Cfg.setPc_tail, Cfg.setPc_nxt, hBh]
  refine ⟨hn, hx, hnn, h1, h2, h4, fun j hj => ?_, h6, h7⟩
  by_cases hjp : j = p
  · subst hjp; simp at hj
  · simp [hjp] at hj; exact h5 j hj

end

end Podc.RMESubLogBoth
