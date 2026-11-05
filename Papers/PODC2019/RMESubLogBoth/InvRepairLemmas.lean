import Papers.PODC2019.RMESubLogBoth.InvDerived

/-!
# Lemmas for the repairer's decision (lines 39–49)
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation

/-- `Pred`-links: `Pred a = node b`. -/
def Cfg.PL (c : Cfg k) (a b : ℕ) : Prop := c.pred a = .node b

lemma wf_not_transGen {r : ℕ → ℕ → Prop} (hwf : WellFounded (flip r)) (a : ℕ) :
    ¬ TransGen r a a := by
  intro h
  have h' : TransGen (flip r) a a := by
    rw [← transGen_swap]; exact h
  exact (hwf.transGen).irrefl.irrefl a h'

section
variable {c : Cfg k} {own : ℕ → ℕ} {q : Fin k} {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)}
  {EA : Set ℕ}

lemma rtg_PL_bh (hG : Glob c own) (hL : ∀ j, LI c own j) {u v : ℕ}
    (h : ReflTransGen c.PL u v) : ReflTransGen c.Bh u v := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact .tail ih (bh_of_pred hG hL e)

/-- Backwards along `E` from a node that is not `&Exit`, edges are `Pred`-links. -/
lemma ScanInv.rtg_E_PL (hS : ScanInv c own q x tl V E i EA) {u v : ℕ}
    (h : ReflTransGen (EdgeR E) u v) (hv : c.pred v ≠ .exit) :
    ReflTransGen c.PL u v ∧ (u = v ∨ ∃ z, c.pred u = .node z) := by
  induction h with
  | refl => exact ⟨.refl, .inl rfl⟩
  | @tail w v hw e ih =>
    rcases hS.E1 _ _ e with h1 | ⟨-, h1⟩
    · have := ih (by rw [h1]; simp)
      refine ⟨.tail this.1 h1, ?_⟩
      rcases this.2 with rfl | h2
      · exact .inr ⟨_, h1⟩
      · exact .inr h2
    · exact absurd h1.1 hv

/-- After the scan, `Bh`-chains from early nodes are `E`-paths. -/
lemma ScanInv.rtg_bh_E (hS : ScanInv c own q x tl V E k EA) {u v : ℕ}
    (h : ReflTransGen c.Bh u v) (hu : u ∈ EA) : ReflTransGen (EdgeR E) u v := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a b hab _ ih =>
    obtain ⟨j, hj, hv⟩ := hab
    rcases hS.scanned j j.isLt a hj with h1 | ⟨-, -, hE⟩
    · exact absurd hu h1
    · exact .head (hE b hv) (ih (hS.bhEarly a b ⟨j, hj, hv⟩ hu))

/-- The repairer's own node is in `V` after the scan and is a sink. -/
lemma ScanInv.x_mem (hS : ScanInv c own q x tl V E k EA) (hn : c.node q = some x) : x ∈ V := by
  rcases hS.scanned q q.isLt x hn with h | ⟨h, -⟩
  · exact absurd hS.xEA h
  · exact h

lemma ScanInv.x_sink (hS : ScanInv c own q x tl V E i EA) (hx : c.pred x = .crash) :
    ∀ w, (x, w) ∉ E := by
  intro w hw
  rcases hS.E1 _ _ hw with h | ⟨h, -⟩
  · rw [hx] at h; cases h
  · rw [hx] at h; rcases h with h | h <;> cases h

/-- Every node of a maximal path containing the repairer's node `x` has a `Pred`-chain to `x`. -/
lemma ScanInv.mpath_PL (hS : ScanInv c own q x tl V E i EA) (hx : c.pred x = .crash)
    {σ : List ℕ} (hσ : IsMaxPath V E σ) (hxσ : x ∈ σ) {u : ℕ} (hu : u ∈ σ) :
    ReflTransGen c.PL u x ∧ (c.pred u = .crash ∨ ∃ z, c.pred u = .node z) := by
  have hxe : x = pend σ := hσ.eq_pend_of_sink hxσ (hS.x_sink hx)
  have h := hS.rtg_E_PL (hxe ▸ hσ.1.rtg_end u hu) (by rw [hx]; simp)
  refine ⟨h.1, ?_⟩
  rcases h.2 with rfl | h2
  · exact .inl hx
  · exact .inr h2

/-- In the FAS branch (line 47), `tail` does not reach `x` along `E`. -/
lemma ScanInv.fas_no_rtg (hS : ScanInv c own q x tl V E k EA) (hx : c.pred x = .crash)
    (hxV : x ∈ V) {mpath : List ℕ} {tpath hpath : Option (List ℕ)} {dn : List (List ℕ)}
    (hP : PathInv c x tl V E EA mpath tpath hpath dn)
    (hfas : tpath = none ∨ ∃ τ, tpath = some τ ∧ (c.pred (pend τ)).isInOut = true)
    (h : ReflTransGen (EdgeR E) tl x) : False := by
  have htlV : tl ∈ V := by
    rcases ReflTransGen.cases_head h with h | ⟨w, e, -⟩
    · exact h ▸ hxV
    · exact hS.Esrc _ _ e
  obtain ⟨τ, hτ, hτm, htlτ⟩ := hP.tpIn htlV
  have hxτ := hτm.mem_rtg hS.outDeg htlτ h
  have hxe := hτm.eq_pend_of_sink hxτ (hS.x_sink hx)
  rcases hfas with h1 | ⟨τ', h1, h2⟩
  · rw [h1] at hτ; cases hτ
  · rw [h1] at hτ; cases hτ; rw [← hxe, hx] at h2; cases h2

/-- The facts needed for line 47 (`FAS(Tail, start(mypath))`). -/
lemma ScanInv.fas_facts (hS : ScanInv c own q x tl V E k EA) (hG : Glob c own)
    (hL : ∀ j, LI c own j) (hn : c.node q = some x) (hx : c.pred x = .crash)
    {mpath : List ℕ} {tpath hpath : Option (List ℕ)} {dn : List (List ℕ)}
    (hP : PathInv c x tl V E EA mpath tpath hpath dn)
    (hfas : tpath = none ∨ ∃ τ, tpath = some τ ∧ (c.pred (pend τ)).isInOut = true) :
    (∀ w, ¬ c.Bh w (pstart mpath)) ∧ c.tail ≠ pstart mpath ∧ ¬ c.Rel (pstart mpath) ∧
      pstart mpath < c.nxt ∧ (∀ j, c.pc j ≠ .l13 (pstart mpath)) ∧
      ¬ ReflTransGen c.Bh c.tail x ∧ ReflTransGen c.PL (pstart mpath) x := by
  obtain ⟨hm, hxm⟩ := hP.mp
  have hxV := hS.x_mem hn
  have hxe : x = pend mpath := hm.eq_pend_of_sink hxm (hS.x_sink hx)
  have hsm := pstart_mem hm.1.1
  have hsV : pstart mpath ∈ V := hm.1.2.1 _ hsm
  have htl : tl ∉ mpath := by
    intro h
    have hrt : ReflTransGen (EdgeR E) tl x := hxe ▸ hm.1.rtg_end tl h
    exact hS.fas_no_rtg hx hxV hP hfas hrt
  have hsEA : pstart mpath ∈ EA := by
    by_contra hns
    have key : ∀ v, ReflTransGen (EdgeR E) v (pend mpath) → v ∈ mpath → v ∉ EA → False := by
      intro v hv
      induction hv using ReflTransGen.head_induction_on with
      | refl => intro _ h; exact h (hxe ▸ hS.xEA)
      | @head v w e1 _ ih =>
        intro hvm hvEA
        have hwm := hm.mem_succ hS.outDeg hvm e1
        rcases (hS.mpath_PL hx hm hxm hvm).2 with h1 | ⟨z, h1⟩
        · rcases hS.E1 _ _ e1 with h2 | ⟨h2, -⟩
          · rw [h1] at h2; cases h2
          · rw [h1] at h2; rcases h2 with h2 | h2 <;> cases h2
        · rcases hS.E1 _ _ e1 with h2 | ⟨h2, -⟩
          · rcases hS.bhLate v w (bh_of_pred hG hL h2) hvEA with h3 | h3
            · exact htl (h3 ▸ hwm)
            · exact ih hwm h3
          · rw [h1] at h2; rcases h2 with h2 | h2 <;> cases h2
    exact key _ (hm.1.rtg_end _ hsm) hsm hns
  have hstl : pstart mpath ≠ tl := fun h => htl (h ▸ hsm)
  refine ⟨?_, ?_, ?_, hS.Vlt _ hsV, fun j => hS.Vl13 _ hsV j, ?_,
    (hS.mpath_PL hx hm hxm hsm).1⟩
  · intro w hw
    by_cases hwEA : w ∈ EA
    · obtain ⟨j, hj, hv⟩ := hw
      rcases hS.scanned j j.isLt w hj with h | ⟨-, -, hE⟩
      · exact h hwEA
      · exact hm.2.1 w (hE _ hv)
    · rcases hS.bhLate w _ hw hwEA with h | h
      · exact hstl h
      · exact h hsEA
  · intro h
    rcases hS.tail with h' | h'
    · exact hstl (h ▸ h')
    · exact h' (h ▸ hsEA)
  · intro hr
    rcases (hS.mpath_PL hx hm hxm hsm).2 with h | ⟨z, h⟩ <;> rw [hr.1] at h <;> cases h
  · intro h
    have key : ∀ v, ReflTransGen c.Bh v x → (v = tl ∨ v ∉ EA) → False := by
      intro v hv
      induction hv using ReflTransGen.head_induction_on with
      | refl =>
        rintro (h | h)
        · exact hS.fas_no_rtg hx hxV hP hfas (h ▸ .refl)
        · exact h hS.xEA
      | @head v w e1 hrest ih =>
        rintro (h | h)
        · subst h
          exact hS.fas_no_rtg hx hxV hP hfas (hS.rtg_bh_E (.head e1 hrest) hS.tlEA)
        · rcases hS.bhLate v w e1 h with h2 | h2
          · exact ih (.inl h2)
          · exact ih (.inr h2)
    rcases hS.tail with h' | h'
    · exact key _ h (.inl h')
    · exact key _ h (.inr h')

lemma InH.not_rel {y : ℕ} (hG : Glob c own) (hL : ∀ j, LI c own j) (h : c.InH y) :
    ¬ c.Rel y := by
  intro hr
  rcases h.2 with h1 | ⟨z, h1, -⟩ | ⟨-, h1, -⟩
  · rw [hr.1] at h1; cases h1
  · exact not_bh_of_rel hL hr h1
  · rw [hr.2] at h1; cases h1

/-- A proper source of an `E`-path to a non-released node has a node `Pred`. -/
lemma ScanInv.src_node (hS : ScanInv c own q x tl V E i EA) {s y : ℕ}
    (h : ReflTransGen (EdgeR E) s y) (hy : ¬ c.Rel y) (hsy : s ≠ y) :
    ∃ z, c.pred s = .node z := by
  rcases ReflTransGen.cases_tail h with h1 | ⟨w, h1, e⟩
  · exact absurd h1.symm hsy
  · rcases hS.E1 _ _ e with h2 | ⟨-, h2⟩
    · rcases (hS.rtg_E_PL h1 (by rw [h2]; simp)).2 with rfl | h3
      · exact ⟨_, h2⟩
      · exact h3
    · exact absurd h2 hy

/-- Line 42 (end of the loop) in the attach branch with `headpath = NIL`: nobody holds the
right to the CS. -/
lemma ScanInv.none_noH (hS : ScanInv c own q x tl V E k EA) (hG : Glob c own)
    (hL : ∀ j, LI c own j) {mpath : List ℕ} {tpath : Option (List ℕ)} {dn : List (List ℕ)}
    (hP : PathInv c x tl V E EA mpath tpath none dn) (hA : AttachBr c tpath)
    (hall : ∀ σ, IsMaxPath V E σ → σ ∈ dn) : ∀ y, ¬ c.InH y := by
  intro y hy
  have htl := hS.attach_pred_tl hG hL hP hA
  have hyEA : y ∈ EA := by
    by_contra hyn
    rcases hy.2 with h1 | ⟨z, h1, h2⟩ | ⟨h1, -⟩
    · exact htl.1 (hS.lateIO y hyn (.inl h1))
    · rcases hS.bhLate y z h1 hyn with h3 | h3
      · exact htl.1 (h3 ▸ h2.1)
      · exact htl.1 (hS.lateIO z h3 (.inr h2.1))
    · exact htl.1 (hS.lateIO y hyn (.inr h1))
  obtain ⟨j, hj⟩ := hy.1
  obtain ⟨hyV, hynn, hyE⟩ : y ∈ V ∧ c.nn y = true ∧ ∀ v, c.vp j = .node v → (y, v) ∈ E := by
    rcases hS.scanned j j.isLt y hj with h | h
    · exact absurd hyEA h
    · exact h
  obtain ⟨σ, hσ, hyσ⟩ := exists_maxPath (fun u v e => ⟨hS.Esrc u v e, hS.Etgt u v e⟩) hS.Eacyc hyV
  have hσd := hall σ hσ
  have hye : ReflTransGen (EdgeR E) y (pend σ) := hσ.1.rtg_end y hyσ
  have heEA : pend σ ∈ EA := hS.rtg_EA hye hyEA
  have hio : (c.pred (pend σ)).isInOut = true := by
    rcases hS.sink_pred hG hL (hσ.1.2.1 _ (pend_mem hσ.1.1)) heEA hσ.2.2 with h | h | h
    · exfalso
      have hy' := hS.pred_nc_back hye (.inl h)
      rcases hy.2 with h1 | ⟨z, h1, h2⟩ | ⟨h1, -⟩
      · rcases hy' with h3 | ⟨_, h3⟩ <;> rw [h1] at h3 <;> cases h3
      · obtain ⟨j', hj', hv'⟩ := h1
        have := hG.node_inj hj hj'; subst this
        have hyz := hyE z hv'
        have hz := hS.pred_nc_back (hσ.1.rtg_end z (hσ.mem_succ hS.outDeg hyσ hyz)) (.inl h)
        rcases hz with h3 | ⟨_, h3⟩ <;> rw [h2.1] at h3 <;> cases h3
      · rcases hy' with h3 | ⟨_, h3⟩ <;> rw [h1] at h3 <;> cases h3
    · rw [h]; rfl
    · rw [h]; rfl
  have hse := hP.visited rfl σ hσd hσ heEA hio
  have hsy : ReflTransGen (EdgeR E) (pstart σ) y := hσ.1.rtg_start y hyσ
  by_cases heq : pstart σ = y
  · rw [heq] at hse
    rcases hy.2 with h1 | ⟨z, h1, -⟩ | ⟨-, -, h3⟩
    · rw [h1] at hse; cases hse
    · obtain ⟨j', hj', hv'⟩ := h1
      rcases vp_cases hL j' hj' with h2 | ⟨m, -, -, h2⟩ | ⟨m, -, -, h2⟩
      · rw [h2, hse] at hv'; cases hv'
      · rw [hse] at h2; cases h2
      · rw [hse] at h2; cases h2
    · rcases h3 with ⟨w, hw⟩ | h3
      · by_cases hwEA : w ∈ EA
        · obtain ⟨j', hj', hv'⟩ := hw
          rcases hS.scanned j' j'.isLt w hj' with h4 | ⟨-, -, hE⟩
          · exact h4 hwEA
          · exact hσ.2.1 w (by rw [show σ.headD 0 = y from heq]; exact hE y hv')
        · rcases hS.bhLate w y hw hwEA with h4 | h4
          · exact htl.1 (h4 ▸ hse)
          · exact h4 hyEA
      · rcases hS.tail with h4 | h4
        · exact htl.1 (h4 ▸ h3 ▸ hse)
        · exact h4 (h3 ▸ hyEA)
  · obtain ⟨z, hz⟩ := hS.src_node hsy (InH.not_rel hG hL hy) heq
    rw [hz] at hse; cases hse

/-- The facts needed for the attach branch (line 48). -/
lemma ScanInv.attach_facts (hS : ScanInv c own q x tl V E k EA) (hG : Glob c own)
    (hL : ∀ j, LI c own j) (hn : c.node q = some x) (hx : c.pred x = .crash)
    {mpath : List ℕ} {tpath hpath : Option (List ℕ)} {dn : List (List ℕ)}
    (hP : PathInv c x tl V E EA mpath tpath hpath dn) (hA : AttachBr c tpath)
    (hnone : hpath = none → ∀ w, ¬ c.InH w) {m : ℕ}
    (hm : (∃ σ, hpath = some σ ∧ m = pstart σ) ∨ (hpath = none ∧ m = special)) :
    (∀ w, ¬ c.Bh w m) ∧ c.tail ≠ m ∧ (c.pred m = .exit → ∀ w, ¬ c.InH w) ∧
      ¬ ReflTransGen c.Bh m x ∧ m < c.nxt ∧ (∀ j, c.pc j ≠ .l13 m) := by
  rcases hm with ⟨σ, hp, rfl⟩ | ⟨hp, rfl⟩
  swap
  · have hH := hnone hp
    refine ⟨fun w hw => ?_, ?_, fun _ => hH, ?_, hG.nxtPos, ?_⟩
    · obtain ⟨j, hj, hv⟩ := hw
      exact hH w ⟨⟨j, hj⟩, .inr (.inl ⟨_, ⟨j, hj, hv⟩, rel_special hG⟩)⟩
    · intro h; exact hS.attach_not_rel_tail hG hL hP hA (h ▸ rel_special hG)
    · intro h
      rcases ReflTransGen.cases_head h with h1 | ⟨w, e, -⟩
      · have := (hG.nodeLt q x hn).1; rw [← h1] at this; exact absurd this (lt_irrefl 0)
      · exact absurd (hG.pos_of_bh e).1 (lt_irrefl 0)
    · intro j hj
      have := hL j; unfold LI at this; rw [hj] at this
      exact absurd (hG.nodeLt j _ this.1).1 (lt_irrefl 0)
  · obtain ⟨hσ, hio, hH⟩ := hP.hp σ hp
    obtain ⟨hmEA, -, hbh, ht⟩ := hS.attach_hp hG hL hP hA hσ hio
    have hmV := hσ.1.2.1 _ (pstart_mem hσ.1.1)
    refine ⟨hbh, ht, hH hA, ?_, hS.Vlt _ hmV, fun j => hS.Vl13 _ hmV j⟩
    intro h
    have hxσ := hσ.mem_rtg hS.outDeg (pstart_mem hσ.1.1) (hS.rtg_bh_E h hmEA)
    have := hσ.eq_pend_of_sink hxσ (hS.x_sink hx)
    rw [← this, hx] at hio; cases hio

end

end Podc.RMESubLogBoth
