import Papers.PODC2019.RMESubLogBoth.InvLocal

/-!
# Consequences of the repairer's invariant after the scan

For the repairer `q` (node `x`) after the scan (`i = k`):
* `ScanInv.sink_pred`: an early sink of the graph has `Pred ∈ {&Crash, &InCS, &Exit}`;
* `ScanInv.attach_tl`: in the attach branch, every node on the path from `tail` has a `Pred` that
  is a node or `&Crash` (so `tail`, read at line 31, never entered the CS);
* `ScanInv.attach_not_rel_tail`: in the attach branch, `Tail` is not released;
* `ScanInv.attach_hp`: in the attach branch, the start `m` of `headpath` is early, `m ≠ tail`,
  nobody is behind `m`, and `m ≠ Tail`.
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation

section
variable {c : Cfg k} {own : ℕ → ℕ} {q : Fin k} {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)}
  {EA : Set ℕ}

lemma ScanInv.outDeg (hS : ScanInv c own q x tl V E k EA) : OutDeg1 E := hS.Eout
lemma ScanInv.inDeg (hS : ScanInv c own q x tl V E k EA) : InDeg1 E := hS.Ein

lemma ScanInv.rtg_EA (hS : ScanInv c own q x tl V E k EA) {u v : ℕ}
    (h : ReflTransGen (EdgeR E) u v) (hu : u ∈ EA) : v ∈ EA := by
  induction h with
  | refl => exact hu
  | tail _ e ih => exact hS.EEA _ _ e ih

/-- After the scan, an early sink of the graph has `Pred ∈ {&Crash, &InCS, &Exit}`. -/
lemma ScanInv.sink_pred (hS : ScanInv c own q x tl V E k EA) (hG : Glob c own)
    (hL : ∀ j, LI c own j) {v : ℕ} (hv : v ∈ V) (hvEA : v ∈ EA) (hsink : ∀ w, (v, w) ∉ E) :
    c.pred v = .crash ∨ c.pred v = .incs ∨ c.pred v = .exit := by
  by_cases hact : c.Act v
  · obtain ⟨j, hj⟩ := hact
    rcases hS.scanned j j.isLt v hj with h | ⟨-, hnn, hE⟩
    · exact absurd hvEA h
    · rcases vp_cases hL j hj with h1 | ⟨m, -, h2, -⟩ | ⟨m, -, h2, -⟩
      · cases h2 : c.pred v with
        | nil => exact absurd h2 (hG.nnPred v hnn)
        | crash => exact .inl rfl
        | incs => exact .inr (.inl rfl)
        | exit => exact .inr (.inr rfl)
        | node w => exact absurd (hE w (by rw [h1, h2])) (hsink w)
      · exact absurd (hE m h2) (hsink m)
      · exact absurd (hE m h2) (hsink m)
  · rcases Nat.eq_zero_or_pos v with rfl | hpos
    · exact .inr (.inr hG.special.1)
    · rcases hG.table v hpos (hS.Vlt v hv) with h | h
      · exact absurd h hact
      · exact .inr (.inr h.1)

/-- Along `E`-paths ending in a node whose `Pred` is a node or `&Crash`, all `Pred`s are nodes
or `&Crash`. -/
lemma ScanInv.pred_nc_back (hS : ScanInv c own q x tl V E k EA) {u e : ℕ}
    (h : ReflTransGen (EdgeR E) u e) (he : c.pred e = .crash ∨ ∃ z, c.pred e = .node z) :
    c.pred u = .crash ∨ ∃ z, c.pred u = .node z := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact he
  | head e1 _ ih =>
    rcases hS.E1 _ _ e1 with h1 | ⟨-, h1⟩
    · exact .inr ⟨_, h1⟩
    · rcases ih with h2 | ⟨z, h2⟩ <;> rw [h1.1] at h2 <;> cases h2

/-- In the attach branch, the node `tail` read at line 31 and every node on its path have a
`Pred` that is a node or `&Crash`. -/
lemma ScanInv.attach_tl (hS : ScanInv c own q x tl V E k EA) (hG : Glob c own)
    (hL : ∀ j, LI c own j) {mpath : List ℕ} {tpath hpath : Option (List ℕ)} {dn : List (List ℕ)}
    (hP : PathInv c x tl V E EA mpath tpath hpath dn) (hA : AttachBr c tpath) :
    ∃ τ, tpath = some τ ∧ IsMaxPath V E τ ∧ tl ∈ τ ∧ c.pred (pend τ) = .crash ∧
      ∀ u ∈ τ, c.pred u = .crash ∨ ∃ z, c.pred u = .node z := by
  obtain ⟨τ, hτ, hio⟩ := hA
  have htlV : tl ∈ V := by
    by_contra h; rw [hP.tpOut h] at hτ; cases hτ
  obtain ⟨τ', hτ', hmax, htl⟩ := hP.tpIn htlV
  rw [hτ] at hτ'; cases hτ'
  have hne := hmax.1.1
  have heEA : pend τ ∈ EA := hS.rtg_EA (hmax.1.rtg_end tl htl) hS.tlEA
  have he : c.pred (pend τ) = .crash := by
    rcases hS.sink_pred hG hL (hmax.1.2.1 _ (pend_mem hne)) heEA hmax.2.2 with h | h | h
    · exact h
    · rw [h] at hio; cases hio
    · rw [h] at hio; cases hio
  refine ⟨τ, hτ, hmax, htl, he, fun u hu => hS.pred_nc_back (hmax.1.rtg_end u hu) (.inl he)⟩

lemma ScanInv.attach_pred_tl (hS : ScanInv c own q x tl V E k EA) (hG : Glob c own)
    (hL : ∀ j, LI c own j) {mpath : List ℕ} {tpath hpath : Option (List ℕ)} {dn : List (List ℕ)}
    (hP : PathInv c x tl V E EA mpath tpath hpath dn) (hA : AttachBr c tpath) :
    c.pred tl ≠ .exit ∧ c.pred tl ≠ .incs := by
  obtain ⟨τ, -, -, htl, -, h⟩ := hS.attach_tl hG hL hP hA
  rcases h tl htl with h | ⟨z, h⟩ <;> rw [h] <;> simp

/-- In the attach branch, `Tail` is not released. -/
lemma ScanInv.attach_not_rel_tail (hS : ScanInv c own q x tl V E k EA) (hG : Glob c own)
    (hL : ∀ j, LI c own j) {mpath : List ℕ} {tpath hpath : Option (List ℕ)} {dn : List (List ℕ)}
    (hP : PathInv c x tl V E EA mpath tpath hpath dn) (hA : AttachBr c tpath) :
    ¬ c.Rel c.tail := by
  have htl := hS.attach_pred_tl hG hL hP hA
  intro hr
  rcases hS.tail with h | h
  · rw [h] at hr; exact htl.1 hr.1
  · exact htl.1 (hS.lateIO _ h (.inr hr.1))

/-- In the attach branch, late nodes never entered the CS. -/
lemma ScanInv.attach_late_pred (hS : ScanInv c own q x tl V E k EA) (hG : Glob c own)
    (hL : ∀ j, LI c own j) {mpath : List ℕ} {tpath hpath : Option (List ℕ)} {dn : List (List ℕ)}
    (hP : PathInv c x tl V E EA mpath tpath hpath dn) (hA : AttachBr c tpath) {a : ℕ}
    (ha : a ∉ EA) : c.pred a ≠ .incs ∧ c.pred a ≠ .exit := by
  have htl := hS.attach_pred_tl hG hL hP hA
  exact ⟨fun h => htl.1 (hS.lateIO a ha (.inl h)), fun h => htl.1 (hS.lateIO a ha (.inr h))⟩

/-- In the attach branch, if a maximal path contains a late node or `tail`, its end is not
`&InCS`/`&Exit`. -/
lemma ScanInv.attach_path_late (hS : ScanInv c own q x tl V E k EA) (hG : Glob c own)
    (hL : ∀ j, LI c own j) {mpath : List ℕ} {tpath hpath : Option (List ℕ)} {dn : List (List ℕ)}
    (hP : PathInv c x tl V E EA mpath tpath hpath dn) (hA : AttachBr c tpath) {σ : List ℕ}
    (hσ : IsMaxPath V E σ) {u : ℕ} (hu : u ∈ σ) (hlate : u ∉ EA ∨ u = tl) :
    (c.pred (pend σ)).isInOut = false := by
  obtain ⟨τ, hτ, hτm, htlτ, he, -⟩ := hS.attach_tl hG hL hP hA
  have htl := hS.attach_pred_tl hG hL hP hA
  by_contra hio
  have hio' : (c.pred (pend σ)).isInOut = true := by simpa using hio
  have htlσ : tl ∉ σ := by
    intro h
    have := maxPath_unique hS.outDeg hS.inDeg hσ hτm h htlτ
    subst this; rw [he] at hio'; cases hio'
  have key : ∀ v, ReflTransGen (EdgeR E) v (pend σ) → v ∈ σ → (v ∉ EA ∨ v = tl) → False := by
    intro v hv
    induction hv using ReflTransGen.head_induction_on with
    | refl =>
      rintro hvσ (h | h)
      · cases hp : c.pred (pend σ) <;> rw [hp] at hio' <;> simp [PV.isInOut] at hio'
        · exact htl.1 (hS.lateIO _ h (.inl hp))
        · exact htl.1 (hS.lateIO _ h (.inr hp))
      · exact htlσ (h ▸ hvσ)
    | @head v w e1 _ ih =>
      rintro hvσ (h | h)
      · rcases hS.E1 _ _ e1 with h1 | ⟨h1, -⟩
        · rcases hS.bhLate v w (bh_of_pred hG hL h1) h with h2 | h2
          · exact ih (hσ.mem_succ hS.outDeg hvσ e1) (.inr h2)
          · exact ih (hσ.mem_succ hS.outDeg hvσ e1) (.inl h2)
        · rcases h1 with h1 | h1
          · exact htl.1 (hS.lateIO _ h (.inl h1))
          · exact htl.1 (hS.lateIO _ h (.inr h1))
      · exact htlσ (h ▸ hvσ)
  exact key u (hσ.1.rtg_end u hu) hu hlate

/-- In the attach branch, the start `m` of a maximal path ending in `&InCS`/`&Exit` is early,
differs from `tail`, has nobody behind it, and is not `Tail`. -/
lemma ScanInv.attach_hp (hS : ScanInv c own q x tl V E k EA) (hG : Glob c own)
    (hL : ∀ j, LI c own j) {mpath : List ℕ} {tpath hpath : Option (List ℕ)} {dn : List (List ℕ)}
    (hP : PathInv c x tl V E EA mpath tpath hpath dn) (hA : AttachBr c tpath) {σ : List ℕ}
    (hσ : IsMaxPath V E σ) (hio : (c.pred (pend σ)).isInOut = true) :
    pstart σ ∈ EA ∧ pstart σ ≠ tl ∧ (∀ w, ¬ c.Bh w (pstart σ)) ∧ c.tail ≠ pstart σ := by
  have hm := pstart_mem hσ.1.1
  have h1 : pstart σ ∈ EA := by
    by_contra h
    have := hS.attach_path_late hG hL hP hA hσ hm (.inl h); rw [this] at hio; cases hio
  have h2 : pstart σ ≠ tl := by
    intro h
    have := hS.attach_path_late hG hL hP hA hσ hm (.inr h); rw [this] at hio; cases hio
  refine ⟨h1, h2, ?_, ?_⟩
  · intro w hw
    by_cases hwEA : w ∈ EA
    · obtain ⟨j, hj, hv⟩ := hw
      rcases hS.scanned j j.isLt w hj with h | ⟨-, -, hE⟩
      · exact h hwEA
      · exact hσ.2.1 w (hE _ hv)
    · rcases hS.bhLate w _ hw hwEA with h | h
      · exact h2 h
      · exact h h1
  · intro h
    rcases hS.tail with h' | h'
    · exact h2 (h ▸ h'.symm ▸ rfl)
    · exact h' (h ▸ h1)

end

end Podc.RMESubLogBoth
