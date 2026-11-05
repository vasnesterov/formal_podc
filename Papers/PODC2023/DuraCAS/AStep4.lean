import Papers.PODC2023.DuraCAS.AStep3

/-!
# Preservation of the global invariant: imprints, installs and moves

Instances of `GInv.ec` for the three kinds of successful `ECSC` (Lemma A.29), given the local
invariant of the acting process after its step (from `AActor.lean`).
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-- The witness update after a change of `Z` of object `k` (to value `sig'`; `mv`: a move). -/
def massW (a : AS P K V) (g : Gh P K V) (k : K) (sig' : V) (mv : Bool) (q : P) : Option ℕ :=
  match (a.ps q).op with
  | some s => if s.k = k then massWit (pview a g q s) sig' mv g.clk else g.wit q
  | none => g.wit q

theorem massW_of {a : AS P K V} {g : Gh P K V} {k : K} {sig' : V} {mv : Bool} {q : P}
    {s : OpRec K V} (hs : (a.ps q).op = some s) (hk : s.k = k) :
    massW a g k sig' mv q = massWit (pview a g q s) sig' mv g.clk := by
  simp [massW, hs, hk]

theorem massW_spec {init : K → V} {a : AS P K V} {g : Gh P K V} {k : K} {sig' : V} {mv : Bool}
    (L' : List (GE K V)) (hsig : curSt init L' k = sig')
    (hwr : mv = true → ∃ y ∈ L', y.key = 4 * g.clk + 1 ∧ y.k = k ∧ y.op.IsWrite) (q : P) :
    massW a g k sig' mv q = g.wit q ∨ (massW a g k sig' mv q = some g.clk ∧ ∃ s,
      (a.ps q).op = some s ∧ s.k = k ∧ (∀ old new, s.op = .cas old new → curSt init L' k ≠ old) ∧
      (∀ u, s.op = .write u → ∃ y ∈ L', y.key = 4 * g.clk + 1 ∧ y.k = k ∧ y.op.IsWrite)) := by
  unfold massW
  rcases hs : (a.ps q).op with _ | s
  · exact Or.inl rfl
  · simp only
    by_cases hk : s.k = k
    · simp only [hk, if_true]
      cases hw : g.wit q with
      | some w => left; simp [massWit, pview, hw]
      | none =>
        rcases hop : s.op with _ | ⟨old, new⟩ | u
        · left; simp [massWit, pview, hw, hop]
        · by_cases ho : sig' = old
          · left; simp [massWit, pview, hw, hop, ho]
          · right
            refine ⟨by simp [massWit, pview, hw, hop, ho], s, rfl, hk, fun o n hon => ?_,
              fun u hu => by simp [hop] at hu⟩
            rw [hop] at hon; simp only [Op.cas.injEq] at hon; rw [← hon.1, hsig]; exact ho
        · cases mv
          · left; simp [massWit, pview, hw, hop]
          · right
            exact ⟨by simp [massWit, pview, hw, hop], s, rfl, hk, fun o n hon => by simp [hop] at hon,
              fun _ _ => hwr rfl⟩
    · simp [hk]

theorem view_ec {init : K → V} (a : AS P K V) (g : Gh P K V) (p : P) (o : Obj K) (c' : Cell V)
    (hd : Hd P) (s' : ℕ) (st' : APS P K V) (k : K) (L' : List (GE K V)) (wit' : P → Option ℕ)
    (pw' : Option ℕ) (zAt' : ℕ) (lm' : Bool) :
    view init (a.ec p o c' hd s' st') (g.ec k L' wit' pw' zAt' lm') k =
      ⟨Function.update a.Y o c' (k, .W), Function.update a.Y o c' (k, .Z), pw', zAt', lm',
        curSt init L' k⟩ := by
  simp [view, AS.ec, Gh.ec]

theorem pview_ec (a : AS P K V) (g : Gh P K V) (p : P) (o : Obj K) (c' : Cell V)
    (hd : Hd P) (s' : ℕ) (st' : APS P K V) (k : K) (L' : List (GE K V)) (wit' : P → Option ℕ)
    (pw' : Option ℕ) (zAt' : ℕ) (lm' : Bool) (q : P) (s : OpRec K V) :
    pview (a.ec p o c' hd s' st') (g.ec k L' wit' pw' zAt' lm') q s =
      ⟨(Function.update a.ps p st' q).pc, s, (Function.update a.ps p st' q).orph,
        Function.update a.ls hd s' (q, .crit), wit' q, s.id ∈ L'.map GE.id⟩ := rfl

theorem PV.ext' {x y : PV P K V} (h1 : x.pc = y.pc) (h2 : x.r = y.r) (h3 : x.orph = y.orph)
    (h4 : x.ls = y.ls) (h5 : x.wit = y.wit) (h6 : x.inL ↔ y.inL) : x = y := by
  cases x; cases y; simp_all

/-- An imprint by `p` (at line 10 or as an orphan). -/
theorem GInv.impr {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {old new : V} (hropc : r.op = .cas old new)
    (hsig : curSt init g.L r.k = old) (hninL : r.id ∉ g.L.map GE.id)
    (st' : APS P K V) (hst : st'.op = some r) (s' : ℕ) (zb : Bool)
    (hI : Impr (view init a g r.k) ⟨a.Y (r.k, .W), (s', (new, zb)), g.pw r.k, g.zAt r.k, false, new⟩ new)
    (hact : Loc p ⟨a.Y (r.k, .W), (s', (new, zb)), g.pw r.k, g.zAt r.k, false, new⟩
      ⟨st'.pc, r, st'.orph, s', massWit (pview a g p r) new false g.clk, True⟩) :
    GInv init (a.ec p (r.k, .Z) (s', (new, zb)) (p, .crit) s' st')
      (g.ec r.k (g.L ++ [⟨4 * g.clk + 1, r.id, r.k, r.op, .ok true⟩]) (massW a g r.k new false)
        (g.pw r.k) (g.zAt r.k) false) := by
  set x : GE K V := ⟨4 * g.clk + 1, r.id, r.k, r.op, .ok true⟩
  have hcurx : curSt init (g.L ++ [x]) = Function.update (curSt init g.L) r.k new := by
    rw [curSt_append_one]; simp [x, hropc, seqStep, hsig]
  have hv' : view init (a.ec p (r.k, .Z) (s', (new, zb)) (p, .crit) s' st')
      (g.ec r.k (g.L ++ [x]) (massW a g r.k new false) (g.pw r.k) (g.zAt r.k) false) r.k =
      ⟨a.Y (r.k, .W), (s', (new, zb)), g.pw r.k, g.zAt r.k, false, new⟩ := by
    rw [view_ec, hcurx]; simp
  have hidx : ∀ q s, (a.ps q).op = some s → q ≠ p → s.id ≠ r.id := fun q s hs hq e =>
    hq (h.uniq q p s r hs hop e)
  refine h.ec hop rfl rfl hst (lgood_append h.lgood x rfl hninL (by simp [x, hropc, seqStep, hsig]))
    (fun e he => List.mem_append_left _ he) ?_ (fun t ht => stAt_append_lt x rfl t ht) ?_
    (massW_spec _ (by rw [hcurx]; simp) (fun h => by simp at h)) (by rw [hv']; exact (h.kinv r.k).impr hI)
    ?_ (Or.inr (Or.inl rfl))
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact Or.inl he
    · simp at he; subst he
      exact Or.inr ⟨rfl, p, r, hop, rfl, rfl, rfl, rfl, rfl⟩
  · intro k' hk; rw [hcurx, Function.update_of_ne hk]
  · intro q s hs hk
    rw [hv', pview_ec]
    by_cases hq : q = p
    · subst hq; rw [hop] at hs; cases hs
      convert hact using 1
      apply PV.ext' <;> simp [massW_of hop rfl, x]
    · have hl0 := h.loc q s hs
      rw [hk] at hl0
      have hl := loc_impr g.clk hl0 (h.kinv r.k) hI
      convert hl using 1
      have hqc : (q, Kind.crit) ≠ (p, Kind.crit) := by simp [hq]
      have hne : r.id ≠ s.id := (hidx q s hs hq).symm
      apply PV.ext' <;> simp [Function.update_of_ne hq, Function.update_of_ne hqc, massW_of hs hk,
        pview, x, hne, hne.symm]

/-- An install by `p` (at line 15 or as an orphan). -/
theorem GInv.inst {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) (st' : APS P K V) (hst : st'.op = some r)
    (s' : ℕ) (cW : Cell V)
    (hI : Inst (view init a g r.k) ⟨cW, a.Y (r.k, .Z), some r.id, (a.Y (r.k, .Z)).1, g.lm r.k,
      curSt init g.L r.k⟩ r.id)
    (hact : Loc p ⟨cW, a.Y (r.k, .Z), some r.id, (a.Y (r.k, .Z)).1, g.lm r.k, curSt init g.L r.k⟩
      ⟨st'.pc, r, st'.orph, s', g.wit p, r.id ∈ g.L.map GE.id⟩) :
    GInv init (a.ec p (r.k, .W) cW (p, .crit) s' st')
      (g.ec r.k g.L g.wit (some r.id) (a.Y (r.k, .Z)).1 (g.lm r.k)) := by
  have hv' : view init (a.ec p (r.k, .W) cW (p, .crit) s' st')
      (g.ec r.k g.L g.wit (some r.id) (a.Y (r.k, .Z)).1 (g.lm r.k)) r.k =
      ⟨cW, a.Y (r.k, .Z), some r.id, (a.Y (r.k, .Z)).1, g.lm r.k, curSt init g.L r.k⟩ := by
    rw [view_ec]; simp
  have hidx : ∀ q s, (a.ps q).op = some s → q ≠ p → s.id ≠ r.id := fun q s hs hq e =>
    hq (h.uniq q p s r hs hop e)
  refine h.ec hop rfl rfl hst (h.lgood.mono (by omega)) (fun e he => he) (fun e he => Or.inl he)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun q => Or.inl rfl)
    (by rw [hv']; exact (h.kinv r.k).inst hI) ?_ (Or.inr (Or.inr rfl))
  intro q s hs hk
  rw [hv', pview_ec]
  by_cases hq : q = p
  · subst hq; rw [hop] at hs; cases hs
    convert hact using 1
    apply PV.ext' <;> simp
  · have hl0 := h.loc q s hs
    rw [hk] at hl0
    have hl := loc_inst hl0 (h.kinv r.k) hI (hidx q s hs hq).symm
    convert hl using 1
    have hqc : (q, Kind.crit) ≠ (p, Kind.crit) := by simp [hq]
    apply PV.ext' <;> simp [Function.update_of_ne hq, Function.update_of_ne hqc, pview]

/-- A move by `p` (at line 21 or as an orphan). -/
theorem GInv.move {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {idw : ℕ} (hpw : g.pw r.k = some idw)
    (st' : APS P K V) (hst : st'.op = some r) (s' : ℕ) (cZ : Cell V)
    (hM : Move (view init a g r.k) ⟨a.Y (r.k, .W), cZ, none, g.zAt r.k, true, (a.Y (r.k, .W)).2.1⟩)
    (hact : Loc p ⟨a.Y (r.k, .W), cZ, none, g.zAt r.k, true, (a.Y (r.k, .W)).2.1⟩
      ⟨st'.pc, r, st'.orph, a.ls (p, .crit), massWit (pview a g p r) (a.Y (r.k, .W)).2.1 true g.clk,
        r.id ∈ g.L.map GE.id ∨ g.pw r.k = some r.id⟩) :
    GInv init (a.ec p (r.k, .Z) cZ (p, .cas) s' st')
      (g.ec r.k (g.L ++ [⟨4 * g.clk + 1, idw, r.k, .write (a.Y (r.k, .W)).2.1, .ok true⟩])
        (massW a g r.k (a.Y (r.k, .W)).2.1 true) none (g.zAt r.k) true) := by
  set x : GE K V := ⟨4 * g.clk + 1, idw, r.k, .write (a.Y (r.k, .W)).2.1, .ok true⟩
  obtain ⟨qw, sw, hsw, hidw, hkw⟩ := h.pw_ex _ _ hpw
  have hlw := h.loc qw sw hsw
  rw [hkw] at hlw
  have hpw' : g.pw r.k = some sw.id := by rw [hpw, hidw]
  have hswop : sw.op = .write (a.Y (r.k, .W)).2.1 := (hlw.pw_op hpw').2
  have hninL : idw ∉ g.L.map GE.id := by
    intro hin
    exact hlw.not_both ⟨show sw.id ∈ g.L.map GE.id by rw [hidw]; exact hin, hpw'⟩
  have hcurx : curSt init (g.L ++ [x]) = Function.update (curSt init g.L) r.k (a.Y (r.k, .W)).2.1 := by
    rw [curSt_append_one]; simp [x, seqStep]
  have hv' : view init (a.ec p (r.k, .Z) cZ (p, .cas) s' st')
      (g.ec r.k (g.L ++ [x]) (massW a g r.k (a.Y (r.k, .W)).2.1 true) none (g.zAt r.k) true) r.k =
      ⟨a.Y (r.k, .W), cZ, none, g.zAt r.k, true, (a.Y (r.k, .W)).2.1⟩ := by
    rw [view_ec, hcurx]; simp
  refine h.ec hop rfl rfl hst (lgood_append h.lgood x rfl hninL (by simp [x, seqStep]))
    (fun e he => List.mem_append_left _ he) ?_ (fun t ht => stAt_append_lt x rfl t ht) ?_
    (massW_spec _ (by rw [hcurx]; simp) (fun _ => ⟨x, by simp, rfl, rfl, trivial⟩))
    (by rw [hv']; exact (h.kinv r.k).move hM) ?_ (Or.inl rfl)
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact Or.inl he
    · simp at he; subst he
      exact Or.inr ⟨rfl, qw, sw, hsw, hkw, hidw.symm, hkw.symm, hswop.symm, rfl⟩
  · intro k' hk; rw [hcurx, Function.update_of_ne hk]
  · intro q s hs hk
    rw [hv', pview_ec]
    have hpc : (p, Kind.crit) ≠ (p, Kind.cas) := by simp
    by_cases hq : q = p
    · subst hq; rw [hop] at hs; cases hs
      convert hact using 1
      apply PV.ext' <;> simp [massW_of hop rfl, x, Function.update_of_ne hpc, hpw, eq_comm]
    · have hl0 := h.loc q s hs
      rw [hk] at hl0
      have hl := loc_move g.clk hl0 (h.kinv r.k) hM
      convert hl using 1
      have hqc : (q, Kind.crit) ≠ (p, Kind.cas) := by simp
      apply PV.ext' <;> simp [Function.update_of_ne hq, Function.update_of_ne hqc, massW_of hs hk,
        pview, view, x, hpw, eq_comm]

end Podc.DuraCAS
