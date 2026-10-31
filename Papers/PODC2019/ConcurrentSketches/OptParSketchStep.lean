import Papers.PODC2019.ConcurrentSketches.OptParSketchInv

/-!
# `OptParSketch`: the invariant is inductive
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentSketches

open Cslib.SharedMemory

variable {S : Composable} {N : ℕ} {Q : Type} [NeZero N] [DecidableEq Q]

/-- The invariant holds initially, provided the initial hint is safe for the empty stream and
`b > 0`. -/
lemma oinv_init {b : ℕ} (hb : 0 < b) {hint₀ : S.Hint} (h₀ : S.Safe hint₀ []) :
    OInv b ([] : List (Lbl S N Q)) (optParSketch S N Q b hint₀).initCfg (OGhost.init S N Q) where
  glob := rfl
  vis_legal := seqSketch_nil
  lin_nodup := List.nodup_nil
  vis_nodup := List.nodup_nil
  lin_op := by simp [OGhost.init]
  lin_resp := by simp [OGhost.init]
  lin_comp := by simp [Completed]
  vis_lin := by simp [OGhost.init]
  lin_cover := by simp [OGhost.init]
  buf_lin := by simp [OGhost.init, OGhost.buf]
  buf_vis := by simp [OGhost.init, OGhost.buf]
  buf_shape := by simp [OGhost.init, OGhost.buf]
  buf_nodup := by simp [OGhost.init, OGhost.buf]
  thr j := ⟨⟨rfl, hb, rfl, rfl, rfl, by simpa [OGhost.init] using h₀⟩,
    by simpa [Impl.initCfg, optParSketch, OInact, OGhost.init, OLoc.init, ophaseOf] using h₀⟩
  qry q := rfl
  lin_shape := by simp [OGhost.init]
  prop_live := by simp [Impl.initCfg, optParSketch, OLoc.init]
  prop_kind := by simp [Impl.initCfg, optParSketch, OLoc.init, IsOPLoc]

variable {b : ℕ} {hint₀ : S.Hint}

lemma OInv.curOp_not_mem {α : List (Lbl S N Q)} {C : OCfg S N Q} {g : OGhost S N Q}
    (hC : (optParSketch S N Q b hint₀).run α = some C) (hI : OInv b α C g) {p : Proc N Q}
    (hp : C.pend p = none) : curOp α p ∉ g.lin.map Prod.fst := by
  intro hm
  obtain ⟨y, hy, hy1⟩ := List.mem_map.1 hm
  have := Invoked.of_opOf_eq_some (hI.lin_op y hy)
  rw [hy1] at this
  exact (optParSketch S N Q b hint₀).not_invoked_curOp_of_idle hC hp this

/-- The thread invariant of `j` is unchanged when nothing it depends on changes. -/
lemma OInv.thr_frame {α : List (Lbl S N Q)} {C C' : OCfg S N Q} {g : OGhost S N Q}
    (hI : OInv b α C g) (j : Fin N) (h1 : C'.loc (.upd j) = C.loc (.upd j))
    (h2 : C'.pend (.upd j) = C.pend (.upd j)) (h3 : ∀ k, C'.mem (.loc j k) = C.mem (.loc j k))
    (h4 : C'.mem (.cur j) = C.mem (.cur j)) (h5 : C'.mem (.prop j) = C.mem (.prop j))
    (h6 : ophaseOf j (C'.loc .prop) = ophaseOf j (C.loc .prop)) :
    OTI b (C'.loc (.upd j)) (C'.pend (.upd j)) (fun k => C'.mem (.loc j k)) (C'.mem (.cur j))
      (C'.mem (.prop j)) (ophaseOf j (C'.loc .prop)) (g.bIn j) (g.bAct j) (upds g.vis)
      (curOp α (.upd j)) g.lin :=
  (hI.thr j).congr h1 h2 (funext h3) h4 h5 h6 rfl rfl rfl

/-- **Frame lemma for internal steps that do not change `l`, `f` and the buffers.** -/
lemma OInv.tau_frame {α : List (Lbl S N Q)} {C C' : OCfg S N Q} {g g' : OGhost S N Q}
    (hI : OInv b α C g) (p : Proc N Q) (hpend : C'.pend = C.pend)
    (hglob : C'.mem .glob = C.mem .glob) (hlin : g'.lin = g.lin) (hvis : g'.vis = g.vis)
    (hbuf : ∀ j, g'.buf j = g.buf j)
    (hthr : ∀ j, OTI b (C'.loc (.upd j)) (C'.pend (.upd j)) (fun k => C'.mem (.loc j k))
      (C'.mem (.cur j)) (C'.mem (.prop j)) (ophaseOf j (C'.loc .prop)) (g'.bIn j) (g'.bAct j)
      (upds g.vis) (curOp α (.upd j)) g.lin)
    (hq : ∀ q, C'.loc (.qry q) = C.loc (.qry q))
    (hlive : C'.pend .prop ≠ none → C'.loc .prop ≠ .pIdle) (hkind : IsOPLoc (C'.loc .prop)) :
    OInv b (α ++ [.tau p]) C' g' where
  glob := by rw [hvis]; exact hglob.trans hI.glob
  vis_legal := by rw [hvis]; exact hI.vis_legal
  lin_nodup := by rw [hlin]; exact hI.lin_nodup
  vis_nodup := by rw [hvis]; exact hI.vis_nodup
  lin_op y hy := (opOf_tau α p y.1).trans (hI.lin_op y (hlin ▸ hy))
  lin_resp y hy r hr := hI.lin_resp y (hlin ▸ hy) r ((respOf_tau α p y.1).symm.trans hr)
  lin_comp x hx := hlin ▸ hI.lin_comp x ((completed_tau α p x).1 hx)
  vis_lin y hy := hlin ▸ hI.vis_lin y (hvis ▸ hy)
  lin_cover y hy := by rw [hvis]; simp only [hbuf]; exact hI.lin_cover y (hlin ▸ hy)
  buf_lin j y hy := hlin ▸ hI.buf_lin j y (hbuf j ▸ hy)
  buf_vis j y hy := hvis ▸ hI.buf_vis j y (hbuf j ▸ hy)
  buf_shape j y hy := hI.buf_shape j y (hbuf j ▸ hy)
  buf_nodup j := hbuf j ▸ hI.buf_nodup j
  thr j := by rw [hvis, hlin]; simpa using hthr j
  qry q := by rw [hlin]; simpa [hq q, hpend] using hI.qry q
  lin_shape y hy := hI.lin_shape y (hlin ▸ hy)
  prop_live := hlive
  prop_kind := hkind

lemma OObj.loc_ne_loc {j j' : Fin N} {k k' : Bool} (h : j' ≠ j ∨ k' ≠ k) :
    OObj.loc j' k' ≠ OObj.loc j k := by
  intro e; cases e; simp at h

/-- Internal steps of update thread `j` preserve the invariant. -/
lemma oinv_step_tau_upd (hb : 0 < b) {α : List (Lbl S N Q)} {C C' : OCfg S N Q}
    {g : OGhost S N Q} {j : Fin N} (hI : OInv b α C g)
    (hs : (optParSketch S N Q b hint₀).step C (.tau (.upd j)) = some C') :
    OInv b (α ++ [.tau (.upd j)]) C' (ogstep α C g (.tau (.upd j))) := by
  have hpne := (Impl.step_tau hs).1
  have hT := hI.thr j
  generalize hl : C.loc (.upd j) = l at hT
  cases l with
  | oIdle cur c h => exact absurd hT.1.1 hpne
  | oRet cur c h =>
    have : (optParSketch S N Q b hint₀).step C (.tau (.upd j)) = none :=
      Impl.step_tau_ret_none (r := .ack) (l := .oIdle cur c h)
        (by simp [optParSketch, OLoc.act, hl])
    rw [hs] at this; cases this
  | oApply a cur c h =>
    have hg : ogstep α C g (.tau (.upd j)) = g := by simp [ogstep, hl]
    rw [hg]
    obtain ⟨⟨hpd, hc, ⟨B', hB, hB'len, hls⟩, hcr, hsafe⟩, hin⟩ := hT
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .loc j cur)
      (o := LOp.update a) (k := fun _ => if c + 1 = b then .oWait cur h else .oRet cur (c + 1) h)
      (by simp [optParSketch, OLoc.act, hl])
    refine hI.tau_frame _ hpend' (by rw [hmem']; simp) rfl rfl (fun _ => rfl) (fun j' => ?_)
      (fun q => by rw [hloc']; simp) (by rw [hpend', hloc']; simpa using hI.prop_live)
      (by rw [hloc']; simpa using hI.prop_kind)
    by_cases hj : j' = j
    · subst hj
      have hls1 : C'.mem (.loc j' cur) = S.run (upds (g.bAct j')) := by
        rw [hmem']; simp [hls, hB, Sketch.run_concat]
      have hls2 : C'.mem (.loc j' (!cur)) = C.mem (.loc j' (!cur)) := by
        rw [hmem', Function.update_of_ne (OObj.loc_ne_loc (Or.inr (by cases cur <;> simp)))]
      have hpr' : C'.mem (.prop j') = C.mem (.prop j') := by rw [hmem']; simp
      have hcr' : C'.mem (.cur j') = C.mem (.cur j') := by rw [hmem']; simp
      have hph' : ophaseOf j' (C'.loc .prop) = ophaseOf j' (C.loc .prop) := by
        rw [hloc', Function.update_of_ne (by simp)]
      have hx : curOp α (.upd j') ∈ g.lin.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst)
          (hI.buf_lin j' (curOp α (.upd j'), .update a, .ack)
            (by simp [OGhost.buf, hB]))
      rw [hph', hloc', Function.update_self, hpend', hpd]
      split_ifs with hcb
      · refine ⟨⟨⟨a, rfl⟩, by rw [hB]; simp [hB'len, hcb], hls1, hcr'.trans hcr, hsafe, hx⟩, ?_⟩
        simp only; rw [hls2, hpr']; exact hin
      · refine ⟨⟨⟨a, rfl⟩, by omega, by rw [hB]; simp [hB'len], hls1, hcr'.trans hcr, hsafe, hx⟩,
          ?_⟩
        simp only; rw [hls2, hpr']; exact hin
    · exact hI.thr_frame j' (by rw [hloc', Function.update_of_ne (by simpa using hj)])
        (by rw [hpend']) (fun k => by rw [hmem', Function.update_of_ne (OObj.loc_ne_loc (Or.inl hj))])
        (by rw [hmem']; simp) (by rw [hmem']; simp) (by rw [hloc', Function.update_of_ne (by simp)])
  | oWait cur h =>
    have hg : ogstep α C g (.tau (.upd j)) = g := by simp [ogstep, hl]
    rw [hg]
    obtain ⟨⟨hpd, hlen, hls, hcr, hsafe, hx⟩, hin⟩ := hT
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .prop j)
      (o := ROp.read) (k := fun r => Option.elim r (.oWait cur h) (.oFlip cur))
      (by simp only [optParSketch, hl, OLoc.act]; congr; funext r; cases r <;> rfl)
    have hmem'' : C'.mem = C.mem := by rw [hmem']; simp
    refine hI.tau_frame _ hpend' (by rw [hmem'']) rfl rfl (fun _ => rfl) (fun j' => ?_)
      (fun q => by rw [hloc']; simp) (by rw [hpend', hloc']; simpa using hI.prop_live)
      (by rw [hloc']; simpa using hI.prop_kind)
    by_cases hj : j' = j
    · subst hj
      have hph' : ophaseOf j' (C'.loc .prop) = ophaseOf j' (C.loc .prop) := by
        rw [hloc', Function.update_of_ne (by simp)]
      rw [hph', hloc', Function.update_self, hpend', hmem'']
      simp only
      generalize hpr : C.mem (.prop j') = pr at hin
      cases pr with
      | none => exact ⟨⟨hpd, hlen, hls, hcr, hsafe, hx⟩, hin⟩
      | some h' =>
        obtain ⟨hs', hB, hli, hph⟩ := hin
        exact ⟨hpd, hlen, hls, hcr, rfl, hs', hB, hli, hph, hx⟩
    · exact hI.thr_frame j' (by rw [hloc', Function.update_of_ne (by simpa using hj)])
        (by rw [hpend']) (fun k => by rw [hmem'']) (by rw [hmem'']) (by rw [hmem''])
        (by rw [hloc', Function.update_of_ne (by simp)])
  | oFlip cur h =>
    have hg : ogstep α C g (.tau (.upd j)) =
        { g with bIn := Function.update g.bIn j (g.bAct j),
                 bAct := Function.update g.bAct j [] } := by simp [ogstep, hl]
    rw [hg]
    obtain ⟨hpd, hlen, hls, hcr, hpr, hsafe, hB, hli, hph, hx⟩ := hT
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .cur j)
      (o := ROp.write (!cur)) (k := fun _ => .oSignal (!cur) h)
      (by simp [optParSketch, OLoc.act, hl])
    refine hI.tau_frame _ hpend' (by rw [hmem']; simp) rfl rfl (fun j' => ?_) (fun j' => ?_)
      (fun q => by rw [hloc']; simp) (by rw [hpend', hloc']; simpa using hI.prop_live)
      (by rw [hloc']; simpa using hI.prop_kind)
    · by_cases hj : j' = j
      · subst hj; simp [OGhost.buf, hB]
      · simp [OGhost.buf, Function.update_of_ne hj]
    by_cases hj : j' = j
    · subst hj
      have hph' : ophaseOf j' (C'.loc .prop) = ophaseOf j' (C.loc .prop) := by
        rw [hloc', Function.update_of_ne (by simp)]
      rw [hph', hloc', Function.update_self, hpend']
      simp only [Function.update_self]
      refine ⟨hpd, rfl, ?_, by simp [hlen], ?_, by rw [hmem']; simp, ?_, hph, hsafe, hx⟩
      · rw [hmem']; simpa using hli
      · rw [hmem', Bool.not_not]; simpa using hls
      · rw [hmem']; simp [hpr]
    · simp only [Function.update_of_ne hj]
      exact hI.thr_frame j' (by rw [hloc', Function.update_of_ne (by simpa using hj)])
        (by rw [hpend']) (fun k => by rw [hmem']; simp) (by rw [hmem', Function.update_of_ne
          (by simpa using hj)]) (by rw [hmem']; simp) (by rw [hloc', Function.update_of_ne (by simp)])
  | oSignal cur h =>
    have hg : ogstep α C g (.tau (.upd j)) = g := by simp [ogstep, hl]
    rw [hg]
    obtain ⟨hpd, hB, hls, hlen, hli, hcr, hpr, hph, hsafe, hx⟩ := hT
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .prop j)
      (o := ROp.write none) (k := fun _ => .oRet cur 0 h)
      (by simp [optParSketch, OLoc.act, hl])
    refine hI.tau_frame _ hpend' (by rw [hmem']; simp) rfl rfl (fun _ => rfl) (fun j' => ?_)
      (fun q => by rw [hloc']; simp) (by rw [hpend', hloc']; simpa using hI.prop_live)
      (by rw [hloc']; simpa using hI.prop_kind)
    by_cases hj : j' = j
    · subst hj
      have hph' : ophaseOf j' (C'.loc .prop) = ophaseOf j' (C.loc .prop) := by
        rw [hloc', Function.update_of_ne (by simp)]
      rw [hph', hloc', Function.update_self, hpend', hph]
      refine ⟨⟨hpd, hb, by simp [hB], ?_, by rw [hmem']; simpa using hcr, hsafe, hx⟩, ?_⟩
      · rw [hmem']; simpa [hB] using hls
      · rw [hmem']; simp only [Function.update_self]
        exact ⟨hlen, by simpa using hli⟩
    · exact hI.thr_frame j' (by rw [hloc', Function.update_of_ne (by simpa using hj)])
        (by rw [hpend']) (fun k => by rw [hmem']; simp) (by rw [hmem']; simp)
        (by rw [hmem', Function.update_of_ne (by simpa using hj)])
        (by rw [hloc', Function.update_of_ne (by simp)])
  | _ => exact hT.elim

/-- The thread invariant of `j` along a propagator step that works on thread `j` while
`prop_j = 0`: it suffices to re-establish the inactive half. -/
lemma OInv.thr_prop {α : List (Lbl S N Q)} {C C' : OCfg S N Q} {g : OGhost S N Q}
    (hI : OInv b α C g) (j : Fin N) (hpr : C.mem (.prop j) = none)
    (hloc : C'.loc (.upd j) = C.loc (.upd j)) (hpend : C'.pend (.upd j) = C.pend (.upd j))
    (hcr : C'.mem (.cur j) = C.mem (.cur j))
    (hls : C'.mem (.loc j (C.mem (.cur j))) = C.mem (.loc j (C.mem (.cur j))))
    {bIn' : List (Entry (Proc N Q) S.toSketch)} {F' : List S.Elem}
    {lin' : List (Entry (Proc N Q) S.toSketch)} (hF : upds g.vis <+: F')
    (hlin : ∀ y ∈ g.lin, y ∈ lin')
    (hin : OInact b (C.mem (.cur j)) none (ophaseOf j (C.loc .prop))
        (C.mem (.loc j (!C.mem (.cur j)))) (g.bIn j) (upds g.vis) →
      OInact b (C.mem (.cur j)) (C'.mem (.prop j)) (ophaseOf j (C'.loc .prop))
        (C'.mem (.loc j (!C.mem (.cur j)))) bIn' F') :
    OTI b (C'.loc (.upd j)) (C'.pend (.upd j)) (fun k => C'.mem (.loc j k)) (C'.mem (.cur j))
      (C'.mem (.prop j)) (ophaseOf j (C'.loc .prop)) bIn' (g.bAct j) F' (curOp α (.upd j)) lin' := by
  have hT := hI.thr j
  rw [hpr] at hT
  obtain ⟨h1, h2⟩ := hT.transport
  exact (h2 (fun k => C'.mem (.loc j k)) _ _ bIn' F' lin' hls hF hlin (hin h1)).congr hloc hpend
    rfl hcr rfl rfl rfl rfl rfl

lemma ophaseOf_ne {j j' : Fin N} (h : j' ≠ j) :
    ophaseOf (S := S) j (.pCur j') = .free ∧ (∀ k, ophaseOf (S := S) j (.pRead j' k) = .free) ∧
    (∀ k s, ophaseOf (S := S) j (.pMerge j' k s) = .free) ∧
    (∀ k, ophaseOf (S := S) j (.pReset j' k) = .free) ∧ ophaseOf (S := S) j (.pHint j') = .free ∧
    (∀ hh, ophaseOf (S := S) j (.pSignal j' hh) = .free) := by
  simp [ophaseOf, h]

/-- Internal steps of the propagator that do not merge preserve the invariant. -/
lemma oinv_step_tau_prop_nomerge {α : List (Lbl S N Q)} {C C' : OCfg S N Q}
    {g : OGhost S N Q} (hI : OInv b α C g)
    (hs : (optParSketch S N Q b hint₀).step C (.tau .prop) = some C')
    (hnm : ∀ j k s, C.loc .prop ≠ .pMerge j k s) :
    OInv b (α ++ [.tau .prop]) C' (ogstep α C g (.tau .prop)) := by
  have hpne := (Impl.step_tau hs).1
  have hg : ogstep α C g (.tau .prop) = g := by
    simp only [ogstep]
  rw [hg]
  generalize hl : C.loc .prop = l at hnm
  cases l with
  | pIdle => exact absurd hl (hI.prop_live hpne)
  | pCheck j =>
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .prop j) (o := ROp.read)
      (k := fun r => Option.elim r (.pCur j) (fun _ => .pCheck (j + 1)))
      (by simp only [optParSketch, hl, OLoc.act]; congr; funext r; cases r <;> rfl)
    have hmem'' : C'.mem = C.mem := by rw [hmem']; simp
    refine hI.tau_frame _ hpend' (by rw [hmem'']) rfl rfl (fun _ => rfl) (fun j' => ?_)
      (fun q => by rw [hloc']; simp) (by rw [hloc']; simp; cases C.mem (.prop j) <;> simp)
      (by rw [hloc']; simp; cases C.mem (.prop j) <;> simp [IsOPLoc])
    by_cases hj : j' = j
    · subst hj
      generalize hpr : C.mem (.prop j') = pr at hloc'
      cases pr with
      | none =>
        refine hI.thr_prop j' hpr (by rw [hloc']; simp) (by rw [hpend']) (by rw [hmem''])
          (by rw [hmem'']) (List.prefix_refl _) (fun y hy => hy) (fun h => ?_)
        rw [hl] at h; rw [hloc', hmem'', hpr]; simp only [ophaseOf] at h ⊢
        simp only [Option.elim, Function.update_self, ite_true]; exact h
      | some hh =>
        exact hI.thr_frame j' (by rw [hloc']; simp) (by rw [hpend']) (by simp [hmem''])
          (by rw [hmem'']) (by rw [hmem'']) (by rw [hloc', hl]; simp [ophaseOf])
    · exact hI.thr_frame j' (by rw [hloc']; simp) (by rw [hpend']) (by simp [hmem''])
        (by rw [hmem'']) (by rw [hmem''])
        (by rw [hloc', hl]; cases C.mem (.prop j) <;> simp [ophaseOf, Ne.symm hj])
  | pCur j =>
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .cur j) (o := ROp.read)
      (k := fun v => .pRead j (!v)) (by simp only [optParSketch, hl, OLoc.act])
    have hmem'' : C'.mem = C.mem := by rw [hmem']; simp
    refine hI.tau_frame _ hpend' (by rw [hmem'']) rfl rfl (fun _ => rfl) (fun j' => ?_)
      (fun q => by rw [hloc']; simp) (by rw [hloc']; simp) (by rw [hloc']; simp [IsOPLoc])
    by_cases hj : j' = j
    · subst hj
      have hpr := (hI.thr j').none_of_busy (by rw [hl]; simp [ophaseOf])
      refine hI.thr_prop j' hpr (by rw [hloc']; simp) (by rw [hpend']) (by rw [hmem''])
        (by rw [hmem'']) (List.prefix_refl _) (fun y hy => hy) (fun h => ?_)
      rw [hl] at h; rw [hloc', hmem'', hpr]; simp only [ophaseOf, ite_true] at h
      simp only [Function.update_self, ophaseOf, ite_true]
      exact ⟨rfl, h⟩
    · exact hI.thr_frame j' (by rw [hloc']; simp) (by rw [hpend']) (by simp [hmem''])
        (by rw [hmem'']) (by rw [hmem'']) (by rw [hloc', hl]; simp [ophaseOf, Ne.symm hj])
  | pRead j k =>
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .loc j k) (o := LOp.read)
      (k := fun r => match r with
        | .state s => .pMerge j k s
        | .unit => .pCheck j)
      (by simp only [optParSketch, hl, OLoc.act]; congr)
    have hmem'' : C'.mem = C.mem := by rw [hmem']; simp
    refine hI.tau_frame _ hpend' (by rw [hmem'']) rfl rfl (fun _ => rfl) (fun j' => ?_)
      (fun q => by rw [hloc']; simp) (by rw [hloc']; simp) (by rw [hloc']; simp [IsOPLoc])
    by_cases hj : j' = j
    · subst hj
      have hpr := (hI.thr j').none_of_busy (by rw [hl]; simp [ophaseOf])
      refine hI.thr_prop j' hpr (by rw [hloc']; simp) (by rw [hpend']) (by rw [hmem''])
        (by rw [hmem'']) (List.prefix_refl _) (fun y hy => hy) (fun h => ?_)
      rw [hl] at h; rw [hloc', hmem'', hpr]; simp only [ophaseOf, ite_true] at h
      simp only [Function.update_self, ophaseOf, ite_true]
      obtain ⟨rfl, h2, h3⟩ := h
      exact ⟨rfl, h2, h3⟩
    · exact hI.thr_frame j' (by rw [hloc']; simp) (by rw [hpend']) (by simp [hmem''])
        (by rw [hmem'']) (by rw [hmem'']) (by rw [hloc', hl]; simp [ophaseOf, Ne.symm hj])
  | pMerge j k s => exact absurd rfl (hnm j k s)
  | pReset j k =>
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .loc j k) (o := LOp.reset)
      (k := fun _ => .pHint j) (by simp only [optParSketch, hl, OLoc.act])
    refine hI.tau_frame _ hpend' (by rw [hmem']; simp) rfl rfl (fun _ => rfl) (fun j' => ?_)
      (fun q => by rw [hloc']; simp) (by rw [hloc']; simp) (by rw [hloc']; simp [IsOPLoc])
    by_cases hj : j' = j
    · subst hj
      have hpr := (hI.thr j').none_of_busy (by rw [hl]; simp [ophaseOf])
      have hin := (hI.thr j')
      rw [hpr] at hin
      have hin := hin.transport.1
      rw [hl] at hin; simp only [ophaseOf, ite_true] at hin
      obtain ⟨hk, hB⟩ := hin
      subst hk
      refine hI.thr_prop j' hpr (by rw [hloc']; simp) (by rw [hpend']) (by rw [hmem']; simp)
        (by rw [hmem', Function.update_of_ne (OObj.loc_ne_loc (Or.inr (by
          cases C.mem (.cur j') <;> simp)))]) (List.prefix_refl _) (fun y hy => hy) (fun _ => ?_)
      rw [hloc', hmem']; simp only [Function.update_self, ophaseOf, ite_true]
      rw [Function.update_of_ne (by simp), hpr]
      exact ⟨hB, rfl⟩
    · exact hI.thr_frame j' (by rw [hloc']; simp) (by rw [hpend'])
        (fun k' => by rw [hmem', Function.update_of_ne (OObj.loc_ne_loc (Or.inl hj))])
        (by rw [hmem']; simp) (by rw [hmem']; simp) (by rw [hloc', hl]; simp [ophaseOf, Ne.symm hj])
  | pHint j =>
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .glob) (o := GOp.calcHint)
      (k := fun r => match r with
        | .hint h => .pSignal j h
        | _ => .pCheck j)
      (by simp only [optParSketch, hl, OLoc.act]; congr)
    have hmem'' : C'.mem = C.mem := by rw [hmem']; simp
    refine hI.tau_frame _ hpend' (by rw [hmem'']) rfl rfl (fun _ => rfl) (fun j' => ?_)
      (fun q => by rw [hloc']; simp) (by rw [hloc']; simp) (by rw [hloc']; simp [IsOPLoc])
    by_cases hj : j' = j
    · subst hj
      have hpr := (hI.thr j').none_of_busy (by rw [hl]; simp [ophaseOf])
      have hsafe : S.Safe (S.calcHint (C.mem .glob)) (upds g.vis) := by
        rw [hI.glob]; exact Composable.safe_calcHint _
      refine hI.thr_prop j' hpr (by rw [hloc']; simp) (by rw [hpend']) (by rw [hmem''])
        (by rw [hmem'']) (List.prefix_refl _) (fun y hy => hy) (fun h => ?_)
      rw [hl] at h; rw [hloc', hmem'', hpr]; simp only [ophaseOf, ite_true] at h
      simp only [Function.update_self, ophaseOf, ite_true]
      exact ⟨h.1, h.2, hsafe⟩
    · exact hI.thr_frame j' (by rw [hloc']; simp) (by rw [hpend']) (by simp [hmem''])
        (by rw [hmem'']) (by rw [hmem'']) (by rw [hloc', hl]; simp [ophaseOf, Ne.symm hj])
  | pSignal j h =>
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .prop j)
      (o := ROp.write (some h)) (k := fun _ => .pCheck (j + 1))
      (by simp only [optParSketch, hl, OLoc.act])
    refine hI.tau_frame _ hpend' (by rw [hmem']; simp) rfl rfl (fun _ => rfl) (fun j' => ?_)
      (fun q => by rw [hloc']; simp) (by rw [hloc']; simp) (by rw [hloc']; simp [IsOPLoc])
    by_cases hj : j' = j
    · subst hj
      have hpr := (hI.thr j').none_of_busy (by rw [hl]; simp [ophaseOf])
      refine hI.thr_prop j' hpr (by rw [hloc']; simp) (by rw [hpend']) (by rw [hmem']; simp)
        (by rw [hmem']; simp) (List.prefix_refl _) (fun y hy => hy) (fun h' => ?_)
      rw [hl] at h'; rw [hloc', hmem']; simp only [ophaseOf, ite_true] at h'
      simp only [Function.update_self, ophaseOf]
      rw [Function.update_of_ne (by simp)]
      exact ⟨h'.2.2, h'.1, h'.2.1, rfl⟩
    · exact hI.thr_frame j' (by rw [hloc']; simp) (by rw [hpend']) (fun k => by rw [hmem']; simp)
        (by rw [hmem']; simp) (by rw [hmem', Function.update_of_ne (by simpa using hj)])
        (by rw [hloc', hl]; simp [ophaseOf, Ne.symm hj])
  | _ =>
    rw [Impl.step_tau_ret_none (I := optParSketch S N Q b hint₀) (r := SkResp.ack)
      (l := C.loc .prop) (by simp [optParSketch, OLoc.act, hl])] at hs
    cases hs

/-- The merge step of the propagator preserves the invariant. -/
lemma oinv_step_tau_prop_merge {α : List (Lbl S N Q)} {C C' : OCfg S N Q}
    {g : OGhost S N Q} (hI : OInv b α C g)
    (hs : (optParSketch S N Q b hint₀).step C (.tau .prop) = some C') {j : Fin N} {k : Bool}
    {s : S.State} (hl : C.loc .prop = .pMerge j k s) :
    OInv b (α ++ [.tau .prop]) C' (ogstep α C g (.tau .prop)) := by
  have hg : ogstep α C g (.tau .prop) =
      { g with vis := g.vis ++ g.bIn j, bIn := Function.update g.bIn j [] } := by
    simp [ogstep, hl]
  rw [hg]
  obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .glob) (o := GOp.merge s)
    (k := fun _ => .pReset j k) (by simp only [optParSketch, hl, OLoc.act])
  have hpr := (hI.thr j).none_of_busy (by rw [hl]; simp [ophaseOf])
  have hin := hI.thr j
  rw [hpr] at hin
  have hin := hin.transport.1
  rw [hl] at hin; simp only [ophaseOf, ite_true] at hin
  obtain ⟨hk, hlen, hs_eq⟩ := hin
  set g' : OGhost S N Q := { g with vis := g.vis ++ g.bIn j, bIn := Function.update g.bIn j [] }
    with hg'
  have hbuf' : ∀ j', g'.buf j' = if j' = j then g.bAct j else g.buf j' := by
    intro j'
    by_cases hjj : j' = j
    · subst hjj; simp [g', OGhost.buf]
    · simp [g', OGhost.buf, hjj]
  have hbuf_sub : ∀ j', ∀ y ∈ g'.buf j', y ∈ g.buf j' := by
    intro j' y hy
    rw [hbuf' j'] at hy
    split_ifs at hy with hjj
    · subst hjj; exact List.mem_append_right _ hy
    · exact hy
  have hIn_sub : ∀ y ∈ g.bIn j, y ∈ g.buf j := fun y hy => List.mem_append_left _ hy
  have hFpre : upds g.vis <+: upds (g.vis ++ g.bIn j) := by simp
  have hcur : ∀ q, curOp (α ++ [.tau .prop]) q = curOp α q := fun q => curOp_append_tau α _ q
  have hother_buf : ∀ j', j' ≠ j → ∀ y ∈ g.buf j', y ∉ g.buf j := by
    intro j' hj' y hy hy'
    have := (hI.buf_shape j' y hy).1.symm.trans (hI.buf_shape j y hy').1
    exact hj' (by simpa using this)
  have hdisj : ∀ y ∈ g.bAct j, y ∉ g.bIn j := by
    intro y hy hy'
    have := hI.buf_nodup j
    simp only [OGhost.buf, List.nodup_append] at this
    exact this.2.2 y hy' y hy rfl
  exact {
    glob := by
      rw [hmem']; simp only [Function.update_self]
      rw [hI.glob, hs_eq, Composable.merge_run', upds_append]
    vis_legal := seqSketch_append hI.vis_legal _ fun e he => by
      obtain ⟨-, a, ha⟩ := hI.buf_shape j e (hIn_sub e he)
      rw [ha]; exact ⟨rfl, fun q h => by cases h⟩
    lin_nodup := hI.lin_nodup
    vis_nodup := List.nodup_append.2 ⟨hI.vis_nodup,
      (hI.buf_nodup j).sublist (List.sublist_append_left _ _),
      fun y hy y' hy' h => hI.buf_vis j y' (hIn_sub y' hy') (h ▸ hy)⟩
    lin_op := fun y hy => (opOf_tau α _ y.1).trans (hI.lin_op y hy)
    lin_resp := fun y hy r hr => hI.lin_resp y hy r ((respOf_tau α _ y.1).symm.trans hr)
    lin_comp := fun x hx => hI.lin_comp x ((completed_tau α _ x).1 hx)
    vis_lin := by
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hI.vis_lin y hy
      · exact hI.buf_lin j y (hIn_sub y hy)
    lin_cover := by
      intro y hy
      rcases hI.lin_cover y hy with h | ⟨j', hj'⟩
      · exact Or.inl (List.mem_append_left _ h)
      · by_cases hjj : j' = j
        · subst hjj
          rcases List.mem_append.1 hj' with h | h
          · exact Or.inl (List.mem_append_right _ h)
          · exact Or.inr ⟨j', by rw [hbuf']; simpa using h⟩
        · exact Or.inr ⟨j', by rw [hbuf']; simpa [hjj] using hj'⟩
    buf_lin := fun j' y hy => hI.buf_lin j' y (hbuf_sub j' y hy)
    buf_vis := by
      intro j' y hy
      show y ∉ g.vis ++ g.bIn j
      simp only [List.mem_append, not_or]
      refine ⟨hI.buf_vis j' y (hbuf_sub j' y hy), fun h => ?_⟩
      rw [hbuf' j'] at hy
      split_ifs at hy with hjj
      · exact hdisj y hy h
      · exact hother_buf j' hjj y hy (hIn_sub y h)
    buf_shape := fun j' y hy => hI.buf_shape j' y (hbuf_sub j' y hy)
    buf_nodup := by
      intro j'
      rw [hbuf' j']
      split_ifs with hjj
      · subst hjj; exact (hI.buf_nodup j').sublist (List.sublist_append_right _ _)
      · exact hI.buf_nodup j'
    thr := by
      intro j'
      simp only [hcur]
      by_cases hjj : j' = j
      · subst hjj
        refine hI.thr_prop j' hpr (by rw [hloc']; simp) (by rw [hpend']) (by rw [hmem']; simp)
          (by rw [hmem']; simp) hFpre (fun y hy => hy) (fun _ => ?_)
        rw [hloc', hmem']; simp only [Function.update_self, ophaseOf, ite_true]
        rw [Function.update_of_ne (by simp), hpr]
        exact ⟨hk, by simp [g']⟩
      · have := (hI.thr j').mono hFpre (fun y hy => hy)
        refine this.congr (by rw [hloc']; simp) (by rw [hpend']) (by funext k'; rw [hmem']; simp)
          (by rw [hmem']; simp) (by rw [hmem']; simp)
          (by rw [hloc', hl]; simp [ophaseOf, Ne.symm hjj])
          (by simp [g', Function.update_of_ne hjj]) rfl rfl
    qry := fun q => by
      simpa [hloc', hpend', hcur] using hI.qry q
    lin_shape := hI.lin_shape
    prop_live := by rw [hloc']; simp
    prop_kind := by rw [hloc']; simp [IsOPLoc] }

/-- Internal steps of the propagator preserve the invariant. -/
lemma oinv_step_tau_prop {α : List (Lbl S N Q)} {C C' : OCfg S N Q}
    {g : OGhost S N Q} (hI : OInv b α C g)
    (hs : (optParSketch S N Q b hint₀).step C (.tau .prop) = some C') :
    OInv b (α ++ [.tau .prop]) C' (ogstep α C g (.tau .prop)) := by
  by_cases h : ∃ j k s, C.loc .prop = .pMerge j k s
  · obtain ⟨j, k, s, hl⟩ := h
    exact oinv_step_tau_prop_merge hI hs hl
  · push Not at h
    exact oinv_step_tau_prop_nomerge hI hs h

/-- Snapshot steps of query threads preserve the invariant. -/
lemma oinv_step_tau_qry {α : List (Lbl S N Q)} {C C' : OCfg S N Q}
    {g : OGhost S N Q} {q : Q} (hC : (optParSketch S N Q b hint₀).run α = some C)
    (hI : OInv b α C g)
    (hs : (optParSketch S N Q b hint₀).step C (.tau (.qry q)) = some C') :
    OInv b (α ++ [.tau (.qry q)]) C' (ogstep α C g (.tau (.qry q))) := by
  have hpne := (Impl.step_tau hs).1
  have hQ := hI.qry q
  generalize hl : C.loc (.qry q) = l at hQ
  cases l with
  | qIdle => exact absurd hQ hpne
  | qRet v =>
    rw [Impl.step_tau_ret_none (I := optParSketch S N Q b hint₀) (r := .val v) (l := .qIdle)
      (by simp [optParSketch, OLoc.act, hl])] at hs
    cases hs
  | qSnap a =>
    obtain ⟨hpd, hnotin⟩ := hQ
    set e : Entry (Proc N Q) S.toSketch :=
      (curOp α (.qry q), .query a, .val (S.snapQuery (S.snapshot (C.mem .glob)) a)) with he
    have hg : ogstep α C g (.tau (.qry q)) =
        { g with lin := g.lin ++ [e], vis := g.vis ++ [e] } := by
      simp [ogstep, hl, he]
    rw [hg]
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .glob) (o := GOp.snapshot)
      (k := fun r => match r with
        | .snap x => .qRet (S.snapQuery x a)
        | _ => .qIdle) (by simp only [optParSketch, hl, OLoc.act]; congr)
    have hmem'' : C'.mem = C.mem := by rw [hmem']; simp
    have heL : e ∉ g.lin := fun h => hnotin (List.mem_map_of_mem (f := Prod.fst) h)
    have hcur : ∀ p, curOp (α ++ [.tau (.qry q)]) p = curOp α p :=
      fun p => curOp_append_tau α _ p
    have hlin : ∀ y ∈ g.lin, y ∈ g.lin ++ [e] := fun y hy => List.mem_append_left _ hy
    have hopcur := ((optParSketch S N Q b hint₀).run_pend_curOp hC hpd)
    exact {
      glob := by rw [hmem'', hI.glob]; simp [he]
      vis_legal := seqSketch_concat hI.vis_legal e (by
        simp [he, seqResp, S.snapQuery_snapshot, hI.glob])
      lin_nodup := by
        rw [List.map_append, List.nodup_append]
        refine ⟨hI.lin_nodup, by simp, ?_⟩
        intro x hx y hy hxy
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
        subst hy hxy; exact hnotin (by simpa [he] using hx)
      vis_nodup := List.nodup_append.2 ⟨hI.vis_nodup, by simp,
        by simp only [List.mem_singleton]; rintro y hy _ rfl rfl; exact heL (hI.vis_lin _ hy)⟩
      lin_op := by
        intro y hy
        rw [opOf_tau]
        rcases List.mem_append.1 hy with hy | hy
        · exact hI.lin_op y hy
        · simp only [List.mem_singleton] at hy; subst hy; exact hopcur.2.2
      lin_resp := by
        intro y hy r hr
        rw [respOf_tau] at hr
        rcases List.mem_append.1 hy with hy | hy
        · exact hI.lin_resp y hy r hr
        · simp only [List.mem_singleton] at hy; subst hy
          exact absurd (Completed.of_respOf_eq_some hr) hopcur.2.1
      lin_comp := fun x hx => by
        have := hI.lin_comp x ((completed_tau α _ x).1 hx)
        rw [List.map_append]; exact List.mem_append_left _ this
      vis_lin := by
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact hlin _ (hI.vis_lin y hy)
        · exact List.mem_append_right _ hy
      lin_cover := by
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · rcases hI.lin_cover y hy with h | h
          · exact Or.inl (List.mem_append_left _ h)
          · exact Or.inr h
        · exact Or.inl (List.mem_append_right _ hy)
      buf_lin := fun j y hy => hlin _ (hI.buf_lin j y hy)
      buf_vis := by
        intro j y hy hy'
        rcases List.mem_append.1 hy' with hy' | hy'
        · exact hI.buf_vis j y hy hy'
        · simp only [List.mem_singleton] at hy'; subst hy'; exact heL (hI.buf_lin j _ hy)
      buf_shape := hI.buf_shape
      buf_nodup := hI.buf_nodup
      thr := fun j => by
        rw [hcur]
        exact ((hI.thr j).mono (by simp [he]) hlin).congr (by rw [hloc']; simp)
          (by rw [hpend']) (by rw [hmem'']) (by rw [hmem'']) (by rw [hmem''])
          (by rw [hloc']; simp) rfl rfl rfl
      qry := fun q' => by
        rw [hcur]
        by_cases hq : q' = q
        · subst hq
          rw [hloc', Function.update_self, hpend']
          exact ⟨a, hpd, by simp [he]⟩
        · rw [hloc', hpend', Function.update_of_ne (by simpa using hq)]
          refine (hI.qry q').mono hlin ?_
          intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · exact Or.inl hy
          · right; simp only [List.mem_singleton] at hy; subst hy
            simp only [he, curOp, ne_eq, Prod.mk.injEq, Proc.qry.injEq, not_and]
            intro h; exact absurd h.symm hq
      lin_shape := by
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact hI.lin_shape y hy
        · simp only [List.mem_singleton] at hy; subst hy
          exact Or.inr ⟨q, rfl, a, _, rfl⟩
      prop_live := by rw [hloc', hpend']; simpa using hI.prop_live
      prop_kind := by rw [hloc']; simpa using hI.prop_kind }
  | _ => exact hQ.elim

/-- Response steps preserve the invariant. -/
lemma oinv_step_ret {α : List (Lbl S N Q)} {C C' : OCfg S N Q} {g : OGhost S N Q}
    {p : Proc N Q} {r : SkResp S.toSketch} (hI : OInv b α C g)
    (hs : (optParSketch S N Q b hint₀).step C (.ret p r) = some C') :
    OInv b (α ++ [.ret p r]) C' (ogstep α C g (.ret p r)) := by
  have hg : ogstep α C g (.ret p r) = g := rfl
  rw [hg]
  obtain ⟨hpne, hpend', hmem', l', hact, hloc'⟩ := Impl.step_ret hs
  have hcur_ne : ∀ p', p' ≠ p → curOp (α ++ [.ret p r]) p' = curOp α p' :=
    fun p' h => curOp_append_ret_of_ne α r (Ne.symm h)
  have key : ∀ x, x ∈ g.lin.map Prod.fst → x.1 = p →
      (x ≠ curOp α p → respOf (α ++ [.ret p r]) x = respOf α x) := by
    intro x _ hx hne
    refine respOf_concat_ret_of_ne hne fun _ => ?_
    have : x.2 ≠ (respsOf α p).length := fun h => hne (by
      obtain ⟨x1, x2⟩ := x; simp only at hx h; subst hx; simp [curOp, h])
    omega
  have common : ∀ (hin : curOp α p ∈ g.lin.map Prod.fst)
      (hresp : ∀ y ∈ g.lin, y.1 = curOp α p → y.2.2 = r)
      (hthr : ∀ j, OTI b (C'.loc (.upd j)) (C'.pend (.upd j)) (fun k => C'.mem (.loc j k))
        (C'.mem (.cur j)) (C'.mem (.prop j)) (ophaseOf j (C'.loc .prop)) (g.bIn j) (g.bAct j)
        (upds g.vis) (curOp (α ++ [.ret p r]) (.upd j)) g.lin)
      (hqry : ∀ q, OQI (C'.loc (.qry q)) (C'.pend (.qry q)) (curOp (α ++ [.ret p r]) (.qry q))
        g.lin)
      (hlive : C'.pend .prop ≠ none → C'.loc .prop ≠ .pIdle) (hkind : IsOPLoc (C'.loc .prop)),
      OInv b (α ++ [.ret p r]) C' g := by
    intro hin hresp hthr hqry hlive hkind
    exact {
      glob := by rw [hmem']; exact hI.glob
      vis_legal := hI.vis_legal
      lin_nodup := hI.lin_nodup
      vis_nodup := hI.vis_nodup
      lin_op := fun y hy => opOf_append_of_eq_some (hI.lin_op y hy) _
      lin_resp := by
        intro y hy r' hr
        by_cases hy1 : y.1 = curOp α p
        · rw [hy1, respOf_concat_ret_curOp] at hr
          cases hr; exact hresp y hy hy1
        · by_cases hp : y.1.1 = p
          · rw [key y.1 (List.mem_map_of_mem hy) hp hy1] at hr
            exact hI.lin_resp y hy r' hr
          · rw [respOf_concat_of_ne (fun r'' h => hp (by cases h; rfl))] at hr
            exact hI.lin_resp y hy r' hr
      lin_comp := fun x hx => by
        rcases completed_concat_ret hx with h | h
        · exact hI.lin_comp x h
        · rw [h]; exact hin
      vis_lin := hI.vis_lin
      lin_cover := hI.lin_cover
      buf_lin := hI.buf_lin
      buf_vis := hI.buf_vis
      buf_shape := hI.buf_shape
      buf_nodup := hI.buf_nodup
      thr := hthr
      qry := hqry
      lin_shape := hI.lin_shape
      prop_live := hlive
      prop_kind := hkind }
  cases p with
  | upd j =>
    have hT := hI.thr j
    generalize hl : C.loc (.upd j) = l at hT
    cases l with
    | oRet cur c h =>
      have hact' : (optParSketch S N Q b hint₀).act (.upd j) (C.loc (.upd j)) =
          .ret .ack (.oIdle cur c h) := by simp [optParSketch, OLoc.act, hl]
      obtain ⟨rfl, -, -, hloc''⟩ := Impl.step_ret_ret hs hact'
      obtain ⟨⟨-, hc, hlen, hls, hcr, hsafe, hx⟩, hin⟩ := hT
      refine common hx (fun y hy hy1 => ?_) (fun j' => ?_) (fun q => ?_) ?_ ?_
      · rcases hI.lin_shape y hy with ⟨j'', h1, a, h2⟩ | ⟨q, h1, a, v, h2⟩
        · rw [h2]
        · rw [hy1] at h1; cases h1
      · by_cases hj : j' = j
        · subst hj
          have hph' : ophaseOf j' (C'.loc .prop) = ophaseOf j' (C.loc .prop) := by
            rw [hloc'', Function.update_of_ne (by simp)]
          rw [hph', hloc'', Function.update_self, hpend', Function.update_self, hmem']
          exact ⟨⟨rfl, hc, hlen, hls, hcr, hsafe⟩, hin⟩
        · rw [hcur_ne _ (by simpa using hj)]
          exact hI.thr_frame j' (by rw [hloc'', Function.update_of_ne (by simpa using hj)])
            (by rw [hpend', Function.update_of_ne (by simpa using hj)]) (by simp [hmem'])
            (by rw [hmem']) (by rw [hmem']) (by rw [hloc'', Function.update_of_ne (by simp)])
      · rw [hcur_ne _ (by simp), hloc'', hpend', Function.update_of_ne (by simp),
          Function.update_of_ne (by simp)]
        exact hI.qry q
      · rw [hloc'', hpend', Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
        exact hI.prop_live
      · rw [hloc'', Function.update_of_ne (by simp)]; exact hI.prop_kind
    | oIdle cur c h => exact absurd hT.1.1 hpne
    | oApply a cur c h =>
      rw [Impl.step_ret_none_of_not_ret (I := optParSketch S N Q b hint₀)
        (by simp [optParSketch, OLoc.act, hl])] at hs; cases hs
    | oWait cur h =>
      rw [Impl.step_ret_none_of_not_ret (I := optParSketch S N Q b hint₀)
        (by simp [optParSketch, OLoc.act, hl])] at hs; cases hs
    | oFlip cur h =>
      rw [Impl.step_ret_none_of_not_ret (I := optParSketch S N Q b hint₀)
        (by simp [optParSketch, OLoc.act, hl])] at hs; cases hs
    | oSignal cur h =>
      rw [Impl.step_ret_none_of_not_ret (I := optParSketch S N Q b hint₀)
        (by simp [optParSketch, OLoc.act, hl])] at hs; cases hs
    | _ => exact hT.elim
  | prop =>
    have hl := hI.prop_live hpne
    have hk := hI.prop_kind
    generalize hl' : C.loc .prop = l at hl hk
    cases l with
    | pIdle => exact absurd rfl hl
    | pCheck _ | pCur _ | pRead _ _ | pMerge _ _ _ | pReset _ _ | pHint _ | pSignal _ _ =>
      rw [Impl.step_ret_none_of_not_ret (I := optParSketch S N Q b hint₀)
        (by simp [optParSketch, OLoc.act, hl'])] at hs; cases hs
    | _ => exact hk.elim
  | qry q =>
    have hQ := hI.qry q
    generalize hl : C.loc (.qry q) = l at hQ
    cases l with
    | qRet v =>
      have hact' : (optParSketch S N Q b hint₀).act (.qry q) (C.loc (.qry q)) =
          .ret (.val v) .qIdle := by simp [optParSketch, OLoc.act, hl]
      obtain ⟨rfl, -, -, hloc''⟩ := Impl.step_ret_ret hs hact'
      obtain ⟨a, -, hmem⟩ := hQ
      refine common (List.mem_map_of_mem (f := Prod.fst) hmem)
        (fun y hy hy1 => by rw [eq_of_mem_of_fst_eq hI.lin_nodup hy hmem hy1]) (fun j => ?_)
        (fun q' => ?_) ?_ ?_
      · rw [hcur_ne _ (by simp)]
        exact hI.thr_frame j (by rw [hloc'', Function.update_of_ne (by simp)])
          (by rw [hpend', Function.update_of_ne (by simp)]) (by simp [hmem'])
          (by rw [hmem']) (by rw [hmem']) (by rw [hloc'', Function.update_of_ne (by simp)])
      · by_cases hq : q' = q
        · subst hq
          rw [hloc'', hpend', Function.update_self, Function.update_self]
          rfl
        · rw [hcur_ne _ (by simpa using hq), hloc'', hpend',
            Function.update_of_ne (by simpa using hq), Function.update_of_ne (by simpa using hq)]
          exact hI.qry q'
      · rw [hloc'', hpend', Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
        exact hI.prop_live
      · rw [hloc'', Function.update_of_ne (by simp)]; exact hI.prop_kind
    | qIdle => exact absurd hQ hpne
    | qSnap a =>
      rw [Impl.step_ret_none_of_not_ret (I := optParSketch S N Q b hint₀)
        (by simp [optParSketch, OLoc.act, hl])] at hs; cases hs
    | _ => exact hQ.elim

/-- Frame lemma for invocations that do not change the ghost state. -/
lemma OInv.inv_frame {α : List (Lbl S N Q)} {C C' : OCfg S N Q} {g : OGhost S N Q}
    (hI : OInv b α C g) (p : Proc N Q) (o : SkOp S.toSketch) (hmem : C'.mem = C.mem)
    (hthr : ∀ j, OTI b (C'.loc (.upd j)) (C'.pend (.upd j)) (fun k => C'.mem (.loc j k))
      (C'.mem (.cur j)) (C'.mem (.prop j)) (ophaseOf j (C'.loc .prop)) (g.bIn j) (g.bAct j)
      (upds g.vis) (curOp α (.upd j)) g.lin)
    (hq : ∀ q, OQI (C'.loc (.qry q)) (C'.pend (.qry q)) (curOp α (.qry q)) g.lin)
    (hlive : C'.pend .prop ≠ none → C'.loc .prop ≠ .pIdle) (hkind : IsOPLoc (C'.loc .prop)) :
    OInv b (α ++ [.inv p o]) C' g where
  glob := by rw [hmem]; exact hI.glob
  vis_legal := hI.vis_legal
  lin_nodup := hI.lin_nodup
  vis_nodup := hI.vis_nodup
  lin_op y hy := opOf_append_of_eq_some (hI.lin_op y hy) _
  lin_resp y hy r hr := hI.lin_resp y hy r
    ((respOf_append_of_not_ret (by intro _ _ h; cases h) y.1).symm.trans hr)
  lin_comp x hx := hI.lin_comp x ((completed_concat_of_not_ret (by intro _ _ h; cases h)).1 hx)
  vis_lin := hI.vis_lin
  lin_cover := hI.lin_cover
  buf_lin := hI.buf_lin
  buf_vis := hI.buf_vis
  buf_shape := hI.buf_shape
  buf_nodup := hI.buf_nodup
  thr j := by simpa using hthr j
  qry q := by simpa using hq q
  lin_shape := hI.lin_shape
  prop_live := hlive
  prop_kind := hkind

/-- Invocation steps preserve the invariant. -/
lemma oinv_step_inv {α : List (Lbl S N Q)} {C C' : OCfg S N Q} {g : OGhost S N Q}
    {p : Proc N Q} {o : SkOp S.toSketch} (hC : (optParSketch S N Q b hint₀).run α = some C)
    (hI : OInv b α C g) (hs : (optParSketch S N Q b hint₀).step C (.inv p o) = some C') :
    OInv b (α ++ [.inv p o]) C' (ogstep α C g (.inv p o)) := by
  obtain ⟨hpend, hall, hpend', hloc', hmem'⟩ := Impl.step_inv hs
  have hidle := (optParSketch S N Q b hint₀).run_idle_counts hC hpend
  have hnotid := hI.curOp_not_mem hC hpend
  have hresp : ∀ x, respOf (α ++ [.inv p o]) x = respOf α x :=
    respOf_append_of_not_ret (by intro _ _ h; cases h)
  have hcomp : ∀ x, Completed (α ++ [.inv p o]) x ↔ Completed α x :=
    fun x => completed_concat_of_not_ret (by intro _ _ h; cases h)
  have hcur : ∀ q, curOp (α ++ [.inv p o]) q = curOp α q := fun q => curOp_append_inv α p q o
  have hnewop : opOf (α ++ [.inv p o]) (curOp α p) = some o := opOf_concat_inv_curOp hidle
  have hnewresp : ∀ r, respOf α (curOp α p) ≠ some r := fun r h =>
    not_completed_curOp α p (Completed.of_respOf_eq_some h)
  have thr_other : ∀ j, Proc.upd j ≠ p →
      OTI b (C'.loc (.upd j)) (C'.pend (.upd j)) (fun k => C'.mem (.loc j k))
        (C'.mem (.cur j)) (C'.mem (.prop j)) (ophaseOf j (C'.loc .prop)) (g.bIn j) (g.bAct j)
        (upds g.vis) (curOp α (.upd j)) g.lin := by
    intro j hj
    have hprop : C'.loc .prop = C.loc .prop ∨ p = .prop := by
      by_cases h : p = .prop
      · exact Or.inr h
      · left; rw [hloc', Function.update_of_ne (Ne.symm h)]
    refine hI.thr_frame j (by rw [hloc', Function.update_of_ne hj])
      (by rw [hpend', Function.update_of_ne hj]) (by simp [hmem']) (by rw [hmem'])
      (by rw [hmem']) ?_
    rcases hprop with h | rfl
    · rw [h]
    · rw [hloc', Function.update_self]
      generalize C.loc .prop = l
      cases o <;> cases l <;> rfl
  have qry_other : ∀ q, Proc.qry q ≠ p → ∀ lin', (∀ y ∈ g.lin, y ∈ lin') →
      (∀ y ∈ lin', y ∈ g.lin ∨ y.1 ≠ curOp α (.qry q)) →
      OQI (C'.loc (.qry q)) (C'.pend (.qry q)) (curOp α (.qry q)) lin' := by
    intro q hq lin' h1 h2
    refine ((hI.qry q).mono h1 h2) |> fun h => ?_
    rwa [hloc', hpend', Function.update_of_ne hq, Function.update_of_ne hq]
  have live_other : p ≠ .prop → (C'.pend .prop ≠ none → C'.loc .prop ≠ .pIdle) ∧
      IsOPLoc (C'.loc .prop) := by
    intro hp
    rw [hloc', hpend', Function.update_of_ne (Ne.symm hp), Function.update_of_ne (Ne.symm hp)]
    exact ⟨hI.prop_live, hI.prop_kind⟩
  cases p with
  | prop =>
    cases o with
    | update _ => exact hall.elim
    | query _ => exact hall.elim
    | propagate =>
    have hg : ogstep α C g (.inv .prop .propagate) = g := rfl
    rw [hg]
    have hk := hI.prop_kind
    refine hI.inv_frame _ _ hmem' (fun j => thr_other j (by simp)) (fun q =>
      by simpa using qry_other q (by simp) g.lin (fun y hy => hy) (fun y hy => Or.inl hy))
      (by rw [hloc', Function.update_self]; generalize C.loc .prop = l at hk
          cases l <;> simp [optParSketch, OLoc.invoke, IsOPLoc] at hk ⊢) ?_
    rw [hloc', Function.update_self]; generalize C.loc .prop = l at hk
    cases l <;> simp [optParSketch, OLoc.invoke, IsOPLoc] at hk ⊢
  | qry q =>
    cases o with
    | update _ => exact hall.elim
    | propagate => exact hall.elim
    | query a =>
    have hg : ogstep α C g (.inv (.qry q) (.query a)) = g := rfl
    rw [hg]
    have hQ := hI.qry q
    have hlq : C.loc (.qry q) = .qIdle := by
      generalize C.loc (.qry q) = l at hQ
      cases l with
      | qIdle => rfl
      | qSnap a' => rw [hpend] at hQ; cases hQ.1
      | qRet v => obtain ⟨_, h1, _⟩ := hQ; rw [hpend] at h1; cases h1
      | _ => exact hQ.elim
    obtain ⟨hl1, hl2⟩ := live_other (by simp)
    refine hI.inv_frame _ _ hmem' (fun j => thr_other j (by simp)) (fun q' => ?_) hl1 hl2
    by_cases hq : q' = q
    · subst hq
      rw [hloc', hpend', Function.update_self, Function.update_self, hlq]
      exact ⟨rfl, hnotid⟩
    · simpa using qry_other q' (by simpa using hq) g.lin (fun y hy => hy) (fun y hy => Or.inl hy)
  | upd j =>
    cases o with
    | query _ => exact hall.elim
    | propagate => exact hall.elim
    | update a =>
    have hT := hI.thr j
    obtain ⟨cur, c, h, hl⟩ : ∃ cur c h, C.loc (.upd j) = .oIdle cur c h := by
      generalize C.loc (.upd j) = l at hT
      cases l
      case oIdle cur c h => exact ⟨cur, c, h, rfl⟩
      case oApply => exact absurd hpend (by rw [hT.1.1]; simp)
      case oRet => obtain ⟨⟨⟨a, ha⟩, -⟩, -⟩ := hT; rw [hpend] at ha; cases ha
      case oWait => obtain ⟨⟨⟨a, ha⟩, -⟩, -⟩ := hT; rw [hpend] at ha; cases ha
      case oFlip => obtain ⟨⟨a, ha⟩, -⟩ := hT; rw [hpend] at ha; cases ha
      case oSignal => obtain ⟨⟨a, ha⟩, -⟩ := hT; rw [hpend] at ha; cases ha
      all_goals exact hT.elim
    rw [hl] at hT
    obtain ⟨⟨-, hc, hlen, hls, hcr, hsafe⟩, hin⟩ := hT
    set e : Entry (Proc N Q) S.toSketch := (curOp α (.upd j), .update a, .ack) with he
    have heL : e ∉ g.lin := fun h' => hnotid (List.mem_map_of_mem (f := Prod.fst) h')
    have hlin : ∀ y ∈ g.lin, y ∈ g.lin ++ [e] := fun y hy => List.mem_append_left _ hy
    obtain ⟨hl1, hl2⟩ := live_other (by simp)
    have hph' : ophaseOf j (C'.loc .prop) = ophaseOf j (C.loc .prop) := by
      rw [hloc', Function.update_of_ne (by simp)]
    have lin_nodup' : ((g.lin ++ [e]).map Prod.fst).Nodup := by
      rw [List.map_append, List.nodup_append]
      refine ⟨hI.lin_nodup, by simp, ?_⟩
      intro x hx y hy hxy
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
      subst hy hxy; exact hnotid (by simpa [he] using hx)
    have lin_op' : ∀ y ∈ g.lin ++ [e],
        opOf (α ++ [.inv (.upd j) (.update a)]) y.1 = some y.2.1 := by
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact opOf_append_of_eq_some (hI.lin_op y hy) _
      · simp only [List.mem_singleton] at hy; subst hy; exact hnewop
    have lin_resp' : ∀ y ∈ g.lin ++ [e], ∀ r,
        respOf (α ++ [.inv (.upd j) (.update a)]) y.1 = some r → y.2.2 = r := by
      intro y hy r hr
      rw [hresp] at hr
      rcases List.mem_append.1 hy with hy | hy
      · exact hI.lin_resp y hy r hr
      · simp only [List.mem_singleton] at hy; subst hy; exact absurd hr (hnewresp r)
    have lin_comp' : ∀ x, Completed (α ++ [.inv (.upd j) (.update a)]) x →
        x ∈ (g.lin ++ [e]).map Prod.fst := fun x hx => by
      rw [List.map_append]; exact List.mem_append_left _ (hI.lin_comp x ((hcomp x).1 hx))
    have lin_shape' : ∀ y ∈ g.lin ++ [e],
        (∃ j, y.1.1 = .upd j ∧ ∃ a, y.2 = (.update a, .ack)) ∨
        (∃ q, y.1.1 = .qry q ∧ ∃ a v, y.2 = (.query a, .val v)) := by
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hI.lin_shape y hy
      · simp only [List.mem_singleton] at hy; subst hy; exact Or.inl ⟨j, rfl, a, rfl⟩
    have qry' : ∀ q, OQI (C'.loc (.qry q)) (C'.pend (.qry q))
        (curOp (α ++ [.inv (.upd j) (.update a)]) (.qry q)) (g.lin ++ [e]) := by
      intro q
      rw [hcur]
      refine qry_other q (by simp) _ hlin fun y hy => ?_
      rcases List.mem_append.1 hy with hy | hy
      · exact Or.inl hy
      · right; simp only [List.mem_singleton] at hy; subst hy; simp [he, curOp]
    by_cases hsa : S.shouldAdd h a = true
    · -- accepted: the update joins the active buffer of thread `j`
      have hg : ogstep α C g (.inv (.upd j) (.update a)) =
          { g with lin := g.lin ++ [e], bAct := Function.update g.bAct j (g.bAct j ++ [e]) } := by
        simp [ogstep, hl, hsa, he]
      rw [hg]
      set g' : OGhost S N Q :=
        { g with lin := g.lin ++ [e], bAct := Function.update g.bAct j (g.bAct j ++ [e]) }
        with hg'
      have hbuf' : ∀ j', g'.buf j' = if j' = j then g.buf j ++ [e] else g.buf j' := by
        intro j'
        by_cases hjj : j' = j
        · subst hjj; simp [g', OGhost.buf]
        · simp [g', OGhost.buf, hjj]
      exact {
        glob := by rw [hmem']; exact hI.glob
        vis_legal := hI.vis_legal
        lin_nodup := lin_nodup'
        vis_nodup := hI.vis_nodup
        lin_op := lin_op'
        lin_resp := lin_resp'
        lin_comp := lin_comp'
        vis_lin := fun y hy => hlin _ (hI.vis_lin y hy)
        lin_cover := by
          intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · rcases hI.lin_cover y hy with h' | ⟨j', hj'⟩
            · exact Or.inl h'
            · right; refine ⟨j', ?_⟩
              rw [hbuf']
              split_ifs with hjj
              · subst hjj; simp [hj']
              · exact hj'
          · right; refine ⟨j, ?_⟩; simp only [List.mem_singleton] at hy; rw [hbuf']; simp [hy]
        buf_lin := by
          intro j' y hy
          rw [hbuf'] at hy
          split_ifs at hy with hjj
          · simp only [List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact hlin _ (hI.buf_lin _ y hy)
            · exact List.mem_append_right _ (List.mem_singleton_self _)
          · exact hlin _ (hI.buf_lin j' y hy)
        buf_vis := by
          intro j' y hy
          rw [hbuf'] at hy
          split_ifs at hy with hjj
          · simp only [List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact hI.buf_vis _ y hy
            · exact fun h' => heL (hI.vis_lin _ h')
          · exact hI.buf_vis j' y hy
        buf_shape := by
          intro j' y hy
          rw [hbuf'] at hy
          split_ifs at hy with hjj
          · subst hjj
            simp only [List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact hI.buf_shape _ y hy
            · exact ⟨rfl, a, rfl⟩
          · exact hI.buf_shape j' y hy
        buf_nodup := by
          intro j'
          rw [hbuf']
          split_ifs with hjj
          · exact (List.nodup_append.2 ⟨hI.buf_nodup _, by simp, by
              simp only [List.mem_singleton]
              rintro y hy _ rfl rfl; exact heL (hI.buf_lin _ _ hy)⟩)
          · exact hI.buf_nodup j'
        thr := by
          intro j'
          rw [hcur]
          by_cases hjj : j' = j
          · subst hjj
            have hinv : (optParSketch S N Q b hint₀).invoke (.upd j') (.oIdle cur c h)
                (.update a) = .oApply a cur c h := by
              simp [optParSketch, OLoc.invoke, hsa]
            rw [hph', hloc', hpend', Function.update_self, Function.update_self, hl, hinv]
            simp only [g', Function.update_self]
            refine ⟨⟨rfl, hc, ⟨g.bAct j', rfl, hlen, by rw [hmem']; exact hls⟩,
              by rw [hmem']; exact hcr, hsafe⟩, ?_⟩
            rw [hmem']; exact hin
          · have := (thr_other j' (by simpa using hjj)).mono (List.prefix_refl _) hlin
            exact this.congr rfl rfl rfl rfl rfl rfl rfl (by simp [g', hjj]) rfl
        qry := qry'
        lin_shape := lin_shape'
        prop_live := hl1
        prop_kind := hl2 }
    · -- filtered out: visible at once, the summary does not change
      have hsa' : S.shouldAdd h a = false := by simpa using hsa
      have hg : ogstep α C g (.inv (.upd j) (.update a)) =
          { g with lin := g.lin ++ [e], vis := g.vis ++ [e] } := by
        simp [ogstep, hl, hsa', he]
      rw [hg]
      have hFpre : upds g.vis <+: upds (g.vis ++ [e]) := by simp
      exact {
        glob := by
          rw [hmem', hI.glob]; simp only [upds_append, he, upds_update]
          exact (hsafe.run_concat hsa').symm
        vis_legal := seqSketch_concat hI.vis_legal e rfl
        lin_nodup := lin_nodup'
        vis_nodup := List.nodup_append.2 ⟨hI.vis_nodup, by simp, by
          simp only [List.mem_singleton]
          rintro y hy _ rfl rfl; exact heL (hI.vis_lin _ hy)⟩
        lin_op := lin_op'
        lin_resp := lin_resp'
        lin_comp := lin_comp'
        vis_lin := by
          intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · exact hlin _ (hI.vis_lin y hy)
          · exact List.mem_append_right _ hy
        lin_cover := by
          intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · rcases hI.lin_cover y hy with h' | h'
            · exact Or.inl (List.mem_append_left _ h')
            · exact Or.inr h'
          · exact Or.inl (List.mem_append_right _ hy)
        buf_lin := fun j' y hy => hlin _ (hI.buf_lin j' y hy)
        buf_vis := by
          intro j' y hy hy'
          rcases List.mem_append.1 hy' with hy' | hy'
          · exact hI.buf_vis j' y hy hy'
          · simp only [List.mem_singleton] at hy'; subst hy'; exact heL (hI.buf_lin j' _ hy)
        buf_shape := hI.buf_shape
        buf_nodup := hI.buf_nodup
        thr := by
          intro j'
          rw [hcur]
          by_cases hjj : j' = j
          · subst hjj
            have hinv : (optParSketch S N Q b hint₀).invoke (.upd j') (.oIdle cur c h)
                (.update a) = .oRet cur c h := by
              simp [optParSketch, OLoc.invoke, hsa']
            rw [hph', hloc', hpend', Function.update_self, Function.update_self, hl, hinv]
            refine ⟨⟨⟨a, rfl⟩, hc, hlen, by rw [hmem']; exact hls, by rw [hmem']; exact hcr,
              hsafe.mono hFpre, by simp [he]⟩, ?_⟩
            rw [hmem']; exact hin.mono hFpre
          · exact (thr_other j' (by simpa using hjj)).mono hFpre hlin
        qry := qry'
        lin_shape := lin_shape'
        prop_live := hl1
        prop_kind := hl2 }

end Podc.ConcurrentSketches
