import Papers.PODC2019.ConcurrentSketches.ParSketchInv
import Papers.PODC2019.ConcurrentSketches.ExecLemmas

/-!
# `ParSketch`: the invariant is inductive
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentSketches

open Cslib.SharedMemory

variable {S : Composable} {N : ℕ} {Q : Type} [NeZero N] [DecidableEq Q]

/-- The invariant holds initially, provided the initial hint is safe for the empty stream and
`b > 0`. -/
lemma inv_init {b : ℕ} (hb : 0 < b) {hint₀ : S.Hint} (h₀ : S.Safe hint₀ []) :
    Inv b ([] : List (Lbl S N Q)) (parSketch S N Q b hint₀).initCfg (Ghost.init S N Q) where
  glob := rfl
  vis_legal := seqSketch_nil
  lin_nodup := List.nodup_nil
  vis_nodup := List.nodup_nil
  lin_op := by simp [Ghost.init]
  lin_resp := by simp [Ghost.init]
  lin_comp := by simp [Completed]
  vis_lin := by simp [Ghost.init]
  lin_cover := by simp [Ghost.init]
  buf_lin := by simp [Ghost.init]
  buf_vis := by simp [Ghost.init]
  buf_shape := by simp [Ghost.init]
  buf_nodup := by simp [Ghost.init]
  thr j := ⟨rfl, hb, rfl, rfl, by simp [Impl.initCfg, parSketch], by simpa [Ghost.init] using h₀,
    rfl⟩
  qry q := rfl
  lin_shape := by simp [Ghost.init]
  prop_live := by simp [Impl.initCfg, parSketch, PLoc.init]
  prop_kind := by simp [Impl.initCfg, parSketch, PLoc.init, IsPLoc]

variable {b : ℕ} {hint₀ : S.Hint}

lemma Inv.curOp_not_mem {α : List (Lbl S N Q)} {C : PCfg S N Q} {g : Ghost S N Q}
    (hC : (parSketch S N Q b hint₀).run α = some C) (hI : Inv b α C g) {p : Proc N Q}
    (hp : C.pend p = none) : curOp α p ∉ g.lin.map Prod.fst := by
  intro hm
  obtain ⟨y, hy, hy1⟩ := List.mem_map.1 hm
  have := Invoked.of_opOf_eq_some (hI.lin_op y hy)
  rw [hy1] at this
  exact (parSketch S N Q b hint₀).not_invoked_curOp_of_idle hC hp this

lemma Inv.not_mem_lin {α : List (Lbl S N Q)} {C : PCfg S N Q} {g : Ghost S N Q}
    (hC : (parSketch S N Q b hint₀).run α = some C) (hI : Inv b α C g) {p : Proc N Q}
    (hp : C.pend p = none) (o : SkOp S.toSketch) (r : SkResp S.toSketch) :
    (curOp α p, o, r) ∉ g.lin := fun h =>
  hI.curOp_not_mem hC hp (List.mem_map_of_mem (f := Prod.fst) h)

lemma opOf_tau (α : List (Lbl S N Q)) (p : Proc N Q) (x : OpId (Proc N Q)) :
    opOf (α ++ [.tau p]) x = opOf α x := opOf_concat_of_ne (by intro _ h; cases h)

lemma respOf_tau (α : List (Lbl S N Q)) (p : Proc N Q) (x : OpId (Proc N Q)) :
    respOf (α ++ [.tau p]) x = respOf α x := respOf_append_of_not_ret (by intro _ _ h; cases h) x

lemma completed_tau (α : List (Lbl S N Q)) (p : Proc N Q) (x : OpId (Proc N Q)) :
    Completed (α ++ [.tau p]) x ↔ Completed α x :=
  completed_concat_of_not_ret (by intro _ _ h; cases h)

/-- **Frame lemma for internal steps that do not change the ghost state.** -/
lemma Inv.tau_frame {α : List (Lbl S N Q)} {C C' : PCfg S N Q} {g : Ghost S N Q}
    (hI : Inv b α C g) (p : Proc N Q) (hpend : C'.pend = C.pend)
    (hglob : C'.mem .glob = C.mem .glob)
    (hthr : ∀ j, TI b (C'.loc (.upd j)) (C'.pend (.upd j)) (C'.mem (.loc j)) (C'.mem (.prop j))
      (phaseOf j (C'.loc .prop)) (g.buf j) (upds g.vis) (curOp α (.upd j)) g.lin)
    (hq : ∀ q, C'.loc (.qry q) = C.loc (.qry q))
    (hlive : C'.pend .prop ≠ none → C'.loc .prop ≠ .pIdle) (hkind : IsPLoc (C'.loc .prop)) :
    Inv b (α ++ [.tau p]) C' g where
  glob := hglob.trans hI.glob
  vis_legal := hI.vis_legal
  lin_nodup := hI.lin_nodup
  vis_nodup := hI.vis_nodup
  lin_op y hy := (opOf_tau α p y.1).trans (hI.lin_op y hy)
  lin_resp y hy r hr := hI.lin_resp y hy r ((respOf_tau α p y.1).symm.trans hr)
  lin_comp x hx := hI.lin_comp x ((completed_tau α p x).1 hx)
  vis_lin := hI.vis_lin
  lin_cover := hI.lin_cover
  buf_lin := hI.buf_lin
  buf_vis := hI.buf_vis
  buf_shape := hI.buf_shape
  buf_nodup := hI.buf_nodup
  thr j := by simpa using hthr j
  qry q := by simpa [hq q, hpend] using hI.qry q
  lin_shape := hI.lin_shape
  prop_live := hlive
  prop_kind := hkind

/-- Internal steps of update thread `j` preserve the invariant. -/
lemma inv_step_tau_upd (hb : 0 < b) {α : List (Lbl S N Q)} {C C' : PCfg S N Q}
    {g : Ghost S N Q} {j : Fin N} (hI : Inv b α C g)
    (hs : (parSketch S N Q b hint₀).step C (.tau (.upd j)) = some C') :
    Inv b (α ++ [.tau (.upd j)]) C' (gstep α C g (.tau (.upd j))) := by
  have hg : gstep α C g (.tau (.upd j)) = g := rfl
  rw [hg]
  have hpne := (Impl.step_tau hs).1
  have hT := hI.thr j
  -- frame facts for other threads
  have other : ∀ j', j' ≠ j → C'.loc (.upd j') = C.loc (.upd j') →
      C'.pend (.upd j') = C.pend (.upd j') → C'.mem (.loc j') = C.mem (.loc j') →
      C'.mem (.prop j') = C.mem (.prop j') → C'.loc .prop = C.loc .prop →
      TI b (C'.loc (.upd j')) (C'.pend (.upd j')) (C'.mem (.loc j')) (C'.mem (.prop j'))
        (phaseOf j' (C'.loc .prop)) (g.buf j') (upds g.vis) (curOp α (.upd j')) g.lin := by
    intro j' _ h1 h2 h3 h4 h5
    exact (hI.thr j').congr h1 h2 h3 h4 (by rw [h5]) rfl rfl
  generalize hl : C.loc (.upd j) = l at hT
  cases l with
  | uIdle c h => exact absurd hT.1 hpne
  | uRet c h =>
    have : (parSketch S N Q b hint₀).step C (.tau (.upd j)) = none :=
      Impl.step_tau_ret_none (r := .ack) (l := .uIdle c h) (by simp [parSketch, PLoc.act, hl])
    rw [hs] at this; cases this
  | uApply a c h =>
    obtain ⟨hpd, hc, ⟨B', hB, hB'len, hls⟩, hpr, hsafe, hph⟩ := hT
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .loc j) (o := LOp.update a)
      (k := fun _ => if c + 1 = b then .uSignal h else .uRet (c + 1) h)
      (by simp [parSketch, PLoc.act, hl])
    refine hI.tau_frame _ hpend' (by rw [hmem']; simp) (fun j' => ?_) (fun q => by
      rw [hloc']; simp) (by rw [hpend', hloc']; simpa using hI.prop_live)
      (by rw [hloc']; simpa using hI.prop_kind)
    by_cases hj : j' = j
    · subst hj
      have hls' : C'.mem (.loc j') = S.run (upds (g.buf j')) := by
        rw [hmem']; simp [hls, hB, Sketch.run_concat]
      rw [hloc', Function.update_self, hpend', hpd]
      have hph' : phaseOf j' (Function.update C.loc (.upd j')
          (if c + 1 = b then .uSignal h else .uRet (c + 1) h) .prop) = .free := by
        rw [Function.update_of_ne (by simp)]; exact hph
      have hpr' : C'.mem (.prop j') = C.mem (.prop j') := by rw [hmem']; simp
      have hx : curOp α (.upd j') ∈ g.lin.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst)
          (hI.buf_lin j' (curOp α (.upd j'), .update a, .ack) (by rw [hB]; simp))
      split_ifs at hph' ⊢ with hcb
      · exact ⟨⟨a, rfl⟩, by rw [hB]; simp [hB'len, hcb], hls', by rw [hpr']; exact hpr,
          hsafe, hph', hx⟩
      · exact ⟨⟨a, rfl⟩, by omega, by rw [hB]; simp [hB'len], hls', by rw [hpr']; exact hpr,
          hsafe, hph', hx⟩
    · exact other j' hj (by rw [hloc', Function.update_of_ne (by simpa using hj)])
        (by rw [hpend']) (by rw [hmem', Function.update_of_ne (by simp [hj])])
        (by rw [hmem']; simp) (by rw [hloc', Function.update_of_ne (by simp)])
  | uSignal h =>
    obtain ⟨hpd, hlen, hls, hpr, hsafe, hph, hx⟩ := hT
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .prop j)
      (o := ROp.write none) (k := fun _ => .uWait h) (by simp [parSketch, PLoc.act, hl])
    refine hI.tau_frame _ hpend' (by rw [hmem']; simp) (fun j' => ?_) (fun q => by
      rw [hloc']; simp) (by rw [hpend', hloc']; simpa using hI.prop_live)
      (by rw [hloc']; simpa using hI.prop_kind)
    by_cases hj : j' = j
    · subst hj
      rw [hloc', Function.update_self, hpend']
      have hph' : phaseOf j' (C'.loc .prop) = .free := by
        rw [hloc', Function.update_of_ne (by simp)]; exact hph
      refine ⟨hpd, hsafe, hx, ?_⟩
      rw [hmem', Function.update_self]
      simp only [regObj]
      have : phaseOf j' (Function.update C.loc (.upd j') (.uWait h) .prop) = .free := by
        rw [Function.update_of_ne (by simp)]; exact hph
      rw [this]
      refine ⟨hlen, ?_⟩
      rw [Function.update_of_ne (by simp)]; exact hls
    · exact other j' hj (by rw [hloc', Function.update_of_ne (by simpa using hj)])
        (by rw [hpend']) (by rw [hmem']; simp)
        (by rw [hmem', Function.update_of_ne (by simp [hj])])
        (by rw [hloc', Function.update_of_ne (by simp)])
  | uWait h =>
    obtain ⟨hpd, hsafe, hx, hw⟩ := hT
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .prop j)
      (o := ROp.read) (k := fun r => Option.elim r (.uWait h) (.uRet 0))
      (by simp only [parSketch, hl, PLoc.act]; congr; funext r; cases r <;> rfl)
    have hmem'' : C'.mem = C.mem := by rw [hmem']; simp
    refine hI.tau_frame _ hpend' (by rw [hmem'']) (fun j' => ?_) (fun q => by
      rw [hloc']; simp) (by rw [hpend', hloc']; simpa using hI.prop_live)
      (by rw [hloc']; simpa using hI.prop_kind)
    by_cases hj : j' = j
    · subst hj
      rw [hloc', Function.update_self, hpend', hmem'']
      simp only [regObj]
      generalize hpr : C.mem (.prop j') = pr at hw
      cases pr with
      | none =>
        rw [Function.update_of_ne (by simp)]
        exact ⟨hpd, hsafe, hx, hw⟩
      | some h' =>
        obtain ⟨hs', hB, hls, hph⟩ := hw
        obtain ⟨a, ha⟩ := hpd
        refine ⟨⟨a, ha⟩, hb, by simp [hB], by simp [hls, hB], by simp, hs', ?_, hx⟩
        rw [Function.update_of_ne (by simp)]; exact hph
    · exact other j' hj (by rw [hloc', Function.update_of_ne (by simpa using hj)])
        (by rw [hpend']) (by rw [hmem'']) (by rw [hmem''])
        (by rw [hloc', Function.update_of_ne (by simp)])
  | _ => exact hT.elim

lemma phaseOf_pCheck (j j' : Fin N) : phaseOf (S := S) j' (.pCheck j) = .free := rfl

/-- Internal steps of the propagator preserve the invariant. -/
lemma inv_step_tau_prop {α : List (Lbl S N Q)} {C C' : PCfg S N Q}
    {g : Ghost S N Q} (hI : Inv b α C g)
    (hs : (parSketch S N Q b hint₀).step C (.tau .prop) = some C') :
    Inv b (α ++ [.tau .prop]) C' (gstep α C g (.tau .prop)) := by
  have hpne := (Impl.step_tau hs).1
  -- frame for threads other than the one the propagator works on
  have other : ∀ j' (newL : PLoc S N), C'.loc = Function.update C.loc .prop newL →
      C'.pend = C.pend → C'.mem (.loc j') = C.mem (.loc j') →
      C'.mem (.prop j') = C.mem (.prop j') →
      phaseOf j' newL = phaseOf j' (C.loc .prop) →
      TI b (C'.loc (.upd j')) (C'.pend (.upd j')) (C'.mem (.loc j')) (C'.mem (.prop j'))
        (phaseOf j' (C'.loc .prop)) (g.buf j') (upds g.vis) (curOp α (.upd j')) g.lin := by
    intro j' newL hloc' hpend' h3 h4 h5
    refine (hI.thr j').congr (by rw [hloc']; simp) (by rw [hpend']) h3 h4 ?_ rfl rfl
    rw [hloc', Function.update_self, h5]
  generalize hl : C.loc .prop = l at other
  cases l with
  | pIdle => exact absurd hl (hI.prop_live hpne)
  | pCheck j =>
    have hg : gstep α C g (.tau .prop) = g := by simp [gstep, hl]
    rw [hg]
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .prop j) (o := ROp.read)
      (k := fun r => Option.elim r (.pRead j) (fun _ => .pCheck (j + 1)))
      (by simp only [parSketch, hl, PLoc.act]; congr; funext r; cases r <;> rfl)
    have hmem'' : C'.mem = C.mem := by rw [hmem']; simp
    refine hI.tau_frame _ hpend' (by rw [hmem'']) (fun j' => ?_) (fun q => by
      rw [hloc']; simp) (by rw [hloc']; simp; cases C.mem (.prop j) <;> simp)
      (by rw [hloc']; simp; cases C.mem (.prop j) <;> simp [IsPLoc])
    by_cases hj : j' = j
    · subst hj
      have hT := hI.thr j'
      rw [hl] at hT
      simp only [regObj] at hloc'
      generalize hpr : C.mem (.prop j') = pr at hloc'
      cases pr with
      | none =>
        rw [hpr] at hT
        have := hT.toRead
        refine this.congr (by rw [hloc']; simp) (by rw [hpend']) (by rw [hmem''])
          (by rw [hmem'', hpr]) (by rw [hloc']; simp [phaseOf]) rfl rfl
      | some hh =>
        exact other j' _ (by rw [hloc']) hpend' (by rw [hmem'']) (by rw [hmem''])
          (by simp [phaseOf])
    · exact other j' _ hloc' hpend' (by rw [hmem'']) (by rw [hmem''])
        (by cases C.mem (.prop j) <;> simp [phaseOf, Ne.symm hj])
  | pRead j =>
    have hg : gstep α C g (.tau .prop) = g := by simp [gstep, hl]
    rw [hg]
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .loc j) (o := LOp.read)
      (k := fun r => match r with
        | .state s => .pMerge j s
        | .unit => .pCheck j)
      (by simp only [parSketch, hl, PLoc.act]; congr)
    have hmem'' : C'.mem = C.mem := by rw [hmem']; simp
    refine hI.tau_frame _ hpend' (by rw [hmem'']) (fun j' => ?_) (fun q => by
      rw [hloc']; simp) (by rw [hloc']; simp) (by rw [hloc']; simp [IsPLoc])
    by_cases hj : j' = j
    · subst hj
      have hT := hI.thr j'
      rw [hl] at hT
      simp only [phaseOf, ite_true] at hT
      obtain ⟨hh, -, hpr⟩ := hT.wait_of_busy (by simp)
      rw [hpr] at hT
      refine hT.toMerge.congr (by rw [hloc']; simp) (by rw [hpend']) (by rw [hmem''])
        (by rw [hmem'', hpr]) (by rw [hloc']; simp [phaseOf]) rfl rfl
    · exact other j' _ hloc' hpend' (by rw [hmem'']) (by rw [hmem''])
        (by simp [phaseOf, Ne.symm hj])
  | pMerge j s =>
    have hg : gstep α C g (.tau .prop) =
        { g with vis := g.vis ++ g.buf j, buf := Function.update g.buf j [] } := by
      simp [gstep, hl]
    rw [hg]
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .glob) (o := GOp.merge s)
      (k := fun _ => .pReset j) (by simp only [parSketch, hl, PLoc.act])
    have hT := hI.thr j
    rw [hl] at hT
    simp only [phaseOf, ite_true] at hT
    obtain ⟨hh, -, hpr⟩ := hT.wait_of_busy (by simp)
    rw [hpr] at hT
    have hs_eq : s = S.run (upds (g.buf j)) := by
      obtain ⟨hh', hl'⟩ := hT.wait_of_none; rw [hl'] at hT; exact hT.2.2.2.2
    have hFpre : upds g.vis <+: upds (g.vis ++ g.buf j) := by simp
    have hcur : ∀ q, curOp (α ++ [.tau .prop]) q = curOp α q := fun q => curOp_append_tau α _ q
    have hother_buf : ∀ j', j' ≠ j → ∀ y ∈ g.buf j', y ∉ g.buf j := by
      intro j' hj' y hy hy'
      have := (hI.buf_shape j' y hy).1.symm.trans (hI.buf_shape j y hy').1
      exact hj' (by simpa using this)
    exact {
      glob := by
        rw [hmem']; simp only [Function.update_self, globObj]
        rw [hI.glob, hs_eq, Composable.merge_run', upds_append]
      vis_legal := seqSketch_append hI.vis_legal _ fun e he => by
        obtain ⟨-, a, ha⟩ := hI.buf_shape j e he
        rw [ha]; exact ⟨rfl, fun q h => by cases h⟩
      lin_nodup := hI.lin_nodup
      vis_nodup := List.nodup_append.2 ⟨hI.vis_nodup, hI.buf_nodup j,
        fun y hy y' hy' h => hI.buf_vis j y' hy' (h ▸ hy)⟩
      lin_op := fun y hy => (opOf_tau α _ y.1).trans (hI.lin_op y hy)
      lin_resp := fun y hy r hr => hI.lin_resp y hy r ((respOf_tau α _ y.1).symm.trans hr)
      lin_comp := fun x hx => hI.lin_comp x ((completed_tau α _ x).1 hx)
      vis_lin := by
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact hI.vis_lin y hy
        · exact hI.buf_lin j y hy
      lin_cover := by
        intro y hy
        rcases hI.lin_cover y hy with h | ⟨j', hj'⟩
        · exact Or.inl (List.mem_append_left _ h)
        · by_cases hjj : j' = j
          · subst hjj; exact Or.inl (List.mem_append_right _ hj')
          · exact Or.inr ⟨j', by simpa [Function.update_of_ne hjj] using hj'⟩
      buf_lin := by
        intro j' y hy
        by_cases hjj : j' = j
        · subst hjj; simp at hy
        · exact hI.buf_lin j' y (by simpa [Function.update_of_ne hjj] using hy)
      buf_vis := by
        intro j' y hy
        by_cases hjj : j' = j
        · subst hjj; simp at hy
        · have hy : y ∈ g.buf j' := by simpa [Function.update_of_ne hjj] using hy
          show y ∉ g.vis ++ g.buf j
          simp only [List.mem_append, not_or]
          exact ⟨hI.buf_vis j' y hy, hother_buf j' hjj y hy⟩
      buf_shape := by
        intro j' y hy
        by_cases hjj : j' = j
        · subst hjj; simp at hy
        · exact hI.buf_shape j' y (by simpa [Function.update_of_ne hjj] using hy)
      buf_nodup := by
        intro j'
        by_cases hjj : j' = j
        · subst hjj; simp
        · simpa [Function.update_of_ne hjj] using hI.buf_nodup j'
      thr := by
        intro j'
        simp only [hcur]
        by_cases hjj : j' = j
        · subst hjj
          refine (hT.toReset hFpre).congr (by rw [hloc']; simp) (by rw [hpend'])
            (by rw [hmem']; simp) (by rw [hmem', Function.update_of_ne (by simp)]; exact hpr)
            (by rw [hloc']; simp [phaseOf]) (by simp) rfl
        · refine (TI.mono (hI.thr j') hFpre (fun y hy => hy)).congr (by rw [hloc']; simp)
            (by rw [hpend']) (by rw [hmem']; simp) (by rw [hmem']; simp)
            (by rw [hloc', hl]; simp [phaseOf, Ne.symm hjj]) (by simp [Function.update_of_ne hjj])
            rfl
      qry := fun q => by
        simpa [hloc', hpend', hcur] using hI.qry q
      lin_shape := hI.lin_shape
      prop_live := by rw [hloc']; simp
      prop_kind := by rw [hloc']; simp [IsPLoc] }
  | pReset j =>
    have hg : gstep α C g (.tau .prop) = g := by simp [gstep, hl]
    rw [hg]
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .loc j) (o := LOp.reset)
      (k := fun _ => .pHint j) (by simp only [parSketch, hl, PLoc.act])
    refine hI.tau_frame _ hpend' (by rw [hmem']; simp) (fun j' => ?_) (fun q => by
      rw [hloc']; simp) (by rw [hloc']; simp) (by rw [hloc']; simp [IsPLoc])
    by_cases hj : j' = j
    · subst hj
      have hT := hI.thr j'
      rw [hl] at hT
      simp only [phaseOf, ite_true] at hT
      obtain ⟨hh, -, hpr⟩ := hT.wait_of_busy (by simp)
      rw [hpr] at hT
      refine hT.toHint.congr (by rw [hloc']; simp) (by rw [hpend']) (by rw [hmem']; simp)
        (by rw [hmem', Function.update_of_ne (by simp)]; exact hpr)
        (by rw [hloc']; simp [phaseOf]) rfl rfl
    · exact other j' _ hloc' hpend' (by rw [hmem', Function.update_of_ne (by simp [hj])])
        (by rw [hmem']; simp) (by simp [phaseOf, Ne.symm hj])
  | pHint j =>
    have hg : gstep α C g (.tau .prop) = g := by simp [gstep, hl]
    rw [hg]
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .glob) (o := GOp.calcHint)
      (k := fun r => match r with
        | .hint h => .pSignal j h
        | _ => .pCheck j)
      (by simp only [parSketch, hl, PLoc.act]; congr)
    have hmem'' : C'.mem = C.mem := by rw [hmem']; simp
    refine hI.tau_frame _ hpend' (by rw [hmem'']) (fun j' => ?_) (fun q => by
      rw [hloc']; simp) (by rw [hloc']; simp) (by rw [hloc']; simp [IsPLoc])
    by_cases hj : j' = j
    · subst hj
      have hT := hI.thr j'
      rw [hl] at hT
      simp only [phaseOf, ite_true] at hT
      obtain ⟨hh, -, hpr⟩ := hT.wait_of_busy (by simp)
      rw [hpr] at hT
      have hsafe : S.Safe (S.calcHint (C.mem .glob)) (upds g.vis) := by
        rw [hI.glob]; exact Composable.safe_calcHint _
      refine (hT.toSignal hsafe).congr (by rw [hloc']; simp) (by rw [hpend']) (by rw [hmem''])
        (by rw [hmem'', hpr]) (by rw [hloc']; simp [phaseOf]) rfl rfl
    · exact other j' _ hloc' hpend' (by rw [hmem'']) (by rw [hmem''])
        (by simp [phaseOf, Ne.symm hj])
  | pSignal j h =>
    have hg : gstep α C g (.tau .prop) = g := by simp [gstep, hl]
    rw [hg]
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .prop j)
      (o := ROp.write (some h)) (k := fun _ => .pCheck (j + 1))
      (by simp only [parSketch, hl, PLoc.act])
    refine hI.tau_frame _ hpend' (by rw [hmem']; simp) (fun j' => ?_) (fun q => by
      rw [hloc']; simp) (by rw [hloc']; simp) (by rw [hloc']; simp [IsPLoc])
    by_cases hj : j' = j
    · subst hj
      have hT := hI.thr j'
      rw [hl] at hT
      simp only [phaseOf, ite_true] at hT
      obtain ⟨hh, -, hpr⟩ := hT.wait_of_busy (by simp)
      rw [hpr] at hT
      refine hT.toSome.congr (by rw [hloc']; simp) (by rw [hpend']) (by rw [hmem']; simp)
        (by rw [hmem']; simp) (by rw [hloc']; simp [phaseOf]) rfl rfl
    · exact other j' _ hloc' hpend' (by rw [hmem']; simp)
        (by rw [hmem', Function.update_of_ne (by simp [hj])]) (by simp [phaseOf, Ne.symm hj])
  | _ =>
    rw [Impl.step_tau_ret_none (I := parSketch S N Q b hint₀) (r := SkResp.ack)
      (l := C.loc .prop) (by simp [parSketch, PLoc.act, hl])] at hs
    cases hs

/-- Two entries of a list with distinct ids and the same id are equal. -/
lemma eq_of_mem_of_fst_eq {lin : List (Entry (Proc N Q) S.toSketch)}
    (hnd : (lin.map Prod.fst).Nodup) {y z : Entry (Proc N Q) S.toSketch} (hy : y ∈ lin)
    (hz : z ∈ lin) (h : y.1 = z.1) : y = z :=
  List.inj_on_of_nodup_map hnd hy hz h

/-- Snapshot steps of query threads preserve the invariant. -/
lemma inv_step_tau_qry {α : List (Lbl S N Q)} {C C' : PCfg S N Q}
    {g : Ghost S N Q} {q : Q} (hC : (parSketch S N Q b hint₀).run α = some C) (hI : Inv b α C g)
    (hs : (parSketch S N Q b hint₀).step C (.tau (.qry q)) = some C') :
    Inv b (α ++ [.tau (.qry q)]) C' (gstep α C g (.tau (.qry q))) := by
  have hpne := (Impl.step_tau hs).1
  have hQ := hI.qry q
  generalize hl : C.loc (.qry q) = l at hQ
  cases l with
  | qIdle => exact absurd hQ hpne
  | qRet v =>
    rw [Impl.step_tau_ret_none (I := parSketch S N Q b hint₀) (r := .val v) (l := .qIdle)
      (by simp [parSketch, PLoc.act, hl])] at hs
    cases hs
  | qSnap a =>
    obtain ⟨hpd, hnotin⟩ := hQ
    set e : Entry (Proc N Q) S.toSketch :=
      (curOp α (.qry q), .query a, .val (S.snapQuery (S.snapshot (C.mem .glob)) a)) with he
    have hg : gstep α C g (.tau (.qry q)) =
        { g with lin := g.lin ++ [e], vis := g.vis ++ [e] } := by
      simp [gstep, hl, he]
    rw [hg]
    obtain ⟨hpend', hmem', hloc'⟩ := Impl.step_tau_access hs (i := .glob) (o := GOp.snapshot)
      (k := fun r => match r with
        | .snap x => .qRet (S.snapQuery x a)
        | _ => .qIdle) (by simp only [parSketch, hl, PLoc.act]; congr)
    have hmem'' : C'.mem = C.mem := by rw [hmem']; simp
    have heL : e ∉ g.lin := fun h => hnotin (List.mem_map_of_mem (f := Prod.fst) h)
    have hcur : ∀ p, curOp (α ++ [.tau (.qry q)]) p = curOp α p := fun p => curOp_append_tau α _ p
    have hlin : ∀ y ∈ g.lin, y ∈ g.lin ++ [e] := fun y hy => List.mem_append_left _ hy
    have hopcur := ((parSketch S N Q b hint₀).run_pend_curOp hC hpd)
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
        refine (TI.mono (hI.thr j) (by simp [he]) hlin).congr (by rw [hloc']; simp)
          (by rw [hpend']) (by rw [hmem'']) (by rw [hmem'']) (by rw [hloc']; simp) rfl rfl
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
lemma inv_step_ret {α : List (Lbl S N Q)} {C C' : PCfg S N Q} {g : Ghost S N Q} {p : Proc N Q}
    {r : SkResp S.toSketch} (hI : Inv b α C g)
    (hs : (parSketch S N Q b hint₀).step C (.ret p r) = some C') :
    Inv b (α ++ [.ret p r]) C' (gstep α C g (.ret p r)) := by
  have hg : gstep α C g (.ret p r) = g := rfl
  rw [hg]
  obtain ⟨hpne, hpend', hmem', l', hact, hloc'⟩ := Impl.step_ret hs
  have hcur_ne : ∀ p', p' ≠ p → curOp (α ++ [.ret p r]) p' = curOp α p' :=
    fun p' h => curOp_append_ret_of_ne α r (Ne.symm h)
  -- the completed instance is in the linearization with response `r`
  have key : ∀ x, x ∈ g.lin.map Prod.fst → x.1 = p →
      (x ≠ curOp α p → respOf (α ++ [.ret p r]) x = respOf α x) := by
    intro x _ hx hne
    refine respOf_concat_ret_of_ne hne fun _ => ?_
    have : x.2 ≠ (respsOf α p).length := fun h => hne (by
      obtain ⟨x1, x2⟩ := x; simp only at hx h; subst hx; simp [curOp, h])
    omega
  have common : ∀ (hin : curOp α p ∈ g.lin.map Prod.fst)
      (hresp : ∀ y ∈ g.lin, y.1 = curOp α p → y.2.2 = r)
      (hthr : ∀ j, TI b (C'.loc (.upd j)) (C'.pend (.upd j)) (C'.mem (.loc j)) (C'.mem (.prop j))
        (phaseOf j (C'.loc .prop)) (g.buf j) (upds g.vis) (curOp (α ++ [.ret p r]) (.upd j)) g.lin)
      (hqry : ∀ q, QI (C'.loc (.qry q)) (C'.pend (.qry q)) (curOp (α ++ [.ret p r]) (.qry q))
        g.lin)
      (hlive : C'.pend .prop ≠ none → C'.loc .prop ≠ .pIdle) (hkind : IsPLoc (C'.loc .prop)),
      Inv b (α ++ [.ret p r]) C' g := by
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
    | uRet c h =>
      have hact' : (parSketch S N Q b hint₀).act (.upd j) (C.loc (.upd j)) =
          .ret .ack (.uIdle c h) := by simp [parSketch, PLoc.act, hl]
      obtain ⟨rfl, -, -, hloc''⟩ := Impl.step_ret_ret hs hact'
      obtain ⟨-, hc, hlen, hls, hpr, hsafe, hph, hx⟩ := hT
      refine common hx (fun y hy hy1 => ?_) (fun j' => ?_) (fun q => ?_) ?_ ?_
      · rcases hI.lin_shape y hy with ⟨j'', h1, a, h2⟩ | ⟨q, h1, a, v, h2⟩
        · rw [h2]
        · rw [hy1] at h1; cases h1
      · by_cases hj : j' = j
        · subst hj
          rw [hloc'', Function.update_self, hpend', Function.update_self, hmem']
          exact ⟨rfl, hc, hlen, hls, hpr, hsafe, by rw [Function.update_of_ne (by simp)]; exact hph⟩
        · rw [hcur_ne _ (by simpa using hj)]
          refine (hI.thr j').congr (by rw [hloc'', Function.update_of_ne (by simpa using hj)])
            (by rw [hpend', Function.update_of_ne (by simpa using hj)]) (by rw [hmem'])
            (by rw [hmem']) (by rw [hloc'', Function.update_of_ne (by simp)]) rfl rfl
      · rw [hcur_ne _ (by simp), hloc'', hpend', Function.update_of_ne (by simp),
          Function.update_of_ne (by simp)]
        exact hI.qry q
      · rw [hloc'', hpend', Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
        exact hI.prop_live
      · rw [hloc'', Function.update_of_ne (by simp)]; exact hI.prop_kind
    | uIdle c h => exact absurd hT.1 hpne
    | uApply a c h =>
      rw [Impl.step_ret_none_of_not_ret (I := parSketch S N Q b hint₀)
        (by simp [parSketch, PLoc.act, hl])] at hs; cases hs
    | uSignal h =>
      rw [Impl.step_ret_none_of_not_ret (I := parSketch S N Q b hint₀)
        (by simp [parSketch, PLoc.act, hl])] at hs; cases hs
    | uWait h =>
      rw [Impl.step_ret_none_of_not_ret (I := parSketch S N Q b hint₀)
        (by simp [parSketch, PLoc.act, hl])] at hs; cases hs
    | _ => exact hT.elim
  | prop =>
    have hl := hI.prop_live hpne
    have hk := hI.prop_kind
    generalize hl' : C.loc .prop = l at hl hk
    cases l with
    | pIdle => exact absurd rfl hl
    | pCheck _ | pRead _ | pMerge _ _ | pReset _ | pHint _ | pSignal _ _ =>
      rw [Impl.step_ret_none_of_not_ret (I := parSketch S N Q b hint₀)
        (by simp [parSketch, PLoc.act, hl'])] at hs; cases hs
    | _ => exact hk.elim
  | qry q =>
    have hQ := hI.qry q
    generalize hl : C.loc (.qry q) = l at hQ
    cases l with
    | qRet v =>
      have hact' : (parSketch S N Q b hint₀).act (.qry q) (C.loc (.qry q)) =
          .ret (.val v) .qIdle := by simp [parSketch, PLoc.act, hl]
      obtain ⟨rfl, -, -, hloc''⟩ := Impl.step_ret_ret hs hact'
      obtain ⟨a, -, hmem⟩ := hQ
      refine common (List.mem_map_of_mem (f := Prod.fst) hmem)
        (fun y hy hy1 => by rw [eq_of_mem_of_fst_eq hI.lin_nodup hy hmem hy1]) (fun j => ?_)
        (fun q' => ?_) ?_ ?_
      · rw [hcur_ne _ (by simp)]
        refine (hI.thr j).congr (by rw [hloc'', Function.update_of_ne (by simp)])
          (by rw [hpend', Function.update_of_ne (by simp)]) (by rw [hmem'])
          (by rw [hmem']) (by rw [hloc'', Function.update_of_ne (by simp)]) rfl rfl
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
      rw [Impl.step_ret_none_of_not_ret (I := parSketch S N Q b hint₀)
        (by simp [parSketch, PLoc.act, hl])] at hs; cases hs
    | _ => exact hQ.elim

/-- Frame lemma for invocations that do not change the ghost state. -/
lemma Inv.inv_frame {α : List (Lbl S N Q)} {C C' : PCfg S N Q} {g : Ghost S N Q}
    (hI : Inv b α C g) (p : Proc N Q) (o : SkOp S.toSketch) (hmem : C'.mem = C.mem)
    (hthr : ∀ j, TI b (C'.loc (.upd j)) (C'.pend (.upd j)) (C'.mem (.loc j)) (C'.mem (.prop j))
      (phaseOf j (C'.loc .prop)) (g.buf j) (upds g.vis) (curOp α (.upd j)) g.lin)
    (hq : ∀ q, QI (C'.loc (.qry q)) (C'.pend (.qry q)) (curOp α (.qry q)) g.lin)
    (hlive : C'.pend .prop ≠ none → C'.loc .prop ≠ .pIdle) (hkind : IsPLoc (C'.loc .prop)) :
    Inv b (α ++ [.inv p o]) C' g where
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
lemma inv_step_inv {α : List (Lbl S N Q)} {C C' : PCfg S N Q} {g : Ghost S N Q} {p : Proc N Q}
    {o : SkOp S.toSketch} (hC : (parSketch S N Q b hint₀).run α = some C) (hI : Inv b α C g)
    (hs : (parSketch S N Q b hint₀).step C (.inv p o) = some C') :
    Inv b (α ++ [.inv p o]) C' (gstep α C g (.inv p o)) := by
  obtain ⟨hpend, hall, hpend', hloc', hmem'⟩ := Impl.step_inv hs
  have hidle := (parSketch S N Q b hint₀).run_idle_counts hC hpend
  have hnotid := hI.curOp_not_mem hC hpend
  have hresp : ∀ x, respOf (α ++ [.inv p o]) x = respOf α x :=
    respOf_append_of_not_ret (by intro _ _ h; cases h)
  have hcomp : ∀ x, Completed (α ++ [.inv p o]) x ↔ Completed α x :=
    fun x => completed_concat_of_not_ret (by intro _ _ h; cases h)
  have hcur : ∀ q, curOp (α ++ [.inv p o]) q = curOp α q := fun q => curOp_append_inv α p q o
  have hnewop : opOf (α ++ [.inv p o]) (curOp α p) = some o := opOf_concat_inv_curOp hidle
  have hnewresp : ∀ r, respOf α (curOp α p) ≠ some r := fun r h =>
    not_completed_curOp α p (Completed.of_respOf_eq_some h)
  -- frame facts
  have thr_other : ∀ j, Proc.upd j ≠ p →
      TI b (C'.loc (.upd j)) (C'.pend (.upd j)) (C'.mem (.loc j)) (C'.mem (.prop j))
        (phaseOf j (C'.loc .prop)) (g.buf j) (upds g.vis) (curOp α (.upd j)) g.lin := by
    intro j hj
    have hprop : C'.loc .prop = C.loc .prop ∨ p = .prop := by
      by_cases h : p = .prop
      · exact Or.inr h
      · left; rw [hloc', Function.update_of_ne (Ne.symm h)]
    refine (hI.thr j).congr (by rw [hloc', Function.update_of_ne hj])
      (by rw [hpend', Function.update_of_ne hj]) (by rw [hmem']) (by rw [hmem']) ?_ rfl rfl
    rcases hprop with h | rfl
    · rw [h]
    · rw [hloc', Function.update_self]
      generalize C.loc .prop = l
      cases o <;> cases l <;> rfl
  have qry_other : ∀ q, Proc.qry q ≠ p → ∀ lin', (∀ y ∈ g.lin, y ∈ lin') →
      (∀ y ∈ lin', y ∈ g.lin ∨ y.1 ≠ curOp α (.qry q)) →
      QI (C'.loc (.qry q)) (C'.pend (.qry q)) (curOp α (.qry q)) lin' := by
    intro q hq lin' h1 h2
    refine ((hI.qry q).mono h1 h2) |> fun h => ?_
    rwa [hloc', hpend', Function.update_of_ne hq, Function.update_of_ne hq]
  have live_other : p ≠ .prop → (C'.pend .prop ≠ none → C'.loc .prop ≠ .pIdle) ∧
      IsPLoc (C'.loc .prop) := by
    intro hp
    rw [hloc', hpend', Function.update_of_ne (Ne.symm hp), Function.update_of_ne (Ne.symm hp)]
    exact ⟨hI.prop_live, hI.prop_kind⟩
  cases p with
  | prop =>
    cases o with
    | update _ => exact hall.elim
    | query _ => exact hall.elim
    | propagate =>
    have hg : gstep α C g (.inv .prop .propagate) = g := rfl
    rw [hg]
    have hk := hI.prop_kind
    refine hI.inv_frame _ _ hmem' (fun j => thr_other j (by simp)) (fun q =>
      by simpa using qry_other q (by simp) g.lin (fun y hy => hy) (fun y hy => Or.inl hy))
      (by rw [hloc', Function.update_self]; generalize C.loc .prop = l at hk
          cases l <;> simp [parSketch, PLoc.invoke, IsPLoc] at hk ⊢) ?_
    rw [hloc', Function.update_self]; generalize C.loc .prop = l at hk
    cases l <;> simp [parSketch, PLoc.invoke, IsPLoc] at hk ⊢
  | qry q =>
    cases o with
    | update _ => exact hall.elim
    | propagate => exact hall.elim
    | query a =>
    have hg : gstep α C g (.inv (.qry q) (.query a)) = g := rfl
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
    obtain ⟨c, h, hl⟩ : ∃ c h, C.loc (.upd j) = .uIdle c h := by
      generalize C.loc (.upd j) = l at hT
      cases l <;> simp only [TI, hpend, reduceCtorEq, false_and, exists_false] at hT
      · exact ⟨_, _, rfl⟩
    rw [hl] at hT
    obtain ⟨-, hc, hlen, hls, hpr, hsafe, hph⟩ := hT
    set e : Entry (Proc N Q) S.toSketch := (curOp α (.upd j), .update a, .ack) with he
    have heL : e ∉ g.lin := fun h' => hnotid (List.mem_map_of_mem (f := Prod.fst) h')
    have hlin : ∀ y ∈ g.lin, y ∈ g.lin ++ [e] := fun y hy => List.mem_append_left _ hy
    obtain ⟨hl1, hl2⟩ := live_other (by simp)
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
    have lin_shape' : ∀ y ∈ g.lin ++ [e], (∃ j, y.1.1 = .upd j ∧ ∃ a, y.2 = (.update a, .ack)) ∨
        (∃ q, y.1.1 = .qry q ∧ ∃ a v, y.2 = (.query a, .val v)) := by
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hI.lin_shape y hy
      · simp only [List.mem_singleton] at hy; subst hy; exact Or.inl ⟨j, rfl, a, rfl⟩
    have qry' : ∀ q, QI (C'.loc (.qry q)) (C'.pend (.qry q))
        (curOp (α ++ [.inv (.upd j) (.update a)]) (.qry q)) (g.lin ++ [e]) := by
      intro q
      rw [hcur]
      refine qry_other q (by simp) _ hlin fun y hy => ?_
      rcases List.mem_append.1 hy with hy | hy
      · exact Or.inl hy
      · right; simp only [List.mem_singleton] at hy; subst hy; simp [he, curOp]
    by_cases hsa : S.shouldAdd h a = true
    · -- accepted: the update joins the unpropagated updates of thread `j`
      have hg : gstep α C g (.inv (.upd j) (.update a)) =
          { g with lin := g.lin ++ [e], buf := Function.update g.buf j (g.buf j ++ [e]) } := by
        simp [gstep, hl, hsa, he]
      rw [hg]
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
              by_cases hjj : j' = j
              · subst hjj; simp [hj']
              · simpa [Function.update_of_ne hjj] using hj'
          · right; refine ⟨j, ?_⟩; simp only [List.mem_singleton] at hy; simp [hy]
        buf_lin := by
          intro j' y hy
          by_cases hjj : j' = j
          · subst hjj
            simp only [Function.update_self, List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact hlin _ (hI.buf_lin _ y hy)
            · exact List.mem_append_right _ (List.mem_singleton_self _)
          · exact hlin _ (hI.buf_lin j' y (by simpa [Function.update_of_ne hjj] using hy))
        buf_vis := by
          intro j' y hy
          by_cases hjj : j' = j
          · subst hjj
            simp only [Function.update_self, List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact hI.buf_vis _ y hy
            · exact fun h' => heL (hI.vis_lin _ h')
          · exact hI.buf_vis j' y (by simpa [Function.update_of_ne hjj] using hy)
        buf_shape := by
          intro j' y hy
          by_cases hjj : j' = j
          · subst hjj
            simp only [Function.update_self, List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact hI.buf_shape _ y hy
            · exact ⟨rfl, a, rfl⟩
          · exact hI.buf_shape j' y (by simpa [Function.update_of_ne hjj] using hy)
        buf_nodup := by
          intro j'
          by_cases hjj : j' = j
          · subst hjj
            simp only [Function.update_self]
            exact (List.nodup_append.2 ⟨hI.buf_nodup _, by simp, by
              simp only [List.mem_singleton]
              rintro y hy _ rfl rfl; exact heL (hI.buf_lin _ _ hy)⟩)
          · simpa [Function.update_of_ne hjj] using hI.buf_nodup j'
        thr := by
          intro j'
          rw [hcur]
          by_cases hjj : j' = j
          · subst hjj
            simp only [Function.update_self]
            rw [hloc', hpend', Function.update_self, Function.update_self, hl]
            have hinv : (parSketch S N Q b hint₀).invoke (.upd j') (.uIdle c h) (.update a) =
                .uApply a c h := by simp [parSketch, PLoc.invoke, hsa]
            rw [hinv]
            refine ⟨rfl, hc, ⟨g.buf j', rfl, hlen, by rw [hmem']; exact hls⟩,
              by rw [hmem']; exact hpr, hsafe, ?_⟩
            rw [Function.update_of_ne (by simp)]; exact hph
          · simp only [Function.update_of_ne hjj]
            exact TI.mono (thr_other j' (by simpa using hjj)) (List.prefix_refl _) hlin
        qry := qry'
        lin_shape := lin_shape'
        prop_live := hl1
        prop_kind := hl2 }
    · -- filtered out: visible at once, the summary does not change
      have hsa' : S.shouldAdd h a = false := by simpa using hsa
      have hg : gstep α C g (.inv (.upd j) (.update a)) =
          { g with lin := g.lin ++ [e], vis := g.vis ++ [e] } := by
        simp [gstep, hl, hsa', he]
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
            rw [hloc', hpend', Function.update_self, Function.update_self, hl]
            have hinv : (parSketch S N Q b hint₀).invoke (.upd j') (.uIdle c h) (.update a) =
                .uRet c h := by simp [parSketch, PLoc.invoke, hsa']
            rw [hinv]
            refine ⟨⟨a, rfl⟩, hc, hlen, by rw [hmem']; exact hls, by rw [hmem']; exact hpr,
              hsafe.mono hFpre, ?_, by simp [he]⟩
            rw [Function.update_of_ne (by simp)]; exact hph
          · exact TI.mono (thr_other j' (by simpa using hjj)) hFpre hlin
        qry := qry'
        lin_shape := lin_shape'
        prop_live := hl1
        prop_kind := hl2 }

end Podc.ConcurrentSketches
