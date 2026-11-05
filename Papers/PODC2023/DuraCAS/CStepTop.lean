import Papers.PODC2023.DuraCAS.CStepMem

/-!
# Simulation of DuraCAS-level steps, call starts, invocations and crashes
-/

set_option linter.unusedSectionVars false

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

theorem PInv.orph_none_of_notRecv {m : Mem P K V} {ls p st ap} (h : PInv m ls p st ap)
    (hr : ∀ j, st.pc ≠ .recv j) : ap.orph = none := by
  cases hor : ap.orph with
  | none => rfl
  | some x =>
    obtain ⟨-, -, -, -, -, r, j, -, hpc, -⟩ := h.orph x hor
    exact absurd hpc (hr j)

theorem Inv.ownPre_of_noFrame {s : St P K V} {a : AS P K V} {p : P} (hI : Inv s a)
    (hfr : (s.ps p).fr = none) : OwnPre s.m s.ps a.ps p := by
  intro o g hx hp
  by_cases hgp : g.1 = p
  · right; refine ⟨hgp, ?_⟩
    rcases owner_cases (hI.own o g hx hp) hx (hI.p g.1) with ⟨f0, hf0, -⟩ | ⟨x, hx', hxo, -⟩
    · rw [hgp, hfr] at hf0; cases hf0
    · exact ⟨x, hgp ▸ hx', hxo⟩
  · exact Or.inl ⟨hgp, hI.own o g hx hp⟩

/-- A DuraCAS-level step (an `ECLL` = read of `Y`, or a local step) is one A-level step. -/
theorem sim_pure {s : St P K V} {a : AS P K V} {p : P} {r : OpRec K V} {n : Next V}
    (hI : Inv s a) (hfr : (s.ps p).fr = none) (hop : (s.ps p).op = some r)
    (hrecv : ∀ j, (s.ps p).pc ≠ .recv j) (hn : n ≠ .go .idle)
    (ha : apstep a p = a.next p n) :
    ∃ a', Relation.ReflTransGen AStep a a' ∧ Inv (applyNext s p s.m n) a' := by
  have hP := hI.p p
  have hapc : (a.ps p).pc = .at (s.ps p).pc := by rw [hP.pc]; simp [apcOf, hfr]
  refine ⟨_, Relation.ReflTransGen.single ⟨.step p, ⟨r, hP.op.trans hop, ?_⟩, ha.symm⟩, ?_⟩
  · intro j hj; rw [hapc] at hj; exact absurd (APc.at.inj hj) (hrecv j)
  · refine inv_applyNext hI.Y hI.hist hI.nid hI.g (fun q _ => hI.p q) (hI.ownPre_of_noFrame hfr)
      hP.op (by simp [hop]) ?_
    rw [hP.orph_none_of_notRecv hrecv]; exact nextOK_none hn

theorem scArgs_not_recv {p : P} {k : K} {op : Op V} {c : Pc V} {x : Orph P K V}
    (hx : scArgs p k op c = some x) : ∀ j, c ≠ .recv j := by
  rintro j rfl; simp [scArgs] at hx

theorem scArgs_h {p : P} {k : K} {op : Op V} {c : Pc V} {x : Orph P K V}
    (hx : scArgs p k op c = some x) : x.h.1 = p ∧ (x.o = (k, .W) ∨ x.o = (k, .Z)) := by
  cases c <;> simp [scArgs] at hx
  · rename_i i z; cases op <;> simp at hx; subst hx; simp
  · rename_i w; cases op <;> simp at hx; subst hx; simp
  · subst hx; simp

/-- Start of an `ECSC` call (line 6): a failing check is a failing A-level `ECSC` (Definition A.8.3),
otherwise the call becomes an active frame at line 7. -/
theorem sim_startSC {s : St P K V} {a : AS P K V} {p : P} {r : OpRec K V} {o : Obj K} {h : Hd P}
    {sq : ℕ} {v : V × Bool} (hI : Inv s a) (hfr : (s.ps p).fr = none) (hop : (s.ps p).op = some r)
    (hx : scArgs p r.k r.op (s.ps p).pc = some ⟨o, h, sq, v⟩) :
    ∃ a', Relation.ReflTransGen AStep a a' ∧ Inv (startSC s p o h sq v) a' := by
  have hP := hI.p p
  have hrecv := scArgs_not_recv hx
  have hor := hP.orph_none_of_notRecv hrecv
  have hapc : (a.ps p).pc = .at (s.ps p).pc := by rw [hP.pc]; simp [apcOf, hfr]
  unfold startSC
  split_ifs with hne
  · exact ret_frame (f := ⟨.sc, o, h, sq, v, 0, false, .l7⟩) (rr := false) hI.Y hI.hist hI.nid
      hI.g (fun q _ => hI.p q) (hI.ownPre_of_noFrame hfr) (hP.op.trans hop) hop (fun _ => hx)
      (fun h => by cases h) (by simp [hapc]) (fun _ _ => hne) (fun _ => hor)
      (fun h => by cases h)
  · refine ⟨a, .refl, hI.Y, hI.hist, hI.nid, hI.g, ?_, ?_⟩
    · apply forall_update_PInv' _ (fun q _ => hI.p q)
      refine ⟨hP.op, hP.idle, fun hi => ?_, ?_, ?_, ?_⟩
      · rw [(hP.idle.2 hi)] at hop; cases hop
      · rw [hapc]; simp [apcOf, Moved]
      · intro x hx'; rw [hor] at hx'; cases hx'
      · intro f hf; simp only [Option.some.injEq] at hf; subst hf
        refine ⟨(scArgs_h hx).1, ⟨r, hop, fun _ => hx, fun h => (by cases h)⟩,
          fun _ => ⟨by simp at hne; simp [hne], fun h => (by simp [FPc.IsFwd] at h)⟩,
          fun h => (by cases h), rfl⟩
    · intro o' g hx' hp
      have hgp : g.1 ≠ p := by
        intro hgp
        rcases owner_cases (hI.own o' g hx' hp) hx' (hI.p g.1) with ⟨f0, hf0, -⟩ | ⟨x, hx'', -⟩
        · rw [hgp, hfr] at hf0; cases hf0
        · rw [hgp, hor] at hx''; cases hx''
      rcases hI.own o' g hx' hp with ⟨f0, hf0, h'⟩ | h'
      · exact Or.inl ⟨f0, by simp [setFrame, Function.update_of_ne hgp, hf0], h'⟩
      · exact Or.inr h'

/-- Start of a `RECOVER` call (line 13 of the `FORWARD` of line 20 is executed with it). -/
theorem sim_recv {s : St P K V} {a : AS P K V} {p : P} {r : OpRec K V} {j : Fin 4}
    (hI : Inv s a) (hfr : (s.ps p).fr = none) (hop : (s.ps p).op = some r)
    (hpc : (s.ps p).pc = .recv j) :
    Inv (setFrame s p s.m ⟨.recov, (r.k, if j.val % 2 = 0 then .W else .Z),
      (p, if j.val < 2 then .crit else .cas), 0, (s.m.hval (p, .crit)), 0, false,
      .f14 (s.m.X (r.k, if j.val % 2 = 0 then .W else .Z))⟩) a := by
  have hP := hI.p p
  have hapc : (a.ps p).pc = .at (s.ps p).pc := by rw [hP.pc]; simp [apcOf, hfr]
  refine ⟨hI.Y, hI.hist, hI.nid, hI.g, ?_, ?_⟩
  · apply forall_update_PInv' _ (fun q _ => hI.p q)
    refine ⟨hP.op, hP.idle, fun hi => ?_, ?_, hP.orph, ?_⟩
    · rw [(hP.idle.2 hi)] at hop; cases hop
    · rw [hapc]; simp [apcOf, Moved]
    · intro f hf; simp only [Option.some.injEq] at hf; subst hf
      refine ⟨rfl, ⟨r, hop, fun h => (by cases h), fun _ => ⟨j, hpc, rfl⟩⟩,
        fun h => (by cases h), fun _ => trivial, fun _ => rfl, ?_⟩
      intro g hx; exact fresh_cur hI.g _ g hx
  · intro o' g hx' hp
    by_cases hgp : g.1 = p
    · rcases owner_cases (hI.own o' g hx' hp) hx' (hI.p g.1) with ⟨f0, hf0, -⟩ | ⟨x, hx'', hxo, -⟩
      · rw [hgp, hfr] at hf0; cases hf0
      · exact Or.inr ⟨x, hx'', hxo⟩
    · rcases hI.own o' g hx' hp with ⟨f0, hf0, h'⟩ | h'
      · exact Or.inl ⟨f0, by simp [setFrame, Function.update_of_ne hgp, hf0], h'⟩
      · exact Or.inr h'

/-- Simulation of a step of a process without an active DurEC call. -/
theorem sim_top {s : St P K V} {a : AS P K V} {p : P} {r : OpRec K V} (hI : Inv s a)
    (hfr : (s.ps p).fr = none) (hop : (s.ps p).op = some r) :
    ∃ a', Relation.ReflTransGen AStep a a' ∧ Inv (pstep s p) a' := by
  have hP := hI.p p
  have hapc : (a.ps p).pc = .at (s.ps p).pc := by rw [hP.pc]; simp [apcOf, hfr]
  have haop : (a.ps p).op = some r := hP.op.trans hop
  cases hpc : (s.ps p).pc with
  | idle =>
    have : pstep s p = s := by simp only [pstep, hfr, hop, hpc]
    rw [this]; exact ⟨a, .refl, hI⟩
  | read =>
    simp only [pstep, hfr, hop, hpc]
    exact sim_pure hI hfr hop (by simp [hpc]) (by simp) (by simp [apstep, haop, hapc, hpc, hI.Y])
  | cas7 i =>
    cases hro : r.op with
    | cas old new =>
      simp only [pstep, hfr, hop, hpc, hro]
      split_ifs with h1 h2
      · exact sim_pure hI hfr hop (by simp [hpc]) (by simp)
          (by simp [apstep, haop, hapc, hpc, hI.Y, hro, h1])
      · have h1' := not_not.mp h1; subst h2
        exact sim_pure hI hfr hop (by simp [hpc]) (by simp)
          (by simp [apstep, haop, hapc, hpc, hI.Y, hro, h1'])
      · exact sim_pure hI hfr hop (by simp [hpc]) (by simp)
          (by simp [apstep, haop, hapc, hpc, hI.Y, hro, h1, h2])
    | read =>
      have : pstep s p = s := by simp only [pstep, hfr, hop, hpc, hro]
      rw [this]; exact ⟨a, .refl, hI⟩
    | write v =>
      have : pstep s p = s := by simp only [pstep, hfr, hop, hpc, hro]
      rw [this]; exact ⟨a, .refl, hI⟩
  | cas10 i z =>
    cases hro : r.op with
    | cas old new =>
      simp only [pstep, hfr, hop, hpc, hro]
      exact sim_startSC hI hfr hop (by simp [hpc, hro, scArgs])
    | read =>
      have : pstep s p = s := by simp only [pstep, hfr, hop, hpc, hro]
      rw [this]; exact ⟨a, .refl, hI⟩
    | write v =>
      have : pstep s p = s := by simp only [pstep, hfr, hop, hpc, hro]
      rw [this]; exact ⟨a, .refl, hI⟩
  | wr12 =>
    simp only [pstep, hfr, hop, hpc]
    exact sim_pure hI hfr hop (by simp [hpc]) (by simp) (by simp [apstep, haop, hapc, hpc, hI.Y])
  | wr13 w =>
    cases hro : r.op with
    | write v =>
      simp only [pstep, hfr, hop, hpc, hro]
      split_ifs with h1 h2
      · exact sim_pure hI hfr hop (by simp [hpc]) (by simp)
          (by simp [apstep, haop, hapc, hpc, hI.Y, hro, h1])
      · exact sim_pure hI hfr hop (by simp [hpc]) (by simp)
          (by simp [apstep, haop, hapc, hpc, hI.Y, hro, h1, h2])
      · exact sim_pure hI hfr hop (by simp [hpc]) (by simp)
          (by simp [apstep, haop, hapc, hpc, hI.Y, hro, h1, h2])
    | read =>
      have : pstep s p = s := by simp only [pstep, hfr, hop, hpc, hro]
      rw [this]; exact ⟨a, .refl, hI⟩
    | cas old new =>
      have : pstep s p = s := by simp only [pstep, hfr, hop, hpc, hro]
      rw [this]; exact ⟨a, .refl, hI⟩
  | wr15 w =>
    cases hro : r.op with
    | write v =>
      simp only [pstep, hfr, hop, hpc, hro]
      exact sim_startSC hI hfr hop (by simp [hpc, hro, scArgs])
    | read =>
      have : pstep s p = s := by simp only [pstep, hfr, hop, hpc, hro]
      rw [this]; exact ⟨a, .refl, hI⟩
    | cas old new =>
      have : pstep s p = s := by simp only [pstep, hfr, hop, hpc, hro]
      rw [this]; exact ⟨a, .refl, hI⟩
  | tw19 ret =>
    simp only [pstep, hfr, hop, hpc]
    exact sim_pure hI hfr hop (by simp [hpc]) (by simp) (by simp [apstep, haop, hapc, hpc, hI.Y])
  | tw20 ret zh =>
    simp only [pstep, hfr, hop, hpc]
    split_ifs with h1
    · exact sim_pure hI hfr hop (by simp [hpc]) (by simp)
        (by simp [apstep, haop, hapc, hpc, hI.Y, h1])
    · exact sim_pure hI hfr hop (by simp [hpc]) (by cases ret <;> simp [afterTW])
        (by simp [apstep, haop, hapc, hpc, hI.Y, h1])
  | tw21 ret zh wh =>
    simp only [pstep, hfr, hop, hpc]
    exact sim_startSC hI hfr hop (by simp [hpc, scArgs])
  | recv j =>
    simp only [pstep, hfr, hop, hpc]
    exact ⟨a, .refl, sim_recv hI hfr hop hpc⟩

/-! ## Invocations and crashes -/

theorem firstPc_ne_idle (op : Op V) : firstPc op ≠ .idle := by cases op <;> simp [firstPc]

theorem Inv.det_eq_of_idle {s : St P K V} {a : AS P K V} {p : P} (hI : Inv s a)
    (hfr : (s.ps p).fr = none) (hor : (a.ps p).orph = none) (c : Kind) :
    s.m.det (p, c) = a.ls (p, c) := by
  apply hI.g.detEq; intro o hx hp
  rcases owner_cases (hI.own o _ hx hp) hx (hI.p p) with ⟨f0, hf0, -⟩ | ⟨x, hx', -⟩
  · rw [hfr] at hf0; cases hf0
  · rw [hor] at hx'; cases hx'

theorem sim_invoke {s : St P K V} {a : AS P K V} {p : P} {k : K} {op : Op V} (hI : Inv s a)
    (hidle : (s.ps p).op = none) :
    ∃ a', Relation.ReflTransGen AStep a a' ∧ Inv (doInvoke s p k op) a' := by
  have hP := hI.p p
  have hpc := hP.idle.1 hidle
  have hfr := hP.idleFr hpc
  have hor : (a.ps p).orph = none := by
    cases hx : (a.ps p).orph with
    | none => rfl
    | some x => obtain ⟨-, -, -, -, -, r, -, hr, -⟩ := hP.orph x hx; rw [hidle] at hr; cases hr
  have hdet := hI.det_eq_of_idle hfr hor .crit
  refine ⟨a.invoke p k op, .single ⟨.invoke p k op, hP.op.trans hidle, rfl⟩, ?_⟩
  refine ⟨hI.Y, by simp [AS.invoke, doInvoke, hI.hist, hI.nid, hdet], by simp [AS.invoke, doInvoke, hI.nid], hI.g, ?_, ?_⟩
  · apply forall_update_PInv _ (fun q _ => hI.p q)
    refine ⟨by simp [hI.nid, hdet], by simp [firstPc_ne_idle], fun _ => rfl, by simp [apcOf], ?_,
      fun f hf => by cases hf⟩
    intro x hx; simp only [hor] at hx; cases hx
  · intro o g hx hp
    have hgp : g.1 ≠ p := by
      intro hgp
      rcases owner_cases (hI.own o g hx hp) hx (hI.p g.1) with ⟨f0, hf0, -⟩ | ⟨x, hx', -⟩
      · rw [hgp, hfr] at hf0; cases hf0
      · rw [hgp, hor] at hx'; cases hx'
    rcases hI.own o g hx hp with ⟨f0, hf0, h'⟩ | ⟨x, hx', h'⟩
    · exact Or.inl ⟨f0, by simp [doInvoke, Function.update_of_ne hgp, hf0], h'⟩
    · exact Or.inr ⟨x, by simp [AS.invoke, Function.update_of_ne hgp, hx'], h'⟩

theorem COrphOK.toRecv0 {m : Mem P K V} {p : P} {st : PState P K V} {x : Orph P K V}
    (h : COrphOK m p st x) : COrphOK m p ⟨.recv 0, none, st.op⟩ x := by
  obtain ⟨h1, h2, h3, h4, h5, r, j, hr, -, hj⟩ := h
  refine ⟨h1, h2, h3, h4, h5, r, 0, hr, rfl, ?_⟩
  rcases hj with ⟨ho, -⟩ | ⟨ho, -⟩
  · exact Or.inl ⟨ho, rfl⟩
  · exact Or.inr ⟨ho, by simp⟩

/-- The A-level crash flag: the process crashes after its install and before it is moved. -/
def crashFlag (s : St P K V) (p : P) : Bool :=
  match (s.ps p).fr with
  | some f => decide (f.kind = .sc ∧ f.r = true ∧ ¬ f.sh ≤ (s.m.Y f.o).1)
  | none => false

theorem sim_crash {s : St P K V} {a : AS P K V} {p : P} (hI : Inv s a)
    (hbusy : (s.ps p).op.isSome) :
    ∃ a', Relation.ReflTransGen AStep a a' ∧ Inv (doCrash s p) a' := by
  have hP := hI.p p
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hbusy
  have haop : (a.ps p).op = some r := hP.op.trans hr
  -- the new orphan component
  have hnew : ∀ x, ((a.crash p (crashFlag s p)).ps p).orph = some x →
      COrphOK s.m p ⟨.recv 0, none, (s.ps p).op⟩ x ∧
      (crashFlag s p = false → (a.ps p).orph = some x) ∧
      (crashFlag s p = true → ∃ f, (s.ps p).fr = some f ∧ x.o = f.o) := by
    intro x hx
    simp only [AS.crash, Function.update_self] at hx
    cases hb : crashFlag s p with
    | false =>
      simp only [hb, Option.orElse] at hx
      exact ⟨(hP.orph x hx).toRecv0, fun _ => hx, fun h => (by cases h)⟩
    | true =>
      cases hfr : (s.ps p).fr with
      | none => simp [crashFlag, hfr] at hb
      | some f =>
        have hb' := hb
        simp only [crashFlag, hfr, decide_eq_true_eq] at hb
        obtain ⟨hk, hrt, hnm⟩ := hb
        have hF := hP.fr f hfr
        have hapc : (a.ps p).pc = .at (s.ps p).pc := by
          rw [hP.pc]; simp [apcOf, hfr, Moved, hnm]
        obtain ⟨r', hr', hsc, -⟩ := hF.2.1
        rw [hr] at hr'; cases hr'
        have hsc' := hsc hk
        simp only [hb', haop, hapc, hsc', Option.orElse] at hx
        cases hx
        obtain ⟨hlt, hm⟩ := ((hF.2.2.1 hk).2 (hF.fwd_of_r hrt)).1 hrt
        obtain ⟨hX, hy, hv⟩ := hm.resolve_left hnm
        refine ⟨⟨hF.1, by simp [hX], ?_, hy.symm, hv.symm, r, 0, hr, rfl, ?_⟩,
          fun h => (by cases h), fun _ => ⟨f, rfl, rfl⟩⟩
        · show (s.m.Y f.o).1 < (s.m.X f.o).2
          rw [hX, hy]; exact hlt
        · rcases (scArgs_h hsc').2 with h | h
          · exact Or.inl ⟨h, rfl⟩
          · exact Or.inr ⟨h, by simp⟩
  refine ⟨a.crash p (crashFlag s p), .single ⟨.crash p (crashFlag s p),
    by simp [ALbl.En, hP.op, hr], rfl⟩, ?_⟩
  refine ⟨hI.Y, by simp [AS.crash, doCrash, hI.hist], by simp [AS.crash, doCrash, hI.nid], hI.g,
    ?_, ?_⟩
  · apply forall_update_PInv _ (fun q _ => hI.p q)
    exact ⟨by simp [hP.op], by simp [hr], fun h => (by cases h), by simp [apcOf],
      fun x hx => (hnew x (by simpa [AS.crash] using hx)).1, fun f hf => (by cases hf)⟩
  · intro o g hx hp
    change Pend s.m o at hp
    change (s.m.X o).1 = some g at hx
    by_cases hgp : g.1 = p
    · right
      rw [hgp]
      rcases owner_cases (hI.own o g hx hp) hx (hI.p g.1) with
        ⟨f0, hf0, hk, hrt, hfo, -, hsh, -⟩ | ⟨x, hx', hxo, -, hrec⟩
      · rw [hgp] at hf0
        have hb : crashFlag s p = true := by
          have : ¬ f0.sh ≤ (s.m.Y f0.o).1 := by
            rw [hsh, hfo]; unfold Pend at hp; omega
          simp [crashFlag, hf0, hk, hrt, this]
        have hfr0 := hf0
        have hF := hP.fr f0 hf0
        have hapc : (a.ps p).pc = .at (s.ps p).pc := by
          rw [hP.pc]; simp [apcOf, hf0, Moved, hk, hrt]
          rw [hsh, hfo]; unfold Pend at hp; omega
        obtain ⟨r', hr', hsc, -⟩ := hF.2.1
        rw [hr] at hr'; cases hr'
        refine ⟨⟨f0.o, f0.h, f0.s, f0.v⟩, ?_, hfo⟩
        simp [AS.crash, hb, haop, hapc, hsc hk]
      · rw [hgp] at hx' hrec
        have hb : crashFlag s p = false := by
          cases hfr : (s.ps p).fr with
          | none => simp [crashFlag, hfr]
          | some f => have := hrec f hfr; simp [crashFlag, hfr, this]
        exact ⟨x, by simp [AS.crash, hb, Option.orElse, hx'], hxo⟩
    · rcases hI.own o g hx hp with ⟨f0, hf0, h'⟩ | ⟨x, hx', h'⟩
      · exact Or.inl ⟨f0, by simp [doCrash, Function.update_of_ne hgp, hf0], h'⟩
      · exact Or.inr ⟨x, by simp [AS.crash, Function.update_of_ne hgp, hx'], h'⟩

end Podc.DuraCAS
