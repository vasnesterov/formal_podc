import Papers.PODC2022.RecoverableHarder.Fig2Inv

/-!
# Figure 2 solves recoverable team consensus

`fig2_safe`: with a read operation `rd` of `S`, recording data (`RecOn` on all processes) and the
orientation `q₀ ∉ Q_B`, every execution of `fig2` (any crashes and recoveries) from team-uniform
inputs satisfies agreement (including outputs of different incarnations) and validity
(Lemmas 9–13 of the paper). Together with `fig2_ranked` (recoverable wait-freedom) this is the
"thus, it suffices to show that the algorithm in Figure 2 solves recoverable team consensus" part
of the proof of Theorem 8.
-/

namespace Podc.RecoverableHarder

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

section Safe

variable {S : ObjSpec} {rd : S.Op} {k : ℕ} {π : List Bool} {u : S.State} {team : Fin k → Bool}
  {o : Fin k → S.Op}

/-- The register `R_X` of node `π`. -/
def RV (C : Cfg (fig2 rd π u team o)) (X : Bool) : Option Bool := C.mem (.inl (π, X))

/-- The object `O` of node `π`. -/
def OV (C : Cfg (fig2 rd π u team o)) : S.State := C.mem (.inr π)

/-- The program counters. -/
def PCs (C : Cfg (fig2 rd π u team o)) : Fin k → PC := fun q => (C.loc q).pc

/-- The invariant on configurations. -/
def Inv (x : Fin k → Bool) (C : Cfg (fig2 rd π u team o)) (g : Ghost k) : Prop :=
  C.inp = x ∧ (∀ q, (C.loc q).p = q ∧ (C.loc q).v = x q) ∧
    InvV u team o x (PCs C) (RV C) (OV C) g

lemma loc_eq {x : Fin k → Bool} {C : Cfg (fig2 rd π u team o)} {g : Ghost k} (hI : Inv x C g)
    (q : Fin k) : C.loc q = ⟨q, x q, (C.loc q).pc⟩ := by
  obtain ⟨h1, h2⟩ := hI.2.1 q
  rcases hl : C.loc q with ⟨p', v', pc'⟩
  rw [hl] at h1 h2; simp only at h1 h2; subst h1 h2; rfl

/-- The program counters after a step of `p` that leaves `p` in local state `l'`. -/
lemma pcs_stepP (C : Cfg (fig2 rd π u team o)) (p : Fin k) {i : Idx} {o' : (Obj S i).Op}
    {κ : (Obj S i).Resp → TL k} (h : (fig2 rd π u team o).act (C.loc p) = .access i o' κ) :
    PCs (C.stepP p) = Function.update (PCs C) p (κ ((Obj S i).δ (C.mem i) o').2).pc := by
  funext q
  by_cases hq : q = p
  · subst hq; simp [PCs, stepP_loc_self C h]
  · simp [PCs, stepP_loc_other C hq, hq]

lemma inv_loc_stepP {x : Fin k → Bool} {C : Cfg (fig2 rd π u team o)} {g : Ghost k}
    (hI : Inv x C g) (p : Fin k) {i : Idx} {o' : (Obj S i).Op}
    {κ : (Obj S i).Resp → TL k} (h : (fig2 rd π u team o).act (C.loc p) = .access i o' κ)
    (hκ : ∀ r, (κ r).p = p ∧ (κ r).v = x p) :
    ∀ q, ((C.stepP p).loc q).p = q ∧ ((C.stepP p).loc q).v = x q := by
  intro q
  by_cases hq : q = p
  · subst hq; rw [stepP_loc_self C h]; exact hκ _
  · rw [stepP_loc_other C hq]; exact hI.2.1 q

variable (hrd : ∀ q, (S.δ q rd).1 = q) (hinj : Function.Injective fun q => (S.δ q rd).2)
  (hrec : RecOn S Finset.univ u team o) (hB : ¬ QX u team o true u)

include hrd hinj hrec hB in
open Classical in
/-- One step preserves the invariant (with a new ghost value and the same decision, if any). -/
theorem Inv.stepP {x : Fin k → Bool} (hx : ∀ p q, team p = team q → x p = x q)
    {C : Cfg (fig2 rd π u team o)} {g : Ghost k} (hI : Inv x C g) (p : Fin k) :
    ∃ g', Inv x (C.stepP p) g' ∧ ∀ d, g.dec = some d → g'.dec = some d := by
  have hl := loc_eq hI p
  have hV := hI.2.2
  have hinp : (C.stepP p).inp = x := by rw [stepP_inp]; exact hI.1
  rcases hpc : (C.loc p).pc with _ | _ | _ | _ | _ | Y | w
  · -- wr
    rw [hpc] at hl
    have h : (fig2 rd π u team o).act (C.loc p) = .access (.inl (π, team p))
        (RWOp.write (some (x p))) (fun _ => ⟨p, x p, .rd1⟩) := by rw [hl]; rfl
    refine ⟨g, ⟨hinp, inv_loc_stepP hI p h (fun _ => ⟨rfl, rfl⟩), ?_⟩, fun d hd => hd⟩
    have hR : RV (C.stepP p) = Function.update (RV C) (team p) (some (x p)) := by
      funext X
      by_cases hX : X = team p
      · subst hX; simp only [RV, Function.update_self]; rw [stepP_mem_self C h]; rfl
      · simp only [RV, Function.update_of_ne hX]
        rw [stepP_mem_other C h (by simpa using hX)]
    have hO : OV (C.stepP p) = OV C := by
      simp only [OV]; rw [stepP_mem_other C h (by simp)]
    rw [pcs_stepP C p h, hR, hO]
    exact hV.wr hx hpc
  · -- rd1
    rw [hpc] at hl
    have h : (fig2 rd π u team o).act (C.loc p) = .access (.inr π) rd (fun r => ⟨p, x p,
        if r = (S.δ u rd).2 then (if team p = true ∧ (∃! q, team q = true) then .chk else .upd)
        else .rdR (side rd u team o r)⟩) := by rw [hl]; rfl
    refine ⟨g, ⟨hinp, inv_loc_stepP hI p h (fun _ => ⟨rfl, rfl⟩), ?_⟩, fun d hd => hd⟩
    have hmem : (C.stepP p).mem = C.mem := by
      rw [stepP_mem_of_access C h]
      exact Function.update_eq_self_iff.2 (hrd _)
    have hR : RV (C.stepP p) = RV C := by funext X; simp only [RV]; rw [hmem]
    have hO : OV (C.stepP p) = OV C := by simp only [OV]; rw [hmem]
    rw [pcs_stepP C p h, hR, hO]
    exact hV.rd1 hinj hrec hB hpc
  · -- chk
    rw [hpc] at hl
    have h : (fig2 rd π u team o).act (C.loc p) = .access (.inl (π, false)) RWOp.read
        (fun r => ⟨p, x p, match (r : Option Bool) with
          | some w => .done w
          | none => .upd⟩) := by rw [hl]; rfl
    have hmem : (C.stepP p).mem = C.mem := by
      rw [stepP_mem_of_access C h]
      exact Function.update_eq_self_iff.2 rfl
    have hR : RV (C.stepP p) = RV C := by funext X; simp only [RV]; rw [hmem]
    have hO : OV (C.stepP p) = OV C := by simp only [OV]; rw [hmem]
    have hpcs := pcs_stepP C p h
    have hloc := inv_loc_stepP hI p h (fun _ => ⟨rfl, rfl⟩)
    rcases hRA : RV C false with _ | w
    · refine ⟨g, ⟨hinp, hloc, ?_⟩, fun d hd => hd⟩
      rw [hpcs, hR, hO]
      have : (Obj S (.inl (π, false))).δ (C.mem (.inl (π, false))) RWOp.read =
          (RV C false, RV C false) := rfl
      rw [this, hRA]
      exact hV.chk_none hpc hRA
    · obtain ⟨hV', hw⟩ := hV.chk_some hrec hpc hRA
      refine ⟨⟨g.L, g.ep2, some w⟩, ⟨hinp, hloc, ?_⟩, fun d hd => by rw [hw d hd]⟩
      rw [hpcs, hR, hO]
      have : (Obj S (.inl (π, false))).δ (C.mem (.inl (π, false))) RWOp.read =
          (RV C false, RV C false) := rfl
      rw [this, hRA]
      exact hV'
  · -- upd
    rw [hpc] at hl
    have h : (fig2 rd π u team o).act (C.loc p) = .access (.inr π) (o p)
        (fun _ => ⟨p, x p, .rd2⟩) := by rw [hl]; rfl
    obtain ⟨g', hV', hd'⟩ := hV.upd hrec hB hpc
    refine ⟨g', ⟨hinp, inv_loc_stepP hI p h (fun _ => ⟨rfl, rfl⟩), ?_⟩,
      fun d hd => by rw [hd', hd]⟩
    have hR : RV (C.stepP p) = RV C := by
      funext X; simp only [RV]; rw [stepP_mem_other C h (by simp)]
    have hO : OV (C.stepP p) = (S.δ (OV C) (o p)).1 := by
      simp only [OV]; rw [stepP_mem_self C h]; rfl
    rw [pcs_stepP C p h, hR, hO]
    exact hV'
  · -- rd2
    rw [hpc] at hl
    have h : (fig2 rd π u team o).act (C.loc p) = .access (.inr π) rd
        (fun r => ⟨p, x p, .rdR (side rd u team o r)⟩) := by rw [hl]; rfl
    refine ⟨g, ⟨hinp, inv_loc_stepP hI p h (fun _ => ⟨rfl, rfl⟩), ?_⟩, fun d hd => hd⟩
    have hmem : (C.stepP p).mem = C.mem := by
      rw [stepP_mem_of_access C h]
      exact Function.update_eq_self_iff.2 (hrd _)
    have hR : RV (C.stepP p) = RV C := by funext X; simp only [RV]; rw [hmem]
    have hO : OV (C.stepP p) = OV C := by simp only [OV]; rw [hmem]
    rw [pcs_stepP C p h, hR, hO]
    exact hV.step_rd2 hinj hrec hpc
  · -- rdR Y
    rw [hpc] at hl
    have h : (fig2 rd π u team o).act (C.loc p) = .access (.inl (π, Y)) RWOp.read
        (fun r => ⟨p, x p, .done ((r : Option Bool).getD false)⟩) := by rw [hl]; rfl
    obtain ⟨w, hw, hV', hdec⟩ := hV.step_rdR hrec hpc
    refine ⟨⟨g.L, g.ep2, some w⟩, ⟨hinp, inv_loc_stepP hI p h (fun _ => ⟨rfl, rfl⟩), ?_⟩,
      fun d hd => by rw [hdec d hd]⟩
    have hmem : (C.stepP p).mem = C.mem := by
      rw [stepP_mem_of_access C h]
      exact Function.update_eq_self_iff.2 rfl
    have hR : RV (C.stepP p) = RV C := by funext X; simp only [RV]; rw [hmem]
    have hO : OV (C.stepP p) = OV C := by simp only [OV]; rw [hmem]
    rw [pcs_stepP C p h, hR, hO]
    have : (Obj S (.inl (π, Y))).δ (C.mem (.inl (π, Y))) RWOp.read = (RV C Y, RV C Y) := rfl
    rw [this, hw]
    exact hV'
  · -- done w: no-op
    rw [hpc] at hl
    have h : C.Out p w := by simp only [Cfg.Out]; rw [hl]; rfl
    rw [stepP_of_out C h]
    exact ⟨g, hI, fun d hd => hd⟩

/-- A crash preserves the invariant. -/
theorem Inv.crash {x : Fin k → Bool} {C : Cfg (fig2 rd π u team o)} {g : Ghost k}
    (hI : Inv x C g) (p : Fin k) : Inv x (C.next (.crash p)) g := by
  have hself : (C.next (.crash p)).loc p = (⟨p, x p, .wr⟩ : TL k) := by
    rw [crash_loc_self, hI.1]; rfl
  have hother : ∀ q, q ≠ p → (C.next (.crash p)).loc q = C.loc q :=
    fun q hq => next_loc_other C _ (by simpa using hq)
  refine ⟨by simpa using hI.1, fun q => ?_, ?_⟩
  · by_cases hq : q = p
    · subst hq; rw [hself]; exact ⟨rfl, rfl⟩
    · rw [hother q hq]; exact hI.2.1 q
  · have hpcs : PCs (C.next (.crash p)) = Function.update (PCs C) p .wr := by
      funext q
      by_cases hq : q = p
      · subst hq; simp only [PCs, hself, Function.update_self]
      · simp only [PCs, hother q hq, Function.update_of_ne hq]
    rw [hpcs]
    exact hI.2.2.crash

include hrd hinj hrec hB in
/-- **Figure 2 solves recoverable team consensus** (Lemmas 9–13): agreement and validity for
inputs that are constant on each team, in all executions (crashes and recoveries included). -/
theorem fig2_safe :
    Safe (fig2 rd π u team o) (fun x => ∀ p q, team p = team q → x p = x q) (AdmB true) := by
  refine safe_of_ghost true _ (fun x C g => Inv x C g) Ghost.dec (fun x _ => ?_)
    (fun x hx C g p hI => hI.stepP hrd hinj hrec hB hx p)
    (fun _ x _ C g p hI => ⟨g, hI.crash p, fun d hd => hd⟩) (fun x C g p w hI hout => ?_)
    (fun x _ C g d hI hd => ?_)
  · refine ⟨⟨[], false, none⟩, rfl, fun q => ⟨rfl, rfl⟩, ?_⟩
    refine ⟨fun X w hw => by simp [RV, initCfg, fig2, mem0] at hw, fun q hq => by
      simp [PCs, initCfg, fig2] at hq, by simp [OV, initCfg, fig2, mem0], by simp,
      fun _ h => absurd rfl h, fun h => by simp at h, fun q hq => by simp [PCs, initCfg, fig2] at hq,
      fun q hq => by simp [PCs, initCfg, fig2] at hq, fun q hq => by simp [PCs, initCfg, fig2] at hq,
      fun q Y hq => by simp [PCs, initCfg, fig2] at hq,
      fun q w hq => by simp [PCs, initCfg, fig2] at hq, fun d hd => by simp at hd,
      fun Y hY => by simp [Ghost.fst] at hY⟩
  · have hl := loc_eq hI p
    simp only [Cfg.Out] at hout
    rw [hl] at hout
    rcases hpc : (C.loc p).pc with _ | _ | _ | _ | _ | Y | w'
    all_goals rw [hpc] at hout
    all_goals simp [fig2] at hout
    subst hout
    exact hI.2.2.done p _ (by simp [PCs, hpc])
  · rcases hf : g.fst team with _ | Y
    · obtain ⟨a, ha⟩ := exists_team hrec false
      exact ⟨a, ((hI.2.2.dec d hd).2 hf).2.2.1 a ha⟩
    · obtain ⟨a, ha⟩ := exists_team hrec Y
      exact ⟨a, (hI.2.2.dec d hd).1 Y hf a ha⟩

end Safe

end Podc.RecoverableHarder
