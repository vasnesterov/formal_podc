import Papers.PODC2023.DuraCAS.AStep6

/-!
# DuraCAS over atomic durable EC objects is durably linearizable and detectable

(Appendix A.3, Lemmas A.28–A.45, made rigorous in the A-level model.)

Every A-level transition preserves the invariant `GInv` of `AGlob.lean` for a suitable update of
the ghost state (`GInv.astep`); the initial state satisfies it (`gInv_init`), and it implies
durable linearizability and detectability of the history (`GInv.durLinDet`).
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

theorem GInv.stepP {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r)
    (hen : ∀ j, (a.ps p).pc = .at (.recv j) → ∀ x, (a.ps p).orph = some x → x.o ≠ recObj r.k j) :
    ∃ g', GInv init (apstep a p) g' := by
  rcases hpc : (a.ps p).pc with c | ⟨c, b⟩
  · cases c with
    | idle => exact (h.pcok hop hpc).elim
    | read => exact step_read h hop hpc
    | cas7 i => exact step_cas7 h hop hpc
    | cas10 i z => exact step_cas10 h hop hpc
    | wr12 => exact step_wr12 h hop hpc
    | wr13 w => exact step_wr13 h hop hpc
    | wr15 w => exact step_wr15 h hop hpc
    | tw19 ret => exact step_tw19 h hop hpc
    | tw20 ret zh => exact step_tw20 h hop hpc
    | tw21 ret zh wh => exact step_tw21 h hop hpc
    | recv j => exact step_recv h hop hpc (hen j hpc)
  · cases c with
    | cas10 i z => exact step_aft_cas10 h hop hpc
    | wr15 w => exact step_aft_wr15 h hop hpc
    | tw21 ret zh wh => exact step_aft_tw21 h hop hpc
    | _ => exact (h.pcok hop hpc).elim

/-- An orphan `ECSC` takes effect. -/
theorem GInv.orphStep {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {x : Orph P K V}
    (h : GInv init a g) (ho : (a.ps p).orph = some x) (hs : (a.Y x.o).1 = x.s) :
    ∃ g', GInv init (a.orphEff p) g' := by
  obtain ⟨r, hop⟩ : ∃ r, (a.ps p).op = some r := by
    cases hop : (a.ps p).op with
    | none => rw [h.idle p hop] at ho; cases ho
    | some r => exact ⟨r, rfl⟩
  have hl := h.loc p r hop
  have hv := h.kinv r.k
  simp only [AS.orphEff, ho, ecsc, hs, ↓reduceIte]
  rcases (hl.orph x ho).2 with ⟨hoo, hoh, hls, -⟩ | ⟨hoo, hoh, hls, -⟩ | ⟨hoo, hoh, -⟩
  · rw [hoo] at hs ⊢; rw [hoh]
    obtain ⟨hI, hact⟩ := orph_inst (max (a.ls (p, .crit)) x.s + 1) hl hv ho hoo hs
      (by show a.ls (p, .crit) < _; omega) (by omega)
    exact ⟨_, h.inst hop _ (by simp [hop]) _ _ hI hact⟩
  · rw [hoo] at hs ⊢; rw [hoh]
    obtain ⟨hI, hact, old, hopr, hZo⟩ := orph_impr g.clk (max (a.ls (p, .crit)) x.s + 1) hl hv ho
      hoo hoh hs (by show a.ls (p, .crit) < _; omega) (by omega)
    have hsig : curSt init g.L r.k = old := by
      have h1 : curSt init g.L r.k = (a.Y (r.k, .Z)).2.1 := hv.sig_eq
      rw [h1]; exact hZo
    have hninL : r.id ∉ g.L.map GE.id := fun hin => by
      have := hl.inL_lt hin; simp only [pview] at this hls; omega
    exact ⟨_, h.impr hop hopr hsig hninL _ (by simp [hop]) _ x.v.2 hI hact⟩
  · rw [hoo] at hs ⊢; rw [hoh]
    obtain ⟨hM, hact⟩ := orph_move g.clk (max (a.ls (p, .cas)) x.s + 1) hl hv ho hoo hoh hs
      (by omega)
    obtain ⟨idw, hidw⟩ := Option.ne_none_iff_exists'.1 (hv.pend_iff.1 hM.pend)
    exact ⟨_, h.move hop hidw _ (by simp [hop]) _ _ hM hact⟩

/-- **Preservation.** Every A-level transition preserves the invariant (for some ghost update). -/
theorem GInv.astep {init : K → V} {a a' : AS P K V} {g : Gh P K V} (h : GInv init a g)
    (hs : AStep a a') : ∃ g', GInv init a' g' := by
  obtain ⟨ℓ, hen, rfl⟩ := hs
  cases ℓ with
  | step p =>
    obtain ⟨r, hop, hg⟩ := hen
    exact h.stepP hop hg
  | invoke p k op => exact ⟨_, h.invoke k op hen⟩
  | crash p b =>
    obtain ⟨r, hop⟩ := Option.isSome_iff_exists.1 hen
    exact ⟨_, h.crash b hop⟩
  | orph p =>
    obtain ⟨x, ho, hs⟩ := hen
    exact h.orphStep ho hs
  | drop p =>
    obtain ⟨x, ho⟩ := Option.isSome_iff_exists.1 hen
    obtain ⟨r, hop⟩ : ∃ r, (a.ps p).op = some r := by
      cases hop : (a.ps p).op with
      | none => rw [h.idle p hop] at ho; cases ho
      | some r => exact ⟨r, rfl⟩
    exact ⟨g, h.go hop _ hop (drop_actor (h.loc p r hop))⟩

/-- Every reachable A-level state has a ghost state satisfying the invariant. -/
theorem aReach_gInv {init : K → V} {a : AS P K V} (h : AReach init a) : ∃ g, GInv init a g := by
  induction h with
  | refl => exact ⟨gInit, gInv_init init⟩
  | tail _ hs ih =>
    obtain ⟨g, hg⟩ := ih
    exact hg.astep hs

/-- **Lemmas A.44 and A.45 (A-level).** Every history of DuraCAS over atomic durable EC objects is
durably linearizable and detectable. -/
theorem aReach_durLinDet {init : K → V} {a : AS P K V} (h : AReach init a) :
    DurLinDet init a.hist := by
  obtain ⟨g, hg⟩ := aReach_gInv h
  exact hg.durLinDet

end Podc.DuraCAS
