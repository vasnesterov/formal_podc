import Papers.PODC2023.DuraCAS.AStep4

/-!
# Preservation of the global invariant: the ends of operations

The linearization of operations that end (Definitions A.42 and A.43): a `READ`, a `CAS` returning
at line 8 and a trivial `WRITE` are linearized at their last step (`GInv.mainret`); a `CAS` that
returns `false` at line 11 is inserted after its witness step (`GInv.fret`); a `WRITE` returning at
line 18 is already linearized (installer) or inserted before the installer moved at its witness
step (`GInv.wret`); a completed `RECOVER` adds nothing (`GInv.rdn`).
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-- An operation linearized at its last step (it does not change the value). -/
theorem GInv.mainret {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) (horph : (a.ps p).orph = none)
    (hpw : g.pw r.k ≠ some r.id) (hls : a.ls (p, .crit) = r.d1) (resp : Resp V)
    (hseq : seqStep (curSt init g.L) r.k r.op = (curSt init g.L, resp)) :
    GInv init (a.fin p (.ret r.id resp (a.ls (p, .crit))))
      (g.tick a.hist.length (g.L ++ [⟨4 * g.clk + 1, r.id, r.k, r.op, resp⟩])) := by
  set x : GE K V := ⟨4 * g.clk + 1, r.id, r.k, r.op, resp⟩
  have hl := h.loc p r hop
  have hninL : r.id ∉ g.L.map GE.id := fun hin => by
    have := hl.inL_lt hin; simp only [pview] at this; omega
  have hit := h.busy_it p r hop
  refine h.fin hop horph hpw _ _ ⟨rfl, rfl, by intros; simp⟩
    (lgood_append h.lgood x rfl hninL (by simp [x, hseq])) (fun e he => List.mem_append_left _ he)
    (fun e he => ?_) (by rw [curSt_append_one]; simp [x, hseq])
    (fun t ht => stAt_append_lt x rfl t ht) (fun id resp' d he => ?_) (fun hlt => by omega)
    (fun id d he => by simp at he)
  · rcases List.mem_append.1 he with he | he
    · exact Or.inl he
    · simp at he; subst he; exact Or.inr ⟨rfl, rfl, rfl, by simp [x]; omega, by simp [x]⟩
  · simp only [Ev.ret.injEq] at he
    exact ⟨x, by simp, rfl, he.2.1⟩

/-- A completed operation already in the linearization or ending without effect. -/
theorem GInv.done_noL {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) (horph : (a.ps p).orph = none)
    (hpw : g.pw r.k ≠ some r.id) (ev : Ev P K V)
    (hev : ev.Ends r.id ∧ ev.dEnd = a.ls (p, .crit) ∧ ∀ id p k op d, ev ≠ Ev.inv id p k op d)
    (hret : ∀ id resp d, ev = Ev.ret id resp d → resp = .ok true ∧ r.id ∈ g.L.map GE.id) :
    GInv init (a.fin p ev) (g.tick a.hist.length g.L) := by
  have hl := h.loc p r hop
  have hin : r.d1 < a.ls (p, .crit) → r.id ∈ g.L.map GE.id := fun hlt => by
    rcases hl.lt_inL hlt with h' | h'
    · exact h'
    · exact absurd h' hpw
  have hentry : r.id ∈ g.L.map GE.id → ∃ e ∈ g.L, e.id = r.id ∧ e.rsp = .ok true := fun hm => by
    obtain ⟨e, he, hid⟩ := List.mem_map.1 hm
    exact ⟨e, he, hid, (h.act_rsp p r hop e he hid).2.2⟩
  refine h.fin hop horph hpw ev _ hev (h.lgood.mono (by omega)) (fun e he => he)
    (fun e he => Or.inl he) rfl (fun _ _ => rfl) (fun id resp d he => ?_)
    (fun hlt => hentry (hin hlt)) (fun id d _ heq hm => ?_)
  · obtain ⟨rfl, hm⟩ := hret id resp d he
    exact hentry hm
  · have := hl.inL_lt hm; simp only [pview] at this; omega

/-- A `CAS` returning `false` at line 11. -/
theorem GInv.fret {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) (horph : (a.ps p).orph = none)
    {old new : V} (hropc : r.op = .cas old new) (hls : a.ls (p, .crit) = r.d1)
    (hw : g.wit p ≠ none) :
    ∃ g', GInv init (a.fin p (.ret r.id (.ok false) (a.ls (p, .crit)))) g' := by
  have hl := h.loc p r hop
  have hninL : r.id ∉ g.L.map GE.id := fun hin => by
    have := hl.inL_lt hin; simp only [pview] at this; omega
  have hpw : g.pw r.k ≠ some r.id := fun e => by
    have := (hl.pw_op e).2; simp only [pview] at this; rw [hropc] at this; cases this
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hw
  obtain ⟨a1, a2, a3, -⟩ := h.wit p r hop t ht
  set x : GE K V := ⟨4 * t + 3, r.id, r.k, r.op, .ok false⟩
  obtain ⟨L', hLg, hsub, hmem, hx, hcur, hst⟩ :=
    lgood_insert_fcas h.lgood a2 x rfl hropc (a3 old new hropc) rfl hninL
  refine ⟨_, h.fin hop horph hpw _ L' ⟨rfl, rfl, by intros; simp⟩ hLg hsub (fun e he => ?_) hcur
    (fun t' _ => hst t') (fun id resp d he => ?_) (fun hlt => by omega) (fun id d he => by simp at he)⟩
  · rcases hmem e he with he | rfl
    · exact Or.inl he
    · exact Or.inr ⟨rfl, rfl, rfl, by simp [x]; omega, by simp [x]; omega⟩
  · simp only [Ev.ret.injEq] at he
    exact ⟨x, hx, rfl, he.2.1⟩

/-- A `WRITE` returning at line 18 (after its second transfer): it no longer needs a move. -/
theorem GInv.wret {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) (horph : (a.ps p).orph = none)
    (hwr : IsWr r.op) (hneed : ¬ needW (view init a g r.k) (pview a g p r)) :
    ∃ g', GInv init (a.fin p (.ret r.id (.ok true) (a.ls (p, .crit)))) g' := by
  have hl := h.loc p r hop
  have hpw : g.pw r.k ≠ some r.id := fun e => hneed (Or.inl e)
  by_cases hlt : r.d1 < a.ls (p, .crit)
  · refine ⟨_, h.done_noL hop horph hpw _ ⟨rfl, rfl, by intros; simp⟩ (fun id resp d he => ?_)⟩
    simp only [Ev.ret.injEq] at he
    refine ⟨he.2.1.symm, ?_⟩
    rcases hl.lt_inL hlt with h' | h'
    · exact h'
    · exact absurd h' hpw
  · have hls : a.ls (p, .crit) = r.d1 := by have := hl.d1_le; simp only [pview] at this; omega
    have hw : g.wit p ≠ none := fun hw => hneed (Or.inr ⟨hls, hw⟩)
    have hninL : r.id ∉ g.L.map GE.id := fun hin => by
      have := hl.inL_lt hin; simp only [pview] at this; omega
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hw
    obtain ⟨u, hu⟩ := hwr
    obtain ⟨a1, a2, -, a4⟩ := h.wit p r hop t ht
    obtain ⟨a5, hy⟩ := a4 u hu
    set x : GE K V := ⟨4 * t, r.id, r.k, r.op, .ok true⟩
    obtain ⟨L', hLg, hsub, hmem, hx, hcur, hst⟩ :=
      lgood_insert_hh h.lgood a2 x rfl (by simp [x, hu, Op.IsWrite]) hy rfl hninL
    refine ⟨_, h.fin hop horph hpw _ L' ⟨rfl, rfl, by intros; simp⟩ hLg hsub (fun e he => ?_) hcur
      (fun t' _ => hst t') (fun id resp d he => ?_) (fun hlt' => by omega)
      (fun id d he => by simp at he)⟩
    · rcases hmem e he with he | rfl
      · exact Or.inl he
      · exact Or.inr ⟨rfl, rfl, rfl, by simp [x]; omega, by simp [x]; omega⟩
    · simp only [Ev.ret.injEq] at he
      exact ⟨x, hx, rfl, he.2.1⟩

end Podc.DuraCAS
